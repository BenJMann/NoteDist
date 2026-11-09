import math
import os
import random
import tempfile
import unittest

import notedist as nd


class TheoryTest(unittest.TestCase):
    def test_degrees(self):
        cases = {"CuG": 5, "BuG": 6, "AuC": 3, "GdC": 5, "CdA": 3, "EdF": 7, "CuD": 2, "BuC": 2, "CdB": 2}
        for combo, want in cases.items():
            self.assertEqual(nd.degree(combo), want, combo)

    def test_all_combos(self):
        self.assertEqual(len(nd.ALL_COMBOS), 84)
        self.assertEqual({nd.degree(c) for c in nd.ALL_COMBOS}, set(range(2, 8)))

    def test_up_and_down_add_to_nine(self):
        for c in nd.ALL_COMBOS:
            a, d, b = c
            other = a + (nd.DOWN if d == nd.UP else nd.UP) + b
            self.assertEqual(nd.degree(c) + nd.degree(other), 9)


class ModelTest(unittest.TestCase):
    def setUp(self):
        self.tr = nd.Trainer(rng=random.Random(1))

    def answer(self, combo, correct, t):
        key = nd.degree(combo) if correct else (nd.degree(combo) % 6) + 2
        self.tr.record(nd.item(combo, "warm"), str(key), t)

    def test_benchmark_is_low_percentile(self):
        for t in [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]:
            self.answer("CuG", True, t)
        self.assertAlmostEqual(self.tr.bench(), 3.0)

    def test_struggle_relative(self):
        for _ in range(6):
            self.answer("CuG", True, 1.0)
            self.answer("BuG", True, 3.0)
            self.answer("AuC", False, 2.0)
        s = self.tr.struggle
        self.assertLess(s("CuG"), s("BuG"))
        self.assertLess(s("BuG"), s("AuC"))
        self.assertEqual(s("DuE"), 0.8)

    def test_level_falls_on_misses_and_rises_on_hits(self):
        start = self.tr.s["level"]
        for _ in range(5):
            self.answer("CuG", False, 3.0)
        self.assertLess(self.tr.s["level"], start)
        low = self.tr.s["level"]
        for _ in range(30):
            self.answer("CuG", True, 1.0)
        self.assertGreater(self.tr.s["level"], low)

    def test_time_is_capped(self):
        self.answer("CuG", True, 500)
        self.assertEqual(self.tr.s["recent_times"], [nd.TIME_CAP])


def play_order(trace, gid):
    """The sequence plays of a group in order, e.g. "AAABBBBABA…"; "·" is a random question."""
    return "".join(nd.seq_name(it["sid"]) if it["sid"] else "·" for it, _ in trace
                   if it["gid"] == gid and it["mode"] in ("seq", "rand") and (it["end"] or not it["sid"]))


def run(tr, n, seconds):
    """Answer n questions, all right, taking seconds(item) each."""
    trace = []
    for _ in range(n):
        it = tr.next_item()
        trace.append((it, tr.record(it, str(nd.degree(it["combo"])), seconds(it))))
    return trace


class BuildUpTest(unittest.TestCase):
    def test_perfect_learner_builds_up_round_by_round(self):
        tr = nd.Trainer(rng=random.Random(8))
        order = play_order(run(tr, 400, lambda it: 0.8), 1)
        # new A, new B, check A B, new C, check A B C, new D, check A B C D, shuffled, random
        self.assertTrue(order.startswith("AAABBB" "AAABBB" "CCC" "AAABBBCCC" "DDD" "AAABBBCCCDDD"), order)
        self.assertIn("·" * 10, order)
        g = tr.group(1)
        for sid in g["seqs"]:
            items = tr.seq(g, sid)["items"]
            self.assertEqual(len(set(items)), 3)
            self.assertTrue(set(items) <= set(g["members"]))
        # the first sequences cover the whole group before old combos are reused
        first = [c for sid in g["seqs"][:2] for c in tr.seq(g, sid)["items"]]
        self.assertEqual(len(set(first)), min(6, len(g["members"])))

    def test_block_runs_until_fast(self):
        tr = nd.Trainer(rng=random.Random(9))
        state = {"slow": 7}     # B's first 7 plays are slow, then it speeds up
        def seconds(it):
            if it["gid"] == 1 and it["sid"] == 2 and state["slow"] > 0:
                if it["end"]:
                    state["slow"] -= 1
                return 3.0
            return 0.8
        order = play_order(run(tr, 200, seconds), 1)
        self.assertRegex(order, r"^AAAB{8,}AAABBB")

    def test_new_sequence_waits_for_a_clean_round(self):
        tr = nd.Trainer(rng=random.Random(10))
        misses = {"left": 1}    # one slip in A when it's re-checked
        trace = []
        for _ in range(200):
            it = tr.next_item()
            g = tr.s["active"] and tr.group(tr.s["active"])
            wrong = (g and it["sid"] == 1 and not g.get("intro") and len(g["seqs"]) == 2
                     and misses["left"] > 0)
            if wrong:
                misses["left"] -= 1
            key = (nd.degree(it["combo"]) % 6) + 2 if wrong else nd.degree(it["combo"])
            trace.append((it, tr.record(it, str(key), 0.8)))
        order = play_order(trace, 1)
        # A needs a longer block after the slip, so A B is checked again before C comes in
        self.assertTrue(order.startswith("AAABBB" "AAAABBB" "AAABBB" "CCC"), order)


class StorageTest(unittest.TestCase):
    def test_round_trip(self):
        tr = nd.Trainer(rng=random.Random(5))
        for _ in range(40):
            it = tr.next_item()
            tr.record(it, str(nd.degree(it["combo"])), 1.5)
        with tempfile.TemporaryDirectory() as d:
            path = os.path.join(d, "x", "state.json")
            nd.save_state(tr.s, path)
            self.assertEqual(nd.load_state(path), tr.s)
            tr2 = nd.Trainer(nd.load_state(path), rng=random.Random(6))
        tr2.record(tr2.next_item(), "5", 2.0)
        self.assertEqual(tr2.s["q"], 41)


class SimUser:
    """A learner who improves with practice and forgets over unseen questions."""

    def __init__(self, rng, forget=0.003):
        self.rng = rng
        self.forget = forget
        self.skill = {c: rng.uniform(-2.0, 0.5) for c in nd.ALL_COMBOS}
        self.last = {}

    def answer(self, combo, q):
        sk = self.skill[combo] - self.forget * (q - self.last.get(combo, q))
        p = 1 / (1 + math.exp(-2 * sk))
        correct = self.rng.random() < p
        t = (0.9 + 3.0 * math.exp(-max(sk, 0))) * math.exp(self.rng.gauss(0, 0.15))
        self.skill[combo] = min(sk + (0.2 if correct else 0.12), 4.0)
        self.last[combo] = q
        key = nd.degree(combo) if correct else self.rng.choice([k for k in range(2, 8) if k != nd.degree(combo)])
        return str(key), t


def simulate(n, seed, forget=0.003):
    rng = random.Random(seed)
    tr = nd.Trainer(rng=random.Random(seed + 100))
    user = SimUser(rng, forget)
    trace = []
    events = []
    for _ in range(n):
        it = tr.next_item()
        key, t = user.answer(it["combo"], tr.s["q"])
        trace.append((it, tr.record(it, key, t)))
        events += tr.events
        tr.events.clear()
    return tr, trace, events


class SimulationTest(unittest.TestCase):
    def test_learner_progresses(self):
        tr, trace, events = simulate(3000, seed=7)
        groups = tr.s["groups"]
        learned = [g for g in groups if g["state"] == "review"]
        self.assertGreaterEqual(len(groups), 4)
        self.assertGreaterEqual(len(learned), 3)
        self.assertGreaterEqual(sum(g["reviews"] for g in groups), 2)
        # groups overlap with the one before
        self.assertTrue(set(groups[0]["members"]) & set(groups[1]["members"]))
        # every learned group went through sequences to random order before its first review
        for g in learned:
            before = []
            for it, _ in trace:
                if it["gid"] == g["id"] and it["mode"] == "review":
                    break
                if it["gid"] == g["id"]:
                    before.append(it["mode"])
            self.assertEqual(before[0], "seq")
            self.assertEqual(before[-1], "rand")
        # difficulty keeps overall accuracy near the ~80% target...
        acc = lambda xs: sum(ok for _, ok in xs) / len(xs)
        self.assertTrue(0.6 < acc(trace) < 0.92, acc(trace))
        # ...while learned groups mostly hold up when reviewed
        self.assertGreater(acc([x for x in trace if x[0]["mode"] == "review"]), 0.75)

    def test_simulated_order_is_predictable(self):
        tr, trace, events = simulate(1500, seed=7)
        order = play_order(trace, 1)
        self.assertTrue(order.startswith("AAA"), order[:60])
        self.assertLessEqual(len(set(order[:12])), 2, order[:60])

    def test_forgetting_brings_extra_reps(self):
        tr, trace, events = simulate(3000, seed=11, forget=0.006)
        self.assertTrue(any(it["mode"] == "rep" for it, _ in trace), "\n".join(events[-20:]))
        self.assertTrue(any("rusty" in e or "slipped" in e for e in events))


if __name__ == "__main__":
    unittest.main()
