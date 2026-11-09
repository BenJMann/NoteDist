import os
import random
import re
import tempfile
import unittest

import noterhythm as nr


class TheoryTest(unittest.TestCase):
    def test_degrees(self):
        for combo, want in {"CG": 5, "BG": 6, "AC": 3, "CD": 2, "BC": 2, "DC": 7, "EB": 5}.items():
            self.assertEqual(nr.degree(combo), want, combo)

    def test_ascending_only(self):
        self.assertEqual(len(nr.ALL_COMBOS), 42)
        self.assertEqual({nr.degree(c) for c in nr.ALL_COMBOS}, set(range(2, 8)))


class PlanTest(unittest.TestCase):
    def test_order_follows_the_build_up(self):
        names = [nr.step_name(s) for s in nr.build_plan()]
        pair = lambda a, b: [f"bar {a}, first half", f"bar {a}, second half", f"bar {a}",
                             f"bar {b}, first half", f"bar {b}, second half", f"bar {b}",
                             f"bars {a} and {b} alternating", f"bars {a}–{b}"]
        want = (pair(1, 2) + pair(3, 4) + ["bars 1–4"] + pair(5, 6) + pair(7, 8)
                + ["bars 5–8", "bars 1–8"])
        self.assertEqual(names, want)


def answer_all(coach, ok=lambda r: True, off=0.0):
    """One repetition answered right on the beat; ok(slot) False makes that one wrong.
    A cards step on top is answered right first."""
    clear_cards(coach)
    results = []
    for i in coach.rep_slots():
        if i is None:
            continue
        r = {"i": i, "off": off}
        right = nr.degree(coach.combo(i))
        r["key"] = str(right if ok(r) else right % 6 + 2)
        results.append(r)
    oks = coach.record_rep(results)
    return oks


def answer_cards(coach, wrong=()):
    items = coach.card_items()
    results = [{"combo": it["combo"], "show": it["show"],
                "key": str(nr.degree(it["combo"]) % 6 + 2 if it["combo"] in wrong and not it["show"]
                           else nr.degree(it["combo"]))} for it in items]
    coach.record_cards(results)
    return items


def clear_cards(coach):
    while coach.step()["kind"] == "cards":
        answer_cards(coach)


class CoachTest(unittest.TestCase):
    def setUp(self):
        self.c = nr.Coach(rng=random.Random(1))
        self.c.ensure()

    def test_new_combos_are_shown_then_recalled_before_timing(self):
        c = self.c
        st = c.step()
        self.assertEqual(st["kind"], "cards")
        first_two = [c.combo(0), c.combo(1)]
        shown = answer_cards(c)
        self.assertEqual([it["combo"] for it in shown], first_two)
        self.assertTrue(all(it["show"] for it in shown))
        # recall: no answers shown; get one wrong and it comes back
        recall = answer_cards(c, wrong=[first_two[0]])
        self.assertFalse(any(it["show"] for it in recall))
        self.assertEqual(sorted(it["combo"] for it in recall), sorted(first_two))
        self.assertEqual(c.step()["kind"], "cards")
        again = answer_cards(c)
        self.assertEqual([it["combo"] for it in again], [first_two[0]])
        # now in time, at the start tempo
        self.assertEqual(c.step()["kind"], "drill")
        self.assertEqual(c.step()["tempo"], nr.START_BPM)

    def test_recall_mixes_in_learned_combos(self):
        c = self.c
        clear_cards(c)
        while c.step()["kind"] != "cards":      # first half until the second half's cards come up
            c.record_rep([{"i": i, "key": str(nr.degree(c.combo(i))), "off": 0.0} for i in c.rep_slots()])
        self.assertEqual(c.cur["i"], 1)
        answer_cards(c)                         # show
        recall = [it["combo"] for it in c.card_items()]
        self.assertGreater(len(recall), 2)      # the two new ones plus learned extras

    def test_clean_at_60_moves_on(self):
        c = self.c
        clear_cards(c)
        self.assertEqual(c.step()["tempo"], 60)
        answer_all(c)
        self.assertEqual(c.cur["i"], 1)

    def test_streak_climbs_back_to_target(self):
        c = self.c
        clear_cards(c)
        st = c.step()
        st["tempo"] = 42
        tempos = []
        while c.cur["i"] == 0:
            tempos.append(c.step()["tempo"])
            answer_all(c)
        self.assertEqual(tempos, [42, 48, 60])     # +6, +12 (capped)

    def test_wide_timing_window(self):
        clear_cards(self.c)
        self.assertTrue(all(answer_all(self.c, off=0.45)))
        clear_cards(self.c)
        self.assertFalse(any(answer_all(self.c, off=-0.55)))

    def test_one_or_two_misses_repeat_the_same_step(self):
        c = self.c
        while nr.step_name(c.step()) != "bars 1–2":
            answer_all(c)
        for _ in range(2):
            answer_all(c, ok=lambda r: r["i"] != 5)
            self.assertEqual(nr.step_name(c.step()), "bars 1–2")
            self.assertEqual(c.step()["tempo"], 60)
            self.assertEqual(c.cur["stack"], [])
        answer_all(c)                               # clean clears the misses and moves on
        self.assertEqual(nr.step_name(c.step()), "bar 3, first half")

    def test_misses_are_counted_in_a_row(self):
        c = self.c
        clear_cards(c)
        st = c.step()
        st["tempo"] = 54                            # below target so a clean rep doesn't finish it
        answer_all(c, ok=lambda r: r["i"] != 1)
        answer_all(c, ok=lambda r: r["i"] != 1)
        answer_all(c)
        answer_all(c, ok=lambda r: r["i"] != 1)
        self.assertEqual(st["misses"], 1)

    def test_third_miss_rebuilds_from_the_half(self):
        c = self.c
        while nr.step_name(c.step()) != "bars 1–2":
            answer_all(c)
        bad = 5                                     # second combo of bar 2
        for _ in range(3):
            answer_all(c, ok=lambda r: r["i"] != bad)
        self.assertEqual(nr.step_name(c.step()), "bar 2, first half")
        self.assertEqual(c.step()["tempo"], 60 - nr.BPM_STEP)
        answer_all(c)                               # one clean rep each, no climbing
        self.assertEqual(nr.step_name(c.step()), "bar 2")
        answer_all(c)
        self.assertEqual(nr.step_name(c.step()), "bars 1–2")
        self.assertEqual(c.step()["tempo"], 60 - nr.BPM_STEP)
        self.assertEqual(c.cur["stack"], [])
        answer_all(c)
        answer_all(c)
        self.assertEqual(nr.step_name(c.step()), "bar 3, first half")

    def test_third_miss_in_a_half_just_slows_it(self):
        c = self.c
        clear_cards(c)
        for _ in range(3):
            answer_all(c, ok=lambda r: r["i"] != 1)
        self.assertEqual(nr.step_name(c.step()), "bar 1, first half")
        self.assertEqual(c.step()["tempo"], 60 - nr.BPM_STEP)
        self.assertEqual(c.cur["stack"], [])

    def test_old_progress_is_migrated(self):
        c = self.c
        c.s["version"] = 1
        c.s["settings"].update(target=90, tolerance=0.25)
        clear_cards(c)
        c.step()["target"], c.step()["tempo"] = 90, 84
        with tempfile.TemporaryDirectory() as d:
            path = os.path.join(d, "state.json")
            nr.save_state(c.s, path)
            s = nr.load_state(path)
        self.assertEqual((s["settings"]["target"], s["settings"]["tolerance"]), (60, 0.5))
        self.assertEqual((s["current"]["steps"][0]["target"], s["current"]["steps"][0]["tempo"]), (60, 60))

    def test_alternation_has_a_gap(self):
        c = self.c
        while c.step()["kind"] != "alt":
            answer_all(c)
        self.assertEqual(c.rep_slots(), [0, 1, 2, 3, None, 4, 5, 6, 7])

    def test_whole_sequence_completes_and_next_starts(self):
        c = self.c
        first = list(c.cur["combos"])
        for _ in range(2000):
            answer_all(c)
            if c.s["done"]:
                break
        self.assertEqual(c.s["done"], 1)
        self.assertEqual(c.s["history"], [first])
        self.assertEqual(c.cur["n"], 2)
        self.assertTrue(any("complete" in e for e in c.events))


class PanelTest(unittest.TestCase):
    def test_panel_shows_all_bars_and_the_fix_up(self):
        c = nr.Coach(rng=random.Random(1))
        c.ensure()
        while nr.step_name(c.step()) != "bars 1–2":
            answer_all(c)
        for _ in range(3):
            answer_all(c, ok=lambda r: r["i"] != 5)
        plain = [re.sub(r"\x1b\[[0-9;]*m", "", l) for l in nr.panel_lines(c, playing=4)]
        self.assertEqual(len(plain), 3 + 2 * 3)
        for b in range(1, 9):
            self.assertTrue(any(f"bar {b}" in l for l in plain))
        self.assertIn("then back to bars 1–2", plain[1])
        self.assertIn("━━━ ─── ┄┄┄ ┄┄┄", plain[5])     # playing, rest of the half, the step it returns to
        self.assertEqual(len(nr.panel_lines(c, width=60)), 3 + 4 * 3)


class ComposerTest(unittest.TestCase):
    def test_sequences_are_varied_but_familiar(self):
        c = nr.Coach(rng=random.Random(3))
        seqs, pools = [], []
        for _ in range(8):
            c.new_sequence()
            seqs.append(c.cur["combos"])
            pools.append(list(c.s["pool"]))
        for seq, pool in zip(seqs, pools):
            self.assertEqual(len(seq), 32)
            self.assertTrue(all(a != b for a, b in zip(seq, seq[1:])), seq)
            self.assertTrue(set(seq) <= set(pool))
            for b in range(1, 8):    # each bar is a small change on the one before
                diff = sum(x != y for x, y in zip(seq[b * 4 - 4:b * 4], seq[b * 4:b * 4 + 4]))
                self.assertLessEqual(diff, 3)
        self.assertEqual(len(pools[0]), nr.POOL_START)
        for a, b in zip(pools, pools[1:]):
            self.assertLessEqual(len(set(b) - set(a)), nr.NOVEL_PER_SEQ)   # a little novelty each time
            self.assertGreaterEqual(len(set(a) & set(b)), len(a) - nr.DROP_PER_SEQ - 1)
        # novelty accumulates: more combos used over time
        used = [len(set(sum(seqs[:k], []))) for k in range(1, 9)]
        self.assertEqual(sorted(used), used)
        self.assertGreater(used[-1], used[0] + 8)

    def test_new_combos_feature(self):
        c = nr.Coach(rng=random.Random(4))
        c.new_sequence()
        c.new_sequence()
        for n in c.cur["novel"]:
            self.assertGreaterEqual(c.cur["combos"].count(n), 3)


class StorageTest(unittest.TestCase):
    def test_round_trip(self):
        c = nr.Coach(rng=random.Random(5))
        c.ensure()
        for _ in range(30):
            answer_all(c)
        with tempfile.TemporaryDirectory() as d:
            path = os.path.join(d, "x", "state.json")
            nr.save_state(c.s, path)
            c2 = nr.Coach(nr.load_state(path))
        self.assertEqual(c2.s, c.s)
        self.assertEqual(c2.rep_slots(), c.rep_slots())


if __name__ == "__main__":
    unittest.main()
