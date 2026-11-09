#!/usr/bin/env python3
"""NoteDist: drill note distances in degrees, one keypress per answer.

    C ↑ G = 5    B ↑ G = 6    G ↓ C = 5

Count from the first note as 1, in the direction of the arrow. Press 2-7 to
answer, s for stats, p to pause, q to quit. Progress is saved after every
answer, so you can stop and pick up again at any time.
"""

import argparse
import json
import math
import os
import random
import statistics
import sys
import time

# ------------------------------------------------------------------ theory

LETTERS = "CDEFGAB"
UP, DOWN = "u", "d"
ARROW = {UP: "↑", DOWN: "↓"}
ALL_COMBOS = [f"{a}{d}{b}" for a in LETTERS for b in LETTERS if a != b for d in (UP, DOWN)]


def degree(combo):
    a, d, b = combo
    ia, ib = LETTERS.index(a), LETTERS.index(b)
    steps = (ib - ia) % 7 if d == UP else (ia - ib) % 7
    return steps + 1


def label(combo):
    a, d, b = combo
    return f"{a} {ARROW[d]} {b}"


# ------------------------------------------------------------------ tuning

ALPHA = 0.3             # EWMA weight of the newest answer
TIME_CAP = 15.0         # longer answers count as this (you were probably distracted)
DEFAULT_BENCH = 2.5     # benchmark seconds before there is any data
RECENT_TIMES = 80       # correct-answer times kept for the benchmark
RECENT = 40             # answers kept for momentum and group forming
WARMUP = 12             # random questions on the very first run
CHECK_EVERY = 25        # questions between checks for due reviews
NEW_GROUP_LEVEL = 0.4   # level needed before new material is introduced
MASTER_ACC = 0.9        # per-combo accuracy counted as mastered
MASTER_SLACK = 1.4      # per-combo time allowed, relative to the group's best
GRAD_ACC = 0.9          # random-mode accuracy needed to graduate a group
GRAD_TIME = 1.6         # random-mode median time allowed, relative to the benchmark
GRAD_MASTERY = 0.75
SR_START = 30           # first review interval, in questions
SR_GROWTH = 2.5
REVIEW_OK = 0.15        # review badness at or under this is a pass
REVIEW_RELEARN = 0.4    # review badness over this sends the group back to learning
MAX_SEQUENCES = 40      # saved sequences per group
SEQ_LEN = 3             # combos per sequence
MAX_SEQS = 6            # sequences per group before shuffled and random order
FAST = 1.25             # a block is good when it's all right with median time under this × benchmark
STEP_PATIENCE = 12      # rounds after which shuffle/random moves on if it's at least 85% right
BLOCK_MIN = 3           # plays a block needs at least; good in this many = good straight away
BLOCK_PATIENCE = 10     # plays after which a block moves on if it's at least 85% right
BLOCK_WINDOW = 4        # most recent sequences checked in each round


def clamp(x, lo=0.0, hi=1.0):
    return max(lo, min(hi, x))


def percentile(xs, p):
    s = sorted(xs)
    if not s:
        return None
    k = (len(s) - 1) * p
    f = math.floor(k)
    c = min(f + 1, len(s) - 1)
    return s[f] + (s[c] - s[f]) * (k - f)


def new_state():
    return {
        "version": 1,
        "q": 0,               # questions answered, ever: the clock for spaced repetition
        "level": 0.3,         # overall difficulty, 0 = struggling, 1 = flying
        "combos": {},         # combo -> {"acc", "lt", "n", "last"}
        "recent_times": [],   # recent correct-answer times, for the benchmark
        "recent": [],         # recent answers as [combo, quality]
        "groups": [],
        "active": None,       # id of the group being learned
        "reactivate": [],     # groups that failed a review badly and wait to be relearned
        "extra": {},          # combo -> extra reps owed after a bad review
    }


def item(combo, mode, gid=None, sid=None):
    return {"combo": combo, "mode": mode, "gid": gid, "sid": sid, "end": False}


def seq_name(sid):
    """1 -> A, 26 -> Z, 27 -> AA."""
    name = ""
    while sid:
        sid, r = divmod(sid - 1, 26)
        name = chr(65 + r) + name
    return name


# ------------------------------------------------------------------ scheduler

class Trainer:
    """Decides what to ask next and learns from each answer.

    It works without a terminal: call next_item(), then record() with the key
    pressed and the seconds taken. All lasting state lives in self.s.
    """

    def __init__(self, state=None, rng=None):
        self.s = state or new_state()
        self.rng = rng or random.Random()
        self.queue = []
        self.forming = None        # size of the group to form once the explore burst is answered
        self.review = None         # review in progress: {"gid", "results"}
        self.since_check = CHECK_EVERY   # so due reviews come first in a session
        self.events = []           # messages for the UI

    # -- measures

    def bench(self):
        """Your current fast time: the 20th percentile of recent correct answers."""
        return percentile(self.s["recent_times"], 0.2) or DEFAULT_BENCH

    def stat(self, c):
        return self.s["combos"].get(c)

    def ctime(self, c):
        st = self.stat(c)
        return math.exp(st["lt"]) if st and st["lt"] is not None else None

    def struggle(self, c):
        """0 = easy for you right now, 1 = hard. Relative to your benchmark."""
        st = self.stat(c)
        if not st or st["n"] == 0:
            return 0.8
        t = self.ctime(c)
        slow = 0.5 if t is None else clamp((t / self.bench() - 1) / 2)
        return clamp(0.6 * (1 - st["acc"]) + 0.4 * slow)

    def quality(self, correct, t):
        return 0.4 + 0.6 * min(1.0, self.bench() / t) if correct else 0.0

    def group(self, gid):
        return self.s["groups"][gid - 1]

    def group_mastery(self, g):
        times = [self.ctime(c) for c in g["members"]]
        known = [t for t in times if t]
        if not known:
            return 0.0
        ref = max(min(known), 0.75 * self.bench())
        ok = 0
        for c, t in zip(g["members"], times):
            st = self.stat(c)
            if st and t and st["acc"] >= MASTER_ACC and t <= MASTER_SLACK * ref:
                ok += 1
        return ok / len(g["members"])

    def group_struggle(self, g):
        return sum(self.struggle(c) for c in g["members"]) / len(g["members"])

    def group_size(self):
        return 5 + round(2 * self.s["level"])

    def due_groups(self):
        q = self.s["q"]
        due = [g for g in self.s["groups"]
               if g["state"] == "review" and q >= g["sr_last"] + g["sr_interval"]]
        return sorted(due, key=lambda g: g["sr_last"] + g["sr_interval"])

    def due_in(self, g):
        return g["sr_last"] + g["sr_interval"] - self.s["q"]

    # -- planning

    def next_item(self):
        while not self.queue:
            self.plan()
        return self.queue.pop(0)

    def plan(self):
        s = self.s
        if self.forming is not None:
            self.form_group(self.forming)
        if self.since_check >= CHECK_EVERY and self.at_boundary():
            self.since_check = 0
            due = self.due_groups()
            if due:
                self.start_review(due[0])
                return
        if s["active"] is None and s["reactivate"]:
            s["active"] = s["reactivate"].pop(0)
        if s["active"] is not None:
            self.sequence_block(self.group(s["active"]))
            return
        if not s["groups"]:
            if s["q"] < WARMUP:
                self.queue = [item(c, "warm") for c in self.rng.sample(ALL_COMBOS, WARMUP - s["q"])]
                return
            self.form_group(self.group_size())
            self.sequence_block(self.group(s["active"]))
            return
        if s["level"] >= NEW_GROUP_LEVEL and self.start_explore():
            return
        learned = [g for g in s["groups"] if g["state"] == "review"]
        if s["level"] < NEW_GROUP_LEVEL and learned:
            # struggling: go back over the learned group you find hardest, for some wins
            self.sequence_block(max(learned, key=self.group_struggle))
            return
        self.mix_block()

    def at_boundary(self):
        """Not partway through a block, so a review can come in without splitting it."""
        if self.s["active"] is None:
            return True
        g = self.group(self.s["active"])
        return (g.get("phase") != "blocks" or not g.get("block_plays")
                or self.block_verdict(g) is not None)

    def start_explore(self):
        """Show a few combos not in any group yet; the next group is formed from them."""
        s = self.s
        grouped = {c for g in s["groups"] for c in g["members"]}
        fresh = [c for c in ALL_COMBOS if c not in grouped]
        if not fresh:
            return False
        n = self.group_size()
        prev = s["groups"][-1]
        n_overlap = 1 + (s["level"] > 0.6)
        overlap = sorted(prev["members"], key=self.struggle, reverse=True)[:n_overlap]
        burst = self.rng.sample(fresh, min(len(fresh), n - len(overlap)))
        items = burst + overlap
        self.rng.shuffle(items)
        self.queue = [item(c, "new") for c in items]
        self.forming = len(items)
        return True

    def form_group(self, n):
        members = []
        for c, _ in reversed(self.s["recent"]):
            if c not in members:
                members.append(c)
            if len(members) == n:
                break
        members.reverse()
        g = {"id": len(self.s["groups"]) + 1, "members": members, "state": "active",
             "mastery": 0.0, "sequences": [], "next_sid": 1, "rand_log": [],
             "seqs": [], "phase": "blocks", "rounds": 0, "step_log": [],
             "sr_interval": 0, "sr_last": 0, "reviews": 0, "created": self.s["q"]}
        self.s["groups"].append(g)
        self.s["active"] = g["id"]
        self.forming = None
        self.events.append(f"New group {g['id']}: " + "  ".join(label(c) for c in members))

    def start_review(self, g):
        members = list(g["members"])
        self.rng.shuffle(members)
        self.queue = [item(c, "review", g["id"]) for c in members]
        self.review = {"gid": g["id"], "results": []}
        self.events.append(f"Review of group {g['id']}")

    def mix_block(self):
        """Everything is grouped and learned: random practice over all, leaning on weak spots."""
        weights = [0.3 + self.struggle(c) for c in ALL_COMBOS]
        plays = [[item(c, "mix")] for c in self.rng.choices(ALL_COMBOS, weights, k=8)]
        self.weave_extra(plays)
        self.queue = [it for play in plays for it in play]

    # -- the build-up within a group
    #
    # Each sequence is 3 combos, played in blocks: the same sequence over and over
    # until it's right and fast. A new sequence gets its own block first. Then
    # every sequence so far is checked in turn, a block each, round after round:
    #   A A A A …   B B B B B …   A A A …   B B B …   A A …   B B   (both good straight away)
    #   C C C C …   A A …   B B B …   C C …   A A   B B   C C     (all good straight away)
    #   D D D …
    # Only a round where every block is good straight away lets the next sequence in.
    # After the last one: every sequence in shuffled order, then random combos from
    # the group, which is where the group can graduate.

    def sequence_block(self, g):
        """Queue the next play of the current block, or the next round in shuffle/random."""
        self.migrate(g)
        if not g["seqs"]:
            self.introduce(g)
        between = False
        if g["phase"] == "blocks" and g["block_plays"]:
            between = self.block_done(g)
        if g["phase"] in ("shuffle", "random"):
            self.advance_late(g)
        plays = [[]] if between else []     # owed reps can go between blocks
        if g["phase"] == "blocks":
            plays.append(self.play(g, self.seq(g, g["order"][g["pos"]])))
            g["block_plays"] += 1
        else:
            if g["phase"] == "random":
                plays += [[item(self.pick_weak(g), "rand", g["id"])] for _ in g["members"]]
            else:
                order = [self.seq(g, sid) for sid in g["seqs"]]
                self.rng.shuffle(order)
                plays += [self.play(g, seq) for seq in order]
            g["rounds"] += 1
            between = True
        if between:
            self.weave_extra(plays)
        self.queue = [it for play in plays for it in play]

    def play(self, g, seq):
        play = [item(c, "seq", g["id"], seq["id"]) for c in seq["items"]]
        play[-1]["end"] = True
        return play

    def block_verdict(self, g):
        """'good' when the last BLOCK_MIN plays are all right and fast; 'enough' if it's long and nearly there."""
        log = g["step_log"]
        n = BLOCK_MIN * SEQ_LEN
        if len(log) >= n:
            last = log[-n:]
            if all(x[0] for x in last) and statistics.median(x[1] for x in last) <= FAST * self.bench():
                return "good"
        if g["block_plays"] >= BLOCK_PATIENCE:
            last = log[-3 * SEQ_LEN:]
            if sum(x[0] for x in last) >= 0.85 * len(last):
                return "enough"
        return None

    def block_done(self, g):
        """Check the block that's playing; if it's done, move to the next block. True if moved."""
        verdict = self.block_verdict(g)
        if not verdict:
            return False
        # good straight away: right and fast from the first play of the block
        g["clean"] = g["clean"] and verdict == "good" and g["block_plays"] == BLOCK_MIN
        g["pos"] += 1
        g["block_plays"] = 0
        g["step_log"] = []
        if g["pos"] < len(g["order"]):
            return True
        if g["intro"] and len(g["seqs"]) == 1:
            self.introduce(g)               # nothing to check A against yet: straight on to B
        elif g["intro"] or not g["clean"]:
            self.start_round(g)
        elif self.ready_for_shuffle(g):
            self.set_late(g, "shuffle")
        else:
            names = " ".join(seq_name(sid) for sid in g["order"])
            self.events.append(f"Group {g['id']}: {names} all good straight away")
            self.introduce(g)
        return True

    def start_round(self, g):
        """A block of each sequence in play, oldest first."""
        g.update(order=g["seqs"][-BLOCK_WINDOW:], pos=0, block_plays=0, step_log=[],
                 clean=True, intro=False)
        g["round_no"] = g.get("round_no", 0) + 1
        names = " ".join(seq_name(sid) for sid in g["order"])
        self.events.append(f"Group {g['id']}: checking {names}" + (" again" if g["round_no"] > 1 else ""))

    def migrate(self, g):
        if "seqs" not in g:
            # saved by an earlier version: start its sequences afresh from A
            g.update(sequences=[], next_sid=1, seqs=[], rand_log=[])
            for k in ("core", "newbie", "stage", "calm"):
                g.pop(k, None)
        if "order" not in g and g["phase"] not in ("shuffle", "random"):
            g["phase"] = "blocks"
            g["rounds"] = 0
            if g["seqs"]:
                self.start_round(g)

    def cycle_len(self, g):
        if g["phase"] == "random":
            return len(g["members"])
        return sum(len(self.seq(g, sid)["items"]) for sid in g["seqs"])

    def step_verdict(self, g):
        """For shuffle and random order: 'good' when a stretch is all right and fast."""
        n = max(9, self.cycle_len(g))
        log = g["step_log"][-n:]
        if len(log) < n:
            return None
        acc = sum(x[0] for x in log) / n
        times = [x[1] for x in log if x[0]]
        if acc == 1 and statistics.median(times) <= FAST * self.bench():
            return "good"
        if g["rounds"] >= STEP_PATIENCE and acc >= 0.85:
            return "enough"
        if g["rounds"] >= 4 and acc < 0.5:
            return "lost"
        return None

    def advance_late(self, g):
        verdict = self.step_verdict(g)
        if g["phase"] == "random":
            # graduation is checked answer by answer; if random is too much, go back a step
            if verdict == "lost":
                self.set_late(g, "shuffle")
        elif verdict == "lost":
            g["phase"] = "blocks"
            self.start_round(g)
        elif verdict:
            self.set_late(g, "random")

    def ready_for_shuffle(self, g):
        if len(g["seqs"]) >= MAX_SEQS:
            return True
        covered = {c for sid in g["seqs"] for c in self.seq(g, sid)["items"]}
        return (len(g["seqs"]) >= 4 and set(g["members"]) <= covered
                and self.group_mastery(g) >= 0.7)

    def set_late(self, g, phase):
        g["phase"] = phase
        g["rounds"] = 0
        g["step_log"] = []
        self.events.append(f"Group {g['id']}: " + ("now random order" if phase == "random"
                                                  else "all sequences, shuffled"))

    def introduce(self, g):
        """Add a 3-combo sequence: combos not practised yet first, then old ones in new company."""
        members = g["members"]
        used = [c for sid in g["seqs"] for c in self.seq(g, sid)["items"]]
        fresh = [c for c in members if c not in used]
        self.rng.shuffle(fresh)
        picks = fresh[:SEQ_LEN]
        existing = [set(self.seq(g, sid)["items"]) for sid in g["seqs"]]
        for _ in range(20):
            rest = sorted((c for c in members if c not in picks),
                          key=lambda c: (used.count(c), self.rng.random()))
            items = picks + rest[:SEQ_LEN - len(picks)]
            self.rng.shuffle(items)
            if set(items) not in existing:
                break
            picks = fresh[:max(0, len(picks) - 1)]
        seq = self.save_sequence(g, items)
        g["seqs"].append(seq["id"])
        g.update(phase="blocks", order=[seq["id"]], pos=0, block_plays=0, step_log=[],
                 clean=True, intro=True, round_no=0)
        self.events.append(f"Group {g['id']}: new sequence {seq_name(seq['id'])}: "
                           + "  ".join(label(c) for c in items))

    def seq(self, g, sid):
        return next(s for s in g["sequences"] if s["id"] == sid)

    def weave_extra(self, plays):
        """Owed reps go between plays, so the sequences themselves stay intact."""
        extra = self.s["extra"]
        owed = sorted((c for c in extra if extra[c] > 0), key=lambda c: -extra[c])[:2]
        for c in owed:
            plays.insert(self.rng.randint(1, len(plays)), [item(c, "rep")])
            extra[c] -= 1
            if extra[c] <= 0:
                del extra[c]

    def pick_weak(self, g):
        return self.rng.choices(g["members"], [0.5 + self.struggle(c) for c in g["members"]])[0]

    def save_sequence(self, g, items):
        for seq in g["sequences"]:
            if seq["items"] == items:
                return seq
        seq = {"id": g["next_sid"], "items": items, "n": 0, "ok": 0, "tsum": 0.0, "best": None}
        g["next_sid"] += 1
        if len(g["sequences"]) >= MAX_SEQUENCES:
            g["sequences"].remove(min((s for s in g["sequences"] if s["id"] not in g["seqs"]),
                                      key=lambda s: s["n"]))
        g["sequences"].append(seq)
        return seq

    # -- learning from answers

    def record(self, it, key, seconds):
        s = self.s
        c = it["combo"]
        t = clamp(seconds, 0.05, TIME_CAP)
        correct = int(key) == degree(c)
        struggle = self.struggle(c)
        q = self.quality(correct, t)

        st = s["combos"].setdefault(c, {"acc": 0.5, "lt": None, "n": 0, "last": -1})
        st["acc"] += ALPHA * (float(correct) - st["acc"])
        if correct:
            lt = math.log(t)
            st["lt"] = lt if st["lt"] is None else st["lt"] + ALPHA * (lt - st["lt"])
            s["recent_times"] = (s["recent_times"] + [t])[-RECENT_TIMES:]
        st["n"] += 1
        st["last"] = s["q"]
        s["q"] += 1
        self.since_check += 1
        s["recent"] = (s["recent"] + [[c, q]])[-RECENT:]
        self.update_level(correct, q, struggle)

        if it["gid"]:
            g = self.group(it["gid"])
            if it["mode"] == "seq":
                seq = next((x for x in g["sequences"] if x["id"] == it["sid"]), None)
                if seq:
                    seq["n"] += 1
                    seq["ok"] += correct
                    seq["tsum"] += t
                    if correct and (seq["best"] is None or t < seq["best"]):
                        seq["best"] = t
            elif it["mode"] == "rand":
                g["rand_log"] = (g["rand_log"] + [[int(correct), t]])[-30:]
            if it["mode"] in ("seq", "rand") and "step_log" in g:
                g["step_log"] = (g["step_log"] + [[int(correct), t]])[-40:]
            g["mastery"] += 0.3 * (self.group_mastery(g) - g["mastery"])
            if g["state"] == "active" and it["mode"] != "review":
                self.check_graduation(g)
            if it["mode"] == "review" and self.review and self.review["gid"] == g["id"]:
                self.review["results"].append([c, correct, t])
                if len(self.review["results"]) == len(g["members"]):
                    self.finish_review(g)
        return correct

    def update_level(self, correct, q, struggle):
        D = self.s["level"]
        if correct:
            # getting hard things right fast lifts the level most
            D += 0.03 * (0.5 + struggle) * clamp((q - 0.6) / 0.4, -1, 1)
        else:
            # missing easy things drops it most
            D -= 0.12 * (1.5 - struggle)
        qs = [r[1] for r in self.s["recent"][-8:]][::-1]
        if len(qs) >= 4:
            w = [0.7 ** i for i in range(len(qs))]
            momentum = sum(a * b for a, b in zip(qs, w)) / sum(w)
            if momentum < 0.4:
                D -= 0.03
            elif momentum > 0.85:
                D += 0.01
        self.s["level"] = clamp(D)

    def check_graduation(self, g):
        if g.get("phase") != "random":
            return
        n = 2 * len(g["members"])
        log = g["rand_log"][-n:]
        if len(log) < n:
            return
        acc = sum(x[0] for x in log) / n
        times = [x[1] for x in log if x[0]]
        if (acc >= GRAD_ACC and statistics.median(times) <= GRAD_TIME * self.bench()
                and g["mastery"] >= GRAD_MASTERY):
            g["state"] = "review"
            g["sr_interval"] = SR_START
            g["sr_last"] = self.s["q"]
            if self.s["active"] == g["id"]:
                self.s["active"] = None
            self.queue = []
            self.events.append(f"★ Group {g['id']} mastered. First check in {SR_START} questions.")

    def finish_review(self, g):
        s = self.s
        bench = self.bench()
        bads = []
        for c, correct, t in self.review["results"]:
            # a miss counts 1; right but slow counts up to half a miss
            b = 0.5 * clamp((t / bench - 1.5) / 3) if correct else 1.0
            bads.append((c, b))
        self.review = None
        badness = sum(b for _, b in bads) / len(bads)
        g["reviews"] += 1
        g["sr_last"] = s["q"]
        if badness <= REVIEW_OK:
            g["sr_interval"] = round(g["sr_interval"] * SR_GROWTH)
            self.events.append(f"✓ Group {g['id']} still solid. Next check in {g['sr_interval']} questions.")
            return
        g["sr_interval"] = max(SR_START, round(g["sr_interval"] * (1 - badness)))
        for c, b in bads:
            if b > REVIEW_OK:
                s["extra"][c] = s["extra"].get(c, 0) + math.ceil(b * 4)
        if badness > REVIEW_RELEARN:
            g["state"] = "active"
            g["mastery"] *= 0.5
            g["rand_log"] = []
            if g.get("seqs"):
                g.update(phase="shuffle", rounds=0, step_log=[])
            if s["active"] is None:
                s["active"] = g["id"]
            elif g["id"] not in s["reactivate"]:
                s["reactivate"].append(g["id"])
            self.events.append(f"✗ Group {g['id']} slipped ({badness:.0%}). Back to learning it.")
        else:
            self.events.append(f"~ Group {g['id']} a bit rusty ({badness:.0%}). Extra reps added; "
                               f"next check in {g['sr_interval']} questions.")


# ------------------------------------------------------------------ storage

def data_dir():
    base = os.environ.get("XDG_DATA_HOME") or os.path.expanduser("~/.local/share")
    return os.path.join(base, "notedist")


def load_state(path):
    if os.path.exists(path):
        with open(path) as f:
            return json.load(f)
    return new_state()


def save_state(state, path):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    tmp = path + ".tmp"
    with open(tmp, "w") as f:
        json.dump(state, f)
    os.replace(tmp, path)


def log_answer(path, record):
    with open(path, "a") as f:
        f.write(json.dumps(record) + "\n")


# ------------------------------------------------------------------ terminal UI

COLOR = sys.stdout.isatty() and not os.environ.get("NO_COLOR")


def paint(text, code):
    return f"\033[{code}m{text}\033[0m" if COLOR else text


def green(t): return paint(t, "32")
def red(t): return paint(t, "31")
def yellow(t): return paint(t, "33")
def dim(t): return paint(t, "2")
def bold(t): return paint(t, "1")


MODE_NAMES = {"warm": "warm-up", "new": "new", "seq": "seq", "rand": "random",
              "rep": "repeat", "review": "review", "mix": "mix"}


def tag(tr, it):
    g = f"G{it['gid']}" if it["gid"] else "--"
    mode = f"seq {seq_name(it['sid'])}" if it["mode"] == "seq" else MODE_NAMES[it["mode"]]
    return dim(f"[{g} · {mode:<7} · lvl {tr.s['level']:.2f}]")


def struggle_color(tr, c, text):
    s = tr.struggle(c)
    return green(text) if s < 0.25 else yellow(text) if s < 0.5 else red(text)


def stats_text(tr):
    s = tr.s
    lines = ["", bold("Stats"),
             f"  answered {s['q']}   level {s['level']:.2f}   benchmark {tr.bench():.2f}s", ""]
    for d in (UP, DOWN):
        lines.append(f"  {ARROW[d]}  " + "".join(f"{b:>5}" for b in LETTERS)
                     + dim("   (typical seconds; green easy, red hard)" if d == UP else ""))
        for a in LETTERS:
            row = f"  {a}  "
            for b in LETTERS:
                c = f"{a}{d}{b}"
                if a == b:
                    row += dim("    ·")
                elif not tr.stat(c):
                    row += dim("    -")
                else:
                    t = tr.ctime(c)
                    row += struggle_color(tr, c, f"{t:5.1f}" if t else "    ✗")
            lines.append(row)
        lines.append("")
    if s["groups"]:
        lines.append(bold("Groups"))
        for g in s["groups"]:
            if g["state"] == "active":
                st = f"learning, mastery {g['mastery']:.0%}"
            else:
                due = tr.due_in(g)
                st = f"learned, reviews {g['reviews']}, " + ("due now" if due <= 0 else f"due in {due} questions")
            members = " ".join(struggle_color(tr, c, label(c).replace(" ", "")) for c in g["members"])
            lines.append(f"  G{g['id']:<3}{members}   {dim(st)}")
            if g["state"] == "active" and g.get("seqs"):
                for sid in g["seqs"]:
                    seq = tr.seq(g, sid)
                    lines.append(dim(f"       {seq_name(sid)}: " + " ".join(label(c).replace(" ", "") for c in seq["items"])))
                if g["phase"] in ("shuffle", "random"):
                    now = "all sequences shuffled" if g["phase"] == "shuffle" else "random order"
                elif g.get("order"):
                    now = (("new " if g["intro"] else "checking ")
                           + " ".join(("[" + seq_name(x) + "]") if i == g["pos"] else seq_name(x)
                                      for i, x in enumerate(g["order"])))
                lines.append(dim(f"       now: {now}"))
    if s["extra"]:
        lines.append("  extra reps owed: " + ", ".join(f"{label(c)} ×{n}" for c, n in s["extra"].items()))
    lines.append("")
    return "\n".join(lines)


def run(state_path, log_path):
    import termios
    import tty

    tr = Trainer(load_state(state_path))
    fd = sys.stdin.fileno()
    old = termios.tcgetattr(fd)
    answered = right = 0
    total_time = 0.0
    print(bold("NoteDist") + dim("  press 2-7 to answer · s stats · p pause · q quit"))
    tty.setcbreak(fd)
    try:
        while True:
            for e in tr.events:
                print(yellow(e))
            tr.events.clear()
            it = tr.next_item()
            for e in tr.events:
                print(yellow(e))
            tr.events.clear()
            prompt = f"{tag(tr, it)}  {bold(label(it['combo']))}  "
            termios.tcflush(fd, termios.TCIFLUSH)
            sys.stdout.write(prompt)
            sys.stdout.flush()
            t0 = time.monotonic()
            while True:
                k = sys.stdin.read(1)
                if k in "234567" and k:
                    break
                if k in ("q", ""):
                    raise KeyboardInterrupt
                if k == "s":
                    print(stats_text(tr))
                elif k == "p":
                    sys.stdout.write("\n" + dim("paused, press any key to carry on") + "\n")
                    sys.stdout.flush()
                    sys.stdin.read(1)
                else:
                    continue
                termios.tcflush(fd, termios.TCIFLUSH)
                sys.stdout.write(prompt)
                sys.stdout.flush()
                t0 = time.monotonic()
            t = time.monotonic() - t0
            level = tr.s["level"]
            correct = tr.record(it, k, t)
            answered += 1
            right += correct
            total_time += min(t, TIME_CAP)
            mark = green(f"{k} ✓") if correct else red(f"{k} ✗ {degree(it['combo'])}")
            print(f"{mark}  {dim(f'{t:.1f}s')}")
            save_state(tr.s, state_path)
            log_answer(log_path, {"at": time.time(), "q": tr.s["q"], "combo": it["combo"], "key": k,
                                  "correct": correct, "seconds": round(t, 3), "mode": it["mode"],
                                  "group": it["gid"], "sequence": it["sid"], "level": round(level, 3)})
    except KeyboardInterrupt:
        pass
    finally:
        termios.tcsetattr(fd, termios.TCSADRAIN, old)
        save_state(tr.s, state_path)
    if answered:
        print(f"\n\nSession: {answered} answered, {right / answered:.0%} right, "
              f"{total_time / answered:.1f}s average. Saved.")
    else:
        print("\n")


def main():
    p = argparse.ArgumentParser(description="Drill note distances in degrees.")
    p.add_argument("--data", default=data_dir(), help="folder for progress files (default: %(default)s)")
    p.add_argument("--stats", action="store_true", help="print stats and exit")
    p.add_argument("--reset", action="store_true", help="start from scratch (keeps the answer log)")
    args = p.parse_args()
    state_path = os.path.join(args.data, "state.json")
    log_path = os.path.join(args.data, "answers.jsonl")
    os.makedirs(args.data, exist_ok=True)
    if args.reset and os.path.exists(state_path):
        os.replace(state_path, state_path + ".bak")
        print(f"Old progress moved to {state_path}.bak")
    if args.stats:
        print(stats_text(Trainer(load_state(state_path))))
        return
    if not sys.stdin.isatty():
        sys.exit("NoteDist needs an interactive terminal.")
    run(state_path, log_path)


if __name__ == "__main__":
    main()
