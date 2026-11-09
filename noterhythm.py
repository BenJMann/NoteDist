#!/usr/bin/env python3
"""NoteRhythm: learn ascending note distances in time with a metronome.

    C → G = 5    B → G = 6    A → C = 3

Count up from the first note as 1. Each prompt appears on a beat and you answer
(2-7) on the next beat. Answers that are wrong, missing, or too far off the beat
fail. Sequences are built up two combos at a time: halves, bars, pairs of bars,
up to 8 bars. Keys: 2-7 answer · p pause · q quit.
"""

import argparse
import json
import math
import os
import random
import select
import shutil
import struct
import subprocess
import sys
import tempfile
import time
import wave
from collections import Counter

# ------------------------------------------------------------------ theory

LETTERS = "CDEFGAB"
ALL_COMBOS = [a + b for a in LETTERS for b in LETTERS if a != b]


def degree(combo):
    return (LETTERS.index(combo[1]) - LETTERS.index(combo[0])) % 7 + 1


def label(combo):
    return f"{combo[0]} → {combo[1]}"


def counting(combo):
    """C → G counted out: C D E F G."""
    i = LETTERS.index(combo[0])
    return " ".join(LETTERS[(i + k) % 7] for k in range(degree(combo)))


# ------------------------------------------------------------------ tuning

HALF = 2                # combos in half a bar
BAR = 4                 # combos in a bar
BARS = 8                # bars in a sequence
START_BPM = 60          # tempo new material starts at
TARGET_BPM = 60         # tempo a step has to be clean at to count as done
MIN_BPM = 40
BPM_STEP = 6            # tempo change after a clean or failed repetition
TOLERANCE = 0.5         # how far off the beat an answer may be, as a fraction of a beat
STRIKES = 3             # misses in a row before a step is broken down
COUNT_IN = 4            # beats counted in, on screen, before every repetition
POOL_START = 6          # combos the first sequence is made from
POOL_MAX = 12
NOVEL_PER_SEQ = 2       # combos brought in with each new sequence
DROP_PER_SEQ = 1        # best-known combos left out of each new sequence


def new_state():
    return {
        "version": 2,
        "settings": {"target": TARGET_BPM, "start": START_BPM, "tolerance": TOLERANCE,
                     "latency_ms": 0, "sound": True},
        "combos": {},       # combo -> {"n", "ok", "off"}: answers, right-and-in-time, mean |offset| in beats
        "usage": {},        # combo -> times used in sequences
        "pool": [],         # combos the current sequence draws on
        "done": 0,          # sequences completed
        "history": [],      # completed sequences' combos
        "current": None,    # sequence being learned
    }


# ------------------------------------------------------------------ build plan
#
# A sequence is 8 bars of 4 combos. It's built up like learning a piece:
#   bar 1: first half, second half, whole bar
#   bar 2: the same
#   bars 1 and 2 alternating, then bars 1-2 together
#   bars 3-4 the same way, then bars 1-4
#   bars 5-8 the same way as 1-4, then bars 1-8

def drill(s, e):
    return {"kind": "drill", "units": [[s, e]]}


def bar_steps(b):
    s = b * BAR
    return [drill(s, s + HALF), drill(s + HALF, s + BAR), drill(s, s + BAR)]


def pair_steps(b):
    s = b * BAR
    return (bar_steps(b) + bar_steps(b + 1)
            + [{"kind": "alt", "units": [[s, s + BAR], [s + BAR, s + 2 * BAR]]}, drill(s, s + 2 * BAR)])


def build_plan():
    half = BARS // 2 * BAR
    return (pair_steps(0) + pair_steps(2) + [drill(0, half)]
            + pair_steps(4) + pair_steps(6) + [drill(half, 2 * half)]
            + [drill(0, 2 * half)])


def span(step):
    return min(u[0] for u in step["units"]), max(u[1] for u in step["units"])


def bars_name(s, e):
    first, last = s // BAR + 1, (e - 1) // BAR + 1
    return f"bar {first}" if first == last else f"bars {first}–{last}"


def step_name(step):
    if step["kind"] == "cards":
        return "new combos" if step["new"] else "quick check"
    s, e = span(step)
    if step["kind"] == "alt":
        a, b = step["units"]
        return f"bars {a[0] // BAR + 1} and {b[0] // BAR + 1} alternating"
    if e - s == HALF:
        return f"{bars_name(s, e)}, {'first' if s % BAR == 0 else 'second'} half"
    return bars_name(s, e)


# ------------------------------------------------------------------ coach

class Coach:
    """Decides what to play and learns from each repetition. Works without a terminal."""

    def __init__(self, state=None, rng=None):
        self.s = state or new_state()
        self.rng = rng or random.Random()
        self.events = []        # messages for the UI

    @property
    def cur(self):
        return self.s["current"]

    @property
    def settings(self):
        return self.s["settings"]

    def ensure(self):
        """Ready to play: a sequence exists and the step on top has been started."""
        if not self.cur:
            self.new_sequence()
            return
        # fix-ups left over from the last session are dropped: carry on with the plan itself
        self.cur["stack"] = []
        self.begin()

    def step(self):
        cur = self.cur
        return cur["stack"][-1] if cur["stack"] else cur["steps"][cur["i"]]

    def combo(self, i):
        return self.cur["combos"][i]

    def rep_slots(self):
        """One repetition of the current step: combo positions, None for a gap of one combo."""
        st = self.step()
        slots = []
        for k, (s, e) in enumerate(st["units"]):
            if k:
                slots.append(None)
            slots += list(range(s, e))
        return slots

    def describe(self, st):
        s, e = span(st)
        combos = "  ".join(label(self.combo(i)) for i in range(s, e)) if e - s <= BAR else ""
        return step_name(st) + (f":  {combos}" if combos else "")

    # -- knowledge

    def knowledge(self, c):
        st = self.s["combos"].get(c)
        if not st or not st["n"]:
            return 0.0
        return st["ok"] / st["n"] * min(1.0, st["n"] / 20)

    def familiar(self, c):
        st = self.s["combos"].get(c)
        return bool(st) and st["n"] >= 12 and st["ok"] / st["n"] >= 0.9

    # -- composing sequences

    def next_pool(self):
        """Keep most of the last pool, leave out what you know best, bring in a little novelty."""
        pool = list(self.s["pool"])
        usage = self.s["usage"]
        unused = sorted((c for c in ALL_COMBOS if c not in pool),
                        key=lambda c: (usage.get(c, 0), self.rng.random()))
        if not pool:
            novel = unused[:POOL_START]
            return novel, novel
        drop = DROP_PER_SEQ + max(0, len(pool) + NOVEL_PER_SEQ - DROP_PER_SEQ - POOL_MAX)
        best = sorted(pool, key=self.knowledge, reverse=True)[:drop]
        pool = [c for c in pool if c not in best]
        novel = unused[:NOVEL_PER_SEQ]
        return pool + novel, novel

    def compose(self, pool, novel):
        """8 bars; each bar is the one before with a small change, new combos favoured."""
        seq = []

        def pick(exclude, ctx):
            counts = Counter(ctx)
            options = [c for c in pool if c not in exclude] or [c for c in ALL_COMBOS if c not in exclude]
            return min(options, key=lambda c: (counts[c] - (2 if c in novel else 0), self.rng.random()))

        bar = []
        for _ in range(BAR):
            bar.append(pick(set(bar), bar))
        seq += bar
        for b in range(1, BARS):
            bar = list(seq[-BAR:])
            for p in self.rng.sample(range(BAR), 1 if b % 2 else 2):
                before = seq[-1] if p == 0 else bar[p - 1]
                after = bar[p + 1] if p + 1 < BAR else None
                bar[p] = pick({bar[p], before, after}, seq + bar)
            if bar[0] == seq[-1]:
                bar[0] = pick({bar[0], bar[1], seq[-1]}, seq + bar)
            seq += bar
        return seq

    def new_sequence(self):
        pool, novel = self.next_pool()
        combos = self.compose(pool, novel)
        self.s["pool"] = pool
        for c in combos:
            self.s["usage"][c] = self.s["usage"].get(c, 0) + 1
        self.s["current"] = {"n": self.s["done"] + 1, "combos": combos, "novel": novel,
                             "steps": build_plan(), "i": 0, "stack": []}
        self.events.append(f"New sequence {self.cur['n']}")
        self.begin()

    # -- steps

    def cstat(self, c):
        cs = self.s["combos"].setdefault(c, {"n": 0, "ok": 0, "off": None})
        cs.setdefault("learned", cs["ok"] >= 2)
        cs.setdefault("best_bpm", None)
        return cs

    def begin(self):
        """Start whatever is now on top: cards for anything new first, then the step in time."""
        st = self.step()
        if st["kind"] == "cards":
            return
        s, e = span(st)
        new = []
        for i in range(s, e):
            c = self.combo(i)
            if not self.cstat(c)["learned"] and c not in new:
                new.append(c)
        if new:
            self.cur["stack"].append({"kind": "cards", "new": new, "stage": "show", "pending": new})
            self.events.append("New: " + "   ".join(f"{label(c)} = {degree(c)}" for c in new))
            return
        if st.get("tempo") is None:
            st["target"] = self.settings["target"]
            st["tempo"] = self.start_tempo(st)
            st["clean"] = 0
            st["streak"] = 0
        st["misses"] = 0
        self.events.append(f"▶ {self.describe(st)}   ♩={st['tempo']:.0f}")

    def start_tempo(self, st):
        s, e = span(st)
        start, target = min(self.settings["start"], st["target"]), st["target"]
        bests = [self.cstat(self.combo(i))["best_bpm"] for i in range(s, e)]
        if all(bests):
            return max(start, min(target, min(bests) - BPM_STEP))
        return start

    def need(self, st):
        """Clean repetitions at the target tempo before a step is done: once you can do it, move on."""
        return 1

    def judge(self, r):
        return (r["key"] is not None and int(r["key"]) == degree(self.combo(r["i"]))
                and r["off"] is not None and abs(r["off"]) <= self.settings["tolerance"])

    def record_rep(self, results):
        """results: [{"i", "key", "off"}] per combo slot, off in beats (negative = early)."""
        st = self.step()
        oks = [self.judge(r) for r in results]
        for r, ok in zip(results, oks):
            cs = self.cstat(self.combo(r["i"]))
            cs["n"] += 1
            cs["ok"] += ok
            if r["off"] is not None:
                a = abs(r["off"])
                cs["off"] = a if cs["off"] is None else cs["off"] + 0.3 * (a - cs["off"])
        if all(oks):
            st["misses"] = 0
            for r in results:
                cs = self.cstat(self.combo(r["i"]))
                cs["best_bpm"] = max(cs["best_bpm"] or 0, st["tempo"])
            if st["tempo"] < st["target"]:
                # the longer the streak of clean repetitions, the bigger the jump
                st["streak"] = st.get("streak", 0) + 1
                st["tempo"] = min(st["target"], st["tempo"] + BPM_STEP * 2 ** (st["streak"] - 1))
                st["clean"] = 0
                self.events.append(f"Clean. Tempo up: ♩={st['tempo']:.0f}")
            else:
                st["clean"] += 1
                if st["clean"] >= self.need(st):
                    self.finish_step()
            return oks
        st["clean"] = 0
        st["streak"] = 0
        i = results[oks.index(False)]["i"]
        c = self.combo(i)
        self.events.append(f"✗ {label(c)} = {degree(c)}   ({counting(c)})")
        st["misses"] = st.get("misses", 0) + 1
        if st["misses"] < STRIKES:
            self.events.append(f"Again, same tempo   (miss {st['misses']} of {STRIKES})")
            return oks
        st["misses"] = 0
        st["tempo"] = max(MIN_BPM, st["tempo"] - BPM_STEP)
        self.break_down(st, i)
        return oks

    def break_down(self, st, i):
        """Third miss in a row: rebuild from the half (2 combos) around the miss, then its bar, then the step."""
        s, e = span(st)
        for size in (BAR, HALF):
            if e - s > size:
                part = i - i % size
                self.cur["stack"].append({"kind": "drill", "units": [[part, part + size]], "remedial": True,
                                          "tempo": st["tempo"], "target": st["tempo"],
                                          "clean": 0, "streak": 0, "misses": 0})
        if self.step() is not st:
            self.events.append(f"Breaking it down: {self.describe(self.step())}")

    def card_items(self):
        """The next pass of cards: [{"combo", "show"}]."""
        st = self.step()
        if st["stage"] == "show":
            return [{"combo": c, "show": True} for c in st["new"]]
        extras = st.get("extras")
        if extras is None:
            learned = [c for c in self.s["pool"] if c not in st["new"] and self.cstat(c)["learned"]]
            extras = st["extras"] = self.rng.sample(learned, min(2, len(learned)))
        combos = list(st["pending"]) + [c for c in extras if c not in st["pending"]]
        self.rng.shuffle(combos)
        return [{"combo": c, "show": False} for c in combos]

    def record_cards(self, results):
        """results: [{"combo", "show", "key"}]. Recall passes repeat until every target is right."""
        st = self.step()
        if st["stage"] == "show":
            st["stage"] = "recall"
            return
        wrong = []
        for r in results:
            right = r["key"] is not None and int(r["key"]) == degree(r["combo"])
            if r["combo"] in st["pending"]:
                if right:
                    self.cstat(r["combo"])["learned"] = True
                else:
                    wrong.append(r["combo"])
        st["pending"] = wrong
        if not wrong:
            self.cur["stack"].pop()
            self.begin()

    def finish_step(self):
        cur = self.cur
        if cur["stack"]:
            cur["stack"].pop()
            self.events.append("✓ Good. Back to it.")
        else:
            cur["i"] += 1
            if cur["i"] == len(cur["steps"]):
                self.complete_sequence()
                return
            self.events.append("✓ Done.")
        self.begin()

    def complete_sequence(self):
        self.s["done"] += 1
        self.s["history"].append(self.cur["combos"])
        self.events.append(f"★ Sequence {self.cur['n']} complete!")
        self.s["current"] = None
        self.new_sequence()


# ------------------------------------------------------------------ storage

def data_dir():
    base = os.environ.get("XDG_DATA_HOME") or os.path.expanduser("~/.local/share")
    return os.path.join(base, "noterhythm")


def load_state(path):
    if os.path.exists(path):
        with open(path) as f:
            state = json.load(f)
        for k, v in new_state()["settings"].items():
            state["settings"].setdefault(k, v)
        if state.get("version", 1) < 2:
            migrate_v2(state)
        return state
    return new_state()


def migrate_v2(state):
    """Wider timing window and a lower target tempo, also for steps already under way."""
    st = state["settings"]
    if st["target"] == 90:
        st["target"] = TARGET_BPM
    if st["tolerance"] == 0.25:
        st["tolerance"] = TOLERANCE
    cur = state["current"]
    if cur:
        for step in cur["steps"] + cur["stack"]:
            if step.get("target") is not None:
                step["target"] = min(step["target"], st["target"])
                step["tempo"] = min(step["tempo"], step["target"])
    state["version"] = 2


def save_state(state, path):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    tmp = path + ".tmp"
    with open(tmp, "w") as f:
        json.dump(state, f)
    os.replace(tmp, path)


def log_answer(path, record):
    with open(path, "a") as f:
        f.write(json.dumps(record) + "\n")


# ------------------------------------------------------------------ sound

class Clicker:
    """Metronome clicks through paplay / pw-play / aplay, one short process per click."""

    def __init__(self, enabled):
        self.player = None
        self.procs = []
        if not enabled:
            return
        for name in ("paplay", "pw-play", "aplay"):
            if shutil.which(name):
                self.player = [name] + (["-q"] if name == "aplay" else [])
                break
        if not self.player:
            return
        self.dir = tempfile.mkdtemp(prefix="noterhythm-")
        self.files = {"soft": self.tone(1800, 0.02, 0.25), "loud": self.tone(1000, 0.035, 0.6),
                      "count": self.tone(1400, 0.03, 0.45)}

    def tone(self, freq, secs, vol):
        path = os.path.join(self.dir, f"{freq}.wav")
        rate = 44100
        n = int(rate * secs)
        frames = b"".join(
            struct.pack("<h", int(32767 * vol * math.sin(2 * math.pi * freq * k / rate) * (1 - k / n) ** 2))
            for k in range(n))
        with wave.open(path, "wb") as w:
            w.setnchannels(1)
            w.setsampwidth(2)
            w.setframerate(rate)
            w.writeframes(frames)
        return path

    def click(self, kind):
        if not self.player:
            return
        self.procs = [p for p in self.procs if p.poll() is None]
        self.procs.append(subprocess.Popen(self.player + [self.files[kind]],
                                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL))


# ------------------------------------------------------------------ terminal UI

COLOR = sys.stdout.isatty() and not os.environ.get("NO_COLOR")


def paint(text, code):
    return f"\033[{code}m{text}\033[0m" if COLOR else text


def green(t): return paint(t, "32")
def red(t): return paint(t, "31")
def yellow(t): return paint(t, "33")
def cyan(t): return paint(t, "36")
def dim(t): return paint(t, "2")
def bold(t): return paint(t, "1")


def answer_text(coach, i, key, off):
    """How one answer is shown: the key, a tick or cross, and how far off the beat it was."""
    if key is None:
        return red("—  ✗ missed")
    beat_ms = 60000 / coach.step()["tempo"]
    ms = f"{off * beat_ms:+.0f}ms"
    right = int(key) == degree(coach.combo(i))
    in_time = abs(off) <= coach.settings["tolerance"]
    if right and in_time:
        return green(f"{key} ✓") + "  " + dim(ms)
    if not right:
        return red(f"{key} ✗ {degree(coach.combo(i))}") + "  " + dim(ms)
    return red(f"{key} ✗ {'early' if off < 0 else 'late'} {ms}")


def short(combo):
    return f"{combo[0]}→{combo[1]}"


def panel_lines(coach, playing=None, width=80):
    """The map at the top of the screen: the 8-bar pattern, what's being worked on and what's playing."""
    cur = coach.cur
    steps, i, stack = cur["steps"], cur["i"], cur["stack"]
    timed = [st for st in stack if st["kind"] != "cards"]
    active = timed[-1] if timed else steps[i]
    a_s, a_e = span(active)
    p_s, p_e = span(steps[i])               # the plan step a fix-up returns to
    top = coach.step()
    what = step_name(active)
    if top["kind"] == "cards":
        what = f"{step_name(top)}, then {what}"
    tempo = f"   ♩={active['tempo']:.0f}" if active.get("tempo") else ""
    lines = [f"  {bold('Sequence ' + str(cur['n']))}   step {i + 1} of {len(steps)}   {cyan(what)}{tempo}"]
    ladder = "".join(green("■") if k < i else cyan("▶") if k == i else dim("·") for k in range(len(steps)))
    if timed:
        after = f"then back to {step_name(steps[i])}"
    elif i + 1 < len(steps):
        after = f"next: {step_name(steps[i + 1])}"
    else:
        after = "last step of the sequence"
    lines += [f"  {ladder}   {dim(after)}", ""]
    done = [span(st) for st in steps[:i]]
    per_row = 4 if width >= 77 else 2
    for row in range(0, BARS, per_row):
        head, body, mark = "  ", "  ", "  "
        for b in range(row, row + per_row):
            bs = b * BAR
            ok = any(s <= bs and bs + BAR <= e for s, e in done)
            title = f"bar {b + 1}" + (" ✓" if ok else "")
            head += "│ " + (green(title) if ok else bold(title)) + " " * (16 - len(title))
            cells, marks = [], []
            for j in range(bs, bs + BAR):
                c = short(coach.combo(j))
                if j == playing:
                    cells.append(paint(c, "1;7;36"))
                    marks.append(cyan("━━━"))
                elif a_s <= j < a_e:
                    cells.append(bold(cyan(c)))
                    marks.append(cyan("───"))
                elif timed and p_s <= j < p_e:
                    cells.append(c)
                    marks.append(dim("┄┄┄"))
                else:
                    cells.append(dim(c))
                    marks.append("   ")
            body += "│ " + " ".join(cells) + " "
            mark += "│ " + " ".join(marks) + " "
        lines += [head + "│", body + "│", mark + "│"]
    return lines


class Terminal:
    def __init__(self, coach, clicker):
        self.coach = coach
        self.clicker = clicker
        self.fd = sys.stdin.fileno()
        self.size = None        # terminal size the panel was laid out for
        self.panel_h = 0

    def setup_screen(self):
        """Clear the screen and keep the top half for the panel; everything else scrolls underneath."""
        cols, rows = os.get_terminal_size()
        self.size = (cols, rows)
        need = len(panel_lines(self.coach, width=cols)) + 1
        self.panel_h = min(max(need, rows // 2), max(0, rows - 6))
        self.write(f"\033[2J\033[{self.panel_h + 1};{rows}r\033[{rows};1H")

    def restore_screen(self):
        self.write(f"\033[r\033[{self.size[1]};1H\n" if self.size else "\n")

    def draw_panel(self, playing=None):
        if os.get_terminal_size() != self.size:
            self.setup_screen()
        lines = panel_lines(self.coach, playing, self.size[0])[:self.panel_h - 1]
        out = "\0337\033[H"
        for k in range(self.panel_h - 1):
            text = lines[k] if k < len(lines) else ""
            out += "\033[K" + text + "\n"
        out += "\033[K" + dim("─" * self.size[0]) + "\n"
        out = out[:-1] + "\0338"
        self.write(out)

    def write(self, text):
        sys.stdout.write(text)
        sys.stdout.flush()

    def read_key(self, timeout):
        r, _, _ = select.select([self.fd], [], [], max(0.0, timeout))
        if not r:
            return None, None
        t = time.monotonic()
        ch = os.read(self.fd, 1).decode(errors="ignore")
        return ch, t

    def run_cards(self, items):
        """Untimed cards. Shown cards wait for the right key; recall cards take one try.
        Returns (status, results)."""
        results = []
        for it in items:
            c = it["combo"]
            if it["show"]:
                self.write(f"  {bold(label(c))} = {bold(str(degree(c)))}   {dim('(' + counting(c) + ')')}   "
                           + dim(f"press {degree(c)} "))
            else:
                self.write(f"  {bold(label(c))}  ?  ")
            while True:
                ch = os.read(self.fd, 1).decode(errors="ignore")
                if ch in ("q", "\x1b"):
                    self.write("\n")
                    return "quit", None
                if not ch or ch not in "234567":
                    continue
                right = int(ch) == degree(c)
                if it["show"] and not right:
                    self.write(red("✗") + " ")
                    continue
                results.append({"combo": c, "show": it["show"], "key": ch})
                if right:
                    self.write(green(f"{ch} ✓") + "\n")
                else:
                    self.write(red(f"{ch} ✗") + f"   {label(c)} = {degree(c)}   {dim('(' + counting(c) + ')')}\n")
                break
        return None, results

    def wait_until(self, t_end):
        """Sleep until t_end, but notice q / p."""
        while True:
            now = time.monotonic()
            if now >= t_end:
                return None
            ch, _ = self.read_key(t_end - now)
            if ch in ("q", "\x1b"):
                return "quit"
            if ch == "p":
                return "pause"

    def count_in(self, bpm, t_first, beats, title):
        """`beats` beats ending one beat before t_first, each shown as it clicks: 1 ● ○ ○ ○."""
        beat = 60 / bpm
        for k in range(beats):
            t = t_first - (beats - k) * beat
            status = self.wait_until(t)
            if status:
                return status
            dots = " ".join("●" if j <= k else "○" for j in range(beats))
            self.write(f"\r\033[K  {bold(title)}   {cyan(f'♩={bpm:.0f}')}   {cyan(dots)}  {bold(str(k + 1))}")
            self.clicker.click("count")
        status = self.wait_until(t_first)
        self.write("\r\033[K")
        return status

    def run_rep(self, slots, bpm, t_start, countin, title=""):
        """Play one repetition, after `countin` beats of count-in. Returns (status, results, t_end)."""
        coach = self.coach
        beat = 60 / bpm
        if countin:
            status = self.count_in(bpm, t_start, countin, title)
            if status:
                return status, None, None
        lat = coach.settings["latency_ms"] / 1000
        prompts = [t_start + j * 2 * beat for j in range(len(slots))]
        t_end = t_start + len(slots) * 2 * beat
        events = []
        for j, i in enumerate(slots):
            events.append((prompts[j], "prompt", j))
            events.append((prompts[j] + beat, "answer", j))
        events.append((t_end, "end", None))
        keys = [None] * len(slots)      # (key, time)
        shown = -1                      # slot whose line is on screen
        phase = {}

        def line(j):
            i = slots[j]
            if i is None:
                return "\r\033[K" + dim("     ·")
            mark = "●○" if phase.get(j) == "prompt" else "○●"
            text = f"\r\033[K  {dim(f'♩{bpm:.0f}')} {cyan(mark)}  {bold(label(coach.combo(i)))}   "
            if keys[j]:
                key, t = keys[j]
                text += answer_text(coach, i, key, (t - lat - prompts[j] - beat) / beat)
            return text

        def finish(j):
            if j >= 0 and slots[j] is not None and keys[j] is None:
                self.write(f"\r\033[K  {dim(f'♩{bpm:.0f}')} {cyan('○●')}  {bold(label(coach.combo(slots[j])))}   "
                           + answer_text(coach, slots[j], None, None))
            if j >= 0:
                self.write("\n")

        k = 0
        while k < len(events):
            now = time.monotonic()
            if events[k][0] <= now:
                t, kind, j = events[k]
                k += 1
                if kind == "prompt":
                    finish(shown)
                    shown = j
                    phase[j] = "prompt"
                    self.draw_panel(slots[j])
                    self.write(line(j))
                    self.clicker.click("soft")
                elif kind == "answer":
                    phase[j] = "answer"
                    self.write(line(j))
                    self.clicker.click("loud" if slots[j] is not None else "soft")
                else:
                    finish(shown)
                    self.draw_panel()
                continue
            ch, t = self.read_key(events[k][0] - now)
            if ch in ("q", "\x1b"):
                self.write("\n")
                return "quit", None, None
            if ch == "p":
                self.write("\n")
                return "pause", None, None
            if ch and ch in "234567" and shown >= 0 and slots[shown] is not None and keys[shown] is None:
                keys[shown] = (ch, t)
                self.write(line(shown))
        results = []
        for j, i in enumerate(slots):
            if i is None:
                continue
            if keys[j]:
                key, t = keys[j]
                results.append({"i": i, "key": key, "off": (t - lat - prompts[j] - beat) / beat})
            else:
                results.append({"i": i, "key": None, "off": None})
        return None, results, t_end


def rep_summary(coach, results, oks, bpm):
    offs = [abs(r["off"]) * 60000 / bpm for r in results if r["off"] is not None]
    timing = f"   timing ±{sum(offs) / len(offs):.0f}ms" if offs else ""
    if all(oks):
        return green("  ✓ clean") + dim(timing)
    return red(f"  ✗ {oks.count(False)} of {len(oks)} failed") + dim(timing)


def run(state_path, log_path, mute):
    import termios
    import tty

    coach = Coach(load_state(state_path))
    clicker = Clicker(coach.settings["sound"] and not mute)
    ui = Terminal(coach, clicker)
    fd = sys.stdin.fileno()
    old = termios.tcgetattr(fd)
    coach.ensure()
    ui.setup_screen()
    print(bold("NoteRhythm") + dim("  answer 2-7 on the loud beat · p pause · q quit"))
    print(dim("  new combos come as cards first: no clock until you've recalled them"))
    if not clicker.player:
        print(dim("  (no sound: watch ●○ for the prompt beat and ○● for the answer beat)"))
    tty.setcbreak(fd)
    t_next = None
    try:
        while True:
            for e in coach.events:
                print("\r\033[K" + yellow(e))
            coach.events.clear()
            ui.draw_panel()
            st = coach.step()
            if st["kind"] == "cards":
                status, results = ui.run_cards(coach.card_items())
                if status == "quit":
                    break
                for r in results:
                    log_answer(log_path, {"at": time.time(), "seq": coach.cur["n"], "step": step_name(st),
                                          "combo": r["combo"], "key": r["key"], "card": True,
                                          "shown": r["show"], "ok": int(r["key"]) == degree(r["combo"])})
                coach.record_cards(results)
                save_state(coach.s, state_path)
                t_next = None
                continue
            bpm = st["tempo"]
            beat = 60 / bpm
            # every repetition gets the same count-in; after a repetition it carries straight on from the beat
            t_start = (t_next if t_next is not None else time.monotonic() + 0.5) + COUNT_IN * beat
            status, results, t_end = ui.run_rep(coach.rep_slots(), bpm, t_start, COUNT_IN,
                                                step_name(st).capitalize())
            if status == "quit":
                break
            if status == "pause":
                print(dim("paused, press any key to carry on"))
                os.read(fd, 1)
                t_next = None
                continue
            name = step_name(st)
            seq_n, combos = coach.cur["n"], coach.cur["combos"]
            oks = coach.record_rep(results)
            print(rep_summary(coach, results, oks, bpm))
            for e in coach.events:          # straight away, so a miss's answer is there during the rest
                print("\r\033[K" + yellow(e))
            coach.events.clear()
            save_state(coach.s, state_path)
            for r, ok in zip(results, oks):
                log_answer(log_path, {"at": time.time(), "seq": seq_n, "step": name,
                                      "combo": combos[r["i"]], "i": r["i"], "key": r["key"],
                                      "off": None if r["off"] is None else round(r["off"], 3),
                                      "ok": ok, "bpm": bpm})
            t_next = t_end
    except KeyboardInterrupt:
        pass
    finally:
        termios.tcsetattr(fd, termios.TCSADRAIN, old)
        ui.restore_screen()
        save_state(coach.s, state_path)
    print("\nSaved.")


def calibrate(state_path, mute):
    """Tap space along with 16 clicks; the typical offset is taken off every answer from now on."""
    import termios
    import tty

    state = load_state(state_path)
    clicker = Clicker(not mute)
    if not clicker.player:
        sys.exit("No sound player found (paplay, pw-play or aplay); nothing to calibrate against.")
    fd = sys.stdin.fileno()
    old = termios.tcgetattr(fd)
    beat = 60 / 80
    print("Tap space on every click (16 clicks).")
    tty.setcbreak(fd)
    offs = []
    try:
        t0 = time.monotonic() + 1.5
        times = [t0 + k * beat for k in range(16)]
        k = 0
        while time.monotonic() < times[-1] + beat / 2:
            now = time.monotonic()
            if k < len(times) and times[k] <= now:
                clicker.click("loud")
                sys.stdout.write(f"\r  {'●' * (k + 1)}{'○' * (15 - k)}")
                sys.stdout.flush()
                k += 1
                continue
            nxt = times[k] if k < len(times) else times[-1] + beat / 2
            r, _, _ = select.select([fd], [], [], max(0, nxt - now))
            if r:
                t = time.monotonic()
                os.read(fd, 1)
                nearest = min(times, key=lambda x: abs(x - t))
                if times.index(nearest) >= 4:
                    offs.append(t - nearest)
    finally:
        termios.tcsetattr(fd, termios.TCSADRAIN, old)
    if len(offs) < 6:
        sys.exit("\nNot enough taps; try again.")
    offs.sort()
    median = offs[len(offs) // 2]
    state["settings"]["latency_ms"] = round(median * 1000)
    save_state(state, state_path)
    print(f"\nYou tap {median * 1000:+.0f}ms from the click on average. "
          "That's now taken off every answer.")


def stats_text(coach):
    s = coach.s
    lines = ["", bold("NoteRhythm stats"),
             f"  sequences complete: {s['done']}   target ♩={s['settings']['target']}   "
             f"tolerance ±{s['settings']['tolerance']:.0%} of a beat   latency {s['settings']['latency_ms']}ms", ""]
    cur = s["current"]
    if cur:
        lines.append(f"  Sequence {cur['n']}, step {cur['i'] + 1} of {len(cur['steps'])}: "
                     f"{step_name(cur['steps'][cur['i']])}"
                     + (f"  ♩={cur['steps'][cur['i']]['tempo']:.0f}" if cur['steps'][cur['i']].get('tempo') else ""))
        for b in range(BARS):
            bar = cur["combos"][b * BAR:(b + 1) * BAR]
            lines.append(f"    bar {b + 1}:  " + "   ".join(label(c) for c in bar))
        lines.append("")
    lines.append("  Combos (right and in time):")
    lines.append("     " + "".join(f"{b:>6}" for b in LETTERS))
    for a in LETTERS:
        row = f"  {a}  "
        for b in LETTERS:
            c = a + b
            cs = s["combos"].get(c)
            if a == b:
                row += dim("     ·")
            elif not cs or not cs["n"]:
                row += dim("     -")
            else:
                pct = cs["ok"] / cs["n"]
                cell = f"{pct:6.0%}"
                row += green(cell) if pct >= 0.9 else yellow(cell) if pct >= 0.7 else red(cell)
        lines.append(row)
    lines.append("")
    return "\n".join(lines)


def main():
    p = argparse.ArgumentParser(description="Learn ascending note distances in time with a metronome.")
    p.add_argument("--data", default=data_dir(), help="folder for progress files (default: %(default)s)")
    p.add_argument("--stats", action="store_true", help="print stats and exit")
    p.add_argument("--target", type=int, help="tempo (bpm) a step must be clean at; saved")
    p.add_argument("--start", type=int, help="tempo (bpm) new material starts at; saved")
    p.add_argument("--tolerance", type=float, help="how far off the beat counts, as a fraction of a beat; saved")
    p.add_argument("--calibrate", action="store_true", help="measure your tap/sound delay")
    p.add_argument("--mute", action="store_true", help="no clicks this time")
    p.add_argument("--reset", action="store_true", help="start from scratch (keeps the answer log)")
    args = p.parse_args()
    state_path = os.path.join(args.data, "state.json")
    log_path = os.path.join(args.data, "answers.jsonl")
    os.makedirs(args.data, exist_ok=True)
    if args.reset and os.path.exists(state_path):
        os.replace(state_path, state_path + ".bak")
        print(f"Old progress moved to {state_path}.bak")
    state = load_state(state_path)
    for k in ("target", "start", "tolerance"):
        if getattr(args, k) is not None:
            state["settings"][k] = getattr(args, k)
            save_state(state, state_path)
    if args.stats:
        coach = Coach(state)
        print(stats_text(coach) if state["current"] else "No progress yet.")
        return
    if not sys.stdin.isatty():
        sys.exit("NoteRhythm needs an interactive terminal.")
    if args.calibrate:
        calibrate(state_path, args.mute)
        return
    run(state_path, log_path, args.mute)


if __name__ == "__main__":
    main()
