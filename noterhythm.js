#!/usr/bin/env node
/*
NoteRhythm: learn ascending note distances in time with a metronome.

    C → G = 5    B → G = 6    A → C = 3

Count up from the first note as 1. Each prompt appears on a beat and you answer
(2-7) on the next beat. Answers that are wrong, missing, or too far off the beat
fail. Sequences are built up two combos at a time: halves, bars, pairs of bars,
up to 8 bars. Keys: 2-7 answer · p pause · q quit.

Node port of noterhythm.py that also runs on Windows (Windows Terminal or the
Windows 10+ console). No npm packages needed:  node noterhythm.js
*/
"use strict";

const fs = require("fs");
const os = require("os");
const path = require("path");
const { spawn } = require("child_process");
const { performance } = require("perf_hooks");

// ------------------------------------------------------------------ theory

const LETTERS = "CDEFGAB";
const ALL_COMBOS = [];
for (const a of LETTERS) for (const b of LETTERS) if (a !== b) ALL_COMBOS.push(a + b);

function degree(combo) {
  return ((LETTERS.indexOf(combo[1]) - LETTERS.indexOf(combo[0])) % 7 + 7) % 7 + 1;
}

function label(combo) {
  return `${combo[0]} → ${combo[1]}`;
}

function counting(combo) {
  // C → G counted out: C D E F G.
  const i = LETTERS.indexOf(combo[0]);
  return Array.from({ length: degree(combo) }, (_, k) => LETTERS[(i + k) % 7]).join(" ");
}

// ------------------------------------------------------------------ tuning

const HALF = 2;             // combos in half a bar
const BAR = 4;              // combos in a bar
const BARS = 8;             // bars in a sequence
const START_BPM = 60;       // tempo new material starts at
const TARGET_BPM = 60;      // tempo a step has to be clean at to count as done
const MIN_BPM = 40;
const BPM_STEP = 6;         // tempo change after a clean or failed repetition
const TOLERANCE = 0.5;      // how far off the beat an answer may be, as a fraction of a beat
const STRIKES = 3;          // misses in a row before a step is broken down
const COUNT_IN = 4;         // beats counted in, on screen, before every repetition
const POOL_START = 6;       // combos the first sequence is made from
const POOL_MAX = 12;
const NOVEL_PER_SEQ = 2;    // combos brought in with each new sequence
const DROP_PER_SEQ = 1;     // best-known combos left out of each new sequence

function newState() {
  return {
    version: 2,
    settings: { target: TARGET_BPM, start: START_BPM, tolerance: TOLERANCE, latency_ms: 0, sound: true },
    combos: {},       // combo -> {n, ok, off}: answers, right-and-in-time, mean |offset| in beats
    usage: {},        // combo -> times used in sequences
    pool: [],         // combos the current sequence draws on
    done: 0,          // sequences completed
    history: [],      // completed sequences' combos
    current: null,    // sequence being learned
  };
}

// ------------------------------------------------------------------ random

class Random {
  // Small seeded generator (mulberry32) so tests are repeatable.
  constructor(seed) {
    this.a = (seed === undefined ? Math.floor(Math.random() * 2 ** 32) : seed) >>> 0;
  }
  random() {
    let t = (this.a = (this.a + 0x6d2b79f5) >>> 0);
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  }
  shuffle(arr) {
    for (let i = arr.length - 1; i > 0; i--) {
      const j = Math.floor(this.random() * (i + 1));
      [arr[i], arr[j]] = [arr[j], arr[i]];
    }
    return arr;
  }
  sample(arr, k) {
    return this.shuffle([...arr]).slice(0, k);
  }
}

function minBy(items, key) {
  let best, bestKey;
  for (const it of items) {
    const k = key(it);
    if (bestKey === undefined || cmpKeys(k, bestKey) < 0) [best, bestKey] = [it, k];
  }
  return best;
}

function cmpKeys(a, b) {
  for (let i = 0; i < a.length; i++) if (a[i] !== b[i]) return a[i] < b[i] ? -1 : 1;
  return 0;
}

// ------------------------------------------------------------------ build plan
//
// A sequence is 8 bars of 4 combos. It's built up like learning a piece:
//   bar 1: first half, second half, whole bar
//   bar 2: the same
//   bars 1 and 2 alternating, then bars 1-2 together
//   bars 3-4 the same way, then bars 1-4
//   bars 5-8 the same way as 1-4, then bars 1-8

function drill(s, e) {
  return { kind: "drill", units: [[s, e]] };
}

function barSteps(b) {
  const s = b * BAR;
  return [drill(s, s + HALF), drill(s + HALF, s + BAR), drill(s, s + BAR)];
}

function pairSteps(b) {
  const s = b * BAR;
  return [...barSteps(b), ...barSteps(b + 1),
    { kind: "alt", units: [[s, s + BAR], [s + BAR, s + 2 * BAR]] }, drill(s, s + 2 * BAR)];
}

function buildPlan() {
  const half = (BARS / 2) * BAR;
  return [...pairSteps(0), ...pairSteps(2), drill(0, half),
    ...pairSteps(4), ...pairSteps(6), drill(half, 2 * half),
    drill(0, 2 * half)];
}

function span(step) {
  return [Math.min(...step.units.map((u) => u[0])), Math.max(...step.units.map((u) => u[1]))];
}

function barsName(s, e) {
  const first = Math.floor(s / BAR) + 1, last = Math.floor((e - 1) / BAR) + 1;
  return first === last ? `bar ${first}` : `bars ${first}–${last}`;
}

function stepName(step) {
  if (step.kind === "cards") return step.new.length ? "new combos" : "quick check";
  const [s, e] = span(step);
  if (step.kind === "alt") {
    const [a, b] = step.units;
    return `bars ${a[0] / BAR + 1} and ${b[0] / BAR + 1} alternating`;
  }
  if (e - s === HALF) return `${barsName(s, e)}, ${s % BAR === 0 ? "first" : "second"} half`;
  return barsName(s, e);
}

// ------------------------------------------------------------------ coach

class Coach {
  // Decides what to play and learns from each repetition. Works without a terminal.

  constructor(state, rng) {
    this.s = state || newState();
    this.rng = rng || new Random();
    this.events = [];       // messages for the UI
  }

  get cur() { return this.s.current; }
  get settings() { return this.s.settings; }

  ensure() {
    // Ready to play: a sequence exists and the step on top has been started.
    if (!this.cur) {
      this.newSequence();
      return;
    }
    // fix-ups left over from the last session are dropped: carry on with the plan itself
    this.cur.stack = [];
    this.begin();
  }

  step() {
    const cur = this.cur;
    return cur.stack.length ? cur.stack[cur.stack.length - 1] : cur.steps[cur.i];
  }

  combo(i) { return this.cur.combos[i]; }

  repSlots() {
    // One repetition of the current step: combo positions, null for a gap of one combo.
    const slots = [];
    this.step().units.forEach(([s, e], k) => {
      if (k) slots.push(null);
      for (let i = s; i < e; i++) slots.push(i);
    });
    return slots;
  }

  describe(st) {
    const [s, e] = span(st);
    const combos = [];
    if (e - s <= BAR) for (let i = s; i < e; i++) combos.push(label(this.combo(i)));
    return stepName(st) + (combos.length ? `:  ${combos.join("  ")}` : "");
  }

  // -- knowledge

  knowledge(c) {
    const st = this.s.combos[c];
    if (!st || !st.n) return 0;
    return (st.ok / st.n) * Math.min(1, st.n / 20);
  }

  // -- composing sequences

  nextPool() {
    // Keep most of the last pool, leave out what you know best, bring in a little novelty.
    let pool = [...this.s.pool];
    const usage = this.s.usage;
    const unused = ALL_COMBOS.filter((c) => !pool.includes(c))
      .map((c) => [c, [usage[c] || 0, this.rng.random()]])
      .sort((x, y) => cmpKeys(x[1], y[1])).map((x) => x[0]);
    if (!pool.length) {
      const novel = unused.slice(0, POOL_START);
      return [novel, novel];
    }
    const drop = DROP_PER_SEQ + Math.max(0, pool.length + NOVEL_PER_SEQ - DROP_PER_SEQ - POOL_MAX);
    const best = [...pool].sort((a, b) => this.knowledge(b) - this.knowledge(a)).slice(0, drop);
    pool = pool.filter((c) => !best.includes(c));
    const novel = unused.slice(0, NOVEL_PER_SEQ);
    return [[...pool, ...novel], novel];
  }

  compose(pool, novel) {
    // 8 bars; each bar is the one before with a small change, new combos favoured.
    const seq = [];
    const pick = (exclude, ctx) => {
      const counts = {};
      for (const c of ctx) counts[c] = (counts[c] || 0) + 1;
      let options = pool.filter((c) => !exclude.has(c));
      if (!options.length) options = ALL_COMBOS.filter((c) => !exclude.has(c));
      return minBy(options, (c) => [(counts[c] || 0) - (novel.includes(c) ? 2 : 0), this.rng.random()]);
    };
    let bar = [];
    for (let k = 0; k < BAR; k++) bar.push(pick(new Set(bar), bar));
    seq.push(...bar);
    for (let b = 1; b < BARS; b++) {
      bar = seq.slice(-BAR);
      for (const p of this.rng.sample([0, 1, 2, 3], b % 2 ? 1 : 2)) {
        const before = p === 0 ? seq[seq.length - 1] : bar[p - 1];
        const after = p + 1 < BAR ? bar[p + 1] : null;
        bar[p] = pick(new Set([bar[p], before, after]), [...seq, ...bar]);
      }
      if (bar[0] === seq[seq.length - 1]) {
        bar[0] = pick(new Set([bar[0], bar[1], seq[seq.length - 1]]), [...seq, ...bar]);
      }
      seq.push(...bar);
    }
    return seq;
  }

  newSequence() {
    const [pool, novel] = this.nextPool();
    const combos = this.compose(pool, novel);
    this.s.pool = pool;
    for (const c of combos) this.s.usage[c] = (this.s.usage[c] || 0) + 1;
    this.s.current = { n: this.s.done + 1, combos, novel, steps: buildPlan(), i: 0, stack: [] };
    this.events.push(`New sequence ${this.cur.n}`);
    this.begin();
  }

  // -- steps

  cstat(c) {
    const cs = (this.s.combos[c] = this.s.combos[c] || { n: 0, ok: 0, off: null });
    if (cs.learned === undefined) cs.learned = cs.ok >= 2;
    if (cs.best_bpm === undefined) cs.best_bpm = null;
    return cs;
  }

  begin() {
    // Start whatever is now on top: cards for anything new first, then the step in time.
    const st = this.step();
    if (st.kind === "cards") return;
    const [s, e] = span(st);
    const fresh = [];
    for (let i = s; i < e; i++) {
      const c = this.combo(i);
      if (!this.cstat(c).learned && !fresh.includes(c)) fresh.push(c);
    }
    if (fresh.length) {
      this.cur.stack.push({ kind: "cards", new: fresh, stage: "show", pending: fresh });
      this.events.push("New: " + fresh.map((c) => `${label(c)} = ${degree(c)}`).join("   "));
      return;
    }
    if (st.tempo === undefined || st.tempo === null) {
      st.target = this.settings.target;
      st.tempo = this.startTempo(st);
      st.clean = 0;
      st.streak = 0;
    }
    st.misses = 0;
    this.events.push(`▶ ${this.describe(st)}   ♩=${Math.round(st.tempo)}`);
  }

  startTempo(st) {
    const [s, e] = span(st);
    const start = Math.min(this.settings.start, st.target), target = st.target;
    const bests = [];
    for (let i = s; i < e; i++) bests.push(this.cstat(this.combo(i)).best_bpm);
    if (bests.every((b) => b)) return Math.max(start, Math.min(target, Math.min(...bests) - BPM_STEP));
    return start;
  }

  need() {
    // Clean repetitions at the target tempo before a step is done: once you can do it, move on.
    return 1;
  }

  judge(r) {
    return r.key !== null && Number(r.key) === degree(this.combo(r.i))
      && r.off !== null && Math.abs(r.off) <= this.settings.tolerance;
  }

  recordRep(results) {
    // results: [{i, key, off}] per combo slot, off in beats (negative = early).
    const st = this.step();
    const oks = results.map((r) => this.judge(r));
    results.forEach((r, k) => {
      const cs = this.cstat(this.combo(r.i));
      cs.n += 1;
      cs.ok += oks[k] ? 1 : 0;
      if (r.off !== null) {
        const a = Math.abs(r.off);
        cs.off = cs.off === null ? a : cs.off + 0.3 * (a - cs.off);
      }
    });
    if (oks.every(Boolean)) {
      st.misses = 0;
      for (const r of results) {
        const cs = this.cstat(this.combo(r.i));
        cs.best_bpm = Math.max(cs.best_bpm || 0, st.tempo);
      }
      if (st.tempo < st.target) {
        // the longer the streak of clean repetitions, the bigger the jump
        st.streak = (st.streak || 0) + 1;
        st.tempo = Math.min(st.target, st.tempo + BPM_STEP * 2 ** (st.streak - 1));
        st.clean = 0;
        this.events.push(`Clean. Tempo up: ♩=${Math.round(st.tempo)}`);
      } else {
        st.clean += 1;
        if (st.clean >= this.need(st)) this.finishStep();
      }
      return oks;
    }
    st.clean = 0;
    st.streak = 0;
    const i = results[oks.indexOf(false)].i;
    const c = this.combo(i);
    this.events.push(`✗ ${label(c)} = ${degree(c)}   (${counting(c)})`);
    st.misses = (st.misses || 0) + 1;
    if (st.misses < STRIKES) {
      this.events.push(`Again, same tempo   (miss ${st.misses} of ${STRIKES})`);
      return oks;
    }
    st.misses = 0;
    st.tempo = Math.max(MIN_BPM, st.tempo - BPM_STEP);
    this.breakDown(st, i);
    return oks;
  }

  breakDown(st, i) {
    // Third miss in a row: rebuild from the half (2 combos) around the miss, then its bar, then the step.
    const [s, e] = span(st);
    for (const size of [BAR, HALF]) {
      if (e - s > size) {
        const part = i - (i % size);
        this.cur.stack.push({ kind: "drill", units: [[part, part + size]], remedial: true,
          tempo: st.tempo, target: st.tempo, clean: 0, streak: 0, misses: 0 });
      }
    }
    if (this.step() !== st) this.events.push(`Breaking it down: ${this.describe(this.step())}`);
  }

  cardItems() {
    // The next pass of cards: [{combo, show}].
    const st = this.step();
    if (st.stage === "show") return st.new.map((c) => ({ combo: c, show: true }));
    let extras = st.extras;
    if (extras === undefined || extras === null) {
      const learned = this.s.pool.filter((c) => !st.new.includes(c) && this.cstat(c).learned);
      extras = st.extras = this.rng.sample(learned, Math.min(2, learned.length));
    }
    const combos = [...st.pending, ...extras.filter((c) => !st.pending.includes(c))];
    this.rng.shuffle(combos);
    return combos.map((c) => ({ combo: c, show: false }));
  }

  recordCards(results) {
    // results: [{combo, show, key}]. Recall passes repeat until every target is right.
    const st = this.step();
    if (st.stage === "show") {
      st.stage = "recall";
      return;
    }
    const wrong = [];
    for (const r of results) {
      const right = r.key !== null && Number(r.key) === degree(r.combo);
      if (st.pending.includes(r.combo)) {
        if (right) this.cstat(r.combo).learned = true;
        else wrong.push(r.combo);
      }
    }
    st.pending = wrong;
    if (!wrong.length) {
      this.cur.stack.pop();
      this.begin();
    }
  }

  finishStep() {
    const cur = this.cur;
    if (cur.stack.length) {
      cur.stack.pop();
      this.events.push("✓ Good. Back to it.");
    } else {
      cur.i += 1;
      if (cur.i === cur.steps.length) {
        this.completeSequence();
        return;
      }
      this.events.push("✓ Done.");
    }
    this.begin();
  }

  completeSequence() {
    this.s.done += 1;
    this.s.history.push(this.cur.combos);
    this.events.push(`★ Sequence ${this.cur.n} complete!`);
    this.s.current = null;
    this.newSequence();
  }
}

// ------------------------------------------------------------------ storage

function dataDir() {
  if (process.platform === "win32") {
    return path.join(process.env.APPDATA || path.join(os.homedir(), "AppData", "Roaming"), "noterhythm");
  }
  const base = process.env.XDG_DATA_HOME || path.join(os.homedir(), ".local", "share");
  return path.join(base, "noterhythm-node");
}

function loadState(file) {
  if (!fs.existsSync(file)) return newState();
  const state = JSON.parse(fs.readFileSync(file, "utf8"));
  for (const [k, v] of Object.entries(newState().settings)) {
    if (state.settings[k] === undefined) state.settings[k] = v;
  }
  return state;
}

function saveState(state, file) {
  fs.mkdirSync(path.dirname(file), { recursive: true });
  const tmp = file + ".tmp";
  fs.writeFileSync(tmp, JSON.stringify(state));
  fs.renameSync(tmp, file);
}

function logAnswer(file, record) {
  fs.appendFileSync(file, JSON.stringify(record) + "\n");
}

// ------------------------------------------------------------------ sound

function which(name) {
  const exts = process.platform === "win32" ? (process.env.PATHEXT || ".EXE").split(";") : [""];
  for (const dir of (process.env.PATH || "").split(path.delimiter)) {
    for (const ext of exts) {
      const p = path.join(dir, name + ext);
      try {
        fs.accessSync(p, fs.constants.X_OK);
        return p;
      } catch (e) { /* not here */ }
    }
  }
  return null;
}

function toneWav(freq, secs, vol) {
  const rate = 44100;
  const n = Math.floor(rate * secs);
  const buf = Buffer.alloc(44 + n * 2);
  buf.write("RIFF", 0);
  buf.writeUInt32LE(36 + n * 2, 4);
  buf.write("WAVEfmt ", 8);
  buf.writeUInt32LE(16, 16);
  buf.writeUInt16LE(1, 20);          // PCM
  buf.writeUInt16LE(1, 22);          // mono
  buf.writeUInt32LE(rate, 24);
  buf.writeUInt32LE(rate * 2, 28);
  buf.writeUInt16LE(2, 32);
  buf.writeUInt16LE(16, 34);
  buf.write("data", 36);
  buf.writeUInt32LE(n * 2, 40);
  for (let k = 0; k < n; k++) {
    const v = 32767 * vol * Math.sin((2 * Math.PI * freq * k) / rate) * (1 - k / n) ** 2;
    buf.writeInt16LE(Math.trunc(v), 44 + k * 2);
  }
  return buf;
}

class Clicker {
  // Metronome clicks. On Windows one hidden PowerShell keeps a SoundPlayer per click loaded and plays
  // whichever name it's sent, so there's no start-up delay per click. Elsewhere paplay / pw-play /
  // aplay / afplay, one short process per click.

  constructor(enabled) {
    this.player = null;
    this.ps = null;
    if (!enabled) return;
    const dir = fs.mkdtempSync(path.join(os.tmpdir(), "noterhythm-"));
    this.files = {};
    for (const [kind, freq, secs, vol] of [["soft", 1800, 0.02, 0.25], ["loud", 1000, 0.035, 0.6],
      ["count", 1400, 0.03, 0.45]]) {
      this.files[kind] = path.join(dir, `${kind}.wav`);
      fs.writeFileSync(this.files[kind], toneWav(freq, secs, vol));
    }
    if (process.platform === "win32") {
      this.startPowerShell();
      return;
    }
    for (const name of ["paplay", "pw-play", "aplay", "afplay"]) {
      if (which(name)) {
        this.player = [name, ...(name === "aplay" ? ["-q"] : [])];
        break;
      }
    }
  }

  startPowerShell() {
    const quote = (p) => "'" + p.replace(/'/g, "''") + "'";
    const script = [
      "$p = @{}",
      ...Object.entries(this.files).map(([k, f]) =>
        `$p['${k}'] = New-Object System.Media.SoundPlayer ${quote(f)}; $p['${k}'].Load()`),
      "while ($null -ne ($l = [Console]::In.ReadLine())) { $s = $p[$l.Trim()]; if ($s) { $s.Play() } }",
    ].join("\n");
    const encoded = Buffer.from(script, "utf16le").toString("base64");
    try {
      this.ps = spawn("powershell.exe", ["-NoProfile", "-NonInteractive", "-EncodedCommand", encoded],
        { stdio: ["pipe", "ignore", "ignore"], windowsHide: true });
      this.ps.on("error", () => { this.ps = null; this.player = null; });
      this.ps.stdin.on("error", () => {});
      this.player = ["powershell"];
    } catch (e) {
      this.ps = null;
    }
  }

  click(kind) {
    if (!this.player) return;
    if (this.ps) {
      this.ps.stdin.write(kind + "\n");
      return;
    }
    const p = spawn(this.player[0], [...this.player.slice(1), this.files[kind]], { stdio: "ignore" });
    p.on("error", () => {});
  }

  close() {
    if (this.ps) {
      this.ps.stdin.end();
      this.ps.kill();
    }
  }
}

// ------------------------------------------------------------------ terminal UI

const COLOR = process.stdout.isTTY && !process.env.NO_COLOR;

function paint(text, code) {
  return COLOR ? `\x1b[${code}m${text}\x1b[0m` : text;
}

const green = (t) => paint(t, "32");
const red = (t) => paint(t, "31");
const yellow = (t) => paint(t, "33");
const cyan = (t) => paint(t, "36");
const dim = (t) => paint(t, "2");
const bold = (t) => paint(t, "1");

const NL = "\r\n";      // raw mode on Windows doesn't turn \n into a new line by itself

function signed(x) {
  const v = Math.round(x);
  return (v >= 0 ? "+" : "") + v;
}

function capitalize(s) {
  return s[0].toUpperCase() + s.slice(1);
}

function answerText(coach, i, key, off) {
  // How one answer is shown: the key, a tick or cross, and how far off the beat it was.
  if (key === null) return red("—  ✗ missed");
  const beatMs = 60000 / coach.step().tempo;
  const ms = `${signed(off * beatMs)}ms`;
  const right = Number(key) === degree(coach.combo(i));
  const inTime = Math.abs(off) <= coach.settings.tolerance;
  if (right && inTime) return green(`${key} ✓`) + "  " + dim(ms);
  if (!right) return red(`${key} ✗ ${degree(coach.combo(i))}`) + "  " + dim(ms);
  return red(`${key} ✗ ${off < 0 ? "early" : "late"} ${ms}`);
}

function short(combo) {
  return `${combo[0]}→${combo[1]}`;
}

function panelLines(coach, playing = null, width = 80) {
  // The map at the top of the screen: the 8-bar pattern, what's being worked on and what's playing.
  const cur = coach.cur;
  const { steps, i, stack } = cur;
  const timed = stack.filter((st) => st.kind !== "cards");
  const active = timed.length ? timed[timed.length - 1] : steps[i];
  const [aS, aE] = span(active);
  const [pS, pE] = span(steps[i]);          // the plan step a fix-up returns to
  const top = coach.step();
  let what = stepName(active);
  if (top.kind === "cards") what = `${stepName(top)}, then ${what}`;
  const tempo = active.tempo ? `   ♩=${Math.round(active.tempo)}` : "";
  const lines = [`  ${bold("Sequence " + cur.n)}   step ${i + 1} of ${steps.length}   ${cyan(what)}${tempo}`];
  const ladder = steps.map((_, k) => (k < i ? green("■") : k === i ? cyan("▶") : dim("·"))).join("");
  let after;
  if (timed.length) after = `then back to ${stepName(steps[i])}`;
  else if (i + 1 < steps.length) after = `next: ${stepName(steps[i + 1])}`;
  else after = "last step of the sequence";
  lines.push(`  ${ladder}   ${dim(after)}`, "");
  const done = steps.slice(0, i).map(span);
  const perRow = width >= 77 ? 4 : 2;
  for (let row = 0; row < BARS; row += perRow) {
    let head = "  ", body = "  ", mark = "  ";
    for (let b = row; b < row + perRow; b++) {
      const bs = b * BAR;
      const ok = done.some(([s, e]) => s <= bs && bs + BAR <= e);
      const title = `bar ${b + 1}` + (ok ? " ✓" : "");
      head += "│ " + (ok ? green(title) : bold(title)) + " ".repeat(16 - title.length);
      const cells = [], marks = [];
      for (let j = bs; j < bs + BAR; j++) {
        const c = short(coach.combo(j));
        if (j === playing) {
          cells.push(paint(c, "1;7;36"));
          marks.push(cyan("━━━"));
        } else if (aS <= j && j < aE) {
          cells.push(bold(cyan(c)));
          marks.push(cyan("───"));
        } else if (timed.length && pS <= j && j < pE) {
          cells.push(c);
          marks.push(dim("┄┄┄"));
        } else {
          cells.push(dim(c));
          marks.push("   ");
        }
      }
      body += "│ " + cells.join(" ") + " ";
      mark += "│ " + marks.join(" ") + " ";
    }
    lines.push(head + "│", body + "│", mark + "│");
  }
  return lines;
}

function now() {
  return performance.now() / 1000;
}

class Keys {
  // Keypresses, each stamped with the time it arrived, read with a deadline.

  constructor(stdin) {
    this.queue = [];
    this.waiter = null;
    this.stdin = stdin;
    this.onData = (buf) => {
      const t = now();
      for (const ch of buf.toString("utf8")) this.queue.push({ ch: ch === "\x03" ? "q" : ch, t });
      if (this.waiter) this.waiter();
    };
  }

  start() {
    this.stdin.setRawMode(true);
    this.stdin.resume();
    this.stdin.on("data", this.onData);
  }

  stop() {
    this.stdin.off("data", this.onData);
    if (this.stdin.isTTY) this.stdin.setRawMode(false);
    this.stdin.pause();
  }

  read(deadline = Infinity) {
    // The next key, or {ch: null} at the deadline. Timers on Windows are coarse, so the last
    // few milliseconds are waited out with setImmediate.
    return new Promise((resolve) => {
      let timer = null, imm = null;
      const finish = (v) => {
        clearTimeout(timer);
        clearImmediate(imm);
        this.waiter = null;
        resolve(v);
      };
      const check = () => {
        clearTimeout(timer);
        clearImmediate(imm);
        if (this.queue.length) return finish(this.queue.shift());
        const left = deadline - now();
        if (left <= 0) return finish({ ch: null, t: null });
        if (left === Infinity) return;
        if (left > 0.02) timer = setTimeout(check, (left - 0.015) * 1000);
        else imm = setImmediate(check);
      };
      this.waiter = check;
      check();
    });
  }
}

class Terminal {
  constructor(coach, clicker, keys) {
    this.coach = coach;
    this.clicker = clicker;
    this.keys = keys;
    this.size = null;       // terminal size the panel was laid out for
    this.panelH = 0;
  }

  write(text) {
    process.stdout.write(text);
  }

  print(text = "") {
    this.write(text + NL);
  }

  termSize() {
    return [process.stdout.columns || 80, process.stdout.rows || 24];
  }

  setupScreen() {
    // Clear the screen and keep the top half for the panel; everything else scrolls underneath.
    const [cols, rows] = this.termSize();
    this.size = [cols, rows];
    const need = panelLines(this.coach, null, cols).length + 1;
    this.panelH = Math.min(Math.max(need, Math.floor(rows / 2)), Math.max(0, rows - 6));
    this.write(`\x1b[2J\x1b[${this.panelH + 1};${rows}r\x1b[${rows};1H`);
  }

  restoreScreen() {
    this.write(this.size ? `\x1b[r\x1b[${this.size[1]};1H${NL}` : NL);
  }

  drawPanel(playing = null) {
    const [cols, rows] = this.termSize();
    if (!this.size || cols !== this.size[0] || rows !== this.size[1]) this.setupScreen();
    const lines = panelLines(this.coach, playing, this.size[0]).slice(0, this.panelH - 1);
    let out = "\x1b7\x1b[H";
    for (let k = 0; k < this.panelH - 1; k++) out += "\x1b[K" + (k < lines.length ? lines[k] : "") + NL;
    out += "\x1b[K" + dim("─".repeat(this.size[0])) + "\x1b8";
    this.write(out);
  }

  async runCards(items) {
    // Untimed cards. Shown cards wait for the right key; recall cards take one try.
    const results = [];
    for (const it of items) {
      const c = it.combo;
      if (it.show) {
        this.write(`  ${bold(label(c))} = ${bold(String(degree(c)))}   ${dim("(" + counting(c) + ")")}   `
          + dim(`press ${degree(c)} `));
      } else {
        this.write(`  ${bold(label(c))}  ?  `);
      }
      for (;;) {
        const { ch } = await this.keys.read();
        if (ch === "q" || ch === "\x1b") {
          this.print();
          return ["quit", null];
        }
        if (!ch || !"234567".includes(ch)) continue;
        const right = Number(ch) === degree(c);
        if (it.show && !right) {
          this.write(red("✗") + " ");
          continue;
        }
        results.push({ combo: c, show: it.show, key: ch });
        if (right) this.print(green(`${ch} ✓`));
        else this.print(red(`${ch} ✗`) + `   ${label(c)} = ${degree(c)}   ${dim("(" + counting(c) + ")")}`);
        break;
      }
    }
    return [null, results];
  }

  async waitUntil(tEnd) {
    // Sleep until tEnd, but notice q / p.
    for (;;) {
      const { ch } = await this.keys.read(tEnd);
      if (ch === null) return null;
      if (ch === "q" || ch === "\x1b") return "quit";
      if (ch === "p") return "pause";
    }
  }

  async countIn(bpm, tFirst, beats, title) {
    // `beats` beats ending one beat before tFirst, each shown as it clicks: 1 ● ○ ○ ○.
    const beat = 60 / bpm;
    for (let k = 0; k < beats; k++) {
      const status = await this.waitUntil(tFirst - (beats - k) * beat);
      if (status) return status;
      const dots = Array.from({ length: beats }, (_, j) => (j <= k ? "●" : "○")).join(" ");
      this.write(`\r\x1b[K  ${bold(title)}   ${cyan(`♩=${Math.round(bpm)}`)}   ${cyan(dots)}  ${bold(String(k + 1))}`);
      this.clicker.click("count");
    }
    const status = await this.waitUntil(tFirst);
    this.write("\r\x1b[K");
    return status;
  }

  async runRep(slots, bpm, tStart, countin, title = "") {
    // Play one repetition, after `countin` beats of count-in. Returns [status, results, tEnd].
    const coach = this.coach;
    const beat = 60 / bpm;
    if (countin) {
      const status = await this.countIn(bpm, tStart, countin, title);
      if (status) return [status, null, null];
    }
    const lat = coach.settings.latency_ms / 1000;
    const prompts = slots.map((_, j) => tStart + j * 2 * beat);
    const tEnd = tStart + slots.length * 2 * beat;
    const events = [];
    slots.forEach((_, j) => {
      events.push([prompts[j], "prompt", j]);
      events.push([prompts[j] + beat, "answer", j]);
    });
    events.push([tEnd, "end", null]);
    const keys = slots.map(() => null);     // {ch, t}
    let shown = -1;                         // slot whose line is on screen
    const phase = {};
    const bpmTag = dim(`♩${Math.round(bpm)}`);

    const line = (j) => {
      const i = slots[j];
      if (i === null) return "\r\x1b[K" + dim("     ·");
      const mark = phase[j] === "prompt" ? "●○" : "○●";
      let text = `\r\x1b[K  ${bpmTag} ${cyan(mark)}  ${bold(label(coach.combo(i)))}   `;
      if (keys[j]) text += answerText(coach, i, keys[j].ch, (keys[j].t - lat - prompts[j] - beat) / beat);
      return text;
    };
    const finish = (j) => {
      if (j >= 0 && slots[j] !== null && keys[j] === null) {
        this.write(`\r\x1b[K  ${bpmTag} ${cyan("○●")}  ${bold(label(coach.combo(slots[j])))}   `
          + answerText(coach, slots[j], null, null));
      }
      if (j >= 0) this.write(NL);
    };

    let k = 0;
    while (k < events.length) {
      if (events[k][0] <= now()) {
        const [, kind, j] = events[k];
        k += 1;
        if (kind === "prompt") {
          finish(shown);
          shown = j;
          phase[j] = "prompt";
          this.drawPanel(slots[j]);
          this.write(line(j));
          this.clicker.click("soft");
        } else if (kind === "answer") {
          phase[j] = "answer";
          this.write(line(j));
          this.clicker.click(slots[j] !== null ? "loud" : "soft");
        } else {
          finish(shown);
          this.drawPanel();
        }
        continue;
      }
      const key = await this.keys.read(events[k][0]);
      if (key.ch === "q" || key.ch === "\x1b") {
        this.print();
        return ["quit", null, null];
      }
      if (key.ch === "p") {
        this.print();
        return ["pause", null, null];
      }
      if (key.ch && "234567".includes(key.ch) && shown >= 0 && slots[shown] !== null && keys[shown] === null) {
        keys[shown] = key;
        this.write(line(shown));
      }
    }
    const results = [];
    slots.forEach((i, j) => {
      if (i === null) return;
      if (keys[j]) results.push({ i, key: keys[j].ch, off: (keys[j].t - lat - prompts[j] - beat) / beat });
      else results.push({ i, key: null, off: null });
    });
    return [null, results, tEnd];
  }
}

function repSummary(results, oks, bpm) {
  const offs = results.filter((r) => r.off !== null).map((r) => (Math.abs(r.off) * 60000) / bpm);
  const timing = offs.length ? `   timing ±${Math.round(offs.reduce((a, b) => a + b, 0) / offs.length)}ms` : "";
  if (oks.every(Boolean)) return green("  ✓ clean") + dim(timing);
  return red(`  ✗ ${oks.filter((o) => !o).length} of ${oks.length} failed`) + dim(timing);
}

async function run(statePath, logPath, mute) {
  const coach = new Coach(loadState(statePath));
  const clicker = new Clicker(coach.settings.sound && !mute);
  const keys = new Keys(process.stdin);
  const ui = new Terminal(coach, clicker, keys);
  coach.ensure();
  ui.setupScreen();
  ui.print(bold("NoteRhythm") + dim("  answer 2-7 on the loud beat · p pause · q quit"));
  ui.print(dim("  new combos come as cards first: no clock until you've recalled them"));
  if (!clicker.player) ui.print(dim("  (no sound: watch ●○ for the prompt beat and ○● for the answer beat)"));
  keys.start();
  let tNext = null;
  const flushEvents = () => {
    for (const e of coach.events) ui.print("\r\x1b[K" + yellow(e));
    coach.events.length = 0;
  };
  try {
    for (;;) {
      flushEvents();
      ui.drawPanel();
      const st = coach.step();
      if (st.kind === "cards") {
        const [status, results] = await ui.runCards(coach.cardItems());
        if (status === "quit") break;
        for (const r of results) {
          logAnswer(logPath, { at: Date.now() / 1000, seq: coach.cur.n, step: stepName(st), combo: r.combo,
            key: r.key, card: true, shown: r.show, ok: Number(r.key) === degree(r.combo) });
        }
        coach.recordCards(results);
        saveState(coach.s, statePath);
        tNext = null;
        continue;
      }
      const bpm = st.tempo;
      const beat = 60 / bpm;
      // every repetition gets the same count-in; after a repetition it carries straight on from the beat
      const tStart = (tNext !== null ? tNext : now() + 0.5) + COUNT_IN * beat;
      const [status, results, tEnd] = await ui.runRep(coach.repSlots(), bpm, tStart, COUNT_IN,
        capitalize(stepName(st)));
      if (status === "quit") break;
      if (status === "pause") {
        ui.print(dim("paused, press any key to carry on"));
        await keys.read();
        tNext = null;
        continue;
      }
      const name = stepName(st);
      const seqN = coach.cur.n, combos = coach.cur.combos;
      const oks = coach.recordRep(results);
      ui.print(repSummary(results, oks, bpm));
      flushEvents();          // straight away, so a miss's answer is there during the rest
      saveState(coach.s, statePath);
      results.forEach((r, k) => {
        logAnswer(logPath, { at: Date.now() / 1000, seq: seqN, step: name, combo: combos[r.i], i: r.i,
          key: r.key, off: r.off === null ? null : Math.round(r.off * 1000) / 1000, ok: oks[k], bpm });
      });
      tNext = tEnd;
    }
  } finally {
    keys.stop();
    clicker.close();
    ui.restoreScreen();
    saveState(coach.s, statePath);
  }
  console.log(NL + "Saved.");
}

async function calibrate(statePath, mute) {
  // Tap space along with 16 clicks; the typical offset is taken off every answer from now on.
  const state = loadState(statePath);
  const clicker = new Clicker(!mute);
  if (!clicker.player) {
    console.error("No sound player found; nothing to calibrate against.");
    process.exit(1);
  }
  const keys = new Keys(process.stdin);
  const beat = 60 / 80;
  process.stdout.write("Tap space on every click (16 clicks)." + NL);
  keys.start();
  const offs = [];
  try {
    const t0 = now() + 1.5;
    const times = Array.from({ length: 16 }, (_, k) => t0 + k * beat);
    let k = 0;
    const tLast = times[times.length - 1] + beat / 2;
    while (now() < tLast) {
      if (k < times.length && times[k] <= now()) {
        clicker.click("loud");
        process.stdout.write(`\r  ${"●".repeat(k + 1)}${"○".repeat(15 - k)}`);
        k += 1;
        continue;
      }
      const key = await keys.read(k < times.length ? times[k] : tLast);
      if (key.ch === "q") break;
      if (key.ch !== null) {
        const nearest = times.reduce((a, b) => (Math.abs(b - key.t) < Math.abs(a - key.t) ? b : a));
        if (times.indexOf(nearest) >= 4) offs.push(key.t - nearest);
      }
    }
  } finally {
    keys.stop();
    // give the last click time to play before PowerShell is closed
    await new Promise((r) => setTimeout(r, 300));
    clicker.close();
  }
  if (offs.length < 6) {
    console.error(NL + "Not enough taps; try again.");
    process.exit(1);
  }
  offs.sort((a, b) => a - b);
  const median = offs[Math.floor(offs.length / 2)];
  state.settings.latency_ms = Math.round(median * 1000);
  saveState(state, statePath);
  console.log(`${NL}You tap ${signed(median * 1000)}ms from the click on average. `
    + "That's now taken off every answer.");
}

function statsText(coach) {
  const s = coach.s;
  const lines = ["", bold("NoteRhythm stats"),
    `  sequences complete: ${s.done}   target ♩=${s.settings.target}   `
    + `tolerance ±${Math.round(s.settings.tolerance * 100)}% of a beat   latency ${s.settings.latency_ms}ms`, ""];
  const cur = s.current;
  if (cur) {
    const st = cur.steps[cur.i];
    lines.push(`  Sequence ${cur.n}, step ${cur.i + 1} of ${cur.steps.length}: ${stepName(st)}`
      + (st.tempo ? `  ♩=${Math.round(st.tempo)}` : ""));
    for (let b = 0; b < BARS; b++) {
      lines.push(`    bar ${b + 1}:  ` + cur.combos.slice(b * BAR, (b + 1) * BAR).map(label).join("   "));
    }
    lines.push("");
  }
  lines.push("  Combos (right and in time):");
  lines.push("     " + [...LETTERS].map((b) => b.padStart(6)).join(""));
  for (const a of LETTERS) {
    let row = `  ${a}  `;
    for (const b of LETTERS) {
      const cs = s.combos[a + b];
      if (a === b) row += dim("     ·");
      else if (!cs || !cs.n) row += dim("     -");
      else {
        const pct = cs.ok / cs.n;
        const cell = `${Math.round(pct * 100)}%`.padStart(6);
        row += pct >= 0.9 ? green(cell) : pct >= 0.7 ? yellow(cell) : red(cell);
      }
    }
    lines.push(row);
  }
  lines.push("");
  return lines.join("\n");
}

const HELP = `usage: node noterhythm.js [options]

Learn ascending note distances in time with a metronome.

options:
  --data DIR         folder for progress files (default: ${dataDir()})
  --stats            print stats and exit
  --target BPM       tempo a step must be clean at; saved
  --start BPM        tempo new material starts at; saved
  --tolerance F      how far off the beat counts, as a fraction of a beat; saved
  --calibrate        measure your tap/sound delay
  --mute             no clicks this time
  --reset            start from scratch (keeps the answer log)
  -h, --help         show this help`;

function parseArgs(argv) {
  const args = { data: dataDir() };
  for (let k = 0; k < argv.length; k++) {
    const a = argv[k];
    const value = () => {
      if (k + 1 >= argv.length) throw new Error(`${a} needs a value`);
      return argv[++k];
    };
    if (a === "-h" || a === "--help") args.help = true;
    else if (a === "--data") args.data = value();
    else if (a === "--stats") args.stats = true;
    else if (a === "--calibrate") args.calibrate = true;
    else if (a === "--mute") args.mute = true;
    else if (a === "--reset") args.reset = true;
    else if (a === "--target" || a === "--start") args[a.slice(2)] = parseInt(value(), 10);
    else if (a === "--tolerance") args.tolerance = parseFloat(value());
    else throw new Error(`unknown option ${a}`);
  }
  return args;
}

async function main() {
  let args;
  try {
    args = parseArgs(process.argv.slice(2));
  } catch (e) {
    console.error(e.message + "\n\n" + HELP);
    process.exit(2);
  }
  if (args.help) {
    console.log(HELP);
    return;
  }
  const statePath = path.join(args.data, "state.json");
  const logPath = path.join(args.data, "answers.jsonl");
  fs.mkdirSync(args.data, { recursive: true });
  if (args.reset && fs.existsSync(statePath)) {
    fs.renameSync(statePath, statePath + ".bak");
    console.log(`Old progress moved to ${statePath}.bak`);
  }
  const state = loadState(statePath);
  for (const k of ["target", "start", "tolerance"]) {
    if (args[k] !== undefined && !Number.isNaN(args[k])) {
      state.settings[k] = args[k];
      saveState(state, statePath);
    }
  }
  if (args.stats) {
    console.log(state.current ? statsText(new Coach(state)) : "No progress yet.");
    return;
  }
  if (!process.stdin.isTTY) {
    console.error("NoteRhythm needs an interactive terminal.");
    process.exit(1);
  }
  if (args.calibrate) await calibrate(statePath, args.mute);
  else await run(statePath, logPath, args.mute);
  process.exit(0);
}

module.exports = {
  LETTERS, ALL_COMBOS, degree, label, counting, HALF, BAR, BARS, START_BPM, TARGET_BPM, BPM_STEP,
  STRIKES, POOL_START, NOVEL_PER_SEQ, DROP_PER_SEQ, newState, Random, buildPlan, span, stepName,
  Coach, loadState, saveState, panelLines, toneWav,
};

if (require.main === module) main();
