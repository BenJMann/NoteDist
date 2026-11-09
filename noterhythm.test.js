"use strict";
// node --test noterhythm.test.js

const test = require("node:test");
const assert = require("node:assert/strict");
const fs = require("fs");
const os = require("os");
const path = require("path");
const nr = require("./noterhythm.js");

const newCoach = (seed) => {
  const c = new nr.Coach(null, new nr.Random(seed));
  c.ensure();
  return c;
};
const name = (c) => nr.stepName(c.step());

function answerAll(coach, ok = () => true, off = 0) {
  // One repetition answered right on the beat; ok(slot) false makes that one wrong.
  // A cards step on top is answered right first.
  clearCards(coach);
  const results = [];
  for (const i of coach.repSlots()) {
    if (i === null) continue;
    const r = { i, off };
    const right = nr.degree(coach.combo(i));
    r.key = String(ok(r) ? right : (right % 6) + 2);
    results.push(r);
  }
  return coach.recordRep(results);
}

function answerCards(coach, wrong = []) {
  const items = coach.cardItems();
  coach.recordCards(items.map((it) => ({
    combo: it.combo, show: it.show,
    key: String(wrong.includes(it.combo) && !it.show ? (nr.degree(it.combo) % 6) + 2 : nr.degree(it.combo)),
  })));
  return items;
}

function clearCards(coach) {
  while (coach.step().kind === "cards") answerCards(coach);
}

function until(coach, stepName) {
  while (name(coach) !== stepName) answerAll(coach);
}

test("degrees", () => {
  for (const [combo, want] of Object.entries({ CG: 5, BG: 6, AC: 3, CD: 2, BC: 2, DC: 7, EB: 5 })) {
    assert.equal(nr.degree(combo), want, combo);
  }
});

test("ascending only", () => {
  assert.equal(nr.ALL_COMBOS.length, 42);
  assert.deepEqual(new Set(nr.ALL_COMBOS.map(nr.degree)), new Set([2, 3, 4, 5, 6, 7]));
});

test("plan order follows the build-up", () => {
  const pair = (a, b) => [`bar ${a}, first half`, `bar ${a}, second half`, `bar ${a}`,
    `bar ${b}, first half`, `bar ${b}, second half`, `bar ${b}`, `bars ${a} and ${b} alternating`, `bars ${a}–${b}`];
  const want = [...pair(1, 2), ...pair(3, 4), "bars 1–4", ...pair(5, 6), ...pair(7, 8), "bars 5–8", "bars 1–8"];
  assert.deepEqual(nr.buildPlan().map(nr.stepName), want);
});

test("new combos are shown then recalled before timing", () => {
  const c = newCoach(1);
  assert.equal(c.step().kind, "cards");
  const firstTwo = [c.combo(0), c.combo(1)];
  const shown = answerCards(c);
  assert.deepEqual(shown.map((it) => it.combo), firstTwo);
  assert.ok(shown.every((it) => it.show));
  const recall = answerCards(c, [firstTwo[0]]);
  assert.ok(!recall.some((it) => it.show));
  assert.deepEqual(recall.map((it) => it.combo).sort(), [...firstTwo].sort());
  assert.equal(c.step().kind, "cards");
  assert.deepEqual(answerCards(c).map((it) => it.combo), [firstTwo[0]]);
  assert.equal(c.step().kind, "drill");
  assert.equal(c.step().tempo, nr.START_BPM);
});

test("recall mixes in learned combos", () => {
  const c = newCoach(1);
  clearCards(c);
  while (c.step().kind !== "cards") {
    c.recordRep(c.repSlots().map((i) => ({ i, key: String(nr.degree(c.combo(i))), off: 0 })));
  }
  assert.equal(c.cur.i, 1);
  answerCards(c);
  assert.ok(c.cardItems().length > 2);
});

test("clean at 60 moves on", () => {
  const c = newCoach(1);
  clearCards(c);
  assert.equal(c.step().tempo, 60);
  answerAll(c);
  assert.equal(c.cur.i, 1);
});

test("streak climbs back to target", () => {
  const c = newCoach(1);
  clearCards(c);
  c.step().tempo = 42;
  const tempos = [];
  while (c.cur.i === 0) {
    tempos.push(c.step().tempo);
    answerAll(c);
  }
  assert.deepEqual(tempos, [42, 48, 60]);
});

test("wide timing window", () => {
  const c = newCoach(1);
  assert.ok(answerAll(c, undefined, 0.45).every(Boolean));
  assert.ok(!answerAll(c, undefined, -0.55).some(Boolean));
});

test("one or two misses repeat the same step", () => {
  const c = newCoach(1);
  until(c, "bars 1–2");
  for (let k = 0; k < 2; k++) {
    answerAll(c, (r) => r.i !== 5);
    assert.equal(name(c), "bars 1–2");
    assert.equal(c.step().tempo, 60);
    assert.deepEqual(c.cur.stack, []);
  }
  answerAll(c);
  clearCards(c);
  assert.equal(name(c), "bar 3, first half");
});

test("misses are counted in a row", () => {
  const c = newCoach(1);
  clearCards(c);
  const st = c.step();
  st.tempo = 54;
  answerAll(c, (r) => r.i !== 1);
  answerAll(c, (r) => r.i !== 1);
  answerAll(c);
  answerAll(c, (r) => r.i !== 1);
  assert.equal(st.misses, 1);
});

test("third miss rebuilds from the half", () => {
  const c = newCoach(1);
  until(c, "bars 1–2");
  for (let k = 0; k < 3; k++) answerAll(c, (r) => r.i !== 5);
  assert.equal(name(c), "bar 2, first half");
  assert.equal(c.step().tempo, 60 - nr.BPM_STEP);
  answerAll(c);
  assert.equal(name(c), "bar 2");
  answerAll(c);
  assert.equal(name(c), "bars 1–2");
  assert.equal(c.step().tempo, 60 - nr.BPM_STEP);
  assert.deepEqual(c.cur.stack, []);
  answerAll(c);
  answerAll(c);
  clearCards(c);
  assert.equal(name(c), "bar 3, first half");
});

test("third miss in a half just slows it", () => {
  const c = newCoach(1);
  clearCards(c);
  for (let k = 0; k < 3; k++) answerAll(c, (r) => r.i !== 1);
  assert.equal(name(c), "bar 1, first half");
  assert.equal(c.step().tempo, 60 - nr.BPM_STEP);
  assert.deepEqual(c.cur.stack, []);
});

test("known material starts at the target", () => {
  const c = newCoach(1);
  until(c, "bar 1");
  assert.equal(c.step().tempo, nr.TARGET_BPM);
});

test("alternation has a gap", () => {
  const c = newCoach(1);
  while (c.step().kind !== "alt") answerAll(c);
  assert.deepEqual(c.repSlots(), [0, 1, 2, 3, null, 4, 5, 6, 7]);
});

test("whole sequence completes and the next starts", () => {
  const c = newCoach(1);
  const first = [...c.cur.combos];
  for (let k = 0; k < 2000 && !c.s.done; k++) answerAll(c);
  assert.equal(c.s.done, 1);
  assert.deepEqual(c.s.history, [first]);
  assert.equal(c.cur.n, 2);
  assert.ok(c.events.some((e) => e.includes("complete")));
});

test("panel shows all bars and the fix-up", () => {
  const c = newCoach(1);
  until(c, "bars 1–2");
  for (let k = 0; k < 3; k++) answerAll(c, (r) => r.i !== 5);
  const plain = nr.panelLines(c, 4).map((l) => l.replace(/\x1b\[[0-9;]*m/g, ""));
  assert.equal(plain.length, 3 + 2 * 3);
  for (let b = 1; b <= 8; b++) assert.ok(plain.some((l) => l.includes(`bar ${b}`)));
  assert.ok(plain[1].includes("then back to bars 1–2"));
  assert.ok(plain[5].includes("━━━ ─── ┄┄┄ ┄┄┄"));
  assert.equal(nr.panelLines(c, null, 60).length, 3 + 4 * 3);
});

test("sequences are varied but familiar", () => {
  const c = new nr.Coach(null, new nr.Random(3));
  const seqs = [], pools = [];
  for (let k = 0; k < 8; k++) {
    c.newSequence();
    seqs.push(c.cur.combos);
    pools.push([...c.s.pool]);
  }
  seqs.forEach((seq, k) => {
    assert.equal(seq.length, 32);
    for (let j = 1; j < seq.length; j++) assert.notEqual(seq[j], seq[j - 1]);
    assert.ok(seq.every((x) => pools[k].includes(x)));
    for (let b = 1; b < 8; b++) {
      let diff = 0;
      for (let j = 0; j < 4; j++) if (seq[b * 4 - 4 + j] !== seq[b * 4 + j]) diff++;
      assert.ok(diff <= 3);
    }
  });
  assert.equal(pools[0].length, nr.POOL_START);
  for (let k = 1; k < pools.length; k++) {
    const a = pools[k - 1], b = pools[k];
    assert.ok(b.filter((x) => !a.includes(x)).length <= nr.NOVEL_PER_SEQ);
    assert.ok(a.filter((x) => b.includes(x)).length >= a.length - nr.DROP_PER_SEQ - 1);
  }
  const used = seqs.map((_, k) => new Set(seqs.slice(0, k + 1).flat()).size);
  assert.deepEqual([...used].sort((x, y) => x - y), used);
  assert.ok(used[used.length - 1] > used[0] + 8);
});

test("new combos feature", () => {
  const c = new nr.Coach(null, new nr.Random(4));
  c.newSequence();
  c.newSequence();
  for (const n of c.cur.novel) assert.ok(c.cur.combos.filter((x) => x === n).length >= 3);
});

test("storage round trip", () => {
  const c = newCoach(5);
  for (let k = 0; k < 30; k++) answerAll(c);
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), "nr-test-"));
  const file = path.join(dir, "x", "state.json");
  nr.saveState(c.s, file);
  const c2 = new nr.Coach(nr.loadState(file));
  fs.rmSync(dir, { recursive: true });
  assert.deepEqual(c2.s, c.s);
  assert.deepEqual(c2.repSlots(), c.repSlots());
});

test("click wav is a valid PCM file", () => {
  const buf = nr.toneWav(1000, 0.035, 0.6);
  assert.equal(buf.toString("ascii", 0, 4), "RIFF");
  assert.equal(buf.toString("ascii", 8, 12), "WAVE");
  assert.equal(buf.readUInt32LE(40), buf.length - 44);
});
