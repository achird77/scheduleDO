import React, { useState, useMemo, useRef, useCallback } from "react";
import {
  Calendar, Users, Clock, Sliders, Wand2, RefreshCw,
  FileSpreadsheet, FileText, Save, FolderOpen, ListChecks, AlertTriangle,
  HelpCircle, Repeat, CalendarOff,
} from "lucide-react";

// Duty Officer engine v2 — adds 3-4 week shift tours (a DO holds one shift type
// for 3-4 consecutive weeks, then rotates to a different type).
// Duty Officer engine v3 — original (pre-tour) model, plus:
//  • PTO / sick pre-blocking (cfg.unavailable[o] = [dayIndex,...])
//  • continuity from a previous period (cfg.history = prev period's last week,
//    cfg.carry = prior cumulative tallies) so blocks/rest/gaps & fairness carry over
//  • repair(): patch a generated roster when officers go sick / on PTO
const OFF = 0, DAY = 1, NIGHT = 2, DW = 3;
const CODE_NAME = { 0: "OFF", 1: "DAY", 2: "NIGHT", 3: "DAYWORK" };
const NAME_CODE = { OFF: 0, DAY: 1, NIGHT: 2, DAYWORK: 3, PTO: 0, SICK: 0 };

function mulberry32(a) {
  return function () {
    a |= 0; a = (a + 0x6D2B79F5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}
function shuffle(arr, rng) {
  for (let i = arr.length - 1; i > 0; i--) { const j = Math.floor(rng() * (i + 1)); [arr[i], arr[j]] = [arr[j], arr[i]]; }
  return arr;
}
const weekdayOf = (sd, t) => (sd + t) % 7;
function runLenBack(a, o, end, S) { let n = 0, t = end; while (t >= 0 && a[o][t] === S) { n++; t--; } return n; }
function lastWorkInfo(a, o, t) { for (let d = t - 1; d >= 0; d--) if (a[o][d] !== OFF) return { day: d, type: a[o][d] }; return { day: -1, type: OFF }; }

// Continuity: if a previous week is supplied, prepend it as a fixed "week 0".
function expand(cfg) {
  if (!cfg.history) return { ecfg: cfg, off: 0 };
  const off = 7;
  const ecfg = Object.assign({}, cfg, {
    weeks: cfg.weeks + 1,
    unavailable: cfg.unavailable ? cfg.unavailable.map(arr => (arr || []).map(t => t + off)) : null,
  });
  return { ecfg, off };
}

function assignDayWork(cfg, rng, off, history) {
  const N = cfg.officers.length, W = cfg.weeks, D = cfg.dayworkPerWeek;
  const dwWeek = Array.from({ length: N }, () => new Array(W).fill(false));
  const count = new Array(N).fill(0);
  let prev = [];
  let firstNew = 0;
  if (off && history) {                       // week 0 fixed from history
    firstNew = 1;
    for (let o = 0; o < N; o++) if (history[o].some(c => c === DW)) { dwWeek[o][0] = true; count[o]++; prev.push(o); }
  }
  if (D <= 0) return dwWeek;
  for (let w = firstNew; w < W; w++) {
    const order = shuffle([...Array(N).keys()], rng);
    order.sort((a, b) => count[a] - count[b]);
    const chosen = [];
    const free = (o) => {
      if (w !== firstNew || !history) return true; // only filter at the boundary week
      const gwh = Math.max(1, cfg.switchWorkhoursOffDays);
      for (let k = 1; k <= gwh; k++) { const c = history[o][7 - k]; if (c === DAY || c === NIGHT) return false; }
      return true;
    };
    for (const o of order) { if (chosen.length >= D) break; if (!prev.includes(o) && free(o)) chosen.push(o); }
    for (const o of order) { if (chosen.length >= D) break; if (!chosen.includes(o) && free(o)) chosen.push(o); }
    for (const o of order) { if (chosen.length >= D) break; if (!chosen.includes(o)) chosen.push(o); }
    for (const o of chosen) { dwWeek[o][w] = true; count[o]++; }
    prev = chosen;
  }
  return dwWeek;
}

function buildBlocked(cfg, dwWeek, off) {
  const N = cfg.officers.length, T = cfg.weeks * 7, gwh = Math.max(1, cfg.switchWorkhoursOffDays);
  const blocked = Array.from({ length: N }, () => new Array(T).fill(false));
  for (let o = 0; o < N; o++) {
    for (let w = 0; w < cfg.weeks; w++) {
      if (!dwWeek[o][w]) continue;
      const ws = w * 7;
      for (let t = ws; t < Math.min(ws + 7, T); t++) blocked[o][t] = true;
      for (let k = 1; k <= gwh; k++) { const d = ws - k; if (d >= (off || 0)) blocked[o][d] = true; }
      const fri = ws + 4;
      for (let k = 1; k <= gwh; k++) { const d = fri + k; if (d < T) blocked[o][d] = true; }
    }
    if (cfg.unavailable && cfg.unavailable[o]) for (const t of cfg.unavailable[o]) if (t >= 0 && t < T) blocked[o][t] = true;
    for (let t = 0; t < T - 1; t++)
      if (weekdayOf(cfg.startDow, t) === 5 && (blocked[o][t] || blocked[o][t + 1]))
        blocked[o][t] = blocked[o][t + 1] = true;
  }
  return blocked;
}

// per-type block-length limits (fall back to the shared values for old sessions)
const minC = (cfg, S) => S === NIGHT ? (cfg.minConsecutiveNight ?? cfg.minConsecutive) : (cfg.minConsecutiveDay ?? cfg.minConsecutive);
const maxC = (cfg, S) => S === NIGHT ? (cfg.maxConsecutiveNight ?? cfg.maxConsecutive) : (cfg.maxConsecutiveDay ?? cfg.maxConsecutive);

// most recent watch-block type before day t, and how many same-type blocks end the run
function typeRunInfo(a, o, t) {
  let d = t - 1;
  while (d >= 0 && (a[o][d] === OFF || a[o][d] === DW)) d--;
  if (d < 0) return { lastType: OFF, runBlocks: 0 };
  const lastType = a[o][d];
  let runBlocks = 0;
  while (d >= 0) {
    while (d >= 0 && (a[o][d] === OFF || a[o][d] === DW)) d--;
    if (d < 0 || a[o][d] !== lastType) break;
    runBlocks++;
    while (d >= 0 && a[o][d] === lastType) d--;
  }
  return { lastType, runBlocks };
}
// may officer o start a new block of type S on day t, given the same-type-run rule?
function typeAllowed(cfg, a, o, t, S) {
  const minB = cfg.minBlocksPerType ?? 1, maxB = cfg.maxBlocksPerType ?? 99;
  const { lastType, runBlocks } = typeRunInfo(a, o, t);
  if (lastType === OFF) return true;
  if (S === lastType) return runBlocks < maxB;   // keep same type only if under the cap
  return runBlocks >= minB;                       // switch only after enough same-type blocks
}

function canStartNew(cfg, a, o, t, S) {
  const T = cfg.weeks * 7;
  if (weekdayOf(cfg.startDow, t) === 6) return false;
  if (a.__blocked[o][t]) return false;
  if (t === T - 1 && minC(cfg, S) > 1) return false;
  if (minC(cfg, S) > 1 && t + 1 < T && a.__blocked[o][t + 1]) return false;
  const { day: e, type: lt } = lastWorkInfo(a, o, t);
  if (e < 0) return true;
  const gap = t - e - 1;
  if (lt === DW) return gap >= cfg.switchWorkhoursOffDays;
  if (lt === S) return gap >= Math.max(1, cfg.restDaysAfterBlock);
  return gap >= cfg.switchDaynightOffDays;
}

function slotChoices(cfg, a, t, S, rng) {
  const N = cfg.officers.length, wd = weekdayOf(cfg.startDow, t);
  if (wd === 6) {
    for (let o = 0; o < N; o++) if (a[o][t - 1] === S && !a.__blocked[o][t])
      return { forced: runLenBack(a, o, t - 1, S) < maxC(cfg, S) ? o : -1 };
    return { forced: -1 };
  }
  for (let o = 0; o < N; o++) if (t > 0 && a[o][t - 1] === S && !a.__blocked[o][t]) {
    const rl = runLenBack(a, o, t - 1, S);
    if (rl < minC(cfg, S)) return { forced: rl < maxC(cfg, S) ? o : -1 };
  }
  const opts = [];
  for (let o = 0; o < N; o++) {
    if (a.__blocked[o][t]) continue;
    if (t > 0 && a[o][t - 1] === S) {
      const rl = runLenBack(a, o, t - 1, S);
      if (rl >= minC(cfg, S) && rl < maxC(cfg, S)) opts.push(o);
    } else if (canStartNew(cfg, a, o, t, S) && typeAllowed(cfg, a, o, t, S)) opts.push(o);
  }
  const isWknd = wd >= 5, cost = {}, carry = cfg.carry, prefer = cfg.preferGrid, pFrom = cfg.preferFrom || 0;
  for (const o of opts) {
    let days = 0, dayC = 0, nightC = 0, wknC = 0;
    for (let dd = 0; dd < t; dd++) {
      const c = a[o][dd]; if (c === OFF) continue; days++;
      if (c === DAY) dayC++; else if (c === NIGHT) nightC++;
      if (c !== DW && weekdayOf(cfg.startDow, dd) >= 5) wknC++;
    }
    if (carry) { dayC += carry.day[o] || 0; nightC += carry.night[o] || 0; wknC += carry.weekend[o] || 0; days += (carry.day[o] || 0) + (carry.night[o] || 0); }
    const bal = S === DAY ? dayC - nightC : nightC - dayC;
    cost[o] = days * 1.0 + (isWknd ? wknC * 3.0 : 0) + bal * 1.5 + rng() * 1.5;
    if (wd === 5 && (a[o][t - 7] === DAY || a[o][t - 7] === NIGHT || (t - 6 >= 0 && (a[o][t - 6] === DAY || a[o][t - 6] === NIGHT)))) cost[o] += 8; // avoid back-to-back weekends
    if (prefer && t >= pFrom && prefer[o][t] === S) cost[o] -= 2; // gentle nudge toward the existing roster
  }
  opts.sort((x, y) => cost[x] - cost[y]);
  return { options: opts };
}

function tileWatches(cfg, dwWeek, rng, budget, off, history) {
  const N = cfg.officers.length, T = cfg.weeks * 7;
  const a = Array.from({ length: N }, () => new Array(T).fill(OFF));
  a.__dw = dwWeek;
  a.__blocked = buildBlocked(cfg, dwWeek, off);
  if (off && history) for (let o = 0; o < N; o++) for (let k = 0; k < 7; k++) a[o][k] = history[o][k]; // fixed week 0
  for (let o = 0; o < N; o++)
    for (let w = 0; w < cfg.weeks; w++)
      if (dwWeek[o][w] && !(off && w === 0))
        for (let t = w * 7; t < Math.min(w * 7 + 7, T); t++)
          if (weekdayOf(cfg.startDow, t) < 5) a[o][t] = DW;
  const ctr = { n: 0 };
  function rec(t) {
    if (++ctr.n > budget) return false;
    if (t >= T) return true;
    const dc = slotChoices(cfg, a, t, DAY, rng), nc = slotChoices(cfg, a, t, NIGHT, rng);
    const dl = dc.forced !== undefined ? [dc.forced] : dc.options;
    const nl = nc.forced !== undefined ? [nc.forced] : nc.options;
    if (dl.includes(-1) || nl.includes(-1) || !dl.length || !nl.length) return false;
    for (const dO of dl) {
      if (dO < 0) continue; a[dO][t] = DAY;
      for (const nO of nl) {
        if (nO < 0 || nO === dO || a[nO][t] !== OFF) continue;
        a[nO][t] = NIGHT;
        if (rec(t + 1)) return true;
        a[nO][t] = OFF;
      }
      a[dO][t] = OFF;
    }
    return false;
  }
  return rec(off || 0) ? a : null;
}

function hoursOf(cfg, a, o) { let h = 0; for (const c of a[o]) h += c === DAY ? cfg.dayHours : c === NIGHT ? cfg.nightHours : c === DW ? cfg.dayworkHours : 0; return h; }
const countOf = (a, o, S) => a[o].reduce((x, c) => x + (c === S ? 1 : 0), 0);
function weekendOf(cfg, a, o) { const T = cfg.weeks * 7; let n = 0; for (let t = 0; t < T; t++) if (weekdayOf(cfg.startDow, t) >= 5 && (a[o][t] === DAY || a[o][t] === NIGHT)) n++; return n; }
function weekendsWorked(cfg, a, o) {
  const T = cfg.weeks * 7, res = [];
  for (let w = 0; w < cfg.weeks; w++) { const sat = w * 7 + 5; let on = false; for (const t of [sat, sat + 1]) if (t < T && (a[o][t] === DAY || a[o][t] === NIGHT)) on = true; res.push(on); }
  return res;
}
function softScore(cfg, a) {
  const N = cfg.officers.length, sp = arr => Math.max(...arr) - Math.min(...arr), carry = cfg.carry;
  const hrs = [...Array(N)].map((_, o) => hoursOf(cfg, a, o) + (carry ? carry.hours[o] || 0 : 0));
  const days = [...Array(N)].map((_, o) => countOf(a, o, DAY) + (carry ? carry.day[o] || 0 : 0));
  const nights = [...Array(N)].map((_, o) => countOf(a, o, NIGHT) + (carry ? carry.night[o] || 0 : 0));
  const wknd = [...Array(N)].map((_, o) => weekendOf(cfg, a, o) + (carry ? carry.weekend[o] || 0 : 0));
  let s = cfg.wHours * sp(hrs);
  for (let o = 0; o < N; o++) s += cfg.wDaynightSelf * Math.abs(days[o] - nights[o]);
  s += cfg.wDaynightSpread * (sp(days) + sp(nights));
  s += cfg.wWeekend * sp(wknd);
  // penalise back-to-back weekends for the same officer ("no consecutive weekends if possible")
  let consec = 0;
  for (let o = 0; o < N; o++) { const ww = weekendsWorked(cfg, a, o); for (let w = 0; w < ww.length - 1; w++) if (ww[w] && ww[w + 1]) consec++; }
  s += (cfg.wWeekend + cfg.wDaynightSpread) * consec;
  return s;
}

function generateSchedule(cfg0, seed, opts = {}) {
  const timeLimit = opts.timeLimitMs || 1500, maxAttempts = opts.maxAttempts || 6000, budget = opts.budget || 60000;
  const { ecfg, off } = expand(cfg0);
  const history = cfg0.history || null;
  const rng = mulberry32(seed >>> 0), start = Date.now();
  let best = null, bestScore = Infinity, attempts = 0;
  while (attempts < maxAttempts && Date.now() - start < timeLimit) {
    attempts++;
    const dwWeek = assignDayWork(ecfg, rng, off, history);
    const a = tileWatches(ecfg, dwWeek, rng, budget, off, history);
    if (!a) continue;
    const sc = softScore(ecfg, a);
    if (sc < bestScore) { bestScore = sc; best = a.map(r => r.slice()); }
    if (sc === 0) break;
  }
  if (!best)
    return { ok: false, status: "INFEASIBLE", message: "No valid roster exists for these settings. Try adding an officer, reducing day-work per week, easing the time-off requests, allowing fewer blocks before a day↔night switch, or relaxing the consecutive/rest rules.", attempts };
  // strip the fixed history week before returning
  const grid = best.map(row => row.slice(off).map(c => CODE_NAME[c]));
  return { ok: true, status: bestScore === 0 ? "OPTIMAL" : "FEASIBLE", grid, score: bestScore, attempts };
}

function validate(cfg, grid) {
  const N = cfg.officers.length, T = cfg.weeks * 7, code = NAME_CODE;
  const g = grid.map(r => r.map(x => code[x] ?? 0)), problems = [];
  for (let t = 0; t < T; t++) {
    let dc = 0, nc = 0;
    for (let o = 0; o < N; o++) { if (g[o][t] === DAY) dc++; if (g[o][t] === NIGHT) nc++; }
    if (dc !== 1) problems.push(`Day ${t + 1}: ${dc} on day watch (need 1)`);
    if (nc !== 1) problems.push(`Day ${t + 1}: ${nc} on night watch (need 1)`);
  }
  const gdn = Math.max(1, cfg.switchDaynightOffDays), gwh = Math.max(1, cfg.switchWorkhoursOffDays);
  for (let o = 0; o < N; o++) {
    const row = g[o];
    for (let t = 0; t < T; t++) {
      for (let k = 1; k <= gdn; k++) if (t + k < T) {
        if (row[t] === DAY && row[t + k] === NIGHT) problems.push(`${cfg.officers[o]}: day→night gap < ${gdn} (around day ${t + 1})`);
        if (row[t] === NIGHT && row[t + k] === DAY) problems.push(`${cfg.officers[o]}: night→day gap < ${gdn} (around day ${t + 1})`);
      }
      for (let k = 1; k <= gwh; k++) if (t + k < T) {
        const x = row[t], y = row[t + k];
        if (((x === DAY || x === NIGHT) && y === DW) || (x === DW && (y === DAY || y === NIGHT))) problems.push(`${cfg.officers[o]}: 12h↔8h gap < ${gwh} (around day ${t + 1})`);
      }
    }
    let run = 0, runType = 0;
    for (let t = 0; t <= T; t++) {
      const c = t < T ? row[t] : OFF;
      const isw = c === DAY || c === NIGHT;
      if (isw && (run === 0 || c === runType)) { run++; runType = c; }
      else {
        if (run > 0) {
          const lab = runType === NIGHT ? "night" : "day";
          if (run < minC(cfg, runType)) problems.push(`${cfg.officers[o]}: ${lab} block of ${run} < min ${minC(cfg, runType)} (ending day ${t})`);
          if (run > maxC(cfg, runType)) problems.push(`${cfg.officers[o]}: ${lab} block of ${run} > max ${maxC(cfg, runType)} (ending day ${t})`);
        }
        if (isw) { run = 1; runType = c; } else { run = 0; runType = 0; }
      }
    }
    // consecutive same-type blocks before switching day↔night
    if ((cfg.minBlocksPerType ?? 1) > 1 || (cfg.maxBlocksPerType ?? 99) < 99) {
      const minB = cfg.minBlocksPerType ?? 1, maxB = cfg.maxBlocksPerType ?? 99;
      const blocks = []; let cur = 0, rd = 0;
      for (let t = 0; t <= T; t++) {
        const c = t < T ? g[o][t] : 0, isw = c === DAY || c === NIGHT;
        if (isw && (rd === 0 || c === cur)) { rd++; cur = c; }
        else { if (rd > 0) blocks.push(cur); if (isw) { rd = 1; cur = c; } else { rd = 0; cur = 0; } }
      }
      const firstExempt = !!cfg.history;
      let i = 0;
      while (i < blocks.length) {
        let j = i; while (j < blocks.length && blocks[j] === blocks[i]) j++;
        const len = j - i, isLast = j === blocks.length, lab = blocks[i] === NIGHT ? "night" : "day";
        if (len > maxB) problems.push(`${cfg.officers[o]}: ${len} ${lab} blocks in a row > max ${maxB} before switching`);
        if (len < minB && !isLast && !(i === 0 && firstExempt)) problems.push(`${cfg.officers[o]}: only ${len} ${lab} block(s) before switching < min ${minB}`);
        i = j;
      }
    }
  }
  for (let t = 0; t < T - 1; t++) if (weekdayOf(cfg.startDow, t) === 5)
    for (let o = 0; o < N; o++) {
      if (g[o][t] === DAY && g[o][t + 1] !== DAY) problems.push(`${cfg.officers[o]}: Saturday day watch not matched on Sunday (day ${t + 1})`);
      if (g[o][t] === NIGHT && g[o][t + 1] !== NIGHT) problems.push(`${cfg.officers[o]}: Saturday night watch not matched on Sunday (day ${t + 1})`);
    }
  return problems;
}

// Patch a generated roster after officers become unavailable (sick / PTO).
// Re-cover a roster after watch officers go sick / off.
//   1. if a day-work DO is on duty that weekday, move them onto the open watch (cheapest fix)
//   2. otherwise re-generate from the affected day on, keeping the rest as close to the
//      original as possible (minimal impact)
// Day-work absences need no re-cover. unavail: [{o,t}]. Returns {grid, changes, notes, unresolved, method, changed}.
function regenSuffix(cfg, gridCodes, fromDay, blockedAt, seed) {
  const N = cfg.officers.length, T = cfg.weeks * 7, budget = 200000;
  const dwWeek = Array.from({ length: N }, () => new Array(cfg.weeks).fill(false));
  for (let o = 0; o < N; o++) for (let w = 0; w < cfg.weeks; w++)
    for (let t = w * 7; t < Math.min(w * 7 + 7, T); t++) if (gridCodes[o][t] === DW) { dwWeek[o][w] = true; break; }
  const unav = Array.from({ length: N }, () => []);
  for (let o = 0; o < N; o++) for (let t = 0; t < T; t++) if (blockedAt[o][t]) unav[o].push(t);
  const cfg2 = Object.assign({}, cfg, { unavailable: unav, preferGrid: gridCodes, preferFrom: fromDay, history: null, carry: null });
  const rng = mulberry32(seed >>> 0);
  const a = Array.from({ length: N }, () => new Array(T).fill(OFF));
  a.__dw = dwWeek;
  a.__blocked = buildBlocked(cfg2, dwWeek, 0);
  for (let o = 0; o < N; o++) for (let t = 0; t < fromDay; t++) a[o][t] = gridCodes[o][t];               // fixed prefix
  for (let o = 0; o < N; o++) for (let w = 0; w < cfg.weeks; w++) if (dwWeek[o][w])
    for (let t = Math.max(fromDay, w * 7); t < Math.min(w * 7 + 7, T); t++) if (weekdayOf(cfg.startDow, t) < 5) a[o][t] = DW; // fixed day-work
  const ctr = { n: 0 };
  function rec(t) {
    if (++ctr.n > budget) return false;
    if (t >= T) return true;
    const dc = slotChoices(cfg2, a, t, DAY, rng), nc = slotChoices(cfg2, a, t, NIGHT, rng);
    const dl = dc.forced !== undefined ? [dc.forced] : dc.options;
    const nl = nc.forced !== undefined ? [nc.forced] : nc.options;
    if (dl.includes(-1) || nl.includes(-1) || !dl.length || !nl.length) return false;
    for (const dO of dl) {
      if (dO < 0) continue; a[dO][t] = DAY;
      for (const nO of nl) {
        if (nO < 0 || nO === dO || a[nO][t] !== OFF) continue;
        a[nO][t] = NIGHT;
        if (rec(t + 1)) return true;
        a[nO][t] = OFF;
      }
      a[dO][t] = OFF;
    }
    return false;
  }
  return rec(fromDay) ? a : null;
}

function introducesProblem(cfg, g, o, T) {
  const row = g[o], gdn = Math.max(1, cfg.switchDaynightOffDays), gwh = Math.max(1, cfg.switchWorkhoursOffDays);
  for (let t = 0; t < T; t++) {
    for (let k = 1; k <= gdn; k++) if (t + k < T) {
      if (row[t] === DAY && row[t + k] === NIGHT) return true;
      if (row[t] === NIGHT && row[t + k] === DAY) return true;
    }
    for (let k = 1; k <= gwh; k++) if (t + k < T) {
      const x = row[t], y = row[t + k];
      if (((x === DAY || x === NIGHT) && y === DW) || (x === DW && (y === DAY || y === NIGHT))) return true;
    }
  }
  let run = 0, runType = 0;
  for (let t = 0; t <= T; t++) {
    const c = t < T ? row[t] : OFF, isw = c === DAY || c === NIGHT;
    if (isw && (run === 0 || c === runType)) { run++; runType = c; }
    else { if (run > 0 && (run < minC(cfg, runType) || run > maxC(cfg, runType))) return true; if (isw) { run = 1; runType = c; } else { run = 0; runType = 0; } }
  }
  return false;
}

function repair(cfg, gridStr, unavail) {
  const N = cfg.officers.length, T = cfg.weeks * 7;
  const g = gridStr.map(r => r.map(x => NAME_CODE[x] ?? 0));
  const orig = gridStr.map(r => r.map(x => NAME_CODE[x] ?? 0));
  const changes = [], notes = [], unresolved = [];
  const blockedAt = Array.from({ length: N }, () => new Array(T).fill(false));
  const wkPair = (t) => weekdayOf(cfg.startDow, t) === 5 ? [t, t + 1] : weekdayOf(cfg.startDow, t) === 6 ? [t - 1, t] : [t];
  const labelOf = (S) => S === NIGHT ? "night watch" : "day watch";
  let method = "none";

  // 1. apply the absences; collect open watch slots (weekend slots expand to the pair)
  const freed = [];
  for (const { o, t } of unavail) {
    if (o < 0 || o >= N || t < 0 || t >= T) continue;
    const c = g[o][t];
    if (c === DAY || c === NIGHT) {
      for (const x of wkPair(t).filter(x => x >= 0 && x < T)) {
        if (g[o][x] === c) { changes.push({ o, t: x, from: CODE_NAME[c], to: "OFF" }); g[o][x] = OFF; }
        blockedAt[o][x] = true;
        if (!freed.some(f => f.t === x && f.S === c)) freed.push({ t: x, S: c });
      }
    } else if (c === DW) { changes.push({ o, t, from: "DAYWORK", to: "OFF" }); g[o][t] = OFF; } // day-work: no re-cover needed
  }
  if (!freed.length) return { grid: g.map(r => r.map(c => CODE_NAME[c])), changes, notes, unresolved, method, changed: changes.length };

  // 2. If every open slot is a weekday with a distinct day-work DO free, cover with day-work DOs.
  const allWeekday = freed.every(f => weekdayOf(cfg.startDow, f.t) < 5);
  let dwPlan = null;
  if (allWeekday) {
    dwPlan = []; const used = {};
    for (const { t, S } of freed) {
      let p = -1;
      for (let q = 0; q < N; q++) if (g[q][t] === DW && !blockedAt[q][t] && !used[`${q}_${t}`]) { p = q; break; }
      if (p < 0) { dwPlan = null; break; }
      used[`${p}_${t}`] = true; dwPlan.push({ p, t, S });
    }
  }

  if (dwPlan) {
    for (const { p, t, S } of dwPlan) {
      g[p][t] = S;
      changes.push({ o: p, t, from: "DAYWORK", to: CODE_NAME[S], dwCover: true });
      notes.push(`${cfg.officers[p]} moved from day-work to ${labelOf(S)} for day ${t + 1}.`);
    }
    method = "daywork";
  } else {
    // 3. No day-work cover — re-generate so the rules still hold and weekends stay balanced.
    //    Re-tile from the Monday of the affected week (backing up a week at a time only if needed),
    //    choosing the result with the most equal weekend split, fewest back-to-back weekends,
    //    best overall balance, then the fewest changes.
    const earliest = Math.min(...freed.map(f => f.t));
    const weekStart = earliest - (earliest % 7);
    const levels = []; for (let fd = weekStart; fd >= 0; fd -= 7) levels.push(fd); if (levels[levels.length - 1] !== 0) levels.push(0);
    const wkDaysOf = (a, o) => { let n = 0; for (let w = 0; w < cfg.weeks; w++) for (const x of [w * 7 + 5, w * 7 + 6]) if (x < T && (a[o][x] === DAY || a[o][x] === NIGHT)) n++; return n; };
    const consecOf = (a) => { let c = 0; for (let o = 0; o < N; o++) { const ww = []; for (let w = 0; w < cfg.weeks; w++) { let on = false; for (const x of [w * 7 + 5, w * 7 + 6]) if (x < T && (a[o][x] === DAY || a[o][x] === NIGHT)) on = true; ww.push(on); } for (let w = 0; w < ww.length - 1; w++) if (ww[w] && ww[w + 1]) c++; } return c; };
    let chosen = null, usedStart = earliest; const t0 = Date.now();
    for (const fd of levels) {
      const cands = [];
      for (let s = 1; s <= 30 && Date.now() - t0 < 2200; s++) {
        const res = regenSuffix(cfg, g, fd, blockedAt, s * 4099 + fd);
        if (!res) continue;
        const wd = [...Array(N)].map((_, o) => wkDaysOf(res, o));
        let ch = 0; for (let o = 0; o < N; o++) for (let t = fd; t < T; t++) if (res[o][t] !== orig[o][t]) ch++;
        cands.push({ res, wkSp: Math.max(...wd) - Math.min(...wd), consec: consecOf(res), sc: softScore(cfg, res), ch });
      }
      if (cands.length) {
        cands.sort((a, b) => a.wkSp - b.wkSp || a.consec - b.consec || a.sc - b.sc || a.ch - b.ch);
        chosen = cands[0]; usedStart = fd; break;
      }
      if (Date.now() - t0 > 2200) break;
    }
    if (chosen) {
      for (let o = 0; o < N; o++) for (let t = usedStart; t < T; t++) g[o][t] = chosen.res[o][t];
      method = "regenerated";
      notes.push(`Re-generated from day ${usedStart + 1} on — weekends and shifts re-balanced across the team (${chosen.ch} cell(s) changed). Earlier days are unchanged.`);
    } else {
      // 4. Last resort — patch the open slot(s) locally (may bend a rest rule).
      method = "patched";
      const wkPairR = (t) => weekdayOf(cfg.startDow, t) === 5 ? [t, t + 1] : weekdayOf(cfg.startDow, t) === 6 ? [t - 1, t] : [t];
      for (const { t, S } of freed) {
        let cnt = 0; for (let o = 0; o < N; o++) if (g[o][t] === S) cnt++; if (cnt >= 1) continue;
        const pair = wkPairR(t).filter(x => x >= 0 && x < T);
        const cc = [...Array(N).keys()].filter(p => pair.every(x => g[p][x] === OFF && !blockedAt[p][x]));
        let pchosen = -1;
        for (const p of cc) { pair.forEach(x => { g[p][x] = S; }); if (!introducesProblem(cfg, g, p, T)) { pchosen = p; break; } pair.forEach(x => { g[p][x] = OFF; }); }
        if (pchosen < 0 && cc.length) { pchosen = cc[0]; pair.forEach(x => { g[pchosen][x] = S; }); }
        if (pchosen >= 0) { pair.forEach(x => changes.push({ o: pchosen, t: x, from: "OFF", to: CODE_NAME[S], fill: true })); notes.push(`${cfg.officers[pchosen]} covers the ${labelOf(S)} for day ${pair.map(x => x + 1).join("–")} (emergency cover — please review, it may bend a rest rule).`); }
        else unresolved.push({ t, slot: CODE_NAME[S] });
      }
    }
  }

  let changed = 0;
  for (let o = 0; o < N; o++) for (let t = 0; t < T; t++) if (g[o][t] !== orig[o][t]) changed++;
  return { grid: g.map(r => r.map(c => CODE_NAME[c])), changes, notes, unresolved, method, changed };
}

function metrics(cfg, grid) {
  const N = cfg.officers.length, T = cfg.weeks * 7;
  return [...Array(N)].map((_, o) => {
    let hours = 0, day = 0, night = 0, daywork = 0, weekend = 0;
    for (let t = 0; t < T; t++) {
      const c = grid[o][t];
      if (c === "DAY") { hours += cfg.dayHours; day++; }
      else if (c === "NIGHT") { hours += cfg.nightHours; night++; }
      else if (c === "DAYWORK") { hours += cfg.dayworkHours; daywork++; }
      if (weekdayOf(cfg.startDow, t) >= 5 && (c === "DAY" || c === "NIGHT")) weekend++;
    }
    return { hours, day, night, daywork, weekend };
  });
}


function rulesText(cfg) {
  return [
    `Every day has exactly one ${cfg.dayLabel} watch (${cfg.dayTime}, ${cfg.dayHours}h) and one ${cfg.nightLabel} watch (${cfg.nightTime}, ${cfg.nightHours}h).`,
    cfg.dayworkPerWeek > 0
      ? `${cfg.dayworkPerWeek} officer(s) per week on the 8h day-work shift (${cfg.dayworkLabel} ${cfg.dayworkTime}, ${cfg.dayworkHours}h), Mon–Fri, rotated week to week.`
      : `No 8h day-work shift in use.`,
    `Weekends: whoever works Saturday also works Sunday — one officer for the day watch, one for the night.`,
    (cfg.minConsecutiveDay === cfg.minConsecutiveNight && cfg.maxConsecutiveDay === cfg.maxConsecutiveNight)
      ? `Watch blocks run ${cfg.minConsecutiveDay ?? cfg.minConsecutive}–${cfg.maxConsecutiveDay ?? cfg.maxConsecutive} consecutive days, with at least ${cfg.restDaysAfterBlock} rest day(s) after a block.`
      : `Day-watch blocks run ${cfg.minConsecutiveDay}–${cfg.maxConsecutiveDay} consecutive days and night-watch blocks run ${cfg.minConsecutiveNight}–${cfg.maxConsecutiveNight} consecutive days, with at least ${cfg.restDaysAfterBlock} rest day(s) after any block.`,
    `Switching day ↔ night requires at least ${cfg.switchDaynightOffDays} day(s) off in between.`,
    ((cfg.minBlocksPerType ?? 1) > 1 || (cfg.maxBlocksPerType ?? 99) < 99)
      ? `Each officer stays on the same shift type for ${cfg.minBlocksPerType}–${cfg.maxBlocksPerType} blocks before switching between day and night watches.`
      : null,
    `Switching between a 12h watch and the 8h day-work shift requires at least ${cfg.switchWorkhoursOffDays} day(s) off in between.`,
    `Hours, day/night counts, and weekend duties are shared as evenly as possible across the team, and the same officer avoids working two weekends in a row wherever possible.`,
    `Approved PTO and sick days are kept clear of watches before the roster is built.`,
    `If a day- or night-watch officer goes sick after the roster is built: if a day-work officer is on duty that weekday they take the open watch; otherwise the roster is re-generated from the affected week on, keeping the rules and re-balancing weekends across the team. A sick day-work officer needs no cover.`,
  ].filter(Boolean);
}

/* ============================================================================
   Presentation helpers
============================================================================ */
const WD = ["Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"];
const SHIFT_STYLE = {
  DAY: { bg: "#c6e0b4", fg: "#1b5e20" },
  NIGHT: { bg: "#bdd7ee", fg: "#0d3b66" },
  DAYWORK: { bg: "#ffe699", fg: "#7a4f00" },
  OFF: { bg: "#f2f4f7", fg: "#9aa3af" },
  PTO: { bg: "#e7dbf6", fg: "#5b2a86" },
  SICK: { bg: "#f6cccc", fg: "#8a1c1c" },
};
function mondayOf(dateStr) {
  const d = new Date(dateStr + "T00:00:00");
  if (isNaN(d)) return new Date();
  const dow = (d.getDay() + 6) % 7; // Mon=0
  d.setDate(d.getDate() - dow);
  return d;
}
const fmtDM = d => `${String(d.getDate()).padStart(2, "0")} ${["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"][d.getMonth()]}`;
function cellText(cfg, code) {
  if (code === "DAY") return cfg.dayTime;
  if (code === "NIGHT") return cfg.nightTime;
  if (code === "DAYWORK") return cfg.dayworkTime;
  if (code === "PTO") return "PTO";
  if (code === "SICK") return "SICK";
  return "—";
}
function download(filename, blob) {
  const url = URL.createObjectURL(blob);
  const a = document.createElement("a");
  a.href = url; a.download = filename;
  document.body.appendChild(a); a.click(); a.remove();
  setTimeout(() => URL.revokeObjectURL(url), 1500);
}

/* ============================================================================
   Small UI atoms
============================================================================ */
function Section({ icon: Icon, title, children, help }) {
  return (
    <div className="mb-4">
      <div className="flex items-center gap-2 mb-2 text-[#1f3864]">
        <Icon size={15} strokeWidth={2.4} />
        <h3 className="text-[12px] font-bold uppercase tracking-wide">{title}</h3>
        {help && <InfoDot text={help} />}
      </div>
      <div className="rounded-xl bg-white border border-slate-200 p-3 shadow-sm">{children}</div>
    </div>
  );
}
function InfoDot({ text }) {
  return (
    <span title={text} className="inline-flex items-center text-slate-400 hover:text-slate-600 cursor-help align-middle ml-1">
      <HelpCircle size={13} />
    </span>
  );
}
function NumField({ label, value, onChange, min, max, w = "w-16", help }) {
  return (
    <label className="flex items-center justify-between gap-2 text-[13px] text-slate-700 py-1">
      <span>{label}{help && <InfoDot text={help} />}</span>
      <input type="number" value={value} min={min} max={max}
        onChange={e => onChange(Math.max(min ?? -Infinity, Math.min(max ?? Infinity, Number(e.target.value))))}
        className={`${w} rounded-md border border-slate-300 px-2 py-1 text-right tabular-nums focus:outline-none focus:ring-2 focus:ring-[#1f3864]/30`} />
    </label>
  );
}

/* ============================================================================
   Main component
============================================================================ */
export default function DutyOfficerScheduler() {
  const [officers, setOfficers] = useState(["Tabor", "Andy", "Winston", "Abdullah"]);
  const [weeks, setWeeks] = useState(4);
  const [startDate, setStartDate] = useState(() => {
    const m = mondayOf(new Date().toISOString().slice(0, 10));
    m.setDate(m.getDate() + 7);
    return m.toISOString().slice(0, 10);
  });
  const [dayworkPerWeek, setDayworkPerWeek] = useState(0);
  // Time off (PTO / sick) entered before generating: {o, startISO, endISO, type:'PTO'|'SICK'}
  const [timeOff, setTimeOff] = useState([]);
  const [toOfficer, setToOfficer] = useState(0); const [toType, setToType] = useState("PTO");
  const [toStart, setToStart] = useState(""); const [toEnd, setToEnd] = useState("");
  // Continuity: seed from a previously saved roster
  const [carry, setCarry] = useState(null); // {history, carry, fromISO} or null
  // Post-generation editing
  const [editGrid, setEditGrid] = useState(null);
  const [manualMarks, setManualMarks] = useState({}); // "o_t" -> 'PTO'|'SICK'
  const [editing, setEditing] = useState(null);       // {o,t} cell being edited
  const [repairNote, setRepairNote] = useState("");

  const [dayLabel, setDayLabel] = useState("DAY"); const [dayTime, setDayTime] = useState("1000-2200"); const [dayHours, setDayHours] = useState(12);
  const [nightLabel, setNightLabel] = useState("NIGHT"); const [nightTime, setNightTime] = useState("2200-1000"); const [nightHours, setNightHours] = useState(12);
  const [dwLabel, setDwLabel] = useState("DAY WORK"); const [dwTime, setDwTime] = useState("0800-1700"); const [dwHours, setDwHours] = useState(8);

  const [mincDay, setMincDay] = useState(2); const [maxcDay, setMaxcDay] = useState(3);
  const [mincNight, setMincNight] = useState(2); const [maxcNight, setMaxcNight] = useState(3);
  const [rest, setRest] = useState(1);
  const [minBlk, setMinBlk] = useState(2); const [maxBlk, setMaxBlk] = useState(3);
  const [swdn, setSwdn] = useState(2); const [swwh, setSwwh] = useState(1); const [enforceMin, setEnforceMin] = useState(true);

  const [wHours, setWHours] = useState(100), [wDnSelf, setWDnSelf] = useState(40),
    [wDnSpread, setWDnSpread] = useState(20), [wWknd, setWWknd] = useState(30);
  const [showAdvanced, setShowAdvanced] = useState(false);

  const [result, setResult] = useState(null);
  const [status, setStatus] = useState("Set up your team, then generate a roster.");
  const [busy, setBusy] = useState(false);
  const [tab, setTab] = useState("summary");
  const fileRef = useRef(null);
  const contRef = useRef(null);

  const buildCfg = useCallback(() => {
    const m = mondayOf(startDate);
    const T = weeks * 7;
    const names = officers.map((n, i) => (n && n.trim()) || `DO ${i + 1}`);
    // map time-off date ranges to day indices for each officer
    const unavailable = names.map(() => []);
    for (const e of timeOff) {
      if (e.o < 0 || e.o >= names.length || !e.startISO) continue;
      const s0 = new Date(e.startISO + "T00:00:00"), e0 = new Date((e.endISO || e.startISO) + "T00:00:00");
      for (let d = new Date(s0); d <= e0; d.setDate(d.getDate() + 1)) {
        const t = Math.round((d - m) / 86400000);
        if (t >= 0 && t < T) unavailable[e.o].push(t);
      }
    }
    const cfg = {
      officers: names,
      weeks, startDow: 0, mondayISO: m.toISOString().slice(0, 10),
      dayLabel, dayTime, dayHours, nightLabel, nightTime, nightHours,
      dayworkLabel: dwLabel, dayworkTime: dwTime, dayworkHours: dwHours,
      dayworkPerWeek,
      minConsecutiveDay: enforceMin ? mincDay : 1, maxConsecutiveDay: maxcDay,
      minConsecutiveNight: enforceMin ? mincNight : 1, maxConsecutiveNight: maxcNight,
      minConsecutive: enforceMin ? Math.min(mincDay, mincNight) : 1, maxConsecutive: Math.max(maxcDay, maxcNight),
      minBlocksPerType: Math.min(minBlk, maxBlk), maxBlocksPerType: Math.max(minBlk, maxBlk),
      restDaysAfterBlock: rest,
      switchDaynightOffDays: swdn, switchWorkhoursOffDays: swwh,
      wHours, wDaynightSelf: wDnSelf, wDaynightSpread: wDnSpread, wWeekend: wWknd,
      unavailable: unavailable.some(a => a.length) ? unavailable : null,
    };
    if (carry && carry.history && carry.history.length === names.length) {
      cfg.history = carry.history; cfg.carry = carry.carry;
    }
    return cfg;
  }, [officers, weeks, startDate, dayLabel, dayTime, dayHours, nightLabel, nightTime, nightHours,
    dwLabel, dwTime, dwHours, dayworkPerWeek, mincDay, maxcDay, mincNight, maxcNight, rest, minBlk, maxBlk, swdn, swwh, enforceMin,
    wHours, wDnSelf, wDnSpread, wWknd, timeOff, carry]);

  const cfg = useMemo(() => buildCfg(), [buildCfg]);
  const monday = useMemo(() => mondayOf(startDate), [startDate]);
  const T = weeks * 7;

  const run = useCallback(() => {
    setBusy(true);
    setStatus("Generating…");
    setRepairNote("");
    setTimeout(() => {
      const c = buildCfg();
      const res = generateSchedule(c, (Math.random() * 2 ** 31) >>> 0, { timeLimitMs: 1200 });
      if (!res.ok) { setResult(null); setEditGrid(null); setStatus(res.message); setBusy(false); return; }
      const probs = validate(c, res.grid);
      setResult({ ...res, cfg: c });
      setEditGrid(res.grid.map(r => r.slice()));
      // seed PTO/SICK overlay marks from the entered time-off
      const mk = {}, mon = mondayOf(c.mondayISO);
      for (const e of timeOff) {
        if (e.o < 0 || e.o >= c.officers.length || !e.startISO) continue;
        const s0 = new Date(e.startISO + "T00:00:00"), e0 = new Date((e.endISO || e.startISO) + "T00:00:00");
        for (let d = new Date(s0); d <= e0; d.setDate(d.getDate() + 1)) {
          const t = Math.round((d - mon) / 86400000);
          if (t >= 0 && t < c.weeks * 7) mk[`${e.o}_${t}`] = e.type;
        }
      }
      setManualMarks(mk);
      setEditing(null);
      setStatus(probs.length ? `Roster ready — ${probs.length} item(s) to review.` : "Roster ready. All rules satisfied.");
      setBusy(false);
    }, 25);
  }, [buildCfg, timeOff]);

  const setOfficerCount = (n) => {
    setOfficers(prev => {
      const out = prev.slice(0, n);
      while (out.length < n) out.push(`DO ${out.length + 1}`);
      return out;
    });
  };

  /* ---- derived from the (editable) roster ---- */
  const grid = editGrid;
  const m = useMemo(() => (grid ? metrics(result.cfg, grid) : null), [grid, result]);
  const liveProblems = useMemo(() => (grid ? validate(result.cfg, grid) : []), [grid, result]);
  const markAt = (o, t) => manualMarks[`${o}_${t}`];
  const dispCode = (o, t) => markAt(o, t) || grid[o][t];

  // edit a single cell; PTO/SICK on a watch triggers an auto-repair of that slot
  const applyEdit = (o, t, value) => {
    setEditing(null);
    setRepairNote("");
    if (value === "PTO" || value === "SICK") {
      const wasWatch = grid[o][t] === "DAY" || grid[o][t] === "NIGHT";
      const res = repair(result.cfg, grid, [{ o, t }]);
      setEditGrid(res.grid);
      setManualMarks(prev => ({ ...prev, [`${o}_${t}`]: value }));
      const head = `${result.cfg.officers[o]} marked ${value} on ${fmtDM(addDays(monday, t))}. `;
      const tail = res.unresolved.length ? ` ${res.unresolved.length} slot(s) still uncovered — see items to review.` : "";
      let body;
      if (!wasWatch) body = "No watch to re-cover.";
      else if (res.method === "daywork") body = (res.notes[0] || "Covered by a day-work officer.") + " (Pulling a day-work officer onto a watch bends the 8h↔12h rest gap for that day — review below.)";
      else if (res.method === "regenerated") body = res.notes[0] || "Roster re-generated from that day on.";
      else if (res.method === "patched") body = res.notes.join(" ");
      else body = "";
      setRepairNote(head + body + tail);
    } else {
      const code = { OFF: "OFF", DAY: "DAY", NIGHT: "NIGHT", DAYWORK: "DAYWORK" }[value];
      setEditGrid(prev => prev.map((r, oo) => oo === o ? r.map((c, tt) => tt === t ? code : c) : r));
      setManualMarks(prev => { const n = { ...prev }; delete n[`${o}_${t}`]; return n; });
    }
  };

  // build continuity carry-over from a saved session's grid + settings
  const buildCarryFrom = (s, gridStr) => {
    if (!gridStr || !s.weeks) return null;
    const names = (s.officers || []).map((n, i) => (n && n.trim()) || `DO ${i + 1}`);
    const W = s.weeks, lastStart = (W - 1) * 7;
    const history = gridStr.map(row => row.slice(lastStart).map(x => ({ OFF: 0, DAY: 1, NIGHT: 2, DAYWORK: 3, PTO: 0, SICK: 0 }[x] ?? 0)));
    const ccfg = { officers: names, weeks: W, startDow: 0, dayHours: s.dayHours ?? 12, nightHours: s.nightHours ?? 12, dayworkHours: s.dwHours ?? 8 };
    const full = metrics(ccfg, gridStr), lastM = metrics({ ...ccfg, weeks: 1 }, gridStr.map(r => r.slice(lastStart)));
    const cy = { hours: [], day: [], night: [], weekend: [] };
    for (let o = 0; o < names.length; o++) { cy.hours[o] = full[o].hours - lastM[o].hours; cy.day[o] = full[o].day - lastM[o].day; cy.night[o] = full[o].night - lastM[o].night; cy.weekend[o] = full[o].weekend - lastM[o].weekend; }
    const mon = mondayOf(s.startDate || new Date().toISOString().slice(0, 10));
    const nextStart = new Date(mon); nextStart.setDate(nextStart.getDate() + W * 7);
    return { history, carry: cy, fromISO: s.startDate, nextStartISO: nextStart.toISOString().slice(0, 10), officers: names };
  };

  /* ---- exports ---- */
  const exportCSV = () => {
    if (!grid) return;
    const c = result.cfg;
    const rows = [];
    rows.push(["DUTY OFFICER SCHEDULE", `Start ${cfg.mondayISO}`, `${weeks} weeks`]);
    rows.push([]);
    rows.push(["Officer", ...Array.from({ length: T }, (_, t) => fmtDM(addDays(monday, t)))]);
    rows.push(["", ...Array.from({ length: T }, (_, t) => WD[(t) % 7])]);
    c.officers.forEach((name, o) => rows.push([name, ...grid[o].map((code, t) => { const d = dispCode(o, t); return d === "OFF" ? "OFF" : cellText(c, d); })]));
    rows.push([]);
    rows.push(["Summary", "Total hours", "Day", "Night", "Day-work", "Weekend"]);
    c.officers.forEach((name, o) => rows.push([name, m[o].hours, m[o].day, m[o].night, m[o].daywork, m[o].weekend]));
    rows.push([]);
    rows.push(["SCHEDULING RULES"]);
    rulesText(c).forEach((r, i) => rows.push([`${i + 1}. ${r}`]));
    const csv = rows.map(r => r.map(v => {
      const s = String(v ?? "");
      return /[",\n]/.test(s) ? `"${s.replace(/"/g, '""')}"` : s;
    }).join(",")).join("\n");
    download("DO_Schedule.csv", new Blob([csv], { type: "text/csv;charset=utf-8" }));
  };

  const exportXLSX = () => {
    if (!grid) return;
    const c = result.cfg;
    const esc = s => String(s ?? "").replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;");
    const dateCells = Array.from({ length: T }, (_, t) => {
      const wknd = (t % 7) >= 5;
      return `<th style="background:${wknd ? "#8a5a44" : "#1f3864"};color:#fff;border:1px solid #ffffff;padding:4px 6px;font-size:11px;white-space:nowrap">${fmtDM(addDays(monday, t))}</th>`;
    }).join("");
    const wdCells = Array.from({ length: T }, (_, t) => {
      const wknd = (t % 7) >= 5;
      return `<th style="background:${wknd ? "#8a5a44" : "#1f3864"};color:#e8edf5;border:1px solid #fff;padding:2px 6px;font-size:10px">${WD[t % 7]}</th>`;
    }).join("");
    const bodyRows = c.officers.map((name, o) => {
      const cells = grid[o].map((code0, t) => {
        const code = dispCode(o, t);
        const st = SHIFT_STYLE[code] || SHIFT_STYLE.OFF;
        const txt = code === "OFF" ? "OFF" : cellText(c, code);
        return `<td style="background:${st.bg};color:${st.fg};border:1px solid #fff;padding:4px 6px;text-align:center;font-size:11px;white-space:nowrap">${esc(txt)}</td>`;
      }).join("");
      return `<tr><th style="background:#f1f5f9;border:1px solid #cbd5e1;padding:4px 8px;text-align:left;font-size:12px;white-space:nowrap">${esc(name)}</th>${cells}</tr>`;
    }).join("");
    const sumRows = c.officers.map((name, o) =>
      `<tr><td style="border:1px solid #cbd5e1;padding:3px 8px;font-weight:bold">${esc(name)}</td>` +
      `<td style="border:1px solid #cbd5e1;padding:3px 8px;text-align:center">${m[o].hours}</td>` +
      `<td style="border:1px solid #cbd5e1;padding:3px 8px;text-align:center">${m[o].day}</td>` +
      `<td style="border:1px solid #cbd5e1;padding:3px 8px;text-align:center">${m[o].night}</td>` +
      `<td style="border:1px solid #cbd5e1;padding:3px 8px;text-align:center">${m[o].daywork}</td>` +
      `<td style="border:1px solid #cbd5e1;padding:3px 8px;text-align:center">${m[o].weekend}</td></tr>`).join("");
    const legend = [["DAY", c.dayLabel], ["NIGHT", c.nightLabel], ["DAYWORK", c.dayworkLabel], ["PTO", "PTO"], ["SICK", "Sick"], ["OFF", "Off"]]
      .map(([k, lab]) => `<span style="display:inline-block;background:${SHIFT_STYLE[k].bg};color:${SHIFT_STYLE[k].fg};border:1px solid #fff;padding:2px 8px;margin-right:6px;font-size:11px">${esc(lab)}</span>`).join("");
    const ruleRows = rulesText(c).map((r, i) => `<tr><td style="border:1px solid #e2e8f0;padding:4px 8px;font-size:12px">${i + 1}. ${esc(r)}</td></tr>`).join("");

    const html =
      `<html xmlns:o="urn:schemas-microsoft-com:office:office" xmlns:x="urn:schemas-microsoft-com:office:excel" xmlns="http://www.w3.org/TR/REC-html40">` +
      `<head><meta charset="utf-8"><!--[if gte mso 9]><xml><x:ExcelWorkbook><x:ExcelWorksheets>` +
      `<x:ExcelWorksheet><x:Name>DO Schedule</x:Name><x:WorksheetOptions><x:FreezePanes/><x:FrozenNoSplit/>` +
      `<x:SplitHorizontal>2</x:SplitHorizontal><x:TopRowBottomPane>2</x:TopRowBottomPane>` +
      `<x:SplitVertical>1</x:SplitVertical><x:LeftColumnRightPane>1</x:LeftColumnRightPane>` +
      `<x:ActivePane>2</x:ActivePane></x:WorksheetOptions></x:ExcelWorksheet>` +
      `</x:ExcelWorksheets></x:ExcelWorkbook></xml><![endif]--></head><body>` +
      `<div style="font-family:Calibri,Arial,sans-serif;font-size:18px;font-weight:bold;color:#1f3864">Duty Officer Schedule</div>` +
      `<div style="font-family:Calibri,Arial;font-size:11px;color:#475569;margin-bottom:6px">Start ${esc(c.mondayISO)} &nbsp;•&nbsp; ${weeks} weeks${carry ? " &nbsp;•&nbsp; continued from previous period" : ""}</div>` +
      `<div style="margin-bottom:8px">${legend}</div>` +
      `<table style="border-collapse:collapse"><thead><tr><th style="background:#1f3864;color:#fff;border:1px solid #fff;padding:4px 8px;text-align:left;font-size:12px">Officer</th>${dateCells}</tr>` +
      `<tr><th style="background:#1f3864;border:1px solid #fff"></th>${wdCells}</tr></thead><tbody>${bodyRows}</tbody></table>` +
      `<br/><div style="font-family:Calibri,Arial;font-size:14px;font-weight:bold;color:#1f3864">Per-officer summary</div>` +
      `<table style="border-collapse:collapse;font-family:Calibri,Arial;font-size:12px"><thead><tr>` +
      ["Officer", "Total hours", "Day", "Night", "Day-work", "Weekend"].map(h => `<th style="background:#e2e8f0;border:1px solid #cbd5e1;padding:3px 8px">${h}</th>`).join("") +
      `</tr></thead><tbody>${sumRows}</tbody></table>` +
      `<br/><div style="font-family:Calibri,Arial;font-size:14px;font-weight:bold;color:#1f3864">Scheduling rules</div>` +
      `<table style="border-collapse:collapse;font-family:Calibri,Arial">${ruleRows}</table>` +
      `</body></html>`;
    download("DO_Schedule.xls", new Blob([html], { type: "application/vnd.ms-excel" }));
  };

  const saveSession = () => {
    const gridOut = grid ? grid.map((row, o) => row.map((c, t) => markAt(o, t) || c)) : null;
    const data = { version: 2, settings: serialize(), grid: gridOut };
    download("DO_Schedule_Session.json", new Blob([JSON.stringify(data, null, 2)], { type: "application/json" }));
  };
  const serialize = () => ({
    officers, weeks, startDate, dayworkPerWeek, timeOff,
    dayLabel, dayTime, dayHours, nightLabel, nightTime, nightHours, dwLabel, dwTime, dwHours,
    mincDay, maxcDay, mincNight, maxcNight, rest, minBlk, maxBlk, swdn, swwh, enforceMin, wHours, wDnSelf, wDnSpread, wWknd,
  });
  const loadSession = (file) => {
    const reader = new FileReader();
    reader.onload = () => {
      try {
        const data = JSON.parse(reader.result);
        const s = data.settings || {};
        if (s.officers) setOfficers(s.officers);
        if (s.weeks) setWeeks(s.weeks);
        if (s.startDate) setStartDate(s.startDate);
        if (s.dayworkPerWeek != null) setDayworkPerWeek(s.dayworkPerWeek);
        if (Array.isArray(s.timeOff)) setTimeOff(s.timeOff);
        s.dayLabel != null && setDayLabel(s.dayLabel); s.dayTime != null && setDayTime(s.dayTime); s.dayHours != null && setDayHours(s.dayHours);
        s.nightLabel != null && setNightLabel(s.nightLabel); s.nightTime != null && setNightTime(s.nightTime); s.nightHours != null && setNightHours(s.nightHours);
        s.dwLabel != null && setDwLabel(s.dwLabel); s.dwTime != null && setDwTime(s.dwTime); s.dwHours != null && setDwHours(s.dwHours);
        if (s.mincDay != null) setMincDay(s.mincDay); else if (s.minc != null) setMincDay(s.minc);
        if (s.maxcDay != null) setMaxcDay(s.maxcDay); else if (s.maxc != null) setMaxcDay(s.maxc);
        if (s.mincNight != null) setMincNight(s.mincNight); else if (s.minc != null) setMincNight(s.minc);
        if (s.maxcNight != null) setMaxcNight(s.maxcNight); else if (s.maxc != null) setMaxcNight(s.maxc);
        s.rest != null && setRest(s.rest);
        s.minBlk != null && setMinBlk(s.minBlk); s.maxBlk != null && setMaxBlk(s.maxBlk);
        s.swdn != null && setSwdn(s.swdn); s.swwh != null && setSwwh(s.swwh); s.enforceMin != null && setEnforceMin(s.enforceMin);
        s.wHours != null && setWHours(s.wHours); s.wDnSelf != null && setWDnSelf(s.wDnSelf); s.wDnSpread != null && setWDnSpread(s.wDnSpread);
        s.wWknd != null && setWWknd(s.wWknd);
        if (data.grid) {
          const c = { ...buildCfgFrom(s) };
          const watch = data.grid.map(row => row.map(x => (x === "PTO" || x === "SICK") ? "OFF" : x));
          const mk = {};
          data.grid.forEach((row, o) => row.forEach((x, t) => { if (x === "PTO" || x === "SICK") mk[`${o}_${t}`] = x; }));
          setResult({ ok: true, grid: watch, cfg: c, score: 0 });
          setEditGrid(watch.map(r => r.slice())); setManualMarks(mk); setEditing(null);
          setStatus("Loaded saved roster.");
        } else {
          setResult(null); setEditGrid(null); setStatus("Loaded settings (no saved roster).");
        }
      } catch (e) { setStatus("Could not read that file — is it a saved session?"); }
    };
    reader.readAsText(file);
  };
  const buildCfgFrom = (s) => {
    const m2 = mondayOf(s.startDate || startDate);
    return {
      officers: (s.officers || officers).map((n, i) => (n && n.trim()) || `DO ${i + 1}`),
      weeks: s.weeks || weeks, startDow: 0, mondayISO: m2.toISOString().slice(0, 10),
      dayLabel: s.dayLabel ?? dayLabel, dayTime: s.dayTime ?? dayTime, dayHours: s.dayHours ?? dayHours,
      nightLabel: s.nightLabel ?? nightLabel, nightTime: s.nightTime ?? nightTime, nightHours: s.nightHours ?? nightHours,
      dayworkLabel: s.dwLabel ?? dwLabel, dayworkTime: s.dwTime ?? dwTime, dayworkHours: s.dwHours ?? dwHours,
      dayworkPerWeek: s.dayworkPerWeek ?? dayworkPerWeek,
      minConsecutiveDay: (s.enforceMin ?? enforceMin) ? (s.mincDay ?? s.minc ?? mincDay) : 1,
      maxConsecutiveDay: s.maxcDay ?? s.maxc ?? maxcDay,
      minConsecutiveNight: (s.enforceMin ?? enforceMin) ? (s.mincNight ?? s.minc ?? mincNight) : 1,
      maxConsecutiveNight: s.maxcNight ?? s.maxc ?? maxcNight,
      minConsecutive: (s.enforceMin ?? enforceMin) ? Math.min(s.mincDay ?? s.minc ?? mincDay, s.mincNight ?? s.minc ?? mincNight) : 1,
      maxConsecutive: Math.max(s.maxcDay ?? s.maxc ?? maxcDay, s.maxcNight ?? s.maxc ?? maxcNight),
      minBlocksPerType: Math.min(s.minBlk ?? minBlk, s.maxBlk ?? maxBlk), maxBlocksPerType: Math.max(s.minBlk ?? minBlk, s.maxBlk ?? maxBlk),
      restDaysAfterBlock: s.rest ?? rest, switchDaynightOffDays: s.swdn ?? swdn, switchWorkhoursOffDays: s.swwh ?? swwh,
      wHours: s.wHours ?? wHours, wDaynightSelf: s.wDnSelf ?? wDnSelf, wDaynightSpread: s.wDnSpread ?? wDnSpread,
      wWeekend: s.wWknd ?? wWknd,
    };
  };
  // Load a previous session purely to seed continuity for the NEXT period
  const continueFrom = (file) => {
    const reader = new FileReader();
    reader.onload = () => {
      try {
        const data = JSON.parse(reader.result);
        const s = data.settings || {};
        const cy = buildCarryFrom(s, data.grid);
        if (!cy) { setStatus("That session has no saved roster to continue from."); return; }
        setCarry(cy);
        if (s.officers) setOfficers(s.officers);
        if (cy.nextStartISO) setStartDate(cy.nextStartISO);
        setStatus(`Continuity set — the next roster will follow on from ${cy.fromISO || "the previous period"}.`);
      } catch (e) { setStatus("Could not read that file — is it a saved session?"); }
    };
    reader.readAsText(file);
  };

  const spreadOf = (key) => m ? (Math.max(...m.map(x => x[key])) - Math.min(...m.map(x => x[key]))) : 0;

  /* ============================ render ============================ */
  return (
    <div className="min-h-screen w-full bg-[#eef1f6] text-slate-800"
      style={{ backgroundColor: "#eef1f6", fontFamily: "ui-sans-serif, system-ui, 'Segoe UI', Roboto, sans-serif" }}>
      <style>{`
        [class~="bg-[#1f3864]"]{background-color:#1f3864}
        [class~="bg-[#eef1f6]"]{background-color:#eef1f6}
        [class~="text-[#1f3864]"]{color:#1f3864}
        [class~="border-[#1f3864]"]{border-color:#1f3864}
        [class~="text-[20px]"]{font-size:20px;line-height:1.2}
        [class~="text-[14px]"]{font-size:14px}
        [class~="text-[13px]"]{font-size:13px}
        [class~="text-[12px]"]{font-size:12px}
        [class~="text-[11px]"]{font-size:11px}
        [class~="max-w-[1400px]"]{max-width:1400px}
        [class~="max-h-[52vh]"]{max-height:52vh}
        [class~="top-[26px]"]{top:26px}
        [class~="accent-[#1f3864]"]{accent-color:#1f3864}
        [class~="hover:bg-[#16294a]"]:hover{background-color:#16294a}
        [class~="focus:ring-[#1f3864]/30"]:focus{outline:none;box-shadow:0 0 0 2px rgba(31,56,100,.3)}
        @media (min-width:1024px){
          [class~="lg:bg-[#eef1f6]"]{background-color:#eef1f6}
          [class~="lg:grid-cols-[360px_1fr]"]{grid-template-columns:360px minmax(0,1fr)}
          [class~="lg:max-h-[calc(100vh-110px)]"]{max-height:calc(100vh - 110px)}
        }
      `}</style>
      {/* Header */}
      <header className="bg-[#1f3864] text-white">
        <div className="max-w-[1400px] mx-auto px-5 py-4 flex items-center justify-between gap-4 flex-wrap">
          <div>
            <h1 className="text-[20px] font-bold tracking-tight">Duty Officer Schedule Planner</h1>
            <p className="text-[12px] text-white/70">Build a fair, rule-checked watch roster in seconds.</p>
          </div>
          <div className="flex items-center gap-2 text-[13px] bg-white/10 rounded-lg px-3 py-2">
            {busy ? <RefreshCw size={15} className="animate-spin" /> : <ListChecks size={15} />}
            <span>{status}</span>
          </div>
        </div>
      </header>

      <div className="max-w-[1400px] mx-auto px-5 py-5 grid grid-cols-1 lg:grid-cols-[360px_1fr] gap-5">
        {/* ---------------- Settings ---------------- */}
        <aside className="lg:max-h-[calc(100vh-110px)] lg:overflow-y-auto lg:pr-1">
          <Section icon={Users} title="Duty officers" help="The duty officers to roster. This tour model needs at least 2 day-watch and 2 night-watch officers each week, so a minimum of 4 (plus 1 more for every officer you put on day-work).">
            <NumField label="Number of officers" value={officers.length} min={2} max={8} onChange={setOfficerCount}
              help="How many DOs are in the rotation. For the evenest hours, use an even number of watch officers (4 or 6); an odd watch pool makes one group busier." />
            <div className="mt-2 space-y-1.5">
              {officers.map((name, i) => (
                <div key={i} className="flex items-center gap-2">
                  <span className="text-[12px] text-slate-400 w-5 text-right">{i + 1}.</span>
                  <input value={name} onChange={e => setOfficers(prev => prev.map((p, j) => j === i ? e.target.value : p))}
                    title="Officer name as it appears in the roster and exports."
                    className="flex-1 rounded-md border border-slate-300 px-2 py-1 text-[13px] focus:outline-none focus:ring-2 focus:ring-[#1f3864]/30" />
                </div>
              ))}
            </div>
          </Section>

          <Section icon={Calendar} title="Period" help="The stretch of time this roster covers. The schedule always starts on a Monday and runs in whole weeks.">
            <NumField label="Weeks" value={weeks} min={1} max={26} onChange={setWeeks}
              help="Length of the roster in weeks. With a 4-week roster each officer holds one shift type the whole period; the rotation to a new type lands in the next period (5+ weeks can rotate within the roster)." />
            <label className="flex items-center justify-between gap-2 text-[13px] text-slate-700 py-1 mt-1">
              <span>Start (snaps to Monday)<InfoDot text="Pick any date; it is rounded back to that week's Monday so weeks and weekend pairing line up." /></span>
              <input type="date" value={startDate} onChange={e => setStartDate(e.target.value)}
                className="rounded-md border border-slate-300 px-2 py-1 text-[13px] focus:outline-none focus:ring-2 focus:ring-[#1f3864]/30" />
            </label>
            <p className="text-[11px] text-slate-400 mt-1">Week of {fmtDM(monday)} → {fmtDM(addDays(monday, T - 1))}</p>
          </Section>

          <Section icon={Clock} title="8h day-work (Mon–Fri, rotated)" help="Optional 8-hour weekday role. The day-work officer stands no watches that week; it rotates week to week among the team.">
            <NumField label="Officers per week" value={dayworkPerWeek} min={0} max={2} onChange={setDayworkPerWeek}
              help="How many DOs are on the 8h day-work role each week." />
          </Section>

          <Section icon={CalendarOff} title="Time off (PTO / sick)" help="Mark dates an officer is unavailable before generating. The roster is built around them; PTO and sick days never get a watch. You can also mark a sick day after generating from the roster grid.">
            <div className="grid grid-cols-2 gap-1.5">
              <label className="text-[11px] text-slate-500 col-span-2">Officer
                <select value={toOfficer} onChange={e => setToOfficer(Number(e.target.value))}
                  className="mt-0.5 w-full rounded-md border border-slate-300 px-2 py-1 text-[13px]">
                  {officers.map((n, i) => <option key={i} value={i}>{n || `DO ${i + 1}`}</option>)}
                </select>
              </label>
              <label className="text-[11px] text-slate-500">From
                <input type="date" value={toStart} onChange={e => setToStart(e.target.value)}
                  className="mt-0.5 w-full rounded-md border border-slate-300 px-1.5 py-1 text-[12px]" />
              </label>
              <label className="text-[11px] text-slate-500">To
                <input type="date" value={toEnd} onChange={e => setToEnd(e.target.value)}
                  className="mt-0.5 w-full rounded-md border border-slate-300 px-1.5 py-1 text-[12px]" />
              </label>
              <label className="text-[11px] text-slate-500">Type
                <select value={toType} onChange={e => setToType(e.target.value)}
                  className="mt-0.5 w-full rounded-md border border-slate-300 px-2 py-1 text-[13px]">
                  <option value="PTO">PTO</option><option value="SICK">Sick</option>
                </select>
              </label>
              <button
                onClick={() => { if (!toStart) return; setTimeOff(prev => [...prev, { o: toOfficer, startISO: toStart, endISO: toEnd || toStart, type: toType }]); setToStart(""); setToEnd(""); }}
                className="self-end rounded-md bg-[#1f3864] text-white text-[13px] font-medium py-1.5 hover:bg-[#16294a]">Add</button>
            </div>
            {timeOff.length > 0 && (
              <div className="mt-2 space-y-1">
                {timeOff.map((e, i) => (
                  <div key={i} className="flex items-center justify-between gap-2 text-[12px] rounded-md px-2 py-1"
                    style={{ background: SHIFT_STYLE[e.type].bg, color: SHIFT_STYLE[e.type].fg }}>
                    <span>{(officers[e.o] || `DO ${e.o + 1}`)} · {e.type} · {fmtDM(new Date(e.startISO + "T00:00:00"))}{e.endISO && e.endISO !== e.startISO ? `–${fmtDM(new Date(e.endISO + "T00:00:00"))}` : ""}</span>
                    <button onClick={() => setTimeOff(prev => prev.filter((_, j) => j !== i))} className="font-bold opacity-70 hover:opacity-100">×</button>
                  </div>
                ))}
              </div>
            )}
          </Section>

          <Section icon={Repeat} title="Continuity" help="Carry the rest, block, and day↔night gap rules across into a new period, and keep hours/weekends balanced over the long run. Load the previous period's saved session and the next roster will follow on from where it ended.">
            {carry ? (
              <div className="flex items-center justify-between gap-2 text-[12px] rounded-md px-2 py-1.5 bg-indigo-50 border border-indigo-200 text-indigo-800">
                <span>Continuing on from {carry.fromISO || "previous period"}. Start set to {carry.nextStartISO}.</span>
                <button onClick={() => setCarry(null)} className="font-bold opacity-70 hover:opacity-100">×</button>
              </div>
            ) : (
              <button onClick={() => contRef.current?.click()}
                className="w-full inline-flex items-center justify-center gap-1.5 rounded-md border border-slate-300 bg-white py-1.5 text-[13px] font-medium hover:bg-slate-50">
                <FolderOpen size={15} /> Continue from previous period…
              </button>
            )}
            <input ref={contRef} type="file" accept="application/json,.json" className="hidden"
              onChange={e => { const f = e.target.files?.[0]; if (f) continueFrom(f); e.target.value = ""; }} />
          </Section>

          <Section icon={Sliders} title="Shift definitions" help="The label, clock time, and length of each shift. These appear in the roster cells and exports.">
            {[
              ["Day", dayLabel, setDayLabel, dayTime, setDayTime, dayHours, setDayHours],
              ["Night", nightLabel, setNightLabel, nightTime, setNightTime, nightHours, setNightHours],
              ["Day-work", dwLabel, setDwLabel, dwTime, setDwTime, dwHours, setDwHours],
            ].map(([k, lab, sLab, tm, sTm, hr, sHr]) => (
              <div key={k} className="flex items-center gap-1.5 py-1">
                <input value={lab} onChange={e => sLab(e.target.value)} title={`${k} shift label`} className="w-20 rounded-md border border-slate-300 px-2 py-1 text-[12px]" />
                <input value={tm} onChange={e => sTm(e.target.value)} title={`${k} shift clock time, e.g. 1000-2200`} className="flex-1 rounded-md border border-slate-300 px-2 py-1 text-[12px]" />
                <input type="number" value={hr} min={1} max={24} onChange={e => sHr(Number(e.target.value))} title={`${k} shift length in hours`} className="w-14 rounded-md border border-slate-300 px-2 py-1 text-[12px] text-right" />
                <span className="text-[12px] text-slate-400">h</span>
              </div>
            ))}
          </Section>

          <Section icon={ListChecks} title="Block & rest rules" help="How watch days are grouped into blocks and the rest required around them. Day-watch and night-watch blocks can have their own lengths.">
            <p className="text-[11px] font-semibold text-slate-500 mt-0.5 mb-0.5">Day-watch blocks</p>
            <NumField label="Min consecutive day-watch days" value={mincDay} min={1} max={5} onChange={setMincDay}
              help="Shortest run of day watches in a row before a break — avoids isolated single day watches." />
            <NumField label="Max consecutive day-watch days" value={maxcDay} min={2} max={7} onChange={setMaxcDay}
              help="Longest run of day watches in a row before a mandatory break." />
            <p className="text-[11px] font-semibold text-slate-500 mt-1.5 mb-0.5">Night-watch blocks</p>
            <NumField label="Min consecutive night-watch days" value={mincNight} min={1} max={5} onChange={setMincNight}
              help="Shortest run of night watches in a row before a break — avoids isolated single night watches." />
            <NumField label="Max consecutive night-watch days" value={maxcNight} min={2} max={7} onChange={setMaxcNight}
              help="Longest run of night watches in a row before a mandatory break. Set this lower than the day maximum if you want shorter night stretches." />
            <p className="text-[11px] font-semibold text-slate-500 mt-1.5 mb-0.5">Blocks before switching day↔night</p>
            <NumField label="Min same-type blocks before switch" value={minBlk} min={1} max={5} onChange={setMinBlk}
              help="Fewest blocks (work stints) of the same shift type an officer does in a row before they're allowed to switch between day and night. Set to 1 to allow switching after every block." />
            <NumField label="Max same-type blocks before switch" value={maxBlk} min={1} max={6} onChange={setMaxBlk}
              help="Most blocks of the same shift type in a row before a switch is required. With min 2 / max 3, an officer does 2–3 day stints, then 2–3 night stints, and so on." />
            <p className="text-[11px] font-semibold text-slate-500 mt-1.5 mb-0.5">Rest & switching</p>
            <NumField label="Rest days after a block" value={rest} min={1} max={4} onChange={setRest}
              help="Minimum days off immediately after finishing a block of the same shift type." />
            <NumField label="Off days when day↔night" value={swdn} min={0} max={5} onChange={setSwdn}
              help="Minimum days off when switching between day and night watches." />
            <NumField label="Off days when 12h↔8h" value={swwh} min={0} max={5} onChange={setSwwh}
              help="Minimum days off when switching between a 12h watch and the 8h day-work shift." />
            <label className="flex items-center gap-2 text-[13px] text-slate-700 py-1 mt-1 cursor-pointer">
              <input type="checkbox" checked={enforceMin} onChange={e => setEnforceMin(e.target.checked)} className="accent-[#1f3864]" />
              Strictly enforce minimum consecutive
              <InfoDot text="On: blocks must reach the minimum length. Off: single-day blocks are allowed when needed for coverage." />
            </label>
          </Section>

          <button onClick={() => setShowAdvanced(v => !v)} className="text-[12px] text-[#1f3864] font-semibold mb-2 hover:underline">
            {showAdvanced ? "Hide" : "Show"} fairness weights
          </button>
          {showAdvanced && (
            <Section icon={Sliders} title="Fairness weights" help="How hard the generator works to balance each thing. Higher = more important. It keeps the best-balanced valid roster it finds.">
              <NumField label="Equal hours" value={wHours} min={0} max={500} w="w-20" onChange={setWHours}
                help="Priority on giving everyone similar total hours." />
              <NumField label="Own day/night balance" value={wDnSelf} min={0} max={500} w="w-20" onChange={setWDnSelf}
                help="Priority on each officer getting a similar number of day and night watches." />
              <NumField label="Day/night across team" value={wDnSpread} min={0} max={500} w="w-20" onChange={setWDnSpread}
                help="Priority on an even number of day (and night) watches across the officers." />
              <NumField label="Equal weekends" value={wWknd} min={0} max={500} w="w-20" onChange={setWWknd}
                help="Priority on sharing weekend duty evenly." />
            </Section>
          )}

          <div className="grid grid-cols-2 gap-2 mb-3 lg:sticky lg:bottom-0 lg:z-20 lg:pt-3 lg:pb-2 lg:bg-[#eef1f6] lg:border-t lg:border-slate-200">
            <button onClick={run} disabled={busy}
              className="col-span-2 inline-flex items-center justify-center gap-2 rounded-xl bg-[#1f3864] text-white font-semibold py-2.5 text-[14px] hover:bg-[#16294a] disabled:opacity-60 transition">
              <Wand2 size={16} /> {result ? "Re-generate" : "Generate roster"}
            </button>
            <button onClick={exportXLSX} disabled={!grid}
              className="inline-flex items-center justify-center gap-1.5 rounded-xl border border-slate-300 bg-white py-2 text-[13px] font-medium hover:bg-slate-50 disabled:opacity-50">
              <FileSpreadsheet size={15} /> Excel
            </button>
            <button onClick={exportCSV} disabled={!grid}
              className="inline-flex items-center justify-center gap-1.5 rounded-xl border border-slate-300 bg-white py-2 text-[13px] font-medium hover:bg-slate-50 disabled:opacity-50">
              <FileText size={15} /> CSV
            </button>
            <button onClick={saveSession}
              className="inline-flex items-center justify-center gap-1.5 rounded-xl border border-slate-300 bg-white py-2 text-[13px] font-medium hover:bg-slate-50">
              <Save size={15} /> Save
            </button>
            <button onClick={() => fileRef.current?.click()}
              className="inline-flex items-center justify-center gap-1.5 rounded-xl border border-slate-300 bg-white py-2 text-[13px] font-medium hover:bg-slate-50">
              <FolderOpen size={15} /> Load
            </button>
            <input ref={fileRef} type="file" accept="application/json,.json" className="hidden"
              onChange={e => { const f = e.target.files?.[0]; if (f) loadSession(f); e.target.value = ""; }} />
          </div>
        </aside>

        {/* ---------------- Roster + tabs ---------------- */}
        <main className="min-w-0">
          <div className="rounded-2xl bg-white border border-slate-200 shadow-sm overflow-hidden">
            <div className="px-4 py-3 border-b border-slate-100 flex items-center gap-3 flex-wrap">
              <h2 className="text-[13px] font-bold uppercase tracking-wide text-[#1f3864]">Roster</h2>
              <div className="flex items-center gap-3 text-[11px] text-slate-500 flex-wrap">
                {[["DAY", cfg.dayLabel], ["NIGHT", cfg.nightLabel], ["DAYWORK", cfg.dayworkLabel], ["PTO", "PTO"], ["SICK", "Sick"], ["OFF", "Off"]].map(([k, lab]) => (
                  <span key={k} className="inline-flex items-center gap-1.5">
                    <span className="inline-block w-3 h-3 rounded-sm" style={{ background: SHIFT_STYLE[k].bg }} />{lab}
                  </span>
                ))}
              </div>
              {grid && <span className="text-[11px] text-slate-400 ml-auto">Tip: click any cell to edit it or mark sick / PTO.</span>}
            </div>

            {grid ? (
              <div className="overflow-auto max-h-[52vh]">
                <table className="border-collapse text-[11px]">
                  <thead>
                    <tr>
                      <th className="sticky left-0 top-0 z-30 bg-[#1f3864] text-white px-3 py-1.5 text-left font-semibold">Officer</th>
                      {Array.from({ length: T }, (_, t) => {
                        const d = addDays(monday, t); const wknd = (t % 7) >= 5;
                        return <th key={t} className="sticky top-0 z-20 px-1.5 py-1 font-semibold text-white" style={{ background: wknd ? "#8a5a44" : "#1f3864" }}>{fmtDM(d)}</th>;
                      })}
                    </tr>
                    <tr>
                      <th className="sticky left-0 top-[26px] z-30 bg-[#1f3864]" />
                      {Array.from({ length: T }, (_, t) => {
                        const wknd = (t % 7) >= 5;
                        return <th key={t} className="sticky top-[26px] z-20 px-1.5 py-0.5 font-medium text-white/90" style={{ background: wknd ? "#8a5a44" : "#1f3864" }}>{WD[t % 7]}</th>;
                      })}
                    </tr>
                  </thead>
                  <tbody>
                    {result.cfg.officers.map((name, o) => (
                      <tr key={o}>
                        <td className="sticky left-0 z-10 bg-slate-50 border border-slate-200 px-3 py-1.5 font-semibold whitespace-nowrap">{name}</td>
                        {grid[o].map((code0, t) => {
                          const code = dispCode(o, t);
                          const st = SHIFT_STYLE[code] || SHIFT_STYLE.OFF;
                          const isEditing = editing && editing.o === o && editing.t === t;
                          return (
                            <td key={t} className="relative border border-white/70 px-1.5 py-1.5 text-center whitespace-nowrap cursor-pointer hover:ring-2 hover:ring-[#1f3864]/40"
                              style={{ background: st.bg, color: st.fg }}
                              onClick={() => setEditing(isEditing ? null : { o, t })}>
                              {cellText(result.cfg, code)}
                              {isEditing && (
                                <div className="absolute z-40 left-1/2 -translate-x-1/2 mt-1 top-full bg-white border border-slate-300 rounded-lg shadow-lg p-1 text-left"
                                  onClick={ev => ev.stopPropagation()}>
                                  {[["DAY", cfg.dayLabel], ["NIGHT", cfg.nightLabel], ["DAYWORK", cfg.dayworkLabel], ["OFF", "Off"], ["SICK", "Sick"], ["PTO", "PTO"]].map(([v, lab]) => (
                                    <button key={v} onClick={() => applyEdit(o, t, v)}
                                      className="block w-full text-left px-3 py-1 text-[12px] rounded hover:bg-slate-100 whitespace-nowrap" style={{ color: "#334155" }}>
                                      <span className="inline-block w-2.5 h-2.5 rounded-sm mr-2 align-middle" style={{ background: SHIFT_STYLE[v].bg }} />{lab}
                                    </button>
                                  ))}
                                </div>
                              )}
                            </td>
                          );
                        })}
                      </tr>
                    ))}
                  </tbody>
                </table>
              </div>
            ) : (
              <div className="px-6 py-16 text-center text-slate-400">
                <Wand2 className="mx-auto mb-3" size={28} />
                <p className="text-[14px]">No roster yet. Set your officers and rules, then choose <span className="font-semibold text-slate-600">Generate roster</span>.</p>
              </div>
            )}
          </div>

          {grid && (repairNote || liveProblems.length > 0) && (
            <div className="mt-3 rounded-xl border px-4 py-3 text-[12px]"
              style={liveProblems.length ? { background: "#fff7ed", borderColor: "#fed7aa", color: "#9a3412" } : { background: "#ecfdf5", borderColor: "#a7f3d0", color: "#065f46" }}>
              {repairNote && <p className="mb-1 font-medium">{repairNote}</p>}
              {liveProblems.length > 0 ? (
                <>
                  <p className="font-semibold mb-1">{liveProblems.length} item(s) to review after your edits:</p>
                  <ul className="list-disc list-inside space-y-0.5">
                    {liveProblems.slice(0, 8).map((p, i) => <li key={i}>{p}</li>)}
                    {liveProblems.length > 8 && <li>…and {liveProblems.length - 8} more.</li>}
                  </ul>
                  <p className="mt-1 text-[11px] opacity-80">Emergency single-day cover can leave a short block — adjust any cell by clicking it.</p>
                </>
              ) : <p>All rules still satisfied.</p>}
            </div>
          )}

          {/* tabs */}
          <div className="mt-4 rounded-2xl bg-white border border-slate-200 shadow-sm overflow-hidden">
            <div className="flex border-b border-slate-100">
              {[["summary", "Per-officer summary"], ["rules", "Scheduling rules"]].map(([k, lab]) => (
                <button key={k} onClick={() => setTab(k)}
                  className={`px-4 py-2.5 text-[13px] font-semibold border-b-2 -mb-px ${tab === k ? "border-[#1f3864] text-[#1f3864]" : "border-transparent text-slate-400 hover:text-slate-600"}`}>
                  {lab}
                </button>
              ))}
            </div>

            {tab === "summary" ? (
              <div className="p-4">
                {grid ? (
                  <>
                    <div className="flex flex-wrap gap-2 mb-3 text-[11px]">
                      <Chip label="Hours spread" value={spreadOf("hours") + "h"} good={spreadOf("hours") <= 12} />
                      <Chip label="Day spread" value={spreadOf("day")} good={spreadOf("day") <= 2} />
                      <Chip label="Night spread" value={spreadOf("night")} good={spreadOf("night") <= 2} />
                      <Chip label="Weekend spread" value={spreadOf("weekend")} good={spreadOf("weekend") <= 2} />
                    </div>
                    <table className="w-full text-[13px]">
                      <thead>
                        <tr className="text-left text-slate-500 border-b border-slate-200">
                          <th className="py-1.5 pr-2 font-semibold">Officer</th>
                          <th className="py-1.5 px-2 text-center font-semibold">Total hrs</th>
                          <th className="py-1.5 px-2 text-center font-semibold">Day</th>
                          <th className="py-1.5 px-2 text-center font-semibold">Night</th>
                          <th className="py-1.5 px-2 text-center font-semibold">Day-work</th>
                          <th className="py-1.5 px-2 text-center font-semibold">Weekend</th>
                        </tr>
                      </thead>
                      <tbody>
                        {result.cfg.officers.map((name, o) => (
                          <tr key={o} className="border-b border-slate-100">
                            <td className="py-1.5 pr-2 font-semibold">{name}</td>
                            <td className="py-1.5 px-2 text-center tabular-nums">{m[o].hours}</td>
                            <td className="py-1.5 px-2 text-center tabular-nums">{m[o].day}</td>
                            <td className="py-1.5 px-2 text-center tabular-nums">{m[o].night}</td>
                            <td className="py-1.5 px-2 text-center tabular-nums">{m[o].daywork}</td>
                            <td className="py-1.5 px-2 text-center tabular-nums">{m[o].weekend}</td>
                          </tr>
                        ))}
                      </tbody>
                    </table>
                  </>
                ) : <p className="text-[13px] text-slate-400">Generate a roster to see the per-officer breakdown.</p>}
              </div>
            ) : (
              <ol className="p-4 space-y-2 text-[13px] text-slate-700 list-decimal list-inside">
                {rulesText(cfg).map((r, i) => <li key={i}>{r}</li>)}
              </ol>
            )}
          </div>
        </main>
      </div>
    </div>
  );
}

function addDays(d, n) { const x = new Date(d); x.setDate(x.getDate() + n); return x; }
function Chip({ label, value, good }) {
  return (
    <span className={`inline-flex items-center gap-1.5 rounded-full px-3 py-1 border ${good ? "bg-emerald-50 border-emerald-200 text-emerald-700" : "bg-amber-50 border-amber-200 text-amber-700"}`}>
      {!good && <AlertTriangle size={12} />}<span className="font-medium">{label}:</span> <span className="tabular-nums">{value}</span>
    </span>
  );
}
