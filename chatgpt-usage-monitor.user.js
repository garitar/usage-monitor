// ==UserScript==
// @name         ChatGPT usage monitor
// @namespace    https://chatgpt.com/usage-monitor
// @version      2.1.3
// @description  On the Usage page: predicts when you'll hit 0% left, alarms 24/12/6 s before (plus a % backstop), learns from every cycle, and shows what the burn is costing you.
// @match        https://chatgpt.com/*
// @run-at       document-idle
// @noframes
// @updateURL    https://raw.githubusercontent.com/garitar/usage-monitor/main/chatgpt-usage-monitor.user.js
// @downloadURL  https://raw.githubusercontent.com/garitar/usage-monitor/main/chatgpt-usage-monitor.user.js
// @grant        GM_getValue
// @grant        GM_setValue
// @grant        GM_xmlhttpRequest
// @grant        GM_openInTab
// @connect      raw.githubusercontent.com
// ==/UserScript==

(() => {
  'use strict';

  // ---- Settings ----
  const MARKS = [24, 12, 6];      // alarm this many seconds before it's predicted to hit 0% left
  const HEADS_UP_S = 90;          // one soft tick this many seconds out, so the checkout can be opened in time (0 = off)
  const BACKSTOP_PCT = 3;         // backstop buzz at this % left if the 24 s alarm hasn't fired yet...
  const BACKSTOP_S = 16;          // ...or when the fastest recent tick spacing says this many seconds remain
  const SLOW_POLL_S = 3;          // check usage every 3 s normally...
  const FAST_WHEN_S = 90;         // ...and every 1 s once it's predicted to run out within 90 s
  const AUTO_POPOUT = true;       // open the always-on-top pop-out on your first click on the Usage page
  const LEARN = true;             // after every cycle, re-pick the curve and correct each alarm's steady bias
  const KEEP_DAYS = 60;           // how long cycles are kept for learning
  const RESET_PRICE = 125;        // $ for one instant usage-limit reset (what checkout showed on Oct 25, 2026)
  const CREDIT_PRICE = 0.028;     // $ per credit you pay: 0.04 list, 0.036/0.032/0.028 for $100/$200/$1,000 packs, 0.024 with auto-reload at 25k
  const ROUTE = /^\/settings\/usage/;
  const VERSION = '2.1.3';
  const SCRIPT_URL = 'https://raw.githubusercontent.com/garitar/usage-monitor/main/chatgpt-usage-monitor.user.js';   // where the newest build lives; the monitor checks it for a newer @version

  const K = { hist: 'um2.history', cur: 'um2.current', calib: 'um2.calibration', log: 'um2.log', prefs: 'um2.prefs', last: 'um2.lastResult', recent: 'um2.history.recent', leader: 'um2.leader', day: 'um2.day', econ: 'um2.econ' };
  const OLD_LOG = '__usagelog';

  // ---- Predictor + learner (same code runs in a background worker for learning) ----
  function learnerModule() {
    // The run-out predictor (dependency-free; the same code runs in the userscript and in the tests).
    //
    // The API only reports whole percents, so what is observed is the moment each 1% ticks over.
    // Usage in the current burst is fit as u(t) = a + b·t + c·f(t), with c >= 0 so the burn can only speed up:
    //   shape 'line'   f = 0       constant rate
    //   shape 'sqrt'   f = t^1.5   rate grows like the square root of time
    //   shape 'accel'  f = t^2     rate grows linearly (constant acceleration)
    // The run-out is where that curve reaches the goal, counted from the latest tick-over. A tick that comes
    // late delays the rest of the schedule instead of lowering the rate. Pauses split the cycle into bursts:
    // a new burst starts from the speed of the last full one, and while the burn is paused, or has only just
    // come back from a pause, no alarm may fire.
    function makePredictor(cfg) {
      const C = Object.assign({
        goal: 100, shape: 'sqrt', window: 40, halfLife: 12,
        pauseFactor: 3, pauseMinMs: 15000, minBurst: 6, priorW: 4, holdTicks: 4,
        overdueResid: 0.15, capFactor: 2,
      }, cfg || {});
      let ticks = [], lastUsed = null, lastPollT = null, mem = null;   // mem: ms per 1% of the last full burst
      let cache = null;                                                // the fit only changes when a tick arrives

      const median = a => { const s = a.slice().sort((x, y) => x - y); return s.length ? s[(s.length - 1) >> 1] : null; };
      const gapAt = i => (ticks[i].t - ticks[i - 1].t) / Math.max(1, ticks[i].u - ticks[i - 1].u);
      const curveF = C.shape === 'accel' ? (t => t * t) : (t => Math.pow(Math.max(t, 0), 1.5));

      function burstStart(end) {
        let s = end;
        while (s > 0) {
          const g = gapAt(s), after = [];
          for (let i = s + 1; i <= end && after.length < 6; i++) after.push(gapAt(i));
          const ref = after.length >= 2 ? median(after) : mem;
          if (ref ? g > Math.max(C.pauseFactor * ref, C.pauseMinMs) : g > 30000) break;
          s--;
        }
        return s;
      }

      // weighted least squares: u = a + b t (+ c f(t)), t in seconds from the window start, optional slope prior
      function lsq(pts, useC, prior, priorW) {
        const uTop = pts[pts.length - 1].u, k = useC ? 3 : 2, S = [], R = [];
        for (let r = 0; r < k; r++) { S.push(new Array(k).fill(0)); R.push(0); }
        for (const p of pts) {
          const v = useC ? [1, p.t, curveF(p.t)] : [1, p.t];
          const w = isFinite(C.halfLife) ? Math.pow(0.5, (uTop - p.u) / C.halfLife) : 1;
          for (let r = 0; r < k; r++) { R[r] += w * v[r] * p.u; for (let q = 0; q < k; q++) S[r][q] += w * v[r] * v[q]; }
        }
        if (prior) { S[1][1] += priorW; R[1] += priorW * prior; }
        for (let i = 0; i < k; i++) {                                  // Gauss-Jordan
          let p = i; for (let r = i + 1; r < k; r++) if (Math.abs(S[r][i]) > Math.abs(S[p][i])) p = r;
          if (Math.abs(S[p][i]) < 1e-12) return null;
          [S[i], S[p]] = [S[p], S[i]]; [R[i], R[p]] = [R[p], R[i]];
          for (let r = 0; r < k; r++) if (r !== i) { const m = S[r][i] / S[i][i]; for (let q = i; q < k; q++) S[r][q] -= m * S[i][q]; R[r] -= m * R[i]; }
        }
        const sol = R.map((x, i) => x / S[i][i]);
        return { a: sol[0], b: sol[1], c: useC ? sol[2] : 0 };
      }

      function model() {
        const n = ticks.length;
        if (!n) return null;
        const start = burstStart(n - 1), afterPause = start > 0;
        const burst = ticks.slice(start).slice(-C.window);
        const last = ticks[n - 1], t0 = burst[0].t;
        const prior = mem ? 1000 / mem : null;                              // %/s
        const fromPrior = nb => (prior ? { a: 0, b: prior, c: 0, t0: last.t, last, n: nb, span: 0, afterPause, curved: false } : null);
        if (burst.length < 2) return fromPrior(1);
        const pts = burst.map(p => ({ t: (p.t - t0) / 1000, u: p.u - last.u }));
        let fit = null, curved = false;
        if (C.shape !== 'line' && burst.length >= 8) {                     // bend only towards a faster burn
          fit = lsq(pts, true, null, 0);
          if (fit && fit.c >= 0 && fit.b >= 0) curved = fit.c > 0; else fit = null;
        }
        if (!fit) fit = lsq(pts, false, prior, prior ? C.priorW * Math.pow(0.5, (burst.length - 1) / 3) : 0);
        const span = pts[pts.length - 1].t;
        const endRate = fit ? fit.b + (fit.c ? fit.c * (curveF(span + 0.01) - curveF(span)) / 0.01 : 0) : 0;
        if (!fit || !(endRate > 0)) return fromPrior(burst.length);
        return Object.assign(fit, { t0, last, n: burst.length, span, afterPause, curved });
      }

      // seconds from the window start at which the fitted curve reaches level du (relative to the latest tick);
      // past capT the curve carries on in a straight line at the rate it had there (no runaway extrapolation)
      function timeAt(m, du, capT) {
        const val = t => m.a + m.b * t + m.c * curveF(t);
        if (val(capT) >= du) {
          let lo = 0, hi = capT;
          if (val(lo) >= du) return lo;
          for (let i = 0; i < 48; i++) { const mid = (lo + hi) / 2; if (val(mid) < du) lo = mid; else hi = mid; }
          return hi;
        }
        const r = m.b + (m.c ? m.c * (curveF(capT + 0.01) - curveF(capT)) / 0.01 : 0);
        return r > 0 ? capT + (du - val(capT)) / r : Infinity;
      }

      function fitNow() {
        if (cache) return cache;
        const m = model();
        if (!m) return (cache = { m: null });
        const capT = m.span + Math.max(60, C.capFactor * m.span / 2);
        const tk = timeAt(m, 0, capT), tn = timeAt(m, 1, capT), tg = timeAt(m, C.goal - m.last.u, capT);
        return (cache = { m, tk, tn, tg });
      }

      return {
        sample(now, used) {
          if (lastUsed !== null && used < lastUsed) { ticks = []; cache = null; }     // a reset: new cycle
          if (lastUsed !== null && used > lastUsed && lastPollT !== null) {
            const k = used - lastUsed;
            for (let j = 1; j <= k; j++) ticks.push({ t: lastPollT + (now - lastPollT) * (j - 0.5) / k, u: lastUsed + j });
            if (ticks.length > 300) ticks = ticks.slice(-300);
            const n = ticks.length, s = burstStart(n - 1);
            if (n - s >= C.minBurst) { const b = ticks.slice(s).slice(-C.window); mem = (b[b.length - 1].t - b[0].t) / (b[b.length - 1].u - b[0].u); }
            cache = null;
          }
          lastUsed = used; lastPollT = now;
        },
        // -> { rate (%/s), eta (s), at (ms; Infinity while alarms are held), paused, burnLeft, curved } or null
        estimate(now) {
          if (lastUsed === null) return null;
          if (lastUsed >= C.goal) return { rate: 0, eta: 0, at: now, paused: false };
          const { m, tk, tn, tg } = fitNow();
          if (!m) {
            if (!mem) return null;
            const eta = (C.goal - lastUsed - 0.5) * mem / 1000;
            return { rate: 1000 / mem, eta, at: now + eta * 1000, paused: false, curved: false };
          }
          if (!isFinite(tg)) return null;
          // fastest spacing among the last 3 tick-overs of this burst: the pessimistic rate the backstop uses
          let fastSpacing = null;
          { const n = ticks.length, s0 = Math.max(1, n - 3, burstStart(n - 1) + 1); for (let i = s0; i < n; i++) { const g = gapAt(i); if (fastSpacing === null || g < fastSpacing) fastSpacing = g; } }
          let at = m.last.t + (tg - tk) * 1000;
          const next = m.last.t + (tn - tk) * 1000, spacing = (tn - tk) * 1000;
          const late = now + C.overdueResid * spacing - next;
          if (late > 0) at += late;
          const eta = Math.max(0, (at - now) / 1000);
          const paused = now - m.last.t > Math.max(C.pauseFactor * spacing, C.pauseMinMs);
          const fresh = m.afterPause && m.n < C.holdTicks;
          const rate = spacing > 0 ? 1000 / spacing : 0;
          if (paused || fresh) return { rate: paused ? 0 : rate, eta, at: Infinity, paused: true, burnLeft: eta, curved: m.curved, fastSpacing };
          return { rate, eta, at: now + eta * 1000, paused: false, curved: m.curved, fastSpacing };
        },
      };
    }

    // Learner: replays stored cycles through each candidate predictor the way the monitor runs it, scores
    // every alarm against when usage really hit the goal, picks the shape that has been doing best on recent
    // cycles, and measures each alarm's steady bias so it can be corrected.
    // Cycle format: { s: startMs, u0, ev: [[seenMs, prevPollMs, used], ...], end: { t, kind: 'zero'|'reset'|'cut', u } }

    const CANDIDATES = {
      sqrt:  { shape: 'sqrt',  window: 40, halfLife: 12, holdTicks: 4 },
      accel: { shape: 'accel', window: 40, halfLife: 12, holdTicks: 4 },
      line:  { shape: 'line',  window: 25, holdTicks: 4 },
    };
    const DEFAULT_KEY = 'sqrt';

    function rng(seed) { let a = seed >>> 0; return () => { a = (a + 0x6D2B79F5) >>> 0; let t = Math.imul(a ^ (a >>> 15), 1 | a); t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t; return ((t ^ (t >>> 14)) >>> 0) / 4294967296; }; }

    // real tick-over times: each one happened somewhere between the previous check and the one that saw it
    function truthOf(cycle, rand) {
      const ticks = []; let prevU = cycle.u0;
      for (const [t, p, u] of cycle.ev) {
        if (u <= prevU) { prevU = u; continue; }
        const ts = []; for (let k = prevU + 1; k <= u; k++) ts.push(p + (t - p) * rand());
        ts.sort((a, b) => a - b);
        ts.forEach((x, i) => ticks.push({ t: x, u: prevU + 1 + i }));
        prevU = u;
      }
      for (let i = 1; i < ticks.length; i++) if (ticks[i].t <= ticks[i - 1].t) ticks[i].t = ticks[i - 1].t + 1;
      return ticks;
    }

    // one replay: poll like the monitor does, fire each alarm once, return err per mark
    // err = (when the goal was really reached - when the alarm fired) - mark: > 0 early, < 0 late, null = never fired
    function replay(makePredictor, cfg, ticks, startMs, u0, goal, thresholds, rand) {
      const gi = ticks.findIndex(x => x.u >= goal);
      if (gi < 0) return null;
      const Tgoal = ticks[gi].t;
      const pred = makePredictor(Object.assign({}, cfg, { goal }));
      let idx = -1;
      const usedAt = t => { while (idx + 1 < ticks.length && ticks[idx + 1].t <= t) idx++; return idx >= 0 ? ticks[idx].u : u0; };
      const marks = Object.keys(thresholds).map(Number);
      const maxThr = Math.max(...marks.map(m => thresholds[m])) * 1000;
      const fired = {};
      let now = startMs + Math.floor(rand() * 3000), nextPoll = now;
      while (now < Tgoal) {
        let e = null;
        if (now >= nextPoll) {
          pred.sample(now, usedAt(now));
          e = pred.estimate(now);
          nextPoll = now + (e && e.eta < 90 ? 1000 : 3000);
          if (!e || e.at - now > maxThr + (nextPoll - now) + 500) { now = Math.min(nextPoll, Tgoal); continue; }
        }
        e = e || pred.estimate(now);
        if (e) for (const m of marks) if (fired[m] === undefined && e.at - now <= thresholds[m] * 1000) fired[m] = now;
        now += 250;
      }
      const out = {};
      for (const m of marks) out[m] = fired[m] === undefined ? null : (Tgoal - fired[m]) / 1000 - m;
      return out;
    }

    function goalsFor(cycle) {
      const last = cycle.end ? cycle.end.u : (cycle.ev.length ? cycle.ev[cycle.ev.length - 1][2] : cycle.u0);
      const real = cycle.end && cycle.end.kind === 'zero';
      const top = real ? 100 : last;
      const goals = [];
      for (let k = 0; k <= 5; k++) { const g = top - k; if (g > cycle.u0 + 15) goals.push({ g, w: real && k === 0 ? 2 : 1, real: real && k === 0 }); }
      return goals;
    }

    const loss = (err, m) => (err === null ? 1.5 * m : Math.abs(err) * (err < 0 ? 1.5 : 1));   // late hurts more

    function wmedian(pairs) {           // [[value, weight]]
      const s = pairs.filter(p => p[0] !== null).sort((a, b) => a[0] - b[0]);
      const tot = s.reduce((x, p) => x + p[1], 0); let acc = 0;
      for (const [v, w] of s) { acc += w; if (acc >= tot / 2) return v; }
      return 0;
    }

    // score every candidate on the most recent cycles; returns the calibration to use
    function calibrate(makePredictor, cycles, opts) {
      const O = Object.assign({ marks: [24, 12, 6], maxCycles: 40, current: DEFAULT_KEY, minCycles: 3, switchMargin: 0.05 }, opts || {});
      const usable = cycles.filter(c => c.ev && c.ev.length >= 20 && c.end).slice(-O.maxCycles);
      const res = {};
      for (const [key, cfg] of Object.entries(CANDIDATES)) {
        let L = 0, W = 0; const errs = {}; O.marks.forEach(m => { errs[m] = []; });
        usable.forEach((c, i) => {
          const age = usable.length - 1 - i, wc = Math.pow(0.5, age / 15);
          const rand = rng(Math.floor(c.s / 1000) ^ 0x5bd1e995);
          const ticks = truthOf(c, rand);
          for (const { g, w, real } of goalsFor(c)) {
            const thr = {}; O.marks.forEach(m => { thr[m] = m; });
            const r = replay(makePredictor, cfg, ticks, c.s, c.u0, g, thr, rand);
            if (!r) continue;
            for (const m of O.marks) { L += wc * w * loss(r[m], m); W += wc * w; errs[m].push([r[m], wc * w, real]); }
          }
        });
        res[key] = { score: W ? L / W : Infinity, errs };
      }
      let key = O.current in CANDIDATES ? O.current : DEFAULT_KEY;
      const best = Object.keys(res).reduce((a, b) => (res[b].score < res[a].score ? b : a));
      if (usable.length >= O.minCycles && res[best].score < res[key].score * (1 - O.switchMargin)) key = best;
      // bias: from the real run-outs when there are enough of them (the end of a cycle behaves differently from
      // the middle), otherwise from every scored level
      const n = usable.length, bias = {};
      const realErrs = m => res[key].errs[m].filter(e => e[2]);
      const nReal = realErrs(O.marks[0]).filter(e => e[0] !== null).length;
      for (const m of O.marks) {
        const pool = nReal >= 3 ? realErrs(m) : res[key].errs[m];
        const k = nReal >= 3 ? nReal : n;
        const med = wmedian(pool);
        bias[m] = Math.max(-5, Math.min(5, med * k / (k + 2)));
      }
      const scores = {}; for (const k of Object.keys(res)) scores[k] = +res[k].score.toFixed(3);
      return { key, cfg: CANDIDATES[key], bias, scores, n, nReal, at: Date.now() };
    }

    // thresholds the live monitor should use: fire mark m when the predicted run-out is (m - bias) seconds away
    function thresholdsFrom(calib, marks) {
      const thr = {}; for (const m of marks) thr[m] = Math.max(1, m - ((calib && calib.bias && calib.bias[m]) || 0));
      return thr;
    }

    const LABEL = { sqrt: '√ speed-up', accel: 'linear speed-up', line: 'straight line' };

    return { makePredictor, CANDIDATES, DEFAULT_KEY, LABEL, calibrate, thresholdsFrom, replay, truthOf, goalsFor, rng, loss };
  }
  const L = learnerModule();

  // Tuesday's four cycles (Oct 20), so the learner has something to start from
  const SEED = [[1792521977000,0,"reset",98,1951500,[[190,3,1],[231,3,2],[252,3,3],[276,3,4],[297,3,5],[312,3,6],[330,3,7],[342,3,8],[360,3,9],[369,3,10],[381,3,11],[390,3,12],[396,3,13],[402,3,14],[411,3,15],[423,3,16],[432,3,17],[441,3,18],[447,3,19],[459,3,20],[468,3,21],[474,3,22],[483,3,23],[489,3,24],[495,3,25],[504,3,26],[513,3,27],[519,3,28],[525,3,29],[531,3,30],[537,3,31],[546,3,32],[555,3,33],[561,3,34],[567,3,35],[576,3,36],[579,3,37],[589,3,38],[594,3,39],[600,3,40],[606,3,41],[615,3,42],[621,3,43],[636,3,44],[678,3,45],[912,3,46],[1050,3,47],[1173,3,48],[1209,3,49],[1248,3,50],[1278,3,51],[1308,3,52],[1359,3,53],[1386,3,54],[1434,3,55],[1461,3,56],[1494,3,57],[1512,3,58],[1560,3,59],[1584,3,60],[1617,3,61],[1644,3,62],[1686,3,63],[1710,3,64],[1719,3,65],[1743,3,66],[1752,3,67],[1762,3,68],[1767,3,69],[1773,3,70],[1779,3,71],[1785,3,72],[1794,3,73],[1803,3,74],[1809,3,75],[1815,3,76],[1818,3,77],[1824,3,78],[1830,3,79],[1836,3,80],[1839,3,81],[1845,3,82],[1851,3,83],[1854,3,84],[1860,3,85],[1866,3,86],[1875,3,87],[1878,3,88],[1887,3,89],[1893,3,90],[1899,3,91],[1908,3,92],[1917,3,93],[1920,3,94],[1926,3,95],[1932,3,96],[1938,3,97],[1944,3,98]]],[1792523930000,0,"cut",98,1809000,[[9,3,1],[75,3,2],[204,3,3],[300,3,4],[408,3,5],[420,3,6],[426,3,7],[435,3,8],[442,3,9],[447,3,10],[456,3,11],[465,3,12],[477,3,13],[483,3,14],[492,3,15],[498,3,16],[504,3,17],[513,3,18],[519,3,19],[525,3,20],[534,3,21],[540,3,22],[546,3,23],[553,3,24],[561,3,25],[567,3,26],[573,3,27],[579,3,28],[585,3,29],[591,3,30],[598,3,31],[606,3,32],[636,3,33],[744,3,34],[819,3,35],[942,3,36],[1011,3,37],[1020,3,38],[1026,3,39],[1029,3,40],[1035,3,41],[1038,3,42],[1044,3,43],[1050,3,44],[1053,3,45],[1059,3,46],[1062,3,47],[1071,3,48],[1077,3,49],[1083,3,50],[1092,3,51],[1098,3,52],[1107,3,53],[1113,3,54],[1122,3,55],[1128,3,56],[1137,3,57],[1143,3,58],[1149,3,59],[1155,3,60],[1161,3,61],[1167,3,62],[1173,3,63],[1179,3,64],[1185,3,65],[1191,3,66],[1194,3,67],[1200,3,68],[1206,3,69],[1212,3,70],[1215,3,71],[1224,3,72],[1227,3,73],[1233,3,74],[1239,3,75],[1248,3,76],[1302,3,77],[1401,3,78],[1533,3,79],[1650,3,80],[1707,3,81],[1716,3,82],[1722,3,83],[1725,3,84],[1731,3,85],[1737,3,86],[1743,3,87],[1749,3,88],[1755,3,89],[1761,3,90],[1767,3,91],[1773,3,92],[1779,3,93],[1785,3,94],[1791,3,95],[1794,3,96],[1803,3,97],[1809,3,98]]],[1792533710000,3,"zero",100,535500,[[3,3,4],[6,3,5],[9,3,6],[15,3,7],[18,3,8],[21,3,9],[27,3,10],[30,3,11],[36,3,12],[42,3,13],[45,3,14],[51,3,15],[54,3,16],[57,3,17],[63,3,18],[69,3,19],[72,3,20],[78,3,21],[84,3,22],[90,3,23],[93,3,24],[102,3,25],[108,3,26],[114,3,27],[120,3,28],[126,3,29],[132,3,30],[138,3,31],[144,3,32],[150,3,33],[156,3,34],[165,3,35],[174,3,36],[180,3,37],[186,3,38],[192,3,39],[198,3,40],[207,3,41],[213,3,42],[216,3,43],[222,3,44],[228,3,45],[231,3,46],[237,3,47],[246,3,48],[249,3,49],[255,3,50],[261,3,51],[270,3,52],[273,3,53],[280,3,54],[282,3,55],[291,3,56],[294,3,57],[300,3,58],[306,3,59],[312,3,60],[315,3,61],[321,3,62],[324,3,63],[330,3,64],[339,3,65],[345,3,66],[354,3,67],[363,3,68],[372,3,69],[378,3,70],[384,3,71],[390,3,72],[396,3,73],[402,3,74],[407,3,75],[410,3,76],[416,3,77],[422,3,78],[428,3,79],[431,3,80],[434,3,81],[440,3,82],[444,3,83],[450,1,84],[456,1,85],[461,1,86],[467,1,87],[471,1,88],[475,1,89],[483,1,90],[486,1,91],[493,1,92],[500,1,93],[505,1,94],[512,1,95],[516,1,96],[521,1,97],[527,1,98],[531,1,99],[536,1,100]]],[1792534276000,0,"zero",100,481500,[[3,3,1],[7,3,2],[9,3,3],[15,3,4],[18,3,5],[27,3,6],[31,3,7],[36,3,8],[42,3,9],[48,3,10],[51,3,11],[58,3,12],[60,3,13],[66,3,14],[69,3,15],[75,3,16],[78,3,17],[81,3,18],[87,3,19],[93,3,20],[96,3,21],[102,3,22],[105,3,23],[116,3,24],[117,3,25],[123,3,26],[131,3,27],[135,3,28],[141,3,29],[147,3,30],[150,3,31],[156,3,32],[162,3,33],[168,3,34],[171,3,35],[174,3,36],[180,3,37],[184,3,38],[192,3,39],[195,3,40],[204,3,41],[207,3,42],[211,3,43],[217,3,44],[219,3,45],[225,3,46],[231,3,47],[234,3,48],[240,3,49],[244,3,50],[249,3,51],[255,3,52],[259,3,53],[264,3,54],[270,3,55],[274,3,56],[282,3,58],[289,3,59],[291,3,60],[300,3,61],[303,3,62],[309,3,63],[316,3,64],[318,3,65],[327,3,66],[330,3,67],[336,3,68],[339,3,69],[346,3,70],[349,3,71],[354,3,72],[360,3,73],[363,3,74],[369,3,75],[372,3,76],[378,3,77],[381,3,78],[388,3,79],[390,3,80],[394,1,81],[398,1,82],[402,1,83],[408,1,84],[413,1,85],[417,1,86],[420,1,87],[425,1,88],[429,1,89],[435,1,90],[440,1,91],[447,1,92],[450,1,93],[454,1,94],[459,1,95],[464,1,96],[469,1,97],[473,1,98],[476,1,99],[482,1,100]]]];
  const seedCycles = SEED.map(([s, u0, kind, u, endDt, ev]) => ({ s, u0, src: 'seed', end: { dt: endDt, kind, u }, ev: ev.map(([dt, dp, uu]) => [dt * 1000, dp * 1000, uu]), al: [] }));

  // compact stored cycle -> learner format (absolute times)
  const expand = c => ({ s: c.s, u0: c.u0, ev: c.ev.map(([dt, dp, u]) => [c.s + dt, c.s + dt - dp, u]), end: c.end ? { t: c.s + c.end.dt, kind: c.end.kind, u: c.end.u } : null });

  // ---- Storage: Tampermonkey storage when available (survives clearing ChatGPT's site data) ----
  const hasGM = typeof GM_getValue === 'function' && typeof GM_setValue === 'function';
  const ls = {
    get(k, d) { try { const s = localStorage.getItem(k); return s == null ? d : JSON.parse(s); } catch (e) { return d; } },
    set(k, v) { try { localStorage.setItem(k, JSON.stringify(v)); return true; } catch (e) { return false; } },
  };
  const store = hasGM ? {
    get(k, d) { try { const v = GM_getValue(k); return v === undefined ? d : v; } catch (e) { return d; } },
    set(k, v) { try { GM_setValue(k, v); } catch (e) {} },
  } : ls;

  const dayKey = t => { const d = new Date(t); return `${d.getFullYear()}-${d.getMonth() + 1}-${d.getDate()}`; };

  // ---- Core: cycles, alarms, scoring, learning, economics (no DOM in here) ----
  function makeCore(env) {
    let history = store.get(K.hist, null);
    if (!Array.isArray(history)) history = ls.get(K.recent, []);          // fall back to the page copy
    let calib = store.get(K.calib, null);
    let cur = store.get(K.cur, null);
    let lastResult = store.get(K.last, null);
    let day = store.get(K.day, null);
    let econ = Object.assign({ cpm: null, ppm: null, live: null, n: 0, at: 0 }, store.get(K.econ, {}));   // cpm: credits/min at 0%; ppm: %/min just before 0%
    let lastUsed = null, lastPollT = null, pred = null, est = null, fired = {}, silenced = false, learning = false;
    let credits = null, resetAt = null, creditTrail = [];
    let thr = L.thresholdsFrom(calib, MARKS);
    const keyNow = () => (calib && L.CANDIDATES[calib.key] ? calib.key : L.DEFAULT_KEY);
    const lastU = c => (c.ev.length ? c.ev[c.ev.length - 1][2] : c.u0);

    function today(t) {
      const k = dayKey(t);
      if (!day || day.k !== k) { day = { k, zeros: 0, resets: 0, stallMs: 0, cycles: 0, zeroAt: day && day.zeroAt && t - day.zeroAt < 6 * 3600e3 ? day.zeroAt : null }; store.set(K.day, day); }
      return day;
    }
    function saveDay() { store.set(K.day, day); }
    function trimHistory() {
      const cutoff = env.now() - KEEP_DAYS * 864e5;
      history = history.filter(c => c.s >= cutoff).slice(-3000);
    }
    function saveHistory() {
      trimHistory();
      store.set(K.hist, history);
      ls.set(K.recent, history.slice(-150));                                // readable copy on the page
    }
    let curSavedAt = 0;
    function saveCur(force) { const t = env.now(); if (force || t - curSavedAt > 10000) { store.set(K.cur, cur); curSavedAt = t; } }

    function newPredictor() { pred = L.makePredictor(L.CANDIDATES[keyNow()]); }
    function startCycle(t, used) {
      cur = { s: t, u0: used, ev: [], end: null, al: [], key: keyNow(), lp: t };
      fired = {}; silenced = false; newPredictor(); saveCur(true);
      const D = today(t); D.cycles++;
      if (D.zeroAt) { const stall = t - D.zeroAt; D.stallMs += stall; D.zeroAt = null; env.log(`back from 0% after ${fmtDur(stall / 1000)} stalled`); }
      saveDay();
    }
    function closeCycle(tEnd, kind, u) {
      if (!cur) return;
      cur.end = { dt: Math.round(tEnd - cur.s), kind, u };
      cur.al = Object.keys(fired).map(m => [isNaN(+m) ? m : +m, Math.round(fired[m].at - cur.s), +(+fired[m].thr || 0).toFixed(2), isFinite(fired[m].predAt) ? Math.round(fired[m].predAt - cur.s) : null]);
      delete cur.lp; delete cur.fa;
      if (cur.ev.length >= 3) { history.push(cur); saveHistory(); }
      cur = null; store.set(K.cur, null);
      learn();
    }
    function score(tZero) {
      const res = MARKS.map(m => (fired[m] ? { m, lead: (tZero - fired[m].at) / 1000, err: (tZero - fired[m].at) / 1000 - m } : { m, err: null }));
      const bs = fired.backstop ? (tZero - fired.backstop.at) / 1000 : null;
      lastResult = { t: tZero, res, backstopLead: bs };
      store.set(K.last, lastResult);
      env.log('hit 0% — ' + res.map(r => (r.err === null ? `${r.m}s: never fired` : `${r.m}s warning ${r.lead.toFixed(1)}s ahead (${describeErr(r.err)})`)).join(' · ') + (bs !== null ? ` · backstop ${bs.toFixed(1)}s ahead` : ''));
      const D = today(tZero); D.zeros++; D.zeroAt = tZero; saveDay();
      // plan burn in the last minutes before 0%, to compare like with like against the credit burn right after
      if (cur) {
        const endDt = tZero - cur.s;
        for (const win of [180, 300, 600]) {
          const n = cur.ev.filter(e => e[0] >= endDt - win * 1000).length;
          if (n >= 4 || win === 600) { if (n >= 2) { const r = n / (win / 60); econ.ppm = econ.ppm ? 0.5 * econ.ppm + 0.5 * r : r; econ.n = (econ.n || 0) + 1; econ.at = tZero; store.set(K.econ, econ); } break; }
        }
      }
    }

    function learn() {
      if (!LEARN || learning) return;
      const cycles = seedCycles.concat(history).map(expand).filter(c => c.end);
      if (cycles.length < 2) return;
      learning = true;
      env.runLearner(cycles, keyNow(), result => {
        learning = false;
        if (!result) return;
        const prevKey = keyNow();
        calib = result; store.set(K.calib, calib);
        thr = L.thresholdsFrom(calib, MARKS);
        // switch the cycle in progress to the new curve too (its tick-overs are replayed into it)
        if (cur && !cur.end && cur.key !== calib.key) { cur.key = calib.key; resume(cur); }
        const sc = Object.entries(calib.scores).map(([k, v]) => `${k} ${v.toFixed(2)}`).join(' · ');
        env.log(`learned from ${calib.n} cycles: ${L.LABEL[calib.key]} fits best${calib.key !== prevKey ? ` (was ${L.LABEL[prevKey]})` : ''}; alarms at ${MARKS.map(m => thr[m].toFixed(1)).join('/')} s [miss score ${sc}]`);
      });
    }

    // replay a stored open cycle into a fresh predictor after a page reload
    function resume(c) {
      cur = c; fired = {}; pred = L.makePredictor(L.CANDIDATES[c.key in L.CANDIDATES ? c.key : keyNow()]);
      let prevU = c.u0;
      pred.sample(c.s, c.u0);
      for (const [dt, dp, u] of c.ev) { pred.sample(c.s + dt - dp, prevU); pred.sample(c.s + dt, u); prevU = u; }
      if (c.lp) pred.sample(c.lp, prevU);
      for (const [m, v] of Object.entries(c.fa || {})) fired[m] = { at: c.s + v[0], thr: v[1], predAt: v[2] === null ? Infinity : c.s + v[2] };
      return prevU;
    }

    function fire(m, t, th, predAt, quiet) {
      fired[m] = { at: t, thr: th, predAt };
      if (cur) { cur.fa = cur.fa || {}; cur.fa[m] = [Math.round(t - cur.s), +(+th || 0).toFixed(2), isFinite(predAt) ? Math.round(predAt - cur.s) : null]; saveCur(true); }
      if (!quiet) env.alarm(m, silenced);
    }

    // economics: credits/min while on credits (plan at 0%), %/min while on the plan -> credits per 1% of the allowance
    function noteCredits(t, bal, used) {
      if (typeof bal !== 'number' || !isFinite(bal)) return;
      credits = bal;
      creditTrail.push([t, bal, used]);
      creditTrail = creditTrail.filter(x => t - x[0] <= 6 * 60e3);
      const onCredits = creditTrail.filter(x => x[2] >= 100);
      if (onCredits.length >= 2) {
        const a = onCredits[0], b = onCredits[onCredits.length - 1];
        if (b[0] - a[0] >= 60e3 && a[1] > b[1]) { const cpm = (a[1] - b[1]) / ((b[0] - a[0]) / 60e3); econ.cpm = econ.cpm ? 0.7 * econ.cpm + 0.3 * cpm : cpm; econ.at = t; store.set(K.econ, econ); }
      }
    }
    function notePlanRate(t, ratePerMin) {
      if (!(ratePerMin > 0.2)) return;                                       // ignore idle trickle
      econ.live = econ.live ? 0.9 * econ.live + 0.1 * ratePerMin : ratePerMin;   // only a stand-in until a run-out has been measured
    }

    return {
      poll(t, used, extra) {
        extra = extra || {};
        if (extra.resetAt) resetAt = extra.resetAt;
        if (lastUsed === null) {                                           // first reading since the page loaded
          today(t);
          const fresh = cur && !cur.end && t - (cur.lp || cur.s) < 5 * 60e3 && used >= lastU(cur);
          if (fresh) { const u = resume(cur); lastUsed = u; lastPollT = cur.lp || null; env.log(`(monitor started, picked up the cycle in progress at ${100 - used}% left)`); }
          else {
            if (cur && !cur.end && cur.ev.length) { const lp = cur.lp || cur.s; closeCycle(lp, 'cut', lastU(cur)); }
            cur = null;
            if (used < 100) startCycle(t, used);
            env.log(`(monitor started at ${100 - used}% left)`);
            lastUsed = used; lastPollT = t; if (pred) pred.sample(t, used);
            noteCredits(t, extra.credits, used);
            if (!calib && LEARN) learn();
            return;
          }
        }
        if (used < lastUsed) {                                             // a reset
          if (cur && !cur.end) closeCycle((lastPollT + t) / 2, 'reset', lastUsed);
          env.log(`reset: ${100 - lastUsed}% → ${100 - used}% left`);
          const D = today(t); D.resets++; saveDay();
          startCycle(t, used);
        } else if (used > lastUsed && cur) {
          cur.ev.push([Math.round(t - cur.s), Math.round(t - lastPollT), used]);
          env.log(`${100 - lastUsed}% → ${100 - used}% left`);
          if (used >= 100) { const tz = (lastPollT + t) / 2; score(tz); closeCycle(tz, 'zero', 100); }
          else saveCur(true);
        } else if (!cur && used < 100) startCycle(t, used);
        if (pred) pred.sample(t, used);
        lastUsed = used; lastPollT = t;
        if (cur) { cur.lp = t; saveCur(false); }
        noteCredits(t, extra.credits, used);
      },
      tick(t) {
        est = cur && pred ? pred.estimate(t) : null;
        if (!cur || lastUsed === null) return;
        if (est && est.rate) notePlanRate(t, est.rate * 60);
        const left = 100 - lastUsed;
        if (est && !est.paused) {
          // when several marks come due at once (the prediction caught up late) only the most urgent one sounds
          const due = MARKS.filter(m => !fired[m] && est.at - t <= thr[m] * 1000);
          const loudest = due.length ? due[due.length - 1] : null;
          if (HEADS_UP_S && !fired.headsup && est.at - t <= HEADS_UP_S * 1000) fire('headsup', t, HEADS_UP_S, est.at, due.length > 0);
          for (const m of due) fire(m, t, thr[m], est.at, m !== loudest);
        }
        // backstop, in case the prediction is wrong or missing: while the 24 s alarm is still silent, buzz when the
        // fastest recent tick spacing (the burn often speeds up right at the end) says BACKSTOP_S remain, or at
        // BACKSTOP_PCT left unless a live prediction has the 24 s alarm due within the next ~20 s anyway
        if (!fired[MARKS[0]] && !fired.backstop) {
          const fs = est && est.fastSpacing ? est.fastSpacing : 0;           // ms per 1%
          const byRate = fs > 0 && !(est && est.paused) && (left - 0.5) * fs <= BACKSTOP_S * 1000;
          const live = est && !est.paused && isFinite(est.at) && est.at - t <= (MARKS[0] + 21) * 1000;
          if (byRate || (left <= BACKSTOP_PCT && !live)) fire('backstop', t, left, est && isFinite(est.at) ? est.at : Infinity);
        }
      },
      silence() { silenced = true; },
      learnNow: learn,
      state() {
        const D = today(env.now());
        const ppm = econ.ppm || econ.live;
        const creditsPerPct = econ.cpm && ppm ? econ.cpm / ppm : null;
        return { used: lastUsed, est, cur, fired, thr, calib, key: keyNow(), lastResult, silenced, learning, cycles: history.length, credits, resetAt, day: D, econ: { cpm: econ.cpm, ppm, measured: !!econ.ppm, n: econ.n || 0, creditsPerPct, resetValueCredits: creditsPerPct ? 100 * creditsPerPct : null } };
      },
      exportData() {
        return { app: 'chatgpt-usage-monitor', version: VERSION, exportedAt: new Date(env.now()).toISOString(), storage: hasGM ? 'tampermonkey' : 'page', marks: MARKS, prices: { reset: RESET_PRICE, credit: CREDIT_PRICE }, calibration: calib, lastResult, day, econ, current: cur, history, seed: seedCycles, log: store.get(K.log, []) };
      },
    };
  }

  function describeErr(e) {
    if (e === null) return 'never fired';
    const a = Math.abs(e);
    return a < 0.25 ? 'on time' : `${a.toFixed(1)}s ${e > 0 ? 'early' : 'late'}`;
  }
  const fmtDur = s => { s = Math.max(0, Math.round(s)); const h = Math.floor(s / 3600), m = Math.floor((s % 3600) / 60); if (h) return `${h}h ${String(m).padStart(2, '0')}m`; return m ? `${m}:${String(s % 60).padStart(2, '0')}` : `${s}s`; };
  const fmtLong = s => { s = Math.max(0, Math.round(s)); const d = Math.floor(s / 86400), h = Math.floor((s % 86400) / 3600), m = Math.floor((s % 3600) / 60); return d ? `${d}d ${h}h` : h ? `${h}h ${m}m` : `${m}m`; };

  // ---- Background learning: run the replays in a Worker so the page never stutters ----
  function runLearner(cycles, currentKey, done) {
    const src = `${learnerModule.toString()}\nconst L = learnerModule();\nonmessage = e => { let r = null; try { r = L.calibrate(L.makePredictor, e.data.cycles, { current: e.data.current }); } catch (err) {} postMessage(r); };`;
    let w = null, url = null;
    const WW = (typeof unsafeWindow !== 'undefined' && unsafeWindow && unsafeWindow.Worker) || (typeof Worker !== 'undefined' ? Worker : null);
    try { url = URL.createObjectURL(new Blob([src], { type: 'text/javascript' })); w = WW ? new WW(url) : null; } catch (e) { w = null; }
    if (!w) { setTimeout(() => { let r = null; try { r = L.calibrate(L.makePredictor, cycles.slice(-25), { current: currentKey }); } catch (e) {} done(r); }, 50); return; }
    const finish = r => { try { w.terminate(); URL.revokeObjectURL(url); } catch (e) {} done(r); };
    const to = setTimeout(() => finish(null), 120000);
    w.onmessage = e => { clearTimeout(to); finish(e.data); };
    w.onerror = () => { clearTimeout(to); finish(null); };
    w.postMessage({ cycles, current: currentKey });
  }

  if (typeof window === 'undefined') {                                     // loaded by the test harness
    module.exports = { learnerModule, makeCore, seedCycles, expand, describeErr, MARKS, K, HEADS_UP_S, BACKSTOP_PCT, BACKSTOP_S };
    return;
  }

  // ---- Browser side ----
  const W = (typeof unsafeWindow !== 'undefined' && unsafeWindow) || window;   // the page's own window (Tampermonkey sandboxes `window`)
  if (W.__usageMonitor2Stop) { try { W.__usageMonitor2Stop(); } catch (e) {} }
  const TAB = Math.random().toString(36).slice(2);
  const LIVE = 'um2.live', SILENCE = 'um2.silence';
  const prefs = Object.assign({ sound: true, logOpen: true }, store.get(K.prefs, {}));
  const clock = t => new Date(t).toLocaleTimeString([], { hour: 'numeric', minute: '2-digit', second: '2-digit' });
  const stamp = t => new Date(t).toLocaleString([], { month: 'short', day: 'numeric', hour: 'numeric', minute: '2-digit', second: '2-digit' });

  // text log, newest first (also kept under the old key so it reads the same as before)
  let logLines = store.get(K.log, null);
  if (!Array.isArray(logLines)) logLines = ls.get(OLD_LOG, []).map(x => '(earlier) ' + x);
  function log(line) {
    logLines.unshift(`${stamp(Date.now())}: ${line}`);
    logLines = logLines.slice(0, 400);
    store.set(K.log, logLines); ls.set(OLD_LOG, logLines.slice(0, 200));
    render();
  }

  // sound
  let actx = null;
  function unlockAudio() { try { actx = actx || new (W.AudioContext || W.webkitAudioContext)(); if (actx.state === 'suspended') actx.resume(); } catch (e) {} }
  function tone(n, freq, gap, type, vol) {
    if (!actx || !prefs.sound) return;
    const t0 = actx.currentTime + 0.02;
    for (let i = 0; i < n; i++) {
      const o = actx.createOscillator(), g = actx.createGain();
      o.type = type || 'sine'; o.frequency.value = freq;
      g.gain.setValueAtTime(0.0001, t0 + i * gap); g.gain.exponentialRampToValueAtTime(vol || 0.35, t0 + i * gap + 0.01);
      g.gain.exponentialRampToValueAtTime(0.0001, t0 + i * gap + gap * 0.8);
      o.connect(g).connect(actx.destination); o.start(t0 + i * gap); o.stop(t0 + i * gap + gap);
    }
  }
  const PATTERN = { headsup: [1, 520, 0.25, 'sine', 0.18], 24: [2, 660, 0.28], 12: [3, 880, 0.22], 6: [5, 1100, 0.14], backstop: [2, 220, 0.6, 'square', 0.22] };
  const ALARM_NAME = { headsup: `${HEADS_UP_S}s heads-up`, backstop: 'backstop', 24: '24s alarm', 12: '12s alarm', 6: '6s alarm' };
  let flashUntil = 0;
  function alarm(m, silenced) {
    const p = PATTERN[m] || [2, 880, 0.2];
    if (!silenced) tone(...p);
    if (m !== 'headsup') flashUntil = Date.now() + 2500;
    const S = core ? core.state() : null;
    log(`${ALARM_NAME[m] || m}${m === 'backstop' && S ? ` at ${100 - S.used}% left` : ''}${silenced ? ' (silenced)' : ''}`);
  }

  const core = makeCore({ now: () => Date.now(), log, alarm, runLearner });

  // ---- Panel (drawn in the page and in the pop-out) ----
  const panels = [];
  const FONT = '-apple-system,BlinkMacSystemFont,"Segoe UI",Inter,Roboto,sans-serif';
  const MONO = 'ui-monospace,"SF Mono",Menlo,Consolas,monospace';
  const css = {
    box: `font:12.5px/1.45 ${FONT};color:#e7e9ee;background:#0f1115;border:1px solid #262a33;border-radius:14px;padding:12px 14px 10px;box-sizing:border-box;`,
    btn: `font:10.5px ${FONT};color:#c9cdd6;background:#1a1d24;border:1px solid #2b303a;border-radius:999px;padding:2px 8px;margin-left:4px;cursor:pointer;white-space:nowrap;`,
    label: 'font-size:10.5px;letter-spacing:.04em;text-transform:uppercase;color:#7c8290;',
    cell: 'min-width:0;',
  };
  function buildPanel(doc, inPip) {
    const el = (tag, style, text) => { const e = doc.createElement(tag); if (style) e.style.cssText = style; if (text != null) e.textContent = text; return e; };
    const root = el('div', css.box + (inPip ? 'width:100%;min-height:100vh;border:none;border-radius:0;' : 'position:fixed;bottom:16px;right:16px;z-index:2147483647;width:384px;box-shadow:0 12px 40px rgba(0,0,0,.55);'));
    // header
    const head = el('div', 'display:flex;align-items:center;gap:6px;margin-bottom:8px;');
    const dot = el('span', 'width:8px;height:8px;border-radius:50%;background:#3fb950;box-shadow:0 0 0 0 rgba(63,185,80,.6);transition:background .3s;');
    const title = el('b', 'flex:1;font-size:12.5px;font-weight:600;letter-spacing:.01em;white-space:nowrap;', 'Usage monitor');
    const bPop = el('button', css.btn, 'Pop out'), bSound = el('button', css.btn), bExport = el('button', css.btn, 'Export'), bMin = el('button', css.btn, '–');
    const bUpd = el('button', css.btn + 'background:#173a2a;border-color:#245c3f;color:#9ff0c0;display:none;', 'Update');
    if (inPip) bPop.style.display = 'none';
    head.append(dot, title, bUpd, bPop, bSound, bExport, bMin);
    title.title = `v${VERSION}`;
    bUpd.onclick = () => { try { if (typeof GM_openInTab === 'function') GM_openInTab(SCRIPT_URL, { active: true }); else W.open(SCRIPT_URL, '_blank'); } catch (e) {} };
    const body = el('div');
    // hero
    const hero = el('div', 'display:flex;align-items:baseline;justify-content:space-between;gap:10px;');
    const big = el('div', 'font-size:34px;font-weight:650;letter-spacing:-.02em;line-height:1.05;');
    const countdown = el('div', 'font-size:22px;font-weight:600;letter-spacing:-.01em;font-variant-numeric:tabular-nums;text-align:right;');
    hero.append(big, countdown);
    const eta = el('div', 'font-size:12px;color:#aab0bc;margin-top:3px;display:flex;justify-content:space-between;gap:8px;');
    const etaL = el('span'), etaR = el('span', 'color:#7c8290;');
    eta.append(etaL, etaR);
    // bar
    const track = el('div', 'height:6px;border-radius:999px;background:#1c2029;margin:9px 0 9px;overflow:hidden;');
    const fill = el('div', 'height:100%;width:0;border-radius:999px;background:#3fb950;transition:width .6s ease,background .4s;');
    track.append(fill);
    // alarm pips
    const marks = el('div', 'display:flex;align-items:center;gap:6px;flex-wrap:wrap;');
    const pipFor = (key, text) => { const p = el('span', 'display:inline-flex;align-items:center;gap:5px;font-size:11px;color:#9aa1ae;padding:2px 8px;border:1px solid #262a33;border-radius:999px;'); const d = el('span', 'width:6px;height:6px;border-radius:50%;background:#2b303a;'); p.append(d, doc.createTextNode(text)); p._d = d; p._k = key; return p; };
    const pips = [];
    if (HEADS_UP_S) pips.push(pipFor('headsup', `${HEADS_UP_S}s`));
    for (const m of MARKS) pips.push(pipFor(m, `${m}s`));
    pips.push(pipFor('backstop', `${BACKSTOP_PCT}%`));
    const bSilence = el('button', css.btn + 'margin-left:auto;background:#3a1d1d;border-color:#5c2b2b;color:#ffb4b4;', 'Silence');
    marks.append(...pips, bSilence);
    // stats grid
    const grid = el('div', 'display:grid;grid-template-columns:1fr 1fr;gap:6px 14px;margin-top:10px;');
    const stat = (lbl) => { const c = el('div', css.cell); const l = el('div', css.label, lbl); const v = el('div', 'font-size:12px;color:#d6d9e0;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;'); c.append(l, v); grid.append(c); return v; };
    const sBurn = stat('burn'), sCurve = stat('curve'), sAlarms = stat('alarms fire at'), sLast = stat('last 0%');
    // cost strip
    const costHead = el('div', css.label + 'margin-top:11px;padding-top:9px;border-top:1px solid #1f232c;', 'cost');
    const cost = el('div', 'display:grid;grid-template-columns:1fr 1fr;gap:5px 14px;margin-top:5px;');
    const costStat = (lbl) => { const c = el('div', css.cell); const l = el('div', css.label, lbl); const v = el('div', 'font-size:12px;color:#d6d9e0;line-height:1.35;'); c.append(l, v); cost.append(c); return v; };
    const cReset = costStat('free reset in'), cCredits = costStat('credits'), cToday = costStat('today'), cValue = costStat(`reset ($${RESET_PRICE}) vs credits`);
    const hint = el('div', 'font-size:11px;color:#8b93a1;margin-top:6px;line-height:1.4;');
    const note = el('div', 'color:#e0b050;margin-top:6px;font-size:11.5px;');
    // log
    const logHead = el('div', 'display:flex;align-items:center;justify-content:space-between;margin-top:9px;padding-top:8px;border-top:1px solid #1f232c;cursor:pointer;');
    const logLbl = el('span', css.label, 'log');
    const logTog = el('span', 'font-size:11px;color:#7c8290;', prefs.logOpen ? 'hide' : 'show');
    logHead.append(logLbl, logTog);
    const logBox = el('div', `margin-top:5px;max-height:92px;overflow:auto;color:#7f8694;font:10.5px/1.4 ${MONO};white-space:pre-wrap;display:${prefs.logOpen ? '' : 'none'};`);
    body.append(hero, eta, track, marks, grid, costHead, cost, hint, note, logHead, logBox);
    root.append(head, body);
    bPop.onclick = () => openPip();
    bSound.onclick = () => {
      const wasLocked = !actx || actx.state !== 'running';
      unlockAudio();
      if (!(wasLocked && prefs.sound)) { prefs.sound = !prefs.sound; store.set(K.prefs, prefs); }   // first press just unlocks
      if (prefs.sound) setTimeout(() => tone(1, 880, 0.15), 60);
      render();
    };
    bExport.onclick = () => exportHistory();
    bMin.onclick = () => { body.style.display = body.style.display === 'none' ? '' : 'none'; bMin.textContent = body.style.display === 'none' ? '+' : '–'; };
    bSilence.onclick = () => { core.silence(); ls.set(SILENCE, Date.now()); render(); };
    logHead.onclick = () => { prefs.logOpen = !prefs.logOpen; store.set(K.prefs, prefs); for (const p of panels) { p.logBox.style.display = prefs.logOpen ? '' : 'none'; p.logTog.textContent = prefs.logOpen ? 'hide' : 'show'; } };
    if (inPip) root.dataset.pip = '1';
    const p = { doc, root, dot, big, countdown, etaL, etaR, fill, pips, bSilence, sBurn, sCurve, sAlarms, sLast, cReset, cCredits, cToday, cValue, hint, note, logBox, logTog, bSound, bUpd };
    panels.push(p);
    return p;
  }

  let pipWin = null;
  async function openPip() {
    unlockAudio();
    if (pipWin || !W.documentPictureInPicture) { if (!W.documentPictureInPicture) statusNote = 'this Chrome has no pop-out (document picture-in-picture) support'; return; }
    try {
      pipWin = await W.documentPictureInPicture.requestWindow({ width: 384, height: 430 });
      pipWin.document.title = 'Usage monitor';
      pipWin.document.body.style.cssText = 'margin:0;background:#0f1115;';
      const p = buildPanel(pipWin.document, true);
      pipWin.document.body.append(p.root);
      pipWin.addEventListener('pagehide', () => { const i = panels.indexOf(p); if (i >= 0) panels.splice(i, 1); pipWin = null; render(); });
      render();
    } catch (e) { pipWin = null; statusNote = `pop-out refused: ${e && e.message ? e.message : e}`; render(); }
  }

  function exportHistory() {
    const data = core.exportData();
    data.fastShare = fastShare;
    const blob = new Blob([JSON.stringify(data)], { type: 'application/json' });
    const a = document.createElement('a');
    const d = new Date(), pad = n => String(n).padStart(2, '0');
    a.href = URL.createObjectURL(blob);
    a.download = `usage-monitor-${d.getFullYear()}-${pad(d.getMonth() + 1)}-${pad(d.getDate())}-${pad(d.getHours())}${pad(d.getMinutes())}.json`;
    document.body.append(a); a.click(); a.remove();
    setTimeout(() => URL.revokeObjectURL(a.href), 10000);
  }

  let statusNote = '', fastShare = null, lastRenderKey = '', updateAvail = null;
  function cmpVer(a, b) { const A = String(a).split('.').map(Number), B = String(b).split('.').map(Number); for (let i = 0; i < Math.max(A.length, B.length); i++) { const d = (A[i] || 0) - (B[i] || 0); if (d) return d; } return 0; }
  function checkForUpdate() {
    if (!SCRIPT_URL || !/^https?:/.test(SCRIPT_URL) || typeof GM_xmlhttpRequest !== 'function') return;
    try {
      GM_xmlhttpRequest({ method: 'GET', url: SCRIPT_URL + (SCRIPT_URL.includes('?') ? '&' : '?') + 't=' + Date.now(), headers: { 'Cache-Control': 'no-cache' }, onload: r => {
        const m = /\/\/\s*@version\s+(\S+)/.exec(r.responseText || '');
        if (m && cmpVer(m[1], VERSION) > 0) { if (updateAvail !== m[1]) { updateAvail = m[1]; log(`version ${m[1]} is available — click Update in the panel`); } }
      } });
    } catch (e) {}
  }
  const money = v => (v >= 100 ? `$${Math.round(v).toLocaleString()}` : `$${v.toFixed(v >= 10 ? 0 : 2)}`);
  // the polling tab shares what it shows, so a second Usage tab (and its pop-out) mirrors it instead of saying "connecting"
  let isLeader = true, liveCache = null, liveReadAt = 0;
  function publishLive(S) {
    try {
      const snap = { t: Date.now(), S: { used: S.used, est: S.est, curKey: S.cur ? S.cur.key : null, fired: S.fired, thr: S.thr, calibN: S.calib ? S.calib.n : null, key: S.key, lastResult: S.lastResult, silenced: S.silenced, learning: S.learning, credits: S.credits, resetAt: S.resetAt, day: S.day, econ: S.econ }, fastShare, note: statusNote, upd: updateAvail, flashUntil, log: logLines.slice(0, 14) };
      localStorage.setItem(LIVE, JSON.stringify(snap));
    } catch (e) {}
  }
  function readLive() {
    const t = Date.now();
    if (t - liveReadAt < 400) return liveCache;
    liveReadAt = t;
    try { const v = JSON.parse(localStorage.getItem(LIVE) || 'null'); liveCache = v && t - v.t < 6000 ? v : null; } catch (e) { liveCache = null; }
    return liveCache;
  }
  function render() {
    if (!panels.length) return;
    const t = Date.now();
    const live = isLeader ? null : readLive();
    const S = live ? Object.assign({}, live.S, { cur: live.S.curKey ? { key: live.S.curKey } : null, calib: live.S.calibN !== null ? { n: live.S.calibN } : null }) : core.state();
    if (isLeader) publishLive(S);
    const logL = live ? live.log : logLines, fShare = live ? live.fastShare : fastShare, note = live ? (live.note || 'mirroring the Usage tab that is polling') : statusNote, upd = live ? live.upd : updateAvail;
    const flashT = live ? live.flashUntil || 0 : flashUntil;
    const left = S.used === null ? null : 100 - S.used;
    const atZero = S.used !== null && S.used >= 100;
    const secs = S.est && !S.est.paused && isFinite(S.est.at) ? (S.est.at - t) / 1000 : null;
    const bigT = left === null ? '…' : `${left}%`;
    let cdT = '', etaLT = '', etaRT = '';
    if (atZero) { etaLT = 'at 0% — waiting for a reset'; etaRT = S.day && S.day.zeroAt ? `stalled ${fmtDur((t - S.day.zeroAt) / 1000)}` : ''; }
    else if (!S.est) { etaLT = left === null ? 'connecting…' : 'learning the burn rate…'; }
    else if (S.est.paused) { etaLT = 'burn paused'; etaRT = `~${fmtDur(S.est.burnLeft || 0)} of burn left`; }
    else { cdT = fmtDur(secs); etaLT = `runs out ~${clock(S.est.at)}`; etaRT = 'left'; }
    const urgent = secs !== null && secs <= MARKS[0], warn = secs !== null && secs <= HEADS_UP_S;
    const color = atZero ? '#e5484d' : left === null ? '#2b303a' : urgent ? '#e5484d' : (left <= 15 || warn) ? '#e0a231' : '#3fb950';
    const rateT = S.est && S.est.rate ? `${(S.est.rate * 60).toFixed(1)}%/min` : atZero ? '—' : 'measuring…';
    const curveT = (L.LABEL[S.cur ? S.cur.key : S.key] || S.key) + (S.est && S.est.curved ? ' · bending' : '');
    const alarmsT = `${MARKS.map(m => S.thr[m].toFixed(1)).join(' / ')} s` + (S.calib ? ` · ${S.calib.n} cycles${S.learning ? ' ⟳' : ''}` : '');
    const lr = S.lastResult;
    const lastT = lr ? lr.res.map(r => `${r.m}s ${describeErr(r.err)}`).join(' · ') : 'none scored yet';
    // cost
    const resetT = S.resetAt ? fmtLong((S.resetAt - t) / 1000) : '…';
    const creditsT = S.credits !== null ? `${Math.round(S.credits).toLocaleString()} · ${money(S.credits * CREDIT_PRICE)}` + (S.econ.cpm ? ` · burns ${Math.round(S.econ.cpm)}/min (${money(S.econ.cpm * 60 * CREDIT_PRICE)}/h)` : '') : '…';
    const D = S.day || {};
    const todayT = `${D.resets || 0} reset${D.resets === 1 ? '' : 's'}${D.resets ? ` (${money(D.resets * RESET_PRICE)})` : ''} · stall ${fmtDur((D.stallMs || 0) / 1000)}` + (fShare !== null && fShare !== undefined ? ` · ${Math.round(fShare * 100)}% fast` : '');
    let valueT = 'measuring…', hintT = '';
    if (S.econ.resetValueCredits) {
      const v = S.econ.resetValueCredits, usd = v * CREDIT_PRICE;
      valueT = `100% ≈ ${Math.round(v).toLocaleString()} credits ≈ ${money(usd)}${S.econ.measured ? '' : ' (provisional)'}`;
      hintT = (usd < RESET_PRICE ? `At this workload, running on credits is ${Math.round((1 - usd / RESET_PRICE) * 100)}% cheaper than a $${RESET_PRICE} reset.` : `At this workload a $${RESET_PRICE} reset buys ${(usd / RESET_PRICE).toFixed(1)}× the work your money buys on credits.`) + (S.econ.measured ? ` Measured over ${S.econ.n} run-out${S.econ.n === 1 ? '' : 's'}.` : ' Provisional until a run-out has been measured end to end.');
    } else if (S.econ.ppm && !S.econ.cpm) hintT = 'Credits-vs-reset needs one stretch of work at 0% on credits to measure the credit burn.';
    if (S.resetAt && S.resetAt - t < 2 * 3600e3 && !atZero) hintT = `The free weekly reset is only ${fmtLong((S.resetAt - t) / 1000)} away — don't pay $${RESET_PRICE} for one now.`;
    if (fShare !== null && fShare !== undefined && fShare > 0.5 && !hintT) hintT = `${Math.round(fShare * 100)}% of today's burn is fast mode, which drains the allowance ~2.5× faster than standard.`;
    const flash = t < flashT;
    const key = [bigT, cdT, etaLT, etaRT, color, rateT, curveT, alarmsT, lastT, resetT, creditsT, todayT, valueT, hintT, note, flash, Object.keys(S.fired || {}).join(), S.silenced, logL.length, logL[0], prefs.sound, actx && actx.state, upd].join('|');
    if (key === lastRenderKey) return;
    lastRenderKey = key;
    for (const p of panels) {
      p.big.textContent = bigT; p.big.style.color = atZero ? '#ff8589' : '#e7e9ee';
      p.countdown.textContent = cdT; p.countdown.style.color = color;
      p.etaL.textContent = etaLT; p.etaR.textContent = etaRT;
      p.fill.style.width = `${left === null ? 0 : Math.max(0, Math.min(100, left))}%`; p.fill.style.background = color;
      for (const pip of p.pips) { const f = S.fired[pip._k]; pip._d.style.background = f ? (pip._k === 'backstop' ? '#e5484d' : pip._k === 'headsup' ? '#8b93a1' : '#e0a231') : '#2b303a'; pip.style.color = f ? '#e7e9ee' : '#9aa1ae'; pip.style.borderColor = f ? '#3a4150' : '#262a33'; }
      p.bSilence.style.display = MARKS.some(m => S.fired[m]) || S.fired.backstop ? (S.silenced || atZero ? 'none' : '') : 'none';
      p.sBurn.textContent = rateT; p.sCurve.textContent = curveT; p.sAlarms.textContent = alarmsT; p.sLast.textContent = lastT;
      p.cReset.textContent = resetT; p.cCredits.textContent = creditsT; p.cToday.textContent = todayT; p.cValue.textContent = valueT;
      p.hint.textContent = hintT; p.hint.style.display = hintT ? '' : 'none';
      p.note.textContent = note; p.note.style.display = note ? '' : 'none';
      p.bSound.textContent = prefs.sound ? (actx && actx.state === 'running' ? 'Sound on' : 'Enable sound') : 'Sound off';
      p.bUpd.style.display = upd ? '' : 'none'; p.bUpd.textContent = upd ? `Update to ${upd}` : 'Update';
      p.dot.style.background = live ? '#8b93a1' : statusNote ? '#e0a231' : '#3fb950';
      p.root.style.borderColor = flash ? '#e5484d' : '#262a33';
      p.root.style.boxShadow = flash ? '0 0 0 3px rgba(229,72,77,.35), 0 12px 40px rgba(0,0,0,.55)' : (p.root.dataset.pip ? 'none' : '0 12px 40px rgba(0,0,0,.55)');
      if (p.logBox.dataset.n !== String(logL.length) || p.logBox.dataset.top !== logL[0]) {
        p.logBox.textContent = logL.slice(0, 14).join('\n'); p.logBox.dataset.n = String(logL.length); p.logBox.dataset.top = logL[0] || '';
      }
    }
  }

  // ---- Usage API ----
  let token = null, tokenAt = 0;
  async function getToken(force) {
    if (!force && token && Date.now() - tokenAt < 10 * 60e3) return token;
    const r = await fetch('/api/auth/session', { credentials: 'include' });
    if (!r.ok) throw new Error(`session ${r.status}`);
    const j = await r.json();
    if (!j || !j.accessToken) throw new Error('not signed in');
    token = j.accessToken; tokenAt = Date.now();
    return token;
  }
  async function apiGet(path) {
    for (let attempt = 0; attempt < 2; attempt++) {
      const tok = await getToken(attempt > 0);
      const r = await fetch(path, { credentials: 'include', headers: { Authorization: `Bearer ${tok}` } });
      if (r.status === 401 || r.status === 403) { token = null; continue; }
      if (!r.ok) throw new Error(`API ${r.status}`);
      return r.json();
    }
    throw new Error('not authorized');
  }
  async function fetchUsage() {
    const j = await apiGet('/backend-api/wham/usage');
    const w = j && j.rate_limit && j.rate_limit.primary_window;
    if (!w || typeof w.used_percent !== 'number') throw new Error('usage API sent no %');
    let used = Math.max(0, Math.min(100, Math.floor(w.used_percent + 1e-9)));
    if (j.rate_limit.limit_reached) used = 100;
    const credits = j.credits && j.credits.balance != null ? parseFloat(j.credits.balance) : undefined;
    const resetAt = w.reset_at ? w.reset_at * 1000 : (w.reset_after_seconds ? Date.now() + w.reset_after_seconds * 1000 : null);
    return { used, credits, resetAt };
  }
  // share of today's allowance burn that went to fast mode (the daily breakdown is in % of the allowance)
  async function fetchFastShare() {
    const d = new Date(), pad = n => String(n).padStart(2, '0');
    const utc = x => `${x.getUTCFullYear()}-${pad(x.getUTCMonth() + 1)}-${pad(x.getUTCDate())}`;
    const y = new Date(d.getTime() - 864e5);
    const j = await apiGet(`/backend-api/wham/usage/daily-token-usage-breakdown?start_date=${utc(y)}&end_date=${utc(d)}&group_by=day`);
    const days = (j && j.data) || [];
    const last = days[days.length - 1];
    if (!last || !last.models) return null;
    let fast = 0, all = 0;
    for (const m of last.models) { all += m.credits || 0; if (/fast/i.test(m.speed)) fast += m.credits || 0; }
    return all > 0.05 ? fast / all : null;
  }

  // ---- Loop: a 250 ms clock from a Worker keeps running while the tab is in the background ----
  let running = false, inFlight = false, nextPoll = 0, failures = 0, stopClock = null, leaderAt = 0, mounted = null, nextShare = 0, nextUpdateCheck = 0;
  function amLeader(t) {
    if (t - leaderAt < 1000) return amLeader.last;
    leaderAt = t;
    const cur = ls.get(K.leader, null);
    const ok = !cur || cur.id === TAB || t - cur.ts > 4000;
    if (ok) ls.set(K.leader, { id: TAB, ts: t });
    return (amLeader.last = ok);
  }
  async function poll(t) {
    inFlight = true;
    try {
      const u = await fetchUsage();
      failures = 0; statusNote = '';
      core.poll(Date.now(), u.used, { credits: u.credits, resetAt: u.resetAt });
    } catch (e) {
      failures++;
      statusNote = `can't read usage (${e.message}); retrying`;
    } finally {
      inFlight = false;
      const S = core.state();
      const fast = S.est && S.est.eta < FAST_WHEN_S;
      nextPoll = Date.now() + (failures ? Math.min(30000, 3000 * failures) : fast ? 1000 : SLOW_POLL_S * 1000);
    }
    if (t >= nextShare) { nextShare = t + 120000; fetchFastShare().then(v => { if (v !== null) fastShare = v; }).catch(() => {}); }
    if (t >= nextUpdateCheck) { nextUpdateCheck = t + 10 * 60000; checkForUpdate(); }
  }
  function onClock() {
    const t = Date.now();
    const here = ROUTE.test(location.pathname);
    if (!here) { if (mounted) unmount(); return; }
    isLeader = amLeader(t);
    if (!mounted) mount();
    if (!isLeader) { render(); return; }
    if (!inFlight && t >= nextPoll) poll(t);
    core.tick(t);
    if (t - silenceCheckedAt > 1000) { silenceCheckedAt = t; const sl = ls.get(SILENCE, 0); if (sl && sl > silenceSeen) { silenceSeen = sl; core.silence(); } }
    render();
  }
  let silenceCheckedAt = 0, silenceSeen = Date.now();
  function onFirstClick(e) {
    unlockAudio();
    if (AUTO_POPOUT && !pipWin && ROUTE.test(location.pathname) && !(mounted && mounted.root.contains(e.target))) openPip();
  }
  function mount() {
    mounted = buildPanel(document, false);
    document.body.append(mounted.root);
    document.addEventListener('pointerdown', onFirstClick, true);
    render();
  }
  function unmount() {
    document.removeEventListener('pointerdown', onFirstClick, true);
    if (mounted) { mounted.root.remove(); const i = panels.indexOf(mounted); if (i >= 0) panels.splice(i, 1); }
    mounted = null;
    if (pipWin) { try { pipWin.close(); } catch (e) {} pipWin = null; }
  }
  function startClock() {
    try {
      const url = URL.createObjectURL(new Blob(['setInterval(() => postMessage(0), 250);'], { type: 'text/javascript' }));
      const w = new W.Worker(url);
      w.onmessage = onClock;
      return () => { w.terminate(); URL.revokeObjectURL(url); };
    } catch (e) {
      const id = setInterval(onClock, 250);
      return () => clearInterval(id);
    }
  }
  stopClock = startClock();
  running = true;
  W.__usageMonitor2Stop = () => { running = false; if (stopClock) stopClock(); unmount(); };
  W.__usageMonitor2 = { version: VERSION, exportHistory, openPip, state: () => core.state() };
})();
