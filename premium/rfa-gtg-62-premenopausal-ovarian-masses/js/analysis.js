/* RFA Tutors performance analysis.

   Runs entirely on the learner's device. There is no network call, no API
   key and nothing to bill: a SCORM package sits inside somebody else's LMS,
   often behind a corporate proxy, and a course that phones home is a course
   that breaks. Everything below is arithmetic over the attempt the learner
   has just made.

   What it is doing is what a tutor does with a marked paper: group the
   questions by module, look at where the marks were lost, look at how long
   each one took, and separate "did not know it" from "knew it and rushed",
   because those two need different work.

   ES5 only, no modules — same constraints as the viewer.

   RFA_ANALYSIS.build({
     questions: [{n, ans, correct, ms, flag, label, page}, ...],
     modules:   [{from, to, name}, ...],     // may be empty
     mastery:   80,
     examSeconds: 900,                       // time allowed (target); 0 if no stopwatch
     elapsedSeconds: 640,                    // stopwatch reading, may exceed examSeconds
     timeUp: false
   }) -> report object, rendered by viewer.js
*/

(function () {
'use strict';

/* A question answered faster than this was not really read. */
var FLOOR_FAST_MS = 9000;
/* Below 40% of the learner's own median pace counts as rushed, above 200%
   as laboured. Relative to the learner, not to an absolute clock, because a
   slow careful candidate and a fast one both deserve a fair read. */
var FAST_RATIO = 0.4;
var SLOW_RATIO = 2.0;

var BAND_STRONG = 80;
var BAND_OK = 60;

function median(nums) {
  if (!nums.length) { return 0; }
  var a = nums.slice().sort(function (x, y) { return x - y; });
  var mid = Math.floor(a.length / 2);
  return a.length % 2 ? a[mid] : Math.round((a[mid - 1] + a[mid]) / 2);
}

function pctOf(part, whole) { return whole ? Math.round((part / whole) * 100) : 0; }

function band(p) { return p >= BAND_STRONG ? 'strong' : (p >= BAND_OK ? 'fair' : 'weak'); }

function mmss(ms) {
  var s = Math.max(0, Math.round(ms / 1000));
  var m = Math.floor(s / 60);
  s = s % 60;
  return m + ':' + (s < 10 ? '0' : '') + s;
}

function plural(n, one, many) { return n + ' ' + (n === 1 ? one : (many || one + 's')); }

function listQ(ns, limit) {
  var cap = limit || 8;
  var shown = ns.slice(0, cap);
  var s = 'Q' + shown.join(', Q');
  if (ns.length > cap) { s += ' and ' + (ns.length - cap) + ' more'; }
  return s;
}

/* --------------------------------------------------------------- modules */

function moduleFor(n, ranges) {
  for (var i = 0; i < ranges.length; i++) {
    if (n >= ranges[i].from && n <= ranges[i].to) { return ranges[i].name; }
  }
  return null;
}

function groupByModule(qs, ranges) {
  var order = [], byName = {}, i, name, g;

  function bucket(nm) {
    if (!byName[nm]) {
      byName[nm] = {
        name: nm, total: 0, answered: 0, right: 0, wrong: 0, unanswered: 0,
        ms: 0, timed: 0, wrongQs: [], missedQs: [], flagQs: [], pct: 0, avgMs: 0, band: 'weak'
      };
      order.push(byName[nm]);
    }
    return byName[nm];
  }

  /* Declared ranges come first and in the order they were declared, so the
     report reads in the order the paper was written even if a module has no
     questions answered yet. */
  for (i = 0; i < ranges.length; i++) { bucket(ranges[i].name); }

  for (i = 0; i < qs.length; i++) {
    var q = qs[i];
    name = moduleFor(q.n, ranges) || (ranges.length ? 'Unassigned' : 'Whole paper');
    g = bucket(name);
    g.total++;
    if (q.flag) { g.flagQs.push(q.n); }
    if (!q.ans) { g.unanswered++; g.missedQs.push(q.n); continue; }
    g.answered++;
    if (q.ms > 0) { g.ms += q.ms; g.timed++; }
    if (q.ans === q.correct) { g.right++; }
    else { g.wrong++; g.wrongQs.push(q.n); g.missedQs.push(q.n); }
  }

  var out = [];
  for (i = 0; i < order.length; i++) {
    g = order[i];
    if (!g.total) { continue; }             /* a declared range with no questions */
    g.pct = pctOf(g.right, g.answered);
    g.coverage = pctOf(g.answered, g.total);
    g.avgMs = g.timed ? Math.round(g.ms / g.timed) : 0;
    g.band = g.answered ? band(g.pct) : 'none';
    out.push(g);
  }
  return out;
}

/* Weakest first, but a module nobody has attempted cannot be called weak —
   it sorts to the end with its own wording. */
function rankModules(mods) {
  return mods.slice().sort(function (a, b) {
    if (!a.answered !== !b.answered) { return a.answered ? -1 : 1; }
    if (a.pct !== b.pct) { return a.pct - b.pct; }
    return b.wrong - a.wrong;
  });
}

/* ------------------------------------------------------------- patterns */

function timingPatterns(qs, med) {
  var fast = Math.max(FLOOR_FAST_MS, Math.round(med * FAST_RATIO));
  var slow = Math.round(med * SLOW_RATIO);
  var out = {
    rushedWrong: [], slowWrong: [], slowRight: [], quickRight: [],
    fastMs: fast, slowMs: slow
  };
  for (var i = 0; i < qs.length; i++) {
    var q = qs[i];
    if (!q.ans || !q.ms) { continue; }
    var right = q.ans === q.correct;
    if (q.ms <= fast && !right) { out.rushedWrong.push(q.n); }
    else if (med && q.ms >= slow && !right) { out.slowWrong.push(q.n); }
    else if (med && q.ms >= slow && right) { out.slowRight.push(q.n); }
    else if (q.ms <= fast && right) { out.quickRight.push(q.n); }
  }
  return out;
}

/* Did accuracy hold up across the paper? A drop in the back half is usually
   the clock or fatigue rather than the syllabus, and it is worth separating
   because the fix is different. */
function halves(qs) {
  var answered = [];
  for (var i = 0; i < qs.length; i++) { if (qs[i].ans) { answered.push(qs[i]); } }
  if (answered.length < 6) { return null; }
  var cut = Math.floor(answered.length / 2);
  function score(list) {
    var r = 0;
    for (var k = 0; k < list.length; k++) { if (list[k].ans === list[k].correct) { r++; } }
    return { n: list.length, right: r, pct: pctOf(r, list.length) };
  }
  var a = score(answered.slice(0, cut));
  var b = score(answered.slice(cut));
  return { first: a, second: b, drop: a.pct - b.pct };
}

function flagStats(qs) {
  var out = { rightFlagged: [], wrongFlagged: [], total: 0 };
  for (var i = 0; i < qs.length; i++) {
    var q = qs[i];
    if (!q.flag) { continue; }
    out.total++;
    if (!q.ans) { continue; }
    if (q.ans === q.correct) { out.rightFlagged.push(q.n); }
    else { out.wrongFlagged.push(q.n); }
  }
  return out;
}

/* --------------------------------------------------------- the write-up */

/* Findings are ordered by what would move the score most, not by the order
   they were computed. A learner reads three or four lines; they should be
   the three or four that matter. */
function findings(r) {
  var f = [];
  var ranked = r.ranked, i, m;

  if (r.unanswered) {
    f.push({
      level: r.unanswered > r.total * 0.2 ? 'weak' : 'watch',
      title: plural(r.unanswered, 'question') + ' left unanswered',
      text: (r.timeUp
        ? 'You ran out of time before reaching ' + listQ(r.unansweredQs) + '. '
        : listQ(r.unansweredQs) + ' were never attempted. ') +
        'Unanswered questions score the same as wrong ones, so a considered guess is always worth making.'
    });
  }

  var weakMods = [];
  for (i = 0; i < ranked.length; i++) {
    m = ranked[i];
    if (m.answered >= 2 && m.pct < BAND_OK) { weakMods.push(m); }
  }
  if (weakMods.length) {
    var w = weakMods[0];
    f.push({
      level: 'weak',
      title: w.name + ' is your weakest area — ' + w.pct + '%',
      text: w.right + ' of ' + w.answered + ' correct' +
        (w.wrongQs.length ? ', missing ' + listQ(w.wrongQs) + '. ' : '. ') +
        (weakMods.length > 1
          ? 'The same is true of ' + namesOf(weakMods.slice(1, 3)) + '. Work through these before revisiting anything you already score well in.'
          : 'This is where revision time will buy you the most marks.')
    });
  }

  var strong = [];
  for (i = 0; i < ranked.length; i++) {
    m = ranked[i];
    if (m.answered >= 2 && m.pct >= BAND_STRONG && !m.unanswered) { strong.push(m); }
  }
  if (strong.length) {
    var s = strong[strong.length - 1];
    f.push({
      level: 'good',
      title: 'Secure in ' + namesOf(strong.slice(-3).reverse()),
      text: s.name + ' came out at ' + s.pct + '% (' + s.right + '/' + s.answered + ')' +
        (strong.length > 1
          ? ', and the others held up as well. Keep these ticking over with light recall rather than fresh reading.'
          : '. Keep it ticking over with light recall rather than fresh reading.')
    });
  }

  var p = r.patterns;
  if (p.rushedWrong.length >= 2) {
    f.push({
      level: 'weak',
      title: plural(p.rushedWrong.length, 'question') + ' lost to rushing',
      text: listQ(p.rushedWrong) + ' were answered in under ' + mmss(p.fastMs) +
        ' and came out wrong — well below your own pace of ' + mmss(r.medianMs) + ' a question. ' +
        'These are the cheapest marks on the paper to win back: read the stem twice and rule out two options before choosing.'
    });
  }
  if (p.slowWrong.length >= 2) {
    f.push({
      level: 'weak',
      title: plural(p.slowWrong.length, 'question') + ' laboured over and still missed',
      text: listQ(p.slowWrong) + ' each took over ' + mmss(p.slowMs) + ' and were still wrong. ' +
        'Slow and wrong is the signature of a gap in the underlying concept rather than a careless slip — ' +
        'go back to the source material for these, not to more questions.'
    });
  }
  if (p.slowRight.length >= 3) {
    f.push({
      level: 'watch',
      title: 'You know it, but slowly',
      text: listQ(p.slowRight) + ' were right but took over ' + mmss(p.slowMs) + ' each. ' +
        'The knowledge is there; the recall is not yet automatic. Timed drilling fixes this, more reading does not.'
    });
  }

  if (r.halves && r.halves.drop >= 20 && r.halves.second.n >= 3) {
    f.push({
      level: 'watch',
      title: 'Your accuracy fell away in the second half',
      text: r.halves.first.pct + '% across the first ' + r.halves.first.n + ' answered, ' +
        r.halves.second.pct + '% across the last ' + r.halves.second.n + '. ' +
        'A fall that size usually means the clock or concentration, not the syllabus. ' +
        'Practise full papers in one sitting rather than in short bursts.'
    });
  } else if (r.halves && r.halves.drop <= -20 && r.halves.first.n >= 3) {
    f.push({
      level: 'watch',
      title: 'A slow start',
      text: 'You scored ' + r.halves.first.pct + '% early and ' + r.halves.second.pct + '% later. ' +
        'Settling-in errors are worth a warm-up set of a few questions before the paper that counts.'
    });
  }

  if (r.flags.rightFlagged.length >= 2) {
    f.push({
      level: 'watch',
      title: 'Right, but you were not sure',
      text: 'You flagged ' + listQ(r.flags.rightFlagged) + ' and still got them right. ' +
        'Those topics are half-secure — a light revision pass will turn a guess into a certainty before the exam does it for you.'
    });
  }

  if (r.examSeconds && r.elapsedSeconds > r.examSeconds * 1.05) {
    f.push({
      level: 'watch',
      title: 'Over the time allowed',
      text: 'You took ' + mmss(r.elapsedSeconds * 1000) + ' for a ' + mmss(r.examSeconds * 1000) + ' paper — ' +
        pctOf(r.elapsedSeconds - r.examSeconds, r.examSeconds) + '% over. In the exam that time does not exist, ' +
        'so practise the next set against the clock and move on from any question that runs past twice your typical pace.'
    });
  }

  if (r.examSeconds && r.elapsedSeconds >= 120) {
    var used = pctOf(r.elapsedSeconds, r.examSeconds);
    if (used >= 5 && used <= 60 && r.answered >= r.total * 0.8) {
      f.push({
        level: 'watch',
        title: 'You finished with time to spare',
        text: 'You used ' + used + '% of the allowance. If the score is not where you want it, ' +
          'the spare time is yours to spend on checking rather than on finishing early.'
      });
    }
  }

  if (!f.length) {
    f.push({
      level: 'good',
      title: 'A clean paper',
      text: 'Nothing here stands out as a weak area. Keep the pace and move on to a harder set.'
    });
  }
  return f;
}

function namesOf(mods) {
  var n = [];
  for (var i = 0; i < mods.length; i++) { n.push(mods[i].name); }
  if (n.length <= 1) { return n[0] || ''; }
  return n.slice(0, -1).join(', ') + ' and ' + n[n.length - 1];
}

/* A plan is only useful if it is short and in order. Three or four steps. */
function plan(r) {
  var steps = [], i, m;

  for (i = 0; i < r.ranked.length && steps.length < 3; i++) {
    m = r.ranked[i];
    if (!m.answered || m.pct >= BAND_OK) { continue; }
    steps.push({
      head: 'Revise ' + m.name,
      body: m.pct + '% (' + m.right + '/' + m.answered + ')' +
        (m.missedQs.length ? ' — start from ' + listQ(m.missedQs, 6) : '') + '.'
    });
  }

  if (r.patterns.rushedWrong.length >= 2) {
    steps.push({
      head: 'Slow down on the first read',
      body: 'Re-attempt ' + listQ(r.patterns.rushedWrong, 6) +
        ' with no clock. If you get them right second time, the gap is pace, not knowledge.'
    });
  }
  if (r.patterns.slowWrong.length >= 2) {
    steps.push({
      head: 'Go back to the source material',
      body: listQ(r.patterns.slowWrong, 6) + ' took the longest and were still missed — read the topic again before drilling it.'
    });
  }
  if (r.unanswered) {
    steps.push({
      head: 'Attempt every question',
      body: plural(r.unanswered, 'question') + ' scored nothing because nothing was entered. ' +
        'Leave your best guess on any question you cannot finish.'
    });
  }
  if (r.patterns.slowRight.length >= 3 && steps.length < 4) {
    steps.push({
      head: 'Drill for speed',
      body: 'Set a timer of ' + mmss(r.medianMs) + ' a question and re-run this paper.'
    });
  }
  if (!steps.length) {
    steps.push({
      head: 'Move up a level',
      body: 'This paper is no longer stretching you. Take a harder set or shorten the time allowance.'
    });
  }
  return steps.slice(0, 4);
}

function lede(r) {
  if (!r.answered) {
    return 'Nothing to analyse yet — answer a few questions and come back.';
  }
  var bits = [];
  bits.push('You scored ' + r.right + ' out of ' + r.total + ' (' + r.pct + '%)');
  if (r.mastery) { bits.push(r.pct >= r.mastery ? 'a pass at ' + r.mastery + '%' : 'below the ' + r.mastery + '% pass mark'); }
  var s = bits.join(', ') + '.';
  if (r.medianMs) { s += ' Your typical question took ' + mmss(r.medianMs) + '.'; }
  if (r.timeUp && r.examSeconds && r.elapsedSeconds > r.examSeconds) {
    s += ' You took ' + mmss(r.elapsedSeconds * 1000) + ' against ' + mmss(r.examSeconds * 1000) + ' allowed.';
  } else if (r.timeUp) { s += ' You reached the time allowed.'; }
  return s;
}

/* ------------------------------------------------------------------ api */

function build(opts) {
  var qs = [], i;
  var src = (opts && opts.questions) || [];
  for (i = 0; i < src.length; i++) { if (src[i] && src[i].correct) { qs.push(src[i]); } }

  var ranges = (opts && opts.modules) || [];
  var r = {
    total: qs.length, answered: 0, right: 0, wrong: 0, unanswered: 0,
    unansweredQs: [], wrongQs: [],
    mastery: (opts && opts.mastery) || 0,
    examSeconds: (opts && opts.examSeconds) || 0,
    elapsedSeconds: (opts && opts.elapsedSeconds) || 0,
    timeUp: !!(opts && opts.timeUp),
    hasModules: ranges.length > 0
  };

  var times = [], totalMs = 0;
  for (i = 0; i < qs.length; i++) {
    var q = qs[i];
    if (!q.ans) { r.unanswered++; r.unansweredQs.push(q.n); continue; }
    r.answered++;
    if (q.ans === q.correct) { r.right++; } else { r.wrong++; r.wrongQs.push(q.n); }
    if (q.ms > 0) { times.push(q.ms); totalMs += q.ms; }
  }
  r.pct = pctOf(r.right, r.total);
  r.accuracy = pctOf(r.right, r.answered);
  r.passed = r.mastery ? r.pct >= r.mastery : null;
  r.medianMs = median(times);
  r.avgMs = times.length ? Math.round(totalMs / times.length) : 0;
  r.totalMs = totalMs;

  r.modules = groupByModule(qs, ranges);
  r.ranked = rankModules(r.modules);
  r.patterns = timingPatterns(qs, r.medianMs);
  r.halves = halves(qs);
  r.flags = flagStats(qs);
  r.findings = findings(r);
  r.plan = plan(r);
  r.lede = lede(r);
  /* where "go to my weakest area" should land */
  r.focus = null;
  for (i = 0; i < r.ranked.length; i++) {
    if (r.ranked[i].answered && r.ranked[i].missedQs.length) { r.focus = r.ranked[i]; break; }
  }
  return r;
}

window.RFA_ANALYSIS = { build: build, mmss: mmss, band: band };

})();
