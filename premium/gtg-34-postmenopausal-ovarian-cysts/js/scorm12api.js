/* SCORM 1.2 run-time wrapper.

   Finds the LMS API adapter, then exposes the small set of calls the reader
   uses. Every call is guarded, so the course still runs when it is opened
   outside an LMS, on a browser that blocks cross-frame access, or in an LMS
   that only implements part of the data model.

   Written in ES5 with no dependencies for the same reason as viewer.js: it
   has to run in whatever browser the learner turns up with. */

var SCORM = (function () {

  var API = null;
  var initialised = false;
  var startTime = null;
  var finished = false;
  var completed = false;
  var interactions = 0;
  var MAX_FIND_DEPTH = 500;

  function scanWindow(win) {
    var depth = 0;
    while (win && depth < MAX_FIND_DEPTH) {
      if (win.API) { return win.API; }
      if (win.parent === win) { break; }
      win = win.parent;
      depth++;
    }
    return null;
  }

  function findAPI() {
    var found = null;
    try { found = scanWindow(window); } catch (e) { /* cross-origin */ }
    if (!found && window.opener) {
      try { found = scanWindow(window.opener); } catch (e) { /* cross-origin opener */ }
    }
    if (!found && window.top !== window) {
      try { found = scanWindow(window.top); } catch (e) { /* cross-origin top */ }
    }
    return found;
  }

  function twoDigits(n) { return (n < 10 ? '0' : '') + n; }

  /* SCORM 1.2 CMITimespan: HHHH:MM:SS.SS */
  function toTimespan(ms) {
    var total = Math.max(0, Math.floor(ms / 10)) / 100;
    var hours = Math.floor(total / 3600);
    var minutes = Math.floor((total - hours * 3600) / 60);
    var seconds = total - hours * 3600 - minutes * 60;
    return twoDigits(hours) + ':' + twoDigits(minutes) + ':' +
           (seconds < 10 ? '0' : '') + seconds.toFixed(2);
  }

  function set(key, value) {
    if (!initialised) { return false; }
    try { return API.LMSSetValue(key, String(value)) === 'true'; }
    catch (e) { return false; }
  }

  function get(key) {
    if (!initialised) { return ''; }
    /* Some LMSs (TalentLMS among them) return numbers or other non-string
       values from LMSGetValue; SCORM says string, so coerce here once and
       every caller can safely use string methods. */
    try {
      var v = API.LMSGetValue(key);
      return (v === null || v === undefined) ? '' : String(v);
    } catch (e) { return ''; }
  }

  /* Some LMSs put the SCO into review or browse mode, or mark the attempt as
     not for credit. Writing a score in those states is wrong and some LMSs
     reject it outright, so outcomes are held back. */
  function scorable() {
    if (!initialised) { return false; }
    var mode = get('cmi.core.lesson_mode');
    if (mode === 'review' || mode === 'browse') { return false; }
    if (get('cmi.core.credit') === 'no-credit') { return false; }
    return true;
  }

  return {

    connected: function () { return initialised; },

    init: function () {
      if (initialised) { return true; }
      API = findAPI();
      if (!API) { return false; }
      try { initialised = API.LMSInitialize('') === 'true'; }
      catch (e) { initialised = false; }
      if (!initialised) { return false; }
      startTime = new Date();

      var status = get('cmi.core.lesson_status');
      if (!status || status === 'not attempted' || status === '') {
        set('cmi.core.lesson_status', 'incomplete');
      }
      var count = parseInt(get('cmi.interactions._count'), 10);
      interactions = isNaN(count) ? 0 : count;
      this.commit();
      return true;
    },

    mode: function () { return get('cmi.core.lesson_mode') || 'normal'; },

    learnerName: function () {
      var raw = get('cmi.core.student_name');           /* usually "Last, First" */
      if (!raw) { return ''; }
      var parts = raw.split(',');
      return parts.length === 2 ? (parts[1].replace(/^\s+|\s+$/g, '') + ' ' +
                                   parts[0].replace(/^\s+|\s+$/g, '')) : raw;
    },

    /* cmi.core.student_id is the only identifier SCORM 1.2 exposes besides
       the name; most LMSs (TalentLMS included) put the username or the login
       e-mail in it. There is no separate e-mail field in SCORM 1.2. */
    learnerId: function () { return get('cmi.core.student_id') || ''; },

    /* cmi.core.student_id is the only identifier SCORM 1.2 exposes besides
       the name; most LMSs (TalentLMS included) put the username or login
       e-mail in it. SCORM 1.2 has no separate e-mail field. */
    learnerId: function () { return get('cmi.core.student_id') || ''; },

    /* Reading-only courses report completion; there is no score to give. */
    complete: function () {
      if (!initialised || completed || !scorable()) { return; }
      completed = true;
      set('cmi.core.lesson_status', 'completed');
      this.commit();
    },

    setScore: function (raw, min, max) {
      if (!scorable()) { return; }
      set('cmi.core.score.min', min === undefined ? 0 : min);
      set('cmi.core.score.max', max === undefined ? 100 : max);
      set('cmi.core.score.raw', Math.round(raw));
    },

    setStatus: function (status) {
      if (!scorable()) { return; }
      set('cmi.core.lesson_status', status);
      this.commit();
    },

    /* One row per answered question, so the LMS report shows which item was
       missed rather than only the total. */
    interaction: function (id, type, correct, response, result, latencySeconds) {
      if (!scorable()) { return; }
      var n = interactions++;
      var base = 'cmi.interactions.' + n + '.';
      set(base + 'id', String(id).slice(0, 255));
      set(base + 'type', type || 'choice');
      set(base + 'student_response', response);
      set(base + 'correct_responses.0.pattern', correct);
      set(base + 'result', result === 'correct' ? 'correct' : 'wrong');
      set(base + 'weighting', 1);
      if (latencySeconds) { set(base + 'latency', toTimespan(latencySeconds * 1000)); }
      var d = new Date();
      set(base + 'time', twoDigits(d.getHours()) + ':' + twoDigits(d.getMinutes()) + ':' +
                         twoDigits(d.getSeconds()));
      this.commit();
    },

    isCompleted: function () {
      var s = get('cmi.core.lesson_status');
      return s === 'completed' || s === 'passed';
    },

    setProgress: function (suspendData) {
      if (!initialised) { return; }
      set('cmi.suspend_data', suspendData);
      set('cmi.core.session_time', toTimespan(new Date() - startTime));
      this.commit();
    },

    getProgress: function () { return get('cmi.suspend_data'); },

    close: function () {
      if (!initialised || finished) { return; }
      set('cmi.core.session_time', toTimespan(new Date() - startTime));
      set('cmi.core.exit', '');
      this.commit();
    },

    commit: function () {
      if (!initialised) { return; }
      try { API.LMSCommit(''); } catch (e) { /* ignore */ }
    },

    terminate: function () {
      if (!initialised || finished) { return; }
      finished = true;
      try { API.LMSFinish(''); } catch (e) { /* ignore */ }
    }
  };
})();

window.addEventListener('beforeunload', function () {
  SCORM.close();
  SCORM.terminate();
});
