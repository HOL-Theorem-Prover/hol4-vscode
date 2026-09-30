// An error in the goals pane is a banner, not a replacement.
//
// The pane used to render `error` and return, so the goals the server
// sent alongside it were never displayed.  That threw away the one
// thing the reader wanted: a `>-` branch that proves nothing reports
// the goal it left undischarged, and hol-mode has always shown both.
//
// `stateBody` never touches `this`, so it can be driven straight off
// the prototype with no extension host.  Run via `npm run test:offline`.
const Module = require('module');
const path = require('path');
const REPO = path.join(__dirname, '..', '..');

// goalsView.ts imports vscode, and through lspClient pulls in
// vscode-languageclient, which subclasses things out of it.  A proxy
// handing back a stable class for any property is enough for all of
// that to load; nothing below calls into it.
const stubbed = new Map();
const vscodeStub = new Proxy({}, {
  get(_t, key) {
    if (key === '__esModule') return false;
    if (!stubbed.has(key)) stubbed.set(key, class Stub {});
    return stubbed.get(key);
  },
  has() { return true; },
});
const origLoad = Module._load;
Module._load = function (request, ...rest) {
  if (request === 'vscode') return vscodeStub;
  return origLoad.call(this, request, ...rest);
};

const { GoalsView } = require(path.join(REPO, 'out', 'goalsView.js'));
const body = (reply) => GoalsView.prototype.stateBody.call(null, reply);

let failed = 0;
function check(what, ok, got) {
  if (ok) { console.log('  ok   ' + what); }
  else { failed++; console.log('  FAIL ' + what + '  got: ' + JSON.stringify(got)); }
}

console.log('goals pane: an error does not replace the state');

const GOAL = { goal: '0 = 0', asms: [] };

// --- the regression -------------------------------------------------
const both = body({ error: '`>-` branch did not prove its goal',
                    goals: [GOAL] });
check('goals are still rendered when an error is present',
      both.includes('0 = 0'), both);

const prettyErr = body({ error: 'nope', pretty: 'PRETTY' });
check('and so is `pretty`', prettyErr.includes('PRETTY'), prettyErr);

// --- an error with nothing to show stands alone ---------------------
check('an error with no state gives an empty body',
      body({ error: 'walker timed out', goals: [] }) === '',
      body({ error: 'walker timed out', goals: [] }));
check('while no error and no goals still says so',
      body({ goals: [] }).includes('No open goals.'), body({ goals: [] }));

// --- precedence is unchanged ----------------------------------------
const segs = body({ segments: [{ text: 'SEGMENT' }], pretty: 'PRETTY',
                    goals: [GOAL] });
check('segments still win over pretty and goals',
      segs.includes('SEGMENT') && !segs.includes('PRETTY')
        && !segs.includes('0 = 0'), segs);
const pretty = body({ pretty: 'PRETTY', goals: [GOAL] });
check('pretty still wins over goals',
      pretty.includes('PRETTY') && !pretty.includes('0 = 0'), pretty);

console.log(failed === 0 ? '\nall checks passed'
                         : `\n${failed} check(s) failed`);
process.exit(failed === 0 ? 0 : 1);
