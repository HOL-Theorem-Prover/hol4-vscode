// A small TextMate-subset tokenizer: enough of the model to answer
// "what scope does this token actually get?" for hol4-grammar.json,
// which uses only begin/end/match/captures/patterns/include/name.
'use strict';
const fs = require('fs');

function compile(src) { return new RegExp(src, 'dg'); }

function resolvePatterns(grammar, patterns) {
  const out = [];
  for (const p of patterns || []) {
    if (p.include) {
      const key = p.include.replace(/^#/, '');
      const r = grammar.repository[key];
      if (!r) { continue; }
      if (r.patterns && !r.begin && !r.match) { out.push(...resolvePatterns(grammar, r.patterns)); }
      else { out.push(r); }
    } else { out.push(p); }
  }
  return out;
}

// TextMate substitutes \1, \2 ... in an `end` pattern with the text the
// corresponding group of the `begin` match captured.  `term-quote-ticks`
// relies on it to pair n backticks with n backticks.
function substituteBackrefs(src, beginMatch) {
  if (!beginMatch) { return src; }
  return src.replace(/\\(\d)/g, (whole, d) => {
    const g = beginMatch[Number(d)];
    return g === undefined ? whole : g.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
  });
}

function execAt(re, line, pos) {
  re.lastIndex = pos;
  const m = re.exec(line);
  return m;
}

function paint(scopes, from, to, name) {
  if (!name) { return; }
  for (const n of name.split(/\s+/)) {
    for (let i = from; i < to; i++) {
      if (scopes[i]) { scopes[i] = scopes[i].concat([n]); }
    }
  }
}

function applyCaptures(scopes, m, caps, base) {
  if (base) { paint(scopes, m.index, m.index + m[0].length, base); }
  if (!caps) { return; }
  const ind = m.indices || [];
  for (const k of Object.keys(caps)) {
    const i = Number(k);
    const span = ind[i];
    if (!span) { continue; }
    paint(scopes, span[0], span[1], caps[k].name);
  }
}

/** Tokenize `text`, returning for each line an array of scope-lists, one per character. */
function tokenize(grammar, text) {
  // vscode-textmate hands each line to the tokenizer *with* its newline.
  // That matters: SML's string continuation `"...\` relies on the escape
  // rule `\\[\t-\r ]` matching the backslash-newline pair.
  const lines = text.split(/(?<=\n)/);
  const stack = [{ rule: grammar, scopes: [grammar.scopeName], end: null }];
  const result = [];
  const stacks = [];
  for (const k of Object.keys(grammar.repository)) { grammar.repository[k].__name = k; }

  for (const line of lines) {
    const scopes = new Array(line.length);
    for (let i = 0; i < line.length; i++) { scopes[i] = stack[stack.length - 1].scopes.slice(); }
    let pos = 0;
    let guard = null;
    let steps = 0;

    while (pos <= line.length && steps++ < 2000) {
      const top = stack[stack.length - 1];
      const cands = [];
      if (top.end) {
        const m = execAt(compile(substituteBackrefs(top.end, top.beginMatch)), line, pos);
        if (m) { cands.push({ kind: 'end', m }); }
      }
      for (const r of resolvePatterns(grammar, top.rule.patterns)) {
        if (guard && guard.rule === r && guard.pos === pos) { continue; }
        const src = r.match || r.begin;
        if (!src) { continue; }
        const m = execAt(compile(src), line, pos);
        if (m) { cands.push({ kind: r.match ? 'match' : 'begin', m, rule: r }); }
      }
      if (cands.length === 0) { break; }
      // Earliest wins; a tie goes to the end pattern, as TextMate does
      // unless applyEndPatternLast is set (this grammar never sets it).
      cands.sort((a, b) => (a.m.index - b.m.index) ||
                           ((a.kind === 'end' ? 0 : 1) - (b.kind === 'end' ? 0 : 1)));
      const c = cands[0];
      const m = c.m;

      if (c.kind === 'end') {
        applyCaptures(scopes, m, top.rule.endCaptures || top.rule.captures, null);
        stack.pop();
        pos = m.index + (m[0].length || 0);
        if (m[0].length === 0) { guard = { rule: top.rule, pos }; } else { guard = null; }
        continue;
      }
      if (c.kind === 'match') {
        applyCaptures(scopes, m, c.rule.captures, c.rule.name);
        pos = m.index + (m[0].length || 1);
        guard = null;
        continue;
      }
      // begin
      applyCaptures(scopes, m, c.rule.beginCaptures || c.rule.captures, null);
      const inherited = stack[stack.length - 1].scopes;
      const pushed = c.rule.name ? inherited.concat([c.rule.name]) : inherited.slice();
      stack.push({ rule: c.rule, scopes: pushed, end: c.rule.end, beginMatch: m });
      pos = m.index + m[0].length;
      // Characters after a begin inherit the pushed scope.
      for (let i = pos; i < line.length; i++) { scopes[i] = pushed.slice(); }
      guard = m[0].length === 0 ? { rule: c.rule, pos } : null;
    }
    result.push(scopes);
    stacks.push(stack.map(f => f.rule.__name || (f.rule.begin ? f.rule.begin.slice(0, 28) : 'ROOT')));
  }
  return { lines, scopes: result, stacks };
}

/** The scope list on the first occurrence of `word` on line `lineNo`. */
function scopesOf(tok, lineNo, word) {
  const line = tok.lines[lineNo] || '';
  const i = line.indexOf(word);
  if (i === -1) { return null; }
  return tok.scopes[lineNo][i];
}

module.exports = { tokenize, scopesOf, load: (p) => JSON.parse(fs.readFileSync(p, 'utf8')) };
