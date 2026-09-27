import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';

// Test the exact JavaScript embedded in the Lean widget, with a minimal hook and
// editor harness. This is a component-interaction test, not a browser screenshot.
const lean = readFileSync(new URL('../Macaulean/Verification/Panel.lean', import.meta.url), 'utf8');
const matches = [...lean.matchAll(/javascript\s*:=\s*r#"([\s\S]*?)"#/g)];
assert.equal(matches.length, 1, 'expected exactly one widget module');
const source = matches[0][1];
const executable = source
  .replace("import * as React from 'react';", '')
  .replace("import { EditorContext } from '@leanprover/infoview';", '')
  .replace('export default function IntentPanel', 'function IntentPanel');

function harness(editor = null) {
  let current;
  const React = {
    createElement(type, props, ...children) {
      return { type, props: props ?? {}, children: children.flat(Infinity).filter(x => x !== null && x !== undefined && x !== false) };
    },
    useContext() { return editor; },
    useState(initial) {
      const r = current, i = r.cursor++;
      if (!(i in r.slots)) r.slots[i] = initial;
      return [r.slots[i], value => { r.slots[i] = typeof value === 'function' ? value(r.slots[i]) : value; }];
    },
    useEffect(fn, deps) {
      const r = current, i = r.cursor++;
      const old = r.slots[i];
      if (!old || deps.some((d, j) => !Object.is(d, old[j]))) r.effects.push(fn);
      r.slots[i] = deps.slice();
    },
  };
  const module = new Function('React', 'EditorContext', executable + '\nreturn {IntentPanel,ContractCard};')(React, {});
  function runner(component) {
    const r = { slots: [], cursor: 0, effects: [] };
    return (props, effects = true) => {
      r.cursor = 0; r.effects = []; current = r;
      const view = component(props);
      if (effects) for (const fn of r.effects) fn();
      return view;
    };
  }
  return { module, runner };
}
function visit(node, predicate) {
  if (node && typeof node === 'object') {
    if (predicate(node)) return node;
    for (const child of node.children ?? []) { const found = visit(child, predicate); if (found) return found; }
  }
  return null;
}
function text(node) {
  if (node === null || node === undefined || node === false) return '';
  if (typeof node !== 'object') return String(node);
  return (node.children ?? []).map(text).join(' ');
}
function button(view, label) {
  const b = visit(view, n => n.type === 'button' && text(n) === label);
  assert.ok(b, 'missing button: ' + label); return b;
}
function proposal(overrides = {}) {
  return {
    title: 'Polynomial identity', digest: 'revision-A', status: 'Proposed - intent not approved',
    inputs: ['One polynomial'], guarantees: ['Equal coefficients'], limitations: ['No termination claim', 'No effect claim'],
    formal: 'Contracts.Statement polynomialIdentity fn state', target: 'IntentTargets.t_revisionA',
    version: 'v1', proofStatus: 'Unattempted', canApprove: true, approvalSource: '',
    approveCommand: '#m2_approve "f" polynomialIdentity "revision-A"\n',
    revokeCommand: '#m2_revoke "f" polynomialIdentity\n', inspectCommand: '#print IntentTargets.t_revisionA\n',
    ...overrides,
  };
}
function panelProps() {
  return {
    pos: {uri: 'file:///worksheet.lean', line: 1, character: 0},
    insertAt: {line: 20, character: 12}, theoryAxioms: [], theoryDigest: 'theory',
    entry: {id: 'binding-f', name: 'f', generation: 1, file: 'worksheet.lean',
      className: 'FunctionClosure', views: ['Lexical computation'], sourceText: 'f=p->p;',
      sourceNodes: [], callable: true, contracts: [],
      choices: [{name:'polynomialIdentity', description:'Reviewed deterministic description',
        command:'#m2_contract "f" polynomialIdentity\n'}]},
  };
}

test('review starts disabled and all exclusions are rendered', () => {
  const h = harness(), render = h.runner(h.module.ContractCard), writes = [];
  const p = proposal(), view = render({p, insert: s => writes.push(s)});
  assert.equal(button(view, 'Record approval in source').props.disabled, true);
  button(view, 'Record approval in source').props.onClick();
  assert.deepEqual(writes, []);
  for (const line of [...p.inputs, ...p.guarantees, ...p.limitations, p.proofStatus]) assert.ok(text(view).includes(line));
});

test('explicit review inserts only the frozen source attestation', () => {
  const h = harness(), render = h.runner(h.module.ContractCard), writes = [];
  const p = proposal(), copy = structuredClone(p), props = {p, insert: s => writes.push(s)};
  let view = render(props);
  visit(view, n => n.type === 'input').props.onChange({target:{checked:true}});
  view = render(props);
  assert.equal(button(view, 'Record approval in source').props.disabled, false);
  button(view, 'Record approval in source').props.onClick();
  assert.deepEqual(writes, [p.approveCommand]);
  assert.deepEqual(p, copy, 'client must not optimistically mark approval or proof success');
});

test('a new digest clears consent before effects or another paint', () => {
  const h = harness(), render = h.runner(h.module.ContractCard), writes = [];
  let p = proposal(), view = render({p, insert: s => writes.push(s)});
  visit(view, n => n.type === 'input').props.onChange({target:{checked:true}});
  p = proposal({digest:'revision-B', approveCommand:'NEW TARGET'});
  view = render({p, insert: s => writes.push(s)}, false);
  assert.equal(button(view, 'Record approval in source').props.disabled, true);
  button(view, 'Record approval in source').props.onClick();
  assert.deepEqual(writes, []);
});

test('stale or unavailable targets cannot be approved even by a forced callback', () => {
  for (const status of ['Stale', 'Unavailable']) {
    const h = harness(), render = h.runner(h.module.ContractCard), writes = [];
    const p = proposal({status, canApprove:false}), props = {p, insert:s=>writes.push(s)};
    let view = render(props);
    visit(view, n=>n.type==='input').props.onChange({target:{checked:true}});
    view = render(props);
    button(view,'Record approval in source').props.onClick();
    assert.deepEqual(writes, []);
  }
});

test('revoke and exact-target inspection remain explicit source actions', () => {
  const h = harness(), render = h.runner(h.module.ContractCard), writes = [];
  const p = proposal(), view = render({p, insert:s=>writes.push(s)});
  button(view,'Revoke in source').props.onClick();
  button(view,'Inspect exact Lean proposition').props.onClick();
  assert.deepEqual(writes,[p.revokeCommand,p.inspectCommand]);
});

test('proposal uses the command-tail anchor, not the cursor inside the function', async () => {
  const writes = [], editor = {api:{insertText:async (...args)=>writes.push(args)}};
  const h = harness(editor), render = h.runner(h.module.IntentPanel), props = panelProps();
  let view = render(props);
  assert.equal(button(view,'Propose contract in source').props.disabled,true);
  visit(view,n=>n.type==='select').props.onChange({target:{value:'polynomialIdentity'}});
  view = render(props);
  await button(view,'Propose contract in source').props.onClick();
  assert.deepEqual(writes, [[props.entry.choices[0].command, 'below', {
    textDocument:{uri:props.pos.uri}, position:props.insertAt}]]);
  view = render(props);
  assert.ok(text(view).includes('Status changes only after Lean re-elaborates it.'));
});

test('missing editor gives a copyable command rather than reporting approval', async () => {
  const h = harness(), render = h.runner(h.module.IntentPanel), props = panelProps();
  let view = render(props);
  visit(view,n=>n.type==='select').props.onChange({target:{value:'polynomialIdentity'}});
  view = render(props);
  await button(view,'Propose contract in source').props.onClick();
  view = render(props);
  assert.ok(text(view).includes('No document connection'));
  assert.ok(text(view).includes(props.entry.choices[0].command));
});

test('widget does not inject HTML or invoke an approval/proof RPC', () => {
  assert.ok(!source.includes('dangerouslySetInnerHTML'));
  assert.ok(!source.includes('innerHTML'));
  assert.ok(!source.includes('fetch('));
  assert.ok(!source.includes('rs.call('));
  assert.ok(source.includes('editor.api.insertText'));
});
