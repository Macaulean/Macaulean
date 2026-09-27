import Macaulean.Verification.Index
import Macaulean.Interpreter.DSL

/-!
# Intent review in the ordinary Lean InfoView

The panel is a view of an elaboration snapshot. Buttons insert explicit source
commands at the end of that command, not at an arbitrary cursor inside a function.
The client never marks a contract approved optimistically: re-elaboration must
validate the frozen key. No RPC endpoint grants approval or starts proof search.
-/
namespace Macaulean.M2.Verification.Panel
open Lean Elab Command

private def strings (xs : List String) : Json := toJson xs

def proposalJson (p : Intent.Proposal) (current : Option String) : Json :=
  let status := p.status current
  let d := Contracts.describe p.kind
  Json.mkObj [
    ("schema",Json.str p.kind.name), ("title",Json.str d.title),
    ("inputs",strings d.inputs), ("guarantees",strings d.guarantees),
    ("limitations",strings d.limitations), ("formal",Json.str d.formal),
    ("version",Json.str Contracts.version), ("digest",Json.str p.digest),
    ("status",Json.str status.label), ("proofStatus",Json.str "Unattempted - no proof is supplied by intent approval"),
    ("canApprove",toJson (status != .stale && status != .unavailable)),
    ("approveCommand",Json.str s!"#m2_approve {repr p.bindingName} {p.kind.name} {repr p.digest}\n"),
    ("revokeCommand",Json.str s!"#m2_revoke {repr p.bindingName} {p.kind.name}\n"),
    ("approvalSource",Json.str p.approvalSource)]

def entryJson (index : Index.State) (session : Session) (theory : Option Snapshot.Theory)
    (entry : Index.Entry) : Json :=
  let value := session.lookup entry.name
  let proposals := index.ledger.proposals.filter (fun p => p.bindingId == entry.id)
  let cards := proposals.map fun p =>
    let current := theory.bind fun t => (Index.currentPayload entry p.kind session t).toOption
    proposalJson p current
  let choices := Contracts.all.map fun kind => Json.mkObj [
    ("name",Json.str kind.name), ("description",Json.str (Contracts.render kind)),
    ("command",Json.str s!"#m2_contract {repr entry.name} {kind.name}\n")]
  Json.mkObj [
    ("id",Json.str entry.id), ("name",Json.str entry.name),
    ("generation",toJson entry.generation), ("file",Json.str entry.sourceFile),
    ("className",Json.str ((value.map Value.className).getD "Unavailable")),
    ("callable",toJson ((value.map Runtime.callable).getD false)),
    ("views",strings ((value.map Index.viewLabels).getD ["Binding no longer visible"])),
    ("sourceNodes",toJson entry.nodes), ("contracts",toJson cards),
    ("choices",toJson choices)]

/-- Exported, deterministic, read-only inventory for tools. It contains no proof
success flags and no executable callback. -/
def inventory (env : Environment) : Json :=
  let index := Index.indexExt.getState env
  let session := DSL.sessionExt.getState env
  let theory := Snapshot.theoryExt.getState env
  Json.mkObj [
    ("schema",Json.str "macaulean.semantic-index.v1"),
    ("module",Json.str env.mainModule.toString),
    ("proofStatus",Json.str "unattempted"),
    ("entries",toJson (index.entries.map (entryJson index session theory))),
    ("eventCount",toJson index.ledger.events.length),
    ("theoryDigest",Json.str ((theory.map (·.digest)).getD "not-requested")),
    ("theoryDeclarations",toJson ((theory.map (·.declarations)).getD [])),
    ("theoryAxioms",toJson ((theory.map (·.axioms)).getD []))]

@[widget_module]
def widget : Widget.Module where
  javascript := r#"
import * as React from 'react';
import { EditorContext } from '@leanprover/infoview';
const e = React.createElement;
function paragraphs(xs) { return xs.map((s,i) => e('p', {key:i}, s)); }
function ContractCard({p, insert}) {
  const [reviewed,setReviewed] = React.useState(false);
  React.useEffect(() => setReviewed(false), [p.digest,p.status]);
  return e('section', {className:'mt2'},
    e('h4',null,p.title), e('p',null,'Intent: '+p.status),
    e('p',null,'Proof: '+p.proofStatus),
    e('strong',null,'Inputs'), ...paragraphs(p.inputs),
    e('strong',null,'Guarantees'), ...paragraphs(p.guarantees),
    e('strong',null,'Not claimed'), ...paragraphs(p.limitations),
    e('details',null,e('summary',null,'Formal target and revision'),
      e('pre',null,p.formal),e('p',null,p.version),e('code',null,p.digest),
      e('p',null,'Attestation source: '+(p.approvalSource || 'none'))),
    e('label',null,e('input',{type:'checkbox',checked:reviewed,
      disabled:!p.canApprove,onChange:ev=>setReviewed(ev.target.checked)}),
      ' This contract, including its exclusions, matches my intent.'),
    e('div',null,
      e('button',{disabled:!reviewed || !p.canApprove,onClick:()=>insert(p.approveCommand)},'Record approval in source'),
      e('button',{onClick:()=>insert(p.revokeCommand)},'Revoke in source')));
}
export default function IntentPanel(props) {
  const editor = React.useContext(EditorContext);
  const [choice,setChoice] = React.useState('');
  const [notice,setNotice] = React.useState('');
  const p = props.entry;
  React.useEffect(()=>{setChoice('');setNotice('');},[p.id,p.generation]);
  async function insert(text) {
    try {
      if (!editor || !props.pos || !props.pos.uri) throw new Error('No document connection. Copy the command below.');
      await editor.api.insertText(text,'below',{
        textDocument:{uri:props.pos.uri}, position:props.insertAt});
      setNotice('Source command inserted. Status changes only after Lean re-elaborates it.');
    } catch (error) { setNotice(String(error)+'\n'+text); }
  }
  const selected = p.choices.find(c=>c.name===choice);
  return e('div',{className:'pa2'},
    e('h3',null,'M2 intent: '+p.name),
    e('p',null,p.className+'; binding generation '+p.generation),
    e('p',null,'Snapshot at this source position. Approval is separate from proof.'),
    ...paragraphs(p.views),
    ...p.contracts.map(c=>e(ContractCard,{key:c.schema,p:c,insert})),
    p.callable && e('section',null,
      e('select',{value:choice,onChange:ev=>setChoice(ev.target.value)},
        e('option',{value:''},'Choose a contract to review'),
        ...p.choices.map(c=>e('option',{key:c.name,value:c.name},c.name))),
      selected && e('pre',{style:{whiteSpace:'pre-wrap'}},selected.description),
      e('button',{disabled:!selected,onClick:()=>insert(selected.command)},'Propose contract in source')),
    e('details',null,e('summary',null,'Binding and nested source map'),
      e('p',null,p.file),e('code',null,p.id),
      e('pre',null,JSON.stringify(p.sourceNodes,null,2))),
    notice && e('pre',{role:'status',style:{whiteSpace:'pre-wrap'}},notice));
}
"#

def show (entry : Index.Entry) (stx : Syntax) : CommandElabM Unit := do
  let env ← getEnv
  let index := Index.indexExt.getState env
  let session := DSL.sessionExt.getState env
  let theory := Snapshot.theoryExt.getState env
  let some tail := stx.getTailPos? | throwErrorAt stx "missing source anchor for intent panel"
  let position := (← getFileMap).utf8PosToLspPos tail
  let props := Json.mkObj [
    ("entry",entryJson index session theory entry), ("insertAt",toJson position)]
  Widget.savePanelWidgetInfo widget.javascriptHash (pure props) stx

open Lean.Server Lean.Server.RequestM in
@[server_rpc_method]
def getIndex (position : Lean.Lsp.Position) : RequestM (RequestTask Json) := do
  let doc ← readDoc
  let pos := doc.meta.text.lspPosToUtf8Pos position
  withWaitFindSnap doc
    (notFoundX := throwThe RequestError ⟨.invalidParams,"no elaboration snapshot at this position"⟩)
    (fun snapshot => snapshot.endPos >= pos)
    (fun snapshot => pure (inventory snapshot.env))

end Macaulean.M2.Verification.Panel
