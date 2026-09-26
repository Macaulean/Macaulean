import Lean
import Macaulean.Interpreter.Run
import Macaulean.Macaulay2

/-!
# Differential checking and kernel certificates

`#m2_eval` runs the pure interpreter. `#m2_check` additionally compares a live M2
result and constructs a kernel-checked equality about `run`. Reification of
nested collections is structural and introduces no axioms or native shortcuts.
-/
namespace Macaulean.M2
open Lean Elab Command Meta

deriving instance ToExpr for Error

mutual

def valueExpr : Value → Expr
  | .zz n => mkApp (mkConst ``Value.zz) (toExpr n)
  | .qq q => mkApp (mkConst ``Value.qq) (mkApp2 (mkConst ``mkRat) (toExpr q.num) (toExpr q.den))
  | .bool b => mkApp (mkConst ``Value.bool) (toExpr b)
  | .null => mkConst ``Value.null
  | .list xs => mkApp (mkConst ``Value.list) (valuesExpr xs)
  | .sequence xs => mkApp (mkConst ``Value.sequence) (valuesExpr xs)

def valuesExpr : List Value → Expr
  | [] => mkApp (mkConst ``List.nil [0]) (mkConst ``Value)
  | v :: vs => mkApp3 (mkConst ``List.cons [0]) (mkConst ``Value) (valueExpr v) (valuesExpr vs)

end

instance : ToExpr Value where
  toTypeExpr := mkConst ``Value
  toExpr := valueExpr

instance : ToExpr Outcome where
  toTypeExpr := mkConst ``Outcome
  toExpr
    | .parseError msg => mkApp (mkConst ``Outcome.parseError) (toExpr msg)
    | .error e => mkApp (mkConst ``Outcome.error) (toExpr e)
    | .ok v => mkApp (mkConst ``Outcome.ok) (toExpr v)

def Outcome.toM2String : Outcome → String
  | .parseError msg => s!"parse error: {msg}"
  | .error e => s!"error: {e}"
  | .ok v => v.toM2String

inductive M2Reply where
  | error
  | ok (v : Value)
  deriving DecidableEq

/-- Legacy scalar wire format, retained for callers using `evalValue`. -/
def M2Reply.ofStrings : List String → Except String M2Reply
  | ["error", _, _] => .ok .error
  | ["ok", "ZZ", s] =>
    match s.toInt? with
    | some n => .ok (.ok (.zz n)) | none => .error s!"cannot parse ZZ value {s}"
  | ["ok", "QQ", s] =>
    match s.splitOn "/" with
    | [n, d] =>
      match n.toInt?, d.toNat? with
      | some n, some d => if d = 0 then .error "zero rational denominator"
          else .ok (.ok (.qq (mkRat n d)))
      | _, _ => .error s!"cannot parse QQ value {s}"
    | _ => .error s!"cannot parse QQ value {s}"
  | ["ok", "Boolean", "true"] => .ok (.ok (.bool true))
  | ["ok", "Boolean", "false"] => .ok (.ok (.bool false))
  | ["ok", "Nothing", _] => .ok (.ok .null)
  | ["ok", cls, s] => .error s!"Macaulay2 returned {s} of class {cls}, which is not supported"
  | r => .error s!"unexpected reply from Macaulay2: {r}"

def M2Reply.toM2String : M2Reply → String
  | .error => "error" | .ok v => v.toM2String

def queryM2 (src : String) : IO (Except String M2Reply) := do
  let m2 ← globalM2Server
  let reply : List String ← m2.sendRequest "evalValue" [src]
  return M2Reply.ofStrings reply

def agrees : Outcome → M2Reply → Bool
  | .ok v, .ok w => v == w
  | .error _, .error => true | .parseError _, .error => true
  | _, _ => false

def addRunTheorem (name : Name) (src : String) (o : Outcome) (doc : String) : CommandElabM Unit :=
  liftTermElabM do
    let type ← mkEq (mkApp (mkConst ``run) (toExpr src)) (toExpr o)
    let inst ← synthInstance (mkApp (mkConst ``Decidable) type)
    let proof := mkApp3 (mkConst ``of_decide_eq_true) type inst
      (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``true))
    addDecl <| .thmDecl { name, levelParams := [], type, value := proof }
    addDocStringCore name doc

def freshName : CommandElabM Name := do
  let ns ← getCurrNamespace
  let env ← getEnv
  let rec go : Nat → Nat → Name
    | 0, i => ns ++ Name.mkSimple s!"m2_check_{i}"
    | fuel + 1, i =>
      let n := ns ++ Name.mkSimple s!"m2_check_{i}"
      if env.contains n then go fuel (i + 1) else n
  return go 100000 1

syntax (name := m2Eval) "#m2_eval " str : command
@[command_elab m2Eval] def elabM2Eval : CommandElab
  | `(#m2_eval $s:str) => logInfo (run s.getString).toM2String
  | _ => throwUnsupportedSyntax

syntax (name := m2Check) "#m2_check " (ident " : ")? str : command
@[command_elab m2Check] def elabM2Check : CommandElab
  | `(#m2_check $[$id? :]? $s:str) => do
    let src := s.getString
    let o := run src
    let reply : M2Reply ← match ← queryM2 src with
      | .ok r => pure r | .error msg => throwError msg
    unless agrees o reply do
      throwError m!"interpreter and Macaulay2 disagree on {repr src}:\n  interpreter: {o.toM2String}\n  Macaulay2: {reply.toM2String}"
    let name : Name ← match id? with
      | some id => pure ((← getCurrNamespace) ++ id.getId)
      | none => freshName
    addRunTheorem name src o s!"Macaulay2 evaluates `{src}` to `{reply.toM2String}`."
    logInfo m!"{MessageData.ofConstName name} : run {repr src} = {o.toM2String}"
  | _ => throwUnsupportedSyntax

end Macaulean.M2
