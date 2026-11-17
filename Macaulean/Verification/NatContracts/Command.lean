import Macaulean.Verification.NatContracts.Soundness
import Macaulean.Verification.Targets
import Macaulean.Interpreter.DSL

/-!
# `#m2_verify`: contracts for worksheet M2 functions over natural numbers

    gcdNat = (a,b) -> if b == 0 then a else gcdNat(b, a % b);
    #m2_verify gcdNat (a b : Nat) returns r : r = Nat.gcd a b
      termination_by b := by ...

Binders of type `Nat` are the function's arguments, in order; other binders are
preconditions. The term after `returns r :` is the postcondition, `termination_by`
gives a natural-number measure that must decrease at every self-call, and the
optional tactic proves the generated verification conditions.

The command reflects the current worksheet state and adds, without assuming
anything:
* `gcdNat.state`, `gcdNat.body`: the runtime state and the function's compiled body;
* `gcdNat.contract`: the contract;
* `gcdNat.vc`: the verification conditions, proved by the given tactic;
* `gcdNat.correct`: for natural arguments satisfying the preconditions, the
  production call returns a natural `r` satisfying the postcondition for some fuel,
  and every successful call at any fuel returns such an `r`.

No new keywords are reserved: M2 worksheet identifiers are unaffected.
-/
namespace Macaulean.M2.Verification.NatContracts
open Lean Elab Command Lexical

/-! ## The supported fragment, for early and specific error messages -/

private def describe : Code → String
  | .set .. | .setMany .. => "assignments in function bodies are not supported yet"
  | .seq .. => "`;` sequences in function bodies are not supported yet"
  | .listLit .. | .sequence .. => "lists and sequences are not natural numbers"
  | .lambda .. => "nested functions are not supported"
  | .ifThen .. => "`if` without `else` may return null"
  | .returnTerm .. => "`return` is not supported yet"
  | .logic .. | .unop .notOp _ => "a Boolean is used where a natural number is expected"
  | .unop .neg _ => "negation leaves the natural numbers"
  | _ => "this construct is not supported"

mutual
private partial def checkN (self : String) : Code → Except String Unit
  | .int z => if z < 0 then .error "negative literals are not natural numbers" else pure ()
  | .read (.slot 0 _) => pure ()
  | .read (.slot _ _) => .error "captured outer variables are not supported"
  | .read (.global x) => .error s!"`{x}` is a global value; only parameters may be read"
  | .binop op a b =>
    if [BinOp.add, .sub, .mul, .quot, .rem, .pow].contains op then do
      checkN self a; checkN self b
    else if [BinOp.eq, .ne, .lt, .le, .gt, .ge].contains op then
      .error s!"`{op.symbol}` gives a Boolean where a natural number is expected"
    else if op == .div then .error "`/` gives a rational number; use `//` for natural division"
    else .error s!"operator `{op.symbol}` is not supported on natural numbers"
  | .ifElse c yes no => do checkB self c; checkN self yes; checkN self no
  | .apply (.read (.global f)) arg =>
    if f != self then .error s!"calls to `{f}` are not supported; only self-recursion is"
    else match arg with
      | .sequence args => args.forM (checkN self)
      | arg => checkN self arg
  | .apply .. => .error "only calls of the function itself by its global name are supported"
  | other => .error (describe other)

private partial def checkB (self : String) : Code → Except String Unit
  | .binop op a b =>
    if [BinOp.eq, .ne, .lt, .le, .gt, .ge].contains op then do
      checkN self a; checkN self b
    else .error s!"`{op.symbol}` does not give a Boolean condition"
  | .logic _ a b => do checkB self a; checkB self b
  | .unop .notOp a => checkB self a
  | _ => .error "conditions must be comparisons of natural numbers, `and`, `or` or `not`"
end

/-- Does the body call the function itself? -/
private partial def callsSelf (self : String) : Code → Bool
  | .apply (.read (.global f)) arg => f == self || callsSelf self arg
  | .binop _ a b | .logic _ a b | .apply a b => callsSelf self a || callsSelf self b
  | .unop _ a => callsSelf self a
  | .ifElse c a b => callsSelf self c || callsSelf self a || callsSelf self b
  | .sequence cs => cs.any (callsSelf self)
  | _ => false

/-! ## The command -/

syntax m2VerifyBinder := "(" binderIdent+ " : " term ")"
syntax (name := verifyCommand) "#m2_verify " ident m2VerifyBinder* &"returns" ident " : " term
  (" termination_by " term)? (" := " "by " tacticSeq)? : command

/-- Close verification conditions when no tactic is given; on failure, show them. -/
macro "m2_vc" : tactic => `(tactic|
  first
  | done | omega | grind | (simp_all; done) | (simp_all <;> omega)
  | fail "could not prove this verification condition automatically; give a proof with `:= by ...`")

private def isNat (ty : Syntax.Term) : Bool := ty.raw.isIdent && ty.raw.getId == `Nat

@[command_elab verifyCommand]
def elabVerify : CommandElab := fun stx => do
  let `(#m2_verify $fn:ident $binders:m2VerifyBinder* returns $r:ident : $post:term
      $[termination_by $measure?]? $[:= by $tac?]?) := stx | throwUnsupportedSyntax
  let m2name := fn.getId.toString
  -- Split binders into natural arguments and preconditions.
  let mut args : Array Ident := #[]
  let mut pres : Array Syntax.Term := #[]
  for b in binders do
    let `(m2VerifyBinder| ($ids:binderIdent* : $ty)) := b | throwUnsupportedSyntax
    if isNat ty then
      for id in ids do
        match id with
        | `(binderIdent| $x:ident) => args := args.push x
        | _ => throwErrorAt id "natural-number arguments must be named"
    else
      for _ in ids do pres := pres.push ty
  -- The worksheet function, exactly as compiled.
  let session ← DSL.getSession
  let some (.closure id) := session.env.lookup m2name
    | throwErrorAt fn "`{m2name}` is not globally bound to an M2 function"
  let some (.closure params slots body captured) := session.heap.functions[id]?
    | throwErrorAt fn "`{m2name}` is not an M2 closure"
  let arity := match params with | .fixed ps => ps.length | .variadic _ => 1
  unless arity == args.size do
    throwErrorAt fn "`{m2name}` takes {arity} argument(s), but {args.size} natural-number binder(s) were given"
  unless slots == arity do
    throwErrorAt fn "local variables in `{m2name}` are not supported yet"
  if let .error e := checkN m2name body then
    throwErrorAt fn "`{m2name}` is outside the supported natural-number fragment: {e}"
  if measure?.isNone && callsSelf m2name body then
    throwErrorAt fn "`{m2name}` is recursive: give a decreasing measure with `termination_by`"
  -- Reflected state and body.
  let decl (suffix : Name) := mkIdent (fn.getId ++ suffix)
  let stateId := decl `state
  let bodyId := decl `body
  let contractId := decl `contract
  let vcId := decl `vc
  let correctId := decl `correct
  liftTermElabM do
    addDecl (.defnDecl {
      name := stateId.getId, levelParams := [], type := mkConst ``Runtime.State,
      value := Targets.stateExpr ⟨session.env, session.heap⟩,
      hints := .abbrev, safety := .safe })
    addDecl (.defnDecl {
      name := bodyId.getId, levelParams := [], type := mkConst ``Code,
      value := LibraryCompiler.codeExpr body, hints := .abbrev, safety := .safe })
  -- The contract, as functions of the argument list.
  let pre ← match pres.toList with
    | [] => `(True)
    | p :: ps => ps.foldlM (fun acc q => `($acc ∧ $q)) p
  let measure ← match measure? with
    | some m => pure m
    | none => `(0)
  elabCommand (← `(command|
    set_option linter.unusedVariables false in
    def $contractId : Macaulean.M2.Verification.NatContracts.Contract where
      arity := $(quote arity)
      pre := fun xs => match xs with
        | [$args,*] => $pre
        | _ => False
      post := fun xs $r => match xs with
        | [$args,*] => $post
        | _ => False
      measure := fun xs => match xs with
        | [$args,*] => $measure
        | _ => 0))
  -- Verification conditions.
  let tac ← match tac? with
    | some t => pure t
    | none => `(tacticSeq| m2_vc)
  let names : Array (TSyntax ``binderIdent) ← args.mapM fun a => `(binderIdent| $a:ident)
  let paramsStx ← match params with
    | .fixed ps => `(Macaulean.M2.Parameters.fixed $(quote ps))
    | .variadic x => `(Macaulean.M2.Parameters.variadic $(quote x))
  elabCommand (← `(command|
    set_option Elab.async false in
    theorem $vcId :
        Macaulean.M2.Verification.NatContracts.VC $(quote m2name) $paramsStx $contractId $bodyId := by
      intro xs
      simp only [$contractId:ident]
      split
      next $names* =>
        intro h
        delta $bodyId
        simp [Macaulean.M2.Verification.NatContracts.wpN,
          Macaulean.M2.Verification.NatContracts.wpB,
          Macaulean.M2.Verification.NatContracts.wpArgs,
          Macaulean.M2.Verification.NatContracts.Ctx.callPost,
          Macaulean.M2.Verification.NatContracts.Ctx.acceptsSequence,
          Macaulean.M2.Verification.NatContracts.logicBool, Macaulean.M2.LogicOp.shortCircuit]
        all_goals ($tac)
      next => intro h; exact h.elim))
  -- The user-facing theorem, only once the verification conditions are proved.
  if (← get).messages.hasErrors then return
  match (← getEnv).find? vcId.getId with
  | some info => if info.value?.any (·.hasSorry) then return
  | none => return
  let hyps : Array Ident := (Array.range pres.size).map fun i => mkIdent (.mkSimple s!"pre{i+1}")
  let argBinders ← args.mapM fun a => `(bracketedBinder| ($a : Nat))
  let preBinders ← (hyps.zip pres).mapM fun (h, p) => `(bracketedBinder| ($h : $p))
  let argValues ← args.mapM fun a => `(Macaulean.M2.Value.zz ($a : Int))
  -- A fixed parameter list receives a sequence; a variadic one the single value.
  let argValue ← match params, argValues.toList with
    | .variadic _, [v] => pure v
    | _, _ => `(Macaulean.M2.Value.sequence [$argValues,*])
  let rB ← `(binderIdent| $r:ident)
  let preProof ← match hyps.toList with
    | [] => `(by simp only [$contractId:ident])
    | [h] => `(by simp only [$contractId:ident]; exact $h)
    | hs => `(by simp only [$contractId:ident]; exact ⟨$(hs.toArray),*⟩)
  elabCommand (← `(command|
    theorem $correctId $argBinders* $preBinders* :
        (∃ (fuel : Nat) ($rB : Nat) (after : Macaulean.M2.Runtime.State),
          Macaulean.M2.Runtime.call fuel (.closure $(quote id)) $argValue
            $stateId = .ok (.zz ($r : Int), after) ∧ $post) ∧
        (∀ (fuel : Nat) (v : Macaulean.M2.Value) (after : Macaulean.M2.Runtime.State),
          Macaulean.M2.Runtime.call fuel (.closure $(quote id)) $argValue
            $stateId = .ok (v, after) → ∃ ($rB : Nat), v = .zz ($r : Int) ∧ $post) :=
      Macaulean.M2.Verification.NatContracts.verified (s := $stateId) (name := $(quote m2name))
        (id := $(quote id)) (params := $paramsStx) (body := $bodyId)
        (captured := $(quote captured)) (C := $contractId) (by decide +kernel) rfl rfl $vcId
        [$args,*] rfl $preProof $argValue rfl))

end Macaulean.M2.Verification.NatContracts
