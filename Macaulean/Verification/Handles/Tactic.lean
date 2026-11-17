import Macaulean.Verification.Handles.Simp
import Macaulean.Verification.Handles.Frontend

/-!
# `m2_unfold`: one step of a worksheet function, as ordinary mathematics

On a goal `f a ⇓ r`, `f a ↓` or `Fn.Call.Sat (f a) Q`, where `f` is a closure,
`m2_unfold` replaces the call by its body (`Fn.Call.Sat.intro`), evaluates the
production operations with `m2_simp`, and presents what is left in Lean terms:
naturals instead of casts, and calls `g (x, y) ⇓ s` instead of runtime values.
-/
namespace Macaulean.M2.Handles
open Lean Elab Tactic Meta

/-- `List.lookup "x" S.env` for a reflected worksheet state `S`, with its value. -/
private def lookupFacts (goal : Expr) : MetaM (Array (Expr × Expr)) := do
  let mut facts := #[]
  let reg ← getRegistry
  let apps := collect (← instantiateMVars goal) #[]
  for app in apps do
    let args := app.getAppArgs
    let key := args[args.size - 2]!
    let envE := args[args.size - 1]!
    let .lit (.strVal k) := key | continue
    let state := match envE with
      | .app _ s | .proj _ _ s => s
      | e => e
    let some c := state.constName? | continue
    let some snap := reg.snapshot? c | continue
    let v := snap.state.env.lookup k
    let rhs ← match v with
      | some v => mkAppM ``Option.some #[valueExpr v]
      | none => mkAppOptM ``Option.none #[mkConst ``Value]
    facts := facts.push (app, rhs)
  return facts
where
  collect (e : Expr) (acc : Array Expr) : Array Expr :=
    let acc := if e.isAppOfArity ``List.lookup 5 && !acc.contains e then acc.push e else acc
    match e with
    | .app f a => collect a (collect f acc)
    | .lam _ t b _ | .forallE _ t b _ => collect b (collect t acc)
    | .letE _ t v b _ => collect b (collect v (collect t acc))
    | .mdata _ b | .proj _ _ b => collect b acc
    | _ => acc

/-- Prove `lhs = rhs` by kernel evaluation. -/
private def kernelEq (lhs rhs : Expr) : TacticM Expr := do
  let ty ← mkEq lhs rhs
  let m ← mkFreshExprMVar ty
  let gs ← Tactic.run m.mvarId! (evalTactic (← `(tactic| decide +kernel)))
  unless gs.isEmpty do throwError "m2_unfold: could not evaluate {lhs}"
  instantiateMVars m

/-- A runtime value as the Lean value it represents, when it is one. -/
private def asLean? (v : Expr) : MetaM (Option Expr) := do
  match_expr v with
  | Value.zz i =>
    match_expr i with
    | Nat.cast _ _ n => return some n
    | Int.ofNat n => return some n
    | OfNat.ofNat _ k _ =>
      match k with
      | .lit (.natVal k) => return some (mkNatLit k)
      | _ => return some i
    | _ => return some i
  | Value.bool b => return some b
  | Value.list xs =>
    match_expr xs with
    | List.map _ _ f l => if f.isAppOf ``ToM2.toValue then return some l else return none
    | _ => return none
  | _ => return none

private def leanOrValue (v : Expr) : MetaM Expr := return (← asLean? v).getD v

/-- The registered handle constant for `Fn.mk S (.closure k)`. -/
private def handleFor? (f : Expr) : MetaM (Option Expr) := do
  match_expr f with
  | Fn.mk S v =>
    let some c := S.constName? | return none
    let reg ← getRegistry
    let some snap := reg.snapshot? c | return none
    match_expr v with
    | Value.closure k =>
      let some k := (← instantiateMVars k).rawNatLit? <|> (← whnf k).rawNatLit? | return none
      let some h := reg.handles.find? (fun h => h.key == snap.key && h.value == .closure k)
        | return none
      return some (mkConst h.const)
    | _ => return none
  | _ => return none

/-- Present runtime calls and results as handle calls on Lean values. -/
private def prettify (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun e => do
    match_expr e with
    | Fn.Call.mk f a =>
      let f := (← handleFor? f).getD f
      let arg ← match_expr a with
        | Value.sequence vs =>
          let some (_, vs) := (← instantiateMVars vs).listLit? | return .done e
          match vs.reverse with
          | [] => mkAppM ``Arg.of #[mkConst ``Unit.unit]
          | [_] => return .done (mkApp2 (mkConst ``Fn.Call.mk) f a)
          | last :: rest =>
            let mut tuple ← leanOrValue last
            for v in rest do tuple ← mkAppM ``Prod.mk #[← leanOrValue v, tuple]
            mkAppM ``Arg.of #[tuple]
        | _ => mkAppM ``Arg.of #[← leanOrValue a]
      return .done (← mkAppM ``Fn.call #[f, arg])
    | Fn.call f a =>
      match_expr a with
      | Arg.of α _ x =>
        if α.isConstOf ``Value then
          if let some l ← asLean? x then
            return .done (← mkAppM ``Fn.call #[f, ← mkAppM ``Arg.of #[l]])
        return .continue
      | _ => return .continue
    | Fn.Call.Returns c r =>
      if r.isAppOf ``ToM2.toValue then return .continue
      let some l ← asLean? r | return .continue
      return .done (mkApp2 (mkConst ``Fn.Call.Returns) c (← mkAppM ``ToM2.toValue #[l]))
    | Fn.Call.Sat c q =>
      match q with
      | .lam _ _ body _ =>
        if body.isConstOf ``True then return .done (mkApp (mkConst ``Fn.Call.Terminates) c)
        match_expr body with
        | Eq _ x r =>
          if x == .bvar 0 && !r.hasLooseBVars then
            return .done (mkApp2 (mkConst ``Fn.Call.Returns) c
              (← match ← asLean? r with
                | some l => mkAppM ``ToM2.toValue #[l]
                | none => pure r))
          return .continue
        | _ => return .continue
      | _ => return .continue
    | _ => return .continue)

elab "m2_unfold_raw" : tactic => withMainContext do
  evalTactic (← `(tactic| try unfold Fn.Call.Returns))
  evalTactic (← `(tactic| try unfold Fn.Call.Terminates))
  evalTactic (← `(tactic|
    first
    | (apply Fn.Call.Sat.intro (by rfl) (by rfl) (by rfl))
    | fail "m2_unfold: the goal is not a call of an M2 closure"))
  evalTactic (← `(tactic| simp only [wpV, wpArgs]))
  let goal ← getMainTarget
  let facts ← lookupFacts goal
  let mut names : Array Ident :=
    #[mkIdent `m2_simp, mkIdent ``Arg.of, mkIdent ``ToM2Arg.toArg, mkIdent ``ToM2Seq.toSeq]
  for (lhs, rhs) in facts do
    let proof ← kernelEq lhs rhs
    let name ← mkFreshUserName `m2_lookup
    let g ← getMainGoal
    let (_, g) ← (← g.assert name (← inferType proof) proof).intro1P
    replaceMainGoal [g]
    names := names.push (mkIdent name)
  let lemmas ← names.mapM fun n => `(Parser.Tactic.simpLemma| $n:term)
  withMainContext do
    evalTactic (← `(tactic| set_option linter.unusedSimpArgs false in simp [$lemmas,*]))

/-- Present the goal in Lean terms: natural subtraction under branch conditions,
casts lifted, calls and results folded into handles. -/
elab "m2_tidy" : tactic => do
  if (← getGoals).isEmpty then return
  -- Branch conditions become binders of `dite`, visible to the discharger: natural
  -- subtraction stays natural, and list indices are in range.
  evalTactic (← `(tactic| try simp only [ite_eq_dite]))
  evalTactic (← `(tactic| try (
    set_option linter.unusedSimpArgs false in
    simp (disch := first | omega | (simp_all; done) | decide)
      [m2_simp, zz_sub_natCast, zz_sub_ofNat, -dite_eq_ite])))
  if (← getGoals).isEmpty then return
  evalTactic (← `(tactic| try simp only [dite_eq_ite]))
  evalTactic (← `(tactic| try simp only [ite_true, ite_false, ↓reduceIte]))
  if (← getGoals).isEmpty then return
  evalTactic (← `(tactic| try norm_cast))
  if (← getGoals).isEmpty then return
  evalTactic (← `(tactic| try simp only [ite_true, ite_false, ↓reduceIte]))
  if (← getGoals).isEmpty then return
  withMainContext do
    let g ← getMainGoal
    let t ← instantiateMVars (← g.getType)
    replaceMainGoal [← g.change (← prettify t)]
  withMainContext do
    for d in ← getLCtx do
      if d.userName.toString.startsWith "m2_lookup" then
        replaceMainGoal [← (← getMainGoal).clear d.fvarId]

/-- Unfold one call of a worksheet function and present the result in Lean terms. -/
macro "m2_unfold" : tactic => `(tactic| (m2_unfold_raw; m2_tidy))

/-- Prove that a later worksheet state extends an earlier one, by evaluation. -/
macro "m2_extends" : tactic => `(tactic|
  first
  | exact Extends.refl _
  | (apply Extends.of_parts <;> first | decide +kernel | rfl)
  | fail "m2_extends: the later worksheet state does not extend the earlier one \
      (was a name redefined?)")

/-- Discharge a call in the goal with a proved result `h : g (x) ⇓ r`, possibly about
an earlier worksheet state, and continue with what the caller does with `r`. -/
macro "m2_use " h:term : tactic => `(tactic| (
  refine Fn.Call.Sat.use $h (by m2_extends) ?_
  try simp [m2_simp]
  m2_tidy))

/-- Evaluate a call on concrete arguments by unfolding until nothing is left. -/
macro "m2_eval" : tactic => `(tactic| ((repeat m2_unfold) <;> try decide))

end Macaulean.M2.Handles
