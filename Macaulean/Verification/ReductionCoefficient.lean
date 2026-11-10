import Macaulean.Verification.ReductionTypes
import Macaulean.Verification.CallNormal

/-! The actual source cancellation coefficient expression. -/
namespace Macaulean.M2.Verification.ReductionCoefficient
open Lexical Macaulean.M2.Runtime GCD.Execution Views

/-- The pure operations in `reductionCoefficient`, in source evaluation order. -/
def operations (p q : Views.Polynomial r) : Except Error Value := do
  let a ← Polynomials.callPrimitive .leadCoefficient p.value
  let b ← Polynomials.callPrimitive .leadCoefficient q.value
  let ratio ← evalBinOp .div a b
  let m ← Polynomials.callPrimitive .leadMonomial p.value
  let n ← Polynomials.callPrimitive .leadMonomial q.value
  let quotient ← Polynomials.callPrimitive .monomialQuotient (.sequence [m,n])
  evalBinOp .mul ratio quotient

theorem operations_typed (p q : Views.Polynomial r) (v : Value)
    (success : operations p q = .ok v) : ∃ c : Views.Polynomial r, v = c.value := by
  obtain ⟨a,ha⟩ := ReductionTypes.lead_coefficient p
  obtain ⟨b,hb⟩ := ReductionTypes.lead_coefficient q
  have division : evalBinOp .div (.qq a) (.qq b) =
      if b = 0 then .error .divByZero else .ok (.qq (a/b)) := rfl
  simp only [operations, ha, hb, bind, Except.bind, division] at success
  by_cases zero : b = 0
  · simp [zero] at success
  · simp only [if_neg zero] at success
    cases hm : Polynomials.callPrimitive .leadMonomial p.value with
    | error e => simp [hm] at success
    | ok m =>
      obtain ⟨mp,eq⟩ := ReductionTypes.lead_monomial p m hm
      subst m
      cases hn : Polynomials.callPrimitive .leadMonomial q.value with
      | error e => simp [hm,hn] at success
      | ok n =>
        obtain ⟨np,eq⟩ := ReductionTypes.lead_monomial q n hn
        subst n
        cases hq : Polynomials.callPrimitive .monomialQuotient (.sequence [mp.value,np.value]) with
        | error e => simp [hm,hn,hq] at success
        | ok quotient =>
          obtain ⟨qp,eq⟩ := ReductionTypes.monomial_quotient mp np quotient hq
          subst quotient
          obtain ⟨out,ho⟩ := ReductionTypes.scalar_mul (a/b) qp
          simp only [hm, hn, hq, ho, Except.ok.injEq] at success
          exact ⟨out,success.symm⟩

private theorem primitive_result (fuel : Nat) (primitive : Polynomials.Primitive)
    (arg : Value) (s : State) :
    call (fuel+1) (.algebra (.builtin primitive)) arg s =
      (show Except Signal (Value × State) from do
        let v ← liftResult (Polynomials.callPrimitive primitive arg)
        pure (v,s)) := rfl

/-- Exact execution of the existing source AST. All calls are production
primitives; their errors are preserved, and no state update occurs. -/
theorem execute (fuel : Nat) (p q : Views.Polynomial r) (row : Value)
    (s : State) (fs : Frames)
    (h0 : readRef (.slot 0 0) fs s = .ok p.value)
    (h6 : readRef (.slot 0 6) fs s = .ok (.list [q.value,row]))
    (globals : PreludeBindings s) :
    eval (fuel+10) reductionCoefficient fs s =
      (show Except Signal (Value × State) from do
        let value ← liftResult (operations p q)
        pure (value,s)) := by
  have gc : readRef (.global "leadCoefficient") fs s =
      .ok (.algebra (.builtin .leadCoefficient)) := by
    have h := globals "leadCoefficient" (by decide)
    simp only [readRef, h]
    rfl
  have gm : readRef (.global "leadMonomial") fs s =
      .ok (.algebra (.builtin .leadMonomial)) := by
    have h := globals "leadMonomial" (by decide)
    simp only [readRef, h]
    rfl
  have gq : readRef (.global "m2MonomialQuotient") fs s =
      .ok (.algebra (.builtin .monomialQuotient)) := by
    have h := globals "m2MonomialQuotient" (by decide)
    simp only [readRef, h]
    rfl
  obtain ⟨a,ha⟩ := ReductionTypes.lead_coefficient p
  obtain ⟨b,hb⟩ := ReductionTypes.lead_coefficient q
  cases hd : evalBinOp .div (.qq a) (.qq b) <;>
    simp only [reductionCoefficient, localVar, globalVar, eval, evalMany,
      h0, h6, gc, gm, gq, index_zero, operations,
      primitive_result, ha, hb, hd, liftResult, Except.mapError,
      bind, Except.bind, pure, Except.pure]
  case ok ratio =>
    cases hm : Polynomials.callPrimitive .leadMonomial p.value <;>
      simp only [gm, h6, index_zero, primitive_result,
        liftResult, Except.mapError, bind, Except.bind, pure, Except.pure]
    case ok m =>
      cases Polynomials.callPrimitive .leadMonomial q.value <;> simp only []
      case ok n =>
        cases Polynomials.callPrimitive .monomialQuotient (.sequence [m,n]) <;> simp only []

/-- No early-return signal can escape this primitive-only expression. -/
theorem normal (fuel : Nat) (p q : Views.Polynomial r) (row : Value)
    (s : State) (fs : Frames)
    (h0 : readRef (.slot 0 0) fs s = .ok p.value)
    (h6 : readRef (.slot 0 6) fs s = .ok (.list [q.value,row]))
    (globals : PreludeBindings s) : Normal (eval fuel reductionCoefficient fs s) := by
  have padded : Normal (eval (fuel+10) reductionCoefficient fs s) := by
    rw [execute fuel p q row s fs h0 h6 globals]
    exact Normal.bind (Normal.lift _) (fun value => Normal.ok (value,s))
  rcases Fuel.eval_mono fuel 10 reductionCoefficient fs s with exhausted | same
  · rw [exhausted]
    exact Normal.error _
  · rw [same]
    exact padded

/-- Any successful source evaluation produces a typed coefficient and leaves
state unchanged. Padding is used only for this nonrecursive expression. -/
theorem successful (fuel : Nat) (p q : Views.Polynomial r) (row : Value)
    (s after : State) (fs : Frames) (v : Value)
    (h0 : readRef (.slot 0 0) fs s = .ok p.value)
    (h6 : readRef (.slot 0 6) fs s = .ok (.list [q.value,row]))
    (globals : PreludeBindings s)
    (success : catchReturn (eval fuel reductionCoefficient fs s) = .ok (v,after)) :
    ∃ c : Views.Polynomial r, v = c.value ∧ after = s := by
  have padded := Fuel.preserves_success
    (Fuel.catchRefines (Fuel.eval_mono fuel 10 reductionCoefficient fs s)) success
  rw [execute fuel p q row s fs h0 h6 globals] at padded
  cases ho : operations p q with
  | error e => simp [ho, liftResult, Except.mapError, bind, Except.bind, catchReturn] at padded
  | ok value =>
    simp only [ho, liftResult, Except.mapError, bind, Except.bind,
      pure, Except.pure, catchReturn, Except.ok.injEq, Prod.mk.injEq] at padded
    obtain ⟨c,hc⟩ := operations_typed p q value ho
    exact ⟨c,padded.1.symm.trans hc,padded.2.symm⟩

end Macaulean.M2.Verification.ReductionCoefficient
