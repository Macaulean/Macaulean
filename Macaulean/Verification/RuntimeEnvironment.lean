import Macaulean.Interpreter.Runtime

namespace Macaulean.M2.Runtime

/-- Protected names retain the production prelude's meanings. User globals and
arbitrary heap contents are permitted. -/
def PreludeBindings (s : State) : Prop :=
  ∀ name ∈ protectedNames, s.env.lookup name = prelude.lookup name

theorem PreludeBindings.initial : PreludeBindings ({} : State) := by
  intro name _
  rfl

theorem PreludeBindings.allocate (h : PreludeBindings s) (vs : List Value) :
    PreludeBindings (s.allocate vs).2 := h

theorem PreludeBindings.writeRef (h : PreludeBindings s)
    (success : writeRef ref value frames s = .ok after) : PreludeBindings after := by
  cases ref with
  | global name =>
    simp only [Runtime.writeRef, checkWritable] at success
    split at success
    · simp [bind, Except.bind] at success
    · next notProtected =>
      simp [bind, Except.bind, pure, Except.pure] at success
      subst after
      intro key hk
      have ne : key ≠ name := by
        intro eq
        subst key
        exact notProtected hk
      have different : (key == name) = false := beq_eq_false_iff_ne.mpr ne
      simpa [List.lookup, different] using h key hk
  | slot depth index =>
    simp only [Runtime.writeRef, checkWritable, bind, Except.bind] at success
    split at success
    · split at success
      · simp only [pure, Except.pure, Except.ok.injEq] at success
        subst after
        exact h
      · cases success
    · cases success

theorem PreludeBindings.of_env_eq (h : PreludeBindings s) (same : after.env = s.env) :
    PreludeBindings after := by
  intro name hn
  rw [same]
  exact h name hn

theorem PreludeBindings.function (h : PreludeBindings s) (f : Function) :
    PreludeBindings (s.function f).2 := h

theorem PreludeBindings.writeMany (refs : List Lexical.Ref) (values : List Value)
    (frames : Frames) (s after : State) (h : PreludeBindings s)
    (success : Runtime.writeMany refs values frames s = .ok after) : PreludeBindings after := by
  induction refs generalizing values s with
  | nil =>
    cases values with
    | nil => cases success; exact h
    | cons v vs => cases success
  | cons ref refs ih =>
    cases values with
    | nil => cases success
    | cons v vs =>
      cases hw : Runtime.writeRef ref v frames s with
      | error e => simp [Runtime.writeMany, hw, bind, Except.bind] at success
      | ok next =>
        apply ih vs next (h.writeRef hw)
        simpa only [Runtime.writeMany, hw, bind, Except.bind] using success

def checkPreludeBindings (s : State) : Bool :=
  protectedNames.all fun name => s.env.lookup name == prelude.lookup name

theorem checkPreludeBindings_eq_true (s : State) :
    checkPreludeBindings s = true ↔ PreludeBindings s := by
  simp [checkPreludeBindings, PreludeBindings, List.all_eq_true, beq_iff_eq]

theorem PreludeBindings.of_check (h : checkPreludeBindings s = true) : PreludeBindings s :=
  (checkPreludeBindings_eq_true s).mp h

end Macaulean.M2.Runtime
