import Macaulean.Interpreter.Runtime
import Lean

/-! Increasing the evaluation budget cannot change any completed outcome. These
laws cover the actual mutually recursive evaluator, list evaluator and function
caller, including returns, captured bindings and library calls. -/
namespace Macaulean.M2.Verification.Fuel
open Lexical Macaulean.M2.Runtime

def Refines (a b : Except Signal α) : Prop := a = .error (.error .fuelExhausted) ∨ a = b

theorem refl (a : Except Signal α) : Refines a a := Or.inr rfl

theorem bind {a b : Except Signal α} {f g : α → Except Signal β}
    (h : Refines a b) (k : ∀ x, Refines (f x) (g x)) : Refines (a >>= f) (b >>= g) := by
  rcases h with h | h
  · subst a; exact Or.inl rfl
  · subst a
    cases b with
    | error e => exact Or.inr rfl
    | ok x => exact k x

theorem catchRefines {a b : Runtime.Result Value} (h : Refines a b) :
    Refines (catchReturn a) (catchReturn b) := by
  rcases h with h | h
  · subst a; exact Or.inl rfl
  · subst a; exact Or.inr rfl

theorem step (n : Nat) :
    (∀ e frames s, Refines (eval n e frames s) (eval (n+1) e frames s)) ∧
    (∀ es frames s, Refines (evalMany n es frames s) (evalMany (n+1) es frames s)) ∧
    (∀ f a s, Refines (call n f a s) (call (n+1) f a s)) := by
  induction n with
  | zero =>
    refine ⟨?_,?_,?_⟩ <;> intros <;> exact Or.inl rfl
  | succ n ih =>
    obtain ⟨he,hm,hc⟩ := ih
    refine ⟨?_,?_,?_⟩
    · intro e frames s
      cases e <;> unfold eval <;> try dsimp only
      all_goals
        repeat
          first
          | exact refl _
          | exact he _ _ _
          | exact hm _ _ _
          | exact hc _ _ _
          | apply bind
          | apply catchRefines
          | (rintro ⟨v,s⟩)
          | (intro x)
          | (split <;> try simp_all only)
    · intro es frames s
      cases es <;> unfold evalMany <;> try dsimp only
      all_goals
        repeat
          first
          | exact refl _
          | exact he _ _ _
          | exact hm _ _ _
          | apply bind
          | (rintro ⟨v,s⟩)
          | (intro x)
    · intro f a s
      unfold call
      dsimp only
      repeat
        first
        | exact refl _
        | exact he _ _ _
        | exact hc _ _ _
        | apply bind
        | apply catchRefines
        | (rintro ⟨v,s⟩)
        | (intro x)
        | (split <;> try simp_all only)

theorem trans {a b c : Except Signal α} (h : Refines a b) (k : Refines b c) : Refines a c := by
  rcases h with h | h
  · exact Or.inl h
  · subst a; exact k

theorem call_mono (n extra : Nat) (f a : Value) (s : State) :
    Refines (call n f a s) (call (n+extra) f a s) := by
  induction extra with
  | zero => exact refl _
  | succ extra ih => exact trans ih ((step (n+extra)).2.2 f a s)

theorem preserves_success {a b : Except Signal α} (h : Refines a b) (ha : a = .ok x) : b = .ok x := by
  rcases h with h | h
  · rw [ha] at h; cases h
  · rw [← h]; exact ha

theorem call_success_unique (n m : Nat) (f a : Value) (s : State) (x y : Value × State)
    (hx : call n f a s = .ok x) (hy : call m f a s = .ok y) : x = y := by
  have first := preserves_success (call_mono n m f a s) hx
  have second := preserves_success (call_mono m n f a s) hy
  rw [Nat.add_comm m n, first] at second
  exact Except.ok.inj second

end Macaulean.M2.Verification.Fuel
