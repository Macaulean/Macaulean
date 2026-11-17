import Macaulean.Interpreter.GCD.Frames
import Macaulean.Verification.RuntimeEnvironment

/-! Effects of expressions that only read their caller's frame. Callee contracts
may allocate private cells, but cannot change the caller's cells or globals. -/
namespace Macaulean.M2.Verification.ExecutionEffects
open Lexical Macaulean.M2.Runtime GCD.Execution
variable {α β : Type}

def Safe (before : State) (result : Runtime.Result α) : Prop :=
  match result with
  | .ok (_,after) => Extends before after
  | .error (.error _) => True
  | .error (.returned ..) => False

theorem Safe.pure (s : State) (value : α) : Safe s (.ok (value,s)) := Extends.refl s

theorem Safe.function (s : State) (f : Function) : Safe s (.ok (s.function f)) :=
  ⟨rfl, ⟨[], by simp⟩⟩

theorem Safe.error (s : State) (error : Error) : Safe s (α := α) (.error (.error error)) :=
  True.intro

theorem Safe.bind {result : Runtime.Result α} {next : α × State → Runtime.Result β}
    (h : Safe s result) (hn : ∀ x t, Extends s t → Safe t (next (x,t))) :
    Safe s (Except.bind result next) := by
  cases result with
  | error e => cases e <;> simp_all [Safe, Except.bind]
  | ok pair =>
    obtain ⟨x,t⟩ := pair
    have nextSafe := hn x t h
    cases hnxt : next (x,t) with
    | error e => cases e <;> simp_all [Safe, Except.bind]
    | ok pair =>
      simp only [Safe, hnxt, Except.bind] at nextSafe ⊢
      exact h.trans nextSafe

theorem Safe.operation (s : State) (result : Except Error α) :
    Safe s (Except.bind (liftResult result) (fun value => Except.ok (value,s))) := by
  cases result with
  | error e => exact Safe.error s e
  | ok value => exact Safe.pure s value

/-- The read-only expression fragment used by source-level search and row
helpers. Calls are restricted to explicit global names with supplied contracts. -/
inductive ReadOnly (names : List String) : Code → Prop where
  | int : ReadOnly names (.int n)
  | read : ReadOnly names (.read ref)
  | unop : ReadOnly names arg → ReadOnly names (.unop op arg)
  | binop : op ≠ .rem → ReadOnly names left → ReadOnly names right → ReadOnly names (.binop op left right)
  | ifElse : ReadOnly names condition → ReadOnly names yes → ReadOnly names no →
      ReadOnly names (.ifElse condition yes no)
  | seq : ReadOnly names first → ReadOnly names second → ReadOnly names (.seq first second)
  | listLit : (∀ e ∈ es, ReadOnly names e) → ReadOnly names (.listLit es)
  | sequence : (∀ e ∈ es, ReadOnly names e) → ReadOnly names (.sequence es)
  | globalCall : name ∈ names → ReadOnly names arg →
      ReadOnly names (.apply (.read (.global name)) arg)

/-- A modular effect contract at all invocation depths up to the current budget. -/
def CallsSafe (depth : Nat) (names : List String) (env : Env) : Prop :=
  ∀ fuel ≤ depth, ∀ name ∈ names, ∀ fn arg s,
    s.env = env → s.env.lookup name = some fn → Safe s (call fuel fn arg s)

theorem evaluate (names : List String) (env : Env) (depth : Nat) :
    (∀ _calls : CallsSafe depth names env, ∀ code, ReadOnly names code →
      ∀ frames s, s.env = env → Safe s (eval depth code frames s)) ∧
    (∀ _calls : CallsSafe depth names env, ∀ codes, (∀ code ∈ codes, ReadOnly names code) →
      ∀ frames s, s.env = env → Safe s (evalMany depth codes frames s)) := by
  induction depth with
  | zero =>
    constructor <;> intros <;> exact Safe.error _ .fuelExhausted
  | succ n ih =>
    have restrict (h : CallsSafe (n+1) names env) : CallsSafe n names env := by
      intro fuel hf
      exact h fuel (by omega)
    constructor
    · intro calls code ro frames s same
      cases ro with
      | int => exact Safe.pure s _
      | read => exact Safe.operation s _
      | unop ha =>
        apply Safe.bind (ih.1 (restrict calls) _ ha frames s same)
        intro value after he
        dsimp only
        split <;> first | exact Safe.function _ _ | exact Safe.operation _ _
      | binop notRem ha hb =>
        apply Safe.bind (ih.1 (restrict calls) _ ha frames s same)
        intro left middle he
        apply Safe.bind (ih.1 (restrict calls) _ hb frames middle (he.env.trans same))
        intro right after he'
        dsimp only
        repeat
          first
          | exact Safe.function _ _
          | exact Safe.operation _ _
          | contradiction
          | split
      | ifElse hc hy hn =>
        apply Safe.bind (ih.1 (restrict calls) _ hc frames s same)
        intro value after he
        dsimp only
        split
        · exact ih.1 (restrict calls) _ hy frames after (he.env.trans same)
        · exact ih.1 (restrict calls) _ hn frames after (he.env.trans same)
        · exact Safe.error _ _
      | seq ha hb =>
        apply Safe.bind (ih.1 (restrict calls) _ ha frames s same)
        intro value after he
        exact ih.1 (restrict calls) _ hb frames after (he.env.trans same)
      | listLit hs =>
        apply Safe.bind (ih.2 (restrict calls) _ hs frames s same)
        intro values after he
        exact Safe.pure after _
      | sequence hs =>
        apply Safe.bind (ih.2 (restrict calls) _ hs frames s same)
        intro values after he
        exact Safe.pure after _
      | @globalCall name arg member ha =>
        cases n with
        | zero => exact Safe.error _ .fuelExhausted
        | succ k =>
          rw [eval, eval]
          simp only [readRef]
          cases lookup : s.env.lookup name with
          | none => simp [liftResult, Except.mapError, bind, Except.bind, Safe]
          | some fn =>
            simp only [liftResult, Except.mapError, bind, Except.bind,
              pure, Except.pure]
            apply Safe.bind (ih.1 (restrict calls) _ ha frames s same)
            intro value after he
            apply calls (k+1) (by omega) name member fn value after (he.env.trans same)
            simpa only [he.env] using lookup
    · intro calls codes ro frames s same
      cases codes with
      | nil => exact Safe.pure s []
      | cons code codes =>
        apply Safe.bind (ih.1 (restrict calls) code (ro code (by simp)) frames s same)
        intro value middle he
        apply Safe.bind (ih.2 (restrict calls) codes (by
          intro c hc
          exact ro c (List.mem_cons_of_mem _ hc)) frames middle (he.env.trans same))
        intro values after he'
        exact Safe.pure after _

theorem Safe.builtin_call (fuel : Nat) (primitive : Polynomials.Primitive)
    (arg : Value) (s : State) : Safe s (call fuel (.algebra (.builtin primitive)) arg s) := by
  cases fuel with
  | zero => exact Safe.error s .fuelExhausted
  | succ fuel => exact Safe.operation s _

theorem Safe.catchReturn (h : Safe s result) : Safe s (Runtime.catchReturn result) := by
  cases result with
  | ok pair => exact h
  | error e => cases e with
    | error e => exact h
    | returned v t => exact False.elim h

theorem Safe.prefix (prior : Extends before s) (h : Safe s result) : Safe before result := by
  cases result with
  | ok pair => exact prior.trans h
  | error e => cases e <;> exact h

/-- A recursive tracked-library function in the read-only fragment preserves
caller cells and globals. Its only other callees are production primitives. -/
theorem library_safe (name : String) (params : Parameters) (slots : Nat) (body : Code)
    (names : List String)
    (source : Library.lookup name = some (.lambda params slots body))
    (readOnly : ReadOnly names body)
    (protectedCalls : ∀ callee ∈ names, callee ∈ protectedNames)
    (selfBinding : prelude.lookup name = some (.algebra (.library name)))
    (callees : ∀ callee ∈ names, callee = name ∨
      ∃ primitive, prelude.lookup callee = some (.algebra (.builtin primitive)))
    (fuel : Nat) (arg : Value) (s : State) (globals : PreludeBindings s) :
    Safe s (call fuel (.algebra (.library name)) arg s) := by
  induction fuel using Nat.strongRecOn generalizing arg s with
  | ind fuel ih =>
    cases fuel with
    | zero => exact Safe.error _ .fuelExhausted
    | succ n =>
      have calls : CallsSafe n names s.env := by
        intro budget hb callee member fn operand state same lookup
        have canonical := globals.of_env_eq same
        have binding := canonical callee (protectedCalls callee member)
        rcases callees callee member with self | ⟨primitive,primitiveBinding⟩
        · subst callee
          rw [selfBinding] at binding
          have fnEq := Option.some.inj (lookup.symm.trans binding)
          subst fn
          exact ih budget (by omega) operand state canonical
        · rw [primitiveBinding] at binding
          have fnEq := Option.some.inj (lookup.symm.trans binding)
          subst fn
          exact Safe.builtin_call _ _ _ _
      cases args : arguments params arg with
      | error e =>
        simp [call, source, args, liftResult, Except.mapError, bind, Except.bind, Safe]
      | ok values =>
        let locals := values ++ List.replicate (slots-values.length) .null
        have evaluation := (evaluate names s.env n).1 calls body readOnly
          [(s.allocate locals).1] (s.allocate locals).2 rfl
        have result := evaluation.catchReturn.prefix (allocate_extends s locals)
        simpa [call, source, args, locals, liftResult, Except.mapError, bind, Except.bind]
          using result

end Macaulean.M2.Verification.ExecutionEffects
