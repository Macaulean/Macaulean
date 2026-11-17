import Macaulean.Verification.GenericProofs
import Macaulean.Interpreter.Groebner

/-!
# A generic proof of the M2 coefficient-row update

The program body is identified with the tracked M2 library by kernel equality.
The result theorem ranges over arbitrary rows, coefficients and runtime states;
scalar operations are exactly the production interpreter's operations.
-/
namespace Macaulean.M2.Verification.RowProgram
open Lexical Macaulean.M2.Runtime

private def slot (i : Nat) : Code := .read (.slot 0 i)
def body : Code :=
  .ifElse (.binop .eq (slot 3) (.unop .length (slot 0))) (.listLit [])
    (.binop .concat
      (.listLit [.binop .sub (.binop .index (slot 0) (slot 3))
        (.binop .mul (slot 1) (.binop .index (slot 2) (slot 3)))])
      (.apply (.read (.global "m2gbSubtractRow"))
        (.sequence [slot 0, slot 1, slot 2, .binop .add (slot 3) (.int 1)])))

theorem source_body : Library.lookup "m2gbSubtractRow" =
    some (.lambda (.fixed ["row","c","other","i"]) 4 body) := rfl

def arg (xs : List Value) (c : Value) (ys : List Value) (i : Nat) : Value :=
  .sequence [.list xs,c,.list ys,.zz i]
def locals (xs : List Value) (c : Value) (ys : List Value) (i : Nat) : List Value :=
  [.list xs,c,.list ys,.zz i]
def allocated (s : State) (xs : List Value) (c : Value) (ys : List Value) (i : Nat) :=
  s.allocate (locals xs c ys i)

private theorem read0 (s : State) (xs ys : List Value) (c : Value) (i : Nat) :
    readRef (.slot 0 0) [(allocated s xs c ys i).1] (allocated s xs c ys i).2 = .ok (.list xs) := by
  simp [allocated, locals, readRef, cellAt, State.allocate, bind, pure, Except.pure]
private theorem read1 (s : State) (xs ys : List Value) (c : Value) (i : Nat) :
    readRef (.slot 0 1) [(allocated s xs c ys i).1] (allocated s xs c ys i).2 = .ok c := by
  simp [allocated, locals, readRef, cellAt, State.allocate, bind, pure, Except.pure]
private theorem read2 (s : State) (xs ys : List Value) (c : Value) (i : Nat) :
    readRef (.slot 0 2) [(allocated s xs c ys i).1] (allocated s xs c ys i).2 = .ok (.list ys) := by
  simp [allocated, locals, readRef, cellAt, State.allocate, bind, pure, Except.pure]
private theorem read3 (s : State) (xs ys : List Value) (c : Value) (i : Nat) :
    readRef (.slot 0 3) [(allocated s xs c ys i).1] (allocated s xs c ys i).2 = .ok (.zz i) := by
  simp [allocated, locals, readRef, cellAt, State.allocate, bind, pure, Except.pure]

private theorem eq_nat (i j : Nat) : evalBinOp .eq (.zz i) (.zz j) = .ok (.bool (i == j)) := by
  simp [evalBinOp, Value.toRat?, Rat.intCast_inj, Int.natCast_inj]
  rfl
private theorem add_one (i : Nat) : evalBinOp .add (.zz i) (.zz 1) = .ok (.zz (i+1)) := by
  simp [evalBinOp]
private theorem len (xs : List Value) : evalUnOp .length (.list xs) = .ok (.zz xs.length) := rfl
private theorem index (xs : List Value) (i : Nat) (v : Value) (h : xs[i]? = some v) :
    evalBinOp .index (.list xs) (.zz i) = .ok v := by
  have hi : i < xs.length := (List.getElem?_eq_some_iff.mp h).1
  have hnonneg : ¬ (i : Int) < 0 := by omega
  have hbound : (0 : Int) ≤ i ∧ (i : Int) < xs.length := by omega
  simp [evalBinOp, indexValue, normalizedIndex, hnonneg, hbound, h, pure, Except.pure]

theorem stop (fuel : Nat) (xs ys : List Value) (c : Value) (s : State) :
    Runtime.call (fuel+16) (.algebra (.library "m2gbSubtractRow")) (arg xs c ys xs.length) s =
      .ok (.list [], (allocated s xs c ys xs.length).2) := by
  rw [Groebner.library_call (fuel+15) "m2gbSubtractRow" (.fixed ["row","c","other","i"])
    4 body (arg xs c ys xs.length) (locals xs c ys xs.length) s source_body (by rfl)]
  change catchReturn (eval (fuel+15) body [(allocated s xs c ys xs.length).1]
    (allocated s xs c ys xs.length).2) = _
  simp [body, slot, eval, evalMany, read0, read3, len, eq_nat,
    liftResult, Except.mapError, bind, Except.bind, pure, Except.pure, catchReturn]

theorem step (fuel : Nat) (xs ys : List Value) (c : Value) (s : State) (i : Nat)
    (x y product z : Value) (rest : List Value) (after : State)
    (hi : i ≠ xs.length) (hx : xs[i]? = some x) (hy : ys[i]? = some y)
    (hm : evalBinOp .mul c y = .ok product) (hs : evalBinOp .sub x product = .ok z)
    (hg : s.env.lookup "m2gbSubtractRow" = some (.algebra (.library "m2gbSubtractRow")))
    (hr : Runtime.call (fuel+12) (.algebra (.library "m2gbSubtractRow"))
      (arg xs c ys (i+1)) (allocated s xs c ys i).2 = .ok (.list rest,after)) :
    Runtime.call (fuel+16) (.algebra (.library "m2gbSubtractRow")) (arg xs c ys i) s =
      .ok (.list (z::rest),after) := by
  rw [Groebner.library_call (fuel+15) "m2gbSubtractRow" (.fixed ["row","c","other","i"])
    4 body (arg xs c ys i) (locals xs c ys i) s source_body (by rfl)]
  change catchReturn (eval (fuel+15) body [(allocated s xs c ys i).1]
    (allocated s xs c ys i).2) = _
  have global : readRef (.global "m2gbSubtractRow") [(allocated s xs c ys i).1]
      (allocated s xs c ys i).2 = .ok (.algebra (.library "m2gbSubtractRow")) := by
    simp [readRef, allocated, State.allocate, hg]
  have hne : (i == xs.length) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    exact hi (beq_iff_eq.mp h)
  have recursive : Runtime.call (fuel+12) (.algebra (.library "m2gbSubtractRow"))
      (.sequence [.list xs,c,.list ys,.zz ((i : Int)+1)])
      (allocated s xs c ys i).2 = .ok (.list rest,after) := by
    simpa [arg] using hr
  have concat : evalBinOp .concat (.list [z]) (.list rest) = .ok (.list (z::rest)) := rfl
  simp [body, slot, eval, evalMany, read0, read1, read2, read3, len, eq_nat,
    hne, index xs i x hx, index ys i y hy, hm, hs, global, add_one,
    liftResult, Except.mapError, bind, Except.bind, pure, Except.pure,
    recursive, concat, catchReturn]

/-- Each output entry is the actual production subtraction of the scaled entry.
No arithmetic correctness axiom is introduced by this relation. -/
inductive Updates (c : Value) : List Value → List Value → List Value → Prop where
  | nil : Updates c [] [] []
  | cons {x y product z : Value} {xs ys zs : List Value} (hm : evalBinOp .mul c y = .ok product)
      (hs : evalBinOp .sub x product = .ok z)
      (tail : Updates c xs ys zs) : Updates c (x::xs) (y::ys) (z::zs)

theorem Updates.lengths (h : Updates c xs ys zs) : xs.length = ys.length ∧ xs.length = zs.length := by
  induction h with
  | nil => simp
  | cons _ _ _ ih => simp only [List.length_cons]; omega

structure AllocatesOnly (before after : State) : Prop where
  env : after.env = before.env
  cells : ∃ fresh, after.heap.cells = before.heap.cells ++ fresh
  functions : after.heap.functions = before.heap.functions
  nextRing : after.heap.nextRing = before.heap.nextRing

theorem AllocatesOnly.allocate (s : State) (vs : List Value) : AllocatesOnly s (s.allocate vs).2 :=
  ⟨rfl, ⟨vs,rfl⟩, rfl, rfl⟩

theorem AllocatesOnly.trans {a b c : State} (h : AllocatesOnly a b) (k : AllocatesOnly b c) :
    AllocatesOnly a c := by
  obtain ⟨xs,hxs⟩ := h.cells
  obtain ⟨ys,hys⟩ := k.cells
  exact ⟨k.env.trans h.env, ⟨xs++ys, by rw [hys,hxs,List.append_assoc]⟩,
    k.functions.trans h.functions, k.nextRing.trans h.nextRing⟩

/-- Generic execution of a suffix of the actual M2 program. The fuel bound is
linear in the result length; the output is not a single concrete test vector. -/
theorem execute_suffix (c : Value) (tailX tailY result : List Value)
    (updates : Updates c tailX tailY result) :
    ∀ (xs ys : List Value) (i : Nat), xs.drop i = tailX → ys.drop i = tailY →
      i ≤ xs.length → xs.length = ys.length → ∀ (s : State) (spare : Nat),
      s.env.lookup "m2gbSubtractRow" = some (.algebra (.library "m2gbSubtractRow")) →
      ∃ after, Runtime.call (spare + 16 * (result.length+1))
        (.algebra (.library "m2gbSubtractRow")) (arg xs c ys i) s = .ok (.list result,after) ∧
        AllocatesOnly s after := by
  induction updates with
  | nil =>
    intro xs ys i hx _ hi _ s spare _
    have stopAt : i = xs.length := by
      have := List.drop_eq_nil_iff.mp hx
      omega
    subst i
    exact ⟨(allocated s xs c ys xs.length).2, by simpa using stop spare xs ys c s,
      AllocatesOnly.allocate s _⟩
  | @cons x y product z tx ty zs hm hs updates ih =>
    intro xs ys i hx hy hi same s spare global
    have hxi : xs[i]? = some x := by
      have h := congrArg (fun l : List Value => l[0]?) hx
      simpa using h
    have hyi : ys[i]? = some y := by
      have h := congrArg (fun l : List Value => l[0]?) hy
      simpa using h
    have lt : i < xs.length := (List.getElem?_eq_some_iff.mp hxi).1
    have nextX : xs.drop (i+1) = tx := by
      have h := congrArg (List.drop 1) hx
      simpa [List.drop_drop, Nat.add_comm] using h
    have nextY : ys.drop (i+1) = ty := by
      have h := congrArg (List.drop 1) hy
      simpa [List.drop_drop, Nat.add_comm] using h
    obtain ⟨after,hr,he⟩ := ih xs ys (i+1) nextX nextY (by omega) same
      (allocated s xs c ys i).2 (spare+12) (by simpa [allocated, State.allocate] using global)
    refine ⟨after, ?_, (AllocatesOnly.allocate s _).trans he⟩
    have recursion : Runtime.call ((spare + 16*(zs.length+1))+12)
        (.algebra (.library "m2gbSubtractRow")) (arg xs c ys (i+1))
        (allocated s xs c ys i).2 = .ok (.list zs,after) := by
      have eq : spare + 16*(zs.length+1)+12 = spare+12+16*(zs.length+1) := by omega
      rw [eq]; exact hr
    have result := step (spare + 16*(zs.length+1)) xs ys c s i x y product z zs after
      (by omega) hxi hyi hm hs global recursion
    have eq : spare + 16*((z::zs).length+1) = spare + 16*(zs.length+1)+16 := by
      simp only [List.length_cons]; omega
    rw [eq]; exact result

/-- At entry index zero, arbitrary valid rows terminate and produce exactly their
pointwise production update. All old cells, functions, globals and ring IDs remain
unchanged; fresh internal frames are permitted. -/
theorem execute (updates : Updates c xs ys zs) (s : State) (spare : Nat)
    (global : s.env.lookup "m2gbSubtractRow" = some (.algebra (.library "m2gbSubtractRow"))) :
    ∃ after, Runtime.call (spare + 16*(zs.length+1))
      (.algebra (.library "m2gbSubtractRow")) (arg xs c ys 0) s = .ok (.list zs,after) ∧
      AllocatesOnly s after :=
  execute_suffix c xs ys zs updates xs ys 0 (by simp) (by simp) (by omega)
    updates.lengths.1 s spare global

end Macaulean.M2.Verification.RowProgram
