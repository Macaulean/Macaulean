import Macaulean.Interpreter.Runtime

/-!
# Checked polynomial-interface laws

The round-trip and bridge theorems connect runtime coefficient/exponent lists to
Macaulean's dependent sparse polynomials and the structural kernel evaluator. These are representation and
execution contracts, not Gröbner-basis or termination theorems.
-/
namespace Macaulean.M2.Polynomials

/-- Encoding never forgets or fabricates a dependent exponent-vector witness. -/
theorem decodeTerms_encode (ts : List (Macaulean.PolyTerm Rat n)) :
    decodeTerms n (ts.map fun t => (t.coefficient,t.monomial.powers)) = .ok ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    rcases t with ⟨c, powers, h⟩
    simp [decodeTerms, h, ih, bind, Except.bind, pure, Except.pure]

theorem decode_encode (p : Macaulean.Polynomial Rat n) :
    decode n (encode p) = .ok p := by
  cases p with
  | mk ts => simp [decode, encode, decodeTerms_encode, Functor.map, Except.map]

theorem encode_injective (p q : Macaulean.Polynomial Rat n)
    (h : encode p = encode q) : p = q := by
  have h' := congrArg (decode n) h
  simpa [decode_encode] using h'

theorem encode_dimension (p : Macaulean.Polynomial Rat n) (t : Rat × List Nat)
    (h : t ∈ encode p) : t.2.length = n := by
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp h
  exact a.monomial.powers_length

theorem normalize_bridge (p : Macaulean.Polynomial Rat n) :
    normalized n (encode p) = .ok (encode (KernelPolynomial.normalize p)) := by
  simp [normalized, decode_encode, bind, Except.bind, pure, Except.pure]

theorem unary_bridge (p : Macaulean.Polynomial Rat n)
    (f : Macaulean.Polynomial Rat n → Macaulean.Polynomial Rat n) :
    unary n f (encode p) = .ok (encode (KernelPolynomial.normalize (f p))) := by
  simp [unary, decode_encode, bind, Except.bind, pure, Except.pure]

theorem binary_bridge (p q : Macaulean.Polynomial Rat n)
    (f : Macaulean.Polynomial Rat n → Macaulean.Polynomial Rat n → Macaulean.Polynomial Rat n) :
    binary n f (encode p) (encode q) = .ok (encode
      (KernelPolynomial.normalize (f (KernelPolynomial.normalize p)
        (KernelPolynomial.normalize q)))) := by
  simp [binary, decode_encode, bind, Except.bind, pure, Except.pure]

theorem add_bridge (p q : Macaulean.Polynomial Rat n) :
    add n (encode p) (encode q) = .ok (encode (KernelPolynomial.normalize
      (KernelPolynomial.add (KernelPolynomial.normalize p) (KernelPolynomial.normalize q)))) :=
  binary_bridge p q KernelPolynomial.add

theorem mul_bridge (p q : Macaulean.Polynomial Rat n) :
    mul n (encode p) (encode q) = .ok (encode (KernelPolynomial.normalize
      (KernelPolynomial.mul (KernelPolynomial.normalize p) (KernelPolynomial.normalize q)))) :=
  binary_bridge p q KernelPolynomial.mul

theorem constant_zero (n : Nat) : constant n 0 = [] := by simp [constant]

theorem generator_dimension (n i : Nat) :
    (generator n i).all (fun t => t.2.length == n) = true := by
  simp [generator]

theorem divides_refl (a : List Nat) : divides a a = true := by
  induction a with
  | nil => rfl
  | cons x xs ih => simpa [divides] using ih

theorem divides_same_dimension (a b : List Nat) (h : divides a b = true) :
    a.length = b.length := by
  simp only [divides, Bool.and_eq_true] at h
  exact of_decide_eq_true h.1

theorem divides_wrong_dimension (a b : List Nat) (h : a.length ≠ b.length) :
    divides a b = false := by simp [divides, h]

/-- A native polynomial implementation cannot be smuggled into primitive execution. -/
theorem primitive_call_success (fuel : Nat) (p : Primitive) (a v : Value)
    (s : Runtime.State) (h : callPrimitive p a = .ok v) :
    Runtime.call (fuel+1) (.algebra (.builtin p)) a s = .ok (v,s) := by
  simp [Runtime.call, h, Runtime.liftResult, Except.mapError, bind, Except.bind,
    pure, Except.pure]

/-- Bracket names do not create lexical locals or change capture resolution. -/
theorem resolve_ring_scope (a : Term) (names : List String) (r : Lexical.Resolver) :
    (Lexical.resolve (.polyRing a names) r).2 = (Lexical.resolve a r).2 := by
  simp only [Lexical.resolve]

end Macaulean.M2.Polynomials
