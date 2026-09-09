/-
  Packing a monomial's exponent vector into a single `Nat` key.

  A monomial `x₀^e₀ ⋯ x_{n-1}^e_{n-1}` is stored as the base-`b` numeral whose
  little-endian digits are the *partial sums*

      S₁ = e₀,  S₂ = e₀+e₁,  …,  Sₙ = e₀+⋯+e_{n-1} = total degree,

  so the most significant digit is the total degree.  Two facts make this the
  right packing:

  * partial sums are additive, so multiplying monomials is `key₁ + key₂`
    (`encodeFrom_add`), a single kernel `Nat.add`; and
  * comparing the keys as `Nat`s is exactly **grevlex** (`compare_encodeKey`) --
    degree first, then reverse-lexicographic with the swap -- so ordering a
    monomial is a single kernel `Nat.blt`.

  Both facts hold as long as no digit overflows, i.e. as long as the total
  degree stays below `b`.  Nothing here is about soundness: the callers carry
  the degree bound as an explicit hypothesis, and check it with `Nat.blt`.
-/

namespace Macaulean
namespace Mon

/-! ## Digit width -/

/-- Bits per digit for `n` variables.  At least 8 (so degrees up to 255 always
fit), and small enough that an `n`-digit key stays below `2^62` -- Lean's small
`Nat` fast path -- whenever `n ≤ 7`. -/
def bits (n : Nat) : Nat := max 8 (62 / max 1 n)

/-- Digit base for `n` variables: a power of two, so the kernel's digit
arithmetic is GMP shifts and masks. -/
def base (n : Nat) : Nat := 2 ^ bits n

theorem base_ge (n : Nat) : 256 ≤ base n := by
  have h : 8 ≤ bits n := Nat.le_max_left _ _
  calc (256 : Nat) = 2 ^ 8 := by decide
    _ ≤ 2 ^ bits n := Nat.pow_le_pow_right (by omega) h

theorem base_pos (n : Nat) : 0 < base n := by have := base_ge n; omega

theorem one_lt_base (n : Nat) : 1 < base n := by have := base_ge n; omega

/-- `base n ^ n < 2 ^ 62` -- the packed key stays on Lean's small-`Nat` path.
The tactic checks this natively before emitting a certificate. -/
def fitsFast (n : Nat) : Bool := base n ^ n < 2 ^ 62

/-! ## Encoding -/

/-- Base-`b` little-endian numeral. -/
def fromDigits (b : Nat) : List Nat → Nat
  | [] => 0
  | d :: ds => d + b * fromDigits b ds

/-- Partial sums of `p`, each offset by `prev`. -/
def psumsFrom : Nat → List Nat → List Nat
  | _, [] => []
  | prev, e :: es => (prev + e) :: psumsFrom (prev + e) es

/-- Partial sums `[e₀, e₀+e₁, …]`. -/
abbrev psums (p : List Nat) : List Nat := psumsFrom 0 p

/-- The packed key of `p`, with every partial sum offset by `prev`. -/
def encodeFrom (b : Nat) : Nat → List Nat → Nat
  | _, [] => 0
  | prev, e :: es => (prev + e) + b * encodeFrom b (prev + e) es

/-- The packed key of an exponent vector. -/
def encodeKey (b : Nat) (p : List Nat) : Nat := encodeFrom b 0 p

/-- Recover `len` exponents from a key, `prev` being the partial sum already
consumed.  Truncated subtraction makes this total; it inverts `encodeFrom`
exactly when no digit overflowed (`decodeFrom_encodeFrom`). -/
def decodeFrom (b : Nat) : Nat → Nat → Nat → List Nat
  | 0, _, _ => []
  | len + 1, prev, k => (k % b - prev) :: decodeFrom b len (k % b) (k / b)

/-- Recover `len` exponents from a key. -/
def decodeKey (b : Nat) (len : Nat) (k : Nat) : List Nat := decodeFrom b len 0 k

/-! ## Basic shape lemmas -/

@[simp] theorem fromDigits_nil (b : Nat) : fromDigits b [] = 0 := rfl
@[simp] theorem fromDigits_cons (b d : Nat) (ds : List Nat) :
    fromDigits b (d :: ds) = d + b * fromDigits b ds := rfl
@[simp] theorem psumsFrom_nil (prev : Nat) : psumsFrom prev [] = [] := rfl
@[simp] theorem psumsFrom_cons (prev e : Nat) (es : List Nat) :
    psumsFrom prev (e :: es) = (prev + e) :: psumsFrom (prev + e) es := rfl

@[simp] theorem decodeFrom_zero (b prev k : Nat) : decodeFrom b 0 prev k = [] := rfl

@[simp] theorem decodeFrom_succ (b len prev k : Nat) :
    decodeFrom b (len + 1) prev k = (k % b - prev) :: decodeFrom b len (k % b) (k / b) := rfl

@[simp] theorem decodeFrom_length (b len prev k : Nat) :
    (decodeFrom b len prev k).length = len := by
  induction len generalizing prev k with
  | zero => rfl
  | succ len ih => simp [decodeFrom, ih]

@[simp] theorem decodeKey_length (b len k : Nat) : (decodeKey b len k).length = len := by
  simp [decodeKey]

@[simp] theorem encodeFrom_nil (b prev : Nat) : encodeFrom b prev [] = 0 := rfl

@[simp] theorem encodeFrom_cons (b prev e : Nat) (es : List Nat) :
    encodeFrom b prev (e :: es) = (prev + e) + b * encodeFrom b (prev + e) es := rfl

@[simp] theorem encodeKey_nil (b : Nat) : encodeKey b [] = 0 := rfl

/-- Decoding the zero key gives the zero exponent vector. -/
theorem decodeFrom_zero_key (b len : Nat) : decodeFrom b len 0 0 = List.replicate len 0 := by
  induction len with
  | zero => rfl
  | succ len ih => simp [decodeFrom, List.replicate_succ, ih]

theorem encodeFrom_replicate_zero (b len : Nat) :
    encodeFrom b 0 (List.replicate len 0) = 0 := by
  induction len with
  | zero => rfl
  | succ len ih => simp [List.replicate_succ, ih]

theorem encodeKey_replicate_zero (b len : Nat) :
    encodeKey b (List.replicate len 0) = 0 :=
  encodeFrom_replicate_zero b len

/-! ## Additivity: multiplying monomials is adding keys -/

theorem encodeFrom_add (b : Nat) :
    ∀ (p q : List Nat), p.length = q.length → ∀ (i j : Nat),
      encodeFrom b i p + encodeFrom b j q = encodeFrom b (i + j) (List.zipWith (· + ·) p q) := by
  intro p
  induction p with
  | nil => intro q hq i j; cases q <;> simp_all
  | cons e es ih =>
    intro q hq i j
    cases q with
    | nil => simp at hq
    | cons f fs =>
      have hlen : es.length = fs.length := by simpa using hq
      have := ih fs hlen (i + e) (j + f)
      simp only [encodeFrom_cons, List.zipWith_cons_cons]
      have harg : i + j + (e + f) = i + e + (j + f) := by omega
      rw [harg, ← this, Nat.mul_add]
      omega

/-- The key of a product is the sum of the keys. -/
theorem encodeKey_add (b : Nat) (p q : List Nat) (h : p.length = q.length) :
    encodeKey b p + encodeKey b q = encodeKey b (List.zipWith (· + ·) p q) := by
  simpa [encodeKey] using encodeFrom_add b p q h 0 0

/-! ## Decoding inverts encoding below the digit bound -/

theorem decodeFrom_encodeFrom (b : Nat) (hb : 0 < b) :
    ∀ (p : List Nat) (len prev : Nat), p.length = len → prev + p.sum < b →
      decodeFrom b len prev (encodeFrom b prev p) = p := by
  intro p
  induction p with
  | nil => intro len prev hlen _; cases len <;> simp_all
  | cons e es ih =>
    intro len prev hlen hlt
    cases len with
    | zero => simp at hlen
    | succ len =>
      have hlen' : es.length = len := by simpa using hlen
      have hsum : prev + e + es.sum < b := by simp [List.sum_cons] at hlt; omega
      have hpe : prev + e < b := by omega
      have hmod : ((prev + e) + b * encodeFrom b (prev + e) es) % b = prev + e := by
        rw [Nat.add_mul_mod_self_left]
        exact Nat.mod_eq_of_lt hpe
      have hdiv : ((prev + e) + b * encodeFrom b (prev + e) es) / b
          = encodeFrom b (prev + e) es := by
        rw [Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt hpe]
        omega
      simp only [encodeFrom_cons, decodeFrom_succ, hmod, hdiv]
      rw [ih len (prev + e) hlen' hsum]
      simp

theorem decodeKey_encodeKey (b : Nat) (hb : 0 < b) (p : List Nat) (len : Nat)
    (hlen : p.length = len) (hsum : p.sum < b) :
    decodeKey b len (encodeKey b p) = p :=
  decodeFrom_encodeFrom b hb p len 0 hlen (by omega)

/-! ## Checking a key without decoding it

Whether a key really is the packing of its own exponent vector is a property of
its *digits*: they must be non-decreasing (partial sums are), and there must be
no more than `len` of them.  `wfFrom` checks exactly that with one walk down the
key -- `len` GMP divisions and comparisons, no list -- where decoding and
re-encoding costs three walks and allocates two lists.  `topFrom` reads off the
same walk's last digit, which is the monomial's total degree.

The reflective checker runs both at every product (`Polynomial.mulOk`), so they
are on the hot path; `wfFrom_iff_encodeFrom` and `sum_decodeFrom_eq_topFrom`
say they agree with the decoding definitions.
-/

/-- `k` is the packing of `len` further exponents, the partial sums starting
from `prev`. -/
def wfFrom (b : Nat) : Nat → Nat → Nat → Bool
  | 0, _, k => Nat.beq k 0
  | len + 1, prev, k => Nat.ble prev (k % b) && wfFrom b len (k % b) (k / b)

/-- The last digit of the same walk: the total degree of the packed monomial. -/
def topFrom (b : Nat) : Nat → Nat → Nat → Nat
  | 0, prev, _ => prev
  | len + 1, _, k => topFrom b len (k % b) (k / b)

@[simp] theorem wfFrom_zero (b prev k : Nat) : wfFrom b 0 prev k = Nat.beq k 0 := rfl

@[simp] theorem wfFrom_succ (b len prev k : Nat) :
    wfFrom b (len + 1) prev k = (Nat.ble prev (k % b) && wfFrom b len (k % b) (k / b)) := rfl

@[simp] theorem topFrom_zero (b prev k : Nat) : topFrom b 0 prev k = prev := rfl

@[simp] theorem topFrom_succ (b len prev k : Nat) :
    topFrom b (len + 1) prev k = topFrom b len (k % b) (k / b) := rfl

/-- The walk's last digit is a digit, so it is below the base. -/
theorem topFrom_lt (b : Nat) (hb : 0 < b) :
    ∀ (len prev k : Nat), prev < b → topFrom b len prev k < b := by
  intro len
  induction len with
  | zero => intro prev k h; exact h
  | succ len ih => intro prev k _; exact ih _ _ (Nat.mod_lt _ hb)

/-- On a key the walk accepts, the decoded exponents sum to the last digit --
that is, the total degree is the top digit, without decoding. -/
theorem sum_decodeFrom_eq_topFrom (b : Nat) :
    ∀ (len prev k : Nat), wfFrom b len prev k = true →
      prev + (decodeFrom b len prev k).sum = topFrom b len prev k := by
  intro len
  induction len with
  | zero => intro prev k _; simp
  | succ len ih =>
    intro prev k h
    rw [wfFrom_succ, Bool.and_eq_true] at h
    have hle : prev ≤ k % b := Nat.le_of_ble_eq_true h.1
    rw [decodeFrom_succ, topFrom_succ, List.sum_cons, ← ih _ _ h.2]
    omega

/-- On a key the walk accepts, re-encoding the decoded exponents gives the key
back: the walk is exactly the faithfulness of the packing. -/
theorem encodeFrom_decodeFrom (b : Nat) (hb : 0 < b) :
    ∀ (len prev k : Nat), wfFrom b len prev k = true →
      encodeFrom b prev (decodeFrom b len prev k) = k := by
  intro len
  induction len with
  | zero =>
    intro prev k h
    simp only [wfFrom_zero] at h
    rw [decodeFrom_zero, encodeFrom_nil]
    exact (Nat.eq_of_beq_eq_true h).symm
  | succ len ih =>
    intro prev k h
    rw [wfFrom_succ, Bool.and_eq_true] at h
    have hle : prev ≤ k % b := Nat.le_of_ble_eq_true h.1
    have hprev : prev + (k % b - prev) = k % b := by omega
    rw [decodeFrom_succ, encodeFrom_cons, hprev, ih _ _ h.2]
    exact Nat.mod_add_div k b

/-- Conversely, the walk accepts every faithfully packed key. -/
theorem wfFrom_encodeFrom (b : Nat) (hb : 0 < b) :
    ∀ (p : List Nat) (len prev : Nat), p.length = len → prev + p.sum < b →
      wfFrom b len prev (encodeFrom b prev p) = true := by
  intro p
  induction p with
  | nil => intro len prev hlen _; cases len <;> simp_all
  | cons e es ih =>
    intro len prev hlen hlt
    cases len with
    | zero => simp at hlen
    | succ len =>
      have hlen' : es.length = len := by simpa using hlen
      have hsum : prev + e + es.sum < b := by simp [List.sum_cons] at hlt; omega
      have hpe : prev + e < b := by omega
      have hmod : ((prev + e) + b * encodeFrom b (prev + e) es) % b = prev + e := by
        rw [Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt hpe
      have hdiv : ((prev + e) + b * encodeFrom b (prev + e) es) / b
          = encodeFrom b (prev + e) es := by
        rw [Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt hpe]; omega
      rw [encodeFrom_cons, wfFrom_succ, hmod, hdiv, ih len (prev + e) hlen' hsum]
      simp [Nat.ble_eq_true_of_le (Nat.le_add_right prev e)]

/-! ## Comparing keys is grevlex -/

theorem compare_add_right (a c k : Nat) : compare (a + k) (c + k) = compare a c := by
  rcases h : compare a c with _ | _ | _
  · exact Nat.compare_eq_lt.mpr (by have := Nat.compare_eq_lt.mp h; omega)
  · exact Nat.compare_eq_eq.mpr (by have := Nat.compare_eq_eq.mp h; omega)
  · exact Nat.compare_eq_gt.mpr (by have := Nat.compare_eq_gt.mp h; omega)

theorem compare_digit {b l₁ l₂ r₁ r₂ : Nat} (h₁ : l₁ < b) (h₂ : l₂ < b) :
    compare (l₁ + b * r₁) (l₂ + b * r₂) = (compare r₁ r₂).then (compare l₁ l₂) := by
  rcases hr : compare r₁ r₂ with _ | _ | _
  · have hlt : r₁ < r₂ := Nat.compare_eq_lt.mp hr
    have hle : b * (r₁ + 1) ≤ b * r₂ := Nat.mul_le_mul_left b hlt
    have : l₁ + b * r₁ < l₂ + b * r₂ := by
      have : b * (r₁ + 1) = b * r₁ + b := by rw [Nat.mul_succ]
      omega
    simp [Nat.compare_eq_lt.mpr this, Ordering.then]
  · have hre : r₁ = r₂ := Nat.compare_eq_eq.mp hr
    subst hre
    simp only [Ordering.eq_then]
    exact compare_add_right l₁ l₂ (b * r₁)
  · have hgt : r₂ < r₁ := Nat.compare_eq_gt.mp hr
    have hle : b * (r₂ + 1) ≤ b * r₁ := Nat.mul_le_mul_left b hgt
    have : l₂ + b * r₂ < l₁ + b * r₁ := by
      have : b * (r₂ + 1) = b * r₂ + b := by rw [Nat.mul_succ]
      omega
    simp [Nat.compare_eq_gt.mpr this, Ordering.then]

theorem compare_append_singleton :
    ∀ (u v : List Nat), u.length = v.length → ∀ (a c : Nat),
      compare (u ++ [a]) (v ++ [c]) = (compare u v).then (compare a c) := by
  intro u
  induction u with
  | nil =>
    intro v hv a c
    cases v with
    | nil =>
      show compare [a] [c] = (compare ([] : List Nat) []).then (compare a c)
      rw [List.compare_cons_cons]
      cases compare a c <;> rfl
    | cons => simp at hv
  | cons x xs ih =>
    intro v hv a c
    cases v with
    | nil => simp at hv
    | cons y ys =>
      have hlen : xs.length = ys.length := by simpa using hv
      rw [List.cons_append, List.cons_append, List.compare_cons_cons, ih ys hlen a c,
        List.compare_cons_cons]
      cases compare x y <;> rfl

theorem compare_fromDigits (b : Nat) :
    ∀ (ds₁ ds₂ : List Nat), ds₁.length = ds₂.length →
      (∀ d ∈ ds₁, d < b) → (∀ d ∈ ds₂, d < b) →
      compare (fromDigits b ds₁) (fromDigits b ds₂) = compare ds₁.reverse ds₂.reverse := by
  intro ds₁
  induction ds₁ with
  | nil =>
    intro ds₂ h _ _
    cases ds₂ with
    | nil => simp [fromDigits]
    | cons => simp at h
  | cons d₁ t₁ ih =>
    intro ds₂ h hb₁ hb₂
    cases ds₂ with
    | nil => simp at h
    | cons d₂ t₂ =>
      have hlen : t₁.length = t₂.length := by simpa using h
      have hd₁ : d₁ < b := hb₁ d₁ (by simp)
      have hd₂ : d₂ < b := hb₂ d₂ (by simp)
      have ht₁ : ∀ d ∈ t₁, d < b := fun d hd => hb₁ d (by simp [hd])
      have ht₂ : ∀ d ∈ t₂, d < b := fun d hd => hb₂ d (by simp [hd])
      show compare (d₁ + b * fromDigits b t₁) (d₂ + b * fromDigits b t₂) = _
      rw [compare_digit hd₁ hd₂, ih t₂ hlen ht₁ ht₂]
      rw [List.reverse_cons, List.reverse_cons,
        compare_append_singleton _ _ (by simpa using hlen)]

/-! ### The partial-sum digit list, read from the top, is grevlex -/

/-- Suffix sums: the `i`-th entry is the sum of the elements from `i` on. -/
def sufSums : List Nat → List Nat
  | [] => []
  | a :: t => (a + t.sum) :: sufSums t

@[simp] theorem sufSums_nil : sufSums [] = [] := rfl
@[simp] theorem sufSums_cons (a : Nat) (t : List Nat) :
    sufSums (a :: t) = (a + t.sum) :: sufSums t := rfl

theorem psumsFrom_eq_map :
    ∀ (p : List Nat) (prev : Nat), psumsFrom prev p = (psums p).map (prev + ·) := by
  intro p
  induction p with
  | nil => intro _; rfl
  | cons e es ih =>
    intro prev
    rw [psumsFrom_cons, ih (prev + e)]
    show _ = ((0 + e) :: psumsFrom (0 + e) es).map (prev + ·)
    rw [ih (0 + e), List.map_cons, List.map_map]
    have hhead : prev + e = prev + (0 + e) := by omega
    rw [← hhead]
    congr 1
    apply List.map_congr_left
    intro x _
    simp only [Function.comp_apply]
    omega

theorem sufSums_append_singleton :
    ∀ (u : List Nat) (e : Nat), sufSums (u ++ [e]) = (sufSums u).map (e + ·) ++ [e] := by
  intro u
  induction u with
  | nil => intro e; simp [sufSums]
  | cons a t ih =>
    intro e
    rw [List.cons_append, sufSums_cons, ih e, sufSums_cons, List.map_cons, List.cons_append]
    congr 1
    simp only [List.sum_append, List.sum_cons, List.sum_nil]
    omega

theorem reverse_psums :
    ∀ (p : List Nat), (psums p).reverse = sufSums p.reverse := by
  intro p
  induction p with
  | nil => rfl
  | cons e es ih =>
    show ((0 + e) :: psumsFrom (0 + e) es).reverse = _
    rw [psumsFrom_eq_map es (0 + e), List.reverse_cons, ← List.map_reverse, ih,
      List.reverse_cons, sufSums_append_singleton]
    simp

theorem compare_sufSums :
    ∀ (q₁ q₂ : List Nat), q₁.length = q₂.length →
      compare (sufSums q₁) (sufSums q₂)
        = (compare q₁.sum q₂.sum).then ((compare q₁ q₂).swap) := by
  intro q₁
  induction q₁ with
  | nil =>
    intro q₂ h
    cases q₂ with
    | nil => simp [sufSums]
    | cons => simp at h
  | cons a₁ t₁ ih =>
    intro q₂ h
    cases q₂ with
    | nil => simp at h
    | cons a₂ t₂ =>
      have hlen : t₁.length = t₂.length := by simpa using h
      simp only [sufSums_cons, List.compare_cons_cons, List.sum_cons]
      rw [ih t₂ hlen]
      rcases htop : compare (a₁ + t₁.sum) (a₂ + t₂.sum) with _ | _ | _
      · simp [Ordering.then]
      · have heq : a₁ + t₁.sum = a₂ + t₂.sum := Nat.compare_eq_eq.mp htop
        have hsum : compare t₁.sum t₂.sum = (compare a₁ a₂).swap := by
          rcases ha : compare a₁ a₂ with _ | _ | _
          · have : a₁ < a₂ := Nat.compare_eq_lt.mp ha
            simp [Ordering.swap, Nat.compare_eq_gt.mpr (by omega : t₂.sum < t₁.sum)]
          · have : a₁ = a₂ := Nat.compare_eq_eq.mp ha
            simp [Ordering.swap, Nat.compare_eq_eq.mpr (by omega : t₁.sum = t₂.sum)]
          · have : a₂ < a₁ := Nat.compare_eq_gt.mp ha
            simp [Ordering.swap, Nat.compare_eq_lt.mpr (by omega : t₁.sum < t₂.sum)]
        rw [hsum]
        simp only [Ordering.eq_then]
        rw [Ordering.swap_then]
      · simp [Ordering.then]

/-! ### Putting it together -/

theorem encodeFrom_eq_fromDigits (b : Nat) :
    ∀ (prev : Nat) (p : List Nat), encodeFrom b prev p = fromDigits b (psumsFrom prev p) := by
  intro prev p
  induction p generalizing prev with
  | nil => rfl
  | cons e es ih =>
    rw [encodeFrom_cons, psumsFrom_cons, fromDigits_cons, ih (prev + e)]

theorem mem_psums_le : ∀ (p : List Nat) (d : Nat), d ∈ psums p → d ≤ p.sum := by
  have key : ∀ (p : List Nat) (prev d : Nat), d ∈ psumsFrom prev p → d ≤ prev + p.sum := by
    intro p
    induction p with
    | nil => intro prev d hd; simp [psumsFrom] at hd
    | cons e es ih =>
      intro prev d hd
      rcases List.mem_cons.mp hd with h | h
      · subst h; simp only [List.sum_cons]; omega
      · have := ih (prev + e) d h
        simp only [List.sum_cons]; omega
  intro p d hd
  simpa using key p 0 d hd

/--
**Comparing packed keys is exactly grevlex.**

Below the digit bound, `compare` on keys is `(compare degrees).then
((compare reversed exponent vectors).swap)` -- the definition of grevlex.
-/
theorem compare_encodeKey (b : Nat) (p₁ p₂ : List Nat)
    (hlen : p₁.length = p₂.length) (h₁ : p₁.sum < b) (h₂ : p₂.sum < b) :
    compare (encodeKey b p₁) (encodeKey b p₂)
      = (compare p₁.sum p₂.sum).then ((compare p₁.reverse p₂.reverse).swap) := by
  have hlen' : (psums p₁).length = (psums p₂).length := by
    have len : ∀ (p : List Nat) (prev : Nat), (psumsFrom prev p).length = p.length := by
      intro p
      induction p with
      | nil => intro _; rfl
      | cons e es ih => intro prev; show (psumsFrom (prev + e) es).length + 1 = _; simp [ih]
    simp [len, hlen]
  rw [encodeKey, encodeKey, encodeFrom_eq_fromDigits, encodeFrom_eq_fromDigits,
    compare_fromDigits b _ _ hlen'
      (fun d hd => Nat.lt_of_le_of_lt (mem_psums_le p₁ d hd) h₁)
      (fun d hd => Nat.lt_of_le_of_lt (mem_psums_le p₂ d hd) h₂),
    reverse_psums, reverse_psums,
    compare_sufSums _ _ (by simpa using hlen)]
  simp

end Mon
end Macaulean
