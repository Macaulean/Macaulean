/-
Copyright (c) 2025 Macaulean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Macaulean.Grind.AlgPoly.Basic

@[expose] public section

/-!
# GMP-free size bounds and coprimality certificates

Two ingredients of the single-pass CRT certificate
(`Macaulean/Grind/AlgPoly/KroneckerMod.lean`), both of which the kernel must
evaluate without ever leaving the boxed-scalar range:

* `UBnd` — a base-2 "float" `m * 2^e` used as an *upper* bound for the L1 norm
  of a normalized polynomial.  The mantissa is renormalized below `2^31` after
  every operation, so mantissa products stay below `2^62`.  The exponent is a
  small `Nat` (a few hundred at certificate scale).  The specification function
  `UBnd.val` mentions `pow2`, which is **never** evaluated by the kernel on a
  large argument — only `UBnd.m` and `UBnd.e` are compared, against literals.

* `pairwiseCoprimeB` — a Bézout-witness table certifying that a list of moduli
  is pairwise coprime.  `Nat.gcd` is an out-of-line, GMP-backed primitive and
  is therefore never evaluated; the kernel only checks `a * m = b * n + 1` with
  `a < n`, `b < m`, `m, n < 2^31`, i.e. products below `2^62`.

Lean-core `Nat` operations used on the kernel path here: `+`, `*`, `/` (by the
literal `2`), `Nat.ble`, `Nat.blt`, `Nat.beq`.  All have inline scalar fast
paths in `lean.h`.  `Nat.pow`, `Nat.gcd`, `Nat.log2` are *not* used.
-/

namespace Macaulean

/-! ### Powers of two (specification only) -/

/-- `2 ^ n`, defined by doubling.  Used only inside `UBnd.val` and the
soundness proofs; the kernel never evaluates it on a large argument.  (`pow2 30`
and `pow2 31` are reduced once each, by 30/31 scalar doublings.) -/
def pow2 : Nat → Nat
  | 0 => 1
  | n + 1 => 2 * pow2 n

theorem pow2_pos : ∀ n, 0 < pow2 n
  | 0 => Nat.zero_lt_one
  | n + 1 => by
    have := pow2_pos n
    show 0 < 2 * pow2 n
    omega

theorem pow2_add (a : Nat) : ∀ b, pow2 (a + b) = pow2 a * pow2 b
  | 0 => by simp [pow2]
  | b + 1 => by
    have ih := pow2_add a b
    show 2 * pow2 (a + b) = pow2 a * (2 * pow2 b)
    rw [ih]
    simp [Nat.mul_left_comm, Nat.mul_comm, Nat.mul_assoc]

theorem pow2_le_pow2 {a b : Nat} (h : a ≤ b) : pow2 a ≤ pow2 b := by
  obtain ⟨c, rfl⟩ := Nat.le.dest h
  rw [pow2_add]
  have h2 := pow2_pos c
  calc pow2 a = pow2 a * 1 := (Nat.mul_one _).symm
    _ ≤ pow2 a * pow2 c := Nat.mul_le_mul (Nat.le_refl _) h2

theorem pow2_30 : pow2 30 = 1073741824 := by rfl

theorem pow2_31 : pow2 31 = 2147483648 := by rfl

/-! ### `UBnd`: an upper bound of the form `m * 2^e` -/

/-- An upper bound for a `Nat`, represented as `m * 2^e`.  Kept normalized with
`m < 2^31`, so all mantissa products stay below `2^62`. -/
structure UBnd where
  m : Nat
  e : Nat
  deriving Inhabited

namespace UBnd

/-- The value denoted by the bound.  **Specification only** — never evaluated
by the kernel. -/
def val (x : UBnd) : Nat := x.m * pow2 x.e

/-- Round-up right shift by `d` bits: `m ≤ (shrUp m d + 1) * 2^d`.
At most 63 halvings actually happen, because the value reaches `1` and then
short-circuits; no `Nat.shiftRight` and no `Nat.pow` is needed. -/
def shrUp : Nat → Nat → Nat
  | m, 0 => m
  | m, d + 1 => bif m.ble 1 then m else shrUp ((m + 1) / 2) d

theorem shrUp_le : ∀ (m d : Nat), m ≤ (shrUp m d + 1) * pow2 d
  | m, 0 => by
    show m ≤ (m + 1) * 1
    omega
  | m, d + 1 => by
    have hp : 0 < pow2 d := pow2_pos d
    show m ≤ ((bif m.ble 1 then m else shrUp ((m + 1) / 2) d) + 1) * pow2 (d + 1)
    have hpe : pow2 (d + 1) = 2 * pow2 d := rfl
    cases hb : m.ble 1 with
    | true =>
      have hm : m ≤ 1 := Nat.ble_eq.mp hb
      simp only [cond_true, hpe]
      have : 1 * 1 ≤ (m + 1) * (2 * pow2 d) :=
        Nat.mul_le_mul (by omega) (by omega)
      omega
    | false =>
      simp only [cond_false, hpe]
      have ih := shrUp_le ((m + 1) / 2) d
      have h2 : m ≤ 2 * ((m + 1) / 2) := by omega
      have h3 : 2 * ((m + 1) / 2) ≤ 2 * ((shrUp ((m + 1) / 2) d + 1) * pow2 d) :=
        Nat.mul_le_mul (Nat.le_refl _) ih
      have h4 : 2 * ((shrUp ((m + 1) / 2) d + 1) * pow2 d)
          = (shrUp ((m + 1) / 2) d + 1) * (2 * pow2 d) := by
        simp [Nat.mul_left_comm, Nat.mul_comm, Nat.mul_assoc]
      omega

/-- Renormalization fuel: the loop short-circuits as soon as the mantissa is
below `2^31`, and any mantissa below `2^63` gets there in at most 32 halvings. -/
def normFuel : Nat := 70

/-- Halve the mantissa (rounding up) until it is below `2^31`. -/
def normAux : Nat → Nat → Nat → UBnd
  | 0, m, e => ⟨m, e⟩
  | f + 1, m, e => bif m.blt 2147483648 then ⟨m, e⟩ else normAux f ((m + 1) / 2) (e + 1)

/-- Renormalize `m * 2^e`. -/
def norm (m e : Nat) : UBnd := normAux normFuel m e

theorem normAux_le : ∀ (f m e : Nat), m * pow2 e ≤ (normAux f m e).val
  | 0, m, e => Nat.le_refl _
  | f + 1, m, e => by
    show m * pow2 e ≤
      (bif m.blt 2147483648 then (⟨m, e⟩ : UBnd) else normAux f ((m + 1) / 2) (e + 1)).val
    cases hb : m.blt 2147483648 with
    | true => exact Nat.le_refl _
    | false =>
      simp only [cond_false]
      have ih := normAux_le f ((m + 1) / 2) (e + 1)
      refine Nat.le_trans ?_ ih
      have hpe : pow2 (e + 1) = 2 * pow2 e := rfl
      rw [hpe]
      have h2 : m * pow2 e ≤ (2 * ((m + 1) / 2)) * pow2 e :=
        Nat.mul_le_mul (by omega) (Nat.le_refl _)
      have h3 : (2 * ((m + 1) / 2)) * pow2 e = (m + 1) / 2 * (2 * pow2 e) := by
        simp [Nat.mul_left_comm, Nat.mul_comm, Nat.mul_assoc]
      omega

theorem le_norm (m e : Nat) : m * pow2 e ≤ (norm m e).val := normAux_le _ _ _

/-- Product of bounds. -/
def mul (x y : UBnd) : UBnd := norm (x.m * y.m) (x.e + y.e)

/-- Sum of bounds; the smaller exponent is shifted up, rounding the mantissa. -/
def add (x y : UBnd) : UBnd :=
  bif x.e.ble y.e then norm (shrUp x.m (y.e - x.e) + 1 + y.m) y.e
  else norm (shrUp y.m (x.e - y.e) + 1 + x.m) x.e

/-- Power of a bound, by repeated multiplication. -/
def pow (x : UBnd) : Nat → UBnd
  | 0 => ⟨1, 0⟩
  | k + 1 => mul x (pow x k)

/-- The bound `n = n * 2^0`, renormalized. -/
def ofNat (n : Nat) : UBnd := norm n 0

theorem le_mul (x y : UBnd) : x.val * y.val ≤ (x.mul y).val := by
  refine Nat.le_trans (Nat.le_of_eq ?_) (le_norm (x.m * y.m) (x.e + y.e))
  show x.m * pow2 x.e * (y.m * pow2 y.e) = x.m * y.m * pow2 (x.e + y.e)
  rw [pow2_add]
  simp [Nat.mul_left_comm, Nat.mul_comm, Nat.mul_assoc]

private theorem add_aux (x y : UBnd) (h : x.e ≤ y.e) :
    x.val + y.val ≤ (norm (shrUp x.m (y.e - x.e) + 1 + y.m) y.e).val := by
  refine Nat.le_trans ?_ (le_norm _ _)
  have hd : y.e - x.e + x.e = y.e := Nat.sub_add_cancel h
  have hx : x.val ≤ (shrUp x.m (y.e - x.e) + 1) * pow2 y.e := by
    have h1 : x.m * pow2 x.e
        ≤ ((shrUp x.m (y.e - x.e) + 1) * pow2 (y.e - x.e)) * pow2 x.e :=
      Nat.mul_le_mul (shrUp_le x.m (y.e - x.e)) (Nat.le_refl _)
    have h2 : ((shrUp x.m (y.e - x.e) + 1) * pow2 (y.e - x.e)) * pow2 x.e
        = (shrUp x.m (y.e - x.e) + 1) * pow2 (y.e - x.e + x.e) := by
      rw [pow2_add]
      simp [Nat.mul_left_comm, Nat.mul_comm, Nat.mul_assoc]
    rw [hd] at h2
    show x.m * pow2 x.e ≤ _
    omega
  have hy : y.val = y.m * pow2 y.e := rfl
  have hsum : (shrUp x.m (y.e - x.e) + 1) * pow2 y.e + y.m * pow2 y.e
      = (shrUp x.m (y.e - x.e) + 1 + y.m) * pow2 y.e := (Nat.add_mul _ _ _).symm
  omega

theorem le_add (x y : UBnd) : x.val + y.val ≤ (x.add y).val := by
  cases hb : x.e.ble y.e with
  | true =>
    have he : x.add y = norm (shrUp x.m (y.e - x.e) + 1 + y.m) y.e := by
      simp only [add, hb, cond_true]
    rw [he]
    exact add_aux x y (Nat.ble_eq.mp hb)
  | false =>
    have he : x.add y = norm (shrUp y.m (x.e - y.e) + 1 + x.m) x.e := by
      simp only [add, hb, cond_false]
    rw [he]
    have h : y.e ≤ x.e := by
      have : ¬ x.e ≤ y.e := fun hle => Bool.noConfusion ((Nat.ble_eq.mpr hle).symm.trans hb)
      omega
    have := add_aux y x h
    omega

theorem le_pow (x : UBnd) : ∀ k, x.val ^ k ≤ (x.pow k).val
  | 0 => by
    show x.val ^ 0 ≤ 1 * pow2 0
    exact Nat.le_refl 1
  | k + 1 => by
    refine Nat.le_trans ?_ (le_mul x (x.pow k))
    rw [Nat.pow_succ]
    have h1 : x.val ^ k * x.val ≤ (x.pow k).val * x.val :=
      Nat.mul_le_mul (le_pow x k) (Nat.le_refl _)
    have h2 : (x.pow k).val * x.val = x.val * (x.pow k).val := Nat.mul_comm _ _
    omega

theorem le_ofNat (n : Nat) : n ≤ (ofNat n).val := by
  refine Nat.le_trans (Nat.le_of_eq ?_) (le_norm n 0)
  show n = n * 1
  omega

/-- `val x < 2^(31 + e)` whenever the mantissa is normalized. -/
theorem val_lt (x : UBnd) (h : x.m < 2147483648) : x.val < pow2 (31 + x.e) := by
  rw [pow2_add, pow2_31]
  have hp : 0 < pow2 x.e := pow2_pos x.e
  have h1 : (x.m + 1) * pow2 x.e ≤ 2147483648 * pow2 x.e :=
    Nat.mul_le_mul (by omega) (Nat.le_refl _)
  have h2 : (x.m + 1) * pow2 x.e = x.m * pow2 x.e + pow2 x.e := by
    rw [Nat.add_mul, Nat.one_mul]
  show x.m * pow2 x.e < 2147483648 * pow2 x.e
  omega

end UBnd

/-! ### Products and pairwise coprimality -/

/-- Product of a list of naturals.  Specification only. -/
def prodN : List Nat → Nat
  | [] => 1
  | m :: ms => m * prodN ms

/-- A single Bézout check `a * m = b * n + 1`, which certifies `Coprime m n`
without ever calling `Nat.gcd`. -/
def bezOk (a m b n : Nat) : Bool := (a * m).beq (b * n + 1)

theorem coprime_of_bezOk {a m b n : Nat} (h : bezOk a m b n = true) :
    Nat.Coprime m n := by
  have h : a * m = b * n + 1 := Nat.eq_of_beq_eq_true h
  have hm : Nat.gcd m n ∣ a * m :=
    Nat.dvd_trans (Nat.gcd_dvd_left m n) ⟨a, Nat.mul_comm a m⟩
  have hn : Nat.gcd m n ∣ b * n :=
    Nat.dvd_trans (Nat.gcd_dvd_right m n) ⟨b, Nat.mul_comm b n⟩
  have h1 : Nat.gcd m n ∣ a * m - b * n := Nat.dvd_sub hm hn
  have he : a * m - b * n = 1 := by omega
  rw [he] at h1
  exact Nat.dvd_one.mp h1

/-- Bézout witnesses for `m` against every element of a list. -/
def allBez (m : Nat) : List Nat → List (Nat × Nat) → Bool
  | [], _ => true
  | n :: ns, ab :: t => bezOk ab.1 m ab.2 n && allBez m ns t
  | _ :: _, [] => false

/-- A table of Bézout witnesses certifying that `ms` is pairwise coprime.
Row `i` holds the witnesses for `ms[i]` against `ms[i+1:]`. -/
def pairwiseCoprimeB : List Nat → List (List (Nat × Nat)) → Bool
  | [], _ => true
  | m :: ms, row :: rows => allBez m ms row && pairwiseCoprimeB ms rows
  | _ :: _, [] => false

theorem allBez_sound (m : Nat) : ∀ (ns : List Nat) (row : List (Nat × Nat)),
    allBez m ns row = true → ∀ n ∈ ns, Nat.Coprime m n
  | [], _, _, _, hn => by cases hn
  | _ :: _, [], h, _, _ => by simp [allBez] at h
  | n :: ns, ab :: t, h, n', hn' => by
    simp only [allBez, Bool.and_eq_true] at h
    cases hn' with
    | head => exact coprime_of_bezOk h.1
    | tail _ hn'' => exact allBez_sound m ns t h.2 n' hn''

theorem pairwiseCoprimeB_sound : ∀ (ms : List Nat) (tbl : List (List (Nat × Nat))),
    pairwiseCoprimeB ms tbl = true → ms.Pairwise Nat.Coprime
  | [], _, _ => List.Pairwise.nil
  | _ :: _, [], h => by simp [pairwiseCoprimeB] at h
  | m :: ms, row :: rows, h => by
    simp only [pairwiseCoprimeB, Bool.and_eq_true] at h
    exact List.Pairwise.cons (allBez_sound m ms row h.1)
      (pairwiseCoprimeB_sound ms rows h.2)

/-! ### CRT: pairwise coprime divisors multiply -/

theorem coprime_prodN {m : Nat} : ∀ (ms : List Nat),
    (∀ n ∈ ms, Nat.Coprime m n) → Nat.Coprime m (prodN ms)
  | [], _ => Nat.coprime_one_right m
  | n :: ms, h =>
    Nat.Coprime.mul_right (h n (List.Mem.head _))
      (coprime_prodN ms fun x hx => h x (List.Mem.tail _ hx))

theorem prodN_dvd {n : Nat} : ∀ (ms : List Nat), ms.Pairwise Nat.Coprime →
    (∀ m ∈ ms, m ∣ n) → prodN ms ∣ n
  | [], _, _ => Nat.one_dvd n
  | m :: ms, hp, hd => by
    cases hp with
    | cons hhead htail =>
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (coprime_prodN ms fun x hx => hhead x hx)
        (hd m (List.Mem.head _))
        (prodN_dvd ms htail fun x hx => hd x (List.Mem.tail _ hx))

/-- Every modulus is at least `2^30`. -/
def allBig : List Nat → Bool
  | [] => true
  | m :: ms => Nat.ble 1073741824 m && allBig ms

theorem pow2_le_prodN : ∀ (ms : List Nat), allBig ms = true →
    pow2 (30 * ms.length) ≤ prodN ms
  | [], _ => Nat.le_refl 1
  | m :: ms, h => by
    simp only [allBig, Bool.and_eq_true] at h
    have hm : 1073741824 ≤ m := Nat.ble_eq.mp h.1
    have ih := pow2_le_prodN ms h.2
    show pow2 (30 * (ms.length + 1)) ≤ m * prodN ms
    have he : 30 * (ms.length + 1) = 30 + 30 * ms.length := by omega
    rw [he, pow2_add, pow2_30]
    exact Nat.mul_le_mul hm ih

end Macaulean

end
