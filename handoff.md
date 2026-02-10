# `m2sos` Tactic — Handoff Notes

## What Was Done

Implemented the `m2sos` tactic for proving a polynomial over `Rat` is a weighted sum of squares, following the established pattern of `m2idealmem` and `m2factor`.

### Files Created

- **`Macaulean/SumOfSquares.lean`** — Core implementation:
  - `IsSumOfSquares` inductive predicate (weighted: `c * a^2 + p` with `0 ≤ c`)
  - `SumOfSquaresResult` structure for JSON deserialization of M2 response
  - `m2SumOfSquares` IO wrapper for the JSON-RPC call
  - `ratAsRingElem` helper to construct `Rat` coefficient expressions
  - `m2SOSGetDecomposition` (MetaM): reifies polynomial, serializes, calls M2, deserializes generators and coefficients
  - `m2SOSTactic` (TacticM): builds the canonical SOS expression + proof term, rewrites goal

- **`MacauleanTest/SumOfSquares.lean`** — Three working test examples (fourth commented out)

### Files Modified

- **`m2/macaulean.m2`** — Added `needsPackage "SumsOfSquares"` at top level and `sumOfSquares` JSON-RPC method
- **`Macaulean.lean`** — Added import
- **`MacauleanTest.lean`** — Added import

## Architecture Decisions

### Why `MetaM` / `TacticM` split

`m2SOSGetDecomposition` runs in `MetaM` because `evalExpr` creates serializer/deserializer functions typed as `... → MrdiT MetaM ...`. Attempting to run these in `TacticM` causes a monad mismatch (`MrdiT MetaM` vs `MrdiT TacticM`). The tactic handler (`m2SOSTactic`) then uses the returned expressions to build proofs in `TacticM`, where `runTactic` with syntax quotations is available.

### Why weighted `IsSumOfSquares`

M2's `solveSOS` returns `p = Σ cᵢ * qᵢ²` with positive rational weights. Absorbing weights into generators (`√c · q`) would require irrational square roots and fail over Q. The weighted form is the natural representation.

### Why `SumsOfSquares` loaded at top level

Loading `needsPackage "SumsOfSquares"` lazily inside the method handler (as originally planned) causes `solveSOS` to silently fail. The JSONRPC `try/else` catches the error as generic "Invalid params". Moving the load to the top of `macaulean.m2` (alongside other packages) fixes this. Root cause is likely a scope/state interaction between `needsPackage` and the JSONRPC handler's `try` block.

### Why symbol keys in M2

M2's `SumsOfSquares` package uses M2 symbol keys (`Status`, `generators`, `coefficients`), not string keys (`"Status"`, etc.). Using string keys silently returns `null` / throws key-not-found errors.

## Outstanding Issues (all use `sorry` fallbacks)

### 1. `decide` fails for `Rat` inequalities

**Symptom:** `decide` cannot prove `0 ≤ 3/4` for `Rat`. The `Decidable` instance `Rat.instDecidableLe` doesn't fully reduce in the kernel.

**Current workaround:** Try `decide`, fall back to `sorry`.

**Possible fixes:**
- `native_decide` (compiles to native code, bypassing kernel reduction — untested but likely works)
- Construct the proof term directly using `Rat.le_def` and arithmetic on `num`/`den`
- Use `norm_num` if it has a `Rat` extension

### 2. `grind` fails for polynomial equalities with rational coefficients

**Symptom:** `grind` proves `1 * x^2 + 1 * 1^2 + 0 = x^2 + 1` (integer coefficients) but fails on `1 * (x + 1/2 * y)^2 + 3/4 * y^2 + 0 = x^2 + x*y + y^2`. The issue is that `grind`'s `CommRing` normalizer handles `OfNat`/`Int.cast` coefficients but not `Rat.mk'` or `⁻¹` (field operations).

**Current workaround:** Try `grind`, fall back to `sorry`.

**Possible fixes:**
- Clear denominators: multiply both sides by the LCM of all denominators, prove the integer-coefficient equality with `grind`, then derive the original via cancellation
- A `ring` tactic that handles fields (not available in base Lean 4 without Mathlib)
- Custom polynomial normalizer at the MetaM level that understands `Rat` coefficients
- `norm_num` preprocessing to fold `Rat.mk'` / `(-1) * 2⁻¹` into normalized `Rat` literals before `grind`

### 3. `String.toNat!` PANIC on 3-variable polynomials

**Symptom:** The test `(x - y)^2 + (y - z)^2 + (z - x)^2` causes a PANIC at `String.toNat!` during ConcretePoly deserialization.

**Root cause (likely):** The ConcretePoly MRDI deserialization in `IdealMembership.lean:102` uses `i.toNat!` to parse coefficient variable indices. For 3-variable polynomials, M2 may produce coefficient entries with indices that aren't valid `Nat` strings (perhaps negative or non-numeric). This is an existing issue in the MRDI deserialization code, not specific to `m2sos`.

**To investigate:** Log the raw JSON response from M2 for the 3-variable case and inspect the `coefficients` array in the ConcretePoly data.

## Reuse from Existing Code

Nearly all serialization/deserialization infrastructure is reused from `IdealMembership.lean`:
- `VariableState`, `toCommRingExpr?`, `toExprPoly` — polynomial reification
- `serializePoly`, `deserializePoly` — `ConcretePoly` ↔ MRDI conversion
- `exprFromPoly`, `intAsRingElem` — Lean expression reconstruction
- `Macaulay2Ring Rat`, `MrdiType Rat`, `MrdiType (ConcretePoly R)` — existing instances
- `globalM2Server`, `Macaulay2.sendRequest` — M2 communication

New code is: `IsSumOfSquares` definition, `ratAsRingElem`, proof-term construction loop, M2 method, tactic handler.

## Testing

```bash
lake build MacauleanTest  # builds everything including SOS tests
```

- `x^2 + 1` — passes (no sorry)
- `x^2 + y^2` — passes (no sorry)
- `x^2 + x*y + y^2` — passes with sorry (rational coefficients in decomposition)
- `(x-y)^2 + (y-z)^2 + (z-x)^2` — commented out (PANIC)
