# Verified M2 functions: contracts and generated verification conditions

This note describes an experiment: verifying functions written in the M2 DSL
without translating them into Lean by hand. The first instance covers functions on
natural numbers (`#m2_verify`). The design is meant to grow to more of the DSL;
the last section explains how.

## The idea

You write ordinary M2 in a worksheet, and a contract (pre- and postcondition) in
Lean. Everything in between is mechanical:

1. **Verification conditions come from the compiled code.** A Lean function `wpN`
   (a weakest-precondition calculus) walks the `Lexical.Code` that the runtime
   actually executes. It produces a plain mathematical statement, the
   *verification condition* (VC). The VC mentions neither the interpreter nor
   fuel nor heaps.
2. **Soundness is proved once.** The theorem `NatContracts.verified` states that
   for *every* function body, if its VC holds then the production
   `Runtime.call` meets the contract. There is no separate model of M2: the
   theorem is about the same evaluator the worksheet runs.
3. **A command connects the two.** `#m2_verify` reads the function from the
   worksheet session and generates the VC. It proves the VC with the user's tactic
   and instantiates the soundness theorem for this function.

So the only per-program proof is pure mathematics. For `gcdNat` it is

```
if b = 0 then a = Nat.gcd a b else a % b < b ∧ Nat.gcd b (a % b) = Nat.gcd a b
```

Compare an earlier hand-written proof of the same function. It needed a
symbolic-execution lemma for each branch, an induction, and fuel bookkeeping, all
specific to that one program. Here all of that lives in the generic soundness
proof.

## Quick start

```lean
import Macaulean.Verification.NatContracts
open M2

gcdNat = (a,b) -> if b == 0 then a else gcdNat(b, a % b);

#m2_verify gcdNat (a b : Nat) returns r : r = Nat.gcd a b
  termination_by b := by
    split
    · simp_all
    · exact ⟨Nat.mod_lt _ (by omega), by rw [Nat.gcd_comm b, ← Nat.gcd_rec, Nat.gcd_comm]⟩

predNat = n -> n - 1;
#m2_verify predNat (n : Nat) (h : 0 < n) returns r : r + 1 = n   -- proved automatically
```

| Part | Meaning |
| --- | --- |
| `(a b : Nat)` | The function's arguments, in order; their count must match the M2 parameters. |
| `(h : P)` | Any binder whose type is not `Nat` is a precondition on the arguments. |
| `returns r : Q` | The postcondition; `r` names the result. |
| `termination_by m` | A natural-number measure that every self-call must decrease. It is required for recursive functions. |
| `:= by tac` | Optional proof of the VC. When omitted, `m2_vc` tries `omega`, `grind` and `simp_all`. |

To see the VC, write `:= by trace_state; sorry`. If the default tactic fails, the
error message shows the unproved goal.

### Declarations added to the environment

| Name | Content |
| --- | --- |
| `f.state` | The worksheet's runtime state at this point, copied into a Lean term. |
| `f.body` | The function's compiled body, as `Lexical.Code`. |
| `f.contract` | The contract, as a `NatContracts.Contract`. |
| `f.vc` | `NatContracts.VC …`, proved by the user's tactic. |
| `f.correct` | The theorem below. It is installed only if `f.vc` was proved without `sorry`. |

`f.correct` says: for all natural arguments satisfying the preconditions,
- **termination:** there are `fuel`, `r` and `after` such that `Runtime.call fuel f args f.state = .ok (.zz r, after)` and the postcondition holds for `r`;
- **partial correctness:** every successful call, at any fuel, returns some `.zz r` satisfying the postcondition.

### What is trusted

- **The Lean kernel.**
- **The copy of the session.** `Targets.stateExpr` copies the live session into
  `f.state`. The theorems are about that term; nothing proves it equals the
  session.
- **The snapshot.** A later redefinition of `f` is not covered.

The theorem gives no explicit fuel bound: termination is "for some fuel", which
follows from the decreasing measure.

## How it works

Files: `Macaulean/Verification/NatContracts/{Wp,Soundness,Command}.lean`.

### Contracts and weakest preconditions (`Wp.lean`)

A `Contract` consists of `arity`, `pre : List Nat → Prop`,
`post : List Nat → Nat → Prop` and `measure : List Nat → Nat`. A `Ctx` fixes:
- the function's global name and parameter list;
- its contract;
- the current arguments `xs`, which are slots `0..k-1`;
- the bound `measure xs`.

`wpN c code Q` means that `code` yields a natural number `n` with `Q n`.
`wpB c code Q` is the same for a Boolean result, and `wpArgs` handles argument
lists. The three are defined by structural recursion on `Code`:

| Code | Weakest precondition |
| --- | --- |
| `.int z` | `0 ≤ z ∧ Q z.toNat` |
| parameter slot `i` | `i < xs.length ∧ Q xs[i]` |
| `a + b`, `a * b`, `a // b`, `a % b`, `a ^ b` | `wpN a (fun x => wpN b (fun y => Q (x op y)))` |
| `a - b` | the same, with the extra obligation `y ≤ x` |
| `if c then t else e` | `wpB c (fun b => if b then wpN t Q else wpN e Q)` |
| self-call `f(args)` | each argument as above; then `pre ys ∧ measure ys < bound ∧ ∀ r, post ys r → Q r` |
| `== != < <= > >=`, `and`, `or`, `not` | Boolean versions, short-circuiting exactly as `Runtime.eval` does |
| anything else | `False` |

The `False` default makes the calculus sound by construction. The command checks
the fragment beforehand only to give better error messages.

The self-call rule is the usual Hoare-style treatment of recursion: the
recursive call is assumed to satisfy the contract, provided its measure is
smaller.

### Soundness, once (`Soundness.lean`)

- **Per-construct runtime lemmas.** There is one for each construct, e.g.
  `eval_bin`, `eval_if_true`, `eval_apply`, `evalMany_cons`. Arithmetic lemmas
  (`bin_rem`, `cmp_eq`, …) rewrite the production `evalBinOp` on `.zz ↑x` into ℕ
  operations.
- **Fuel.** Every result is stated with existential fuel. Subterm results are
  combined by taking the maximum of their fuels, which is valid because of
  `eval_mono`/`call_mono`; these are derived from `Fuel.step`. Partial correctness
  then follows from determinism (`Fuel.call_success_unique`).
- **The heap.** Evaluation only appends cells (`RowProgram.AllocatesOnly`). So
  argument slots, globals and closure records stay valid across nested calls.
- **The `Good` invariant.** It says the frame holds the arguments, the global
  name resolves to the function, and calls with smaller measure already meet the
  contract.
- **The main induction.** Under `Good`, the mutual theorems `runsN`, `runsB` and
  `runsArgs` show by induction on code size that a satisfied `wp` gives a
  successful evaluation with the promised result.
- **`total` and `verified`.** `total` closes the loop by strong induction on the
  measure: it enters the body with `Functions.call_closure` and discharges
  `Good.calls` with the induction hypothesis. `verified` packages total and
  partial correctness.

### The command (`Command.lean`)

1. Look up the closure in `DSL.getSession`, and check the parameters and the
   supported fragment.
2. Add `f.state` and `f.body` by reflection, using `Targets.stateExpr` and
   `LibraryCompiler.codeExpr`.
3. Build `f.contract` from the binders, by pattern matching on the argument list.
4. Elaborate `f.vc`. The proof unfolds the `wp` functions with `simp`, which
   leaves the readable VC, then runs the user's tactic. This step is synchronous,
   so failures are detected.
5. Elaborate `f.correct` as an application of `verified`. Its side conditions are
   closed by `decide +kernel` and `rfl` on the copied state.

The command adds no new reserved keywords: `returns` is non-reserved, and
`termination_by`/`:=` already exist. This matters because M2 worksheet input is
tokenized by Lean.

## Current scope (v1)

- **Supported:** natural literals, parameters, `+ - * // % ^`, comparisons,
  `and`/`or`/`not`, `if … then … else`, and self-recursion. Both `n -> …` and
  `(a,b) -> …` work.
- **Refused, with a message:** local variables and assignments, `;` sequences,
  lists, `/` (rational division), calls to other functions, and a missing
  `termination_by` on a recursive function.
- **Tests:** `MacauleanTest/VerificationNatContracts.lean` contains positive and
  negative examples. `Examples/Gcd.lean` is a worksheet.

## Extending beyond natural numbers

Each new feature follows the same five-step recipe:

1. **Choose a semantic domain.** Decide which runtime values are represented, and
   by which mathematical object. For ℕ this is `natV n = .zz ↑n`.
2. **Add `wp` clauses** for the new constructs, with side conditions wherever
   the runtime can fail, e.g. a division by zero or an out-of-range index.
3. **Add runtime lemmas** that evaluate each construct, and add the matching
   cases to the soundness induction.
4. **Add `simp` lemmas** that turn production operations on represented values
   into mathematical operations. These keep VCs readable and are usually the bulk
   of the work.
5. **Extend the fragment checker and the command's binder types.**

Suggested next steps, roughly in order of effort:

- **Typed values (ℤ, ℚ, Booleans as results).** Replace `wpN`/`wpB` by a single
  `wp : Ty → Code → (Ty.denote → Prop) → Prop`. Here `Ty` lists the supported
  types (`nat`, `int`, `rat`, `bool`, …), and a view function
  `Ty.view : Value → Option Ty.denote` relates them to runtime values.
  Contracts become typed signatures. For ℤ, `//` and `%` are Euclidean, as
  already characterized by `quot_rem_spec` in
  `Interpreter/Semantics.lean`, and `-` needs no side
  condition. For ℚ, `/` needs the obligation `y ≠ 0`.
- **Calls to other verified functions.** Add a table of already-verified
  contracts to `Ctx`. A call then uses the callee's postcondition, and soundness
  takes the callees' `correct` theorems as hypotheses. This gives modular
  verification, and the same mechanism gives library functions (`normalForm`, …)
  prebuilt contracts. Mutual recursion needs a shared measure.
- **Lists and sequences.** These are immutable in the DSL, so they fit the
  current state-free design. The domain is `List τ`, indexing gets an in-bounds
  obligation, and recursion over lists can use `length` as the measure.
- **Polynomials.** The domain is `Views.Polynomial r` with its denotation. Much
  of step 4 already exists:
  - `PolynomialArithmetic.eval_add`/`eval_sub`/`eval_mul` give the
    runtime-to-polynomial step;
  - `KernelPolynomial.denote_*` (in `KernelPolynomialSemantics.lean`) give the
    algebraic meaning.

  VCs become ring identities, which `grind`'s commutative-ring solver can often
  close. A contract has to fix the ring, which is part of the runtime state.
- **Local variables and `;`.** This is the most invasive extension. Slots become
  mutable, so `wp` must thread a store, and `AllocatesOnly` must be weakened to
  "writes only this frame's cells".
- **Smaller items.**
  - a partial-correctness mode without a measure, by induction on fuel;
  - lexicographic measures;
  - explicit fuel bounds;
  - sending VCs to the existing proof-job pipeline, so that agents prove only
    pure-math goals.

Keep one principle throughout: the semantics of a construct is stated once, in a
soundness lemma about the production runtime. Each program then contributes only
mathematics.
