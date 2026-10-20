# Euclid as a translation-preservation example

**Status: detailed example and proof plan; universal proofs and production while integration are TODO.**

Macaulean is our interpreter. Its chosen semantics, not the native Macaulay2 D implementation, are the verification target. We preserve the source algorithm rather than substitute a built-in gcd. A later theorem that the answer is a mathematical greatest common divisor is a different task and is not a prerequisite here.

## 1. Baseline and reuse

This work starts from `andrew-tawfeek/Macaulean@0e2231ba340d7cb2bd7748f6d54aa4032dc8b483`, the head of [#41](https://github.com/Macaulean/Macaulean/pull/41), including [#40](https://github.com/Macaulean/Macaulean/pull/40). The PR is stacked on those changes and targets their existing base, `feature/m2-proof-stage2-20260927`. It does not merge them or change their branches.

The following are existing implementation interfaces, inspected rather than proposed replacements:

| Existing file | Reuse in this example |
|---|---|
| `Macaulean/Interpreter/Syntax.lean` | `Term`, `Parameters.fixed`, `BinOp.rem/ne/lt`, `UnOp.neg`; assignments and sequential expressions |
| `Macaulean/Interpreter/Lexical.lean` | `Resolver.declareMany`, `Resolver.declare/lookup`, `resolve`, `prepare`, `Code`, `Ref.slot` |
| `Macaulean/Interpreter/Runtime.lean` | `State.allocate`, `Frames`, `readRef`, `writeRef`, `eval`, `call`, `finish`; actual heap-backed values and closures |
| `Macaulean/Interpreter/Semantics.lean` | `IntExpr.evalTerm_toTerm` as the existing denotation/interpretation pattern; `quot_rem_spec` for the existing remainder theorem |
| `Macaulean/Verification/Contracts.lean` | Unproved specifications are `Prop` definitions; selecting a contract is not a proof |
| `Macaulean/Interpreter/LibraryCompiler.lean` | `compile`, `collect`, `codeExpr`, and `m2_library%` already produce literal Lean `Code` data |
| `Macaulean/Interpreter/SourceFile.lean` | `m2_source%` embeds the checked-in `.m2` text as a literal String |
| `Macaulean/Interpreter/DSL.lean` | Actual `reader`, `treeSyntax`, `lowerTree`, `lowerInput`, and session elaboration boundaries |
| `Macaulean/Verification/Snapshot.lean` | Existing declaration/reachable-state sealing and `references` traversal; extend rather than replace for a future translation contract |

The fork's polynomial proofs remain intact. Their mathematical representation contracts do not prove this program's compilation or loop behavior. Likewise the existing `Contracts.Statement` asserts successful-return mathematical postconditions, explicitly not termination or heap preservation. Do not relabel it as a translation theorem.

## 2. What is present and what is not

The baseline has no `whileDo` constructor in either `Term` or `Lexical.Code`. Its lexer classifies `while` and `do` as ordinary identifiers. Consequently an input can lex or even parse without representing the intended loop. Testing only that parsing succeeds is not an adequate acceptance test.

This PR adds:

* the exact source algorithm in `gcd.m2`, including its while loop;
* the four supported source components as actual existing `Term` values;
* a small `Plan` / `CodePlan` adapter around those components, exposing exactly the missing control seam;
* concrete lowering through `Lexical.resolve` and execution of every leaf through `Runtime.eval`;
* an independent inductive source relation and precise, quantified proof obligations;
* concrete parser/layout/iteration/body checks, including a wrong-assignment-order negative control;
* a worksheet using the existing DSL for the supported helper and one-iteration function;
* the production-source, closure-call, exporter, and proof integration TODOs below.

`executePlan` is an example driver, not a production interpreter implementation. It does not parse the whole `gcd.m2` file, construct a production while-containing closure, or establish the source link. Delete this adapter after GCD-01 is implemented. Its existence is not an excuse to leave a parallel permanent language in the repository.

No semantic TODO is filled with an axiom, an admitted proof, a native answer, an always-true contract, or a mathematical gcd call. The small proved declarations concern local update identities and the existing remainder operation only. The `TODO.Proofs` structure has **no inhabitant** in this PR.

## 3. The source and its exact state transition

The example supplies its own source-language absolute-value helper, avoiding an unstated primitive dependency:

```m2
abs = (n) -> if n < 0 then -n else n;

gcdEuclid = (a, b) -> (
    a = abs a;
    b = abs b;
    while b != 0 do (
        r := a % b;
        a = b;
        b = r
    );
    a
);
```

The proof concerns the body under a particular installed helper. It does not quantify over every possible global binding called `abs`. `AbsInstalled` identifies the exact existing-runtime closure and its captured environment. `TODO.AbsBridge` requires the actual `Runtime.call` on that closure to satisfy the independently stated absolute-value contract.

The function's three declaration sites are:

| Declaration | Resolution | At call entry |
|---|---|---|
| parameter `a` | `.slot 0 0` | `.zz a` |
| parameter `b` | `.slot 0 1` | `.zz b` |
| local `r` | `.slot 0 2` | `.null` |

Resolution enters the parameter scope, handles the two assignments, resolves the guard, declares `r` before its RHS, then resolves the rest of the body and the final `a`. While does not add a scope. The three slots are allocated once for a call, not once per iteration. The separate `abs` calls may allocate their own temporary call frames in the baseline heap.

At an iteration boundary with locals `(A,B,R)`, the three writes are:

```text
read a; read b; compute A % B; store r  -> (A, B, A % B)
read b; store a                       -> (B, B, A % B)
read r; store b                       -> (B, A % B, A % B)
```

Thus the final state is `(B, A % B, A % B)`, and the body expression returns the last assigned value, `A % B`. The while expression itself returns null on its ordinary false-condition exit; the function returns the separate final read of `a`.

For `(1071,462)`, the iteration boundaries are `(1071,462,null)`, `(462,147,147)`, `(147,21,21)`, `(21,0,0)`. This finite example tests the translation shape. It is not the universal theorem.

## 4. The actual generated code shape

`Program.lean` constructs the existing source Terms and threads the real resolver through them. `LoweringShape` requires the result to be:

```text
seq
  leaf(seq
    set(slot 0 0, apply(read(global abs), read(slot 0 0)))
    set(slot 0 1, apply(read(global abs), read(slot 0 1))))
  seq
    whileDo(binop ne (read(slot 0 1)) (int 0))
      leaf(seq
        set(slot 0 2, binop rem (read(slot 0 0)) (read(slot 0 1)))
        seq
          set(slot 0 0, read(slot 0 1))
          set(slot 0 1, read(slot 0 2)))
    leaf(read(slot 0 0))
```

Only the outer `CodePlan` while/sequence structure is provisional. The leaf code is not a second instruction language. It is the repository's actual `Lexical.Code`.

The lowering test checks that `r` is slot 2 and total slot count is 3. It does not establish that an arbitrary resolver preserves binding. Nor does it establish that full source text was parsed into this Plan. These are distinct claims with distinct TODOs.

## 5. Independent source semantics

`Semantics.lean` uses the existing `Term` type in a relation `Source.Eval`, not a source evaluator that calls the target compiler. The relation has only the constructors required for this closed integer example:

```text
integer literal                 no store change
local name                      read named location
integer negation                operand then negation
integer remainder/ne/lt          left operand, then right, mathematical operation
call of specified abs helper    evaluate integer argument, return absInt
local assignment                evaluate RHS, update named location, return value
r declaration occurrence        write the pre-bound r location
sequential expression           first, then second, return second's value
```

`Source.Exec` then has four constructors: leaf, sequence, false while, and true while. A true-while derivation contains three smaller derivations: guard, body, remaining loop. Induction is on this **execution derivation**, not merely on the unchanged while syntax.

This relation concerns successful finite executions on exact integers. It intentionally does not define arbitrary calls, globals, general redeclaration, reflection, exceptions, or divergence. The source store can use the three distinct names because each corresponds to one fixed binding site in this example. A universal lexical compiler theorem must generalize it to declaration/activation identities and explicitly handle shadowing. It must not claim that this restricted model already does so.

`Source.Graph a b z` means that this independently specified body, starting with `a`, `b`, and null `r`, finishes with integer `z`. It is not defined in terms of `executePlan`, `Runtime.eval`, `lowerPlan`, or mathematical gcd.

## 6. The representation relation is about the real heap

The machine does not have the toy memory `Nat -> Int` from an explanatory sketch. It uses the existing `Runtime.Frames` (lists of cell IDs) and `Runtime.State.heap.cells`.

For a head frame `[ca,cb,cr]`, `FrameValid` requires three distinct allocated cells. `Related source frames state` requires:

```text
Runtime.readRef (.slot 0 0) frames state = .ok (source "a")
Runtime.readRef (.slot 0 1) frames state = .ok (source "b")
Runtime.readRef (.slot 0 2) frames state = .ok (source "r")
```

Distinctness is essential: otherwise a write to slot 0 could alter what slot 1 reads. Validity is essential: invalid references are real baseline errors. Global `abs` is constrained separately by `AbsInstalled`.

`OutsideUnchanged` requires unchanged environment, function definitions, ring identity counter, and values of every pre-existing cell outside the three local cells. It allows appended temporary cells from helper calls. This observation policy is for a closed call without arbitrary heap/frame introspection. It is not a claim of contextual equivalence under all reflection or allocation observations.

The reusable `TODO.WritePreserves` is stated against **actual `Runtime.writeRef`**. The proof should unfold `cellAt` and the successful write branch, then prove indexed-list update facts at equal/different indices. Split the three names, use distinctness for the unequal cells, preserve the bounds/shape, and prove the outside footprint. No gcd lemma is involved.

## 7. Proof obligations and their proof recipes

### GCD-02: helper and scalar operations

For `%`, reuse `remainder_leaf` (definitional equality to `evalBinOp .rem`) and the already-existing `quot_rem_spec`; do not add another arithmetic assumption.

For `!=` and `<`, the runtime currently goes through `Value.toRat?` for the integer pair. `TODO.ScalarOperations` asks for equality with integer comparison. Discharge the integer-to-rational equality/order facts, not just the syntactic fact that both inputs are `.zz`.

`TODO.AbsBridge` quantifies over an installed actual closure, every integer, and every sufficiently large runtime depth. Unfold `Runtime.call` for the fixed single parameter and execute `absCode` through its existing if/negation/read cases. Show the result is `Source.absInt n`, the global helper is unchanged, and all pre-existing cells are unchanged. A helper activation may append cells; its allocation is not a mutation of the caller's frame.

### GCD-03: syntax and resolution

Prove `TODO.LeafSyntax` by checking the four supported source strings and `LoweringShape`. A concrete `rfl` or kernel-reduced parser check is sufficient for these fixed data equalities. It is **not** a proof of arbitrary parser correctness.

After GCD-01, replace the Plan-source hand construction with the actual whole-source `parse`/`LibraryCompiler.compile` result and prove that exact connection. Retain the source text as a constant and check the full while-containing AST, not merely successful parsing.

### GCD-04: store/layout preservation

Prove `TODO.WritePreserves` for any valid three-cell frame at any heap offset. Prove the corresponding read lemma from `Related`. Then generalize the layout statement for a reviewed language fragment; this example alone does not prove fresh declarations, nested functions, or shadowing in all Terms.

### GCD-05: four leaf preservation statements

`TODO.LeafPreserves term code` quantifies over related source and actual machine states, an installed helper, a source execution derivation, and all runtime depths above a sufficient bound. It concludes actual `Runtime.eval` success, identical returned Value, related final state, preserved helper, and outside footprint.

For initialization, compose: source a-read -> helper call -> write a -> source b-read -> helper call -> write b. `abs` on a cannot change the old b location. For the guard, use the source b-read and ScalarOperations.ne and prove no change. For the iteration, compose remainder -> write r -> read old b/write a -> read r/write b. For the final expression, use Related directly.

The iteration's three intermediate relations are:

```text
Related(source, frames, machine)
Related(update(source,r,A%B), frames, machine1)
Related(update(update(source,r,A%B),a,B), frames, machine2)
Related(update(update(update(source,r,A%B),a,B),b,A%B), frames, machine3)
```

The returned body value must be `A % B`. Proving only the final a/b pair misses a result-value preservation condition.

### GCD-06: while/sequence preservation in both directions

`TODO.PlanPreserves bodyPlan lowered.1` is forward finite-execution simulation. In the false case, use guard preservation and return null. In the true case, apply guard preservation, then body preservation, then the induction hypothesis for the smaller derivation of the remaining while. Combine footprints transitively; retain FrameValid and AbsInstalled between iterations.

Depth bookkeeping is explicit. `Runtime.eval` and the provisional control driver are depth-bounded, not total-step counters. For each finite source derivation, construct sufficient lower bounds. A sequence/loop parent needs a control depth larger than the maximum required by its recursive children; each leaf uses a runtime depth sufficient for that leaf. Prove monotonicity for the relevant closed code, then quantify over all greater bounds. Never infer nontermination from one exhausted run.

`TODO.PlanReflects` is the reverse finite-success obligation. Invert a successful machine while evaluation, recover integer predicate/body steps, and recursively reconstruct a source derivation. Its `Source.IntegerInputs` premise is necessary: the production runtime also accepts some rational computations not represented by this integer-only relation.

Neither direction alone establishes totality. A checker that rejects everything is ruled out only when forward adequacy is combined with an actual source execution/existence argument.

### GCD-07: existence, not mathematical gcd correctness

`TODO.SourceTerminates` requires that every integer input pair has a finite `Source.Graph` result. After the helper calls, a and b are nonnegative. At b=0 use the false rule. At b>0, the remainder is nonnegative and strictly smaller than b. Induct on b's natural magnitude to construct a finite derivation. The existing remainder theorem supplies the decrease facts.

This does not prove divisibility, greatestness, or equality with a mathematical gcd. Those facts belong to a later algorithm-correctness theorem. No total `Int -> Int -> Int` export is justified merely by a fuel-bounded successful example.

### GCD-08: function and invocation boundary

`TODO.SetupCorrect` connects the current harness's real helper installation and one-time three-cell allocation to Source.initial. Prove its bound and state relation; also use the same construction in the reverse body theorem.

Production integration must additionally use `Runtime.Function.closure (.fixed ["a","b"]) 3 body captured` and `Runtime.call` on `.sequence [.zz a,.zz b]`, once Code can contain while. Prove fixed-arity unpacking, actual frame allocation, final result, and preservation of pre-existing caller state. Do not merely rename the body harness a closure call.

`TODO.BodyTranslation` finally states:

```text
for every integer a, b, z:
  Source.Graph a b z
    iff
  there exist controlDepth, runtimeDepth, after such that
    runBody controlDepth runtimeDepth a b = .ok (.zz z, after)
```

This is an end-to-end BODY proposition. The stronger full-source/DSL theorem needs GCD-01/GCD-03/GCD-09 as well. The source helper contract is discharged by AbsBridge, not assumed forever.

## 8. Production while integration: exact TODO surface

GCD-01 should be a small coherent extension of the existing pipeline, not an unrelated new interpreter:

| File / interface | Required edit |
|---|---|
| `Lexer.Sym`, `Lexer.identifierToken` | Add actual while/do tokens under our chosen syntax; remove the current identifier classification for these words |
| `Parser.Tree`, prefix parsing, `Tree.toTerm` and bounds | Add the while form and parse condition/body with deliberate precedence/newline rules |
| `Syntax.Term`, `Term.decEq`, `toM2String` | Add whileDo and all exhaustive cases |
| `Lexical.Code`, `resolve` | Resolve guard then body in the same scope, threading declarations once; append a Code.whileDo |
| `Runtime.eval` | Execute guard/body/repetition on the same Frames; false returns null; wrong condition class and depth exhaustion use explicit Macaulean decisions |
| `DSL.treeSyntax`, `lowerTree` | Carry structured while syntax through both directions; no string-print/reparse workaround |
| `Input` | Establish statement boundary handling for multi-line while; test its reader path, not only the standalone parser |
| `LibraryCompiler.codeExpr`, `collect/compile` | Reify the new Code node; allow the existing named-function collector to retain the exact loop body |
| `Verification.Snapshot.references` and code/Term traversals | Visit guard/body dependencies and declarations; do not silently omit them from sealing |
| Existing evaluator/reference modules | Make unsupported outcomes explicit where a fragment remains loop-free; do not return null for unknown while |

The current runtime's errors do not retain a reached state in `Signal.error`. This PR does not impose the earlier native-D audit's state-on-error specification. For this first successful integer theorem the issue is excluded; choose and document our own full error/control policy before claiming a theorem about those observations. Do not import D's accidental clause-specific behavior unless deliberately selected.

## 9. DSL and Lean declaration export

There is already more export infrastructure here than a from-scratch plan needs: `m2_library%` generates literal `(String × Code)` entries; `codeExpr` and `valueExpr` reify existing data; the verification fork seals declaration and runtime dependencies. Reuse these.

For the complete example, GCD-09 should generate stable, versioned declarations with these roles:

```text
gcdEuclid_source       : String             exact accepted source
gcdEuclid_code         : Lexical.Code       actual parsed/resolved function code
gcdEuclid_initial      : Runtime.State      explicit sealed/linkable environment
gcdEuclid_run          : Nat -> Int -> Int -> Runtime.Result Value
gcdEuclid_translation  : Prop               the all-input preservation statement
```

The final name is initially a **definition of a proposition**, not a theorem. A separately checked proof may later inhabit it. Concrete result definitions can be emitted immediately; total mathematical functions require termination and a bridge theorem.

`Check.addRunTheorem` currently proves a concrete `run source = outcome` and `#m2_check` asks an external M2 oracle. Do not route this own-semantics example through that oracle and call it compiler correctness. Extract/reuse only the kernel-checked declaration-construction pattern as appropriate. A finite-run equality is also not the all-input theorem.

A new translation schema must not be smuggled into one of the three polynomial `Contracts.Kind` values. Add an explicitly reviewed schema or a separate translation-contract module, with input domain, state/effect observations, forward/backward scope, and termination status. Add its semantic declarations to `Snapshot.roots` and traverse new Code nodes. Changing source, helper code, scope layout, or semantic rules must invalidate old approval/proof artifacts.

A Lean constant cannot be a mutable live M2 binding. It denotes immutable code or a versioned state/value. Do not import raw session-relative closure/cell IDs into another worksheet without the existing sealing/linking discipline.

## 10. TODO checklist and completion criteria

| ID | Deliverable | Completion criterion |
|---|---|---|
| GCD-01 | Production while pipeline | Whole source parsed to actual while nodes and invoked through Runtime.call; Plan/CodePlan removed |
| GCD-02 | AbsBridge and ScalarOperations | Kernel-accepted universal proofs against current helper/code/operators |
| GCD-03 | Source/layout link | Whole-file source -> actual code equality, plus existing leaf/layout checks; no manual source-plan gap |
| GCD-04 | Frame/write and binder relation | Actual indexed heap lemmas, distinctness and footprint proved; generalizations have explicit domains |
| GCD-05 | Four leaf preservation proofs | Instantiate LeafPreserves for init/guard/iteration/result |
| GCD-06 | Forward/backward while lifting | Both directions with depth adequacy and intermediate relation preservation |
| GCD-07 | Termination/non-vacuity | SourceTerminates for all integer inputs; no use of mathematical gcd correctness |
| GCD-08 | Production call/return boundary | Actual closure arity, allocation, return, external footprint and body theorem compose |
| GCD-09 | DSL declarations and review metadata | Literal source/code/state/run/Prop exports using fork infrastructure, validated dependency changes |
| GCD-10 | Validation | Pinned-toolchain build, these tests, existing suites, proof dependency audit; log what actually ran |
| GCD-11 | Broader semantics, separately scoped | Choose errors/returns/divergence/resource and reflection policies; extend theorem without claiming the integer fragment covers them |
| GCD-12 | Optional functional extraction | Prove mutation-elimination to a pure Euclid recurrence only after source/IR bridge; not required for the first theorem |

The checklist is not an implementation claim. In particular, `TODO.Proofs` enumerates proof types and has no constructed proof object. Compile-checking those types does not discharge them.

## 11. Validation and next commands

The source baseline pins Lean 4.33.1. In a checkout with that toolchain:

```sh
lake build Macaulean.Verification.Examples.GcdTranslation.Semantics
lake env lean MacauleanTest/GcdTranslation.lean
lake env lean Examples/GcdTranslation/Worksheet.lean
lake test
```

The first two avoid a native M2 oracle. The existing full test driver includes unrelated native-M2 suites and may need their normal service/dependency setup. `gcdTranslationSource` is registered as a Lake input so changes to embedded source invalidate the build.

Tests cover supported parsing, the literal frame layout, the three (1071,462) iteration transitions, signed/zero/coprime examples, depth exhaustion, and a wrong-order body producing `(462,0,0)` instead of `(462,147,147)`. They are concrete regressions, not substitutes for the quantified proof obligations.

**Validation in this editing session:** repository files and PR ancestry were inspected through the GitHub connector; new files and commits were pushed through that connector. No local Lean or Lake executable was present, and the attempted public source clone could not resolve github.com. Therefore Lean compilation and the newly added checks are not reported as passing. No native M2 execution, benchmark, or universal preservation proof was performed. The PR remains draft and the TODOs remain explicit.
