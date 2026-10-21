# GCD translation preservation — design-first revision

**Draft prototype with explicit proof and frontend TODOs.** This revision replaces the
previous example's `Plan`/`CodePlan` wrappers around the legacy interpreter. The new
example is built from the Word/profile, Symbol/namespace, activation/location design
developed in the discussion. It is not constrained by the old implementation's `Sym`,
`Term.binop`, string globals, or polynomial-ring grammar special case.

**Our semantics define our interpreter. Native M2's D implementation is inspiration,
not the specification or proof oracle.** Earlier native-fidelity audit findings remain
useful design evidence, but do not impose accidental D behavior on this language.

The branch retains the DSL fork's ancestry (PRs #40/#41); existing functionality is
not rewritten underneath those PRs. New semantic modules live in
`Macaulean/Language/Design/`. The only legacy utility imported by the example is
`Interpreter.SourceFile`, for literal file inclusion. No legacy evaluator or parser
is called. Editor/session/review infrastructure remains a future adapter, not the
semantic foundation.

## 1. The actual architecture in this PR

| Concern | Previous attempt | This revision |
|---|---|---|
| Lexical identity | legacy `Sym`/String | byte `WordKey`, interned `WordId` |
| Grammar | existing scattered parser cases | immutable `ParseProfile`, finite action tags, first-wins registry |
| Source operator | early `BinOp.rem/ne/...` | `WordId` retained until symbol resolution |
| Namespace | `.global String` | retained entries, ordered namespace search, distinct `SymbolId` |
| Unknown global | old runtime unbound error | binder allocates a global initialized to its reified Symbol |
| Local declaration | old resolver | design binder allocates a fresh declaration before its initializer |
| Surface / bound / executable | old Term plus Plan | `Surface`, `Node SymbolId`, `Node Ref` |
| Executable variable | old Ref | stable declaration + direct global slot / lexical depth and slot |
| Reification | old `Value.symbol String Nat` | declaration identity + optional activation identity |
| While | example-only wrapper | actual node in Surface, Bound, Code, semantics and machine |
| Function call | manually set up body frame | actual new closures, captured activations, fixed-arity call frames |
| Proof target | restricted special abs/r semantics | independent relational semantics for the whole chosen node algebra |

The intended pipeline is:

```text
source bytes
  -- DESIGN-PARSE remains open --> Surface with WordIds
  -- implemented prototype ----> Bound with SymbolIds
  -- implemented prototype ----> Code with direct Refs
  -- implemented prototype ----> Machine.Result(value, reached state)
```

The example **does not yet parse `gcd.m2`**. `surfaceFixture` is explicitly a manually
constructed surface fixture corresponding to that source, not disguised parser output.
Unlike the old example, however, every operation after that boundary uses the new design,
including the complete function definition and call, not a loop-body substitute.
“Implemented prototype” here describes code supplied, not a successful Lean build;
see `VALIDATION.md`.

## 2. Files and responsibilities

| File | Responsibility |
|---|---|
| `Macaulean/Language/Design/Words.lean` | distinct ID domains, exact byte keys, immutable profiles, frozen occurrence metadata, first registration wins |
| `.../IR.lean` | Surface/Bound/Code, Symbols, namespaces, scopes, values, direct locations, primitive contract and reached-state results |
| `.../Binding.lean` | namespace/lexical search, implicit globals, declarations, quotes, aliases, source-ordered resolution and location lowering |
| `.../Machine.lean` | direct-address execution, closure allocation/calls, while, read versus reify, stateful failures |
| `.../Meaning.lean` | independent SymbolId-based relational meaning, frame/closure/state relation and generic lowering obligations |
| `Macaulean/Verification/Examples/GcdTranslation/Program.lean` | grammar/actor seed, source fixture, binding/lowering artifact, actual designed function invocation |
| `.../Semantics.lean` | source-link interface, all-input translation/termination/adequacy propositions |
| `MacauleanTest/GcdTranslation.lean` | concrete design tests, not universal proofs |
| `Examples/GcdTranslation/Worksheet.lean` | ordinary Lean definitions of immutable artifacts and proof targets; no fake new DSL command |
| `scripts/check-gcd-design.py` | limited structural checks and dependency-boundary checks |

## 3. Words are not Symbols, and neither is a primitive opcode

The three distinct steps for `%` are:

```text
wordKey "%" -- intern --> WordId
WordId       -- grammar --> ParseProfile
WordId       -- namespace lookup --> SymbolId
(SymbolId, arity=2) -- actors --> Primitive.rem
```

The grammar seed enumerates the spellings used in the GCD source. It is not a complete
M2 grammar. Profiles are syntactic data, not executable arithmetic callbacks. `Surface`
retains operator WordIds; bound/executable nodes retain `OperatorRef {sourceWord,symbol}`.
The closed exact-integer actor implementation is selected by the resolved SymbolId.

A new ordinary spelling creates only a Word. Encountering an unresolved ordinary name
*during binding* creates its Symbol in the first writable namespace on the search path.
An unknown operator is rejected instead of silently fabricated. Two namespaces can bind
the same Word to different Symbols. Old direct references do not re-resolve after changes
to visibility.

Aliasing updates two separate relations: word/profile history, and namespace entries.
Copying a profile alone does not install an operator. An actual symbol alias preserves
SymbolId while changing the source WordId. A previously registered ordinary spelling
keeps its generic profile. Retained dictionary entries and lexical layouts do not discard
shadowed declarations.

This prototype supports ordinary, global and current-local quotation. Thread-relative
storage is explicitly unsupported rather than incorrectly mapped to a normal global.
Full class/method tables, parser reflection, source-position metadata and host services
remain separate capability TODOs. The primitive Actors table is authoritative for this
closed fragment; there is no second hidden class-table store to keep synchronized.

## 4. The GCD example, without replacing the algorithm

`gcd.m2` contains the source-defined abs helper and the actual while-based algorithm:

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

No built-in gcd or recurrence substitutes for that loop. `abs` is an ordinary interpreted
closure whose body uses the installed `<` and unary `-` operator Symbols. The independent
meaning likewise evaluates its ordinary closure body: it has no special `abs` axiom/rule.

Binding creates a helper scope with parameter `n`, and a GCD scope with:

```text
parameter declaration a -> slot 0
parameter declaration b -> slot 1
local declaration r     -> slot 2
```

`r := ...` creates its declaration before its RHS is resolved, once during binding. The
runtime allocates the three cells once per GCD invocation. The while loop does not create
new scopes or allocate `r` repeatedly. Each abs call has its own activation.

At an iteration boundary `(A,B,R)` the source and target both implement:

```text
r := a % b    -> (A, B, A % B)
a = b         -> (B, B, A % B)
b = r         -> (B, A % B, A % B)
```

The body returns the last assigned value; false while exits with null; the final read of
`a` supplies the function's value. For the concrete fixture, `(1071,462,null)` progresses
to `(462,147,147)`, `(147,21,21)`, `(21,0,0)` and returns 21. These are expected behaviors,
not a report of a native or Lean run in this editing session.

`run` constructs both source-defined closures and invokes the GCD closure with a real
argument list. The target references a direct global location for `abs`, lexical slots
for `a/b/r`, and resolved Symbols for operators. Tests also check that this run needs
only the root frame, the GCD activation, and two abs activations—not one r frame per loop.

## 5. Independent meaning, not an interpreter proving itself by definition

`Meaning.Eval` is an inductive relation over `Bound = Node SymbolId`. Source frames store
SymbolId/value associations. Reading a local searches by declaration identity in the
activation chain. Parameter binding associates supplied values with parameter Symbols.

`Machine.eval` executes `Code = Node Ref`. It follows compiler-computed depth/slot
addresses, and calls fill the parameter prefix of an indexed frame. Neither source
meaning nor `Graph` invokes the compiler or machine evaluator. Both sides intentionally
share the small `primitiveValue` arithmetic contract: that is part of the language we
choose, not an assumption about a foreign computation engine.

Sharing the control-node *datatype family* does not make preservation tautological:
`Node SymbolId` and `Node Ref` have different read/write/call implementations. A wrong
slot, wrong parameter layout, alias mix-up or assignment order can violate the theorem.

The relation currently describes finite normal executions. Machine errors retain reached
state, and depth exhaustion is a separate result. Error traces, abrupt transfers,
divergence and host events need an expanded relation before claiming their preservation.
No native D clause-specific control quirks are imposed.

## 6. What the preservation proof must actually show

`Related` is not an uninterpreted assumption. It requires matching catalogs/actors,
matching global values by declaration and slot, corresponding frame graphs and local
values, and corresponding closures whose bodies are related by lowering under the
captured lexical scope path. `Meaning.WellFormed` fixes parent order, layout/declaration
consistency and parameter layout. IDs agree in the prototype; compacting execution can
later use a separately proved renaming relation.

The reusable obligations `Design.TODO.LowerForward` and `LowerBackward` quantify over
arbitrary admissible bound trees, not just GCD. Their proof route is:

1. **Read/reify:** prove declaration lookup reaches the same activation/location as
   `Binding.address`. Reification returns declaration plus activation, not the cell value.
2. **Write:** prove association update and indexed update preserve `Related`. Different
   declaration slots stay separate; writing one does not affect another. Preserve existing
   unrelated bindings and metadata.
3. **Operators:** related operands and equal actor tables select the same Primitive under
   the same Symbol. WordId is retained but does not decide arithmetic. State that property
   rather than assuming a spelling like `%` forever means remainder.
4. **Sequencing/if:** compose the corresponding subderivations in order, preserving state
   and the returned value, not only a selected local variable.
5. **While:** induct on the finite execution derivation. False guards finish with null.
   True guards give three smaller derivations: guard, body, remaining loop. Thread the
   state relation through all three. Do not invoke gcd correctness in this generic proof.
6. **Functions:** source parameters matched by SymbolId equal target prefix slots because
   lowering validates the parameter/layout invariant. Captured parents agree. Fresh calls
   get distinct activations; reifying the same declaration in two calls gives different
   first-class symbol values.
7. **Resource adequacy:** extract a sufficient target depth bound from a finite source
   derivation and prove success for all larger bounds. A failed bounded run is not a proof
   of divergence. Reverse simulation reconstructs a source derivation from target success.

`Gcd.TODO.Translation` is the all-integer source/target result equivalence for the actual
bound program plus invocation. `Terminates` requires finite source execution for all
integer inputs, using absolute value and strict decrease of positive b. `Adequate` rules
out an always-failing target. These concern execution preservation/existence, not the
mathematical assertion that the result divides both inputs and is greatest.

`Gcd.TODO.Builds` additionally requires a successful artifact construction, so the
conditional translation/termination statements cannot pass through an always-failing
compiler.

All unfinished claims are **definitions of Prop**. `Obligations` lists their types but has
no constructed inhabitant. There are no axioms, admitted proofs, or native answers used
as facts. A definition of a proposition is not an automatically generated theorem.

## 7. Exact TODO and integration boundary

| ID | Required work and acceptance criterion |
|---|---|
| DESIGN-PARSE | Byte lexer/cursor and profile-driven Pratt parser; frozen located tokens and newline policy; exact `SourceLink` for gcd.m2 plus a generic grammar contract. Never return the fixture as a pretend parser. |
| DESIGN-BIND | Prove source-ordered lookup/allocation, first-wins history, namespace shadowing, alias distinction, fresh-local-before-RHS and layout correctness. Add an independent surface binding relation/checker. |
| DESIGN-LOWER | Prove address/read/reify/write lemmas and generic `LowerForward`/`LowerBackward`; kernel-check layout, closure and state invariants. |
| DESIGN-GCD | Instantiate source/target equivalence; prove helper body, three-write simulation, source termination and sufficient target depth. Do not replace by a builtin gcd. |
| DESIGN-OUTCOMES | Extend source meaning to errors, resources, control transfers and divergence under *our* chosen policies; no silent adoption of D quirks. |
| DESIGN-DSL | Replace the fork adapter's semantic payload with the new parser's located Surface, then binding/Code; session stores catalog/activations, not legacy Term/Runtime. Parsing/backtracking must not execute code. |
| DESIGN-EXPORT | Generate immutable versioned source/code/environment/run/Prop declarations from accepted new-frontend syntax. Kernel-check source and preservation links before exporting a theorem. Define relocation for session IDs. |
| DESIGN-REVIEW | Reuse fork dependency sealing and approval UI, but update syntax/code traversal and contract roots. Translation is not a polynomial postcondition schema. |
| DESIGN-STORE | Replace prototype lists with indexed, snapshot-safe stores and indexed namespace lookup under refinement. Preserve reification/capture without allocating a heap object per conceptual identity. |
| DESIGN-CAPABILITIES | Add chosen general object/method/reflection/thread/host semantics with one authoritative store and explicit contracts. Unsupported capability is not successful conformance. |
| DESIGN-CHECK | Run pinned Lean build and guards; audit theorem axioms after proofs exist; record actual status separately from structural validation. |

The old DSL remains available for existing users; this draft does not claim that it now
implements this new frontend. `Worksheet.lean` deliberately does **not** use `open M2` to
bypass that gap. It names immutable Lean artifacts and the new run/translation propositions.

The existing source-file inclusion utility is reused. Existing `LibraryCompiler`,
`Snapshot`, review widgets and session adapter provide engineering patterns, but their
hard-coded legacy Term/Code traversals must be adapted. They are not specification
constraints. Do not retain the old semantics merely to avoid touching those traversals.

## 8. Performance and scope

Prototype collections are lists so the scaffold is easy to inspect. No fast-store claim
is made. Preserve the design's intended performance: cached WordId/profile access, no
name lookup on ordinary machine reads, indexed frames/globals, shared captured activations,
linear tree construction, efficient namespace indexes, and sound actor/method-cache guards.
Benchmark after the observable semantics are fixed; a list-backed proof model is not a
production performance requirement.

Logical cells can be `(activation,slot)`. Source declaration identity and activation
identity are retained without requiring a separate heap cell object per slot. Any future
reflection contract must constrain physical optimizations explicitly.

The catalog is assembled before this closed example executes. A full incremental source
unit must commit word/binding deltas without resetting old runtime globals, and parse the
next statement under the updated environment. This integration remains DESIGN-DSL; do not
call Machine.initial after each statement of a growing session.

## 9. Validation commands

```sh
python scripts/check-gcd-design.py
lake build Macaulean.Verification.Examples.GcdTranslation.Semantics
lake env lean MacauleanTest/GcdTranslation.lean
lake env lean Examples/GcdTranslation/Worksheet.lean
```

The test driver still imports `MacauleanTest.GcdTranslation`. Existing unrelated tests
and PR #40/#41 remain unchanged. Full `lake test` may additionally require the older
suite's normal services; these new tests use no external M2 service.

See `VALIDATION.md` for what actually ran. Structural checks, concrete execution guards,
universal preservation proofs, parser correctness and native compatibility are different
claims. None is implied by the existence of the other artifacts.
