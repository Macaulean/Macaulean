# Audit of the supplied M2 reference and Macaulean complete specification

**Date:** 29 September 2026  
**Verdict:** Do not freeze either document as a complete, source-faithful conformance contract yet. Keep the architectural decomposition; correct and finish the semantic contract before implementation relies on it.

## 1. Scope and method

This audit examines the actual supplied `Macaulay2-language-spec.md` (**R**) and delivered `Macaulean-M2-complete-specification.md` (**S**), including S's verbatim Annex A and its companion grammar/test/validator files. The comparison target is `Macaulay2/M2@1a37f6fe95badb1e5f99707a485503d213fd9d49`, not a moving branch. S's statements about the Macaulean implementation remain tied to its separately declared baseline.

The audit distinguishes **source-confirmed mismatches**, **under-specified contracts**, and **design recommendations**. A source-confirmed result means it follows from inspection of the pinned native code; it does **not** mean the suggested M2 example was executed. Native probes and Lean compilation were not run: this environment has neither executable. There is no new benchmark or proof result. The checks run here are byte/hash and JSON/document validation experiments. The reference's older-binary checkmarks remain claims of that reference, not independently reproduced evidence.

The original inputs were not edited. Annex A matches the original reference. The baseline structural validator passes. Its scope is explicitly not behavior; the negative controls below demonstrate exactly what it does and does not establish. The pinned source was read through the GitHub connector, including parser/binding/lowering, evaluator/control, method/hash-table operations, source-unit hooks, frame reflection, and native builtin registrations.

This is a substantial audit, not a proof that no further discrepancy exists. In particular, the full external engine, every native numerical routine and every Core/package API were not executed or exhaustively re-specified. Those limitations are different from the concrete counterexamples already sufficient to reject a complete-conformance claim.

## 2. Overall assessment

| Dimension | Supplied reference R | New specification S |
|---|---|---|
| Grammar coverage | Detailed Pratt table and algorithm; several overstatements and a source-unit acceptance error | Much better phase separation and word-history model; complete parser-action vocabulary, but inherits the source-unit error |
| Runtime correctness | Useful overview, not a reliable exhaustive operational contract | Repairs several major earlier mistakes, but incorporates remaining wrong rules normatively |
| Completeness | Native primitive/bootstrap boundary is incomplete and partly misclassified | Covers all listed families, but “has a home” does not uniquely define every case |
| Fidelity | Strong on common lexical/scope cases; weaker on effects, reflection and exceptional paths | Strong direction: native effects, alias history, actor-controlled evaluation; important residual mismatches |
| Simplicity | Relatively compact for its breadth, but broad universal claims hide exceptions | Approximately doubles the reference length and distributes authority over body, amendments, annex and generated data |
| Verification | Useful input to a formal semantics | Good roadmap and abstraction boundaries; not yet a closed runtime relation suitable as the final refinement target |

### What should be retained

The decomposition into word spelling/profile, dictionary binding, declaration identity and activation/storage identity is sound as a design direction. S improves the earlier drafts by recording all ordinary word registrations under first-registration-wins, using bytes rather than assuming valid Unicode, preserving source-word and resolved-symbol identity separately, retaining exact Pratt actions/newline lookahead, treating square brackets as Array syntax rather than a polynomial-ring production, resolving globals through dictionary paths, distinguishing thread-relative reads from reified cells, retaining native partial effects on errors, and putting primitive fast paths before method fallback where native actors do so. Its explicit distinction between an unexecuted test plan and executed conformance is also correct.

Several errors in R are **already amended in S**, and should not be counted as new failures of S: the blanket `SPACE` rejection; restriction of fixed parameter syntax to round parentheses; unconditional interning of literal occurrences; the BNF-impossibility claim; and the lookup flag described as merely a warning. The real-literal conversion phase is also clarified usefully. The problem is the remaining unamended behavior, not failure to notice these repairs.

## 3. Finding index

High means a semantic divergence or material missing contract that blocks the claimed conformance scope. Medium means a narrower divergence, significant under-specification, validation weakness or design simplification. Severity does not claim how commonly packages exercise a behavior.

| ID | Severity | Applies to | Finding |
|---|---|---|---|
| F01 | High | Reference and specification | The claimed core boundary omits native primitives and a bootstrap ABI |
| F02 | High | Reference and specification | AfterEval has the wrong method key |
| F03 | High | Reference and specification | Standalone semicolons are incorrectly accepted by the source-unit grammar |
| F04 | High | Reference and specification | Loop control cannot be specified by a uniform innermost-loop rule |
| F05 | High | Reference and specification | The typed completion taxonomy changes try on step and finish |
| F06 | High | Reference and specification | The second left evaluation of <=/>= does not obey blanket error propagation |
| F07 | High | Specification; reference under-specifies errors | Binding failure effects and traversal are not optional |
| F08 | High | Reference and specification | Assignment-hook lookup time is unspecified |
| F09 | Medium | Reference and specification | Symbol identity immutability is conflated with isMutable |
| F10 | Medium | Reference and specification | CacheTable equality omits class and parent conditions |
| F11 | Medium | Reference and specification | Augmented Default dispatch is name-based, not canonical-symbol identity |
| F12 | High | Reference and specification | Augmented hash-table assignment needs an explicit operand schedule |
| F13 | Medium | Reference and specification | Not every assignment expression returns its supplied RHS |
| F14 | High | Reference and specification | Reflective frame APIs have aliasing semantics, not just display semantics |
| F15 | Medium | Specification | Dictionary history, enumeration and cardinality are not fixed by “shadowing map” |
| F16 | High | Reference and specification | Source-unit hook failures and wrappers need a total policy table |
| F17 | High | Specification | Actor and host interfaces are named but not completely contracted |
| F18 | Medium | Specification | Method state and class hash tables need one authoritative view |
| F19 | Medium | Reference and specification | Strict native conformance and intentional safe departures need separate labels |
| F20 | Medium | Bundle | The structural validator misses inconsistencies within its own data boundary |
| F21 | Medium | Bundle | The 146-case corpus is a test plan, not an executable conformance oracle |
| F22 | Medium | Specification | The normative organization duplicates too much and obscures authority |
| F23 | Medium | Specification | Do not make every logical identity a mandatory hot-path allocation |
| F24 | High | Specification | The proof roadmap has no fully defined runtime transition relation to refine yet |

## 4. Detailed findings

### F01. The claimed core boundary omits native primitives and a bootstrap ABI

**Severity:** High · **Evidence:** source-confirmed omission  
**Affected:** Reference and specification  
**Locations:** R §0.1, §§5–7; S §§0, 9.1, 10.3, 11

The reference describes apply and scan as functions supplied by the M2-language library. It then excludes that library from the core specification. This is not an accurate division of the pinned implementation. The new specification incorporates the same boundary without repairing it.

**Evidence.** actors3.d registers setupfun("apply",map) and setupfun("scan",scan). It also implements override. Other native interfaces used by Core include frame, frames, localDictionaries, lookup/installMethod, value', symbolBody and dictionary operations. Merely naming a Value representation or requiring that Core eventually load does not specify these APIs.

**Consequence.** An independent implementation can implement every grammar production and every table row yet still be unable to bootstrap Core. The current K/L distinction does not tell it which interpreter-provided names, calling conventions and effects must already exist.

**Correction.** Add a versioned bootstrap/primitive manifest: exported name, initial binding and protection, arity, accepted values, evaluation/control policy, result, state effects and errors. Distinguish native primitives, library wrappers/overloads, and external host/engine primitives. Contracts may incorporate a pinned external standard, but each required interface must be enumerated.

**Pinned source:** [N4: actors3.d](https://github.com/Macaulay2/M2/blob/1a37f6fe95badb1e5f99707a485503d213fd9d49/M2/Macaulay2/d/actors3.d) — `lessequalfun2; greaterequalfun2; EqualEqualfun; override; apply/scan registrations`; [N7: hashtables.dd](https://github.com/Macaulay2/M2/blob/1a37f6fe95badb1e5f99707a485503d213fd9d49/M2/Macaulay2/d/hashtables.dd) — `mutablefun; installIt; installMethod; lookupBinaryMethod`; [N10: actors5.d](https://github.com/Macaulay2/M2/blob/1a37f6fe95badb1e5f99707a485503d213fd9d49/M2/Macaulay2/d/actors5.d) — `frame; frames; localDictionaries; dictionaryPath; values via actors2.dd`.

### F02. AfterEval has the wrong method key

**Severity:** High · **Evidence:** source-confirmed mismatch  
**Affected:** Reference and specification  
**Locations:** R §7.4; S §§9.1, 10.1–10.2

R requires {mode, AfterEval}, alongside mode-qualified printing hooks. S adopts that protocol without an amendment.

**Evidence.** readeval4 calls runmethod(AfterEval,lastvalue). It separately constructs modeBeforePrint, modeNoPrint/modePrint and modeAfterNoPrint/modeAfterPrint. BeforeEval is likewise unqualified and is invoked on null. The source comment explicitly states that BeforeEval is mode-independent.

**Consequence.** An implementation following the document searches a different method-table key, so it misses a valid AfterEval hook. This can affect the result passed to subsequent printing/history logic, not just formatting.

**Correction.** Specify exact keys and arguments: BeforeEval(null), AfterEval(value), then the mode-qualified BeforePrint, Print/NoPrint and AfterPrint/AfterNoPrint. Include success-result handling and the failure policies in F16.

**Pinned source:** [N1: interp.dd](https://github.com/Macaulay2/M2/blob/1a37f6fe95badb1e5f99707a485503d213fd9d49/M2/Macaulay2/d/interp.dd) — `readeval4; readeval; load; value`.

**Regression to add (not native-executed):**

Install different handlers under AfterEval and {Standard,AfterEval}; evaluate one printing-enabled input. Only the unqualified AfterEval hook is selected by the driver.

### F03. Standalone semicolons are incorrectly accepted by the source-unit grammar

**Severity:** High · **Evidence:** source-confirmed mismatch  
**Affected:** Reference and specification  
**Locations:** R §§2.6, 7.1; S §§6.6, 10.1

Both documents instruct the driver to skip semicolon tokens between statements, admitting leading semicolons and repeated empty semicolon statements.

**Evidence.** readeval4 skips NewlineW and wordEOC, and terminates on wordEOF. It does not skip SemicolonW. A semicolon encountered at the start of the next statement therefore reaches parse(...,8,true), whose leading action for semicolon is Error. A semicolon is valid when consumed as the terminator of a preceding expression.

**Consequence.** The documented accepted source language differs from the pinned driver: ;1 and 1;;2 are not interchangeable with 1 and 1;2. A separate parse utility is not necessarily an oracle for source-unit execution.

**Correction.** Remove semicolon from the driver's initial skip set. Keep it in the post-expression terminator set. Test parse-tree APIs and source-unit APIs separately, including leading/repeated/trailing semicolons.

**Pinned source:** [N1: interp.dd](https://github.com/Macaulay2/M2/blob/1a37f6fe95badb1e5f99707a485503d213fd9d49/M2/Macaulay2/d/interp.dd) — `readeval4; readeval; load; value`; [N12: parser.d](https://github.com/Macaulay2/M2/blob/1a37f6fe95badb1e5f99707a485503d213fd9d49/M2/Macaulay2/d/parser.d) — `parse; nparse; accumulate; all parser handlers`.

**Regression to add (not native-executed):**

```m2
;1
```

Syntax failure at a leading semicolon, not successful evaluation of 1.

### F04. Loop control cannot be specified by a uniform innermost-loop rule

**Severity:** High · **Evidence:** source-confirmed mismatch  
**Affected:** Reference and specification  
**Locations:** R §§6.2, 6.9; S §§9.2, 9.4–9.5

The reference says continue is intercepted by the innermost loop and summarizes collecting loops with one rule. S preserves this broad rule. Native behavior depends on which loop form and which clause produced the completion.

**Evidence.** In while-do, bare Continue is handled in the do body but not the predicate. In while-list-do, Continue from the collector skips the append but still runs the do clause; even bare Continue from the do clause propagates. In for, bare Continue from do is handled, but Continue(value) from do propagates; Continue from when propagates. Bare Break in a while-list predicate returns null, whereas bare Break in a while-list-do predicate returns the collected list.

**Consequence.** A generic handler around the whole loop changes control flow, collection contents, outer-loop behavior and termination. These distinctions are observable without any exotic engine objects.

**Correction.** Replace the prose shortcut with a matrix indexed by loop form, active clause and completion kind. Define a continuation for each clause. Keep typed completions, but dispatch them at exactly the native catch boundaries.

**Pinned source:** [N2: evaluate.d](https://github.com/Macaulay2/M2/blob/1a37f6fe95badb1e5f99707a485503d213fd9d49/M2/Macaulay2/d/evaluate.d) — `evalWhileDoCode; evalWhileListCode; evalWhileListDoCode; evalForCode`.

**Regression to add (not native-executed):**

```m2
i=0; a=while (if i==1 then break else true) list (i=i+1); i=0; b=while (if i==1 then break else true) list (i=i+1) do null; (a,b)
```

a is null; b is the one-element List {1}. Source-derived, not executed.

### F05. The typed completion taxonomy changes try on step and finish

**Severity:** High · **Evidence:** source-confirmed mismatch  
**Affected:** Reference and specification  
**Locations:** R §§6.2, 6.9; S §9.2

S states that try catches only Error and excludes the distinct control completions. R categorizes step/finish as debugger transfers and excludes control completions in its try description. This tidy taxonomy is not the pinned catchability predicate.

**Evidence.** tryEval excludes break, return, both continue forms, unwind and throw from caught errors. Its exclusion list does not contain step, step-with-argument or finish. Those messages are produced by the corresponding actors and can be caught when ordinary suppression remains enabled.

**Consequence.** For example, the source predicts try finish 3 else 7 selects the else branch. An evaluator that propagates every DebugControl completion instead is incompatible.

**Correction.** Define an explicit catchableByTry predicate, including suppression/interrupt conditions, rather than deriving it from a broad Error-versus-Control type split. Classify a deliberate cleanup of this behavior as a separate compatibility policy.

**Pinned source:** [N3: evaluate.d](https://github.com/Macaulay2/M2/blob/1a37f6fe95badb1e5f99707a485503d213fd9d49/M2/Macaulay2/d/evaluate.d) — `tryEval; evalTryCode; trapfun`.

**Regression to add (not native-executed):**

```m2
try finish 3 else 7
```

7 under the pinned tryEval policy; unexecuted.

### F06. The second left evaluation of <=/>= does not obey blanket error propagation

**Severity:** High · **Evidence:** source-confirmed mismatch  
**Affected:** Reference and specification  
**Locations:** R §§6.2, 6.10; S §9.5

The reference correctly notices that <= and >= evaluate their left operand twice, but omits the behavior of a failure on the second evaluation. Its universal abrupt-propagation rule is consequently false. S inherits the incomplete operator rule.

**Evidence.** lessequalfun2 and greaterequalfun2 first run compareop(lhs,rhs) and propagate its Error. They then evaluate lhs again into L. They inspect whether L is an RR interval but do not branch on L being an Error; the non-interval branch returns a Boolean derived from the earlier comparison. Their interval cases also recognize <=/>= comparison keywords and distinguish degenerate intervals, unlike the abbreviated truth rule in R.

**Consequence.** A conventional monadic eval of the second operand propagates a completion that the native actor ignores. Implementations can disagree on returned value, side effects and diagnostics while both claiming to obey the current prose.

**Correction.** Specify these actor branches explicitly: first comparison, failure check, second evaluation, interval inspection, final Boolean. Separate the native compatibility rule from any corrected language mode. Add second-evaluation failure/control and interval cases, not just the existing counter-increment test.

**Pinned source:** [N4: actors3.d](https://github.com/Macaulay2/M2/blob/1a37f6fe95badb1e5f99707a485503d213fd9d49/M2/Macaulay2/d/actors3.d) — `lessequalfun2; greaterequalfun2; EqualEqualfun; override; apply/scan registrations`.

**Regression to add (not native-executed):**

```m2
n=0; f=()->(n=n+1; if n==1 then 1 else error "second"); r=try(f()<=2); (r,n)
```

Source predicts (true,2), with the second evaluation inside error suppression; unexecuted.

### F07. Binding failure effects and traversal are not optional

**Severity:** High · **Evidence:** source-confirmed ordering gap  
**Affected:** Specification; reference under-specifies errors  
**Locations:** R §3; S §§7.1, 7.6

S permits diagnostic recovery to continue the native binding traversal, but also allows return of the state reached at failure. Its assignment table places capability validation in LHS processing before the RHS. Neither choice is harmless because binding allocates globally visible symbols.

**Evidence.** bindassignment binds the RHS before checking unary/postfix/binary method capability. bind records errors through HadError and often continues traversing later children; localBind only returns the aggregate success flag afterward. There are also explicit early returns for some invalid target shapes. Thus there is a definite per-branch traversal, not permission to stop or continue arbitrarily.

**Consequence.** The input #AuditTarget := AuditRhsAfterInvalidMethod fails binding, but the pinned traversal creates the RHS global before reporting the unsupported method target. A fail-fast binder following the table can leave it absent. Later isGlobalSymbol observations distinguish the states.

**Correction.** Specify every validation point and error-continuation edge. Model ordered diagnostics and reached state, but make the traversal deterministic. Do not implement the binder as a generic short-circuit Except monad unless its continuations reproduce those edges.

**Pinned source:** [N5: binding.d](https://github.com/Macaulay2/M2/blob/1a37f6fe95badb1e5f99707a485503d213fd9d49/M2/Macaulay2/d/binding.d) — `bindassignment; bind; localBind; insert; makeEntry`.

**Regression to add (not native-executed):**

```m2
try value "#AuditTarget := AuditRhsAfterInvalidMethod"; isGlobalSymbol "AuditRhsAfterInvalidMethod"
```

true in a fresh session after the caught binding failure; unexecuted.

### F08. Assignment-hook lookup time is unspecified

**Severity:** High · **Evidence:** source-confirmed ordering gap  
**Affected:** Reference and specification  
**Locations:** R §6.6.1; S §9.6; corpus S011

The documents give hook invocation order, but do not distinguish when each hook is selected. A symbol-specific hook can modify the relevant class method tables.

**Evidence.** globalAssignmentHook looks up and captures the old-class GlobalReleaseHook before invoking symbol-specific hooks. It later invokes that captured method. It looks up the new-class GlobalAssignHook only after the symbol-specific and release-hook calls.

**Consequence.** Re-looking up the release hook after a symbol hook changes it selects a different function. The existing test S011 checks only the call order and will miss this difference.

**Correction.** Specify the sequence capture-release; invoke-symbol-hooks; invoke-captured-release; lookup-and-invoke-new-assignment; store. Test a symbol hook that replaces/removes the release method and one that changes the new-class assignment method.

**Pinned source:** [N6: evaluate.d](https://github.com/Macaulay2/M2/blob/1a37f6fe95badb1e5f99707a485503d213fd9d49/M2/Macaulay2/d/evaluate.d) — `globalAssignmentHook; globalAssignment; assigntofun`.

**Regression to add (not native-executed):**

A symbol-specific assignment hook replaces the old class GlobalReleaseHook before the release call. The previously captured release method runs; later assignments can observe the replacement.

### F09. Symbol identity immutability is conflated with isMutable

**Severity:** Medium · **Evidence:** source-confirmed mismatch  
**Affected:** Reference and specification  
**Locations:** R §5.3; S §§9.1, 9.3

The reference lists symbols among immutable values without specifying the native isMutable behavior. S incorporates that statement while treating protection separately.

**Evidence.** mutablefun returns !symbol.Protected for SymbolClosure and !dictionary.Protected for DictionaryClosure. A symbol can keep the same identity/hash while the language reports it as mutable; protect changes that report.

**Consequence.** Reading “symbols are immutable” as an implementation rule produces the wrong user-visible isMutable result and confuses suitability as a stable key with assignment capability.

**Correction.** Separate immutable declaration/activation identity, mutation of the stored binding value, and the native isMutable predicate. State the predicate explicitly for every representation covered by the API.

**Pinned source:** [N7: hashtables.dd](https://github.com/Macaulay2/M2/blob/1a37f6fe95badb1e5f99707a485503d213fd9d49/M2/Macaulay2/d/hashtables.dd) — `mutablefun; installIt; installMethod; lookupBinaryMethod`.

**Regression to add (not native-executed):**

```m2
s=symbol AuditMutable; a=isMutable s; protect s; (a,isMutable s)
```

(true,false) for a fresh unprotected global symbol; unexecuted.

### F10. CacheTable equality omits class and parent conditions

**Severity:** Medium · **Evidence:** source-confirmed mismatch  
**Affected:** Reference and specification  
**Locations:** R §§5.3, 5.5; S §9.1

The reference says CacheTables have hash zero and are all strictly equal to one another. The new document does not amend that claim.

**Evidence.** equal(HashTable,HashTable) first handles object identity, rejects different hashes, then rejects different Class or parent identities. Only afterward does it accept hash-zero objects whose exact class is cacheTableClass. This is not a blanket rule for all cache tables or their subclasses.

**Consequence.** Cache tables with different parents can be unequal. An implementation using one universal equality class for them changes strict comparisons and hash-key semantics.

**Correction.** State the equality branch in source order. Keep the special case separate from ordinary mutable-table identity and from subclass behavior.

**Pinned source:** [N8: equality.dd](https://github.com/Macaulay2/M2/blob/1a37f6fe95badb1e5f99707a485503d213fd9d49/M2/Macaulay2/d/equality.dd) — `equal(HashTable,HashTable); equal(Expr,Expr)`.

**Regression to add (not native-executed):**

Construct two direct CacheTable instances with different valid parents and compare with ===. false, because the parent comparison precedes the cache special case.

### F11. Augmented Default dispatch is name-based, not canonical-symbol identity

**Severity:** Medium · **Evidence:** source-confirmed mismatch  
**Affected:** Reference and specification  
**Locations:** R §6.7; S §9.6

The phrase “the symbol Default” suggests a distinguished global sentinel identity, consistent with the rest of the proposed SymbolId architecture.

**Evidence.** augmentedAssignmentFun checks whether the method result is a SymbolClosure and then compares s.symbol.word.name with the bytes "Default". It does not compare the result with a single predefined Default SymbolId.

**Consequence.** A different local/dictionary symbol with canonical spelling Default also requests fallback. An identity-only sentinel test produces a different result.

**Correction.** Specify the exact canonical-spelling test. Alternatively declare identity-only behavior an explicit non-native change; do not silently infer it from the general identity model.

**Pinned source:** [N9: evaluate.d](https://github.com/Macaulay2/M2/blob/1a37f6fe95badb1e5f99707a485503d213fd9d49/M2/Macaulay2/d/evaluate.d) — `augmentedAssignmentFun; augmentedParallelAssignmentFun; parallelAssignmentFun`.

**Regression to add (not native-executed):**

An augmented assignment method returns a non-global SymbolClosure whose canonical spelling is Default. The native actor falls back rather than returning that symbol as the completed augmented result.

### F12. Augmented hash-table assignment needs an explicit operand schedule

**Severity:** High · **Evidence:** source-confirmed ordering gap  
**Affected:** Reference and specification  
**Locations:** R §6.7; S §§8.5, 9.6

R says that the container and key are evaluated once and the RHS precedes lookup. That does not uniquely specify the order of key evaluation relative to RHS evaluation. S delegates to this prose.

**Evidence.** For a hash-table # target, augmentedAssignmentFun evaluates the container, then the RHS, then the key, then performs lookup/locking. This is different from the ordinary element-store container/key/RHS schedule. Field keys use the reified symbol path instead.

**Consequence.** An RHS that changes a variable read by the key expression can change which entry gets updated. Caching the key before RHS is not faithful even though it evaluates the key once and performs lookup after RHS.

**Correction.** Give a per-target evaluation schedule for variable, hash-table index, field, other operator and parallel targets. Explicitly identify cached versus re-evaluated subexpressions, including the special ??= path.

**Pinned source:** [N9: evaluate.d](https://github.com/Macaulay2/M2/blob/1a37f6fe95badb1e5f99707a485503d213fd9d49/M2/Macaulay2/d/evaluate.d) — `augmentedAssignmentFun; augmentedParallelAssignmentFun; parallelAssignmentFun`.

**Regression to add (not native-executed):**

```m2
i=0; T=new MutableHashTable from {0=>10,1=>20}; T#i += (i=1;5); (T#0,T#1)
```

Source predicts (10,25), since the key i is read after RHS; unexecuted.

### F13. Not every assignment expression returns its supplied RHS

**Severity:** Medium · **Evidence:** internal contradiction and source-confirmed correction  
**Affected:** Reference and specification  
**Locations:** R §6.6 introduction versus §§6.6.4, 6.7; S §9.6

R begins assignment semantics with the universal claim that every assignment expression has the assigned value. Later custom assignment and augmented-method rules allow a method-produced result instead.

**Evidence.** The native operator-assignment paths return the invoked assignment method result. An augmented method can intercept the operation and return without performing the fallback store. parallelAssignmentFun assembles actual per-target results and unwraps the single-target result.

**Consequence.** The blanket rule contradicts the more specific rules and encourages invalid rewrites of assignment expressions. It also leaves one-target List/Sequence result shaping easy to misread.

**Correction.** Replace the universal sentence with per-form results: direct store result; method result; intercepted augmented result; recursive parallel result with the native single-target unwrapping.

**Pinned source:** [N9: evaluate.d](https://github.com/Macaulay2/M2/blob/1a37f6fe95badb1e5f99707a485503d213fd9d49/M2/Macaulay2/d/evaluate.d) — `augmentedAssignmentFun; augmentedParallelAssignmentFun; parallelAssignmentFun`; [N6: evaluate.d](https://github.com/Macaulay2/M2/blob/1a37f6fe95badb1e5f99707a485503d213fd9d49/M2/Macaulay2/d/evaluate.d) — `globalAssignmentHook; globalAssignment; assigntofun`.

### F14. Reflective frame APIs have aliasing semantics, not just display semantics

**Severity:** High · **Evidence:** source-confirmed omission  
**Affected:** Reference and specification  
**Locations:** R core/API coverage; S §§3, 8.1, 9.4, 12.4

The documents require preservation of frame observations while never specifying frame/frames as native APIs. Describing logical frames and shared closures is not sufficient for this interface.

**Evidence.** actors5.d listFrame(f) returns a MutableList wrapping f.values for a non-global frame. frame and frames expose these wrappers; the global-frame case returns an empty sequence to avoid defeating global protection. Existing-slot writes through such a wrapper can modify the live frame values. localDictionaries exposes related dictionary/frame closures.

**Consequence.** Returning a copied list, always materializing an extra empty logical frame, or optimizing away a frame without the native observation projection can break Core code that inspects or accesses captured state. This is also a memory/aliasing obligation for any flattened-cell implementation.

**Correction.** Specify exact frame API shapes, live aliasing, global hiding, and empty-frame behavior. Define views into storage, not just copied object values. Use these contracts to delimit frame-elision and closure-conversion proofs.

**Pinned source:** [N10: actors5.d](https://github.com/Macaulay2/M2/blob/1a37f6fe95badb1e5f99707a485503d213fd9d49/M2/Macaulay2/d/actors5.d) — `frame; frames; localDictionaries; dictionaryPath; values via actors2.dd`; [N15: expr.d](https://github.com/Macaulay2/M2/blob/1a37f6fe95badb1e5f99707a485503d213fd9d49/M2/Macaulay2/d/expr.d) — `newSymbolHashTable; frame allocation; dictionary creation`.

**Regression to add (not native-executed):**

Obtain a live non-global frame wrapper, overwrite an existing slot, then read the captured variable through its closure. The closure observes the overwritten value; not a detached snapshot.

### F15. Dictionary history, enumeration and cardinality are not fixed by “shadowing map”

**Severity:** Medium · **Evidence:** design under-specification  
**Affected:** Specification  
**Locations:** R dictionary APIs; S §§3.3, 7.7

S says a later := replaces the visible mapping and retains old symbols in stores/layouts. It does not define whether dictionary enumeration and length include retained shadowed entries, or how those differ from active lookup.

**Evidence.** Native makeEntry inserts a new symbol-table entry; insert increments numEntries and prepends the entry. Native dictionary values/pairs walk table entries rather than a deduplicated visible-name map. The phrase “ordered shadowing map” could support this, but only with additional specified operations.

**Consequence.** A normal finite-map implementation can preserve lexical lookup while reporting different #dictionary, keys, values or pairs results after redeclaration.

**Correction.** Define lookup separately from ordered entry storage and enumeration. Specify alias insertion, redeclaration, protection and erase effects on each view. Do not assume retaining SymbolInfo alone reproduces dictionary observations.

**Pinned source:** [N5: binding.d](https://github.com/Macaulay2/M2/blob/1a37f6fe95badb1e5f99707a485503d213fd9d49/M2/Macaulay2/d/binding.d) — `bindassignment; bind; localBind; insert; makeEntry`; [N14: actors2.dd](https://github.com/Macaulay2/M2/blob/1a37f6fe95badb1e5f99707a485503d213fd9d49/M2/Macaulay2/d/actors2.dd) — `values and pairs on DictionaryClosure`.

### F16. Source-unit hook failures and wrappers need a total policy table

**Severity:** High · **Evidence:** source-confirmed omission  
**Affected:** Reference and specification  
**Locations:** R §§7.2–7.5; S §10

The source-unit driver is only schematic about hook failures, stopIfError/returnIfError, and which abrupt results file/value wrappers consume. These policies are essential when traces and reached states are part of conformance.

**Evidence.** In readeval4, a BeforeEval error can be recorded and execution still proceeds when neither stop flag demands return. A non-stopping AfterEval error replaces lastvalue with null before later printing steps. load/value wrappers recognize step and finish as well as return, break and both continue forms; throw is not included in that wrapper-unwrapping list. File exit hooks run in their own defined order and retain the last exit error.

**Consequence.** Two interpreters following the current pseudocode can both claim conformance while one skips an input that the other executes, or they return/print different values after hook failures.

**Correction.** Provide a table by source-unit kind, driver flags, failure stage and completion. Include BeforeEval, evaluation, AfterEval, BeforePrint, Print/NoPrint, AfterPrint/AfterNoPrint, file-exit and close failures, together with precise propagation and state behavior.

**Pinned source:** [N1: interp.dd](https://github.com/Macaulay2/M2/blob/1a37f6fe95badb1e5f99707a485503d213fd9d49/M2/Macaulay2/d/interp.dd) — `readeval4; readeval; load; value`.

### F17. Actor and host interfaces are named but not completely contracted

**Severity:** High · **Evidence:** design under-specification  
**Affected:** Specification  
**Locations:** S §§3.3, 9.1, 9.5, 10.3, 11; R §6.10

ActorId is used in SymbolInfo without a complete actor universe, bootstrap assignment/default rule or per-actor transition definition. The host interface likewise refers to admissible results satisfying primitive contracts that are not enumerated in the bundle.

**Evidence.** The document supplies a useful complete parser-action algebra, but no analogous complete runtime-actor catalog. R's broad numeric promotion/MPFR summaries and operator fallback rows do not define every accepted/error/control case. Named primitives outside the table remain unspecified.

**Consequence.** The K-level interpreter is not uniquely implementable from the document. “Run the native actor” and “satisfy the primitive contract” are references to work still to specify, not closed definitions.

**Correction.** Give each actor/primitive a contract ID, bootstrap symbol, operand schedule, core case dispatch, fallback key and errors. Parameterize platform limits and numerical backend details explicitly; refer to pinned external arithmetic contracts where appropriate. Keep external engine implementation out of scope without leaving its interface undefined.

**Pinned source:** [N4: actors3.d](https://github.com/Macaulay2/M2/blob/1a37f6fe95badb1e5f99707a485503d213fd9d49/M2/Macaulay2/d/actors3.d) — `lessequalfun2; greaterequalfun2; EqualEqualfun; override; apply/scan registrations`; [N7: hashtables.dd](https://github.com/Macaulay2/M2/blob/1a37f6fe95badb1e5f99707a485503d213fd9d49/M2/Macaulay2/d/hashtables.dd) — `mutablefun; installIt; installMethod; lookupBinaryMethod`.

### F18. Method state and class hash tables need one authoritative view

**Severity:** Medium · **Evidence:** design under-specification  
**Affected:** Specification  
**Locations:** R §6.5; S §§3.5, 9.7

S has both methods/nullaryMethods/typicalValues stores and mutable class objects. It says reflective equivalence must be maintained, but does not define the ownership or synchronization law for direct M2 table writes.

**Evidence.** Native method entries are ordinary observable entries in class hash tables, and lookup searches those tables. Code can inspect and mutate those entries. The new spec correctly recognizes the issue, but recognizing it is not a definition of which store controls a later dispatch.

**Consequence.** An implementation can accidentally create a hidden method registry that diverges from visible class objects. Cache invalidation alone does not repair two authoritative sources of truth.

**Correction.** Define method operations as views of the authoritative class/object store, with any separate method table explicitly derived and guarded. State entry placement/observation policy and the effects of direct table mutations. Avoid a second mutable registry unless a preservation invariant is supplied.

**Pinned source:** [N7: hashtables.dd](https://github.com/Macaulay2/M2/blob/1a37f6fe95badb1e5f99707a485503d213fd9d49/M2/Macaulay2/d/hashtables.dd) — `mutablefun; installIt; installMethod; lookupBinaryMethod`.

### F19. Strict native conformance and intentional safe departures need separate labels

**Severity:** Medium · **Evidence:** design boundary ambiguity  
**Affected:** Reference and specification  
**Locations:** R §1.8; S R11, §§6.3, 8.4

The specification explicitly rejects malformed radix/real literals and introduces safe handling of invalid delimiter aliases; it also requires a valid global-key invariant for some alias-created field code. These are not all claims of byte-for-byte native behavior.

**Evidence.** The R11 rejection is honestly documented, and the native source can have unsafe or inconsistent internal paths. The issue is not that safe rejection is wrong; it is that the same conformance label can otherwise obscure whether a failed native differential test is expected.

**Consequence.** A tester cannot infer from “K-conforming” whether to demand exact source behavior, an intentional portable deviation, or rejection outside the admitted native domain.

**Correction.** Define a strict pinned-native profile on its valid domain and a separately named portable/safe profile with an explicit deviation ledger. For native undefined behavior, state domain restrictions rather than requiring a crash. Give each deviation an expected test outcome and phase.

**Pinned source:** [N11: lex.d](https://github.com/Macaulay2/M2/blob/1a37f6fe95badb1e5f99707a485503d213fd9d49/M2/Macaulay2/d/lex.d) — `makeUniqueWord; gettoken; gettoken1`; [N12: parser.d](https://github.com/Macaulay2/M2/blob/1a37f6fe95badb1e5f99707a485503d213fd9d49/M2/Macaulay2/d/parser.d) — `parse; nparse; accumulate; all parser handlers`; [N13: convertr.d](https://github.com/Macaulay2/M2/blob/1a37f6fe95badb1e5f99707a485503d213fd9d49/M2/Macaulay2/d/convertr.d) — `convertTokenReference; convertParentheses; convert0`.

### F20. The structural validator misses inconsistencies within its own data boundary

**Severity:** Medium · **Evidence:** executed validator limitation  
**Affected:** Bundle  
**Locations:** S §§4.2, 13.2, 14; validate_spec.py

The validator compares the JSON against the supplied reference table, not the normative table in the new document, and validates quotation policy membership without validating which policy belongs to which quote word. Its native_table_words_compared field names a comparison against the supplied document, not a direct native-source extraction.

**Evidence.** On isolated copies I changed the main document plus/minus lbp from 50 to 49: PASS. I changed quote_symbol.quote_policy from ordinary to global: PASS. I also changed E001's expected arithmetic value from 7 to 999: PASS. The last result is expected for a structural validator; the first two identify useful additional structural consistency checks.

**Consequence.** G0 does not currently establish agreement among all normative grammar artifacts. A PASS should not be cited as source-verified grammar correctness or correct behavioral expectations.

**Correction.** Compare the normative main table and JSON, check fixed quote-policy/word associations and lexical routes, validate all checksum entries and HTML generation if those are claimed, and rename the supplied-table metric. Keep behavioral checking separate and independent.

**Regression to add (not native-executed):**

Three isolated mutations, original inputs unchanged. All three mutated copies still pass validate_spec.py.

### F21. The 146-case corpus is a test plan, not an executable conformance oracle

**Severity:** Medium · **Evidence:** executed inventory; design gap  
**Affected:** Bundle  
**Locations:** conformance-cases.json; S §14

The corpus truthfully labels itself UNEXECUTED and uses human-readable tree/value/state descriptions. Fourteen entries are scenario steps rather than complete M2 source. Negative examples and setup do not yet form an automated typed oracle.

**Evidence.** The file contains 50 parse cases, 10 source-unit-parse cases, 15 lex-or-literal-decode cases, one lex case, one literal-decode case, 19 bind-or-lower cases, 36 evaluation cases and 14 state scenarios. The planned all-word/operator-pair and every-primitive generation is a requirement for future work, not delivered coverage.

**Consequence.** Case count is not a completeness measure. Current examples miss the loop-clause matrix, AfterEval qualification, second-evaluation failure, standalone semicolons, binding-error state, and mutable reflection identified here.

**Correction.** Build typed expectations with precise initial state, source-unit kind, phase, completion, state delta and trace. Add the audit regressions. Generate coverage from stable rule IDs, but obtain expectations independently of the implementation under test. Preserve raw native version/exit/stdout/stderr records.

### F22. The normative organization duplicates too much and obscures authority

**Severity:** Medium · **Evidence:** editorial/architecture recommendation  
**Affected:** Specification  
**Locations:** S §0, §1, §§4–10 and Annex A

The new file adds approximately 12,885 whitespace-delimited words before reproducing the approximately 14,046-word reference. Many runtime clauses delegate to the reference, while others amend it. A reader must combine the original rule, amendment ledger, body refinements and manifest to know the effective requirement.

**Evidence.** This is particularly costly where an incorporated runtime sentence is wrong or where a body refinement is only qualitative. Verbatim preservation is useful for provenance, but it should not force an erroneous archived text to remain a concurrent normative source.

**Consequence.** The structure makes omissions hard to see and allows the apparent completeness of the larger document to exceed the actual precision of its runtime rules.

**Correction.** Maintain one corrected normative language contract, a generated grammar manifest, a separate architecture/refinement document, and a non-normative change ledger/archive. Link stable rule IDs across them. Generate duplicate tables rather than hand-maintaining them.

### F23. Do not make every logical identity a mandatory hot-path allocation

**Severity:** Medium · **Evidence:** architecture/performance recommendation  
**Affected:** Specification  
**Locations:** S §§3, 12, 15

Distinct semantic IDs are useful, but the specification risks turning a frame-to-cell-ID-to-cell object graph and SymbolId-bearing ordinary reads into mandatory machine layouts. That adds indirection and proof obligations that M2 fidelity does not require.

**Evidence.** A cell can be modeled as a pair (activation,slot), with a separate first-class reification operation. Ordinary resolved reads may carry only a direct address plus validated metadata, while debug/reification paths retain declaration identity. The document already permits refinement, so these representation freedoms should be explicit rather than obscured by normative schema language.

**Consequence.** Unnecessary per-local cell objects, redundant declaration fields on every hot instruction, and eagerly duplicated method stores can cost memory and allocation without improving semantic fidelity.

**Correction.** Keep logical domains distinct in the specification; allow frame-slot addresses or compact cells in the machine. Require identity/reification observations and proof obligations, not redundant physical records. Retain interned words, profile caching, indexed storage and snapshot-aware benchmarking.

### F24. The proof roadmap has no fully defined runtime transition relation to refine yet

**Severity:** High · **Evidence:** verification/completeness gap  
**Affected:** Specification  
**Locations:** S §§9, 11–13

The parser has explicit procedures, but the runtime relies on broad actor/host descriptions and an incomplete annex. Naming StepResult, Rep and theorem families does not complete the semantics those theorems quantify over.

**Evidence.** The completion distinctions, method-store ownership, hook lookup timing, primitive catalog and source-unit failure policies still permit materially different transition systems. The document appropriately says proofs are not completed; the issue is that the stated target relation is not fully fixed either.

**Consequence.** Two implementations could prove refinement to different reasonable interpretations of the same prose. Storage-level proofs cannot repair this semantic ambiguity.

**Correction.** Define configurations and the transition/evaluation rules for every core actor and source-unit stage; make native catchability, state-on-failure and observation projection explicit. Then state determinism/adequacy and machine simulation against that single relation. A prose specification is acceptable, but it must uniquely determine these cases.

## 5. Exact loop-control distinctions to encode

The following excerpt of the required matrix comes directly from the pinned evaluator. It is intentionally clause-specific. “Propagate” means leave that loop implementation as the same abrupt completion; an enclosing construct or source-unit wrapper may then handle it. This table is not a claim that the suggested probes were run.

| Loop form and active clause | Bare continue | Continue(value) | Bare break |
|---|---|---|---|
| `while P do B`: predicate P | Propagate | Propagate | Return null |
| `while P do B`: body B | Next test | Propagate | Return null |
| `while P list L`: predicate P | Propagate | Propagate | Return null, even after earlier collection |
| `while P list L`: collector L | Skip append, next test | Append value, next test | Return collected list |
| `while P list L do B`: predicate P | Propagate | Propagate | Return collected list |
| `while P list L do B`: collector L | Skip append, then execute B | Append value, then execute B | Return collected list |
| `while P list L do B`: body B | Propagate | Propagate | Return collected list |
| `for`: when clause | Propagate | Propagate | Return collected list, or null without collection |
| `for`: collector | Skip append, then execute optional do | Append value, then execute optional do | Return collected list |
| `for`: do clause | Next iteration | Propagate | Return collected list, or null without collection |

A valued break returns its value in the listed handled-break positions. Domain expression failures and transfers are additional cases and must not be confused with an already-entered loop body. The collection value is appended before the do clause; a later do-clause failure does not retroactively undo it.

## 6. Structural validation and negative controls

The unchanged bundle reports PASS with 155 registered source words, 57 named profiles, 34 augmented words, three internal tokens, 121 words compared to the **supplied reference table**, and 146 unexecuted conformance-plan entries. Annex A remains byte-equivalent modulo the validator's declared trailing-newline treatment.

I ran the supplied validator on isolated copies with one mutation each. The originals were unchanged.

| Control | Change | Result |
|---|---|---|
| Baseline | None | PASS |
| Wrong expected value | E001 `1+2*3` expected value changed from `7 : ZZ` to `999 : ZZ` | PASS |
| Main table drift | Main-document `+`/`-` lbp changed from 50 to 49; annex and JSON unchanged | PASS |
| Wrong quote policy | JSON `quote_symbol.quote_policy` changed from `ordinary` to `global` | PASS |

Accepting the wrong arithmetic expectation is not a defect in a validator expressly limited to structure. It establishes that the PASS does not validate answers. Main-table drift and wrong per-word quotation policy are gaps in structural agreement checks and are straightforward to strengthen.

The corpus's phase labels are more careful than a casual reading might suggest: PE010 is explicitly a source-unit-parse test and L017 explicitly a literal-decode test. I do **not** count those labels as errors. The remaining problem is that expectations are prose, not typed executable observations, and planned exhaustive generation has not occurred.

## 7. A simpler organization

### 7.1 One normative language contract

Maintain a corrected reference with stable requirement IDs. Preserve the originally supplied file as a provenance artifact, not a second simultaneously normative definition. Record amendments in a non-normative ledger and integrate their effective rule into the corrected contract.

The contract needs six coherent parts:

1. Bytes, lexical recognition and stateful word registration.
2. The exact Pratt table/actions and source-unit boundary.
3. Binding, scope/layout, namespace mutations and diagnostics.
4. Values, primitive/actor ABI, methods and reflective store operations.
5. Evaluation and source-unit transitions, including exceptional/effectful paths.
6. Observations, compatibility profiles and independent conformance fixtures.

This is an organizational recommendation, not a requirement to copy the native physical data structures.

### 7.2 One architecture and refinement document

Explain optimized words, stores, code layout, caches, snapshots, linking and proof obligations separately. These should not compete with language rules. A compact division into grammar/frontend, binding, runtime/objects, source-unit/host, and verification/adapter responsibilities is sufficient initially; the current long proposed module list can remain an implementation planning appendix.

### 7.3 One authoritative mutable object store

Treat class method tables, dictionaries and frame views as user-visible state. A cache may index that state, but it is not a second semantic authority. A word registry and a dictionary are genuinely different relations and should stay separate. Methods and visible class-table entries are not independently mutable relations unless their consistency is explicitly maintained.

### 7.4 Keep reification separate from ordinary reads

The semantic requirement is that declaration identity and activation identity can be recovered where M2 exposes them. The fast machine need not attach a full symbol record to every local read or allocate a separate heap object for every slot. A logical address `(FrameId,slot)` is a reasonable specification choice; a flattened CellId is a reasonable implementation choice. Prove the correspondence rather than mandating both allocations.

### 7.5 Make fidelity an explicit policy

A pinned-native profile reproduces well-defined native observations, including awkward control/hook rules. A safe/portable profile can intentionally reject malformed inputs or clean up a documented quirk. Neither profile must imitate undefined behavior. The ledger must say exactly which rule and test differ. This avoids silently changing M2 under the banner of a cleaner interpreter.

## 8. Verification and performance priorities

The spec/machine separation remains the right idea. The immediate proof target should be a small, fully defined semantic transition system, not a second large evaluator designed independently of the first. Make binding failures deterministic, use clause-specific continuations for abrupt control, and state primitive effects before proving store refinements.

Useful proof milestones are: grammar manifest consistency; cursor and first-wins registration; parser soundness/adequacy with remaining-input observations; binding selection and state-on-error; layout validity; primitive and reflective-store contracts; lowering preservation; and finally optimized execution simulation with both success soundness and finite-execution adequacy. The existing roadmap correctly rejects vacuous one-way refinement that permits rejecting every input.

For performance, retain cached word profiles, direct resolved references, efficient global maps, linear token scanning/separator construction, snapshot-safe indexed cells and explicit control stacks. Benchmark these separately. Avoid requiring string lookup inside the Pratt loop, historical linked-list cell access, copies of all captured values, or two independently updated method registries. Also avoid overreacting: cached integer IDs and finite action tags already recover most of the native Word design's performance benefits without copying its entire object graph.

An exported hash, serial, frame view or enumeration order constrains which internal changes are observationally irrelevant. Write those API contracts first. “IDs may be renamed” is valid only for identities that are not observed through a numerical or ordering operation. Conversely, do not turn arbitrary native bucket layout into a universal portable requirement where the reference explicitly leaves order implementation-defined; choose and state the observation policy.

## 9. Recommended correction sequence

First correct F02–F13 and F16 in the normative language text, with source-derived regression cases. These include concrete counterexamples and deterministic ordering omissions; adding more architecture prose will not repair them.

Second add the native primitive/bootstrap inventory and the reflective object contracts (F01, F14–F18). Specify what level K actually supplies before level L begins.

Third replace the parallel normative body/annex arrangement with a corrected contract plus archived original, and strengthen the structural checks (F19–F22). The independent behavioral harness must record the pinned binary, complete setup, typed observations, stdout/stderr/exit status and failure phase.

Fourth implement the transparent semantic transitions and link the current Macaulean runtime to them. Optimize physical stores only after the associated visible behavior is fixed. An implementation may remain a clearly marked subset during migration; that does not excuse an incomplete final contract.

## 10. Residual checks not promoted to confirmed user-program findings

Several native paths deserve targeted probes before the next contract is frozen: ignored recursive-installation results in `installIt`'s Option wrapper; iterator `next` failures before the for body; native error values inside equality/collections; exact out-of-range frame-view extension and sharing; and malformed UTF-8/mathematical-operator tails. These paths were noticed in the code or are natural boundary cases, but this audit does not assert a fully established user-program outcome for them.

The native arithmetic backend, every host primitive and all Core/package programs still need their own inventory and coverage. The absence of that wider execution evidence does not weaken the clear mismatches above; it limits any claim that fixing this list alone proves complete compatibility.

## 11. Final conclusion

R is a useful grammar-and-semantics reference, but not yet a complete, uniformly correct interpreter specification. S is a significant architectural improvement and a useful front-end specification, but its normative incorporation of R inherits genuine runtime mistakes. Its larger size does not close the native primitive, reflection, failure-policy and runtime-transition gaps.

The correct next revision is **more precise and less duplicative**, not a larger collection of architectural promises: one corrected normative contract, a complete primitive boundary, clause-specific operational rules, one visible-state model, and independently executable conformance evidence. No native or Lean conformance claim is made by this audit.

## Appendix: source and input integrity

- `Macaulay2-language-spec.md`: SHA-256 `624cf55004f11afd9b728e8ad73df707ce1f190b4fa8089368729b6600065fca`; 85,949 bytes; 1,515 lines.
- `Macaulean-M2-complete-specification.md`: SHA-256 `26d3c19b818ac11077f494002140c15592b25e063595d818dc2fe7ddeff75a6e`; 176,674 bytes; 2,683 lines.

### Pinned source references

- **N1** — [interp.dd](https://github.com/Macaulay2/M2/blob/1a37f6fe95badb1e5f99707a485503d213fd9d49/M2/Macaulay2/d/interp.dd): `readeval4; readeval; load; value`.
- **N2** — [evaluate.d](https://github.com/Macaulay2/M2/blob/1a37f6fe95badb1e5f99707a485503d213fd9d49/M2/Macaulay2/d/evaluate.d): `evalWhileDoCode; evalWhileListCode; evalWhileListDoCode; evalForCode`.
- **N3** — [evaluate.d](https://github.com/Macaulay2/M2/blob/1a37f6fe95badb1e5f99707a485503d213fd9d49/M2/Macaulay2/d/evaluate.d): `tryEval; evalTryCode; trapfun`.
- **N4** — [actors3.d](https://github.com/Macaulay2/M2/blob/1a37f6fe95badb1e5f99707a485503d213fd9d49/M2/Macaulay2/d/actors3.d): `lessequalfun2; greaterequalfun2; EqualEqualfun; override; apply/scan registrations`.
- **N5** — [binding.d](https://github.com/Macaulay2/M2/blob/1a37f6fe95badb1e5f99707a485503d213fd9d49/M2/Macaulay2/d/binding.d): `bindassignment; bind; localBind; insert; makeEntry`.
- **N6** — [evaluate.d](https://github.com/Macaulay2/M2/blob/1a37f6fe95badb1e5f99707a485503d213fd9d49/M2/Macaulay2/d/evaluate.d): `globalAssignmentHook; globalAssignment; assigntofun`.
- **N7** — [hashtables.dd](https://github.com/Macaulay2/M2/blob/1a37f6fe95badb1e5f99707a485503d213fd9d49/M2/Macaulay2/d/hashtables.dd): `mutablefun; installIt; installMethod; lookupBinaryMethod`.
- **N8** — [equality.dd](https://github.com/Macaulay2/M2/blob/1a37f6fe95badb1e5f99707a485503d213fd9d49/M2/Macaulay2/d/equality.dd): `equal(HashTable,HashTable); equal(Expr,Expr)`.
- **N9** — [evaluate.d](https://github.com/Macaulay2/M2/blob/1a37f6fe95badb1e5f99707a485503d213fd9d49/M2/Macaulay2/d/evaluate.d): `augmentedAssignmentFun; augmentedParallelAssignmentFun; parallelAssignmentFun`.
- **N10** — [actors5.d](https://github.com/Macaulay2/M2/blob/1a37f6fe95badb1e5f99707a485503d213fd9d49/M2/Macaulay2/d/actors5.d): `frame; frames; localDictionaries; dictionaryPath; values via actors2.dd`.
- **N11** — [lex.d](https://github.com/Macaulay2/M2/blob/1a37f6fe95badb1e5f99707a485503d213fd9d49/M2/Macaulay2/d/lex.d): `makeUniqueWord; gettoken; gettoken1`.
- **N12** — [parser.d](https://github.com/Macaulay2/M2/blob/1a37f6fe95badb1e5f99707a485503d213fd9d49/M2/Macaulay2/d/parser.d): `parse; nparse; accumulate; all parser handlers`.
- **N13** — [convertr.d](https://github.com/Macaulay2/M2/blob/1a37f6fe95badb1e5f99707a485503d213fd9d49/M2/Macaulay2/d/convertr.d): `convertTokenReference; convertParentheses; convert0`.
- **N14** — [actors2.dd](https://github.com/Macaulay2/M2/blob/1a37f6fe95badb1e5f99707a485503d213fd9d49/M2/Macaulay2/d/actors2.dd): `values and pairs on DictionaryClosure`.
- **N15** — [expr.d](https://github.com/Macaulay2/M2/blob/1a37f6fe95badb1e5f99707a485503d213fd9d49/M2/Macaulay2/d/expr.d): `newSymbolHashTable; frame allocation; dictionary creation`.
