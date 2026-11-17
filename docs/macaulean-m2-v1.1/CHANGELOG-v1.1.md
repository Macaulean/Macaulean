# Revision 1.1 change ledger

29 September 2026. This file is **informative**, not another normative rule layer.
The active text is `Macaulean-M2-specification-v1.1.md`. Both original documents and the
audit remain unchanged in `archive/`. Changes are based on the supplied findings and
existing source excerpts, not a new native execution campaign.

## Audit disposition

“Integrated” means the text/data correction was made, **not** native validation or a
completed proof. A partial/open finding identifies contract work the audit itself did
not finish. All 24 findings are accounted for; they are not all claimed closed.

| ID | Finding | Disposition | Location / change |
|---|---|---|---|
| F01 | The claimed core boundary omits native primitives and a bootstrap ABI | partial — boundary corrected, inventory open | §0.1; §5.8; bootstrap-contracts.json — Native apply/scan and identified primitives are no longer excluded as library-only. OC-BOOTSTRAP/OC-ACTOR remain. |
| F02 | AfterEval has the wrong method key | integrated | §7.4 HOOK-KEYS — Unqualified BeforeEval/AfterEval keys, exact arguments and result roles. |
| F03 | Standalone semicolons are incorrectly accepted by the source-unit grammar | integrated | §2.6; §7.1 UNIT-STEP — No standalone-semicolon skipping; source-unit and parse-utility observations kept separate. |
| F04 | Loop control cannot be specified by a uniform innermost-loop rule | integrated for audited clause matrix | §6.9.1 LOOP-CLAUSE — Ten clause rows define bare/valued continue and break; domain/iterator boundary remains OC-ITERATOR. |
| F05 | The typed completion taxonomy changes try on step and finish | integrated for audited predicate | §6.9.2 TRY-CATCHABILITY — Step/finish caught under active suppression; datatype split does not define catchability; OC-DEBUG retained. |
| F06 | The second left evaluation of <=/>= does not obey blanket error propagation | integrated for audited actor | §6.10.1 COMPARE-SECOND — First comparison checked; second delivered lhs result inspected without blanket abrupt check, including interval branches. |
| F07 | Binding failure effects and traversal are not optional | partial — confirmed ordering corrected | §3.7 BIND-FAILURE — RHS precedes method-capability validation, explicit early branches preserved; full remaining low-level edges OC-BIND. |
| F08 | Assignment-hook lookup time is unspecified | integrated | §6.6.1 ASSIGN-HOOK-SCHEDULE — Capture old release before symbol hooks; late new-class assignment lookup. |
| F09 | Symbol identity immutability is conflated with isMutable | integrated | §5.3 MUTABILITY — Native isMutable representation predicate separated from stable identity. |
| F10 | CacheTable equality omits class and parent conditions | integrated | §5.5 CACHE-EQUALITY — Class and parent checks precede exact-class hash-zero CacheTable special case. |
| F11 | Augmented Default dispatch is name-based, not canonical-symbol identity | integrated | §6.7 AUGMENT-SCHEDULE — Canonical word bytes Default request fallback; not one distinguished global identity. |
| F12 | Augmented hash-table assignment needs an explicit operand schedule | partial — audited schedules integrated | §6.7 AUGMENT-SCHEDULE — HashTable container -> RHS -> key -> lookup schedule and cached-vs-other paths; remaining edges OC-AUGMENT. |
| F13 | Not every assignment expression returns its supplied RHS | integrated | §6.6; §6.6.2 — Per-form result rules; recursive actual results and one-target unwrapping replace universal RHS claim. |
| F14 | Reflective frame APIs have aliasing semantics, not just display semantics | partial — core aliasing fixed | §5.7 FRAME-VIEW — Shared backing sequence, existing-slot writes and global hiding required; extension/stale/empty-frame boundary OC-FRAME. |
| F15 | Dictionary history, enumeration and cardinality are not fixed by “shadowing map” | partial — entry model fixed | §3.8 DICT-HISTORY — Retained duplicate entries/counts separated from lookup; full erase/rehash/enumeration policy OC-DICT. |
| F16 | Source-unit hook failures and wrappers need a total policy table | partial — audited driver paths fixed | §7.2; §7.4; §7.5 — Hook substitutions/continuation, wrapper transfer set, exit and close precedence integrated; OC-UNIT/OC-DEBUG remain. |
| F17 | Actor and host interfaces are named but not completely contracted | open, explicitly inventoried | §5.8; §8.1 — Partial bootstrap register and actor/host/numeric open contracts replace an unsupported completeness claim. |
| F18 | Method state and class hash tables need one authoritative view | design decision integrated | §6.5.5 METHOD-AUTHORITY — Class/object tables authoritative; indexes/caches derived. Full installation edge contract OC-INSTALL remains. |
| F19 | Strict native conformance and intentional safe departures need separate labels | integrated | §0.3 — PN and PS profiles with explicit departures/domain boundaries; no arbitrary cleanup permission. |
| F20 | The structural validator misses inconsistencies within its own data boundary | validator strengthened; tested separately | validate_spec.py; test_validator.py — Active table/JSON agreement, exact quote-word policy, routes, checksum and HTML source binding checks; behavior remains unvalidated. |
| F21 | The 146-case corpus is a test plan, not an executable conformance oracle | partial — typed audit fixtures added | audit-regressions-v1.1.json; §8.3 — Exact-source and controlled configuration fixtures are unexecuted; legacy 146-case plan archived, complete native harness/coverage pending. |
| F22 | The normative organization duplicates too much and obscures authority | integrated | Whole revision — One active contract, separate architecture and non-normative ledger/archive; no verbatim normative Annex A. |
| F23 | Do not make every logical identity a mandatory hot-path allocation | integrated | §3.9; §4.4; architecture §§3,8 — Logical addresses can be activation/slot; no mandatory per-cell object or redundant ID on each hot read. |
| F24 | The proof roadmap has no fully defined runtime transition relation to refine yet | open — scope made explicit | §6.0; §8; architecture §9 — Known transitions fixed; no full runtime relation/proof claimed until OC-* contracts close. |

## Earlier v1.0 reconciliations retained

The effective rules from the prior R1–R13 ledger are integrated into the active chapters,
not left as corrections an implementer must apply to a simultaneous normative archive:
byte strings; literal-versus-word registration and first-wins history; infix SPACE;
all-delimiter fixed-parameter parsing; quotation of id tokens; first writable dictionary;
actor-controlled primitive/fallback ordering; reached effects on failure; distinct <-;
real decoding at lowering; explicit malformed-literal policy; no BNF impossibility claim;
and flagLookup as a binding diagnostic. Prior safe departures now have PN/PS labels.

## Artifact changes

The normative annex/body duplication is removed. The main document is based on the
reference's chapter organization, with corrected runtime and source-unit rules in place.
A generated grammar table exposes quote policies and lexical routes in the same checked
projection. The implementation/refinement discussion moved to a separate short document.
Open contracts, identified primitive interfaces and stable rule IDs have machine-readable
registers. The legacy test plan remains archived rather than silently relabeled as an
executed or corrected oracle.

The updated validator checks active artifact consistency; negative controls separate
schema/integrity validation from behavioral truth. Generated reports state exactly which
Python checks ran. No M2, Lean or performance/proof test is implied.
