# Macaulean implementation and refinement architecture

**Version 1.1 · 29 September 2026**  
**Role:** Implementation design, not an additional language specification. The active contract is
`Macaulean-M2-specification-v1.1.md`; `archive/` contains evidence and superseded drafts.

## 1. Decision and comparison with native D

Keep separate the exact spelling/profile relation, dictionary entries, declaration identity,
and live storage. Retain native's cheap grammar lookup and direct resolved references,
without making its entire interconnected Word/Symbol/Frame object layout mandatory.

| Concern | Native D | Macaulean semantic requirement | Machine freedom |
|---|---|---|---|
| Lexical identity | Interned Word with name/type/parse fields | Exact byte spelling; first-registration-wins profile history | WordId and shared immutable profile table |
| Grammar | Function-valued parse handlers | Finite leading/trailing action algebra; exact native strengths/cursor | Generated enum dispatch or equivalent table |
| Occurrence | Token with word, source position, binding fields | Frozen lexical identity plus byte position/newline state | Source slices and compact tokens |
| Namespaces | Symbol hash tables/chains | Ordered lookup and retained entry history/counts | Map index over an authoritative entry store |
| Declaration | Symbol object | Stable canonical identity, protection and metadata | SymbolId/metadata arena |
| Local storage | Frame.values | Shared captured locations and reflective backing views | Inline slots, `(activation,slot)`, flattened cell IDs |
| Ordinary reference | Local depth/slot or global symbol frame index | Already resolved location | No mandatory redundant SymbolId in each hot instruction |
| First-class symbol | SymbolClosure(Symbol,Frame) | Declaration plus activation/cell identity | Reify from location and validated metadata |
| Methods | Visible class-table entries | One authoritative object/table state | Derived indexes and invalidated caches |
| Operator execution | Actors receive Code, then primitive/fallback paths | Actor-specific operand/control schedule | Specialize only under a proved case or sound guard |
| Errors/transfers | Error records and message tests | Reached effects and exact clause/catchability rules | Typed completions with sufficient native metadata |
| Source units | Parse–bind–convert–execute incrementally | Changes affect subsequent input, not earlier code | Lazy cursor and session snapshots |

The old `Sym` can become a generated BuiltinWord enum; it must not conflate the word `+`
with the SymbolId of `+` or a machine integer-add instruction. A copied parse profile is
not semantic operator aliasing by itself, and a dictionary alias is not arbitrary grammar
extension. First-wins registration includes ordinary previously seen spellings.

## 2. One semantics, not two interpreters with similar behavior

A transparent reference runner and an optimized machine must implement the same active
contract. Simple finite maps and lists can present a small kernel-reducible semantics.
Production arrays/maps and explicit continuations refine it. Neither implementation is
allowed to fill an open contract with a convenient default and then call its agreement
with the other implementation a proof of M2 fidelity.

The contract now explicitly marks unresolved primitive/actor/host cases. Until they are
closed, prove results for a named closed subset. A grammar table, enum of ActorIds, or
opaque `step` function is not a completed transition relation. The audit's corrected
loop-clause, try, comparison, hook and binder-error rules are fixed inputs to that relation.

## 3. Storage and observable identity

Use distinct logical identifier types at abstraction boundaries. Do not turn this into a
requirement that every ID has a separately allocated runtime record. A cell may simply be
a frame/slot address; the fast representation may flatten it or keep inline frame slots.
Ordinary reads can omit declaration metadata when a validator and side table recover it
for reification, errors and reflective APIs.

The relevant graph includes reachable functions, objects, dictionary entries, backing
frame sequences and live views. A symbol-only reference keeps its cell reachable.
Snapshot forks need explicit lineage/relocation rules for handles; they may not import
raw session-relative integers as another session's live objects.

Frame reflection is more restrictive than closure capture alone: an existing-slot write
through a MutableList wrapper can change the sequence shared with the frame. Returning
copies is not equivalent. Conversely, treating a wrapper as an eternal abstract frame
proxy may not match native backing-array replacement. OC-FRAME must be closed before
using either assumption to justify frame compaction or stale-view handling.

Dictionary lookup can have a derived index, but the retained entry store remains
responsible for `#`, keys/values/pairs and shadowing history. Keeping old SymbolInfo alone
is insufficient. Exact erase/rehash observations are OC-DICT, not permission to silently
deduplicate entries.

## 4. One authoritative object store

Class-table methods, nullary methods and typical-value tables are user-visible objects.
Method installation and direct M2 table writes modify those objects. A method registry,
lookup index or inline cache is derived and may be discarded. Do not create two mutable
semantic authorities that require an unimplemented synchronization invariant.

Caches must cover all mutable dependencies, including class/parent changes and reflected
table writes. A global dispatch epoch is a simple conservative strategy, not a requirement
to add a user-visible epoch object. Byte/profile lookup does not need invalidation after
first registration; visibility lookup and method dispatch do.

## 5. Front end and binding

Use the standalone byte parser as the language source of truth. Tokenize lazily with one
lookahead entry and exact obeylines/followsNewline semantics. Don't reclassify a buffered
token when a request changes mode. Register newly encountered generic words, not just
special aliases. Do not eagerly parse/resolve a whole file before previous statements can
change grammar, path or precision.

The binder is an ordered effectful traversal with an aggregate error flag. A generic
short-circuit Except traversal is inappropriate unless it explicitly reproduces native
continuation edges. In particular, invalid operator-method capability is checked after
binding RHS, while invalid literal/other target branches can return earlier. Correctness
includes the state after binding failure, not only which expressions eventually run.

Lowering retains source-word and selected-symbol identities until their distinct native
checks are complete. It normalizes separators, decodes reals at current lowering precision,
computes direct locations, and creates immutable function templates. It must not perform
future type/method selection based only on the surface operator spelling.

## 6. Runtime continuation design

Use separate continuations for strict operands, each loop form and clause, try suppression,
assignment-hook capture/calls, comparison second evaluation, and source-unit stages.
These can share implementation helpers without sharing incorrect semantic catch boundaries.

Typed completions remain desirable. Their representation must not determine catchability
by convention: pinned try can catch step/finish; some loop clauses propagate continue;
the second left evaluation of <=/>= has no native Error check. Pending host requests and
budget suspensions are not delivered language values to be swallowed by such a branch.

For global assignment, capture the old release method before symbol hooks, call it later,
then look up the new assignment method. For augmented HashTable indexing, evaluate
container, RHS, key, then lookup. Preserve the canonical-name Default fallback predicate.
These rules are data/control dependencies, not optimizations that may be reordered.

## 7. Lean worksheet, module and transaction boundary

Host parsing/backtracking must not execute M2. A selected M2 parse result carries its
source range, word-registration delta and entry environment version. Commit the delta
only for the chosen command and matching session; reparse original bytes if the relevant
environment changed. The parser result should be carried into elaboration rather than
printed and reparsed through another grammar.

Native core mode retains reached effects on failure. A transactional worksheet is a
separate wrapper with explicit state, output and irreversible-host-effect rules. It cannot
claim pinned-native error behavior merely because successful examples agree.

Module artifacts contain declared external requirements and validated relocations. Linking
resolves names in an explicit environment and allocates identities; do not serialize a
build-session CellId as a live imported cell. Source parsing, binding and linked code are
different artifact stages.

## 8. Performance requirements

These are acceptance targets, not measured results in this revision.

| Component | Required direction |
|---|---|
| Lexer | Linear byte scanning apart from bounded lookahead and spelling hashing/comparison; no repeated remaining-suffix conversion |
| Pratt parser | Cached profile access; linear-size trees/builders; no repeated prefix append on wide sequences |
| Namespace | Expected constant lookup or logarithmic key comparisons, plus byte cost; retained history stored separately from its lookup index |
| Ordinary local read | Direct indexed slot/address after at most lexical-depth traversal; no string lookup |
| Global read | Direct resolved location; actual persistent-store indexing complexity stated honestly |
| Cell update | No O(total historical cells) linked-list update; no whole-heap copying on each snapshot write |
| Closure call | Allocate callee-local storage, not copies of all captured values |
| Dispatch | Sound cache invalidation; native primitive-before-fallback behavior preserved |
| Control | Explicit stack/trampoline where necessary; preserve language-visible recursion policy |

Benchmark lex, parse, bind, lower, execute, render and proof/replay separately. Include
large dictionaries with shadow history, wide comma lists, deep arrows, long strings,
hot closure updates, For capture, frame views, evolving sessions/snapshots and existing
polynomial workloads. Record allocation and retained memory, toolchain and repeated runs.
No performance gate is satisfied by choosing a container with a promising name.

## 9. Refinement and trusted boundary

An abstraction relation maps machine word IDs to byte keys/profiles, machine declarations
to logical declarations, and storage/views to logical activations and observable object
relations. Preserve symbol equality, canonical spelling, current cells, visibility history,
class/method entries, hook order, completion kind and relevant host/diagnostic traces.

Prove both: (a) a successful finite machine result is a matching specification result;
(b) a finite specified execution is obtainable by the machine with sufficient resources.
Do not accept a one-way theorem that a machine rejecting all inputs satisfies vacuously.
Resource-bounded runners return a distinct exhaustion/suspension; divergence is not null.

The proof sequence is: data/word history, cursor, parser including remaining input,
binding with error state, layout/reification, completed primitive/reflection contracts,
lowering, then optimized storage/execution. Grammar generation must be proved correct or
its output checked by a trusted small checker. Source-derived expected values and native
execution logs are testing evidence, not axioms.

The full relation is still blocked by the active OC-* register. A proof must name its
closed rule set, source/code, initial environment, compatibility profile and host/resource
assumptions. No Lean compilation or theorem was run while editing these documents.

## 10. Module organization and migration

Prefer five responsibility groups initially: **front end**, **binding/layout**, **runtime/
objects**, **source-unit/host adapter**, and **verification/conformance**. Additional file
splits are engineering decisions, not separate language abstractions.

Migrate the shared grammar/cursor first, then source-order binding, direct references and
lowering. Apply the audited runtime/effect corrections before using old arithmetic tests
as the sole oracle. Inventory bootstrap primitives and reflection before declaring Core
compatible. Optimize storage once its observations are fixed, not by filling gaps with
physical assumptions.

`CHANGELOG-v1.1.md` records which findings changed the contract and which remain open.
The archived supplied text is retained for traceability only. The language contract is
one active document; this architecture explains how to implement it, not a second set of
semantics to reconcile with it.
