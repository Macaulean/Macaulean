# Validation status — design-first revision

## Executed in this editing session

- Inspected PR #42 and its interrupted-design head through the GitHub connector.
- Read the existing `Words.lean` / `IR.lean` addition and revised them together with
  the new binder, machine, relational meaning, example and tests.
- Ran `python scripts/check-gcd-design.py`: **PASS_STRUCTURAL_ONLY**.
  This checks nine Lean source files for the stated dependency/identity boundaries,
  a labelled source-fixture gap, explicit obligations, and absence of admissions.
- Ran three isolated negative controls: adding a legacy runtime import, erasing the
  operator WordId field, and inserting an axiom. The checker rejected each modified
  copy. The originals were not changed.
- Pushed the revision through GitHub connector tree/commit/ref operations, with an
  expected-head lease. No direct git push or merge was performed.

Machine-readable reports: `static-validation.json`, `static-negative-controls.json`.
These are **text/import checks**, not a Lean syntax/type checker and not semantic
conformance. The checks cannot establish that the lowering, runtime, or theorem
statements are correct.

## Not executed / not established

- No Lean or Lake executable is installed in this environment. An attempt to access
  the public Lean source host failed DNS resolution. No toolchain was downloaded.
- The 21 supplied `#guard` commands were **not executed**. Their expected outcomes
  are code-derived test targets, not results.
- No new Lean file is claimed to compile; no CI PASS is claimed.
- No generic preservation, binder, parser, termination, or adequacy proof was run.
- No native M2 execution, benchmark or native-D conformance test was run or required.
- `gcd.m2` is not yet parsed by the new frontend. The run path starts with the
  explicitly labelled `Surface` fixture. `SourceLink` and DESIGN-PARSE remain open.
- The legacy worksheet DSL has not been switched to the new language model.

The PR stays draft. First validation in a configured checkout:

```sh
python scripts/check-gcd-design.py
lake build Macaulean.Verification.Examples.GcdTranslation.Semantics
lake env lean MacauleanTest/GcdTranslation.lean
lake env lean Examples/GcdTranslation/Worksheet.lean
```

Proofs should then be completed and audited against the stated closed fragment;
compilation of a `Prop` definition is not proof of its proposition.
