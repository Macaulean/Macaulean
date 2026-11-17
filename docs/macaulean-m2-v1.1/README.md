# Macaulean M2 specification — revision 1.1

This bundle updates the reference/design using all 24 attached audit findings. It does
not claim that all findings are closed, that every native primitive is fully contracted,
or that M2/Lean execution or verification was performed.

## Read first

**Macaulean-M2-specification-v1.1.md** is the single active language contract, with a
matching HTML reading edition. It preserves the supplied reference's chapter organization,
integrates the audited rules in place, and replaces the earlier competing body/annex.

**Macaulean-M2-architecture-v1.1.md** separates implementation/performance/refinement
choices from language behavior. **CHANGELOG-v1.1.md** accounts for findings F01–F24.
Both have HTML editions. The exact original reference, v1.0 specification and audit are
unchanged in `archive/` and are no longer simultaneous normative texts.

## Supporting data

- `m2-grammar-1.26.06.json`: 155 words, including 34 augmented words, 57 profiles and three
  internal profiles. The active Markdown table is generated from it and cross-checked.
- `rule-index.json` and `audit-disposition.json`: stable rule anchors and every finding's
  disposition. Integrated text is not an executed/proved result.
- `open-contracts.json`: 14 explicit remaining contract areas, including the complete
  native primitive/actor/host inventory and outstanding reflective/error boundaries.
- `bootstrap-contracts.json`: 17 identified native interfaces, with unsupported fields
  left explicit. This is not an exhaustive native export inventory.
- `audit-regressions-v1.1.json`: 68 unexecuted typed fixtures (13 exact-source and 55
  configuration fixtures). A native fixture adapter/runner is not included.
- `coverage-plan-v1.1.json`: pending broader coverage; the original 146-case prose plan
  remains archived unchanged rather than relabeled as an independently validated oracle.

## Validate

```sh
python -m pip install -r requirements.txt
python validate_spec.py .
python test_validator.py .
```

The first script checks document/manifest agreement, quotation policies, lexical routes,
skip/terminator sets, rule/finding/open-contract references, fixture structure, exact HTML
rendering and full checksums. Its reference-table comparison is against the archived
supplied document, not an independent extraction from D source.

The second script uses isolated copies with refreshed checksums. Main-table, quote-policy,
lexical-route, skip-set, rendered-HTML and archived-source drift are rejected. A well-typed
wrong expected number is accepted: this explicitly proves that structural PASS is not
behavioral validation. No M2 or Lean program is run.

`validation-report.json` and `validator-controls-report.json` record the checks actually
performed for this bundle. `SHA256SUMS` covers every payload file except itself and Python
bytecode caches.

## After deliberate edits

The Markdown and JSON must be kept synchronized. Regenerate HTML and checksums with:

```sh
python render_documents.py . --checksums
```

This regenerates reading editions only, not the normative grammar table; a changed grammar
manifest requires reviewing/updating its checked projection. Rewriting checksums does not
make incorrect semantics correct. Run validation and record native evidence separately.

The current profiles are PN (pinned-native defined domain) and PS (named safe departures).
Native versus transactional worksheet execution is a separate axis. Open contracts block
full K/L certification; they do not authorize arbitrary successful fallback values.
