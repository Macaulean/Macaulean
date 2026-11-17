#!/usr/bin/env python3
"""Validate this specification bundle's integrity, not an M2 implementation.

Usage: python validate_spec.py [bundle_directory]
No third-party dependencies are required. A successful run verifies transcription,
coverage metadata and checksums only; it does not execute the conformance cases.
"""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import re
import sys

SOURCE_SHA = '624cf55004f11afd9b728e8ad73df707ce1f190b4fa8089368729b6600065fca'
LEADING = {'error','default','unary','nunary','nnunary','paren','if','while','for','try','catch','new','quote'}
TRAILING = {'error','default','binary','nbinary','postfix','arrow'}

def require(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)

def strength(s: str) -> int | None:
    s = s.strip().replace('**','')
    return None if s == '—' else int(s)

def validate(root: Path) -> dict[str, object]:
    source_bytes=(root/'Macaulay2-language-spec.md').read_bytes()
    require(hashlib.sha256(source_bytes).hexdigest()==SOURCE_SHA, 'Supplied reference checksum mismatch')
    source=source_bytes.decode('utf-8')
    design=(root/'Macaulean-M2-complete-specification.md').read_text(encoding='utf-8')
    begin='<!-- BEGIN VERBATIM SUPPLIED SPECIFICATION -->\n'
    end='\n<!-- END VERBATIM SUPPLIED SPECIFICATION -->'
    require(design.count(begin)==1 and design.count(end)==1, 'Missing or duplicated annex boundary')
    embedded=design.split(begin,1)[1].split(end,1)[0]
    require(embedded==source.rstrip('\n'), 'Embedded reference text was changed')
    require('@@PROFILE_TABLE@@' not in design and '@@ANNEX@@' not in design, 'Unexpanded document placeholder')
    g=json.loads((root/'m2-grammar-1.26.06.json').read_text(encoding='utf-8'))
    profiles=g['profiles']; words=g['words']; by_word={w['spelling']:w for w in words}
    require(len(by_word)==len(words)==155, 'Expected 155 distinct registered source words')
    require(len(profiles)==57, 'Expected 57 named profiles')
    require(set(g['internal_tokens'])=={'EOF','EOC','NEWLINE'}, 'Internal token set mismatch')
    require(g['interning_policy']=='first-registration-wins', 'Incorrect word registration policy')
    require(g['delimiter_pairs']=={'(':')','[':']','{':'}','<|':'|>'}, 'Delimiter map mismatch')
    for name,p in profiles.items():
        require(p['leading'] in LEADING, f'Unknown leading action {name}')
        require(p['trailing'] in TRAILING, f'Unknown trailing action {name}')
        require(isinstance(p['lbp'],int) and p['lbp']>=0, f'Invalid lbp {name}')
        for field in ('rbp','ubp'):
            require(p[field] is None or isinstance(p[field],int) and p[field]>=0, f'Invalid {field} {name}')
        if p['leading'] in {'unary','nunary','nnunary','paren','if','while','for','try','catch','new'}:
            require(p['ubp'] is not None, f'Missing required unary strength {name}')
        if p['trailing'] in {'binary','nbinary','arrow'}:
            require(p['rbp'] is not None, f'Missing required binary strength {name}')
        if p['leading']=='quote':
            require(p.get('quote_policy') in {'ordinary','currentLocal','global','threadGlobal'}, f'Invalid quotation policy {name}')
    require({p['leading'] for p in profiles.values()}==LEADING, 'Leading-action coverage incomplete')
    require({p['trailing'] for p in profiles.values()}==TRAILING, 'Trailing-action coverage incomplete')
    for w in words:
        require(w['profile'] in profiles, f'Unbound profile for {w["spelling"]}')
    aug={w['spelling']:w['augmented_base'] for w in words if 'augmented_base' in w}
    require(len(aug)==34, 'Expected 34 augmented assignments')
    require(set(aug)=={b+'=' for b in g['augmented_bases']}, 'Augmented spelling mismatch')
    require(all(w==b+'=' and b in by_word for w,b in aug.items()), 'Missing augmented base')
    require(all(by_word[w]['profile']=='assignment' for w in aug), 'Augmented profile mismatch')
    # Compare every explicitly backtick-quoted token in the supplied precedence table.
    table=source.split('### 2.3 The precedence table (normative)',1)[1].split('### 2.4',1)[0]
    checked=set()
    for line in table.splitlines():
        if not re.match(r'^\|\s*\d+\s*\|',line):
            continue
        cols=re.split(r'(?<!\\)\|',line)[1:-1]
        require(len(cols)==7, f'Unexpected source table shape: {line}')
        lbp=int(cols[0]); rbp=strength(cols[2]); ubp=strength(cols[3])
        tokens=re.findall(r'`([^`]*)`',cols[1])
        if cols[1].strip().startswith('SPACE '):
            tokens.append('SPACE')
        for token in tokens:
            token=token.replace('\\|','|')
            require(token in by_word, f'Source-table token missing from manifest: {token}')
            p=profiles[by_word[token]['profile']]
            require((p['lbp'],p['rbp'],p['ubp'])==(lbp,rbp,ubp), f'Precedence mismatch for {token}')
            source_leading=cols[4].strip()
            source_trailing=cols[5].strip()
            if '/' in source_leading:
                require(token in source_leading.split('/'), f'Unknown special form {token}')
                source_leading=token
            require(p['leading']==source_leading, f'Leading handler mismatch for {token}')
            require(p['trailing']==source_trailing, f'Trailing handler mismatch for {token}')
            checked.add(token)
    nonaug=set(by_word)-set(aug)
    require(checked==nonaug, f'Table/manifest vocabulary mismatch: missing={nonaug-checked}, extra={checked-nonaug}')
    plan=json.loads((root/'conformance-cases.json').read_text(encoding='utf-8'))
    cases=plan['cases']; ids=[c['id'] for c in cases]
    require(len(ids)==len(set(ids))==146, 'Conformance case ID/count mismatch')
    require('UNEXECUTED' in plan['status'], 'Test plan must not be labeled as an executed report')
    require(all('not executed' in c['evidence'] for c in cases), 'A case lacks explicit evidence status')
    require(all(c.get('source') is not None or c.get('steps') or c.get('source_bytes_hex') for c in cases), 'Case lacks source/scenario')
    return dict(status='PASS — specification data and integrity only', supplied_reference_sha256=SOURCE_SHA,
                registered_source_words=len(words), named_profiles=len(profiles), augmented_words=len(aug),
                internal_tokens=len(g['internal_tokens']), native_table_words_compared=len(checked),
                conformance_cases=len(cases), conformance_cases_executed=0,
                lean_compilation_performed=False, native_M2_execution_performed=False,
                reference_text_preserved=True)

def main() -> int:
    root=Path(sys.argv[1]).resolve() if len(sys.argv)>1 else Path(__file__).resolve().parent
    try:
        result=validate(root)
    except (OSError, ValueError, KeyError, TypeError, IndexError, json.JSONDecodeError) as exc:
        print(f'FAIL: {exc}',file=sys.stderr)
        return 1
    print(json.dumps(result,ensure_ascii=False,indent=2))
    return 0

if __name__=='__main__':
    raise SystemExit(main())
