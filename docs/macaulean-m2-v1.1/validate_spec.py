#!/usr/bin/env python3
"""Validate revision data/structure/integrity, not M2 behavior or Lean proofs.

Usage: python validate_spec.py [bundle_directory]
Rendering comparison requires markdown-it-py from requirements.txt. This validator
never executes the source programs or configuration fixtures.
"""
from __future__ import annotations
import json,re,sys
from pathlib import Path
from spec_support import (GRAMMAR_BEGIN,GRAMMAR_END,DOCUMENTS,grammar_markdown,
                          sha256,render_document,checksum_paths)

LEADING={'error','default','unary','nunary','nnunary','paren','if','while','for','try','catch','new','quote'}
TRAILING={'error','default','binary','nbinary','postfix','arrow'}
SOURCE_HASH='624cf55004f11afd9b728e8ad73df707ce1f190b4fa8089368729b6600065fca'
OLD_SPEC_HASH='26d3c19b818ac11077f494002140c15592b25e063595d818dc2fe7ddeff75a6e'
EXPECTED_QUOTES={'symbol':'ordinary','local':'currentLocal','global':'global','threadLocal':'threadGlobal'}
AUGMENTED_BASES=set('<< >> || <==> |- ?? ==> ===> | ^^ & .. ..< - + ++ ** * \\ \\\\ / % // @ @@ @@? ~ |_ ^ _ ^** · ⊠ ⧢'.split())

class ValidationError(ValueError):pass

def require(test:bool,msg:str)->None:
    if not test:raise ValidationError(msg)

def load(root:Path,name:str):return json.loads((root/name).read_text(encoding='utf-8'))
def strength(s:str):
    s=s.strip().replace('**','');return None if s=='—' else int(s)

def validate_value(x):
    if isinstance(x,dict):
        if 'tag' in x:
            tag=x['tag'];require(tag in {'ZZ','QQ','Boolean','Nothing','Sequence','List','Array','AngleBarList','String','TypeName'},'Unknown expected value tag')
            if tag=='ZZ':require(isinstance(x.get('decimal'),str) and bool(re.fullmatch(r'-?\d+',x['decimal'])),'Invalid ZZ expectation')
            if tag=='Boolean':require(isinstance(x.get('value'),bool),'Invalid Boolean expectation')
            if tag in {'Sequence','List','Array','AngleBarList'}:require(isinstance(x.get('items'),list),'Invalid collection expectation')
        for y in x.values():validate_value(y)
    elif isinstance(x,list):
        for y in x:validate_value(y)

def validate(root:Path)->dict:
    main=(root/DOCUMENTS[0]).read_text(encoding='utf-8')
    g=load(root,'m2-grammar-1.26.06.json');profiles=g['profiles'];words=g['words']
    byword={w['spelling']:w for w in words}
    require(len(byword)==len(words)==155,'Registered word count or duplicate mismatch')
    require(len(profiles)==57,'Named profile count mismatch')
    require(g['interning_policy']=='first-registration-wins','Word registration is not first-wins')
    require(g['delimiter_pairs']=={'(':')','[':']','{':'}','<|':'|>'},'Fixed delimiter map mismatch')
    require(g['source_unit_skip_tokens']==['NEWLINE','EOC'],'Source-unit skip set incorrectly admits empty semicolon statements')
    require(set(g['source_unit_terminators'])=={';','NEWLINE','EOC','EOF'},'Source-unit terminator set mismatch')
    require(set(g['internal_tokens'])=={'EOF','EOC','NEWLINE'},'Internal token set mismatch')
    for k,lbp in [('EOF',2),('EOC',4),('NEWLINE',8)]:
        require(g['internal_tokens'][k]=={'lbp':lbp,'rbp':lbp,'ubp':None,'leading':'error','trailing':'nbinary'},'Internal profile mismatch: '+k)
    require(profiles[g['default_profile']]=={'lbp':62,'rbp':None,'ubp':None,'leading':'default','trailing':'default'},'GenericProfile mismatch')
    for name,p in profiles.items():
        require(p['leading'] in LEADING and p['trailing'] in TRAILING,'Unknown action: '+name)
        require(type(p['lbp']) is int and p['lbp']>=0,'Invalid lbp: '+name)
        for field in ['rbp','ubp']:
            require(p[field] is None or (type(p[field]) is int and p[field]>=0),'Invalid strength: '+name)
        if p['leading'] in {'unary','nunary','nnunary','paren','if','while','for','try','catch','new'}:
            require(p['ubp'] is not None,'Missing ubp: '+name)
        if p['trailing'] in {'binary','nbinary','arrow'}:require(p['rbp'] is not None,'Missing rbp: '+name)
    for w in words:
        require(w['profile'] in profiles,'Unknown word profile')
        expected_route='math_operator' if w['spelling'][0] in '·⊠⧢' else ('identifier' if w['spelling'][0].isascii() and w['spelling'][0].isalpha() else 'punctuation_trie')
        require(w['lexical_route']==expected_route,'Wrong lexical route for '+w['spelling'])
    for key,policy in EXPECTED_QUOTES.items():
        p=profiles[byword[key]['profile']]
        require(p['leading']=='quote' and p.get('quote_policy')==policy,'Wrong per-word quotation policy for '+key)
    aug={w['spelling']:w['augmented_base'] for w in words if 'augmented_base' in w}
    require(len(aug)==34 and set(aug.values())==AUGMENTED_BASES,'Augmented-base catalog mismatch')
    require(set(g['augmented_bases'])==AUGMENTED_BASES,'Declared augmented bases mismatch')
    require(all(k==v+'=' and v in byword for k,v in aug.items()),'Incorrect augmented mapping')
    require(all(byword[k]['profile']=='assignment' for k in aug),'Augmented parsing profile mismatch')
    require(main.count(GRAMMAR_BEGIN)==main.count(GRAMMAR_END)==1,'Generated table markers missing/duplicated')
    table=main.split(GRAMMAR_BEGIN,1)[1].split(GRAMMAR_END,1)[0].strip()
    require(table==grammar_markdown(g),'Active document grammar table differs from manifest')
    # Historical supplied table comparison: not an independent D-source extraction.
    raw=(root/'archive/supplied-reference.md').read_bytes()
    require(sha256(raw)==SOURCE_HASH,'Archived supplied reference checksum differs from pinned input')
    require(sha256((root/'archive/specification-v1.0.md').read_bytes())==OLD_SPEC_HASH,'Archived v1.0 checksum differs from pinned input')
    source=raw.decode('utf-8');src_table=source.split('### 2.3 The precedence table (normative)',1)[1].split('### 2.4',1)[0]
    checked=set()
    for line in src_table.splitlines():
        if not re.match(r'^\|\s*\d+\s*\|',line):continue
        cols=re.split(r'(?<!\\)\|',line)[1:-1]
        require(len(cols)==7,'Archived table shape changed')
        tokens=re.findall(r'`([^`]*)`',cols[1])
        if cols[1].strip().startswith('SPACE '):tokens.append('SPACE')
        for key in tokens:
            key=key.replace('\\|','|');require(key in byword,'Archived word missing: '+key)
            p=profiles[byword[key]['profile']]
            require((p['lbp'],p['rbp'],p['ubp'])==(int(cols[0]),strength(cols[2]),strength(cols[3])),'Supplied-reference power mismatch: '+key)
            lead=cols[4].strip()
            if '/' in lead:
                require(key in lead.split('/'),'Archived compound action mismatch');lead=key
            require(p['leading']==lead and p['trailing']==cols[5].strip(),'Supplied-reference handler mismatch: '+key)
            checked.add(key)
    require(checked==set(byword)-set(aug),'Supplied-reference base-word coverage mismatch')
    # Revision coverage and open boundaries.
    disposition=load(root,'audit-disposition.json');items=disposition['entries']
    require({x['id'] for x in items}=={f'F{i:02d}' for i in range(1,25)} and len(items)==24,'Audit finding coverage mismatch')
    require(disposition['all_findings_closed'] is False,'Open findings must not be called all closed')
    oc=load(root,'open-contracts.json')['items'];ocids={x['id'] for x in oc}
    require(len(ocids)==len(oc)==14 and all(x['status']=='open' for x in oc),'Open contract register mismatch')
    used=set(re.findall(r'\bOC-[A-Z][A-Z-]*',main))
    require(used<=ocids,'Unregistered open contract: '+str(used-ocids))
    require(all(i in main for i in ocids),'Open contract omitted from active document')
    ri=load(root,'rule-index.json')['rules'];rules={x['id'] for x in ri}
    require(len(rules)==len(ri),'Duplicate rule IDs')
    require(all(main.count('id="'+x['anchor']+'"')==1 for x in ri),'Rule anchors missing or duplicated')
    require('BEGIN VERBATIM SUPPLIED SPECIFICATION' not in main,'Archived reference must not be an active normative annex')
    register=load(root,'bootstrap-contracts.json')
    require(register['inventory_exhaustive'] is False,'Partial bootstrap inventory incorrectly claims exhaustive coverage')
    require({'apply','scan','override','frame','frames','localDictionaries'}<={p['export_or_interface'] for p in register['interfaces']},'Audit-identified primitive omitted')
    for p in register['interfaces']:require(set(p['open_contracts'])<=ocids,'Unknown primitive contract dependency')
    plan=load(root,'audit-regressions-v1.1.json');cases=plan['fixtures'];ids=set()
    require('UNEXECUTED' in plan['status'] and plan['runner_included'] is False,'Fixture status implies nonexistent runner/results')
    for c in cases:
        require(c['id'] not in ids,'Duplicate fixture ID');ids.add(c['id'])
        require(set(c['rules'])<=rules,'Unknown fixture rule')
        require(set(c['audit_findings'])<={f'F{i:02d}' for i in range(1,25)},'Unknown fixture audit ID')
        require(c['profile'] in {'PN','PS'},'Unspecified compatibility profile')
        require(c['kind'] in {'source','configuration'},'Unknown fixture kind')
        require(isinstance(c['initial_state'],dict) and isinstance(c['expected'],dict),'Fixture lacks typed setup/expectation')
        if c['kind']=='source':require(isinstance(c.get('source_utf8'),str),'Missing exact source')
        else:require(isinstance(c.get('request'),dict),'Missing configuration request')
        require(c['evidence']['status']=='UNEXECUTED' and c['evidence']['native_execution'] is False and c['evidence']['lean_execution'] is False,'Unfounded execution evidence')
        validate_value(c['expected'])
    coverage=load(root,'coverage-plan-v1.1.json')
    require(len(cases)==coverage['delivered_fixtures']==68,'Fixture count drift')
    require(sum(c['kind']=='source' for c in cases)==coverage['source_fixtures']==13,'Source fixture count drift')
    require(coverage['native_executions']==coverage['lean_executions']==0,'Coverage records nonexistent execution')
    # A rendering check rather than a source-hash label alone.
    for filename in DOCUMENTS:
        actual=(root/Path(filename).with_suffix('.html')).read_text(encoding='utf-8')
        require(actual==render_document(root,filename),'HTML does not match active Markdown/CSS: '+filename)
    sums={}
    for line in (root/'SHA256SUMS').read_text().splitlines():
        digest,path=line.split('  ',1)
        require(path not in sums,'Duplicate checksum entry')
        require(not Path(path).is_absolute() and '..' not in Path(path).parts,'Unsafe checksum path')
        sums[path]=digest
    all_files={p.relative_to(root).as_posix():p for p in checksum_paths(root)}
    require(set(sums)==set(all_files),'Checksum manifest does not cover exact file set')
    for name,p in all_files.items():require(sha256(p.read_bytes())==sums[name],'Checksum mismatch: '+name)
    return {'status':'PASS — document/data/structure/integrity only','registered_source_words':len(words),
            'named_profiles':len(profiles),'augmented_words':len(aug),'supplied_reference_table_words_compared':len(checked),
            'independent_native_source_extraction_performed':False,'active_table_manifest_agreement':True,
            'exact_quotation_policy_checks':True,'lexical_route_checks':True,'html_editions_verified':len(DOCUMENTS),
            'checksum_entries_verified':len(sums),'audit_findings_accounted_for':len(items),'open_contracts':len(oc),
            'typed_fixtures':len(cases),'fixtures_executed':0,'behavioral_expectations_validated':False,
            'native_M2_execution_performed':False,'lean_compilation_performed':False,'formal_proof_performed':False}

def main()->int:
    root=Path(sys.argv[1]).resolve() if len(sys.argv)>1 else Path(__file__).resolve().parent
    try:print(json.dumps(validate(root),ensure_ascii=False,indent=2));return 0
    except (OSError,ValueError,KeyError,TypeError,IndexError,RuntimeError) as exc:
        print('FAIL: '+str(exc),file=sys.stderr);return 1
if __name__=='__main__':raise SystemExit(main())
