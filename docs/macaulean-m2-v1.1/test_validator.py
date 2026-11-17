#!/usr/bin/env python3
"""Run isolated structural negative controls. Does not execute M2 or Lean.

Every mutation uses a temporary copy and refreshes checksums, so semantic/data
consistency checks—not merely an old checksum—must detect the relevant drift.
"""
from __future__ import annotations
import json,re,shutil,tempfile
from pathlib import Path
from spec_support import (DOCUMENTS,GRAMMAR_BEGIN,GRAMMAR_END,grammar_markdown,render_all,write_checksums)
from validate_spec import validate,ValidationError

def rewrite_json(root,name,mutate):
    p=root/name;obj=json.loads(p.read_text());mutate(obj);p.write_text(json.dumps(obj,ensure_ascii=False,indent=2)+'\n')

def replace_table(root):
    p=root/DOCUMENTS[0];text=p.read_text();g=json.loads((root/'m2-grammar-1.26.06.json').read_text())
    begin=text.index(GRAMMAR_BEGIN)+len(GRAMMAR_BEGIN);end=text.index(GRAMMAR_END,begin)
    p.write_text(text[:begin]+'\n'+grammar_markdown(g)+'\n'+text[end:])

def mutate_table(root):
    p=root/DOCUMENTS[0];s=p.read_text()
    s,n=re.subn(r'(\| `\+`, `-` \| )50( \|)',r'\g<1>49\2',s,count=1)
    if n!=1:raise RuntimeError('Sign row not found')
    p.write_text(s);render_all(root)

def mutate_quote(root):
    def f(g):g['profiles']['quote_symbol']['quote_policy']='global'
    rewrite_json(root,'m2-grammar-1.26.06.json',f);replace_table(root);render_all(root)

def mutate_route(root):
    def f(g):next(w for w in g['words'] if w['spelling']=='+')['lexical_route']='identifier'
    rewrite_json(root,'m2-grammar-1.26.06.json',f);replace_table(root);render_all(root)

def mutate_skip(root):
    rewrite_json(root,'m2-grammar-1.26.06.json',lambda g:g['source_unit_skip_tokens'].append(';'))

def mutate_behavior(root):
    def f(plan):
        c=next(c for c in plan['fixtures'] if c['id']=='REG-BASE-ARITH')
        c['expected']['completion']['value']['decimal']='999'
    rewrite_json(root,'audit-regressions-v1.1.json',f)

def mutate_html(root):
    p=root/Path(DOCUMENTS[0]).with_suffix('.html')
    p.write_text(p.read_text().replace('<article>','<article><p>Untracked rendered content.</p>',1))

def mutate_archive(root):
    p=root/'archive/supplied-reference.md';p.write_bytes(p.read_bytes()+b'\n')

def run(root:Path)->dict:
    baseline=validate(root)
    controls=[
        ('main-table-drift',mutate_table,False,'Active document grammar table differs'),
        ('wrong-quote-policy-with-matching-projection',mutate_quote,False,'Wrong per-word quotation policy'),
        ('wrong-lexical-route-with-matching-projection',mutate_route,False,'Wrong lexical route'),
        ('standalone-semicolon-skip',mutate_skip,False,'Source-unit skip set'),
        ('rendered-html-drift',mutate_html,False,'HTML does not match'),
        ('archived-source-drift',mutate_archive,False,'Archived supplied reference checksum'),
        ('well-typed-wrong-behavioral-expectation',mutate_behavior,True,None)]
    results=[]
    for name,mutate,expected_accept,reason in controls:
        with tempfile.TemporaryDirectory(prefix='m2-spec-control-') as tmp:
            copy=Path(tmp)/'bundle'
            shutil.copytree(root,copy,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
            mutate(copy);write_checksums(copy)
            try:
                validate(copy);accepted=True;error=None
            except ValidationError as exc:
                accepted=False;error=str(exc)
            ok=accepted==expected_accept and (reason is None or (error is not None and reason in error))
            if not ok:raise AssertionError(f'{name}: expected accept={expected_accept}, got={accepted}, error={error}')
            results.append({'name':name,'expected_structural_acceptance':expected_accept,'actual_structural_acceptance':accepted,'control_passed':ok,'reason':error})
    return {'status':'PASS — structural control behavior only','baseline_status':baseline['status'],'controls':results,
            'behavioral_expectations_validated':False,'native_M2_execution_performed':False,'lean_execution_performed':False,
            'original_inputs_modified':False}

if __name__=='__main__':
    import sys
    root=Path(sys.argv[1]).resolve() if len(sys.argv)>1 else Path(__file__).resolve().parent
    print(json.dumps(run(root),ensure_ascii=False,indent=2))
