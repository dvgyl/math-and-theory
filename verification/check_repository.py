#!/usr/bin/env python3
"""Check public source integrity, statement configurations, and local links."""
from pathlib import Path
import json,re,sys,hashlib
from urllib.parse import unquote
root=Path(__file__).resolve().parents[1]
errors=[]
def require(ok,message):
    if not ok:errors.append(message)
def lean_code(text):
    out=[];i=0;depth=0;string=False
    while i<len(text):
        if depth:
            if text.startswith('/-',i):depth+=1;i+=2
            elif text.startswith('-/',i):depth-=1;i+=2
            else:i+=1
        elif string:
            if text[i]=='\\':i+=2
            elif text[i]=='"':string=False;i+=1
            else:i+=1
        elif text.startswith('/-',i):depth=1;i+=2
        elif text.startswith('--',i):
            end=text.find('\n',i);i=len(text) if end<0 else end
        elif text[i]=='"':string=True;i+=1
        else:out.append(text[i]);i+=1
    require(depth==0,'Unclosed Lean comment')
    return ''.join(out)
files=[p for p in root.rglob('*') if p.is_file() and not any(x in p.relative_to(root).parts for x in ['.git','.lake','__pycache__'])]
lean=[p for p in files if p.suffix=='.lean']
for p in lean:
    rel=p.relative_to(root);code=lean_code(p.read_text());challenge=rel.parts[:2]==('lean','Challenges')
    forbidden=r'\b(sorryAx|admit|native_decide|implemented_by|axiom|unsafe|extern|skipKernelTC|skipCheck)\b|Lean\.ofReduce[A-Z]\w*'
    require(re.search(forbidden,code) is None,f'Prohibited proof mechanism: {rel}')
    require(challenge or re.search(r'\bsorry\b',code) is None,f'Proof hole outside Challenge: {rel}')
    if not challenge:require(re.search(r'\bimport\s+Challenges\.',code) is None,f'Proof imports a Challenge: {rel}')
    require(not p.is_symlink(),f'Symbolic link: {rel}')
    if challenge:require(len(p.read_text().splitlines())<300,f'Challenge has at least 300 lines: {rel}')
configs=list((root/'lean/comparator').glob('*.json'));names=[]
for p in configs:
    c=json.loads(p.read_text());require(set(c)=={'challenge_module','solution_module','theorem_names','permitted_axioms'},f'Unexpected Comparator fields: {p.name}')
    require(set(c['permitted_axioms'])=={'propext','Classical.choice','Quot.sound'},f'Axiom allowlist: {p.name}')
    for key in ['challenge_module','solution_module']:
        require((root/'lean'/(c[key].replace('.','/')+'.lean')).is_file(),f'Missing module: {c[key]}')
    names+=c['theorem_names']
require(len(names)==len(set(names)),'Repeated selected theorem name')
cat=json.loads((root/'catalogue.json').read_text());families=cat['families']
require(len(families)==len(configs),'Catalogue/configuration count mismatch')
require({f['id'] for f in families}=={p.stem for p in configs},'Catalogue/configuration identifiers differ')
for f in families:
    config_path = root / 'lean/comparator' / (f['id'] + '.json')
    selected = json.loads(config_path.read_text())['theorem_names'] if config_path.is_file() else []
    require(f.get('theorems') == selected, f'Catalogue theorem coverage differs: {f["id"]}')
    d=root/'preprints'/f['id']
    for name in ['paper.tex','paper.pdf','references.bib','citation.bib','README.md']:require((d/name).is_file(),f'Missing paper artifact: {f["id"]}/{name}')
    require((root/'lean/docs'/(f['id']+'.md')).is_file(),f'Missing formal guide: {f["id"]}')
links=0
for p in files:
    if p.suffix!='.md':continue
    text=p.read_text()
    for match in re.finditer(r'\[[^\]]*\]\(([^)]+)\)',text):
        target=match[1].split(' "')[0].strip('<>')
        if re.match(r'[a-zA-Z][a-zA-Z0-9+.-]*:',target) or target.startswith('#'):continue
        target=unquote(target.split('#')[0])
        if not target:continue
        links+=1;require((p.parent/target).exists(),f'Broken local link: {p.relative_to(root)} -> {target}')
    require(('Dev' + ' Goyal') not in text,f'Incorrect author name: {p.relative_to(root)}')
for p in files:
    if p.suffix in {'.md','.tex','.bib','.json','.yaml','.toml','.lean','.py','.sh','.rb','.txt','.log'}:
        text=p.read_text(errors='replace')
        require(not re.search(r'/Users/[A-Za-z0-9_.-]+/|/home/[A-Za-z0-9_.-]+/|gh[pousr]_[A-Za-z0-9]{20}',text),f'Private path or credential-like text: {p.relative_to(root)}')
        require(('Dev' + ' Goyal') not in text,f'Incorrect author name: {p.relative_to(root)}')
print(json.dumps({'status':'FAIL' if errors else 'PASS','families':len(families),'papers':len(families),'selected_statements':len(names),'lean_files':len(lean),'local_links':links,'errors':errors},indent=2))
sys.exit(bool(errors))
