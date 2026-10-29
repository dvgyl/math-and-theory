#!/usr/bin/env python3
"""Check all local proof sources in one process with the pinned external cache."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import signal
import subprocess
import time

PIN = 'c44e0c8ee63ca166450922a373c7409c5d26b00b'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
HERE = Path(__file__).resolve().parent

def without_comments(source):
    out, i, depth = [], 0, 0
    while i < len(source):
        if source.startswith('/-', i):
            depth += 1
            i += 2
        elif depth and source.startswith('-/', i):
            depth -= 1
            i += 2
        elif depth:
            if source[i] == '\n': out.append('\n')
            i += 1
        elif source[i] == '"':
            out.append(' ')
            i += 1
            while i < len(source):
                if source[i] == '\\':
                    i += 2
                elif source[i] == '"':
                    i += 1
                    break
                else:
                    if source[i] == '\n': out.append('\n')
                    i += 1
        elif source.startswith('--', i):
            end = source.find('\n', i)
            i = len(source) if end < 0 else end
        else:
            out.append(source[i]); i += 1
    if depth: raise ValueError('Unclosed block comment')
    return ''.join(out)

def fingerprint_dependencies(external, mathlib, leanbin):
    packages = [p for p in sorted(mathlib.parent.iterdir()) if p.is_dir()]
    locations = [(p.name, p, p/'.lake/build/lib/lean') for p in packages]
    locations.append(('lean-core', leanbin.parent/'src/lean', leanbin.parent/'lib/lean'))
    records, active = {}, set()
    def visit(module):
        if module in records or module in active: return
        active.add(module)
        rel = Path(*module.split('.'))
        found = [(name, src/rel.with_suffix('.lean'), obj/rel.with_suffix('.olean'))
            for name,src,obj in locations if (src/rel.with_suffix('.lean')).is_file()]
        if len(found)!=1: raise ValueError('Unresolved or ambiguous dependency: '+module)
        name,src,obj=found[0]
        if not obj.is_file(): raise ValueError('Missing compiled dependency: '+module)
        clean=without_comments(src.read_text())
        deps=[]
        if not re.search(r'^prelude\s*$',clean,re.M) and module!='Init': deps.append('Init')
        for line in re.findall(r'^import\s+([^\n]+)',clean,re.M): deps.extend(line.split())
        for dep in deps: visit(dep)
        records[module]={'module':module,'package':name,
            'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),
            'object_sha256':hashlib.sha256(obj.read_bytes()).hexdigest()}
        active.remove(module)
    for module in external: visit(module)
    return [records[name] for name in sorted(records)]

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--mathlib', type=Path, required=True)
    parser.add_argument('--lean-bin', type=Path, required=True)
    parser.add_argument('--output', type=Path, default=HERE/'verification')
    parser.add_argument('--timeout', type=int, default=600)
    args = parser.parse_args()
    mathlib, leanbin, out = args.mathlib.resolve(), args.lean_bin.resolve(), args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    (out/'verification.json').write_text(json.dumps({'all_passed':False,'status':'preflight'},indent=2)+'\n')
    (out/'UnicyclicAll.olean').unlink(missing_ok=True)
    env = dict(os.environ, LEAN_PATH=str(out))
    env['PATH'] = str(leanbin)+os.pathsep+env.get('PATH', '')
    env['LEAN_SYSROOT']=str(leanbin.parent)
    env.pop('LEAN_SRC_PATH',None)
    paths=[str(out)]+[str(p/'.lake/build/lib/lean') for p in sorted(mathlib.parent.iterdir())
        if (p/'.lake/build/lib/lean').is_dir()]
    env['LEAN_PATH']=os.pathsep.join(paths)
    rev = subprocess.check_output(['git','-C',str(mathlib),'rev-parse','HEAD'], text=True).strip()
    if rev != PIN: raise ValueError('Unexpected mathlib revision: '+rev)
    version = subprocess.check_output([str(leanbin/'lean'),'--version'],env=env,text=True).strip()
    if not re.search(r'\bversion 4\.19\.0\b',version): raise ValueError('Unexpected Lean version: '+version)
    modules = {p.stem:p for p in (HERE/'proof').glob('*.lean')}
    ordered, active, seen, external = [], set(), set(), set()
    def visit(name):
        if name in seen: return
        if name in active: raise ValueError('Import cycle: '+name)
        active.add(name)
        source = without_comments(modules[name].read_text())
        if re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|ofReduceBool|ofReduceNat|debug\.skipKernelTC)\b',source):
            raise ValueError('Disallowed proof shortcut in '+name)
        for line in re.findall(r'^import\s+([^\n]+)',source,re.M):
            for dep in line.split():
                if dep in modules: visit(dep)
                elif dep.startswith(('Mathlib.','Lean.','Std.')): external.add(dep)
                else: raise ValueError('Unknown dependency: '+dep)
        active.remove(name); seen.add(name); ordered.append(name)
    visit('AllResults')
    if set(modules) != seen: raise ValueError('Uncovered source modules')
    result = {'all_passed':False,'lean':version,'mathlib_revision':rev,'target':'AllResults',
              'mode':'all local source; external library imports only','status':'compiling','trust':0,'warnings_as_errors':True,'modules':[]}
    result['external_dependency_fingerprints']=fingerprint_dependencies(external,mathlib,leanbin)
    result['lean_executable_sha256']=hashlib.sha256((leanbin/'lean').read_bytes()).hexdigest()
    combined = '\n'.join('import '+dep for dep in sorted(external))+'\n\n'
    for index,name in enumerate(ordered):
        source = modules[name].read_text()
        record = {'module':name,'source':'proof/'+modules[name].name,
                  'source_sha256':hashlib.sha256(modules[name].read_bytes()).hexdigest()}
        result['modules'].append(record)
        combined += '/- '+record['source']+'; SHA256 '+record['source_sha256']+' -/\n'
        combined += 'section CheckedModule'+str(index)+'\n'
        combined += re.sub(r'^import[^\n]*\n','',source,flags=re.M)
        combined += '\nend CheckedModule'+str(index)+'\n\n'
    combined += '\nset_option pp.universes true\nset_option pp.explicit true\n'
    for name in ['UnicyclicWinding.winding_skewness_interval',
                 'UnicyclicWinding.exists_winding_branch_and_interval',
                 'UnicyclicTwoState.two_state_winding_interval',
                 'UnicyclicPoissonBoundary.poisson_winding_skewness']:
        combined += '#check @'+name+'\n'
    for name in ['UnicyclicDeterminant.ringMatrix','UnicyclicDeterminant.rateMatrix',
                 'UnicyclicDeterminant.edgeTilt','UnicyclicWinding.tiltedCharacteristic',
                 'UnicyclicActual.rateSkewness']:
        combined += '#print '+name+'\n'
    source = out/'UnicyclicAll.lean'; obj=out/'UnicyclicAll.olean'; log=out/'UnicyclicAll.log'
    source.write_text(combined)
    obj.unlink(missing_ok=True)
    result['combined_source_sha256']=hashlib.sha256(source.read_bytes()).hexdigest()
    report=out/'verification.json'
    report.write_text(json.dumps(result,indent=2)+'\n')
    start=time.monotonic()
    with log.open('w') as stream:
        def restrict_memory():
            resource.setrlimit(resource.RLIMIT_AS, (8*1024**3,8*1024**3))
        process=subprocess.Popen([str(leanbin/'lean'),'--trust=0','-j1','-DwarningAsError=true',
            '-o',obj.name,source.name],cwd=out,env=env,
            stdout=stream,stderr=subprocess.STDOUT,start_new_session=True,preexec_fn=restrict_memory)
        try: code=process.wait(timeout=args.timeout)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid,signal.SIGTERM)
            try: process.wait(timeout=10)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid,signal.SIGKILL);process.wait()
            code=124
    output=log.read_text()
    reports=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",output,re.S)
    axioms={a.strip() for _,values in reports for a in values.split(',') if a.strip()}
    principals={'UnicyclicWinding.winding_skewness_interval',
                'UnicyclicWinding.exists_winding_branch_and_interval'}
    printed={name for name,_ in reports}
    result.update({'exit_code':code,'seconds':round(time.monotonic()-start,3),
                   'axiom_reports':len(reports),'axioms':sorted(axioms),
                   'principal_reports_present':principals<=printed,'log':log.name})
    result['dependency_fingerprints_unchanged']=(result['external_dependency_fingerprints']==
        fingerprint_dependencies(external,mathlib,leanbin))
    result['local_source_hashes_unchanged']=all(
        hashlib.sha256((HERE/r['source']).read_bytes()).hexdigest()==r['source_sha256']
        for r in result['modules'])
    result['warnings']=len(re.findall(r'\bwarning:',output))
    result['all_passed']=(code==0 and result['local_source_hashes_unchanged'] and result['dependency_fingerprints_unchanged'] and result['warnings']==0 and obj.exists() and principals<=printed
        and len(reports)>=80 and axioms<=ALLOWED and 'sorryAx' not in output)
    result['status']='passed' if result['all_passed'] else 'failed'
    report.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('modules','external_dependency_fingerprints')},indent=2))
    return 0 if result['all_passed'] else 1

if __name__=='__main__': raise SystemExit(main())
