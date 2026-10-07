#!/usr/bin/env python3
"""Build the generated Gram proofs in bounded batches (safe on modest RAM)."""
import argparse,json,os,subprocess,time
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--jobs',type=int,default=3);args=p.parse_args()
root=Path(__file__).resolve().parents[1]
logdir=root/'.lake/gram-build';logdir.mkdir(parents=True,exist_ok=True)
lake=os.environ.get('FOUR_ROW_LAKE','lake')
results=[]
for start in range(0,131,args.jobs):
 names=[f'FourRow.Grams.G{i:03}' for i in range(start,min(start+args.jobs,131))]
 t=time.monotonic()
 with (logdir/f'{start:03}.log').open('w') as log:
  r=subprocess.run([lake,'build',*names],cwd=root,stdout=log,stderr=subprocess.STDOUT,
    env={**os.environ,'LEAN_NUM_THREADS':'2'})
 results.append(dict(modules=names,exit_code=r.returncode,seconds=round(time.monotonic()-t,2)))
 (logdir/'results.json').write_text(json.dumps(results,indent=2)+'\n')
 print(f'{min(start+args.jobs,131)}/131: code={r.returncode}, seconds={results[-1]["seconds"]}',flush=True)
 if r.returncode: raise SystemExit(r.returncode)
