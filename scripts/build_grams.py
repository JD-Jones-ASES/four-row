#!/usr/bin/env python3
"""Build the generated Gram proofs in bounded batches (safe on modest RAM)."""
import argparse,json,os,subprocess,time
from pathlib import Path
p=argparse.ArgumentParser()
p.add_argument('--jobs',type=int,default=1)
p.add_argument('--shard',type=int,default=0)
p.add_argument('--shards',type=int,default=1)
args=p.parse_args()
if args.jobs < 1 or args.shards < 1 or not 0 <= args.shard < args.shards:
 p.error('jobs and shards must be positive; shard must be in [0, shards)')
root=Path(__file__).resolve().parents[1]
logdir=root/'.lake/gram-build'/f'shard-{args.shard}-of-{args.shards}'
logdir.mkdir(parents=True,exist_ok=True)
lake=os.environ.get('FOUR_ROW_LAKE','lake')
results=[]
lo,hi=131*args.shard//args.shards,131*(args.shard+1)//args.shards
for start in range(lo,hi,args.jobs):
 names=[f'FourRow.Grams.G{i:03}' for i in range(start,min(start+args.jobs,hi))]
 t=time.monotonic()
 with (logdir/f'{start:03}.log').open('w') as log:
  r=subprocess.run([lake,'build',*names],cwd=root,stdout=log,stderr=subprocess.STDOUT,
    env={**os.environ,'LEAN_NUM_THREADS':'2'})
 results.append(dict(modules=names,exit_code=r.returncode,seconds=round(time.monotonic()-t,2)))
 (logdir/'results.json').write_text(json.dumps(results,indent=2)+'\n')
 print(f'{min(start+args.jobs,hi)}/{hi}: code={r.returncode}, seconds={results[-1]["seconds"]}',flush=True)
 if r.returncode: raise SystemExit(r.returncode)
