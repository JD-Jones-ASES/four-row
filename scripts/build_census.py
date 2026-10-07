#!/usr/bin/env python3
"""Bounded-memory sequential build of kernel-checked census certificate blocks."""
from pathlib import Path
import argparse
import subprocess
import time
ROOT=Path(__file__).resolve().parents[1]
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--lake',default='lake')
p.add_argument('--start',type=int,default=0)
a=p.parse_args()
modules=['FourRow.CensusTables','FourRow.CensusWitness']
modules += [f'FourRow.CensusData.Max{i:02}' for i in range(41)]
modules += ['FourRow.CensusIndependence']
modules += [f'FourRow.CensusData.Extension{i:02}' for i in range(40)]
modules += ['FourRow.CensusCoverage']
logs=ROOT/'build-logs'/'census';logs.mkdir(parents=True,exist_ok=True)
for idx,mod in enumerate(modules[a.start:],a.start):
    started=time.monotonic()
    log=logs/(mod+'.log')
    with log.open('w') as f:
        proc=subprocess.Popen([a.lake,'build',mod],cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
        (logs/'active-pid.txt').write_text(str(proc.pid)+'\n')
        status=proc.wait()
    print(f'{idx+1}/{len(modules)} {mod}: exit={status} seconds={time.monotonic()-started:.1f}',flush=True)
    if status:
        print(log.read_text()[-6000:],flush=True)
        raise SystemExit(status)
print('Complete support census kernel build passed.',flush=True)
