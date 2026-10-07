#!/usr/bin/env python3
"""Build finite action/primitive checks sequentially to bound peak memory."""
import os
from pathlib import Path
import subprocess
import sys
import time
ROOT=Path(__file__).resolve().parents[1]
LAKE=os.environ.get('FOUR_ROW_LAKE','lake')
modules=([f'FourRow.CensusTableChecks.Action{i:02d}' for i in range(24)] +
         [f'FourRow.CensusTableChecks.Primitive{i:02d}' for i in range(10)] +
         ['FourRow.CensusTables'])
for module in modules:
    start=time.monotonic()
    result=subprocess.run([LAKE,'build',module],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    print(f'{module}: exit {result.returncode}, {time.monotonic()-start:.1f}s',flush=True)
    if result.returncode:
        print(result.stdout,flush=True)
        sys.exit(result.returncode)
print('All finite table facts and public assembly checked.',flush=True)
