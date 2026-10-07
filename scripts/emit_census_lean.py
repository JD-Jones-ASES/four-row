#!/usr/bin/env python3
"""Emit literal Lean arithmetic certificates from support-closure.json."""
import argparse
import json
from itertools import permutations
from pathlib import Path


def vec(xs): return '!['+','.join(map(str,xs))+']'
def rec(record):
    cols=[i for i in range(24) if record['mask']>>i&1]
    c=record['certificate']
    perms=list(permutations(range(4)))
    b=[[int(perms[j][i//4]==i%4) for j in cols] for i in c['rows']]
    return f'⟨{len(cols)},{vec(cols)},{vec(c["rows"])},{c["scale"]},{vec(vec(row) for row in c["inverse"])},{vec(vec(row) for row in b)}⟩'

def main():
    p=argparse.ArgumentParser();p.add_argument('--input',type=Path,required=True);p.add_argument('--root',type=Path,required=True);p.add_argument('--sample',type=int,default=64);a=p.parse_args()
    data=json.loads(a.input.read_text());out=a.root/'FourRow';out.mkdir(exist_ok=True)
    n=a.sample
    chosen=data['independent'][-n:]
    lines=['import FourRow.Census','set_option maxRecDepth 100000','set_option maxHeartbeats 0','namespace FourRow.Census.Benchmark',
      'def records : Array IndependentRecord := #[\n'+',\n'.join(rec(r) for r in chosen)+'\n]',
      'def record (i : Fin '+str(n)+') : IndependentRecord := records[i.val]!',
      'theorem records_valid : ∀ i : Fin '+str(n)+', (record i).Valid  := by decide +kernel',
      'end FourRow.Census.Benchmark']
    # getElem! needs a harmless default.
    lines.insert(4,'instance : Inhabited IndependentRecord := ⟨⟨0,![],![],1,![],![]⟩⟩')
    (out/'CensusBenchmark.lean').write_text('\n'.join(lines)+'\n')

if __name__=='__main__':main()
