#!/usr/bin/env python3
"""Generate proof-carrying support closure, with no trusted rank algorithm.

The output supplies integer left inverses for independent supports and a
row/column action witness for every extension. A dependent extension contains
a transformed saved circuit; an independent extension is a transformed saved
independent support. The Lean checker must verify all these finite identities
and its generic coverage theorem before this proves real-law coverage.

Only Python's standard library is used. Discovery arithmetic here is not an
axiom. Run with --source <evidence directory> and --output <json path>.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
from functools import reduce
from itertools import permutations
import json
from math import gcd, lcm
from pathlib import Path


def rref(a):
    a = [[Fraction(v) for v in row] for row in a]
    pivots = []
    for j in range(len(a[0])):
        k = len(pivots)
        p = next((i for i in range(k, len(a)) if a[i][j]), None)
        if p is None:
            continue
        a[k], a[p] = a[p], a[k]
        d = a[k][j]
        a[k] = [v/d for v in a[k]]
        for i in range(len(a)):
            if i != k and a[i][j]:
                q = a[i][j]
                a[i] = [u-q*v for u,v in zip(a[i],a[k])]
        pivots.append(j)
        if len(pivots) == len(a):
            break
    return a, pivots


def support(mask):
    return [i for i in range(24) if mask >> i & 1]


def left_inverse(b, mask):
    cols = support(mask)
    k = len(cols)
    if not k:
        return {'rows': [], 'scale': 1, 'inverse': []}
    _, rows = rref([[b[i][j] for i in range(16)] for j in cols])
    assert len(rows) == k
    sq = [[b[i][j] for j in cols] for i in rows]
    reduced, pivots = rref([row + [int(i == j) for j in range(k)] for i,row in enumerate(sq)])
    assert pivots == list(range(k))
    inverse = [row[k:] for row in reduced]
    scale = lcm(*(v.denominator for row in inverse for v in row))
    ints = [[int(v*scale) for v in row] for row in inverse]
    assert all(sum(ints[i][t]*sq[t][j] for t in range(k)) == scale*int(i==j)
               for i in range(k) for j in range(k))
    return {'rows':rows, 'scale':scale, 'inverse':ints}


def generate(source, output):
    saved = json.loads((source/'circuits.json').read_text())
    perms = list(permutations(range(4)))
    lookup = {p:i for i,p in enumerate(perms)}
    assert saved['permutations'] == [list(p) for p in perms]
    b = [[int(p[i]==j) for p in perms] for i in range(4) for j in range(4)]
    # Actual left action (r,c) sends p to c p r^{-1}.
    actions = []
    for r in perms:
        ri = [r.index(i) for i in range(4)]
        for c in perms:
            actions.append(tuple(lookup[tuple(c[p[ri[i]]] for i in range(4))] for p in perms))
    action_index = {g:i for i,g in enumerate(actions)}
    inverses = [action_index[tuple(g.index(i) for i in range(24))] for g in actions]
    tables = []
    for block in range(3):
        table = [[0]*576 for _ in range(256)]
        for mask in range(1,256):
            low = mask & -mask
            bit = low.bit_length()-1
            table[mask] = [v | (1 << g[8*block+bit]) for v,g in zip(table[mask ^ low],actions)]
        tables.append(table)
    cache = {}
    def canonical(mask):
        if mask not in cache:
            a,b,c = (tables[0][mask & 255],tables[1][mask>>8 & 255],tables[2][mask>>16])
            cache[mask] = min((x|y|z,i) for i,(x,y,z) in enumerate(zip(a,b,c)))
        return cache[mask]
    def act(g, mask):
        return sum(1<<actions[g][j] for j in support(mask))
    def comp(g,h):
        return action_index[tuple(actions[g][actions[h][j]] for j in range(24))]
    circuit_masks = {r['support_mask']:i for i,r in enumerate(saved['records'])}
    records = [{'mask':0, 'certificate':left_inverse(b,0)}]
    by_mask = {0:0}
    frontier = [0]
    # Each temporary extension target refers to an eventual mask, or circuit index.
    edge_data = {}
    totals = []
    for size in range(1,12):
        extensions = {(mask,j):canonical(mask | 1<<j) for mask in frontier for j in range(24) if not mask>>j&1}
        candidates = sorted({v[0] for v in extensions.values()})
        classes = {}
        next_frontier = []
        for mask in candidates:
            cols = support(mask)
            reduced,pivots = rref([[row[j] for j in cols] for row in b])
            if len(pivots)==size:
                classes[mask] = ('independent',mask,0)
                next_frontier.append(mask)
                by_mask[mask] = len(records)
                records.append({'mask':mask,'certificate':left_inverse(b,mask)})
            else:
                assert len(pivots)==size-1
                free = next(j for j in range(size) if j not in pivots)
                vec = [Fraction(int(j==free)) for j in range(size)]
                for i,j in enumerate(pivots):
                    vec[j] = -reduced[i][free]
                submask = sum(1<<j for j,v in zip(cols,vec) if v)
                representative,g = canonical(submask)
                assert representative in circuit_masks
                h = inverses[g]
                assert act(h,representative) & mask == act(h,representative)
                classes[mask] = ('dependent',circuit_masks[representative],h)
        for (mask,j),(target,g) in extensions.items():
            kind,dest,h = classes[target]
            # raw extension = g^{-1}(canonical extension).
            edge_data[mask,j] = (kind,dest,comp(inverses[g],h))
        totals.append([size,len(candidates),len(next_frontier)])
        print('generated layer',totals[-1],flush=True)
        frontier=next_frontier
    assert not frontier and len(records)==5109
    for record in records:
        mask=record['mask']
        edges=[]
        for j in range(24):
            if mask>>j&1:
                edges.append(None)
                continue
            kind,dest,g=edge_data[mask,j]
            if kind=='independent':
                target=by_mask[dest]
                assert act(g,dest)==mask | 1<<j
                edges.append([0,target,g])
            else:
                cm=saved['records'][dest]['support_mask']
                assert act(g,cm) & (mask | 1<<j)==act(g,cm)
                edges.append([1,dest,g])
        record['extensions']=edges
    payload={
      'format':'four-row-support-closure-v1',
      'permutations':[list(p) for p in perms],
      'action_convention':'(row,column): p -> column o p o inverse(row)',
      'circuits':saved['records'],
      'layers':totals,
      'independent':records,
    }
    output.parent.mkdir(parents=True,exist_ok=True)
    output.write_text(json.dumps(payload,separators=(',',':'))+'\n')
    print('wrote',output,'bytes',output.stat().st_size,flush=True)

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    generate(args.source,args.output)
