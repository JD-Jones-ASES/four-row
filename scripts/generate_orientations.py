#!/usr/bin/env python3
"""Emit exact signed-circuit/Gram orbit identities, checked by Lean's kernel."""
from pathlib import Path
import json
from fractions import Fraction as Q
from itertools import permutations
ROOT=Path(__file__).resolve().parents[1]
perms=list(permutations(range(4))); index={p:i for i,p in enumerate(perms)}
actions=[]
for r in perms:
    inv=[r.index(i) for i in range(4)]
    for c in perms:
        actions.append([index[tuple(c[p[inv[i]]] for i in range(4))] for p in perms])
circuits=json.loads((ROOT/'evidence/support-closure.json').read_text())['circuits']
certs=json.loads((ROOT/'evidence/certificates.json').read_text())['certificates']
pairs=[]
for sign in (1,-1):
    rows=[]
    for circuit in circuits:
        x=[sign*Q(v,circuit['positive_mass']) for v in circuit['primitive']]
        wanted=[(k,[Q(w)-1 for w in cert['weights']]) for k,cert in enumerate(certs) if cert['support_mask']==circuit['support_mask']]
        found=None
        for k,y in wanted:
            for g,action in enumerate(actions):
                if all(x[action[p]]==y[p] for p in range(24)):
                    found=(k,g);break
            if found:break
        assert found
        rows.append(found)
    pairs.append(rows)
def vec(xs):return '!['+','.join(map(str,xs))+']'
src='''import FourRow.CensusTables
import FourRow.GramData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FourRow.Census
'''
src+='def primitiveL1 : Fin 73 → ℤ := '+vec(2*r['positive_mass'] for r in circuits)+'\n'
for label,rows,sign in zip(('positive','negative'),pairs,(2,-2)):
    src+=f'def {label}Gram : Fin 73 → Fin 131 := '+vec(k for k,g in rows)+'\n'
    src+=f'def {label}Relabel : Fin 73 → Fin 576 := '+vec(g for k,g in rows)+'\n'
src+='''theorem primitiveL1_eq : ∀ k : Fin 73,
    ∑ p : PermIndex, |primitive k p| = primitiveL1 k := by decide +kernel

theorem primitiveL1_pos : ∀ k : Fin 73, 0 < primitiveL1 k := by decide +kernel
'''
for label,sign in zip(('positive','negative'),(2,-2)):
    src+=f'''
theorem {label}_orientation_rat : ∀ k : Fin 73, ∀ p : PermIndex,
    ({sign} : ℚ) * (primitive k (literalAction ({label}Relabel k) p) : ℚ) =
      (primitiveL1 k : ℚ) * representative ({label}Gram k) p := by decide +kernel
'''
src+='end FourRow.Census\n'
(ROOT/'FourRow/Orientations.lean').write_text(src)
