#!/usr/bin/env python3
"""Emit census tables with no dependence on unproved executable rank decisions."""
import json
from lean_table import tree
from itertools import permutations
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
data=json.loads((ROOT/'evidence/support-closure.json').read_text())
def vec(xs): return '!['+','.join(map(str,xs))+']'
perms=list(permutations(range(4)));lookup={p:i for i,p in enumerate(perms)}
actions=[]
for r in perms:
    ri=[r.index(i) for i in range(4)]
    for c in perms:
        actions.append([lookup[tuple(c[p[ri[i]]] for i in range(4))] for p in perms])
lines=['import FourRow.Census\nimport FourRow.LookupTree','set_option maxRecDepth 100000','set_option maxHeartbeats 0','namespace FourRow.Census',
'''def relabel (g : Fin 576) : Relabel :=
  (permEquiv ⟨g.val / 24, by omega⟩, permEquiv ⟨g.val % 24, by omega⟩)
''',
'def literalActions : LookupTree (PermIndex → PermIndex) := '+tree(vec(v) for v in actions),
'def literalAction (g : Fin 576) : PermIndex → PermIndex := literalActions.get g.val',
'''theorem literalAction_permutation : ∀ g : Fin 576, ∀ p : PermIndex, ∀ i : Row,
  permutation (literalAction g p) i =
    permutation ⟨g.val % 24, by omega⟩ (permutation p
      (permutation (inverseIndex ⟨g.val / 24, by omega⟩) i)) := by decide +kernel

theorem literalAction_eq (g : Fin 576) (p : PermIndex) :
  literalAction g p = action (relabel g) p := by
  apply permEquiv_bijective.1
  apply Equiv.ext
  intro i
  change permutation (literalAction g p) i = permutation (action (relabel g) p) i
  have h := congrArg (fun σ : Perm4 => σ i)
    (show lexEquiv (action (relabel g) p) = (relabel g).2 * lexEquiv p * (relabel g).1⁻¹ by
      simp [action,Equiv.trans_apply])
  exact (literalAction_permutation g p i).trans h.symm
''',
'def independentMasks : LookupTree ℕ := '+tree(str(r['mask']) for r in data['independent']),
'def circuitMasks : LookupTree ℕ := '+tree(str(r['support_mask']) for r in data['circuits']),
'''def maskSupport (mask : ℕ) : Finset PermIndex :=
  Finset.univ.filter (fun p => mask.testBit p.val)

def independentSupport (i : Fin 5109) : Finset PermIndex := maskSupport (independentMasks.get i.val)
def circuitSupport (i : Fin 73) : Finset PermIndex := maskSupport (circuitMasks.get i.val)
''',
'def primitives : LookupTree (PermIndex → ℤ) := '+tree(vec(r['primitive']) for r in data['circuits']),
'def primitive (i : Fin 73) : PermIndex → ℤ := primitives.get i.val',
'''theorem primitive_support : ∀ i : Fin 73, ∀ p : PermIndex,
  p ∈ circuitSupport i ↔ primitive i p ≠ 0 := by decide +kernel

theorem primitive_nonzero : ∀ i : Fin 73, ∃ p, primitive i p ≠ 0 := by decide +kernel

theorem primitive_kernel_int : ∀ k : Fin 73, ∀ i j : Row,
  ∑ p, incidence i j p * primitive k p = 0 := by decide +kernel

theorem primitive_kernel (k : Fin 73) : Kernel (fun p => (primitive k p : ℝ)) := by
  intro i j
  exact_mod_cast primitive_kernel_int k i j

end FourRow.Census''']
(ROOT/'FourRow/CensusTables.lean').write_text('\n'.join(lines)+'\n')
