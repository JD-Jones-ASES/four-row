#!/usr/bin/env python3
"""Emit literal census tables and small independent kernel-checked fact blocks."""
import json
from lean_table import tree
from itertools import permutations
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
data=json.loads((ROOT/'evidence/support-closure.json').read_text())
def vec(xs): return '!['+','.join(map(str,xs))+']'
def write(path,text):
    temp=path.with_suffix(path.suffix+'.tmp');temp.write_text(text);temp.replace(path)
perms=list(permutations(range(4)));lookup={p:i for i,p in enumerate(perms)}
actions=[]
for r in perms:
    ri=[r.index(i) for i in range(4)]
    for c in perms:
        actions.append([lookup[tuple(c[p[ri[i]]] for i in range(4))] for p in perms])
header='set_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace FourRow.Census\n'
lines=['import FourRow.Finite\nimport FourRow.LookupTree',header,
'''def relabel (g : Fin 576) : Relabel :=
  (permEquiv ⟨g.val / 24, by omega⟩, permEquiv ⟨g.val % 24, by omega⟩)
''',
'def literalActions : LookupTree (PermIndex → PermIndex) := '+tree(vec(v) for v in actions),
'def literalAction (g : Fin 576) : PermIndex → PermIndex := literalActions.get g.val',
'def independentMasks : LookupTree ℕ := '+tree(str(r['mask']) for r in data['independent']),
'def circuitMasks : LookupTree ℕ := '+tree(str(r['support_mask']) for r in data['circuits']),
'''def maskSupport (mask : ℕ) : Finset PermIndex :=
  Finset.univ.filter (fun p => mask.testBit p.val)

def independentSupport (i : Fin 5109) : Finset PermIndex := maskSupport (independentMasks.get i.val)
def circuitSupport (i : Fin 73) : Finset PermIndex := maskSupport (circuitMasks.get i.val)
''',
'def primitives : LookupTree (PermIndex → ℤ) := '+tree(vec(r['primitive']) for r in data['circuits']),
'def primitive (i : Fin 73) : PermIndex → ℤ := primitives.get i.val',
'''def actionPair (r c : Fin 24) : Fin 576 := ⟨r.val * 24 + c.val, by omega⟩

def ValidAction (g : Fin 576) : Prop := ∀ p : PermIndex, ∀ i : Row,
  permutation (literalAction g p) i =
    permutation ⟨g.val % 24, by omega⟩ (permutation p
      (permutation (inverseIndex ⟨g.val / 24, by omega⟩) i))

instance (g : Fin 576) : Decidable (ValidAction g) := by unfold ValidAction; infer_instance

def ValidPrimitive (k : Fin 73) : Prop :=
  (∀ p : PermIndex, p ∈ circuitSupport k ↔ primitive k p ≠ 0) ∧
  (∃ p : PermIndex, primitive k p ≠ 0) ∧
  (∀ i j : Row, ∑ p : PermIndex, incidence i j p * primitive k p = 0)

instance (k : Fin 73) : Decidable (ValidPrimitive k) := by unfold ValidPrimitive; infer_instance

end FourRow.Census''']
write(ROOT/'FourRow/CensusTableData.lean','\n'.join(lines)+'\n')
folder=ROOT/'FourRow/CensusTableChecks';folder.mkdir(exist_ok=True)
for r in range(24):
    src='import FourRow.CensusTableData\n'+header
    src+=f'theorem action_checked_{r:02d} : ∀ c : Fin 24, ValidAction (actionPair {r} c) := by decide +kernel\n'
    src+='end FourRow.Census\n'
    write(folder/f'Action{r:02d}.lean',src)
for b,start in enumerate(range(0,73,8)):
    n=min(8,73-start)
    src='import FourRow.CensusTableData\n'+header
    src+=f'def primitiveSource{b:02d} (i : Fin {n}) : Fin 73 := ⟨{start}+i.val, by omega⟩\n'
    src+=f'theorem primitive_checked_{b:02d} : ∀ i : Fin {n}, ValidPrimitive (primitiveSource{b:02d} i) := by decide +kernel\n'
    src+='end FourRow.Census\n'
    write(folder/f'Primitive{b:02d}.lean',src)
imports='import FourRow.CensusTableData\nimport Mathlib.Algebra.BigOperators.Ring.Finset\n'+''.join(f'import FourRow.CensusTableChecks.Action{r:02d}\n' for r in range(24))+''.join(f'import FourRow.CensusTableChecks.Primitive{b:02d}\n' for b in range(10))
body=imports+header+'''theorem actionPair_valid (r c : Fin 24) : ValidAction (actionPair r c) := by
  fin_cases r
'''
body+=''.join(f'  · exact action_checked_{r:02d} c\n' for r in range(24))
body+='''
theorem all_action_valid (g : Fin 576) : ValidAction g := by
  let r : Fin 24 := ⟨g.val / 24, by omega⟩
  let c : Fin 24 := ⟨g.val % 24, by omega⟩
  have hg : actionPair r c = g := by
    apply Fin.ext
    simp only [actionPair, r, c]
    omega
  rw [← hg]
  exact actionPair_valid r c

theorem literalAction_permutation (g : Fin 576) (p : PermIndex) (i : Row) :
  permutation (literalAction g p) i =
    permutation ⟨g.val % 24, by omega⟩ (permutation p
      (permutation (inverseIndex ⟨g.val / 24, by omega⟩) i)) := all_action_valid g p i

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

theorem all_primitives_valid (k : Fin 73) : ValidPrimitive k := by
  fin_cases k
'''
body+=''.join(f'  · exact primitive_checked_{k//8:02d} {k%8}\n' for k in range(73))
body+='''
theorem primitive_support (i : Fin 73) (p : PermIndex) :
    p ∈ circuitSupport i ↔ primitive i p ≠ 0 := (all_primitives_valid i).1 p

theorem primitive_nonzero (i : Fin 73) : ∃ p, primitive i p ≠ 0 :=
  (all_primitives_valid i).2.1

theorem primitive_kernel_int (k : Fin 73) (i j : Row) :
    ∑ p, incidence i j p * primitive k p = 0 := (all_primitives_valid k).2.2 i j

theorem primitive_kernel (k : Fin 73) : Kernel (fun p => (primitive k p : ℝ)) := by
  intro i j
  change (∑ p : PermIndex, (incidence i j p : ℝ) * (primitive k p : ℝ)) = 0
  exact_mod_cast primitive_kernel_int k i j

end FourRow.Census
'''
write(ROOT/'FourRow/CensusTables.lean',body)
