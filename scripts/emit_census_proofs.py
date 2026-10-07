#!/usr/bin/env python3
"""Emit kernel-checked census support coverage; no native_decide is used."""
import json
from lean_table import tree
from itertools import permutations
from lean_source import module_source, write_lean
from pathlib import Path
from emit_census_lean import vec, rec
ROOT=Path(__file__).resolve().parents[1]
def write_serial(path,source,predecessor):
    # Public declarations stay unchanged; only the build-order dependency is
    # private. Insert it after module_source has normalized the public imports.
    source=module_source(source)
    marker='\n@[expose] public section\n'
    assert marker in source
    source=source.replace(marker,f'\nimport {predecessor}\n'+marker,1)
    write_lean(path,source)

data=json.loads((ROOT/'evidence/support-closure.json').read_text())
inds=data['independent'];perms=list(permutations(range(4)));index={p:i for i,p in enumerate(perms)}
actions=[]
for r in perms:
    ri=[r.index(i) for i in range(4)]
    for c in perms:
        actions.append(tuple(index[tuple(c[p[ri[i]]] for i in range(4))] for p in perms))
ai={g:i for i,g in enumerate(actions)}
def comp(g,h):return ai[tuple(actions[g][actions[h][j]] for j in range(24))]
def act(g,mask):return sum(1<<actions[g][j] for j in range(24) if mask>>j&1)
aug=[]
for source in range(len(inds)):
    cur=source;g=0
    while inds[cur]['mask'].bit_count()<10:
        edge=next(e for e in inds[cur]['extensions'] if e is not None and e[0]==0)
        _,nxt,h=edge;g=comp(g,h);cur=nxt
    assert cur>=3827
    assert act(g,inds[cur]['mask']) & inds[source]['mask']==inds[source]['mask']
    aug.append((cur-3827,g))
out=ROOT/'FourRow'/'CensusData';out.mkdir(exist_ok=True)
imports=[]
for b in range(41):
    start=32*b;chosen=inds[3827+start:3827+start+32];n=len(chosen)
    ns=f'Max{b:02}'
    s=f'''import FourRow.CensusTableData
import FourRow.Census
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FourRow.Census.{ns}
instance : Inhabited IndependentRecord := ⟨⟨0,![],![],1,![],![]⟩⟩
def records : LookupTree IndependentRecord :=
'''+tree(rec(r) for r in chosen)+f'''

def record (i : Fin {n}) : IndependentRecord := records.get i.val
def source (i : Fin {n}) : Fin 5109 := ⟨{3827+start}+i.val, by omega⟩
theorem checked : ∀ i : Fin {n}, (record i).Valid ∧
  (record i).support = independentSupport (source i) := by decide +kernel

theorem independent (i : Fin {n}) : IndependentSupport (independentSupport (source i)) := by
  intro x hx hs
  exact (record i).kernel_eq_zero (checked i).1 x hx (by simpa only [(checked i).2] using hs)
end FourRow.Census.{ns}
'''
    predecessor=f'FourRow.CensusData.Max{b-1:02}' if b else 'FourRow.CensusTables'
    write_serial(out/(ns+'.lean'),s,predecessor)
    imports.append(f'import FourRow.CensusData.{ns}')
# Independent-support augmentation is checked against literal actions.
s='\n'.join(imports)+'\nimport FourRow.CensusRelabel\nimport FourRow.CensusTables\nimport FourRow.CensusWitnessData'+'''
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FourRow.Census

def maxSource (k : Fin 1282) : Fin 5109 := ⟨3827 + k.val, by omega⟩

theorem maximal_independent (k : Fin 1282) : IndependentSupport (independentSupport (maxSource k)) := by
  have hb : k.val / 32 < 41 := by omega
  interval_cases h : k.val / 32
'''
for b in range(41):
    n=min(32,1282-32*b)
    s+=f'''  · have hi : k.val - {32*b} < {n} := by omega
    have heq : maxSource k = Max{b:02}.source ⟨k.val-{32*b},hi⟩ := by
      apply Fin.ext
      simp only [maxSource, Max{b:02}.source]
      omega
    rw [heq]
    exact Max{b:02}.independent _
'''
s+='def augmentationData : LookupTree (Fin 1282 × Fin 576) := '+tree(f'({k},{g})' for k,g in aug)+'''

def augmentation (i : Fin 5109) : Fin 1282 × Fin 576 := augmentationData.get i.val

def ValidAugmentation (i : Fin 5109) : Prop :=
  match augmentation i with
  | (k,g) =>
      independentMasks.get i.val &&&
        imageMask (literalAction g) (independentMasks.get (maxSource k).val) =
        independentMasks.get i.val

instance (i : Fin 5109) : Decidable (ValidAugmentation i) := by
  unfold ValidAugmentation
  cases augmentation i
  infer_instance
'''
for b in range(40):
    n=min(128,5109-128*b)
    s+=f'''
theorem augmentation_block_{b:02} : ∀ i : Fin {n},
  ValidAugmentation ⟨{128*b}+i.val, by omega⟩ := by decide +kernel
'''
s+='''
theorem augmentation_valid (i : Fin 5109) : ValidAugmentation i := by
  have hb : i.val / 128 < 40 := by omega
  interval_cases h : i.val / 128
'''
for b in range(40):
    n=min(128,5109-128*b)
    s+=f'''  · have hi : i.val - {128*b} < {n} := by omega
    have heq : i = (⟨{128*b} + (i.val-{128*b}),by omega⟩ : Fin 5109) := by
      apply Fin.ext
      simp only
      omega
    rw [heq]
    exact augmentation_block_{b:02} ⟨i.val-{128*b},hi⟩
'''
s+='''
theorem augmentation_checked (i : Fin 5109) :
    independentSupport i ⊆ (independentSupport (maxSource (augmentation i).1)).image
      (literalAction (augmentation i).2) := by
  have h := augmentation_valid i
  rcases he : augmentation i with ⟨k,g⟩
  have hh : independentMasks.get i.val &&&
      imageMask (literalAction g) (independentMasks.get (maxSource k).val) =
      independentMasks.get i.val := by
    simpa only [ValidAugmentation,he] using h
  have hs := maskSupport_subset_of_land_eq hh
  simpa only [maskSupport_imageMask,independentSupport,he] using hs

theorem all_independent (i : Fin 5109) : IndependentSupport (independentSupport i) := by
  apply independent_moved_subset (relabel (augmentation i).2) (maximal_independent (augmentation i).1)
  have hact : literalAction (augmentation i).2 =
      (action (relabel (augmentation i).2) : PermIndex → PermIndex) :=
    funext (literalAction_eq (augmentation i).2)
  simpa only [moved, actionHom_apply, ← hact] using augmentation_checked i
end FourRow.Census
'''
write_lean(ROOT/'FourRow/CensusIndependence.lean',s)
# Extension closure witnesses, with checked target dimensions.
for b in range(40):
    start=128*b;chosen=inds[start:start+128];n=len(chosen);ns=f'Extension{b:02}'
    es=[]
    for off,r in enumerate(chosen):
        row=[]
        for e in r['extensions']:
            kind,target,g=e if e is not None else (0,start+off,0)
            row.append(f'(Sum.in{ "l" if kind==0 else "r" } {target},{g})')
        es.append(vec(row))
    s=f'''import FourRow.CensusWitnessData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FourRow.Census.{ns}
def source (i : Fin {n}) : Fin 5109 := ⟨{start}+i.val, by omega⟩
def witnesses : LookupTree (PermIndex → ExtensionWitness) :=
'''+tree(es)+f'''

def witness (i : Fin {n}) (p : PermIndex) : ExtensionWitness := (witnesses.get i.val) p

theorem checked : ∀ i : Fin {n}, ∀ p : PermIndex,
  ValidExtension (source i) p (witness i p) := by decide +kernel
end FourRow.Census.{ns}
'''
    predecessor=(f'FourRow.CensusData.Extension{b-1:02}' if b
                 else 'FourRow.CensusIndependence')
    write_serial(out/(ns+'.lean'),s,predecessor)
print('Emitted 41 maximal-inverse modules, augmentation, and 40 extension modules.')
s='\n'.join(f'import FourRow.CensusData.Extension{b:02}' for b in range(40))+'''
import FourRow.CensusIndependence
import FourRow.CensusWitness
namespace FourRow.Census
set_option maxHeartbeats 0

theorem all_extensions (i : Fin 5109) (p : PermIndex) :
    (∃ g k, insert p (independentSupport i) = moved actionHom g (independentSupport k)) ∨
    (∃ g k, moved actionHom g (circuitSupport k) ⊆ insert p (independentSupport i)) := by
  have hb : i.val / 128 < 40 := by omega
  interval_cases h : i.val / 128
'''
for b in range(40):
    n=min(128,5109-128*b)
    s+=f'''  · have hi : i.val - {128*b} < {n} := by omega
    have heq : i = Extension{b:02}.source ⟨i.val-{128*b},hi⟩ := by
      apply Fin.ext
      simp only [Extension{b:02}.source]
      omega
    rw [heq]
    exact extension_of_witness _ (Extension{b:02}.checked _ p)
'''
s+='''
theorem empty_independent : independentSupport 0 = ∅ := by decide

theorem support_cover (x : PermIndex → ℝ) (hx : Kernel x) (hne : x ≠ 0) :
    ∃ k : Fin 73, ∃ g : Relabel,
      movedVector g (fun p => (primitive k p : ℝ)) ≠ 0 ∧
      Circuit.SupportedIn (movedVector g (fun p => (primitive k p : ℝ))) x := by
  classical
  let S : Finset PermIndex := Finset.univ.filter (fun p => x p ≠ 0)
  have cover := extension_coverage actionHom independentSupport circuitSupport
    ⟨0,empty_independent⟩ all_extensions S
  rcases cover with ⟨g,k,hS⟩ | ⟨g,k,hS⟩
  · exfalso
    have hind : IndependentSupport S := independent_moved_subset g (all_independent k)
      (by rw [hS])
    apply hne
    exact hind x hx (by simpa only [S,Finset.mem_filter,Finset.mem_univ,true_and,not_not] using
      (show ∀ p, x p = 0 → x p = 0 from fun _ h => h))
  · refine ⟨k,g,?_,?_⟩
    · obtain ⟨p,hp⟩ := primitive_nonzero k
      intro hz
      have hv := congrFun hz (action g p)
      simp only [movedVector, Equiv.symm_apply_apply, Pi.zero_apply] at hv
      exact hp (by exact_mod_cast hv)
    · intro p hp
      change (primitive k ((action g).symm p) : ℝ) = 0
      by_contra h
      have hn : primitive k ((action g).symm p) ≠ 0 := by exact_mod_cast h
      have hm : p ∈ moved actionHom g (circuitSupport k) := by
        apply Finset.mem_image.mpr
        exact ⟨(action g).symm p,(primitive_support k _).mpr hn,(action g).apply_symm_apply p⟩
      have hs := hS hm
      exact (Finset.mem_filter.mp hs).2 hp
end FourRow.Census
'''
write_lean(ROOT/'FourRow/CensusCoverage.lean',s)
