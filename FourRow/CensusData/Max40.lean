module

public import FourRow.CensusTableData
public import FourRow.Census

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FourRow.Census.Max40
instance : Inhabited IndependentRecord := ⟨⟨0,![],![],1,![],![]⟩⟩
def records : LookupTree IndependentRecord :=
(.node (.leaf ⟨10,![0,3,7,8,11,12,15,16,18,19],![0,1,2,3,4,5,6,8,9,10],4,![![1,-1,-2,-2,1,2,-1,2,1,1],![3,1,2,2,-1,-2,1,-2,-1,-1],![2,2,0,0,2,0,-2,0,-2,-2],![-3,-1,-2,-2,1,2,3,2,1,1],![1,3,2,2,-3,-2,-1,-2,1,1],![-2,-2,0,-4,2,0,2,0,2,2],![-1,1,2,2,-1,2,1,-2,-1,-1],![3,1,2,2,-1,-2,-3,2,-1,-1],![2,2,0,4,-2,0,-2,0,2,-2],![-2,-2,0,0,2,0,2,0,-2,2]],![![1,1,0,0,0,0,0,0,0,0],![0,0,1,1,1,0,0,0,0,0],![0,0,0,0,0,1,1,1,0,0],![0,0,0,0,0,0,0,0,1,1],![0,0,1,0,0,1,0,0,1,1],![1,0,0,0,0,0,1,0,0,0],![0,1,0,1,0,0,0,0,0,0],![0,0,0,1,0,0,0,1,0,0],![0,0,0,0,0,1,0,0,1,0],![1,0,0,0,1,0,0,0,0,1]]⟩) (.leaf ⟨10,![0,2,5,7,8,9,13,17,19,20],![0,1,2,3,4,5,6,8,9,10],3,![![-2,-1,-1,-3,1,3,1,0,1,2],![1,-1,-1,0,1,0,1,0,1,-1],![4,2,2,3,-2,-3,-2,0,-2,-1],![1,2,-1,0,1,0,-2,0,1,-1],![-2,-1,-1,-3,1,0,1,3,1,2],![1,2,2,3,-2,0,1,-3,-2,-1],![1,-1,2,0,1,0,1,0,-2,-1],![-1,1,1,0,-1,0,-1,0,2,1],![-2,-1,-1,0,1,0,1,0,1,2],![2,1,1,3,-1,0,-1,0,-1,-2]],![![1,1,1,0,0,0,0,0,0,0],![0,0,0,1,1,1,0,0,0,0],![0,0,0,0,0,0,1,1,0,0],![0,0,0,0,0,0,0,0,1,1],![0,0,0,1,0,0,1,0,1,0],![1,0,0,0,0,0,0,0,0,1],![0,1,0,0,1,1,0,0,0,0],![0,0,0,0,1,0,0,0,0,1],![0,1,0,0,0,0,0,1,0,0],![1,0,1,0,0,0,0,0,1,0]]⟩))

def record (i : Fin 2) : IndependentRecord := records.get i.val
def source (i : Fin 2) : Fin 5109 := ⟨5107+i.val, by omega⟩
theorem checked : ∀ i : Fin 2, (record i).Valid ∧
  (record i).support = independentSupport (source i) := by decide +kernel

theorem independent (i : Fin 2) : IndependentSupport (independentSupport (source i)) := by
  intro x hx hs
  exact (record i).kernel_eq_zero (checked i).1 x hx (by simpa only [(checked i).2] using hs)
end FourRow.Census.Max40
