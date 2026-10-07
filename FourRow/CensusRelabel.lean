module

public import FourRow.Census
public import FourRow.Relabel

@[expose] public section
namespace FourRow.Census
theorem independent_moved_subset {S T : Finset PermIndex} (g : Relabel)
    (hT : IndependentSupport T) (hST : S ⊆ moved actionHom g T) : IndependentSupport S := by
  intro x hx hs
  let z : PermIndex → ℝ := fun p => x (action g p)
  have hz : Kernel z := by
    have h := kernel_movedVector g⁻¹ hx
    change Kernel (fun p => x ((action g⁻¹).symm p)) at h
    have hg : action g⁻¹ = (action g)⁻¹ := map_inv actionHom g
    rw [hg] at h
    exact h
  have hzero : z = 0 := hT z hz (by
    intro p hp
    apply hs
    intro hpx
    have hm := hST hpx
    rcases Finset.mem_image.mp hm with ⟨q,hq,heq⟩
    have heq' : q = p := (action g).injective heq
    exact hp (heq' ▸ hq))
  funext p
  have h := congrFun hzero ((action g).symm p)
  simpa [z] using h

end FourRow.Census
