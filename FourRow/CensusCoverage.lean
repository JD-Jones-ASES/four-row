module

public import FourRow.CensusData.Extension00
public import FourRow.CensusData.Extension01
public import FourRow.CensusData.Extension02
public import FourRow.CensusData.Extension03
public import FourRow.CensusData.Extension04
public import FourRow.CensusData.Extension05
public import FourRow.CensusData.Extension06
public import FourRow.CensusData.Extension07
public import FourRow.CensusData.Extension08
public import FourRow.CensusData.Extension09
public import FourRow.CensusData.Extension10
public import FourRow.CensusData.Extension11
public import FourRow.CensusData.Extension12
public import FourRow.CensusData.Extension13
public import FourRow.CensusData.Extension14
public import FourRow.CensusData.Extension15
public import FourRow.CensusData.Extension16
public import FourRow.CensusData.Extension17
public import FourRow.CensusData.Extension18
public import FourRow.CensusData.Extension19
public import FourRow.CensusData.Extension20
public import FourRow.CensusData.Extension21
public import FourRow.CensusData.Extension22
public import FourRow.CensusData.Extension23
public import FourRow.CensusData.Extension24
public import FourRow.CensusData.Extension25
public import FourRow.CensusData.Extension26
public import FourRow.CensusData.Extension27
public import FourRow.CensusData.Extension28
public import FourRow.CensusData.Extension29
public import FourRow.CensusData.Extension30
public import FourRow.CensusData.Extension31
public import FourRow.CensusData.Extension32
public import FourRow.CensusData.Extension33
public import FourRow.CensusData.Extension34
public import FourRow.CensusData.Extension35
public import FourRow.CensusData.Extension36
public import FourRow.CensusData.Extension37
public import FourRow.CensusData.Extension38
public import FourRow.CensusData.Extension39
public import FourRow.CensusIndependence
public import FourRow.CensusWitness

@[expose] public section
namespace FourRow.Census
set_option maxHeartbeats 0

theorem all_extensions (i : Fin 5109) (p : PermIndex) :
    (∃ g k, insert p (independentSupport i) = moved actionHom g (independentSupport k)) ∨
    (∃ g k, moved actionHom g (circuitSupport k) ⊆ insert p (independentSupport i)) := by
  have hb : i.val / 128 < 40 := by omega
  interval_cases h : i.val / 128
  · have hi : i.val - 0 < 128 := by omega
    have heq : i = Extension00.source ⟨i.val-0,hi⟩ := by
      apply Fin.ext
      simp only [Extension00.source]
      omega
    rw [heq]
    exact extension_of_witness _ (Extension00.checked _ p)
  · have hi : i.val - 128 < 128 := by omega
    have heq : i = Extension01.source ⟨i.val-128,hi⟩ := by
      apply Fin.ext
      simp only [Extension01.source]
      omega
    rw [heq]
    exact extension_of_witness _ (Extension01.checked _ p)
  · have hi : i.val - 256 < 128 := by omega
    have heq : i = Extension02.source ⟨i.val-256,hi⟩ := by
      apply Fin.ext
      simp only [Extension02.source]
      omega
    rw [heq]
    exact extension_of_witness _ (Extension02.checked _ p)
  · have hi : i.val - 384 < 128 := by omega
    have heq : i = Extension03.source ⟨i.val-384,hi⟩ := by
      apply Fin.ext
      simp only [Extension03.source]
      omega
    rw [heq]
    exact extension_of_witness _ (Extension03.checked _ p)
  · have hi : i.val - 512 < 128 := by omega
    have heq : i = Extension04.source ⟨i.val-512,hi⟩ := by
      apply Fin.ext
      simp only [Extension04.source]
      omega
    rw [heq]
    exact extension_of_witness _ (Extension04.checked _ p)
  · have hi : i.val - 640 < 128 := by omega
    have heq : i = Extension05.source ⟨i.val-640,hi⟩ := by
      apply Fin.ext
      simp only [Extension05.source]
      omega
    rw [heq]
    exact extension_of_witness _ (Extension05.checked _ p)
  · have hi : i.val - 768 < 128 := by omega
    have heq : i = Extension06.source ⟨i.val-768,hi⟩ := by
      apply Fin.ext
      simp only [Extension06.source]
      omega
    rw [heq]
    exact extension_of_witness _ (Extension06.checked _ p)
  · have hi : i.val - 896 < 128 := by omega
    have heq : i = Extension07.source ⟨i.val-896,hi⟩ := by
      apply Fin.ext
      simp only [Extension07.source]
      omega
    rw [heq]
    exact extension_of_witness _ (Extension07.checked _ p)
  · have hi : i.val - 1024 < 128 := by omega
    have heq : i = Extension08.source ⟨i.val-1024,hi⟩ := by
      apply Fin.ext
      simp only [Extension08.source]
      omega
    rw [heq]
    exact extension_of_witness _ (Extension08.checked _ p)
  · have hi : i.val - 1152 < 128 := by omega
    have heq : i = Extension09.source ⟨i.val-1152,hi⟩ := by
      apply Fin.ext
      simp only [Extension09.source]
      omega
    rw [heq]
    exact extension_of_witness _ (Extension09.checked _ p)
  · have hi : i.val - 1280 < 128 := by omega
    have heq : i = Extension10.source ⟨i.val-1280,hi⟩ := by
      apply Fin.ext
      simp only [Extension10.source]
      omega
    rw [heq]
    exact extension_of_witness _ (Extension10.checked _ p)
  · have hi : i.val - 1408 < 128 := by omega
    have heq : i = Extension11.source ⟨i.val-1408,hi⟩ := by
      apply Fin.ext
      simp only [Extension11.source]
      omega
    rw [heq]
    exact extension_of_witness _ (Extension11.checked _ p)
  · have hi : i.val - 1536 < 128 := by omega
    have heq : i = Extension12.source ⟨i.val-1536,hi⟩ := by
      apply Fin.ext
      simp only [Extension12.source]
      omega
    rw [heq]
    exact extension_of_witness _ (Extension12.checked _ p)
  · have hi : i.val - 1664 < 128 := by omega
    have heq : i = Extension13.source ⟨i.val-1664,hi⟩ := by
      apply Fin.ext
      simp only [Extension13.source]
      omega
    rw [heq]
    exact extension_of_witness _ (Extension13.checked _ p)
  · have hi : i.val - 1792 < 128 := by omega
    have heq : i = Extension14.source ⟨i.val-1792,hi⟩ := by
      apply Fin.ext
      simp only [Extension14.source]
      omega
    rw [heq]
    exact extension_of_witness _ (Extension14.checked _ p)
  · have hi : i.val - 1920 < 128 := by omega
    have heq : i = Extension15.source ⟨i.val-1920,hi⟩ := by
      apply Fin.ext
      simp only [Extension15.source]
      omega
    rw [heq]
    exact extension_of_witness _ (Extension15.checked _ p)
  · have hi : i.val - 2048 < 128 := by omega
    have heq : i = Extension16.source ⟨i.val-2048,hi⟩ := by
      apply Fin.ext
      simp only [Extension16.source]
      omega
    rw [heq]
    exact extension_of_witness _ (Extension16.checked _ p)
  · have hi : i.val - 2176 < 128 := by omega
    have heq : i = Extension17.source ⟨i.val-2176,hi⟩ := by
      apply Fin.ext
      simp only [Extension17.source]
      omega
    rw [heq]
    exact extension_of_witness _ (Extension17.checked _ p)
  · have hi : i.val - 2304 < 128 := by omega
    have heq : i = Extension18.source ⟨i.val-2304,hi⟩ := by
      apply Fin.ext
      simp only [Extension18.source]
      omega
    rw [heq]
    exact extension_of_witness _ (Extension18.checked _ p)
  · have hi : i.val - 2432 < 128 := by omega
    have heq : i = Extension19.source ⟨i.val-2432,hi⟩ := by
      apply Fin.ext
      simp only [Extension19.source]
      omega
    rw [heq]
    exact extension_of_witness _ (Extension19.checked _ p)
  · have hi : i.val - 2560 < 128 := by omega
    have heq : i = Extension20.source ⟨i.val-2560,hi⟩ := by
      apply Fin.ext
      simp only [Extension20.source]
      omega
    rw [heq]
    exact extension_of_witness _ (Extension20.checked _ p)
  · have hi : i.val - 2688 < 128 := by omega
    have heq : i = Extension21.source ⟨i.val-2688,hi⟩ := by
      apply Fin.ext
      simp only [Extension21.source]
      omega
    rw [heq]
    exact extension_of_witness _ (Extension21.checked _ p)
  · have hi : i.val - 2816 < 128 := by omega
    have heq : i = Extension22.source ⟨i.val-2816,hi⟩ := by
      apply Fin.ext
      simp only [Extension22.source]
      omega
    rw [heq]
    exact extension_of_witness _ (Extension22.checked _ p)
  · have hi : i.val - 2944 < 128 := by omega
    have heq : i = Extension23.source ⟨i.val-2944,hi⟩ := by
      apply Fin.ext
      simp only [Extension23.source]
      omega
    rw [heq]
    exact extension_of_witness _ (Extension23.checked _ p)
  · have hi : i.val - 3072 < 128 := by omega
    have heq : i = Extension24.source ⟨i.val-3072,hi⟩ := by
      apply Fin.ext
      simp only [Extension24.source]
      omega
    rw [heq]
    exact extension_of_witness _ (Extension24.checked _ p)
  · have hi : i.val - 3200 < 128 := by omega
    have heq : i = Extension25.source ⟨i.val-3200,hi⟩ := by
      apply Fin.ext
      simp only [Extension25.source]
      omega
    rw [heq]
    exact extension_of_witness _ (Extension25.checked _ p)
  · have hi : i.val - 3328 < 128 := by omega
    have heq : i = Extension26.source ⟨i.val-3328,hi⟩ := by
      apply Fin.ext
      simp only [Extension26.source]
      omega
    rw [heq]
    exact extension_of_witness _ (Extension26.checked _ p)
  · have hi : i.val - 3456 < 128 := by omega
    have heq : i = Extension27.source ⟨i.val-3456,hi⟩ := by
      apply Fin.ext
      simp only [Extension27.source]
      omega
    rw [heq]
    exact extension_of_witness _ (Extension27.checked _ p)
  · have hi : i.val - 3584 < 128 := by omega
    have heq : i = Extension28.source ⟨i.val-3584,hi⟩ := by
      apply Fin.ext
      simp only [Extension28.source]
      omega
    rw [heq]
    exact extension_of_witness _ (Extension28.checked _ p)
  · have hi : i.val - 3712 < 128 := by omega
    have heq : i = Extension29.source ⟨i.val-3712,hi⟩ := by
      apply Fin.ext
      simp only [Extension29.source]
      omega
    rw [heq]
    exact extension_of_witness _ (Extension29.checked _ p)
  · have hi : i.val - 3840 < 128 := by omega
    have heq : i = Extension30.source ⟨i.val-3840,hi⟩ := by
      apply Fin.ext
      simp only [Extension30.source]
      omega
    rw [heq]
    exact extension_of_witness _ (Extension30.checked _ p)
  · have hi : i.val - 3968 < 128 := by omega
    have heq : i = Extension31.source ⟨i.val-3968,hi⟩ := by
      apply Fin.ext
      simp only [Extension31.source]
      omega
    rw [heq]
    exact extension_of_witness _ (Extension31.checked _ p)
  · have hi : i.val - 4096 < 128 := by omega
    have heq : i = Extension32.source ⟨i.val-4096,hi⟩ := by
      apply Fin.ext
      simp only [Extension32.source]
      omega
    rw [heq]
    exact extension_of_witness _ (Extension32.checked _ p)
  · have hi : i.val - 4224 < 128 := by omega
    have heq : i = Extension33.source ⟨i.val-4224,hi⟩ := by
      apply Fin.ext
      simp only [Extension33.source]
      omega
    rw [heq]
    exact extension_of_witness _ (Extension33.checked _ p)
  · have hi : i.val - 4352 < 128 := by omega
    have heq : i = Extension34.source ⟨i.val-4352,hi⟩ := by
      apply Fin.ext
      simp only [Extension34.source]
      omega
    rw [heq]
    exact extension_of_witness _ (Extension34.checked _ p)
  · have hi : i.val - 4480 < 128 := by omega
    have heq : i = Extension35.source ⟨i.val-4480,hi⟩ := by
      apply Fin.ext
      simp only [Extension35.source]
      omega
    rw [heq]
    exact extension_of_witness _ (Extension35.checked _ p)
  · have hi : i.val - 4608 < 128 := by omega
    have heq : i = Extension36.source ⟨i.val-4608,hi⟩ := by
      apply Fin.ext
      simp only [Extension36.source]
      omega
    rw [heq]
    exact extension_of_witness _ (Extension36.checked _ p)
  · have hi : i.val - 4736 < 128 := by omega
    have heq : i = Extension37.source ⟨i.val-4736,hi⟩ := by
      apply Fin.ext
      simp only [Extension37.source]
      omega
    rw [heq]
    exact extension_of_witness _ (Extension37.checked _ p)
  · have hi : i.val - 4864 < 128 := by omega
    have heq : i = Extension38.source ⟨i.val-4864,hi⟩ := by
      apply Fin.ext
      simp only [Extension38.source]
      omega
    rw [heq]
    exact extension_of_witness _ (Extension38.checked _ p)
  · have hi : i.val - 4992 < 117 := by omega
    have heq : i = Extension39.source ⟨i.val-4992,hi⟩ := by
      apply Fin.ext
      simp only [Extension39.source]
      omega
    rw [heq]
    exact extension_of_witness _ (Extension39.checked _ p)

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
