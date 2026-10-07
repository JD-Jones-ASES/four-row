module

public import FourRow.CensusTableData

@[expose] public section

namespace FourRow.Census

/-- Move a finite list of set bits through a map, combining them with bitwise OR. -/
def imageMaskAux (f : PermIndex → PermIndex) (m : ℕ) : List PermIndex → ℕ
  | [] => 0
  | p :: ps =>
      if m.testBit p.val then (2 ^ (f p).val) ||| imageMaskAux f m ps
      else imageMaskAux f m ps

theorem testBit_imageMaskAux (f : PermIndex → PermIndex) (m : ℕ)
    (ps : List PermIndex) (q : PermIndex) :
    (imageMaskAux f m ps).testBit q.val ↔
      ∃ p ∈ ps, m.testBit p.val ∧ f p = q := by
  induction ps with
  | nil => simp [imageMaskAux]
  | cons p ps ih =>
      by_cases hp : m.testBit p.val
      · simp [imageMaskAux, hp, Nat.testBit_two_pow, ih, Fin.val_inj,
          or_and_right, exists_or]
      · simp [imageMaskAux, hp, ih]

/-- Exact image of a 24-coordinate support mask under an arbitrary coordinate map. -/
def imageMask (f : PermIndex → PermIndex) (m : ℕ) : ℕ :=
  imageMaskAux f m (List.finRange 24)

theorem testBit_imageMask (f : PermIndex → PermIndex) (m : ℕ) (q : PermIndex) :
    (imageMask f m).testBit q.val ↔ ∃ p : PermIndex, m.testBit p.val ∧ f p = q := by
  simpa only [imageMask, List.mem_finRange, true_and] using
    testBit_imageMaskAux f m (List.finRange 24) q

theorem maskSupport_imageMask (f : PermIndex → PermIndex) (m : ℕ) :
    maskSupport (imageMask f m) = (maskSupport m).image f := by
  ext q
  simp only [maskSupport, Finset.mem_filter, Finset.mem_univ, true_and,
    testBit_imageMask, Finset.mem_image]

theorem maskSupport_insertBit (m : ℕ) (p : PermIndex) :
    maskSupport (m ||| 2 ^ p.val) = insert p (maskSupport m) := by
  ext q
  simp only [maskSupport, Finset.mem_filter, Finset.mem_univ, true_and,
    Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow, decide_eq_true_eq,
    Finset.mem_insert, Fin.ext_iff]
  exact or_comm.trans (or_congr eq_comm Iff.rfl)

theorem maskSupport_subset_of_land_eq {m n : ℕ} (h : m &&& n = m) :
    maskSupport m ⊆ maskSupport n := by
  intro p hp
  have hb : m.testBit p.val = true := by simpa [maskSupport] using hp
  have hh := congrArg (fun x : ℕ => x.testBit p.val) h
  have hn : n.testBit p.val = true := by simpa [hb] using hh
  simpa [maskSupport] using hn

end FourRow.Census
