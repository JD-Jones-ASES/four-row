module

public import FourRow.Relabel
public import FourRow.GramData

@[expose] public section

namespace FourRow
noncomputable section

private theorem sum_four_reindex (g : Relabel) (f : Row → Row → Row → Row → ℝ) :
    (∑ i : Row, ∑ j : Row, ∑ k : Row, ∑ l : Row,
      f (g.1 i) (g.1 j) (g.2 k) (g.2 l)) =
      ∑ i : Row, ∑ j : Row, ∑ k : Row, ∑ l : Row, f i j k l := by
  calc
    _ = ∑ i : Row, ∑ j : Row, ∑ k : Row, ∑ l : Row, f (g.1 i) (g.1 j) (g.2 k) l := by
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      apply Finset.sum_congr rfl; intro k _
      exact Equiv.sum_comp g.2 (fun l => f (g.1 i) (g.1 j) (g.2 k) l)
    _ = ∑ i : Row, ∑ j : Row, ∑ k : Row, ∑ l : Row, f (g.1 i) (g.1 j) k l := by
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      exact Equiv.sum_comp g.2 (fun k => ∑ l : Row, f (g.1 i) (g.1 j) k l)
    _ = ∑ i : Row, ∑ j : Row, ∑ k : Row, ∑ l : Row, f (g.1 i) j k l := by
      apply Finset.sum_congr rfl; intro i _
      exact Equiv.sum_comp g.1 (fun j => ∑ k : Row, ∑ l : Row, f (g.1 i) j k l)
    _ = _ := Equiv.sum_comp g.1 (fun i => ∑ j : Row, ∑ k : Row, ∑ l : Row, f i j k l)

/-- The strict product defect is invariant under every allowed row/column
relabeling; equality indicators remove only identical-coordinate products. -/
theorem defect_relabel (g : Relabel) (A : Rows) :
    defect (flat (relabelRows g A)) = defect (flat A) := by
  simp only [defect, flat_cell, relabelRows]
  have h := sum_four_reindex g (fun i j k l =>
    ((if k = l then 0 else (A i k * A i l - A j k * A j l)^2) +
    (if i = j then 0 else (A i k * A j k - A i l * A j l)^2)))
  simpa only [Equiv.apply_eq_iff_eq] using h

end
end FourRow
