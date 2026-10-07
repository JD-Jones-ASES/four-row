module

public import FourRow.Exponent

@[expose] public section

/-! Adaptive tensorization. Kernels may depend on the complete permutation
history. Conditions are imposed only on positive-probability histories. -/
namespace FourRow
noncomputable section

/-- A finite history built by appending the most recent observation. -/
@[reducible] def History (α : Type) : ℕ → Type
  | 0 => Unit
  | n+1 => History α n × α

instance historyFintype {α : Type} [Fintype α] (n : ℕ) : Fintype (History α n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Fintype (History α n × α))

instance historyZeroUnique (α : Type) : Unique (History α 0) where
  default := ()
  uniq x := by cases x; rfl

theorem history_card {α : Type} [Fintype α] (n : ℕ) :
    Fintype.card (History α n) = Fintype.card α ^ n := by
  induction n with
  | zero => simp [History]
  | succ n ih =>
    change Fintype.card (History α n × α) = Fintype.card α ^ (n+1)
    rw [Fintype.card_prod,ih,pow_succ]

abbrev PermHistory := History Perm4
abbrev RowHistory := History Row
abbrev StepKernels := (n : ℕ) → PermHistory n → Law

/-- Probability weight from arbitrary history-dependent one-step kernels. -/
def pathWeight (K : StepKernels) : (n : ℕ) → PermHistory n → ℝ
  | 0, _ => 1
  | n+1, h => pathWeight K n h.1 * K n h.1 h.2

/-- The path seen by a single row. -/
def rowHistory (i : Row) : (n : ℕ) → PermHistory n → RowHistory n
  | 0, _ => ()
  | n+1, h => (rowHistory i n h.1, h.2 i)

/-- Probability Lp norm under uniform product measure on n row observations. -/
def historyNorm (n : ℕ) (F : RowHistory n → ℝ) (p : ℝ) : ℝ :=
  ((∑ x, F x^p)/((4 : ℕ) : ℝ)^n)^(1/p)

/-- Admissibility only at positive-probability full pasts. -/
def Admissible (K : StepKernels) (r : ℝ) (n : ℕ) : Prop :=
  ∀ t, t < n → ∀ h, 0 < pathWeight K t h → InBall (K t h) r

/-- Generic one-step hypotheses for the reusable tensorization argument. -/
def AdaptivePowerBound (K : StepKernels) (p : ℝ) (n : ℕ) : Prop :=
  ∀ t, t < n → ∀ h, 0 < pathWeight K t h →
    Probability (K t h) ∧ ∀ A : Rows, NonnegativeRows A →
      expectation (K t h) A ≤ ∏ i, powerNorm (A i) p

theorem pathWeight_nonneg (K : StepKernels) (n : ℕ)
    (hK : ∀ t, t < n → ∀ h, 0 < pathWeight K t h → Probability (K t h)) :
    ∀ h, 0 ≤ pathWeight K n h := by
  induction n with
  | zero => intro h; norm_num [pathWeight]
  | succ n ih =>
    have hprev := ih (fun t ht h hh => hK t (Nat.lt_trans ht (Nat.lt_succ_self n)) h hh)
    intro h
    have hp := hprev h.1
    by_cases hz : pathWeight K n h.1 = 0
    · simp [pathWeight,hz]
    · exact mul_nonneg hp ((hK n (Nat.lt_succ_self n) h.1
        (lt_of_le_of_ne hp (Ne.symm hz))).nonneg h.2)

/-- The induced history weights sum to one, including kernels unspecified at null pasts. -/
theorem pathWeight_mass (K : StepKernels) (n : ℕ)
    (hK : ∀ t, t < n → ∀ h, 0 < pathWeight K t h → Probability (K t h)) :
    ∑ h, pathWeight K n h = 1 := by
  induction n with
  | zero => simp [pathWeight]
  | succ n ih =>
    have hrestriction := fun t ht h hh => hK t (Nat.lt_trans ht (Nat.lt_succ_self n)) h hh
    have hprev := pathWeight_nonneg K n hrestriction
    change (∑ h : PermHistory n × Perm4, pathWeight K n h.1*K n h.1 h.2) = 1
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum]
    have hstep (h : PermHistory n) : pathWeight K n h*(∑ σ, K n h σ) = pathWeight K n h := by
      by_cases hz : pathWeight K n h = 0
      · simp [hz]
      · rw [(hK n (Nat.lt_succ_self n) h (lt_of_le_of_ne (hprev h) (Ne.symm hz))).mass,mul_one]
    simp_rw [hstep]
    exact ih hrestriction

/-- Taking the last-coordinate norm commutes with the full product norm. -/
theorem historyNorm_step (n : ℕ) (F : RowHistory (n+1) → ℝ)
    (hF : ∀ x, 0 ≤ F x) (p : ℝ) (hp : 0 < p) :
    historyNorm n (fun x => powerNorm (fun j => F (x,j)) p) p = historyNorm (n+1) F p := by
  have he (x : RowHistory n) : powerNorm (fun j => F (x,j)) p ^ p =
      (∑ j : Row, F (x,j)^p)/4 := by
    rw [powerNorm,← Real.rpow_mul (powerMoment_nonneg _ (fun j => hF (x,j)) p),
      one_div_mul_cancel (ne_of_gt hp),Real.rpow_one]
    rfl
  simp only [historyNorm,he]
  change ((∑ x : RowHistory n, (∑ j : Row, F (x,j)^p)/4)/(4:ℝ)^n)^(1/p) =
    ((∑ x : RowHistory n × Row, F x^p)/(4:ℝ)^(n+1))^(1/p)
  rw [Fintype.sum_prod_type,← Finset.sum_div,pow_succ]
  congr 1
  ring

/-- Generic adaptive tensorization of the finite four-row Lp inequality. -/
theorem adaptive_tensorization (K : StepKernels) (p : ℝ) (hp : 0 < p)
    (n : ℕ) (hK : AdaptivePowerBound K p n)
    (F : Row → RowHistory n → ℝ) (hF : ∀ i x, 0 ≤ F i x) :
    (∑ h : PermHistory n, pathWeight K n h * ∏ i : Row, F i (rowHistory i n h)) ≤
      ∏ i : Row, historyNorm n (F i) p := by
  induction n with
  | zero =>
    have hnorm (i : Row) : historyNorm 0 (F i) p = F i () := by
      simp only [historyNorm,pow_zero,div_one]
      rw [Fintype.sum_unique]
      change ((F i ())^p)^(1/p) = F i ()
      rw [← Real.rpow_mul (hF i ()),mul_one_div_cancel (ne_of_gt hp),Real.rpow_one]
    simp only [pathWeight,rowHistory,one_mul,hnorm]
    change (∑ _ : Unit, ∏ i, F i ()) ≤ ∏ i, F i ()
    simp
  | succ n ih =>
    have hrestriction : AdaptivePowerBound K p n :=
      fun t ht h hh => hK t (Nat.lt_trans ht (Nat.lt_succ_self n)) h hh
    have hprev := pathWeight_nonneg K n (fun t ht h hh => (hrestriction t ht h hh).1)
    let G : Row → RowHistory n → ℝ := fun i x => powerNorm (fun j => F i (x,j)) p
    have hG : ∀ i x, 0 ≤ G i x := fun i x => powerNorm_nonneg _ (fun j => hF i (x,j)) p
    have hdrop (h : PermHistory n) :
        pathWeight K n h * (∑ σ : Perm4, K n h σ *
          ∏ i : Row, F i (rowHistory i n h,σ i)) ≤
        pathWeight K n h * ∏ i : Row, G i (rowHistory i n h) := by
      by_cases hz : pathWeight K n h = 0
      · simp [hz]
      · apply mul_le_mul_of_nonneg_left _ (hprev h)
        exact (hK n (Nat.lt_succ_self n) h (lt_of_le_of_ne (hprev h) (Ne.symm hz))).2
          (fun i j => F i (rowHistory i n h,j)) (fun i j => hF i _)
    have hfirst := Finset.sum_le_sum (s := Finset.univ) (fun h _ => hdrop h)
    have hsecond := ih hrestriction G hG
    have hn (i : Row) : historyNorm n (G i) p = historyNorm (n+1) (F i) p :=
      historyNorm_step n (F i) (hF i) p hp
    simp_rw [hn] at hsecond
    apply le_trans ?_ hsecond
    change (∑ h : PermHistory n × Perm4,
      (pathWeight K n h.1*K n h.1 h.2)*∏ i : Row, F i (rowHistory i n h.1,h.2 i)) ≤ _
    rw [Fintype.sum_prod_type]
    simp only [mul_assoc,← Finset.mul_sum]
    exact hfirst

/-- The explicit p(r) inequality on arbitrary adaptive permutation histories. -/
theorem explicitExponent_tensorization (hEndpoint : EndpointBound)
    (K : StepKernels) (r : ℝ) (hr : 0 ≤ r) (hrmax : r ≤ 1/24)
    (n : ℕ) (hK : Admissible K r n)
    (F : Row → RowHistory n → ℝ) (hF : ∀ i x, 0 ≤ F i x) :
    (∑ h : PermHistory n, pathWeight K n h * ∏ i : Row, F i (rowHistory i n h)) ≤
      ∏ i : Row, historyNorm n (F i) (explicitExponent r) := by
  have hp : 0 < explicitExponent r := by dsimp [explicitExponent]; linarith only [hr]
  apply adaptive_tensorization K _ hp n ?_ F hF
  intro t ht h hh
  exact ⟨(hK t ht h hh).probability,
    fun A hA => explicitExponent_bound hEndpoint (K t h) r hr hrmax (hK t ht h hh) A hA⟩

/-- Conditional balance makes each single-row history uniform product measure. -/
theorem rowHistory_expectation (K : StepKernels) (r : ℝ) (n : ℕ)
    (hK : Admissible K r n) (i : Row) (F : RowHistory n → ℝ) :
    (∑ h : PermHistory n, pathWeight K n h*F (rowHistory i n h)) =
      (∑ x : RowHistory n, F x)/(4:ℝ)^n := by
  induction n with
  | zero =>
    simp only [pathWeight,rowHistory,one_mul,pow_zero,div_one]
  | succ n ih =>
    have hrestriction : Admissible K r n :=
      fun t ht h hh => hK t (Nat.lt_trans ht (Nat.lt_succ_self n)) h hh
    have hprev := pathWeight_nonneg K n
      (fun t ht h hh => (hrestriction t ht h hh).probability)
    let G : RowHistory n → ℝ := fun x => (∑ j : Row, F (x,j))/4
    have hstep (h : PermHistory n) :
        pathWeight K n h*(∑ σ : Perm4, K n h σ*F (rowHistory i n h,σ i)) =
        pathWeight K n h*G (rowHistory i n h) := by
      by_cases hz : pathWeight K n h = 0
      · simp [hz]
      · have hb := (hK n (Nat.lt_succ_self n) h
          (lt_of_le_of_ne (hprev h) (Ne.symm hz))).balanced
        rw [marginal_sum (K n h) i (fun j => F (rowHistory i n h,j))]
        have hm (j : Row) : marginal (K n h) i j = 1/4 := hb i j
        simp_rw [hm]
        rw [← Finset.mul_sum]
        dsimp [G]
        ring
    change (∑ h : PermHistory n × Perm4,
      (pathWeight K n h.1*K n h.1 h.2)*F (rowHistory i n h.1,h.2 i)) = _
    rw [Fintype.sum_prod_type]
    simp only [mul_assoc,← Finset.mul_sum]
    simp_rw [hstep]
    rw [ih hrestriction G]
    change ((∑ x : RowHistory n, (∑ j : Row, F (x,j))/4)/(4:ℝ)^n) =
      (∑ x : RowHistory n × Row, F x)/(4:ℝ)^(n+1)
    rw [Fintype.sum_prod_type,← Finset.sum_div,pow_succ]
    ring

end
end FourRow
