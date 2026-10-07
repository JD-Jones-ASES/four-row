module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.EReal.Operations
public import Mathlib.LinearAlgebra.Matrix.Permanent
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Tactic

@[expose] public section

/-!
# Four-row robustness: standalone mathematical contract

Only Mathlib is imported. Probability laws and entries are real, entries are
nonnegative, and the total-variation balls are closed. No finite census,
certificate, rational-law, or endpoint theorem is an assumption. The theorem
holes are confined to this challenge; FourRowSolution supplies closed proofs.
Interior exponents and entropy coefficients are sufficient, not claimed optimal.
-/
namespace FourRow
noncomputable section

/-- The four row and column labels. -/
abbrev Row := Fin 4
/-- Permutations of the four labels. -/
abbrev Perm4 := Equiv.Perm Row
/-- A real row vector. -/
abbrev Vector := Fin 4 → ℝ
/-- A real weight on the permutation group. -/
abbrev Law := Perm4 → ℝ
/-- A four by four real matrix. -/
abbrev Rows := Matrix Row Row ℝ
/-- Uniform measure on the twenty-four permutations. -/
def uniformLaw : Law := fun _ => 1/24
/-- Nonnegative weights of total mass one. -/
structure Probability (ν : Law) : Prop where
  nonneg : ∀ σ, 0 ≤ ν σ
  mass : ∑ σ, ν σ = 1
/-- All sixteen coordinate marginals are uniform. -/
def Balanced (ν : Law) : Prop := ∀ i j : Row,
  ∑ σ : Perm4, (if σ i = j then ν σ else 0) = 1/4
/-- Total variation distance from uniform measure. -/
def tvDistance (ν : Law) : ℝ := (∑ σ : Perm4, |ν σ - uniformLaw σ|) / 2
/-- Balanced probability laws in the closed total-variation ball of radius r. -/
structure InBall (ν : Law) (r : ℝ) : Prop where
  probability : Probability ν
  balanced : Balanced ν
  distance : tvDistance ν ≤ r
/-- Expected product of the four selected matrix entries. -/
def expectation (ν : Law) (A : Rows) : ℝ := ∑ σ : Perm4, ν σ * ∏ i : Row, A i (σ i)
/-- Every entry is nonnegative; zero entries and rows are allowed. -/
def NonnegativeRows (A : Rows) : Prop := ∀ i j, 0 ≤ A i j
/-- Each row has probability-L² norm one under the uniform law on four columns. -/
def NormalizedRows (A : Rows) : Prop := ∀ i, (∑ j : Row, A i j ^ 2) / 4 = 1
/-- Sum of row variances when rows satisfy NormalizedRows. -/
def varianceSum (A : Rows) : ℝ := ∑ i : Row, (1 - ((∑ j : Row, A i j) / 4)^2)
/-- Uniform mean of four real numbers. -/
def meanFour (f : Vector) : ℝ := (∑ i : Fin 4, f i)/4
/-- Uniform p-th moment, used only for nonnegative rows and positive p. -/
def powerMoment (f : Vector) (p : ℝ) : ℝ := meanFour (fun i => f i ^ p)
/-- Probability-Lp norm under the uniform four-point measure. -/
def powerNorm (f : Vector) (p : ℝ) : ℝ := powerMoment f p ^ (1/p)
/-- The explicit sufficient exponent, ranging from 71/36 to two. -/
def explicitExponent (r : ℝ) : ℝ := 2-(1-24*r)/36
/-- Complete endpoint equality shapes: a zero row; constant rows; or rows
supported on a matching permutation having law mass 1/16. -/
def EndpointEqualityShape (ν : Law) (A : Rows) : Prop :=
  (∃ i : Row, ∀ j : Row, A i j = 0) ∨
  (∃ c : Row → ℝ, ∀ i j, A i j = c i) ∨
  (∃ τ : Perm4, ν τ = 1/16 ∧
    ∀ i j, A i j = if j = τ i then A i (τ i) else 0)
/-- Reference weights are positive wherever the first weights are positive. -/
def Supports {α : Type*} (p q : α → ℝ) : Prop := ∀ a, 0 < p a → 0 < q a
/-- Finite relative entropy with natural logarithms and 0 log 0 = 0.
Its real value is used when Supports holds. -/
def finiteKL {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  ∑ a, p a * Real.log (p a / q a)
/-- Relative entropy on all pairs of nonnegative laws; unsupported pairs have
value positive infinity. -/
def relativeEntropy {α : Type*} [Fintype α] (p q : α → ℝ) : EReal :=
  by classical exact if Supports p q then (finiteKL p q : EReal) else ⊤
/-- The image distribution of a specified row under a permutation law. -/
def marginal (ρ : Law) (i j : Row) : ℝ := ∑ σ : Perm4,
  if σ i = j then ρ σ else 0
/-- Sum of the four marginal relative entropies against uniform measure. -/
def marginalEntropySum (ρ : Law) : ℝ :=
  ∑ i : Row, finiteKL (marginal ρ i) (fun _ => 1/4)
/-- Joint law of an independent uniformly chosen row and its image. -/
def observationLaw (ρ : Law) : Row × Row → ℝ :=
  fun ij => marginal ρ ij.1 ij.2 / 4
/-- Matching singleton rows, normalized in probability L². -/
def sharpRows : Rows := fun i j => if i = j then 2 else 0

/-- Perturb uniform measure by one half of the identity atom, one half of
uniform measure on the nine derangements, minus uniform measure on the six
transpositions. In S₄ these classes have respectively four, zero, and two
fixed points. -/
def extremalLaw (r : ℝ) : Law := fun σ => 1/24 + r *
  (if (Finset.univ.filter (fun i : Row => σ i = i)).card = 4 then 1/2
   else if (Finset.univ.filter (fun i : Row => σ i = i)).card = 0 then 1/18
   else if (Finset.univ.filter (fun i : Row => σ i = i)).card = 2 then -1/6
   else 0)


/-- A finite history built by appending the most recent observation. -/
@[reducible] def History (α : Type) : ℕ → Type
  | 0 => Unit
  | n+1 => History α n × α

/-- Canonical finite enumeration of the recursive histories. -/
instance historyFintype {α : Type} [Fintype α] (n : ℕ) : Fintype (History α n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Fintype (History α n × α))

/-- The empty history is unique. -/
instance historyZeroUnique (α : Type) : Unique (History α 0) where
  default := ()
  uniq x := by cases x; rfl


/-- A complete permutation history. -/
abbrev PermHistory := History Perm4
/-- The history visible to one row. -/
abbrev RowHistory := History Row
/-- One-step laws indexed by time and the complete permutation past. -/
abbrev StepKernels := (n : ℕ) → PermHistory n → Law
/-- Joint path weights, permitting arbitrary history dependence. -/
def pathWeight (K : StepKernels) : (n : ℕ) → PermHistory n → ℝ
  | 0, _ => 1
  | n+1, h => pathWeight K n h.1 * K n h.1 h.2
/-- Projection of a permutation history onto a given row. -/
def rowHistory (i : Row) : (n : ℕ) → PermHistory n → RowHistory n
  | 0, _ => ()
  | n+1, h => (rowHistory i n h.1, h.2 i)
/-- Lp norm under uniform product measure on the 4^n row histories. -/
def historyNorm (n : ℕ) (F : RowHistory n → ℝ) (p : ℝ) : ℝ :=
  ((∑ x, F x^p)/(4:ℝ)^n)^(1/p)
/-- Only positive-probability full pasts must have their conditional law in
the balanced radius-r ball. No condition is imposed at null pasts. -/
def Admissible (K : StepKernels) (r : ℝ) (n : ℕ) : Prop :=
  ∀ t, t < n → ∀ h, 0 < pathWeight K t h → InBall (K t h) r

end
end FourRow

open FourRow
namespace FourRowPrincipal
noncomputable section
/-- The exact closed endpoint, without square roots and including zero rows. -/
theorem endpoint (ν : Law) (hν : InBall ν (1/24)) (A : Rows) (hA : NonnegativeRows A) :
    256*(expectation ν A)^2 ≤ ∏ i : Row, ∑ j : Row, A i j^2 := by sorry

/-- The sharp stability coefficient throughout the closed balanced ball. -/
theorem sharp_stability (ν : Law) (r : ℝ) (hr : 0 ≤ r) (hrmax : r ≤ 1/24)
    (hν : InBall ν r) (A : Rows) (hA : NonnegativeRows A) (hn : NormalizedRows A) :
    ((1-24*r)/9)*varianceSum A ≤ 1-expectation ν A := by sorry

/-- Every coefficient valid on the entire ball is at most the stated one. -/
theorem stability_optimal (r κ : ℝ) (hr : 0 ≤ r) (hrmax : r ≤ 1/24)
    (h : ∀ ν, InBall ν r → ∀ A, NonnegativeRows A → NormalizedRows A →
      κ*varianceSum A ≤ 1-expectation ν A) : κ ≤ (1-24*r)/9 := by sorry

/-- The explicit balanced family has exact TV distance and matching-row value. -/
theorem explicit_extremal_family (r : ℝ) (hr : 0 ≤ r) (hrmax : r ≤ 1/4) :
    InBall (extremalLaw r) r ∧ tvDistance (extremalLaw r) = r ∧
    NonnegativeRows sharpRows ∧ NormalizedRows sharpRows ∧ varianceSum sharpRows = 3 ∧
    expectation (extremalLaw r) sharpRows = 2/3+8*r := by sorry

/-- Every larger radius contains an actual balanced normalized counterexample. -/
theorem radius_sharp (r : ℝ) (hr : 1/24 < r) :
    ∃ ν : Law, ∃ A : Rows, InBall ν r ∧ NonnegativeRows A ∧ NormalizedRows A ∧
      1 < expectation ν A := by sorry

/-- All equality cases, including arbitrary nonnegative row scales and zero rows. -/
theorem endpoint_equality (ν : Law) (hν : InBall ν (1/24)) (A : Rows) (hA : NonnegativeRows A) :
    256*(expectation ν A)^2 = (∏ i : Row, ∑ j : Row, A i j^2) ↔
      EndpointEqualityShape ν A := by sorry

/-- The sufficient exponent p(r) for every nonnegative matrix. -/
theorem explicit_exponent (ν : Law) (r : ℝ) (hr : 0 ≤ r) (hrmax : r ≤ 1/24)
    (hν : InBall ν r) (A : Rows) (hA : NonnegativeRows A) :
    expectation ν A ≤ ∏ i : Row, powerNorm (A i) (explicitExponent r) := by sorry

/-- Every exponent at least p(r) also satisfies the row-product inequality. -/
theorem larger_exponents (ν : Law) (r : ℝ) (hr : 0 ≤ r) (hrmax : r ≤ 1/24) (hν : InBall ν r)
    (A : Rows) (hA : NonnegativeRows A) (p : ℝ) (hp : explicitExponent r ≤ p) :
    expectation ν A ≤ ∏ i : Row, powerNorm (A i) p := by sorry

/-- An exponent strictly below two works uniformly exactly at interior radii. -/
theorem subcritical_threshold (r : ℝ) (hr : 0 ≤ r) :
    (∃ p : ℝ, 1 ≤ p ∧ p < 2 ∧ ∀ ν, InBall ν r → ∀ A, NonnegativeRows A →
      expectation ν A ≤ ∏ i : Row, powerNorm (A i) p) ↔ r < 1/24 := by sorry

/-- The finite entropy inequality, including infinite relative-entropy cases. -/
theorem entropy (ν ρ : Law) (r : ℝ) (hr : 0 ≤ r) (hrmax : r ≤ 1/24)
    (hν : InBall ν r) (hρ : Probability ρ) :
    (marginalEntropySum ρ : EReal) ≤ (explicitExponent r : EReal)*relativeEntropy ρ ν := by sorry

/-- A uniformly sampled row/image observation contracts entropy by p(r)/4. -/
theorem observation_contraction (ν ρ : Law) (r : ℝ) (hr : 0 ≤ r) (hrmax : r ≤ 1/24)
    (hν : InBall ν r) (hρ : Probability ρ) :
    (finiteKL (observationLaw ρ) (observationLaw ν) : EReal) ≤
      ((explicitExponent r/4:ℝ):EReal)*relativeEntropy ρ ν := by sorry

/-- The endpoint entropy coefficient two is optimal over the balanced ball. -/
theorem entropy_optimal (κ : ℝ)
    (h : ∀ ν, InBall ν (1/24) → ∀ ρ, Probability ρ → Supports ρ ν →
      marginalEntropySum ρ ≤ κ*finiteKL ρ ν) : 2 ≤ κ := by sorry

/-- The endpoint observation coefficient one half is optimal over the ball. -/
theorem observation_optimal (κ : ℝ)
    (h : ∀ ν, InBall ν (1/24) → ∀ ρ, Probability ρ → Supports ρ ν →
      finiteKL (observationLaw ρ) (observationLaw ν) ≤ κ*finiteKL ρ ν) : 1/2 ≤ κ := by sorry

/-- The same exponent tensorizes under arbitrary full-history dependence. -/
theorem adaptive_tensorization (K : StepKernels) (r : ℝ) (hr : 0 ≤ r) (hrmax : r ≤ 1/24)
    (n : ℕ) (hK : Admissible K r n) (F : Row → RowHistory n → ℝ)
    (hF : ∀ i x, 0 ≤ F i x) :
    (∑ h : PermHistory n, pathWeight K n h*∏ i : Row, F i (rowHistory i n h)) ≤
      ∏ i : Row, historyNorm n (F i) (explicitExponent r) := by sorry

/-- Admissible adaptive kernels define a genuine probability law on paths. -/
theorem adaptive_probability (K : StepKernels) (r : ℝ) (n : ℕ) (hK : Admissible K r n) :
    (∀ h, 0 ≤ pathWeight K n h) ∧ (∑ h, pathWeight K n h) = 1 := by sorry

/-- Each individual row path is uniform product measure, even for adaptive kernels. -/
theorem adaptive_marginals (K : StepKernels) (r : ℝ) (n : ℕ) (hK : Admissible K r n)
    (i : Row) (F : RowHistory n → ℝ) :
    (∑ h : PermHistory n, pathWeight K n h*F (rowHistory i n h)) =
      (∑ x : RowHistory n, F x)/(4:ℝ)^n := by sorry

end
end FourRowPrincipal
