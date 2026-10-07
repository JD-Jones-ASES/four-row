import Mathlib

/-!
# Uniform four-row stability

An algebraic proof of the quantitative uniform permanent bound, independent
of the endpoint certificates.  Rows use Euclidean normalization.
-/

namespace FourRow

noncomputable section

abbrev Vector := Fin 4 → ℝ

/-- Four-coordinate sum, kept explicit for transparent polynomial identities. -/
def sumFour (v : Vector) : ℝ := v 0 + v 1 + v 2 + v 3

def rowSquare (v : Vector) : ℝ := sumFour (fun i => v i ^ 2)
def rowDot (v w : Vector) : ℝ := sumFour (fun i => v i * w i)
def rowOverlap (v w : Vector) : ℝ := sumFour (fun i => v i ^ 2 * w i ^ 2)
def rowPairs (v : Vector) : ℝ :=
  v 0 * v 1 + v 0 * v 2 + v 0 * v 3 + v 1 * v 2 + v 1 * v 3 + v 2 * v 3

def rowDeficit (v : Vector) : ℝ := 1 - (sumFour v) ^ 2 / 4

def pairDefect (v w : Vector) : ℝ :=
  (1 + 4 * rowOverlap v w - 2 * rowDot v w ^ 2) / 2

/-- Explicit quartic sum of squares from the research proof. -/
theorem scalarQuartic_nonneg (a b c d : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    0 ≤ 12 * (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) +
      (a+b+c+d)^2 * (a^2+b^2+c^2+d^2) - 7*(a^2+b^2+c^2+d^2)^2 := by
  let p := a+b+c+d
  let s := a^2+b^2+c^2+d^2
  have hid :
      12 * (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) +
        (a+b+c+d)^2 * (a^2+b^2+c^2+d^2) - 7*(a^2+b^2+c^2+d^2)^2 =
      6*(a*b*(a-b)^2+a*c*(a-c)^2+a*d*(a-d)^2+
        b*c*(b-c)^2+b*d*(b-d)^2+c*d*(c-d)^2) +
      2*((p*a-3*a^2-(p^2-3*s)/4)^2+(p*b-3*b^2-(p^2-3*s)/4)^2+
         (p*c-3*c^2-(p^2-3*s)/4)^2+(p*d-3*d^2-(p^2-3*s)/4)^2) +
      ((a*b+c*d)-(a*c+b*d))^2 + ((a*b+c*d)-(a*d+b*c))^2 +
      ((a*c+b*d)-(a*d+b*c))^2 := by dsimp [p,s]; ring
  rw [hid]
  positivity

/-- Homogeneous form avoids dividing by the inner product in the pair estimate. -/
theorem scalarQuartic_pairs (z : Vector) (hz : ∀ i, 0 ≤ z i) :
    0 ≤ 12 * sumFour (fun i => z i ^ 4) - 6 * rowSquare z ^ 2 +
      2 * rowSquare z * rowPairs z := by
  have h := scalarQuartic_nonneg (z 0) (z 1) (z 2) (z 3)
    (hz 0) (hz 1) (hz 2) (hz 3)
  dsimp [sumFour, rowSquare, rowPairs]
  nlinarith only [h]

private theorem nonneg_amgm (a b s : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (_hs : 0 ≤ s) (h : s^2 = a*b) : 2*s ≤ a+b := by
  nlinarith [sq_nonneg (a-b)]

/-- The elementary pair bound underlying the uniform deficit. -/
theorem pairDefect_lower (v w : Vector) (hv : ∀ i, 0 ≤ v i) (hw : ∀ i, 0 ≤ w i)
    (hnv : rowSquare v = 1) (hnw : rowSquare w = 1) :
    (rowDeficit v + rowDeficit w) / 3 ≤ pairDefect v w := by
  let y : Vector := fun i => Real.sqrt (v i * w i)
  have hy : ∀ i, 0 ≤ y i := fun i => Real.sqrt_nonneg _
  have hysq : ∀ i, y i ^ 2 = v i * w i := fun i =>
    Real.sq_sqrt (mul_nonneg (hv i) (hw i))
  have hyNorm : rowSquare y = rowDot v w := by
    simp only [rowSquare, rowDot, sumFour, hysq]
  have hyFourth : sumFour (fun i => y i ^ 4) = rowOverlap v w := by
    simp only [sumFour, rowOverlap, show ∀ i, y i ^ 4 = (y i ^ 2)^2 from
      fun i => by ring, hysq]
    ring
  have hq := scalarQuartic_pairs y hy
  rw [hyNorm, hyFourth] at hq
  have hd : rowDot v w ≤ 1 := by
    have h := add_nonneg (add_nonneg (sq_nonneg (v 0-w 0)) (sq_nonneg (v 1-w 1)))
      (add_nonneg (sq_nonneg (v 2-w 2)) (sq_nonneg (v 3-w 3)))
    dsimp [rowDot, rowSquare, sumFour] at *
    nlinarith only [hnv, hnw, h]
  have hp : 0 ≤ rowPairs y := by
    dsimp [rowPairs]
    positivity
  have hm (i j : Fin 4) : 2 * (y i * y j) ≤ v i * v j + w i * w j := by
    apply nonneg_amgm _ _ _ (mul_nonneg (hv i) (hv j))
      (mul_nonneg (hw i) (hw j)) (mul_nonneg (hy i) (hy j))
    rw [mul_pow, hysq, hysq]
    ring
  have hps : 2 * rowPairs y ≤ rowPairs v + rowPairs w := by
    have h01 := hm 0 1
    have h02 := hm 0 2
    have h03 := hm 0 3
    have h12 := hm 1 2
    have h13 := hm 1 3
    have h23 := hm 2 3
    dsimp [rowPairs]
    linarith only [h01, h02, h03, h12, h13, h23]
  have hmain : 0 ≤ 12 * rowOverlap v w - 6 * rowDot v w ^ 2 +
      rowPairs v + rowPairs w := by
    have h := mul_nonneg (sub_nonneg.mpr hd) hp
    nlinarith only [hq, hps, h]
  have hId : 6 * (pairDefect v w - (rowDeficit v + rowDeficit w) / 3) =
      12 * rowOverlap v w - 6 * rowDot v w ^ 2 + rowPairs v + rowPairs w := by
    dsimp [pairDefect, rowDeficit, rowPairs, rowSquare, sumFour] at *
    nlinarith only [hnv, hnw]
  linarith only [hId, hmain]

/-- The two by two permanent on a pair of columns. -/
def pairEntry (v w : Vector) (i j : Fin 4) : ℝ := v i * w j + v j * w i

/-- Laplace expansion of the four by four permanent along two pairs of rows. -/
def pairedPermanent (a b c d : Vector) : ℝ :=
  pairEntry a b 0 1 * pairEntry c d 2 3 +
  pairEntry a b 0 2 * pairEntry c d 1 3 +
  pairEntry a b 0 3 * pairEntry c d 1 2 +
  pairEntry a b 1 2 * pairEntry c d 0 3 +
  pairEntry a b 1 3 * pairEntry c d 0 2 +
  pairEntry a b 2 3 * pairEntry c d 0 1

/-- A direct sum of six squares proves the row-pair permanent bound. -/
theorem pairedPermanent_le (a b c d : Vector)
    (ha : rowSquare a = 1) (hb : rowSquare b = 1)
    (hc : rowSquare c = 1) (hd : rowSquare d = 1) :
    2 * pairedPermanent a b c d ≤ 3 - pairDefect a b - pairDefect c d := by
  have hid :
      (pairEntry a b 0 1-pairEntry c d 2 3)^2 +
      (pairEntry a b 0 2-pairEntry c d 1 3)^2 +
      (pairEntry a b 0 3-pairEntry c d 1 2)^2 +
      (pairEntry a b 1 2-pairEntry c d 0 3)^2 +
      (pairEntry a b 1 3-pairEntry c d 0 2)^2 +
      (pairEntry a b 2 3-pairEntry c d 0 1)^2 =
      rowSquare a * rowSquare b + rowSquare c * rowSquare d + 1 -
      pairDefect a b - pairDefect c d - 2 * pairedPermanent a b c d := by
    dsimp [pairEntry, rowSquare, rowDot, rowOverlap, sumFour, pairDefect, pairedPermanent]
    ring
  rw [ha,hb,hc,hd] at hid
  have hs : 0 ≤
      (pairEntry a b 0 1-pairEntry c d 2 3)^2 +
      (pairEntry a b 0 2-pairEntry c d 1 3)^2 +
      (pairEntry a b 0 3-pairEntry c d 1 2)^2 +
      (pairEntry a b 1 2-pairEntry c d 0 3)^2 +
      (pairEntry a b 1 3-pairEntry c d 0 2)^2 +
      (pairEntry a b 2 3-pairEntry c d 0 1)^2 := by positivity
  linarith only [hid,hs]

/-- Quantitative uniform permanent inequality, expressed by its explicit expansion. -/
theorem uniformDeficit_paired (a b c d : Vector)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hc : ∀ i, 0 ≤ c i) (hd : ∀ i, 0 ≤ d i)
    (hna : rowSquare a = 1) (hnb : rowSquare b = 1)
    (hnc : rowSquare c = 1) (hnd : rowSquare d = 1) :
    (rowDeficit a + rowDeficit b + rowDeficit c + rowDeficit d)/9 ≤
      1 - (2/3 : ℝ) * pairedPermanent a b c d := by
  have h1 := pairedPermanent_le a b c d hna hnb hnc hnd
  have h2 := pairedPermanent_le a c b d hna hnc hnb hnd
  have h3 := pairedPermanent_le a d b c hna hnd hnb hnc
  have he2 : pairedPermanent a c b d = pairedPermanent a b c d := by
    dsimp [pairedPermanent,pairEntry]; ring
  have he3 : pairedPermanent a d b c = pairedPermanent a b c d := by
    dsimp [pairedPermanent,pairEntry]; ring
  rw [he2] at h2
  rw [he3] at h3
  have hab := pairDefect_lower a b ha hb hna hnb
  have hac := pairDefect_lower a c ha hc hna hnc
  have had := pairDefect_lower a d ha hd hna hnd
  have hbc := pairDefect_lower b c hb hc hnb hnc
  have hbd := pairDefect_lower b d hb hd hnb hnd
  have hcd := pairDefect_lower c d hc hd hnc hnd
  linarith only [h1,h2,h3,hab,hac,had,hbc,hbd,hcd]

private theorem decomposeFin_apply_two {n : ℕ} (p : Fin (n+3))
    (e : Equiv.Perm (Fin (n+2))) :
    Equiv.Perm.decomposeFin.symm (p,e) 2 = Equiv.swap 0 p (e 1).succ := by
  exact Equiv.Perm.decomposeFin_symm_apply_succ e p 1

private theorem decomposeFin_apply_three {n : ℕ} (p : Fin (n+4))
    (e : Equiv.Perm (Fin (n+3))) :
    Equiv.Perm.decomposeFin.symm (p,e) 3 = Equiv.swap 0 p (e 2).succ := by
  exact Equiv.Perm.decomposeFin_symm_apply_succ e p 2

theorem pairedPermanent_eq_permanent (A : Matrix (Fin 4) (Fin 4) ℝ) :
    pairedPermanent (A 0) (A 1) (A 2) (A 3) = A.permanent := by
  rw [← Matrix.permanent_transpose]
  simp [-Finset.map_univ_equiv, Matrix.permanent, Finset.univ_perm_fin_succ, Finset.sum_map,
    Equiv.toEmbedding_apply, Fintype.sum_prod_type, Fin.sum_univ_succ,
    Fin.prod_univ_succ, Equiv.Perm.decomposeFin_symm_apply_zero,
    Matrix.transpose_apply,
    decomposeFin_apply_two, decomposeFin_apply_three,
    Equiv.swap_apply_def, pairedPermanent, pairEntry]
  ring

/-- Uniform sharp deficit for four nonnegative, probability-L²-normalized rows. -/
theorem uniformDeficit (A : Matrix (Fin 4) (Fin 4) ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hNorm : ∀ i, (∑ j, A i j ^ 2) / 4 = 1) :
    (∑ i, (1 - ((∑ j, A i j) / 4) ^ 2)) / 9 ≤ 1 - A.permanent / 24 := by
  let v : Fin 4 → Vector := fun i j => A i j / 2
  have hv : ∀ i j, 0 ≤ v i j := fun i j => div_nonneg (hA i j) (by norm_num)
  have hn : ∀ i, rowSquare (v i) = 1 := by
    intro i
    have hi := hNorm i
    simp only [Fin.sum_univ_four] at hi
    dsimp [rowSquare,sumFour,v]
    nlinarith only [hi]
  have h := uniformDeficit_paired (v 0) (v 1) (v 2) (v 3)
    (hv 0) (hv 1) (hv 2) (hv 3) (hn 0) (hn 1) (hn 2) (hn 3)
  have hp : pairedPermanent (v 0) (v 1) (v 2) (v 3) = A.permanent / 16 := by
    rw [← pairedPermanent_eq_permanent A]
    dsimp [pairedPermanent, pairEntry, v]
    ring
  rw [hp] at h
  simp only [Fin.sum_univ_four]
  dsimp [rowDeficit,sumFour,v] at h
  nlinarith only [h]

end
end FourRow
