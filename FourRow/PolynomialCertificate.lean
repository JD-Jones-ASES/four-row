module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

/-!
# Exact sparse-polynomial certificate checker

A certificate is an integer expression together with integer weighted squares.
The exposed structural algorithms below can be reduced by Lean's kernel. Their
soundness preserves evaluation for every real assignment, including when a sort
runs out of fuel. Equality of the normalized lists is only a sufficient check;
no claim of completeness or unproved sorting invariant enters the theorem.
-/
@[expose] public section
namespace FourRow.PolynomialCertificate

abbrev Mon := List (Fin 16)
abbrev Poly := List (Mon × ℤ)
def meval (a : Fin 16 → ℝ) (m : Mon) : ℝ := (m.map a).prod
def peval (a : Fin 16 → ℝ) (p : Poly) : ℝ :=
  (p.map fun t => (t.2 : ℝ) * meval a t.1).sum


def insertVar (i : Fin 16) : Mon → Mon
  | [] => [i]
  | j::js => if i ≤ j then i::j::js else j::insertVar i js
def sortMon (m : Mon) : Mon := m.foldr insertVar []
def mtimes (t : Mon × ℤ) (p : Poly) : Poly :=
  p.map fun s => (sortMon (t.1 ++ s.1), t.2*s.2)

theorem insertVar_sound (a : Fin 16 → ℝ) (i : Fin 16) (m : Mon) :
    meval a (insertVar i m) = a i * meval a m := by
  induction m with
  | nil => simp [insertVar, meval]
  | cons j js ih =>
    simp only [insertVar]
    split_ifs
    · simp [meval]
    · change a j * meval a (insertVar i js) = a i * (a j * meval a js)
      rw [ih]
      ring

theorem meval_sort (a : Fin 16 → ℝ) (m : Mon) :
    meval a (sortMon m) = meval a m := by
  induction m with
  | nil => rfl
  | cons i is ih =>
    change meval a (insertVar i (sortMon is)) = _
    rw [insertVar_sound, ih]
    rfl

theorem meval_append (a : Fin 16 → ℝ) (m n : Mon) :
    meval a (m++n) = meval a m * meval a n := by simp [meval]

theorem mtimes_sound (a : Fin 16 → ℝ) (t : Mon × ℤ) (p : Poly) :
    peval a (mtimes t p) = (t.2:ℝ)*meval a t.1 * peval a p := by
  induction p with
  | nil => simp [mtimes, peval]
  | cons s ps ih =>
    change ((t.2*s.2:ℤ):ℝ) * meval a (sortMon (t.1++s.1)) + peval a (mtimes t ps) = _
    rw [Int.cast_mul, meval_sort, meval_append, ih]
    simp only [peval, List.map_cons, List.sum_cons]
    ring


inductive Expr where
  | c : ℤ → Expr
  | x : Fin 16 → Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | sub : Expr → Expr → Expr
  | sq : Expr → Expr
  deriving Repr

def eval (a : Fin 16 → ℝ) : Expr → ℝ
  | .c q => q
  | .x i => a i
  | .add e f => eval a e + eval a f
  | .mul e f => eval a e * eval a f
  | .sub e f => eval a e - eval a f
  | .sq e => (eval a e)^2


def headAdd (m : Mon) (q : ℤ) : Poly → Poly
  | [] => if q=0 then [] else [(m,q)]
  | (n,r)::ps =>
    if m=n then if q+r=0 then ps else (m,q+r)::ps
    else if q=0 then (n,r)::ps else (m,q)::(n,r)::ps

theorem headAdd_sound (a : Fin 16 → ℝ) (m : Mon) (q : ℤ) (p : Poly) :
    peval a (headAdd m q p) = (q:ℝ)*meval a m + peval a p := by
  cases p with
  | nil => simp [headAdd, peval]; split_ifs with h <;> simp_all
  | cons t ps =>
    rcases t with ⟨n,r⟩
    simp only [headAdd]
    split_ifs with h hr hq
    · subst n
      have hc : (q:ℝ)+(r:ℝ)=0 := by exact_mod_cast hr
      simp only [peval, List.map_cons, List.sum_cons] at *
      linear_combination -(meval a m) * hc
    · subst n
      simp only [peval, List.map_cons, List.sum_cons, Int.cast_add]
      ring
    · subst q
      simp [peval]
    · simp only [peval, List.map_cons, List.sum_cons]

def compress (p : Poly) : Poly := p.foldr (fun t acc => headAdd t.1 t.2 acc) []
def pmerge : ℕ → Poly → Poly → Poly
  | 0, p, q => p++q
  | _+1, [], q => q
  | _+1, p, [] => p
  | n+1, t::p, s::q =>
      if compare t.1 s.1 != .gt then t::pmerge n p (s::q) else s::pmerge n (t::p) q

def psort : ℕ → Poly → Poly
  | 0, p => p
  | _+1, [] => []
  | _+1, [t] => [t]
  | n+1, t::s::p =>
    let p := t::s::p
    let left := psort n (p.take (p.length/2))
    let right := psort n (p.drop (p.length/2))
    pmerge p.length left right

def fastnorm (p : Poly) : Poly := compress (psort 20 p)

theorem compress_sound (a : Fin 16 → ℝ) (p : Poly) : peval a (compress p) = peval a p := by
  induction p with
  | nil => rfl
  | cons t ps ih =>
    change peval a (headAdd t.1 t.2 (compress ps)) = _
    rw [headAdd_sound, ih]
    rfl

theorem peval_append (a : Fin 16 → ℝ) (p q : Poly) :
    peval a (p++q) = peval a p+peval a q := by simp [peval]

theorem pmerge_sound (a : Fin 16 → ℝ) (n : ℕ) (p q : Poly) :
    peval a (pmerge n p q) = peval a p+peval a q := by
  induction n generalizing p q with
  | zero => exact peval_append a p q
  | succ n ih =>
    cases p with
    | nil => simp [pmerge, peval]
    | cons t p =>
      cases q with
      | nil => simp [pmerge, peval]
      | cons s q =>
        simp only [pmerge]
        split_ifs
        · change (t.2:ℝ)*meval a t.1+peval a (pmerge n p (s::q)) = _
          rw [ih]
          simp only [peval, List.map_cons, List.sum_cons]
          ring
        · change (s.2:ℝ)*meval a s.1+peval a (pmerge n (t::p) q) = _
          rw [ih]
          simp only [peval, List.map_cons, List.sum_cons]
          ring

theorem psort_sound (a : Fin 16 → ℝ) (n : ℕ) (p : Poly) :
    peval a (psort n p) = peval a p := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    cases p with
    | nil => rfl
    | cons t p =>
      cases p with
      | nil => rfl
      | cons s p =>
        simp only [psort]
        rw [pmerge_sound, ih, ih, ← peval_append, List.take_append_drop]

theorem fastnorm_sound (a : Fin 16 → ℝ) (p : Poly) : peval a (fastnorm p) = peval a p := by
  rw [fastnorm, compress_sound, psort_sound]

def rawmul (p q : Poly) : Poly := p.flatMap (fun t => mtimes t q)
theorem rawmul_sound (a : Fin 16 → ℝ) (p q : Poly) :
    peval a (rawmul p q) = peval a p*peval a q := by
  induction p with
  | nil => simp [rawmul, peval]
  | cons t ps ih =>
    change peval a (mtimes t q ++ rawmul ps q) = _
    rw [peval_append, mtimes_sound, ih]
    simp only [peval, List.map_cons, List.sum_cons]
    ring

def rawexpand : Expr → Poly
  | .c q => [([],q)]
  | .x i => [([i],1)]
  | .add e f => rawexpand e ++ rawexpand f
  | .mul e f => rawmul (rawexpand e) (rawexpand f)
  | .sub e f => rawexpand e ++ rawmul [([],-1)] (rawexpand f)
  | .sq e => rawmul (rawexpand e) (rawexpand e)

theorem rawexpand_sound (a : Fin 16 → ℝ) (e : Expr) : peval a (rawexpand e) = eval a e := by
  induction e with
  | c q => simp [rawexpand, eval, peval, meval]
  | x i => simp [rawexpand, eval, peval, meval]
  | add e f he hf => simp [rawexpand, eval, peval_append, he, hf]
  | mul e f he hf => simp [rawexpand, eval, rawmul_sound, he, hf]
  | sub e f he hf =>
    simp only [rawexpand, eval, peval_append, rawmul_sound, he, hf]
    simp [peval, meval, sub_eq_add_neg]
  | sq e he => simp [rawexpand, eval, rawmul_sound, he, pow_two]

def rawsquares (ss : List (ℤ × Expr)) : Poly :=
  ss.flatMap (fun s => rawmul [([],s.1)] (rawmul (rawexpand s.2) (rawexpand s.2)))

theorem rawsquares_nonneg (a : Fin 16 → ℝ) (ss : List (ℤ × Expr))
    (h : ∀ s ∈ ss, 0 ≤ s.1) : 0 ≤ peval a (rawsquares ss) := by
  induction ss with
  | nil => simp [rawsquares, peval]
  | cons s ss ih =>
    change 0 ≤ peval a ((rawmul [([],s.1)] (rawmul (rawexpand s.2) (rawexpand s.2))) ++
      (rawsquares ss))
    rw [peval_append, rawmul_sound, rawmul_sound, rawexpand_sound]
    simp only [peval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, meval,
      List.prod_nil, mul_one, add_zero]
    have hs : (0:ℝ) ≤ s.1 := by exact_mod_cast h s (by simp)
    exact add_nonneg (mul_nonneg hs (mul_self_nonneg _))
      (ih fun t ht => h t (by simp [ht]))

theorem fast_certificate_nonneg (e : Expr) (ss : List (ℤ × Expr))
    (h : fastnorm (rawexpand e) = fastnorm (rawsquares ss))
    (hp : ss.all (fun s => decide (0 ≤ s.1)) = true) (a : Fin 16 → ℝ) : 0 ≤ eval a e := by
  have he := congrArg (peval a) h
  rw [fastnorm_sound, fastnorm_sound, rawexpand_sound] at he
  rw [he]
  apply rawsquares_nonneg a ss
  simpa only [List.all_eq_true, decide_eq_true_eq] using hp

end FourRow.PolynomialCertificate
