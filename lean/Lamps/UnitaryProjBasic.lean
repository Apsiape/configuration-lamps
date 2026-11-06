import Lamps.UnitaryPhaseFourier

/-!
# Projection products on `Matrix Ω Ω ℂ` with the real Hilbert–Schmidt inner product

`rip X Y = Re Tr(X*Y)`.  Orthogonal projections are idempotent `rip`-symmetric maps; we restate
Lemma `lem:projections` for them, define the averaging projections
`B_{d,s}(Z) = ⅓ ∑ₖ d^{-k} Z d^{±k}`, and show that the average of `F_h* x G_h` over
`h ∈ (ℤ/3)^m` is the iterated composition of these projections (`avg_conj`).
Consequence (`core_bound`): `∑_h ‖F_h x - x G_h‖² ≤ 3^m · 4 ∑_j ‖x - B_j x‖²`.
-/

namespace Lamps

open Finset Matrix ComplexConjugate

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]


/-- `‖X‖²_HS` on matrices (a non-reducible wrapper around `Houghton.nsq`). -/
noncomputable def nq (X : Matrix Ω Ω ℂ) : ℝ := Houghton.nsq X

lemma nq_nonneg (X : Matrix Ω Ω ℂ) : 0 ≤ nq X := Houghton.nsq_nonneg X

lemma nq_neg (X : Matrix Ω Ω ℂ) : nq (-X) = nq X := nsq_neg X

lemma nq_mul_left {U : Matrix Ω Ω ℂ} (hU : Uᴴ * U = 1) (X : Matrix Ω Ω ℂ) :
    nq (U * X) = nq X := nsq_mul_left_unitary hU X

lemma nq_mul_right {U : Matrix Ω Ω ℂ} (hU : U * Uᴴ = 1) (X : Matrix Ω Ω ℂ) :
    nq (X * U) = nq X := nsq_mul_right_unitary hU X

/-- Real Hilbert–Schmidt inner product `Re Tr(X* Y)`. -/
noncomputable def rip (X Y : Matrix Ω Ω ℂ) : ℝ := (Houghton.hip X Y).re

lemma rip_eq_trace (X Y : (Matrix Ω Ω ℂ)) : rip X Y = ((Xᴴ * Y).trace).re := by
  rw [rip, hip_eq_trace]

lemma rip_comm (X Y : (Matrix Ω Ω ℂ)) : rip X Y = rip Y X := by
  simp only [rip, Houghton.hip, Complex.re_sum]
  refine sum_congr rfl fun α _ => sum_congr rfl fun β _ => ?_
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

lemma rip_self (X : (Matrix Ω Ω ℂ)) : rip X X = nq X := by
  simp only [rip, Houghton.hip, nq, Houghton.nsq, Complex.re_sum]
  refine sum_congr rfl fun α _ => sum_congr rfl fun β _ => ?_
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  ring

lemma rip_sub_right (X Y Z : (Matrix Ω Ω ℂ)) : rip X (Y - Z) = rip X Y - rip X Z := by
  simp only [rip_eq_trace, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]

lemma rip_add_right (X Y Z : (Matrix Ω Ω ℂ)) : rip X (Y + Z) = rip X Y + rip X Z := by
  simp only [rip_eq_trace, Matrix.mul_add, Matrix.trace_add, Complex.add_re]

lemma rip_sub_left (X Y Z : (Matrix Ω Ω ℂ)) : rip (X - Y) Z = rip X Z - rip Y Z := by
  rw [rip_comm, rip_sub_right, rip_comm Z, rip_comm Z]

lemma rip_add_left (X Y Z : (Matrix Ω Ω ℂ)) : rip (X + Y) Z = rip X Z + rip Y Z := by
  rw [rip_comm, rip_add_right, rip_comm Z, rip_comm Z]

lemma rip_smul_right (r : ℝ) (X Y : (Matrix Ω Ω ℂ)) : rip X (r • Y) = r * rip X Y := by
  simp only [rip_eq_trace, Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]

lemma rip_smul_left (r : ℝ) (X Y : (Matrix Ω Ω ℂ)) : rip (r • X) Y = r * rip X Y := by
  rw [rip_comm, rip_smul_right, rip_comm]

lemma rip_sum_right {ι : Type} (s : Finset ι) (X : (Matrix Ω Ω ℂ)) (F : ι → (Matrix Ω Ω ℂ)) :
    rip X (∑ k ∈ s, F k) = ∑ k ∈ s, rip X (F k) := by
  simp only [rip_eq_trace, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]

lemma rip_sum_left {ι : Type} (s : Finset ι) (X : (Matrix Ω Ω ℂ)) (F : ι → (Matrix Ω Ω ℂ)) :
    rip (∑ k ∈ s, F k) X = ∑ k ∈ s, rip (F k) X := by
  rw [rip_comm, rip_sum_right]
  exact sum_congr rfl fun k _ => rip_comm _ _

lemma rip_neg_left (X Y : (Matrix Ω Ω ℂ)) : rip (-X) Y = - rip X Y := by
  simp only [rip_eq_trace, conjTranspose_neg, Matrix.neg_mul, Matrix.trace_neg, Complex.neg_re]

lemma nsq_add_rip (X Y : (Matrix Ω Ω ℂ)) :
    nq (X + Y) = nq X + 2 * rip X Y + nq Y := by
  rw [← rip_self, ← rip_self X, ← rip_self Y, rip_add_left, rip_add_right, rip_add_right,
    rip_comm Y X]
  ring

lemma nsq_sub_rip (X Y : (Matrix Ω Ω ℂ)) :
    nq (X - Y) = nq X - 2 * rip X Y + nq Y := by
  rw [← rip_self, ← rip_self X, ← rip_self Y, rip_sub_left, rip_sub_right, rip_sub_right,
    rip_comm Y X]
  ring

lemma abs_rip_le (X Y : (Matrix Ω Ω ℂ)) :
    |rip X Y| ≤ Real.sqrt (nq X) * Real.sqrt (nq Y) := by
  have h1 : rip X Y ≤ Real.sqrt (nq X) * Real.sqrt (nq Y) :=
    Houghton.re_hip_le X Y
  have h2 : rip (-X) Y ≤ Real.sqrt (nq (-X)) * Real.sqrt (nq Y) :=
    Houghton.re_hip_le (-X) Y
  rw [rip_neg_left, nq_neg] at h2
  exact abs_le.mpr ⟨by linarith, h1⟩

/-- `Re Tr((U* a V)* b) = Re Tr(a* (U b V*))`. -/
lemma rip_conj (U V a b : (Matrix Ω Ω ℂ)) : rip (Uᴴ * a * V) b = rip a (U * b * Vᴴ) := by
  rw [rip_eq_trace, rip_eq_trace, conjTranspose_mul, conjTranspose_mul,
    conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm Vᴴ]
  simp only [Matrix.mul_assoc]

/-! ### Orthogonal projections and Lemma `lem:projections` -/

/-- An orthogonal projection for `rip`: idempotent and symmetric. -/
structure IsOP (P : (Matrix Ω Ω ℂ) → (Matrix Ω Ω ℂ)) : Prop where
  idem : ∀ x, P (P x) = P x
  symm : ∀ x y, rip (P x) y = rip x (P y)

lemma IsOP.id : IsOP (id : (Matrix Ω Ω ℂ) → (Matrix Ω Ω ℂ)) := ⟨fun _ => rfl, fun _ _ => rfl⟩

namespace IsOP

variable {P : (Matrix Ω Ω ℂ) → (Matrix Ω Ω ℂ)} (hP : IsOP P)
include hP

lemma range_ker (x y : (Matrix Ω Ω ℂ)) : rip (P x) (y - P y) = 0 := by
  rw [rip_sub_right, hP.symm x y, hP.symm x (P y), hP.idem, sub_self]

lemma eq_sub (x z : (Matrix Ω Ω ℂ)) : rip x (z - P z) = rip (x - P x) (z - P z) := by
  rw [rip_sub_left, hP.range_ker, sub_zero]

lemma nsq_split (z : (Matrix Ω Ω ℂ)) : nq z = nq (P z) + nq (z - P z) := by
  have h := nsq_add_rip (P z) (z - P z)
  rw [hP.range_ker, mul_zero, add_zero, add_sub_cancel] at h
  exact h

lemma nsq_defect (z : (Matrix Ω Ω ℂ)) : nq (z - P z) = nq z - rip z (P z) := by
  have h := hP.nsq_split z
  have h2 : nq (P z) = rip z (P z) := by
    rw [← rip_self, hP.symm, hP.idem]
  linarith

end IsOP

/-- `iterM P x m = P_{m-1} (⋯ (P_0 x))`. -/
def iterM (P : ℕ → (Matrix Ω Ω ℂ) → (Matrix Ω Ω ℂ)) (x : (Matrix Ω Ω ℂ)) : ℕ → (Matrix Ω Ω ℂ)
  | 0 => x
  | j + 1 => P j (iterM P x j)

lemma iterM_shift (P : ℕ → (Matrix Ω Ω ℂ) → (Matrix Ω Ω ℂ)) (x : (Matrix Ω Ω ℂ)) :
    ∀ n, iterM P x (n + 1) = iterM (fun k => P (k + 1)) (P 0 x) n
  | 0 => rfl
  | n + 1 => by
    show P (n + 1) (iterM P x (n + 1)) = P (n + 1) (iterM (fun k => P (k + 1)) (P 0 x) n)
    rw [iterM_shift P x n]

/-- **Lemma `lem:projections`** for `rip`-orthogonal projections on matrices. -/
theorem proj_productsM (P : ℕ → (Matrix Ω Ω ℂ) → (Matrix Ω Ω ℂ)) (hP : ∀ j, IsOP (P j)) (x : (Matrix Ω Ω ℂ)) (m : ℕ) :
    nq x - rip x (iterM P x m) ≤ 2 * ∑ j ∈ range m, nq (x - P j x) := by
  set y := iterM P x with hy
  have hy0 : y 0 = x := rfl
  have hys : ∀ j, y (j + 1) = P j (y j) := fun j => rfl
  have hb : ∑ j ∈ range m, nq (y j - y (j + 1)) =
      nq x - nq (y m) := by
    have step : ∀ j, nq (y j - y (j + 1)) =
        nq (y j) - nq (y (j + 1)) := by
      intro j
      have := (hP j).nsq_split (y j)
      rw [hys]
      linarith
    rw [sum_congr rfl (fun j _ => step j), sum_range_sub' (fun j => nq (y j)), hy0]
  have ha : nq x - rip x (y m) =
      ∑ j ∈ range m, rip (x - P j x) (y j - y (j + 1)) := by
    have step : ∀ j, rip (x - P j x) (y j - y (j + 1)) = rip x (y j) - rip x (y (j + 1)) := by
      intro j
      rw [hys, ← (hP j).eq_sub x (y j), rip_sub_right]
    rw [sum_congr rfl (fun j _ => step j), sum_range_sub' (fun j => rip x (y j)), hy0, rip_self]
  set a := nq x - rip x (y m) with hadef
  set Es := ∑ j ∈ range m, nq (x - P j x) with hEs
  have hEs0 : 0 ≤ Es := sum_nonneg (fun j _ => nq_nonneg _)
  have hcs : a ^ 2 ≤ Es * (nq x - nq (y m)) := by
    rw [ha, ← hb]
    have h1 : |∑ j ∈ range m, rip (x - P j x) (y j - y (j + 1))| ≤
        ∑ j ∈ range m, Real.sqrt (nq (x - P j x)) *
          Real.sqrt (nq (y j - y (j + 1))) :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun j _ => abs_rip_le _ _))
    have h2 := sum_mul_sq_le_sq_mul_sq (range m) (fun j => Real.sqrt (nq (x - P j x)))
      (fun j => Real.sqrt (nq (y j - y (j + 1))))
    have e2 : ∀ j, Real.sqrt (nq (x - P j x)) ^ 2 = nq (x - P j x) :=
      fun j => Real.sq_sqrt (nq_nonneg _)
    have e3 : ∀ j, Real.sqrt (nq (y j - y (j + 1))) ^ 2 = nq (y j - y (j + 1)) :=
      fun j => Real.sq_sqrt (nq_nonneg _)
    simp only [e2, e3] at h2
    have h3 : (∑ j ∈ range m, rip (x - P j x) (y j - y (j + 1))) ^ 2 ≤
        (∑ j ∈ range m, Real.sqrt (nq (x - P j x)) *
          Real.sqrt (nq (y j - y (j + 1)))) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    exact h3.trans h2
  have hab : nq x - nq (y m) ≤ 2 * a := by
    have h := nsq_sub_rip x (y m)
    have h0 := nq_nonneg (x - y m)
    rw [hadef]
    linarith
  by_cases hpos : a ≤ 0
  · linarith
  · push Not at hpos
    have : a ^ 2 ≤ Es * (2 * a) := hcs.trans (mul_le_mul_of_nonneg_left hab hEs0)
    nlinarith

/-! ### The averaging projections `B_{d,s}` -/

/-- `sg s k = ∓k`. -/
def sg (s : Bool) (k : Fin 3) : Fin 3 := if s then -k else k

lemma sg_add (s : Bool) (k l : Fin 3) : sg s k + sg s l = sg s (k + l) := by
  cases s <;> simp [sg] <;> exact add_comm _ _

lemma sg_neg (s : Bool) (k : Fin 3) : sg s (-k) = -(sg s k) := by
  cases s <;> simp [sg]

/-- `T_k(Z) = (d^k)* Z d^{sg k}`. -/
def Tm (d : (Matrix Ω Ω ℂ)) (s : Bool) (k : Fin 3) (Z : (Matrix Ω Ω ℂ)) : (Matrix Ω Ω ℂ) := (d ^ k.val)ᴴ * Z * d ^ (sg s k).val

/-- `B_{d,s}(Z) = ⅓ ∑ₖ T_k(Z)`. -/
noncomputable def Bop (d : (Matrix Ω Ω ℂ)) (s : Bool) (Z : (Matrix Ω Ω ℂ)) : (Matrix Ω Ω ℂ) := (1 / 3 : ℝ) • ∑ k : Fin 3, Tm d s k Z

lemma Tm_smul_sum (d : (Matrix Ω Ω ℂ)) (s : Bool) (k : Fin 3) (r : ℝ) (F : Fin 3 → (Matrix Ω Ω ℂ)) :
    Tm d s k (r • ∑ j, F j) = r • ∑ j, Tm d s k (F j) := by
  simp only [Tm, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul]

lemma sum_Tm (d : (Matrix Ω Ω ℂ)) (s : Bool) (Z : (Matrix Ω Ω ℂ)) : ∑ k, Tm d s k Z = (3 : ℝ) • Bop d s Z := by
  rw [Bop, smul_smul]
  norm_num

lemma smul_three_const (B : (Matrix Ω Ω ℂ)) : (1 / 3 : ℝ) • ∑ _k : Fin 3, B = B := by
  rw [sum_const, card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  norm_num

lemma d_sq {d : (Matrix Ω Ω ℂ)} (hd : IsU d) (hd3 : d ^ 3 = 1) : d ^ 2 = dᴴ := by
  calc d ^ 2 = d ^ 2 * (d * dᴴ) := by rw [hd.2, Matrix.mul_one]
    _ = d ^ 3 * dᴴ := by rw [← Matrix.mul_assoc, ← pow_succ]
    _ = dᴴ := by rw [hd3, Matrix.one_mul]

section Bop

variable {d : (Matrix Ω Ω ℂ)} (hd : IsU d) (hd3 : d ^ 3 = 1)
include hd hd3

lemma pw_neg (k : Fin 3) : d ^ (-k).val = (d ^ k.val)ᴴ := by
  have h1 : d ^ (-k).val * d ^ k.val = 1 := by
    rw [← mpow_val_add d hd3, neg_add_cancel]
    simp
  have hk := (hd.pow k.val).2
  calc d ^ (-k).val = d ^ (-k).val * (d ^ k.val * (d ^ k.val)ᴴ) := by rw [hk, Matrix.mul_one]
    _ = (d ^ k.val)ᴴ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]

lemma Tm_Tm (s : Bool) (k l : Fin 3) (Z : (Matrix Ω Ω ℂ)) : Tm d s l (Tm d s k Z) = Tm d s (k + l) Z := by
  simp only [Tm]
  rw [← sg_add, mpow_val_add d hd3, mpow_val_add d hd3, conjTranspose_mul]
  simp only [Matrix.mul_assoc]

lemma Tm_Bop (s : Bool) (l : Fin 3) (Z : (Matrix Ω Ω ℂ)) : Tm d s l (Bop d s Z) = Bop d s Z := by
  rw [Bop, Tm_smul_sum]
  congr 1
  simp only [Tm_Tm hd hd3]
  exact Fintype.sum_equiv (Equiv.addRight l) (fun k => Tm d s (k + l) Z) (fun k => Tm d s k Z)
    (fun k => rfl)

lemma Bop_idem (s : Bool) (Z : (Matrix Ω Ω ℂ)) : Bop d s (Bop d s Z) = Bop d s Z := by
  show (1 / 3 : ℝ) • ∑ l : Fin 3, Tm d s l (Bop d s Z) = Bop d s Z
  simp only [Tm_Bop hd hd3]
  exact smul_three_const _

lemma rip_Tm (s : Bool) (k : Fin 3) (Z Y : (Matrix Ω Ω ℂ)) : rip (Tm d s k Z) Y = rip Z (Tm d s (-k) Y) := by
  simp only [Tm]
  rw [rip_conj, sg_neg, pw_neg hd hd3, pw_neg hd hd3, conjTranspose_conjTranspose]

lemma Bop_symm (s : Bool) (x y : (Matrix Ω Ω ℂ)) : rip (Bop d s x) y = rip x (Bop d s y) := by
  simp only [Bop, rip_smul_left, rip_smul_right, rip_sum_left, rip_sum_right, rip_Tm hd hd3]
  rw [Fintype.sum_equiv (Equiv.neg (Fin 3)) (fun k => rip x (Tm d s (-k) y))
    (fun k => rip x (Tm d s k y)) (fun k => rfl)]

lemma Bop_isOP (s : Bool) : IsOP (Bop d s) := ⟨Bop_idem hd hd3 s, Bop_symm hd hd3 s⟩

/-- `‖x - B_{d,+}x‖² = ⅓ ‖xd - dx‖²`. -/
lemma Bop_false_defect (x : (Matrix Ω Ω ℂ)) :
    nq (x - Bop d false x) = (1 / 3) * nq (x * d - d * x) := by
  rw [(Bop_isOP hd hd3 false).nsq_defect x]
  have e0 : Tm d false 0 x = x := by simp [Tm, sg]
  have e1 : Tm d false 1 x = dᴴ * x * d := by simp [Tm, sg]
  have e2 : Tm d false 2 x = d * x * dᴴ := by
    have : ((2 : Fin 3)).val = 2 := rfl
    simp only [Tm, sg, Bool.false_eq_true, ite_false, this, d_sq hd hd3,
      conjTranspose_conjTranspose]
  have hB : rip x (Bop d false x) =
      (1 / 3) * (nq x + 2 * rip x (d * x * dᴴ)) := by
    rw [Bop, rip_smul_right, rip_sum_right, Fin.sum_univ_three, e0, e1, e2, rip_self]
    have : rip x (dᴴ * x * d) = rip x (d * x * dᴴ) := by
      rw [rip_comm, rip_conj]
    rw [this]
    ring
  have hN : nq (x * d - d * x) = 2 * nq x - 2 * rip x (d * x * dᴴ) := by
    rw [nsq_sub_rip, nq_mul_right hd.2, nq_mul_left hd.1]
    have : rip (x * d) (d * x) = rip x (d * x * dᴴ) := by
      have h := rip_conj 1 d x (d * x)
      rwa [conjTranspose_one, Matrix.one_mul, Matrix.one_mul] at h
    rw [this]
    ring
  rw [hB, hN]
  ring

lemma Bop_true_fix (x : (Matrix Ω Ω ℂ)) (hfix : ∀ k : Fin 3, Tm d true k x = x) : Bop d true x = x := by
  simp only [Bop, hfix]
  exact smul_three_const _

end Bop

/-! ### Iterated composition = average over `(ℤ/3)^m` -/

/-- The `k`-th projection of the list `(B_{d_j, ε_j})_j` (identity beyond the end). -/
noncomputable def PS {m : ℕ} (d : Fin m → (Matrix Ω Ω ℂ)) (ε : Fin m → Bool) (k : ℕ) : (Matrix Ω Ω ℂ) → (Matrix Ω Ω ℂ) :=
  if h : k < m then Bop (d ⟨k, h⟩) (ε ⟨k, h⟩) else id

lemma PS_isOP {m : ℕ} (d : Fin m → (Matrix Ω Ω ℂ)) (ε : Fin m → Bool) (hd : ∀ j, IsU (d j))
    (hd3 : ∀ j, d j ^ 3 = 1) (k : ℕ) : IsOP (PS d ε k) := by
  unfold PS
  split_ifs with h
  · exact Bop_isOP (hd _) (hd3 _) _
  · exact IsOP.id

lemma PS_succ {m : ℕ} (d : Fin (m + 1) → (Matrix Ω Ω ℂ)) (ε : Fin (m + 1) → Bool) :
    (fun k => PS d ε (k + 1)) = PS (fun j => d j.succ) (fun j => ε j.succ) := by
  funext k
  simp only [PS]
  by_cases hk : k < m
  · rw [dif_pos (by omega), dif_pos hk]
    rfl
  · rw [dif_neg (by omega), dif_neg hk]

lemma PS_sum {m : ℕ} (d : Fin m → (Matrix Ω Ω ℂ)) (ε : Fin m → Bool) (F : ((Matrix Ω Ω ℂ) → (Matrix Ω Ω ℂ)) → ℝ) :
    ∑ k ∈ range m, F (PS d ε k) = ∑ j : Fin m, F (Bop (d j) (ε j)) := by
  rw [Finset.sum_range]
  refine sum_congr rfl fun j _ => ?_
  simp only [PS, dif_pos j.isLt]

/-- `flipS ε g = (sg εⱼ gⱼ)ⱼ`. -/
def flipS {m : ℕ} (ε : Fin m → Bool) (g : Fin m → Fin 3) : Fin m → Fin 3 :=
  fun j => sg (ε j) (g j)

lemma flipS_cons {m : ℕ} (ε : Fin (m + 1) → Bool) (a : Fin 3) (h : Fin m → Fin 3) :
    flipS ε (Fin.cons a h) = Fin.cons (sg (ε 0) a) (flipS (fun j => ε j.succ) h) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j <;> simp [flipS]

lemma fprodU_cons {m : ℕ} (d : Fin (m + 1) → (Matrix Ω Ω ℂ)) (a : Fin 3) (h : Fin m → Fin 3) :
    fprodU d (Fin.cons a h) = d 0 ^ a.val * fprodU (fun j => d j.succ) h := by
  simp only [fprodU, List.ofFn_succ, List.prod_cons, Fin.cons_zero, Fin.cons_succ]

lemma rip_sandwich_sum (y A B : (Matrix Ω Ω ℂ)) (T : Fin 3 → (Matrix Ω Ω ℂ)) :
    ∑ a, rip y (A * T a * B) = rip y (A * (∑ a, T a) * B) := by
  rw [Matrix.mul_sum, Matrix.sum_mul, rip_sum_right]

/-- `∑_h ⟪y, F_h* x G_h⟫ = 3^m ⟪y, B_{m-1} ⋯ B_0 x⟫`. -/
lemma avg_conj : ∀ (m : ℕ) (d : Fin m → (Matrix Ω Ω ℂ)) (ε : Fin m → Bool), (∀ j, IsU (d j)) →
    (∀ j, d j ^ 3 = 1) → ∀ x y : (Matrix Ω Ω ℂ),
    ∑ h : Fin m → Fin 3, rip y ((fprodU d h)ᴴ * x * fprodU d (flipS ε h)) =
      3 ^ m * rip y (iterM (PS d ε) x m)
  | 0, d, ε, _, _, x, y => by
    simp [fprodU, iterM]
  | m + 1, d, ε, hd, hd3, x, y => by
    rw [Houghton.sum_cons3]
    have e : ∀ (a : Fin 3) (h : Fin m → Fin 3),
        rip y ((fprodU d (Fin.cons a h))ᴴ * x * fprodU d (flipS ε (Fin.cons a h))) =
        rip y ((fprodU (fun j => d j.succ) h)ᴴ * Tm (d 0) (ε 0) a x *
          fprodU (fun j => d j.succ) (flipS (fun j => ε j.succ) h)) := by
      intro a h
      rw [flipS_cons, fprodU_cons, fprodU_cons, conjTranspose_mul]
      simp only [Tm, Matrix.mul_assoc]
    simp only [e]
    rw [sum_comm]
    simp only [rip_sandwich_sum, sum_Tm, Matrix.mul_smul, Matrix.smul_mul, rip_smul_right]
    rw [← mul_sum, avg_conj m (fun j => d j.succ) (fun j => ε j.succ) (fun j => hd _)
      (fun j => hd3 _), iterM_shift, PS_succ]
    simp only [PS, dif_pos (Nat.succ_pos m)]
    rw [pow_succ]
    simp only [Fin.zero_eta]
    ring

/-- `‖F x - x G‖² = 2‖x‖² - 2⟪x, F* x G⟫` for unitaries `F, G`. -/
lemma nsq_swap {F G : (Matrix Ω Ω ℂ)} (hF : IsU F) (hG : IsU G) (x : (Matrix Ω Ω ℂ)) :
    nq (F * x - x * G) = 2 * nq x - 2 * rip x (Fᴴ * x * G) := by
  have h1 : nq (F * x - x * G) = nq (x - Fᴴ * x * G) := by
    rw [← nq_mul_left (U := Fᴴ) (by rw [conjTranspose_conjTranspose]; exact hF.2),
      Matrix.mul_sub, ← Matrix.mul_assoc, hF.1, Matrix.one_mul, Matrix.mul_assoc]
  have h2 : nq (Fᴴ * x * G) = nq x := by
    rw [nq_mul_right hG.2,
      nq_mul_left (by rw [conjTranspose_conjTranspose]; exact hF.2)]
  rw [h1, nsq_sub_rip, h2]
  ring

/-- **Core estimate**: `∑_h ‖F_h x - x G_h‖² ≤ 3^m · 4 ∑_j ‖x - B_j x‖²`. -/
theorem core_bound {m : ℕ} (d : Fin m → (Matrix Ω Ω ℂ)) (ε : Fin m → Bool) (hd : ∀ j, IsU (d j))
    (hd3 : ∀ j, d j ^ 3 = 1) (x : (Matrix Ω Ω ℂ)) :
    ∑ h : Fin m → Fin 3, nq (fprodU d h * x - x * fprodU d (flipS ε h)) ≤
      3 ^ m * (4 * ∑ j, nq (x - Bop (d j) (ε j) x)) := by
  have e1 : ∀ h : Fin m → Fin 3, nq (fprodU d h * x - x * fprodU d (flipS ε h)) =
      2 * nq x - 2 * rip x ((fprodU d h)ᴴ * x * fprodU d (flipS ε h)) :=
    fun h => nsq_swap (isU_fprodU d hd h) (isU_fprodU d hd _) x
  rw [sum_congr rfl (fun h _ => e1 h), sum_sub_distrib, sum_const, card_univ, ← mul_sum,
    avg_conj m d ε hd hd3]
  have pp := proj_productsM (PS d ε) (PS_isOP d ε hd hd3) x m
  rw [PS_sum d ε (fun P => nq (x - P x))] at pp
  have hc : (Fintype.card (Fin m → Fin 3) : ℝ) = 3 ^ m := by simp
  rw [nsmul_eq_mul, hc]
  have h3 : (0 : ℝ) ≤ 3 ^ m := by positivity
  nlinarith [mul_le_mul_of_nonneg_left pp h3]

end Lamps
