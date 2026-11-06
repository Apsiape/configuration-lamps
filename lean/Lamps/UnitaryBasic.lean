import Lamps.CriterionModel
import Houghton.Analysis.SectorTwirl

/-!
# Normalized Hilbert–Schmidt distance on unitary matrices, and transport in norm

`uhs X = ‖X‖₂ = (Tr(X*X)/D)^{1/2}`.  It is a norm (triangle inequality via Cauchy–Schwarz),
unitarily bi-invariant, so a word of area `n` under a unitary assignment with relator defects `≤ e`
lies within `n e` of `I` (the unitary half of the first step of Theorem `thm:criterion`).
-/

namespace Lamps

open Finset Matrix ComplexConjugate

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- Normalized Hilbert–Schmidt norm `‖X‖₂`. -/
noncomputable def uhs (X : Matrix Ω Ω ℂ) : ℝ := Real.sqrt (Houghton.nsq X / Fintype.card Ω)

lemma uhs_nonneg (X : Matrix Ω Ω ℂ) : 0 ≤ uhs X := Real.sqrt_nonneg _

lemma nsq_add_sqrt_le (A B : Matrix Ω Ω ℂ) :
    Real.sqrt (Houghton.nsq (A + B)) ≤ Real.sqrt (Houghton.nsq A) + Real.sqrt (Houghton.nsq B) := by
  have hexp : Houghton.nsq (A + B) =
      Houghton.nsq A + Houghton.nsq B + 2 * (Houghton.hip A B).re := by
    simp only [Houghton.nsq, Houghton.hip, Matrix.add_apply, Complex.normSq_add, Complex.re_sum,
      sum_add_distrib, mul_sum]
    congr 1
    refine sum_congr rfl fun α _ => sum_congr rfl fun β _ => ?_
    rw [show (A α β * conj (B α β)).re = (conj (A α β) * B α β).re by
      rw [← Complex.conj_re, map_mul, Complex.conj_conj, mul_comm]]
  have hcs := Houghton.re_hip_le A B
  have ha := Houghton.nsq_nonneg A
  have hb := Houghton.nsq_nonneg B
  rw [Real.sqrt_le_left (by positivity)]
  rw [hexp]
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg (Houghton.nsq A),
    Real.sqrt_nonneg (Houghton.nsq B)]

lemma uhs_add_le (A B : Matrix Ω Ω ℂ) : uhs (A + B) ≤ uhs A + uhs B := by
  unfold uhs
  rcases Nat.eq_zero_or_pos (Fintype.card Ω) with h | h
  · simp [h]
  · have hD : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast h
    rw [Real.sqrt_div' _ hD.le, Real.sqrt_div' _ hD.le, Real.sqrt_div' _ hD.le, ← add_div]
    exact div_le_div_of_nonneg_right (nsq_add_sqrt_le A B) (Real.sqrt_nonneg _)

lemma nsq_neg (A : Matrix Ω Ω ℂ) : Houghton.nsq (-A) = Houghton.nsq A := by
  simp [Houghton.nsq]

lemma uhs_neg (A : Matrix Ω Ω ℂ) : uhs (-A) = uhs A := by
  simp only [uhs, nsq_neg]

lemma nsq_eq_trace (X : Matrix Ω Ω ℂ) : (Houghton.nsq X : ℂ) = (X * Xᴴ).trace :=
  (Houghton.trace_GG X).symm

lemma nsq_mul_left_unitary {U : Matrix Ω Ω ℂ} (hU : Uᴴ * U = 1) (X : Matrix Ω Ω ℂ) :
    Houghton.nsq (U * X) = Houghton.nsq X := by
  have h : ((Houghton.nsq (U * X) : ℝ) : ℂ) = ((Houghton.nsq X : ℝ) : ℂ) := by
    rw [nsq_eq_trace, nsq_eq_trace, conjTranspose_mul, Matrix.mul_assoc, Matrix.trace_mul_comm,
      Matrix.mul_assoc, Matrix.mul_assoc, hU, Matrix.mul_one]
  exact_mod_cast h

lemma nsq_mul_right_unitary {U : Matrix Ω Ω ℂ} (hU : U * Uᴴ = 1) (X : Matrix Ω Ω ℂ) :
    Houghton.nsq (X * U) = Houghton.nsq X := by
  have h : ((Houghton.nsq (X * U) : ℝ) : ℂ) = ((Houghton.nsq X : ℝ) : ℂ) := by
    rw [nsq_eq_trace, nsq_eq_trace, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc U, hU,
      Matrix.one_mul]
  exact_mod_cast h

/-- Unitary matrices (as a predicate). -/
def IsU (U : Matrix Ω Ω ℂ) : Prop := Uᴴ * U = 1 ∧ U * Uᴴ = 1

lemma IsU.mul {U V : Matrix Ω Ω ℂ} (hU : IsU U) (hV : IsU V) : IsU (U * V) := by
  constructor
  · rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, hU.1, Matrix.one_mul, hV.1]
  · rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc V, hV.2, Matrix.one_mul, hU.2]

lemma IsU.one : IsU (1 : Matrix Ω Ω ℂ) := by simp [IsU]

lemma IsU.inv_eq {U : Matrix Ω Ω ℂ} (hU : IsU U) : U⁻¹ = Uᴴ :=
  Matrix.inv_eq_left_inv hU.1

lemma IsU.conjT {U : Matrix Ω Ω ℂ} (hU : IsU U) : IsU Uᴴ := by
  constructor
  · rw [conjTranspose_conjTranspose]; exact hU.2
  · rw [conjTranspose_conjTranspose]; exact hU.1

lemma isU_of_mem {U : Matrix Ω Ω ℂ} (h : U ∈ Matrix.unitaryGroup Ω ℂ) : IsU U :=
  ⟨by simpa [Matrix.star_eq_conjTranspose] using Unitary.star_mul_self_of_mem h,
    by simpa [Matrix.star_eq_conjTranspose] using Unitary.mul_star_self_of_mem h⟩

/-- The distance `‖X - Y‖₂`. -/
noncomputable def ud (X Y : Matrix Ω Ω ℂ) : ℝ := uhs (X - Y)

lemma ud_nonneg (X Y : Matrix Ω Ω ℂ) : 0 ≤ ud X Y := uhs_nonneg _

lemma ud_self (X : Matrix Ω Ω ℂ) : ud X X = 0 := by simp [ud, uhs, Houghton.nsq]

lemma ud_comm (X Y : Matrix Ω Ω ℂ) : ud X Y = ud Y X := by
  rw [ud, ud, ← uhs_neg, neg_sub]

lemma ud_triangle (X Y Z : Matrix Ω Ω ℂ) : ud X Z ≤ ud X Y + ud Y Z := by
  unfold ud
  rw [show X - Z = (X - Y) + (Y - Z) by abel]
  exact uhs_add_le _ _

lemma ud_mul_left {U : Matrix Ω Ω ℂ} (hU : IsU U) (X Y : Matrix Ω Ω ℂ) :
    ud (U * X) (U * Y) = ud X Y := by
  simp only [ud, uhs, ← Matrix.mul_sub, nsq_mul_left_unitary hU.1]

lemma ud_mul_right {U : Matrix Ω Ω ℂ} (hU : IsU U) (X Y : Matrix Ω Ω ℂ) :
    ud (X * U) (Y * U) = ud X Y := by
  simp only [ud, uhs, ← Matrix.sub_mul, nsq_mul_right_unitary hU.2]

lemma ud_mul_le {X Y X' Y' : Matrix Ω Ω ℂ} (hX : IsU X) (hY' : IsU Y') :
    ud (X * Y) (X' * Y') ≤ ud X X' + ud Y Y' := by
  calc ud (X * Y) (X' * Y') ≤ ud (X * Y) (X * Y') + ud (X * Y') (X' * Y') := ud_triangle _ _ _
    _ = ud Y Y' + ud X X' := by rw [ud_mul_left hX, ud_mul_right hY']
    _ = _ := add_comm _ _

lemma ud_conj_one {K : Matrix Ω Ω ℂ} (hK : IsU K) (X : Matrix Ω Ω ℂ) :
    ud (K * X * Kᴴ) 1 = ud X 1 := by
  calc ud (K * X * Kᴴ) 1 = ud (K * X * Kᴴ) (K * 1 * Kᴴ) := by rw [Matrix.mul_one, hK.2]
    _ = ud X 1 := by rw [ud_mul_right hK.conjT, ud_mul_left hK]

lemma ud_inv_one {X : Matrix Ω Ω ℂ} (hX : IsU X) : ud Xᴴ 1 = ud X 1 := by
  calc ud Xᴴ 1 = ud (X * Xᴴ) (X * 1) := (ud_mul_left hX _ _).symm
    _ = ud 1 X := by rw [hX.2, Matrix.mul_one]
    _ = ud X 1 := ud_comm _ _

/-! ### Transport in norm -/

section Transport

variable {S ι : Type*} (R : ι → FreeGroup S) (φ : FreeGroup S →* Matrix.unitaryGroup Ω ℂ)

/-- Coercion of the assignment to matrices. -/
def phiM (w : FreeGroup S) : Matrix Ω Ω ℂ := (φ w : Matrix.unitaryGroup Ω ℂ)

lemma isU_phi (w : FreeGroup S) : IsU (phiM φ w) := isU_of_mem (φ w).2

lemma phiM_mul (u v : FreeGroup S) : phiM φ (u * v) = phiM φ u * phiM φ v := by
  simp [phiM]

lemma phiM_inv (u : FreeGroup S) : phiM φ u⁻¹ = (phiM φ u)ᴴ := by
  simp [phiM, Matrix.star_eq_conjTranspose]

lemma phiM_one : phiM φ (1 : FreeGroup S) = 1 := by simp [phiM]

variable (e : ℝ)

lemma ud_cell_le (hrel : ∀ k, ud (phiM φ (R k)) 1 ≤ e) (x : FreeGroup S × ι × Bool) :
    ud (phiM φ (x.1 * (if x.2.2 then R x.2.1 else (R x.2.1)⁻¹) * x.1⁻¹)) 1 ≤ e := by
  rcases x with ⟨z, k, bb⟩
  dsimp only
  rw [phiM_mul, phiM_mul, phiM_inv, ud_conj_one (isU_phi φ z)]
  cases bb
  · simp only [Bool.false_eq_true, ite_false]
    rw [phiM_inv, ud_inv_one (isU_phi φ _)]
    exact hrel k
  · simpa using hrel k

/-- **Transport in norm**: a word of area `≤ n` lies within `n e` of `I`. -/
theorem ud_le_of_areaLEGen (hrel : ∀ k, ud (phiM φ (R k)) 1 ≤ e) (he : 0 ≤ e) {w : FreeGroup S}
    {n : ℕ} (h : AreaLEGen R w n) : ud (phiM φ w) 1 ≤ n * e := by
  obtain ⟨cs, hlen, rfl⟩ := h
  have key : ∀ cs : List (FreeGroup S × ι × Bool),
      ud (phiM φ (cs.map fun x => x.1 * (if x.2.2 then R x.2.1 else (R x.2.1)⁻¹) * x.1⁻¹).prod) 1
        ≤ cs.length * e := by
    intro cs
    induction cs with
    | nil => simp [phiM_one, ud_self]
    | cons x cs ih =>
      rw [List.map_cons, List.prod_cons, phiM_mul, List.length_cons]
      set c := phiM φ (x.1 * (if x.2.2 then R x.2.1 else (R x.2.1)⁻¹) * x.1⁻¹)
      set P := phiM φ (cs.map fun x => x.1 * (if x.2.2 then R x.2.1 else (R x.2.1)⁻¹) * x.1⁻¹).prod
      have hc : IsU c := isU_phi φ _
      calc ud (c * P) 1 ≤ ud (c * P) c + ud c 1 := ud_triangle _ _ _
        _ = ud P 1 + ud c 1 := by
            rw [show ud (c * P) c = ud (c * P) (c * 1) by rw [Matrix.mul_one], ud_mul_left hc]
        _ ≤ cs.length * e + e := add_le_add ih (ud_cell_le R φ e hrel x)
        _ = ((cs.length + 1 : ℕ) : ℝ) * e := by push_cast; ring
  exact (key cs).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hlen) he)

end Transport

end Lamps
