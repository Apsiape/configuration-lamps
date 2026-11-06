import Lamps.UnitaryCriterion
import FiniteLean.QIT.Integral

/-!
# Lemma `lem:imp-s3round`: exact `S₃` rounding of unitaries

For a unitary `U`, `L = (U + Uᴴ)/2` and `R = (U - Uᴴ)/(2i)` are commuting Hermitian matrices and
`U = L + iR`.  For `r : ℂ → ℂ`, `rnd r U = ∑_{a,b} r(a + ib) E_{ab}` (joint spectral calculus
`QIT.jJ` of `L, R`, extended to complex functions by `jC`).  Rounding to `±1`
(`sgnRe`) and to cube roots of unity (`cr`, conjugation-equivariant) gives the lemma.
-/

namespace Lamps

open Matrix QIT Complex

section Joint

variable {m : Type} [Fintype m] [DecidableEq m] {L R : Matrix m m ℂ}

/-- Complex joint calculus. -/
noncomputable def jC (L R : Matrix m m ℂ) (F : ℝ → ℝ → ℂ) : Matrix m m ℂ :=
  jJ L R (fun a b => (F a b).re) + I • jJ L R (fun a b => (F a b).im)

lemma jJ_zero : jJ L R (fun _ _ => 0) = 0 := by simp [jJ]

lemma jJ_neg (G : ℝ → ℝ → ℝ) : jJ L R (fun a b => -G a b) = -jJ L R G := by
  have := jJ_smul (L := L) (R := R) (-1) G
  simp only [neg_one_mul, neg_smul, one_smul] at this
  exact this.symm

lemma jC_real (G : ℝ → ℝ → ℝ) : jC L R (fun a b => (G a b : ℂ)) = jJ L R G := by
  simp [jC, jJ_zero]

lemma jC_mul (hLR : Commute L R) (F G : ℝ → ℝ → ℂ) :
    jC L R F * jC L R G = jC L R (fun a b => F a b * G a b) := by
  set X1 := jJ L R (fun a b => (F a b).re)
  set Y1 := jJ L R (fun a b => (F a b).im)
  set X2 := jJ L R (fun a b => (G a b).re)
  set Y2 := jJ L R (fun a b => (G a b).im)
  have e1 : jC L R F * jC L R G = (X1 * X2 - Y1 * Y2) + I • (X1 * Y2 + Y1 * X2) := by
    simp only [jC, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      I_mul_I, neg_one_smul, smul_add, X1, X2, Y1, Y2]
    abel
  rw [e1, jJ_mul hLR, jJ_mul hLR, jJ_mul hLR, jJ_mul hLR, jJ_sub, jJ_add]
  simp only [jC, Complex.mul_re, Complex.mul_im]

lemma jC_congr (F G : ℝ → ℝ → ℂ) (h : ∀ a ∈ spf L, ∀ b ∈ spf R, F a b = G a b) :
    jC L R F = jC L R G := by
  unfold jC
  rw [jJ_congr _ _ (fun a ha b hb => by rw [h a ha b hb]),
    jJ_congr (fun a b => (F a b).im) _ (fun a ha b hb => by rw [h a ha b hb])]

lemma jC_one (hL : IsSelfAdjoint L) (hR : IsSelfAdjoint R) : jC L R (fun _ _ => 1) = 1 := by
  simp [jC, jJ_one hL hR, jJ_zero]

lemma jC_sub (F G : ℝ → ℝ → ℂ) : jC L R F - jC L R G = jC L R (fun a b => F a b - G a b) := by
  simp only [jC, Complex.sub_re, Complex.sub_im, ← jJ_sub, smul_sub]
  abel

lemma sproj_sa (A : Matrix m m ℂ) (a : ℝ) : (sproj A a)ᴴ = sproj A a := by
  have : IsSelfAdjoint (sproj A a) := cfc_predicate _ _
  exact this

lemma jE_star (hLR : Commute L R) (a b : ℝ) : (jE L R a b)ᴴ = jE L R a b := by
  have hc : Commute (sproj R b) (sproj L a) := by
    have h1 : Commute (sproj L a) R := hLR.cfc_real (ind a)
    exact (h1.symm.cfc_real (ind b))
  unfold jE
  rw [conjTranspose_mul, sproj_sa, sproj_sa, hc.eq]

lemma jJ_star (hLR : Commute L R) (G : ℝ → ℝ → ℝ) : (jJ L R G)ᴴ = jJ L R G := by
  unfold jJ
  simp only [conjTranspose_sum, conjTranspose_smul, star_trivial, jE_star hLR]

lemma jC_star (hLR : Commute L R) (F : ℝ → ℝ → ℂ) :
    (jC L R F)ᴴ = jC L R (fun a b => star (F a b)) := by
  simp only [jC, conjTranspose_add, conjTranspose_smul, jJ_star hLR, Complex.star_def,
    Complex.conj_re, Complex.conj_im, conj_I, jJ_neg, smul_neg, neg_smul]

lemma trace_jJ_re (G : ℝ → ℝ → ℝ) :
    (jJ L R G).trace.re = ∑ a ∈ spf L, ∑ b ∈ spf R, G a b * (jE L R a b).trace.re := by
  unfold jJ
  simp only [trace_sum, trace_smul, Complex.re_sum, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

lemma jE_trace_nonneg (hLR : Commute L R) (a b : ℝ) : 0 ≤ (jE L R a b).trace.re := by
  have hidem : jE L R a b * (jE L R a b)ᴴ = jE L R a b := by
    rw [jE_star hLR, jE_mul hLR, if_pos rfl, if_pos rfl]
  have h := nsq_eq_trace (jE L R a b)
  rw [hidem] at h
  rw [← h, Complex.ofReal_re]
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

lemma jE_eq_zero_of_trace (hLR : Commute L R) (a b : ℝ) (h : (jE L R a b).trace.re = 0) :
    jE L R a b = 0 := by
  have hidem : jE L R a b * (jE L R a b)ᴴ = jE L R a b := by
    rw [jE_star hLR, jE_mul hLR, if_pos rfl, if_pos rfl]
  have h2 := nsq_eq_trace (jE L R a b)
  rw [hidem] at h2
  have h3 : Houghton.nsq (jE L R a b) = 0 := by
    have := congrArg Complex.re h2
    rw [Complex.ofReal_re] at this
    rw [this, h]
  ext i j
  have hs := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Finset.sum_nonneg fun _ _ =>
    Complex.normSq_nonneg _)).1 h3 i (Finset.mem_univ _)
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Complex.normSq_nonneg _)).1 hs j
    (Finset.mem_univ _)
  simpa using this

lemma jJ_mul_jE (hLR : Commute L R) (G : ℝ → ℝ → ℝ) {a b : ℝ} (ha : a ∈ spf L)
    (hb : b ∈ spf R) : jJ L R G * jE L R a b = G a b • jE L R a b := by
  unfold jJ
  rw [Finset.sum_mul, Finset.sum_eq_single_of_mem a ha]
  · rw [Finset.sum_mul, Finset.sum_eq_single_of_mem b hb]
    · rw [smul_mul_assoc, jE_mul hLR, if_pos rfl, if_pos rfl]
    · intro y _ hy
      rw [smul_mul_assoc, jE_mul hLR, if_pos rfl, if_neg hy, smul_zero]
  · intro x _ hx
    rw [Finset.sum_mul]
    exact Finset.sum_eq_zero fun y _ => by rw [smul_mul_assoc, jE_mul hLR, if_neg hx, smul_zero]

/-- Comparison of `‖jC F‖²` along the support. -/
lemma nsq_jC_le (hLR : Commute L R) (F G : ℝ → ℝ → ℂ) (P : ℝ → ℝ → Prop)
    (hP : ∀ a ∈ spf L, ∀ b ∈ spf R, jE L R a b ≠ 0 → P a b)
    (hFG : ∀ a b, P a b → Complex.normSq (F a b) ≤ Complex.normSq (G a b)) :
    Houghton.nsq (jC L R F) ≤ Houghton.nsq (jC L R G) := by
  have key : ∀ H : ℝ → ℝ → ℂ, Houghton.nsq (jC L R H) =
      ∑ a ∈ spf L, ∑ b ∈ spf R, Complex.normSq (H a b) * (jE L R a b).trace.re := by
    intro H
    have h := nsq_eq_trace (jC L R H)
    rw [jC_star hLR, jC_mul hLR] at h
    have e : jC L R (fun a b => H a b * star (H a b)) =
        jJ L R (fun a b => Complex.normSq (H a b)) := by
      rw [← jC_real]
      congr 1
      funext a b
      rw [Complex.star_def, Complex.mul_conj]
    rw [e] at h
    have := congrArg Complex.re h
    rw [Complex.ofReal_re] at this
    rw [this, trace_jJ_re]
  rw [key, key]
  refine Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => ?_
  by_cases h0 : jE L R a b = 0
  · simp [h0]
  · exact mul_le_mul_of_nonneg_right (hFG a b (hP a ha b hb h0)) (jE_trace_nonneg hLR a b)

end Joint

end Lamps
