import Lamps.UnitaryRoundSpec
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Pointwise rounding to roots of unity (`RoundFn 2`, `RoundFn 3`)

* `k = 2`: `r z = 1` if `Re z ≥ 0`, else `-1`; on the circle `|z² - 1|² = 4(1 - a²)`.
* `k = 3`: `r z = 1` if `Re z ≥ 1/2` or `Im z = 0`; otherwise `ω = -1/2 + (√3/2) i` if `Im z > 0` and
  `ω̄` if `Im z < 0`. On the circle `|z³ - 1|² = 2(1 - a)(2a + 1)²` and
  `|ω - z|² (2 - 2a)(2 + a + √3 b) = |z³ - 1|²`, with both extra factors `≥ 1`.
-/

namespace Lamps

open Complex

theorem normSq_sq_sub_one {z : ℂ} (hz : z.re * z.re + z.im * z.im = 1) :
    normSq (z ^ 2 - 1) = 4 * (1 - z.re ^ 2) := by
  have e : normSq (z ^ 2 - 1) = (z.re ^ 2 - z.im ^ 2 - 1) ^ 2 + 4 * z.re ^ 2 * z.im ^ 2 := by
    simp only [normSq_apply, pow_two, sub_re, sub_im, mul_re, mul_im, one_re, one_im]; ring
  have hb : z.im ^ 2 = 1 - z.re ^ 2 := by nlinarith
  rw [e, hb]; ring

theorem normSq_cube_sub_one {z : ℂ} (hz : z.re * z.re + z.im * z.im = 1) :
    normSq (z ^ 3 - 1) = 2 * (1 - z.re) * (2 * z.re + 1) ^ 2 := by
  have e : normSq (z ^ 3 - 1) =
      (z.re ^ 3 - 3 * z.re * z.im ^ 2 - 1) ^ 2 + z.im ^ 2 * (3 * z.re ^ 2 - z.im ^ 2) ^ 2 := by
    simp only [normSq_apply, pow_succ, pow_zero, one_mul, sub_re, sub_im, mul_re, mul_im, one_re,
      one_im]; ring
  have hb : z.im ^ 2 = 1 - z.re ^ 2 := by nlinarith
  rw [e, hb]; ring

/-- The rounding to `±1`. -/
noncomputable def r2 (z : ℂ) : ℂ := if 0 ≤ z.re then 1 else -1

theorem roundFn_two : ∃ r, RoundFn 2 r := by
  refine ⟨r2, fun z hz => ?_⟩
  rw [normSq_apply] at hz
  have h2 := normSq_sq_sub_one hz
  have ha1 : z.re ≤ 1 := by nlinarith [sq_nonneg z.im]
  have ha1' : -1 ≤ z.re := by nlinarith [sq_nonneg z.im]
  by_cases ha : 0 ≤ z.re
  · have hr : r2 z = 1 := by simp [r2, ha]
    have hr' : r2 ((starRingEnd ℂ) z) = 1 := by simp [r2, ha]
    rw [hr, hr', h2]
    refine ⟨by simp, by simp, ?_, by simp⟩
    rw [normSq_apply]
    simp only [sub_re, one_re, sub_im, one_im]
    nlinarith [mul_nonneg (sub_nonneg.mpr ha1) (show (0:ℝ) ≤ 1 + 2 * z.re by linarith)]
  · have hr : r2 z = -1 := by simp [r2, ha]
    have hr' : r2 ((starRingEnd ℂ) z) = -1 := by simp [r2, ha]
    rw [hr, hr', h2]
    refine ⟨by simp, by norm_num, ?_, by simp⟩
    rw [normSq_apply]
    simp only [sub_re, neg_re, one_re, sub_im, neg_im, one_im]
    push Not at ha
    nlinarith [mul_nonneg (show (0:ℝ) ≤ 1 + z.re by linarith)
      (show (0:ℝ) ≤ 1 - 2 * z.re by linarith)]

/-- `ω_σ = -1/2 + (σ/2) i` (`σ = ±√3`). -/
noncomputable def om (σ : ℝ) : ℂ := ⟨-1 / 2, σ / 2⟩

theorem conj_om (σ : ℝ) : (starRingEnd ℂ) (om σ) = om (-σ) := by
  apply Complex.ext <;> simp [om, neg_div]

theorem normSq_om {σ : ℝ} (hσ : σ ^ 2 = 3) : normSq (om σ) = 1 := by
  rw [normSq_apply]; simp only [om]; nlinarith

theorem om_cube {σ : ℝ} (hσ : σ ^ 2 = 3) : om σ ^ 3 = 1 := by
  apply Complex.ext
  · simp only [om, pow_succ, pow_zero, one_mul, mul_re, mul_im, one_re]
    linear_combination (3 / 8 : ℝ) * hσ
  · simp only [om, pow_succ, pow_zero, one_mul, mul_re, mul_im, one_im]
    linear_combination (-σ / 8) * hσ

/-- The key estimate in the `ω` case: `|ω_σ - z|² ≤ |z³ - 1|²` when `Re z < 1/2`, `σ Im z ≥ 0`. -/
theorem om_close {σ : ℝ} (hσ : σ ^ 2 = 3) {z : ℂ} (hz : z.re * z.re + z.im * z.im = 1)
    (ha : z.re < 1 / 2) (hσb : 0 ≤ σ * z.im) : normSq (om σ - z) ≤ normSq (z ^ 3 - 1) := by
  rw [normSq_cube_sub_one hz]
  have hX : normSq (om σ - z) = 2 + z.re - σ * z.im := by
    rw [normSq_apply]; simp only [om, sub_re, sub_im]
    linear_combination hz + (1 / 4 : ℝ) * hσ
  have hprod : (2 + z.re - σ * z.im) * (2 + z.re + σ * z.im) = (2 * z.re + 1) ^ 2 := by
    have hb : z.im ^ 2 = 1 - z.re ^ 2 := by nlinarith
    have : (σ * z.im) ^ 2 = 3 * (1 - z.re ^ 2) := by rw [mul_pow, hσ, hb]
    nlinarith
  have ha1 : -1 ≤ z.re := by nlinarith [sq_nonneg z.im]
  have hX0 : 0 ≤ 2 + z.re - σ * z.im := by rw [← hX]; exact normSq_nonneg _
  have hf1 : 1 ≤ 2 + z.re + σ * z.im := by linarith
  have hf2 : 1 ≤ 2 * (1 - z.re) := by linarith
  have hff : 1 ≤ (2 + z.re + σ * z.im) * (2 * (1 - z.re)) := by nlinarith
  have := mul_le_mul_of_nonneg_left hff hX0
  rw [hX]
  calc 2 + z.re - σ * z.im = (2 + z.re - σ * z.im) * 1 := by ring
    _ ≤ (2 + z.re - σ * z.im) * ((2 + z.re + σ * z.im) * (2 * (1 - z.re))) := this
    _ = 2 * (1 - z.re) * (2 * z.re + 1) ^ 2 := by rw [← hprod]; ring

/-- The rounding to cube roots of unity. -/
noncomputable def r3 (z : ℂ) : ℂ :=
  if 1 / 2 ≤ z.re ∨ z.im = 0 then 1 else if 0 < z.im then om (Real.sqrt 3) else om (-Real.sqrt 3)

theorem roundFn_three : ∃ r, RoundFn 3 r := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs' : (-Real.sqrt 3) ^ 2 = 3 := by rw [neg_sq, hs]
  have hs0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  refine ⟨r3, fun z hz => ?_⟩
  rw [normSq_apply] at hz
  have h3 := normSq_cube_sub_one hz
  have ha1 : z.re ≤ 1 := by nlinarith [sq_nonneg z.im]
  have ha1' : -1 ≤ z.re := by nlinarith [sq_nonneg z.im]
  by_cases hc : 1 / 2 ≤ z.re ∨ z.im = 0
  · have hc' : 1 / 2 ≤ ((starRingEnd ℂ) z).re ∨ ((starRingEnd ℂ) z).im = 0 := by
      simpa using hc
    have hr : r3 z = 1 := by unfold r3; rw [ite_eq_left_iff]; intro h; exact absurd hc h
    have hr' : r3 ((starRingEnd ℂ) z) = 1 := by
      unfold r3; rw [ite_eq_left_iff]; intro h; exact absurd hc' h
    rw [hr, hr', h3]
    refine ⟨by simp, by simp, ?_, by simp⟩
    rw [normSq_apply]
    simp only [sub_re, one_re, sub_im, one_im]
    rcases hc with ha | hb
    · nlinarith
    · have : z.re * z.re = 1 := by rw [hb] at hz; linarith
      have : (1 - z.re) * (z.re + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h | h
      · have : z.re = 1 := by linarith
        rw [hb, this]; norm_num
      · have : z.re = -1 := by linarith
        rw [hb, this]; norm_num
  · push Not at hc
    obtain ⟨ha, hb⟩ := hc
    have hc' : ¬(1 / 2 ≤ ((starRingEnd ℂ) z).re ∨ ((starRingEnd ℂ) z).im = 0) := by
      simp only [conj_re, conj_im, neg_eq_zero, not_or, not_le]; exact ⟨ha, hb⟩
    have hcon : ¬(1 / 2 ≤ z.re ∨ z.im = 0) := by
      simp only [not_or, not_le]; exact ⟨ha, hb⟩
    rcases lt_or_gt_of_ne hb with hneg | hpos
    · have hnp : ¬(0 < z.im) := by linarith
      have hr : r3 z = om (-Real.sqrt 3) := by unfold r3; rw [if_neg hcon, if_neg hnp]
      have hr' : r3 ((starRingEnd ℂ) z) = om (Real.sqrt 3) := by
        unfold r3; rw [if_neg hc', if_pos (by simp only [conj_im]; linarith)]
      rw [hr, hr', conj_om, neg_neg]
      exact ⟨normSq_om hs', om_cube hs', om_close hs' hz ha (by nlinarith), rfl⟩
    · have hnp : ¬(z.im < 0) := by linarith
      have hr : r3 z = om (Real.sqrt 3) := by unfold r3; rw [if_neg hcon, if_pos hpos]
      have hr' : r3 ((starRingEnd ℂ) z) = om (-Real.sqrt 3) := by
        unfold r3; rw [if_neg hc', if_neg (by simp only [conj_im]; linarith)]
      rw [hr, hr', conj_om]
      exact ⟨normSq_om hs, om_cube hs, om_close hs hz ha (by nlinarith), rfl⟩

end Lamps
