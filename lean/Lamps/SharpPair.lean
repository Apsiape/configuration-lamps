import Lamps.UnitaryPhaseReduction
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# The sharp pair-entropy inequality (`SharpPairEntropy`)

`(u+w) ln 2 - (√u - √w)² ≤ η(u) + η(w) - η(u+w)`, the homogeneous form of
`1 - h₂(t) ≤ (1 - 2√(t(1-t)))/ln 2`. With `u = x² b²`, `w = b²` it reads `b² G(x) ≥ 0` for
`G(x) = -2x² log x + (x²+1) log(x²+1) - (x²+1) log 2 + (x-1)²`; `G(1) = 0` and
`G'(x) = 2x h(x)` with `h(x) = log(x²+1) - log 2 - 2 log x + 1 - 1/x`, which is monotone
(`h' = (x-1)²/(x²(x²+1)) ≥ 0`) with `h(1) = 0`.
-/

namespace Lamps

open Real Set Houghton

/-- The inner function `h`. -/
noncomputable def hS (x : ℝ) : ℝ := log (x ^ 2 + 1) - log 2 - 2 * log x + 1 - x⁻¹

/-- The outer function `G`. -/
noncomputable def GS (x : ℝ) : ℝ :=
  -2 * x ^ 2 * log x + (x ^ 2 + 1) * log (x ^ 2 + 1) - log 2 * (x ^ 2 + 1) + (x ^ 2 - 2 * x + 1)

lemma hS_deriv {x : ℝ} (hx : 0 < x) :
    HasDerivAt hS ((x - 1) ^ 2 / (x ^ 2 * (x ^ 2 + 1))) x := by
  have h1 : HasDerivAt (fun x : ℝ => x ^ 2 + 1) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).add_const 1
  have h2 := h1.log (by positivity)
  have h3 := Real.hasDerivAt_log hx.ne'
  have h4 := hasDerivAt_inv hx.ne'
  have h := ((((h2.sub_const (log 2)).sub (h3.const_mul 2)).add_const 1).sub h4)
  convert h using 1
  · funext y; simp only [hS, Pi.sub_apply]
  · field_simp
    ring

lemma hS_one : hS 1 = 0 := by norm_num [hS]

lemma hS_mono : MonotoneOn hS (Ioi 0) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun x => (x - 1) ^ 2 / (x ^ 2 * (x ^ 2 + 1)))
    (convex_Ioi 0) ?_ ?_ ?_
  · intro x hx; exact (hS_deriv hx).continuousAt.continuousWithinAt
  · intro x hx; rw [interior_Ioi] at hx; exact (hS_deriv hx).hasDerivWithinAt
  · intro x hx; rw [interior_Ioi] at hx
    have : (0 : ℝ) < x := hx
    positivity

lemma GS_deriv {x : ℝ} (hx : 0 < x) : HasDerivAt GS (2 * x * hS x) x := by
  have hsq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
  have h1 : HasDerivAt (fun x : ℝ => x ^ 2 + 1) (2 * x) x := hsq.add_const 1
  have hl := h1.log (by positivity)
  have hlx := Real.hasDerivAt_log hx.ne'
  have a1 := (hsq.const_mul (-2)).mul hlx
  have a2 := h1.mul hl
  have a3 := h1.const_mul (log 2)
  have a4 := (hsq.sub ((hasDerivAt_id x).const_mul 2)).add_const 1
  have h := ((a1.add a2).sub a3).add a4
  convert h using 1
  · funext y; simp only [GS, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, id]
  · simp only [hS]
    field_simp
    ring

lemma GS_one : GS 1 = 0 := by norm_num [GS]; ring

lemma GS_cont {a b : ℝ} (ha : 0 < a) : ContinuousOn GS (Icc a b) :=
  fun _ hx => (GS_deriv (lt_of_lt_of_le ha hx.1)).continuousAt.continuousWithinAt

lemma GS_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ GS x := by
  rcases le_total x 1 with h | h
  · have hanti : AntitoneOn GS (Icc x 1) := by
      refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun y => 2 * y * hS y) (convex_Icc x 1) (GS_cont hx) ?_ ?_
      · intro y hy; rw [interior_Icc] at hy
        exact (GS_deriv (lt_trans hx hy.1)).hasDerivWithinAt
      · intro y hy; rw [interior_Icc] at hy
        have hy0 : 0 < y := lt_trans hx hy.1
        have : hS y ≤ 0 := by
          rw [← hS_one]; exact hS_mono hy0 (by norm_num : (0:ℝ) < 1) hy.2.le
        nlinarith
    have := hanti ⟨le_rfl, h⟩ ⟨h, le_rfl⟩ h
    rw [GS_one] at this; exact this
  · have hmono : MonotoneOn GS (Icc 1 x) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun y => 2 * y * hS y) (convex_Icc 1 x) (GS_cont one_pos) ?_ ?_
      · intro y hy; rw [interior_Icc] at hy
        exact (GS_deriv (lt_trans one_pos hy.1)).hasDerivWithinAt
      · intro y hy; rw [interior_Icc] at hy
        have hy0 : 0 < y := lt_trans one_pos hy.1
        have : 0 ≤ hS y := by
          rw [← hS_one]; exact hS_mono (by norm_num : (0:ℝ) < 1) hy0 hy.1.le
        positivity
    have := hmono ⟨le_rfl, h⟩ ⟨h, le_rfl⟩ h
    rw [GS_one] at this; exact this

lemma log_two_le_one : log 2 ≤ 1 := by
  have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith

/-- **The sharp pair-entropy inequality.** -/
theorem sharpPairEntropy : SharpPairEntropy := by
  intro u w hu hw
  rcases hu.eq_or_lt with rfl | hu
  · simp only [Real.sqrt_zero, zero_mul, mul_zero, zero_add, sub_zero, ent, Real.log_zero]
    nlinarith [log_two_le_one]
  rcases hw.eq_or_lt with rfl | hw
  · simp only [Real.sqrt_zero, mul_zero, add_zero, sub_zero, ent, Real.log_zero]
    nlinarith [log_two_le_one]
  set b := Real.sqrt w with hbdef
  have hb : 0 < b := Real.sqrt_pos.mpr hw
  set x := Real.sqrt u / b with hxdef
  have hx : 0 < x := div_pos (Real.sqrt_pos.mpr hu) hb
  have hsu : Real.sqrt u = x * b := by rw [hxdef]; field_simp
  have hu' : u = (x * b) ^ 2 := by rw [← hsu, Real.sq_sqrt hu.le]
  have hw' : w = b ^ 2 := by rw [hbdef, Real.sq_sqrt hw.le]
  rw [hsu]
  rw [hu', hw']
  have l1 : log ((x * b) ^ 2) = 2 * log x + 2 * log b := by
    rw [Real.log_pow, Real.log_mul hx.ne' hb.ne']; push_cast; ring
  have l2 : log ((x * b) ^ 2 + b ^ 2) = log (x ^ 2 + 1) + 2 * log b := by
    rw [show (x * b) ^ 2 + b ^ 2 = (x ^ 2 + 1) * b ^ 2 by ring,
      Real.log_mul (by positivity) (by positivity), Real.log_pow]; push_cast; ring
  have l3 : log (b ^ 2) = 2 * log b := by rw [Real.log_pow]; push_cast; ring
  simp only [ent, l1, l2, l3]
  have hG := mul_nonneg (sq_nonneg b) (GS_nonneg hx)
  have key : -((x * b) ^ 2 * (2 * log x + 2 * log b)) + -(b ^ 2 * (2 * log b)) -
      -(((x * b) ^ 2 + b ^ 2) * (log (x ^ 2 + 1) + 2 * log b)) -
      (log 2 * ((x * b) ^ 2 + b ^ 2) - ((x * b) ^ 2 + b ^ 2 - 2 * (x * b * b))) = b ^ 2 * GS x := by
    simp only [GS]; ring
  linarith

end Lamps
