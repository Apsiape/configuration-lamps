import Lamps.UnitaryCriterion
import Houghton.Analysis.Sector

/-!
# The numerics `UnitaryMargin` of the "Moreover" clause of Theorem `thm:criterion`

Averaging over copies: for `q₀ > 0` the tangent-line bound `h₂(q) ≤ q₀/ln 2 + q log₂(1/q₀)`
(`h2_le_tangent`, from `ln x ≤ x - 1`) makes `χ` linear in `a_i`, so only `∑ a_i` enters
(a uniform per-copy bound would not suffice). With `L = log₂(1/Δ)`, `K_Δ² = 80000 (1+L)/Δ²` and
`q₀ = (2/3)·3200/(3K_Δ²) = 2Δ²/(225(1+L))`:
`9/K_Δ ≤ Δ/31`, `q₀ (1/ln 2 + 1 + log₂(1/q₀)) ≤ 4Δ²/45`, and
`300/961 - 1936/240000 - 4/45 - 1/225 ≥ 1/12`.
-/

namespace Lamps

open Finset

/-- Tangent-line bound for the binary entropy (bits): `h₂(q) ≤ q₀/ln 2 + q log₂(1/q₀)`. -/
theorem h2_le_tangent {q q₀ : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hq₀ : 0 < q₀) :
    Houghton.h2 q ≤ q₀ / Real.log 2 + q * Real.logb 2 (1 / q₀) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have e1 : Houghton.h2 q = (-(q * Real.log q) - (1 - q) * Real.log (1 - q)) / Real.log 2 := by
    simp only [Houghton.h2, Real.logb]; ring
  have e2 : q₀ / Real.log 2 + q * Real.logb 2 (1 / q₀) =
      (q₀ - q * Real.log q₀) / Real.log 2 := by
    simp only [Real.logb, one_div, Real.log_inv]; ring
  rw [e1, e2]
  apply div_le_div_of_nonneg_right _ hl2.le
  -- `-(1-q) log(1-q) ≤ q`
  have h1 : -q ≤ (1 - q) * Real.log (1 - q) := by
    have := Real.one_sub_inv_le_log_of_pos (show 0 < 1 - q by linarith)
    have h' : (1 - q) * (1 - (1 - q)⁻¹) = -q := by field_simp; ring
    nlinarith [mul_le_mul_of_nonneg_left this (show 0 ≤ 1 - q by linarith)]
  -- `q log q₀ - q log q ≤ q₀ - q`
  have h2 : q * Real.log q₀ - q * Real.log q ≤ q₀ - q := by
    rcases eq_or_lt_of_le hq0 with h0 | hpos
    · subst h0; simp; linarith
    · have := Real.log_le_sub_one_of_pos (show 0 < q₀ / q by positivity)
      rw [Real.log_div hq₀.ne' hpos.ne'] at this
      have h' : q * (q₀ / q - 1) = q₀ - q := by field_simp
      nlinarith [mul_le_mul_of_nonneg_left this hpos.le]
  linarith

/-- The constants of `K_Δ`, with `L = log₂(1/Δ)`. -/
theorem kd_facts {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ1 : Δ ≤ 1) :
    0 ≤ Real.logb 2 (1 / Δ) ∧ 9 / Kd Δ ≤ Δ / 31 ∧ 0 ≤ 9 / Kd Δ ∧
      3 * Kd Δ ^ 2 = 240000 * (1 + Real.logb 2 (1 / Δ)) / Δ ^ 2 := by
  have hΔinv : 1 ≤ 1 / Δ := by rw [le_div_iff₀ hΔ0]; linarith
  have hL0 : 0 ≤ Real.logb 2 (1 / Δ) := Real.logb_nonneg (by norm_num) hΔinv
  obtain ⟨L, hL⟩ : ∃ L, L = Real.logb 2 (1 / Δ) := ⟨_, rfl⟩
  rw [← hL] at hL0 ⊢
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt (80000 * (1 + L)) := ⟨_, rfl⟩
  have hs2 : s ^ 2 = 80000 * (1 + L) := by rw [hs]; exact Real.sq_sqrt (by positivity)
  have hs279 : 279 ≤ s := by
    rw [hs]; apply Real.le_sqrt_of_sq_le; linarith
  have hK : Kd Δ = s / Δ := by rw [hs, hL]; rfl
  refine ⟨hL0, ?_, by rw [hK]; positivity, by rw [hK, div_pow, hs2]; ring⟩
  rw [hK, div_div_eq_mul_div, div_le_div_iff₀ (by linarith) (by norm_num)]
  nlinarith

/-- `log₂(1/q₀) ≤ 7 + 4L` for `q₀ = 2Δ²/(225(1+L))`. -/
theorem logb_q0_le {Δ : ℝ} (hΔ0 : 0 < Δ) (hL0 : 0 ≤ Real.logb 2 (1 / Δ)) :
    Real.logb 2 (1 / (2 * Δ ^ 2 / (225 * (1 + Real.logb 2 (1 / Δ))))) ≤
      7 + 4 * Real.logb 2 (1 / Δ) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2h := Houghton.log_two_gt_half
  obtain ⟨L, hL⟩ : ∃ L, L = Real.logb 2 (1 / Δ) := ⟨_, rfl⟩
  rw [← hL] at hL0 ⊢
  have hLlog : Real.log (1 / Δ) = L * Real.log 2 := by
    rw [hL, Real.logb, div_mul_cancel₀ _ hl2.ne']
  have e : 1 / (2 * Δ ^ 2 / (225 * (1 + L))) = 225 / 2 * (1 + L) * (1 / Δ) ^ 2 := by
    field_simp
  have hlog : Real.log (1 / (2 * Δ ^ 2 / (225 * (1 + L)))) =
      Real.log (225 / 2) + Real.log (1 + L) + 2 * Real.log (1 / Δ) := by
    rw [e, Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num)
      (by positivity), Real.log_pow]; push_cast; ring
  have h128 : Real.log (225 / 2) ≤ 7 * Real.log 2 := by
    rw [← Real.log_rpow (by norm_num)]
    exact Real.log_le_log (by norm_num) (by norm_num)
  have h1L : Real.log (1 + L) ≤ L := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + L by linarith); linarith
  rw [Real.logb, div_le_iff₀ hl2, hlog, hLlog]
  have : L ≤ 2 * L * Real.log 2 := by nlinarith
  nlinarith

/-- **The numerics of the unitary counting criterion** (`UnitaryMargin`). -/
theorem unitaryMargin : UnitaryMargin := by
  intro N Δ d a b hΔ0 hΔ1 hd ha0 ha1 hsa hb
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2h := Houghton.log_two_gt_half
  obtain ⟨hL0, h9, h9', hK2⟩ := kd_facts hΔ0 hΔ1
  have hlgb := logb_q0_le hΔ0 hL0
  obtain ⟨L, hL⟩ : ∃ L, L = Real.logb 2 (1 / Δ) := ⟨_, rfl⟩
  rw [← hL] at hL0 hK2 hlgb
  obtain ⟨q₀, hq₀⟩ : ∃ q₀, q₀ = 2 * Δ ^ 2 / (225 * (1 + L)) := ⟨_, rfl⟩
  rw [← hq₀] at hlgb
  obtain ⟨lg, hlgdef⟩ : ∃ lg, lg = Real.logb 2 (1 / q₀) := ⟨_, rfl⟩
  rw [← hlgdef] at hlgb
  have hq₀pos : 0 < q₀ := by rw [hq₀]; positivity
  have hΔ2 : 0 < Δ ^ 2 := by positivity
  have hdlow : ∀ i, 900 / 961 * Δ ^ 2 ≤ d i := by
    intro i
    refine le_trans ?_ (hd i)
    have h1 : 30 / 31 * Δ ≤ Δ - 9 / Kd Δ := by linarith
    have h2 : 0 ≤ 30 / 31 * Δ := by positivity
    have := mul_le_mul h1 h1 h2 (h2.trans h1)
    linarith only [this]
  have hA : 3200 / (3 * Kd Δ ^ 2) = 3 / 2 * q₀ := by
    rw [hK2, hq₀]; field_simp; ring
  have hB : 1936 / (3 * Kd Δ ^ 2) ≤ 1936 / 240000 * Δ ^ 2 := by
    rw [hK2, div_div_eq_mul_div, div_le_iff₀ (by positivity)]
    have : 0 ≤ 1936 * Δ ^ 2 * L := by positivity
    linarith only [this]
  have hq₀le : q₀ / 2 ≤ 1 / 225 * Δ ^ 2 := by
    rw [hq₀, div_div, div_le_iff₀ (by positivity)]
    have : 0 ≤ Δ ^ 2 * L := by positivity
    linarith only [this]
  have hinvl2 : 1 / Real.log 2 ≤ 2 := by rw [div_le_iff₀ hl2]; linarith
  have hcoef : q₀ * (1 / Real.log 2 + 1 + lg) ≤ 4 / 45 * Δ ^ 2 := by
    have : q₀ * (1 / Real.log 2 + 1 + lg) ≤ q₀ * (10 * (1 + L)) := by
      apply mul_le_mul_of_nonneg_left _ hq₀pos.le; linarith
    refine this.trans (le_of_eq ?_)
    rw [hq₀]; field_simp; ring
  -- pointwise linear lower bound
  obtain ⟨α, hα⟩ : ∃ α, α = (300 / 961 - 1936 / 240000) * Δ ^ 2 - q₀ / Real.log 2 := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β, β = 1 / 3 + 2 / 3 * (1 + lg) := ⟨_, rfl⟩
  have hpt : ∀ i, α - β * a i ≤
      (d i - a i) / 3 - b i / (2 * Real.log 2) - chi (a i) := by
    intro i
    have hmin : min (2 / 3 * a i) (2 / 3) = 2 / 3 * a i :=
      min_eq_left (by linarith [ha1 i])
    have hchi : chi (a i) ≤ q₀ / Real.log 2 + 2 / 3 * a i * (1 + lg) := by
      rw [chi, hmin]
      have := h2_le_tangent (q := 2 / 3 * a i) (by linarith [ha0 i]) (by linarith [ha1 i])
        hq₀pos
      rw [← hlgdef] at this; linarith
    have hbi : b i / (2 * Real.log 2) ≤ 1936 / 240000 * Δ ^ 2 := by
      have hb' := (hb i).trans hB
      have h2l : 1 ≤ 2 * Real.log 2 := by linarith
      rcases le_total (b i) 0 with hneg | hpos
      · have : b i / (2 * Real.log 2) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hneg (by linarith)
        have : 0 ≤ 1936 / 240000 * Δ ^ 2 := by positivity
        linarith
      · exact (div_le_self hpos h2l).trans hb'
    have := hdlow i
    rw [hα, hβ]
    linarith only [hchi, hbi, this]
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ (univ : Finset (Fin N))) => hpt i
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hsum
  refine le_trans ?_ hsum
  have hlg0 : 0 ≤ lg := by
    rw [hlgdef]; apply Real.logb_nonneg (by norm_num)
    rw [le_div_iff₀ hq₀pos]
    have : Δ ^ 2 ≤ 1 := by nlinarith
    linarith
  have hβ0 : 0 ≤ β := by rw [hβ]; linarith
  have hsa' : ∑ i, a i ≤ N * (3 / 2 * q₀) := by rw [← hA]; exact hsa
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have key : Δ ^ 2 / 12 ≤ α - β * (3 / 2 * q₀) := by
    have e : β * (3 / 2 * q₀) = q₀ * (1 / Real.log 2 + 1 + lg) + q₀ / 2 - q₀ / Real.log 2 := by
      rw [hβ]; field_simp; ring
    rw [e, hα]
    linarith only [hcoef, hq₀le, hΔ2]
  have h1 := mul_le_mul_of_nonneg_left key hN0
  have h2 := mul_le_mul_of_nonneg_left hsa' hβ0
  calc (N : ℝ) * Δ ^ 2 / 12 = N * (Δ ^ 2 / 12) := by ring
    _ ≤ N * (α - β * (3 / 2 * q₀)) := h1
    _ = N * α - β * (N * (3 / 2 * q₀)) := by ring
    _ ≤ N * α - β * ∑ i, a i := by linarith only [h2]

end Lamps
