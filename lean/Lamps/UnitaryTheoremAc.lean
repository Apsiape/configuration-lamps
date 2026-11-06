import Lamps.UnitaryTheoremA
import Lamps.UnitaryMargin
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Theorem A(c) (unitary models of the lamps group): the asymptotic form

From `theoremA_c_model` (S1) and the numerics `unitaryMargin`: for `0 < Δ ≤ 1` there are
`c_Δ, e_Δ > 0` with `log₂ D ≥ c_Δ e⁻² / (log₂(1/e))^{2κ}`, `κ = 2 + p_H`, for `0 < e ≤ e_Δ`.

Choice of `N` (a variant of the paper's `⌊log Y − 2κ log log Y⌋`): with `x = 1/e`, `ℓ = log₂ x`,
`K C₁ = K_Δ (C + 4)` and `X = x² / ((K C₁)² (2ℓ)^{2κ})`, take `N = ⌊log₂ ⌊X⌋⌋`; then
`2^N ≤ X ≤ x²` gives `N ≤ 2ℓ`, hence `2^N N^{2κ} ≤ (K C₁ e)^{-2}`, the hypothesis of the unitary
criterion; and `X ≥ 2` for `e ≤ e_Δ` since `(log x)^{2κ} = o(x²)`.
-/

namespace Lamps

/-- `(log x)^P ≤ A x²` for large `x`. -/
theorem log_rpow_le_sq (A P : ℝ) (hA : 0 < A) :
    ∃ x₀ : ℝ, ∀ x ≥ x₀, Real.log x ^ P ≤ A * x ^ 2 := by
  have h := (isLittleO_log_rpow_rpow_atTop P (show (0 : ℝ) < 2 by norm_num)).bound hA
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp h
  refine ⟨max x₀ 1, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := le_of_max_le_right hx
  have := hx₀ x (le_of_max_le_left hx)
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hx1) _),
    abs_of_nonneg (Real.rpow_nonneg (by linarith) _), Real.rpow_two] at this
  exact this

/-- Choice of `N`: for `X ≥ 2`, `X ≤ x²`, `ℓ = log₂ x`, `N = ⌊log₂ ⌊X⌋⌋` satisfies `N ≥ 1`,
`2^N ≤ X < 2^{N+1}` and `N ≤ 2ℓ`. -/
theorem exists_N_of_X {X x : ℝ} (hX2 : 2 ≤ X) (hXx : X ≤ x ^ 2) (hx0 : 0 < x) :
    ∃ N : ℕ, 1 ≤ N ∧ (2 : ℝ) ^ N ≤ X ∧ X < 2 * (2 : ℝ) ^ N ∧ (N : ℝ) ≤ 2 * Real.logb 2 x := by
  obtain ⟨n0, hn0⟩ : ∃ n0, n0 = ⌊X⌋₊ := ⟨_, rfl⟩
  have hn02 : 2 ≤ n0 := by rw [hn0]; exact Nat.le_floor (by simpa using hX2)
  refine ⟨Nat.log 2 n0, Nat.log_pos (by norm_num) hn02, ?_, ?_, ?_⟩
  · have : 2 ^ Nat.log 2 n0 ≤ n0 := Nat.pow_log_le_self 2 (by omega)
    have h' : ((2 ^ Nat.log 2 n0 : ℕ) : ℝ) ≤ X :=
      (Nat.cast_le.mpr this).trans (by rw [hn0]; exact Nat.floor_le (by linarith))
    simpa using h'
  · have h1 : n0 < 2 ^ (Nat.log 2 n0 + 1) := Nat.lt_pow_succ_log_self (by norm_num) n0
    have h2 : X < n0 + 1 := by rw [hn0]; exact Nat.lt_floor_add_one X
    have h3 : (n0 : ℝ) + 1 ≤ ((2 ^ (Nat.log 2 n0 + 1) : ℕ) : ℝ) := by exact_mod_cast h1
    have h4 : ((2 ^ (Nat.log 2 n0 + 1) : ℕ) : ℝ) = 2 * (2 : ℝ) ^ Nat.log 2 n0 := by
      push_cast; ring
    linarith
  · have h2N : (2 : ℝ) ^ Nat.log 2 n0 ≤ X := by
      have : 2 ^ Nat.log 2 n0 ≤ n0 := Nat.pow_log_le_self 2 (by omega)
      have h' : ((2 ^ Nat.log 2 n0 : ℕ) : ℝ) ≤ X :=
        (Nat.cast_le.mpr this).trans (by rw [hn0]; exact Nat.floor_le (by linarith))
      simpa using h'
    rw [← Real.rpow_le_rpow_left_iff (show (1 : ℝ) < 2 by norm_num), Real.rpow_natCast,
      show 2 * Real.logb 2 x = Real.logb 2 x * 2 by ring, Real.rpow_mul (by norm_num),
      Real.rpow_logb (by norm_num) (by norm_num) hx0, Real.rpow_two]
    linarith

/-- The hypothesis of the unitary criterion from `2^N ≤ X`, `N^{2κ} ≤ (2ℓ)^{2κ}`. -/
theorem unitary_cond {K C e X Q N2 Nκ : ℝ} (N : ℕ) (hK : 0 ≤ K) (hC : 0 < C) (he : 0 ≤ e)
    (hNκ1 : 1 ≤ Nκ) (h2N : (2 : ℝ) ^ N ≤ X) (hNP : Nκ ^ 2 ≤ Q)
    (hXQ : (K * (C + 4)) ^ 2 * X * Q * e ^ 2 = 1) (hN2 : N2 = (⌊C * Nκ⌋₊ + 4 : ℕ)) :
    K * Real.sqrt ((2 : ℝ) ^ N) * N2 * e ≤ 1 := by
  have hm : N2 ≤ (C + 4) * Nκ := by
    rw [hN2]; push_cast
    have := Nat.floor_le (show 0 ≤ C * Nκ by positivity)
    nlinarith
  have hs2 : Real.sqrt ((2 : ℝ) ^ N) ^ 2 = (2 : ℝ) ^ N := Real.sq_sqrt (by positivity)
  have ht : K * Real.sqrt ((2 : ℝ) ^ N) * N2 * e ≤
      K * Real.sqrt ((2 : ℝ) ^ N) * ((C + 4) * Nκ) * e := by gcongr
  refine ht.trans ?_
  obtain ⟨t, ht⟩ : ∃ t, t = K * Real.sqrt ((2 : ℝ) ^ N) * ((C + 4) * Nκ) * e := ⟨_, rfl⟩
  rw [← ht]
  have ht0 : 0 ≤ t := by rw [ht]; have := hNκ1; positivity
  have hsq : t ^ 2 ≤ 1 := by
    have e1 : t ^ 2 = (K * (C + 4)) ^ 2 * (2 : ℝ) ^ N * Nκ ^ 2 * e ^ 2 := by
      rw [ht]; ring_nf; rw [hs2]; ring
    rw [e1, ← hXQ]
    have hX0 : 0 ≤ X := le_trans (by positivity) h2N
    have h1 := mul_le_mul h2N hNP (by positivity) hX0
    have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg (K * (C + 4)))
    have h3 := mul_le_mul_of_nonneg_right h2 (sq_nonneg e)
    linarith
  nlinarith

/-- **Theorem A(c)**: for every `0 < Δ ≤ 1` there are `c_Δ, e_Δ > 0` such that every assignment
`φ` of unitaries to the five generators mapping every word of the certificate within `e ≤ e_Δ`
of `I` (normalized Hilbert–Schmidt norm) with `‖φ(a)φ(b) − I‖₂ ≥ Δ` (`b = a c⁴`) has
`log₂ D ≥ c_Δ e⁻² / (log₂(1/e))^{2κ}`, `κ = 2 + p_H`. -/
theorem theoremA_c (hS3 : UnitaryS3Round) (hPR : UnitaryPhaseRobust) (hP : PairAreaStatement)
    (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ ≤ 1) :
    ∃ cΔ > 0, ∃ eΔ > 0, ∀ e : ℝ, 0 < e → e ≤ eΔ →
      ∀ {Ω : Type} [Fintype Ω] [DecidableEq Ω] (φ : F →* Matrix.unitaryGroup Ω ℂ),
      (∀ k, ud (phiM φ (rel k)) 1 ≤ e) → Δ ≤ ud (phiM φ (a * b)) 1 →
      cΔ * (1 / e) ^ 2 / Real.logb 2 (1 / e) ^ (2 * (2 + pH)) ≤
        Real.logb 2 (Fintype.card Ω) := by
  obtain ⟨C, hC, hmodel⟩ := theoremA_c_model hS3 hPR unitaryMargin hP
  have hκ : 0 ≤ 2 + pH := by
    have : 0 ≤ Real.logb 2 107 := Real.logb_nonneg (by norm_num) (by norm_num)
    simp only [pH]; linarith
  obtain ⟨κ, hκdef⟩ : ∃ κ, κ = 2 + pH := ⟨_, rfl⟩
  rw [← hκdef] at hκ ⊢
  obtain ⟨P, hPdef⟩ : ∃ P, P = 2 * κ := ⟨_, rfl⟩
  rw [← hPdef]
  have hP0 : 0 ≤ P := by rw [hPdef]; linarith
  have hK9 : 9 / Δ ≤ Kd Δ := Kd_ge hΔ0 hΔ1
  have hK1 : 1 ≤ Kd Δ := by
    have : 9 ≤ 9 / Δ := by rw [le_div_iff₀ hΔ0]; linarith
    linarith
  obtain ⟨KC, hKCdef⟩ : ∃ KC, KC = Kd Δ * (C + 4) := ⟨_, rfl⟩
  have hKC : 1 ≤ KC := by rw [hKCdef]; nlinarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlp : 0 < Real.log 2 ^ P := Real.rpow_pos_of_pos hl2 _
  have h2P : 0 < (2 : ℝ) ^ P := Real.rpow_pos_of_pos (by norm_num) _
  obtain ⟨x₀, hx₀⟩ := log_rpow_le_sq (Real.log 2 ^ P / (2 * KC ^ 2 * 2 ^ P)) P (by positivity)
  refine ⟨Δ ^ 2 / (24 * KC ^ 2 * 2 ^ P), by positivity, min (1 / 2) (1 / max x₀ 2),
    by positivity, ?_⟩
  intro e he0 heΔ Ω _ _ φ hrel hab
  obtain ⟨x, hxdef⟩ : ∃ x, x = 1 / e := ⟨_, rfl⟩
  rw [← hxdef]
  have hxe : x * e = 1 := by rw [hxdef]; field_simp
  have hxmax : max x₀ 2 ≤ x := by
    have h := heΔ.trans (min_le_right _ _)
    rw [hxdef, le_div_iff₀ he0]
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  have hx2 : 2 ≤ x := le_of_max_le_right hxmax
  have hxx₀ : x₀ ≤ x := le_of_max_le_left hxmax
  have hx0 : 0 < x := by linarith
  obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ, ℓ = Real.logb 2 x := ⟨_, rfl⟩
  rw [← hℓdef]
  have hℓ1 : 1 ≤ ℓ := by
    rw [hℓdef, Real.le_logb_iff_rpow_le (by norm_num) hx0]; simpa using hx2
  have h2ℓP : (2 * ℓ) ^ P = 2 ^ P * (Real.log x ^ P / Real.log 2 ^ P) := by
    rw [Real.mul_rpow (by norm_num) (by linarith), hℓdef, Real.logb,
      Real.div_rpow (Real.log_nonneg (by linarith)) hl2.le]
  have hℓP : (2 * ℓ) ^ P = 2 ^ P * ℓ ^ P := Real.mul_rpow (by norm_num) (by linarith)
  have hℓP1 : 1 ≤ (2 * ℓ) ^ P := Real.one_le_rpow (by linarith) hP0
  -- the parameter `X`
  obtain ⟨X, hXdef⟩ : ∃ X, X = x ^ 2 / (KC ^ 2 * (2 * ℓ) ^ P) := ⟨_, rfl⟩
  have hden : 0 < KC ^ 2 * (2 * ℓ) ^ P := by positivity
  have hX2 : 2 ≤ X := by
    rw [hXdef, le_div_iff₀ hden, h2ℓP]
    have h := hx₀ x hxx₀
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at h
    have e1 : 2 * (KC ^ 2 * (2 ^ P * (Real.log x ^ P / Real.log 2 ^ P))) =
        (Real.log x ^ P * (2 * KC ^ 2 * 2 ^ P)) / Real.log 2 ^ P := by ring
    rw [e1, div_le_iff₀ hlp]; linarith
  have hXx : X ≤ x ^ 2 := by
    rw [hXdef]; apply div_le_self (by positivity)
    have : 1 ≤ KC ^ 2 := by nlinarith
    nlinarith
  -- the number of copies
  obtain ⟨N, hN1, h2N, hX2N, hNℓ⟩ := exists_N_of_X hX2 hXx hx0
  rw [← hℓdef] at hNℓ
  have hNκ1 : (1 : ℝ) ≤ (N : ℝ) ^ κ := Real.one_le_rpow (by exact_mod_cast hN1) hκ
  have hNP : ((N : ℝ) ^ κ) ^ 2 ≤ (2 * ℓ) ^ P := by
    rw [← Real.rpow_two, ← Real.rpow_mul (Nat.cast_nonneg _), show κ * 2 = P by rw [hPdef]; ring]
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) hNℓ hP0
  have hXQ : (Kd Δ * (C + 4)) ^ 2 * X * (2 * ℓ) ^ P * e ^ 2 = 1 := by
    rw [← hKCdef, hXdef]; field_simp; rw [← mul_pow, hxe, one_pow]
  have hcond := unitary_cond N (by linarith) hC he0.le hNκ1 h2N hNP hXQ rfl
  have hD := hmodel N hN1 φ Δ e hΔ0 hΔ1 hrel hab (by rw [← hκdef]; exact hcond)
  refine le_trans ?_ hD
  have e3 : Δ ^ 2 / (24 * KC ^ 2 * 2 ^ P) * x ^ 2 / ℓ ^ P = Δ ^ 2 * X / 24 := by
    rw [hXdef, hℓP]
    have : 0 < ℓ ^ P := Real.rpow_pos_of_pos (by linarith) _
    field_simp
  rw [e3]
  nlinarith

end Lamps
