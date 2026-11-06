import Lamps.PairSpec
import Lamps.Interfaces
import Houghton.DehnWeighted

/-!
# From local identities to the pair-area statement (arithmetic)

* `dehnLE_poly`: `δ_H(m) ≤ ⌊C m^{p_H}⌋` for `m ≥ 1`, transported from `Houghton.dehn_poly_weighted`
  through the Tietze map (`areaLE_κ`), exactly as in `dehnLE_of_astar`.
* `pairAreaStatement_of_family`: any instance of `LocalIdsFamily k B` gives `PairAreaStatement`
  (with `T := PairArea.T τ`, `pair_area_abstract`, `max 3 N ≤ 3N`).
-/

namespace Lamps

theorem four_le_pH : 4 ≤ pH := by
  unfold pH
  have := Real.logb_nonneg (b := 2) (by norm_num) (by norm_num : (1 : ℝ) ≤ 107)
  linarith

/-- **`δ_H(m) ≤ C m^{p_H}`.** -/
theorem dehnLE_poly : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → DehnLE m ⌊C * (m : ℝ) ^ pH⌋₊ := by
  obtain ⟨C, hC⟩ := Houghton.dehn_poly_weighted
  refine ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun m hm w hw h1 => ?_⟩
  have h2 := areaLE_κ (hC m hm (ιab w) ((length_toWord_ιab w).trans hw) h1)
  rw [← MonoidHom.comp_apply, κ_ιab] at h2
  refine h2.mono (Nat.floor_mono (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_))
  exact Real.rpow_nonneg (Nat.cast_nonneg _) _

/-- **Theorem `thm:pair-area` from the local identities.** -/
theorem pairAreaStatement_of_family {k B : ℕ} (h : LocalIdsFamily k B) : PairAreaStatement := by
  obtain ⟨C0, hC0, hD⟩ := dehnLE_poly
  set K : ℕ := max k 1 with hK
  have hp4 := four_le_pH
  refine ⟨49 * (10 * C0 * (3 * K : ℝ) ^ pH + 3 * B) + 1, by positivity, fun N hN => ?_⟩
  set M : ℕ := K * max 3 N with hM
  have hM1 : 1 ≤ M :=
    Nat.mul_le_mul (le_max_right k 1) (le_trans (by norm_num : 1 ≤ 3) (le_max_left 3 N))
  have hDM := (hD M hM1).mono (Nat.mul_le_mul_right _ (le_max_left k 1)) le_rfl
  obtain ⟨τ, X, hloc⟩ := h N hN _ hDM
  refine ⟨PairArea.T τ, fun u w huw x hx y hy => ?_⟩
  refine (PairArea.pair_area_abstract hloc u w huw x hx y hy).mono (Nat.le_floor ?_)
  set D := ⌊C0 * (M : ℝ) ^ pH⌋₊ with hDdef
  have h3N : max 3 N ≤ 3 * N := max_le (by omega) (by omega)
  have hMn : M ≤ 3 * K * N := by
    calc M = K * max 3 N := rfl
      _ ≤ K * (3 * N) := Nat.mul_le_mul_left _ h3N
      _ = 3 * K * N := by ring
  have hpoly : 20 * N ^ 2 + 28 * N + 1 ≤ 49 * N ^ 2 := by nlinarith
  have hnat : (20 * N ^ 2 + 28 * N + 1) * (10 * D + B * max 3 N) ≤
      49 * N ^ 2 * (10 * D + 3 * B * N) := by
    apply Nat.mul_le_mul hpoly
    have : B * max 3 N ≤ 3 * B * N := by
      calc B * max 3 N ≤ B * (3 * N) := Nat.mul_le_mul_left _ h3N
        _ = 3 * B * N := by ring
    omega
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hM' : (M : ℝ) ≤ 3 * K * N := by exact_mod_cast hMn
  have hDle : (D : ℝ) ≤ C0 * (3 * K : ℝ) ^ pH * (N : ℝ) ^ pH := by
    calc (D : ℝ) ≤ C0 * (M : ℝ) ^ pH := Nat.floor_le (by positivity)
      _ ≤ C0 * ((3 * K * N : ℝ) ^ pH) := by
          gcongr
      _ = C0 * (3 * K : ℝ) ^ pH * (N : ℝ) ^ pH := by
          rw [Real.mul_rpow (by positivity) (by positivity)]; ring
  have hNp : (N : ℝ) ≤ (N : ℝ) ^ pH := by
    simpa using Real.rpow_le_rpow_of_exponent_le hN1 (by linarith : (1 : ℝ) ≤ pH)
  have hsplit : (N : ℝ) ^ (2 + pH) = (N : ℝ) ^ 2 * (N : ℝ) ^ pH := by
    rw [Real.rpow_add hN0, Real.rpow_two]
  have hNpos : (0 : ℝ) ≤ (N : ℝ) ^ (2 + pH) := by positivity
  calc (((20 * N ^ 2 + 28 * N + 1) * (10 * D + B * max 3 N) : ℕ) : ℝ)
      ≤ ((49 * N ^ 2 * (10 * D + 3 * B * N) : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = 49 * (N : ℝ) ^ 2 * (10 * (D : ℝ) + 3 * B * N) := by push_cast; ring
    _ ≤ 49 * (N : ℝ) ^ 2 * (10 * (C0 * (3 * K : ℝ) ^ pH * (N : ℝ) ^ pH) + 3 * B * (N : ℝ) ^ pH) := by
        gcongr
    _ = 49 * (10 * C0 * (3 * K : ℝ) ^ pH + 3 * B) * (N : ℝ) ^ (2 + pH) := by
        rw [hsplit]; ring
    _ ≤ (49 * (10 * C0 * (3 * K : ℝ) ^ pH + 3 * B) + 1) * (N : ℝ) ^ (2 + pH) := by
        nlinarith

end Lamps
