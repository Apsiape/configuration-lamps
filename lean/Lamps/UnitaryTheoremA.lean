import Lamps.UnitaryCriterion
import Lamps.TheoremA

/-!
# Theorem A(c), model form (unitary models of the lamps group)

Extend a unitary assignment `φ` of the five letters to `S⁺` by `φ(b) = φ(a)φ(c)⁴` (`φ ∘ σ6`): the
relation `b⁻¹ a c⁴` is mapped to `I` exactly, `b²`, `(ab)³` to the images of the words `b²`, `(ab)³`
of the certificate.  With the `2^N` transport words of `PairAreaStatement` (area `Λ⁺ = Λ_N + 4`),
the unitary counting criterion gives `log D ≥ 2^N Δ²/12` whenever `K_Δ √(2^N) Λ⁺ e ≤ 1`.
-/

namespace Lamps

open Finset

/-- **Theorem A(c), model form**, from the unitary counting criterion and the pair-area theorem. -/
theorem theoremA_c_model (hS3 : UnitaryS3Round) (hPR : UnitaryPhaseRobust) (hM : UnitaryMargin)
    (hP : PairAreaStatement) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ {Ω : Type} [Fintype Ω] [DecidableEq Ω]
      (φ : F →* Matrix.unitaryGroup Ω ℂ) (Δ e : ℝ), 0 < Δ → Δ ≤ 1 →
      (∀ k, ud (phiM φ (rel k)) 1 ≤ e) → Δ ≤ ud (phiM φ (a * b)) 1 →
      Kd Δ * Real.sqrt ((2 : ℝ) ^ N) * ((⌊C * (N : ℝ) ^ (2 + pH)⌋₊ + 4 : ℕ) : ℝ) * e ≤ 1 →
      (2 : ℝ) ^ N * Δ ^ 2 / 12 ≤ Real.logb 2 (Fintype.card Ω) := by
  obtain ⟨C, hC, hT⟩ := hP
  refine ⟨C, hC, fun N hN Ω _ _ φ Δ e hΔ0 hΔ1 hrel hab hK => ?_⟩
  obtain ⟨T, hTa⟩ := hT N hN
  set n := ⌊C * (N : ℝ) ^ (2 + pH)⌋₊
  let eqv : Fin (2 ^ N) ≃ (Fin N → Bool) :=
    (Fintype.equivFinOfCardEq (by simp : Fintype.card (Fin N → Bool) = 2 ^ N)).symm
  have hw := transportAreaLE_lift T n hTa eqv
  let φ6 : F6 →* Matrix.unitaryGroup Ω ℂ := φ.comp σ6
  have hφ6 : ∀ x : F6, phiM φ6 x = phiM φ (σ6 x) := fun x => rfl
  have he : 0 ≤ e := (ud_nonneg _ _).trans (hrel 0)
  have hrel6 : ∀ k, ud (phiM φ6 (relP k)) 1 ≤ e := by
    intro k
    rcases k with i | k
    · simp only [relP, Sum.elim_inl, hφ6, σ6_ι6]
      exact hrel i
    · fin_cases k
      · show ud (phiM φ6 (bP⁻¹ * ι6 a * ι6 c ^ 4)) 1 ≤ e
        have h : σ6 (bP⁻¹ * ι6 a * ι6 c ^ 4) = 1 := by
          simp only [map_mul, map_inv, map_pow, σ6_ι6, σ6_bP, b]; group
        rw [hφ6, h, phiM_one, ud_self]
        exact he
      · show ud (phiM φ6 (bP ^ 2)) 1 ≤ e
        rw [hφ6, map_pow, σ6_bP, ← rel19]
        exact hrel 19
      · show ud (phiM φ6 ((FreeGroup.of 4 * bP) ^ 3)) 1 ≤ e
        rw [hφ6, map_pow, map_mul, σ6_bP, σ6_of4, ← rel20]
        exact hrel 20
  have hab6 : Δ ≤ ud (phiM φ6 (FreeGroup.of 4 * FreeGroup.of 5)) 1 := by
    rw [hφ6, map_mul, show (FreeGroup.of 5 : F6) = bP from rfl, σ6_bP, σ6_of4]
    exact hab
  have hRb : relP (Sum.inr 1) = FreeGroup.of 5 ^ 2 := rfl
  have hRab : relP (Sum.inr 2) = (FreeGroup.of 4 * FreeGroup.of 5) ^ 3 := rfl
  have hK' : Kd Δ * Real.sqrt ((2 ^ N : ℕ) : ℝ) * ((n + 4 : ℕ) : ℝ) * e ≤ 1 := by
    rw [Nat.cast_pow, Nat.cast_ofNat]; exact hK
  have := counting_criterion_unitary hS3 hPR hM relP 4 5 (Sum.inl 18) (Sum.inr 1) (Sum.inr 2)
    relP_a hRb hRab (fun i => ι6 (T (eqv i))) (n + 4) (by omega) hw φ6 Δ e hΔ0 hΔ1 hrel6 hab6 hK'
  push_cast at this
  exact this

end Lamps
