import Lamps.UnitaryPhaseState
import Houghton.Analysis.SSAFinal

/-!
# `UnitaryEntropyBound` from strong subadditivity, and the reduction of `UnitaryPhaseRobust`

Chain (bits): `H(p) ≤ S(Π_all ρ̂) ≤ S(ρ̂) + ∑ᵢ (S(Πᵢ ρ̂) - S(ρ̂)) ≤ log D + ∑ᵢ χ(aᵢ)`, using
`subSectorEntropyU`, SSA (`Houghton.qit_commutingPinchingSSA`, proved), `subStateEntropyU`, the
single-twirl bound `twirlEntropyU` with weight `≤ min((â₁² + â₂²)/3, 2/3)`, and the projection
estimate `âᵢ,ₜ² ≤ aᵢ` (`UnitaryAhatProj`).
-/

namespace Lamps

open Finset Matrix Houghton

/-- The projection estimate for `â` (`lem:projections` for the averages `E_j`). -/
def UnitaryAhatProj : Prop :=
  ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω] (N : ℕ) (c : Fin N → Matrix Ω Ω ℂ),
    (∀ i, IsU (c i)) → (∀ i, c i ^ 3 = 1) → ∀ i, ahat2 c i 1 ≤ aCoef c i ∧ ahat2 c i 2 ≤ aCoef c i

lemma twirl_mono {w0 w : ℝ} (hw0nn : 0 ≤ w0) (hw0 : w0 ≤ w) (hw : w ≤ 2 / 3) :
    ent w0 + ent (1 - w0) + w0 * Real.log 2 ≤ ent w + ent (1 - w) + w * Real.log 2 := by
  rcases (hw0nn.trans hw0).eq_or_lt with h | hwpos
  · have : w0 = 0 := by linarith
    rw [this, ← h]
  · have h1w : 0 < 1 - w := by linarith
    have t1 := ent_tangent hw0nn hwpos
    have t2 := ent_tangent (show 0 ≤ 1 - w0 by linarith) h1w
    have hlog : Real.log w ≤ Real.log 2 + Real.log (1 - w) := by
      rw [← Real.log_mul (by norm_num) h1w.ne']
      exact Real.log_le_log hwpos (by linarith)
    nlinarith

lemma chi_eq (a : ℝ) :
    ent (min (2 / 3 * a) (2 / 3)) + ent (1 - min (2 / 3 * a) (2 / 3)) +
      min (2 / 3 * a) (2 / 3) * Real.log 2 = Real.log 2 * chi a := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  simp only [chi, Houghton.h2, Real.logb, ent]
  field_simp
  ring

/-- **The entropy bound**, from the projection estimate for `â`. -/
theorem unitaryEntropyBound_of (hA : UnitaryAhatProj) : UnitaryEntropyBound := by
  intro Ω _ _ N c hc hc3 hD
  have hl2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set L := Real.log (Fintype.card Ω) with hL
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have h0 : ∑ z, ent (pSecU c z) = 0 := by
      have := sum_pSecU c hc hD
      rw [Fintype.sum_unique] at this ⊢
      rw [this, ent_one]
    rw [h0, zero_div, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    exact Real.logb_nonneg (by norm_num) (by exact_mod_cast hD)
  have hSSA := Houghton.qit_commutingPinchingSSA ((Fin N → Fin 3) × Ω) (Fin 3) N
    (fun i => labelProj i) (fun k => labelProj_family k)
    (fun k l _ a b => labelProj_comm k l a b) (rhoSecU c) (rhoSecU_density c hc hD)
  have hS := subStateEntropyU c hc hD
  have hC := subSectorEntropyU c hc hD
  have hT : ∀ k, vN (pinch (labelProj k) (rhoSecU c)) ≤ L + Real.log 2 * chi (aCoef c k) := by
    intro k
    have t := twirlEntropyU c hc hD k genTwirlBound23
    obtain ⟨h1, h2⟩ := hA Ω N c hc hc3 k
    have ha1 : 0 ≤ ahat2 c k 1 := by
      unfold ahat2; exact div_nonneg (sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
    have ha2 : 0 ≤ ahat2 c k 2 := by
      unfold ahat2; exact div_nonneg (sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
    have hm := twirl_mono (w0 := min ((ahat2 c k 1 + ahat2 c k 2) / 3) (2 / 3))
      (w := min (2 / 3 * aCoef c k) (2 / 3)) (le_min (by positivity) (by norm_num))
      (min_le_min_right _ (by linarith)) (min_le_right _ _)
    rw [chi_eq] at hm
    linarith
  have hsumT : ∑ k : Fin N, vN (pinch (labelProj k) (rhoSecU c)) ≤
      N * L + Real.log 2 * ∑ k, chi (aCoef c k) := by
    calc ∑ k : Fin N, vN (pinch (labelProj k) (rhoSecU c))
        ≤ ∑ k : Fin N, (L + Real.log 2 * chi (aCoef c k)) := sum_le_sum fun k _ => hT k
      _ = N * L + Real.log 2 * ∑ k, chi (aCoef c k) := by
          rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_sum]
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hent : ∑ z, ent (pSecU c z) ≤ L + Real.log 2 * ∑ k, chi (aCoef c k) := by
    have h' : ((N : ℝ) - 1) * L ≤ ((N : ℝ) - 1) * vN (rhoSecU c) :=
      mul_le_mul_of_nonneg_left hS (by linarith)
    nlinarith
  rw [div_le_iff₀ hl2pos, Real.logb, add_mul, div_mul_cancel₀ _ hl2pos.ne']
  linarith

/-- **`UnitaryPhaseRobust`**, reduced to the two projection estimates and the sharp two-point
entropy inequality. -/
theorem unitaryPhaseRobust_of_proj (hH : SharpPairEntropy) (hA : UnitaryAhatProj)
    (hB : UnitaryBhatProj) : UnitaryPhaseRobust :=
  unitaryPhaseRobust_of hH (unitaryEntropyBound_of hA) hB

/-- The weak-constant version needs only the two projection estimates. -/
theorem unitaryPhaseRobustWeak_of_proj (hA : UnitaryAhatProj) (hB : UnitaryBhatProj) :
    UnitaryPhaseRobustWeak :=
  unitaryPhaseRobustWeak_of (unitaryEntropyBound_of hA) hB

end Lamps
