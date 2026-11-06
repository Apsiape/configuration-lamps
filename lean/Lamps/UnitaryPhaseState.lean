import Lamps.UnitaryPhaseTwirl

/-!
# The Fourier state for unitary local actions

`ρ̂ = YY*/(9^N D)` with `Y_{(χ,α),ω} = M_χ(α, ω)` for the unitary family `f(g)`; `Y*Y = 9^N·1`
(Parseval), so `ρ̂` is a density matrix with all eigenvalues `≤ 1/D` and `S(ρ̂) ≥ log D`.
-/

namespace Lamps

open Finset Matrix ComplexConjugate Houghton

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {N : ℕ}

/-- `Y_{(χ,α),ω} = M_χ(α, ω)`. -/
noncomputable def YmatU (c : Fin N → Matrix Ω Ω ℂ) : Matrix ((Fin N → Fin 3) × Ω) Ω ℂ :=
  fun p ω => MsecU c p.1 p.2 ω

/-- `ρ̂ = YY*/(9^N D)`. -/
noncomputable def rhoSecU (c : Fin N → Matrix Ω Ω ℂ) :
    Matrix ((Fin N → Fin 3) × Ω) ((Fin N → Fin 3) × Ω) ℂ :=
  (((9 : ℝ) ^ N * Fintype.card Ω)⁻¹ : ℝ) • (YmatU c * (YmatU c)ᴴ)

lemma YhYU (c : Fin N → Matrix Ω Ω ℂ) (hc : ∀ i, IsU (c i)) :
    (YmatU c)ᴴ * YmatU c = ((9 : ℂ) ^ N) • (1 : Matrix Ω Ω ℂ) := by
  ext ω ω'
  simp only [mul_apply, conjTranspose_apply, YmatU, Matrix.smul_apply, one_apply, smul_eq_mul]
  rw [Fintype.sum_prod_type, sum_comm]
  have h : ∀ α, ∑ χ, star (MsecU c χ α ω) * MsecU c χ α ω' =
      3 ^ N * ∑ g, conj (fprodU c g α ω) * fprodU c g α ω' := by
    intro α
    exact parseval_scalar (fun g => fprodU c g α ω) (fun g => fprodU c g α ω')
  simp only [h, ← mul_sum]
  rw [sum_comm]
  have h2 : ∀ g, ∑ α, conj (fprodU c g α ω) * fprodU c g α ω' = if ω = ω' then 1 else 0 := by
    intro g
    have := congrFun (congrFun (isU_fprodU c hc g).1 ω) ω'
    rw [mul_apply, one_apply] at this
    rw [← this]
    rfl
  simp only [h2, sum_const, card_univ, card_G, nsmul_eq_mul]
  rw [show (9 : ℂ) ^ N = 3 ^ N * 3 ^ N by rw [← mul_pow]; norm_num]
  split_ifs <;> push_cast <;> ring

lemma rhoSecU_density (c : Fin N → Matrix Ω Ω ℂ) (hc : ∀ i, IsU (c i)) (hD : 0 < Fintype.card Ω) : IsDensity (rhoSecU c) := by
  have hK : (0 : ℝ) < 9 ^ N * Fintype.card Ω := by positivity
  refine ⟨?_, ?_, ?_⟩
  · -- Hermitian
    unfold rhoSecU
    rw [IsHermitian, conjTranspose_smul, conjTranspose_mul, conjTranspose_conjTranspose]
    congr 1
  · intro v
    have e : star v ⬝ᵥ (rhoSecU c *ᵥ v) =
        (((9 : ℝ) ^ N * Fintype.card Ω)⁻¹ : ℝ) • (star ((YmatU c)ᴴ *ᵥ v) ⬝ᵥ ((YmatU c)ᴴ *ᵥ v)) := by
      rw [rhoSecU, smul_mulVec, dotProduct_smul, ← mulVec_mulVec, dotProduct_mulVec,
        star_mulVec, conjTranspose_conjTranspose]
    rw [e, Complex.real_smul, Complex.re_ofReal_mul]
    refine mul_nonneg (inv_nonneg.mpr hK.le) ?_
    simp only [dotProduct, Complex.re_sum, Pi.star_apply]
    refine sum_nonneg fun ω _ => ?_
    have : (star (((YmatU c)ᴴ *ᵥ v) ω) * ((YmatU c)ᴴ *ᵥ v) ω).re =
        Complex.normSq (((YmatU c)ᴴ *ᵥ v) ω) := by
      rw [show star (((YmatU c)ᴴ *ᵥ v) ω) = conj (((YmatU c)ᴴ *ᵥ v) ω) from rfl,
        ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
    rw [this]
    exact Complex.normSq_nonneg _
  · -- trace
    rw [rhoSecU, trace_smul]
    have htr : (YmatU c * (YmatU c)ᴴ).trace = ((9 : ℝ) ^ N * Fintype.card Ω : ℝ) := by
      rw [← sum_nsq_MsecU c hc, Complex.ofReal_sum]
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, conjTranspose_apply, YmatU]
      rw [Fintype.sum_prod_type]
      refine sum_congr rfl fun χ _ => ?_
      simp only [nsq, Complex.ofReal_sum]
      refine sum_congr rfl fun α _ => sum_congr rfl fun ω _ => ?_
      rw [show star (MsecU c χ α ω) = conj (MsecU c χ α ω) from rfl, Complex.mul_conj]
    rw [htr, Complex.real_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hK.ne', Complex.ofReal_one]

lemma rhoSecU_cap (c : Fin N → Matrix Ω Ω ℂ) (hc : ∀ i, IsU (c i)) (hD : 0 < Fintype.card Ω) (v : (Fin N → Fin 3) × Ω → ℂ) :
    (star v ⬝ᵥ (rhoSecU c *ᵥ v)).re ≤
      (Fintype.card Ω : ℝ)⁻¹ * ∑ j, Complex.normSq (v j) := by
  have hK : (0 : ℝ) < 9 ^ N * Fintype.card Ω := by positivity
  set W := (YmatU c)ᴴ *ᵥ v with hW
  have e : star v ⬝ᵥ (rhoSecU c *ᵥ v) =
      (((9 : ℝ) ^ N * Fintype.card Ω)⁻¹ : ℝ) • (star W ⬝ᵥ W) := by
    rw [rhoSecU, smul_mulVec, dotProduct_smul, ← mulVec_mulVec, dotProduct_mulVec,
      star_mulVec, conjTranspose_conjTranspose]
  rw [e, Complex.real_smul, Complex.re_ofReal_mul, dot_star_self_re]
  -- `‖W‖² ≤ 9^N ‖v‖²`
  set a := ∑ j, Complex.normSq (W j)
  set b := ∑ j, Complex.normSq (v j)
  have ha : 0 ≤ a := sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have hb : 0 ≤ b := sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have h9 : Real.sqrt (9 ^ N) = 3 ^ N := by
    rw [show (9 : ℝ) ^ N = (3 ^ N) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num,
      Real.sqrt_sq (by positivity)]
  have hYW : ∑ j, Complex.normSq ((YmatU c *ᵥ W) j) = 9 ^ N * a := by
    rw [← dot_star_self_re, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, YhYU c hc, smul_mulVec,
      one_mulVec, dotProduct_smul, smul_eq_mul,
      show ((9 : ℂ) ^ N) = (((9 : ℝ) ^ N : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul,
      dot_star_self_re]
  have hA : a = (star v ⬝ᵥ (YmatU c *ᵥ W)).re := by
    rw [dotProduct_mulVec,
      show star v ᵥ* YmatU c = star W by rw [hW, star_mulVec, conjTranspose_conjTranspose],
      dot_star_self_re]
  have hcs := re_dot_le v (YmatU c *ᵥ W)
  rw [← hA, hYW, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 9 ^ N), h9] at hcs
  have hsa : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  have hsb : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb
  have hsa0 := Real.sqrt_nonneg a
  have hsb0 := Real.sqrt_nonneg b
  have h3 : (0 : ℝ) < 3 ^ N := by positivity
  have key : a ≤ 9 ^ N * b := by
    have hroot : Real.sqrt a ≤ 3 ^ N * Real.sqrt b := by
      rcases hsa0.eq_or_lt with h0 | hpos
      · rw [← h0]; positivity
      · nlinarith
    have h9' : (9 : ℝ) ^ N = 3 ^ N * 3 ^ N := by rw [← mul_pow]; norm_num
    rw [← hsa, h9', ← hsb]
    nlinarith
  have hD' : (Fintype.card Ω : ℝ) ≠ 0 := by positivity
  rw [inv_mul_le_iff₀ hK]
  calc a ≤ 9 ^ N * b := key
    _ = 9 ^ N * (Fintype.card Ω : ℝ) * ((Fintype.card Ω : ℝ)⁻¹ * b) := by
        field_simp

theorem subStateEntropyU (c : Fin N → Matrix Ω Ω ℂ) (hc : ∀ i, IsU (c i))
    (hD : 0 < Fintype.card Ω) : Real.log (Fintype.card Ω) ≤ vN (rhoSecU c) :=
  log_le_vN_of_cap (rhoSecU_density c hc hD) _ (by exact_mod_cast hD) (rhoSecU_cap c hc hD)

lemma rhoSecU_apply (c : Fin N → Matrix Ω Ω ℂ) (p q : (Fin N → Fin 3) × Ω) :
    rhoSecU c p q = (((9 : ℝ) ^ N * Fintype.card Ω)⁻¹ : ℝ) *
      ∑ ω, MsecU c p.1 p.2 ω * conj (MsecU c q.1 q.2 ω) := by
  simp only [rhoSecU, Matrix.smul_apply, mul_apply, conjTranspose_apply, YmatU, Complex.real_smul]
  rfl

theorem subSectorEntropyU (c : Fin N → Matrix Ω Ω ℂ) (hc : ∀ i, IsU (c i))
    (hD : 0 < Fintype.card Ω) :
    ∑ z, ent (pSecU c z) ≤ vN (pinchAll (fun i => labelProj (Ω := Ω) i) (rhoSecU c)) := by
  have hK : (0 : ℝ) < 9 ^ N * Fintype.card Ω := by positivity
  obtain ⟨hρH, hρpsd, -⟩ := rhoSecU_density c hc hD
  set ρ := rhoSecU c with hρdef
  set σ := pinchAll (fun i => labelProj (Ω := Ω) i) ρ with hσdef
  have hσ : ∀ p q, σ p q = if p.1 = q.1 then ρ p q else 0 := by
    intro p q
    have := pinchAll_labelProj N (fun i => i) ρ p q
    rw [hσdef, this]
    by_cases h : p.1 = q.1
    · rw [if_pos (fun k => congrFun h k), if_pos h]
    · rw [if_neg h, if_neg (fun hk => h (funext hk))]
  have hH : σ.IsHermitian := by
    ext p q
    rw [conjTranspose_apply, hσ, hσ]
    by_cases h : p.1 = q.1
    · rw [if_pos h.symm, if_pos h]
      have := congrFun (congrFun hρH p) q
      rw [conjTranspose_apply] at this
      exact this
    · rw [if_neg (Ne.symm h), if_neg h, star_zero]
  rw [vN_eq hH]
  set U := (hH.eigenvectorUnitary :
    Matrix ((Fin N → Fin 3) × Ω) ((Fin N → Fin 3) × Ω) ℂ) with hU
  set lam := hH.eigenvalues with hlam
  -- block masses of the eigenvectors
  set π : (Fin N → Fin 3) × Ω → (Fin N → Fin 3) → ℝ :=
    fun j χ => ∑ α, Complex.normSq (U (χ, α) j) with hπdef
  have hπ0 : ∀ j χ, 0 ≤ π j χ := fun j χ => sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have hπsum : ∀ j, ∑ χ, π j χ = 1 := by
    intro j
    rw [← eigvec_normSq_sum hH j, Fintype.sum_prod_type]
  -- diagonal of `ρ`
  have hρdiag : ∀ χ, ∑ α, (ρ (χ, α) (χ, α)).re = pSecU c χ := by
    intro χ
    simp only [hρdef, rhoSecU_apply, Complex.re_ofReal_mul, ← mul_sum, pSecU, nsq]
    rw [div_eq_inv_mul]
    congr 1
    refine sum_congr rfl fun α _ => ?_
    rw [Complex.re_sum]
    refine sum_congr rfl fun ω _ => ?_
    rw [Complex.mul_conj, Complex.ofReal_re]
  have hp : ∀ χ, pSecU c χ = ∑ j, lam j * π j χ := by
    intro χ
    rw [← hρdiag]
    simp only [hπdef, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun α _ => ?_
    have := herm_diag_re hH (χ, α)
    rw [hσ, if_pos rfl] at this
    exact this
  -- the eigen-relation on blocks
  have hblock : ∀ j χ, lam j * π j χ ≤ pSecU c χ * π j χ ∧ 0 ≤ lam j * π j χ := by
    intro j χ
    set u : (Fin N → Fin 3) × Ω → ℂ := fun p => if p.1 = χ then U p j else 0 with hu
    have hev := eigvec_mulVec hH j
    -- `ρ u = λ u` on the block
    have hρu : ∀ p, p.1 = χ → (ρ *ᵥ u) p = (lam j : ℂ) * U p j := by
      intro p hp1
      have := congrFun hev p
      simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this ⊢
      rw [← this]
      refine sum_congr rfl fun q _ => ?_
      rw [hσ]
      simp only [hu]
      by_cases hq : q.1 = χ
      · simp [hq, show p.1 = q.1 from hp1.trans hq.symm, hU]
      · simp [hq, show ¬ p.1 = q.1 from fun h => hq (h.symm.trans hp1)]
    have hnorm : ∑ p, Complex.normSq (u p) = π j χ := by
      rw [Fintype.sum_prod_type, hπdef]
      simp only [hu]
      rw [sum_eq_single χ]
      · simp
      · intro χ' _ hχ'; simp [hχ']
      · simp
    have hquad : (star u ⬝ᵥ (ρ *ᵥ u)).re = lam j * π j χ := by
      rw [← hnorm, mul_sum]
      simp only [dotProduct, Complex.re_sum, Pi.star_apply]
      refine sum_congr rfl fun p _ => ?_
      by_cases hp1 : p.1 = χ
      · rw [hρu p hp1]
        simp only [hu, if_pos hp1]
        rw [mul_left_comm, Complex.re_ofReal_mul,
          show star (U p j) = conj (U p j) from rfl, ← Complex.normSq_eq_conj_mul_self,
          Complex.ofReal_re]
      · simp [hu, hp1]
    -- Gram bound
    have hgram : (star u ⬝ᵥ (ρ *ᵥ u)).re ≤ pSecU c χ * π j χ := by
      have e : star u ⬝ᵥ (ρ *ᵥ u) =
          (((9 : ℝ) ^ N * Fintype.card Ω)⁻¹ : ℝ) • (star ((YmatU c)ᴴ *ᵥ u) ⬝ᵥ ((YmatU c)ᴴ *ᵥ u)) := by
        rw [hρdef, rhoSecU, smul_mulVec, dotProduct_smul, ← mulVec_mulVec, dotProduct_mulVec,
          star_mulVec, conjTranspose_conjTranspose]
      rw [e, Complex.real_smul, Complex.re_ofReal_mul, dot_star_self_re, ← hnorm]
      have hω : ∀ ω, Complex.normSq (((YmatU c)ᴴ *ᵥ u) ω) ≤
          (∑ α, Complex.normSq (MsecU c χ α ω)) * ∑ p, Complex.normSq (u p) := by
        intro ω
        set a : (Fin N → Fin 3) × Ω → ℂ := fun p => if p.1 = χ then YmatU c p ω else 0
        have e1 : ((YmatU c)ᴴ *ᵥ u) ω = star a ⬝ᵥ u := by
          simp only [mulVec, dotProduct, conjTranspose_apply, Pi.star_apply, a]
          refine sum_congr rfl fun p _ => ?_
          by_cases hp1 : p.1 = χ
          · simp [hp1]
          · simp [hp1, hu]
        have e2 : ∑ p, Complex.normSq (a p) = ∑ α, Complex.normSq (MsecU c χ α ω) := by
          rw [Fintype.sum_prod_type, sum_eq_single χ]
          · simp [a, YmatU]
          · intro χ' _ hχ'; simp [a, hχ']
          · simp
        rw [e1, ← e2]
        exact normSq_dot_le a u
      have hsum : ∑ ω, Complex.normSq (((YmatU c)ᴴ *ᵥ u) ω) ≤
          nsq (MsecU c χ) * ∑ p, Complex.normSq (u p) := by
        calc ∑ ω, Complex.normSq (((YmatU c)ᴴ *ᵥ u) ω)
            ≤ ∑ ω, (∑ α, Complex.normSq (MsecU c χ α ω)) * ∑ p, Complex.normSq (u p) :=
              sum_le_sum fun ω _ => hω ω
          _ = nsq (MsecU c χ) * ∑ p, Complex.normSq (u p) := by
              rw [← sum_mul, nsq, sum_comm]
      have hinv : (0 : ℝ) ≤ ((9 : ℝ) ^ N * Fintype.card Ω)⁻¹ := inv_nonneg.mpr hK.le
      calc ((9 : ℝ) ^ N * Fintype.card Ω)⁻¹ * ∑ ω, Complex.normSq (((YmatU c)ᴴ *ᵥ u) ω)
          ≤ ((9 : ℝ) ^ N * Fintype.card Ω)⁻¹ * (nsq (MsecU c χ) * ∑ p, Complex.normSq (u p)) :=
            mul_le_mul_of_nonneg_left hsum hinv
        _ = pSecU c χ * ∑ p, Complex.normSq (u p) := by
            rw [pSecU, div_eq_inv_mul, mul_assoc]
    have hpsd := hρpsd u
    rw [hquad] at hgram hpsd
    exact ⟨hgram, hpsd⟩
  -- Gibbs inequality
  have hterm : ∀ j χ, lam j * π j χ * (-Real.log (pSecU c χ)) ≤
      lam j * π j χ * (-Real.log (lam j)) := by
    intro j χ
    obtain ⟨h1, h2⟩ := hblock j χ
    rcases h2.eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · have hπpos : 0 < π j χ := by
        rcases (hπ0 j χ).eq_or_lt with h | h
        · rw [← h, mul_zero] at hpos; exact absurd hpos (lt_irrefl 0)
        · exact h
      have hlpos : 0 < lam j := by
        by_contra hneg
        push Not at hneg
        nlinarith
      have hle : lam j ≤ pSecU c χ := le_of_mul_le_mul_right h1 hπpos
      have := Real.log_le_log hlpos hle
      nlinarith
  calc ∑ χ, ent (pSecU c χ) = ∑ χ, ∑ j, lam j * π j χ * (-Real.log (pSecU c χ)) := by
        refine sum_congr rfl fun χ _ => ?_
        rw [← sum_mul, ← hp]; unfold ent; ring
    _ ≤ ∑ χ, ∑ j, lam j * π j χ * (-Real.log (lam j)) :=
        sum_le_sum fun χ _ => sum_le_sum fun j _ => hterm j χ
    _ = ∑ j, ent (lam j) := by
        rw [sum_comm]
        refine sum_congr rfl fun j _ => ?_
        have : ∑ χ, lam j * π j χ * (-Real.log (lam j)) =
            lam j * (-Real.log (lam j)) * ∑ χ, π j χ := by
          rw [mul_sum]; exact sum_congr rfl fun χ _ => by ring
        rw [this, hπsum, mul_one]; unfold ent; ring


/-! ### The twirl in the Fourier picture -/

/-- The projection `P = YY*/9^N` onto `ran ρ̂`. -/
noncomputable def PprojU (c : Fin N → Matrix Ω Ω ℂ) :
    Matrix ((Fin N → Fin 3) × Ω) ((Fin N → Fin 3) × Ω) ℂ :=
  ((9 : ℂ) ^ N)⁻¹ • (YmatU c * (YmatU c)ᴴ)

lemma PprojU_herm (c : Fin N → Matrix Ω Ω ℂ) : (PprojU c)ᴴ = PprojU c := by
  rw [PprojU, conjTranspose_smul, conjTranspose_mul, conjTranspose_conjTranspose]
  congr 1
  simp

lemma YYYYU (c : Fin N → Matrix Ω Ω ℂ) (hc : ∀ i, IsU (c i)) :
    YmatU c * (YmatU c)ᴴ * (YmatU c * (YmatU c)ᴴ) = ((9 : ℂ) ^ N) • (YmatU c * (YmatU c)ᴴ) := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (YmatU c)ᴴ, YhYU c hc, Matrix.smul_mul, Matrix.one_mul,
    Matrix.mul_smul]

lemma PprojU_idem (c : Fin N → Matrix Ω Ω ℂ) (hc : ∀ i, IsU (c i)) : PprojU c * PprojU c = PprojU c := by
  rw [PprojU, Matrix.smul_mul, Matrix.mul_smul, YYYYU c hc, smul_smul, smul_smul]
  congr 1
  field_simp

lemma PprojU_trace (c : Fin N → Matrix Ω Ω ℂ) (hc : ∀ i, IsU (c i)) : (PprojU c).trace = Fintype.card Ω := by
  rw [PprojU, trace_smul, Matrix.trace_mul_comm, YhYU c hc, trace_smul, trace_one, smul_eq_mul,
    smul_eq_mul]
  field_simp

lemma rhoSecU_eq (c : Fin N → Matrix Ω Ω ℂ) (hc : ∀ i, IsU (c i)) (hD : 0 < Fintype.card Ω) :
    rhoSecU c = ((Fintype.card Ω : ℂ))⁻¹ • PprojU c := by
  ext p q
  simp only [rhoSecU, PprojU, Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
  push_cast
  ring

lemma sigmaU_eq (c : Fin N → Matrix Ω Ω ℂ) (hc : ∀ i, IsU (c i)) (hD : 0 < Fintype.card Ω) (i : Fin N) :
    pinch (labelProj i) (rhoSecU c) = (((3 * Fintype.card Ω : ℕ) : ℂ))⁻¹ •
      (PprojU c + Zt i 1 * PprojU c * (Zt i 1)ᴴ + Zt i 2 * PprojU c * (Zt i 2)ᴴ) := by
  rw [pinch_eq_twirl, rhoSecU_eq c hc hD, Fin.sum_univ_three, Zt_zero]
  simp only [Matrix.mul_smul, Matrix.smul_mul, conjTranspose_one, Matrix.one_mul, Matrix.mul_one,
    ← smul_add, smul_smul]
  congr 1
  push_cast
  rw [mul_inv]


lemma traceU_PZPZ (c : Fin N → Matrix Ω Ω ℂ) (Z : Matrix ((Fin N → Fin 3) × Ω) ((Fin N → Fin 3) × Ω) ℂ) :
    (PprojU c * (Z * PprojU c * Zᴴ)).trace =
      ((9 : ℂ) ^ N)⁻¹ * ((9 : ℂ) ^ N)⁻¹ * (nsq ((YmatU c)ᴴ * Z * YmatU c) : ℂ) := by
  have e : PprojU c * (Z * PprojU c * Zᴴ) = (((9 : ℂ) ^ N)⁻¹ * ((9 : ℂ) ^ N)⁻¹) •
      (YmatU c * (YmatU c)ᴴ * (Z * (YmatU c * (YmatU c)ᴴ) * Zᴴ)) := by
    simp only [PprojU, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  rw [e, trace_smul, smul_eq_mul, ← trace_GG]
  congr 1
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm (YmatU c)]
  simp only [Matrix.mul_assoc]


lemma G_innerU (c : Fin N → Matrix Ω Ω ℂ) (i : Fin N) (t : Fin 3) (ω ω' α : Ω) :
    ∑ χ, star (MsecU c χ α ω) * ech (t * χ i) * MsecU c χ α ω' =
      3 ^ N * ∑ g, conj (fprodU c g α ω) * fprodU c (g + Pi.single i t) α ω' := by
  have hterm : ∀ χ, star (MsecU c χ α ω) * ech (t * χ i) * MsecU c χ α ω' =
      conj (∑ g, ech (-(dot χ g)) * fprodU c g α ω) *
        ∑ h, ech (-(dot χ h)) * fprodU c (h + Pi.single i t) α ω' := by
    intro χ
    have := FT_shift (fun g => (fprodU c g : Ω → Ω → ℂ)) χ i t α ω'
    simp only [FT] at this
    simp only [MsecU, FT]
    rw [mul_assoc, this, starRingEnd_apply]
  have e := Finset.sum_congr (s₁ := (univ : Finset (Fin N → Fin 3))) rfl
    (fun χ (_ : χ ∈ univ) => hterm χ)
  rw [e]
  have p := parseval_scalar (fun g => fprodU c g α ω) (fun g => fprodU c (g + Pi.single i t) α ω')
  beta_reduce at p
  exact p

lemma G_applyU (c : Fin N → Matrix Ω Ω ℂ) (i : Fin N) (t : Fin 3) (ω ω' : Ω) :
    ((YmatU c)ᴴ * Zt (Ω := Ω) i t * YmatU c) ω ω' =
      3 ^ N * ∑ g, ∑ α, conj (fprodU c g α ω) * fprodU c (g + Pi.single i t) α ω' := by
  simp only [Zt]
  rw [mul_apply]
  simp only [mul_diagonal, conjTranspose_apply, YmatU]
  rw [Fintype.sum_prod_type, sum_comm]
  dsimp only
  have e := Finset.sum_congr (s₁ := (univ : Finset Ω)) rfl
    (fun α (_ : α ∈ univ) => G_innerU c i t ω ω' α)
  rw [e, ← mul_sum, sum_comm]

/-- `â²(i,t) = E_g ‖f(g) c_i^t - f(g + t e_i)‖₂²`. -/
noncomputable def ahat2 (c : Fin N → Matrix Ω Ω ℂ) (i : Fin N) (t : Fin 3) : ℝ :=
  (∑ g, ud (fprodU c g * c i ^ t.val) (fprodU c (g + Pi.single i t)) ^ 2) / 3 ^ N


lemma G_matU (c : Fin N → Matrix Ω Ω ℂ) (i : Fin N) (t : Fin 3) :
    (YmatU c)ᴴ * Zt (Ω := Ω) i t * YmatU c =
      (3 : ℂ) ^ N • ∑ g, (fprodU c g)ᴴ * fprodU c (g + Pi.single i t) := by
  ext ω ω'
  rw [G_applyU, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  rfl

lemma hip_G (c : Fin N → Matrix Ω Ω ℂ) (i : Fin N) (t : Fin 3) (X : Matrix Ω Ω ℂ) :
    hip X ((YmatU c)ᴴ * Zt (Ω := Ω) i t * YmatU c) =
      3 ^ N * ∑ g, hip (fprodU c g * X) (fprodU c (g + Pi.single i t)) := by
  rw [G_matU, hip_eq_trace, Matrix.mul_smul, trace_smul, Finset.mul_sum, trace_sum, smul_eq_mul]
  congr 1
  refine sum_congr rfl fun g _ => ?_
  rw [hip_eq_trace, conjTranspose_mul, Matrix.mul_assoc]

/-- Lower bound for the overlap `tr(P Zₜ P Zₜ*) ≥ D (1 - â²)`. -/
lemma trace_PZPZU_ge (c : Fin N → Matrix Ω Ω ℂ) (hc : ∀ i, IsU (c i)) (hD : 0 < Fintype.card Ω)
    (i : Fin N) (t : Fin 3) :
    (Fintype.card Ω : ℝ) * (1 - ahat2 c i t) ≤
      (PprojU c * (Zt i t * PprojU c * (Zt i t)ᴴ)).trace.re := by
  set G := (YmatU c)ᴴ * Zt (Ω := Ω) i t * YmatU c with hG
  set D : ℝ := (Fintype.card Ω : ℝ) with hDdef
  have hDpos : 0 < D := by rw [hDdef]; exact_mod_cast hD
  rw [traceU_PZPZ, ← hG]
  have hre : ((((9 : ℂ) ^ N)⁻¹ * ((9 : ℂ) ^ N)⁻¹ * (nsq G : ℂ))).re =
      nsq G / ((9 : ℝ) ^ N * 9 ^ N) := by
    rw [show ((9 : ℂ) ^ N)⁻¹ * ((9 : ℂ) ^ N)⁻¹ * (nsq G : ℂ) =
      ((nsq G / ((9 : ℝ) ^ N * 9 ^ N) : ℝ) : ℂ) by push_cast; field_simp, Complex.ofReal_re]
  rw [hre]
  have hU := (hc i).pow t.val
  have hcs := re_hip_le (c i ^ t.val) G
  rw [nsq_isU hU] at hcs
  have hval : (hip (c i ^ t.val) G).re = 9 ^ N * D * (1 - ahat2 c i t / 2) := by
    rw [hG, hip_G, show (3 : ℂ) ^ N = (((3 : ℝ) ^ N : ℝ) : ℂ) by push_cast; rfl,
      Complex.re_ofReal_mul, Complex.re_sum]
    have e : ∀ g, (hip (fprodU c g * c i ^ t.val) (fprodU c (g + Pi.single i t))).re =
        D - D * ud (fprodU c g * c i ^ t.val) (fprodU c (g + Pi.single i t)) ^ 2 / 2 := by
      intro g
      rw [re_hip_isU ((isU_fprodU c hc g).mul hU) (isU_fprodU c hc _)]
      have h0 : 0 ≤ nsq (fprodU c g * c i ^ t.val - fprodU c (g + Pi.single i t)) / D :=
        div_nonneg (nsq_nonneg _) hDpos.le
      have hsq : ud (fprodU c g * c i ^ t.val) (fprodU c (g + Pi.single i t)) ^ 2 =
          nsq (fprodU c g * c i ^ t.val - fprodU c (g + Pi.single i t)) / D := Real.sq_sqrt h0
      rw [hsq, hDdef]; field_simp
    simp only [e, ahat2]
    rw [sum_sub_distrib, sum_const, card_univ, card_G, nsmul_eq_mul, ← sum_div, ← mul_sum]
    rw [show (9 : ℝ) ^ N = 3 ^ N * 3 ^ N by rw [← mul_pow]; norm_num]
    field_simp
    push_cast
    ring
  rw [hval] at hcs
  have h81 : (0 : ℝ) < 9 ^ N * 9 ^ N := by positivity
  rw [le_div_iff₀ h81]
  have hG0 := nsq_nonneg G
  have hsD := Real.mul_self_sqrt hDpos.le
  have hsG := Real.mul_self_sqrt hG0
  by_cases hpos : 0 ≤ 1 - ahat2 c i t / 2
  · have hX : 0 ≤ (9 : ℝ) ^ N * D * (1 - ahat2 c i t / 2) := by positivity
    have hsq := mul_self_le_mul_self hX hcs
    have : (9 : ℝ) ^ N * D * (1 - ahat2 c i t / 2) * ((9 : ℝ) ^ N * D * (1 - ahat2 c i t / 2)) ≤
        D * nsq G := by
      calc _ ≤ Real.sqrt D * Real.sqrt (nsq G) * (Real.sqrt D * Real.sqrt (nsq G)) := hsq
        _ = Real.sqrt D * Real.sqrt D * (Real.sqrt (nsq G) * Real.sqrt (nsq G)) := by ring
        _ = D * nsq G := by rw [hsD, hsG]
    have h9 : (0 : ℝ) < 9 ^ N * 9 ^ N := by positivity
    have h1 : (9 ^ N * 9 ^ N) * D * (1 - ahat2 c i t / 2) ^ 2 ≤ nsq G := by
      have h' : D * ((9 ^ N * 9 ^ N) * D * (1 - ahat2 c i t / 2) ^ 2) ≤ D * nsq G := by
        nlinarith
      exact le_of_mul_le_mul_left h' hDpos
    have h2 : 1 - ahat2 c i t ≤ (1 - ahat2 c i t / 2) ^ 2 := by
      nlinarith [sq_nonneg (ahat2 c i t / 2)]
    have h3 := mul_le_mul_of_nonneg_left h2 (le_of_lt (mul_pos h9 hDpos))
    nlinarith
  · push Not at hpos
    have : D * (1 - ahat2 c i t) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hDpos.le (by linarith)
    nlinarith


lemma trace_PZPZU_nonneg (c : Fin N → Matrix Ω Ω ℂ) (i : Fin N) (t : Fin 3) :
    0 ≤ (PprojU c * (Zt i t * PprojU c * (Zt i t)ᴴ)).trace.re := by
  rw [traceU_PZPZ]
  set G := (YmatU c)ᴴ * Zt (Ω := Ω) i t * YmatU c
  have e : ((9 : ℂ) ^ N)⁻¹ * ((9 : ℂ) ^ N)⁻¹ * (nsq G : ℂ) =
      ((nsq G / ((9 : ℝ) ^ N * 9 ^ N) : ℝ) : ℂ) := by push_cast; field_simp
  rw [e, Complex.ofReal_re]
  exact div_nonneg (nsq_nonneg _) (by positivity)

/-- Weight moved by the `i`-th twirl: `w ≤ min((â₁² + â₂²)/3, 2/3)`. -/
lemma weightU (c : Fin N → Matrix Ω Ω ℂ) (hc : ∀ i, IsU (c i)) (hD : 0 < Fintype.card Ω)
    (i : Fin N) :
    1 - (PprojU c * ((((3 * Fintype.card Ω : ℕ) : ℂ))⁻¹ • (PprojU c +
      Zt i 1 * PprojU c * (Zt i 1)ᴴ + Zt i 2 * PprojU c * (Zt i 2)ᴴ))).trace.re ≤
      min ((ahat2 c i 1 + ahat2 c i 2) / 3) (2 / 3) := by
  have hDpos : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast hD
  have t1 := trace_PZPZU_ge c hc hD i 1
  have t2 := trace_PZPZU_ge c hc hD i 2
  have n1 := trace_PZPZU_nonneg c i 1
  have n2 := trace_PZPZU_nonneg c i 2
  set x := (PprojU c * (Zt i 1 * PprojU c * (Zt i 1)ᴴ)).trace.re
  set y := (PprojU c * (Zt i 2 * PprojU c * (Zt i 2)ᴴ)).trace.re
  have e : (PprojU c * ((((3 * Fintype.card Ω : ℕ) : ℂ))⁻¹ • (PprojU c +
      Zt i 1 * PprojU c * (Zt i 1)ᴴ + Zt i 2 * PprojU c * (Zt i 2)ᴴ))).trace.re =
      (3 * (Fintype.card Ω : ℝ))⁻¹ * ((Fintype.card Ω : ℝ) + x + y) := by
    rw [Matrix.mul_smul, trace_smul, Matrix.mul_add, Matrix.mul_add, trace_add, trace_add,
      PprojU_idem c hc, PprojU_trace c hc, smul_eq_mul,
      show (((3 * Fintype.card Ω : ℕ) : ℂ))⁻¹ = (((3 * (Fintype.card Ω : ℝ))⁻¹ : ℝ) : ℂ) by
        push_cast; ring, Complex.re_ofReal_mul]
    simp only [Complex.add_re, Complex.natCast_re]
    rfl
  rw [e]
  have key : 1 - (3 * (Fintype.card Ω : ℝ))⁻¹ * ((Fintype.card Ω : ℝ) + x + y) =
      (2 * (Fintype.card Ω : ℝ) - x - y) / (3 * Fintype.card Ω) := by
    field_simp; ring
  rw [key, le_min_iff, div_le_iff₀ (by positivity), div_le_iff₀ (by positivity)]
  constructor
  · rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num)]
    nlinarith
  · nlinarith

/-- **Single-twirl entropy bound** for unitary local actions. -/
theorem twirlEntropyU (c : Fin N → Matrix Ω Ω ℂ) (hc : ∀ i, IsU (c i)) (hD : 0 < Fintype.card Ω)
    (i : Fin N) (hG : GenTwirlBound23) :
    vN (pinch (labelProj i) (rhoSecU c)) ≤ Real.log (Fintype.card Ω) +
      ent (min ((ahat2 c i 1 + ahat2 c i 2) / 3) (2 / 3)) +
      ent (1 - min ((ahat2 c i 1 + ahat2 c i 2) / 3) (2 / 3)) +
      min ((ahat2 c i 1 + ahat2 c i 2) / 3) (2 / 3) * Real.log 2 := by
  rw [sigmaU_eq c hc hD i]
  exact hG ((Fin N → Fin 3) × Ω) (PprojU c) (Zt i 1) (Zt i 2) (Fintype.card Ω) _
    (PprojU_herm c) (PprojU_idem c hc) (PprojU_trace c hc) hD (Zt_unitary i 1) (Zt_unitary i 2)
    (weightU c hc hD i) (min_le_right _ _)

end Lamps
