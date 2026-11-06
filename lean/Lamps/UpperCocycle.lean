import Lamps.UpperCocycleSpec
import Lamps.Clock

/-!
# Step 1 of `prop:upper`: the letter cocycles lie in `K_{W_R}` (`R = 2m + 3`)

Proves `Lamps.LetterCocycleSpec` (Lemma `lem:clock`): `p^{±1}, q^{±1}` via `permKW` and
`clock_restrict`; `t^{±1}` via `tauKW` at `g_z⁻¹ e₁`; `c^{±1}` via `tvKW` and `lampKW (sa·sb)^{±1}`;
`a^{±1}` via `lampKW sa^{±1}`. Uses that `g_z⁻¹` maps `e₁, e₂` into `Y_R` (`gz_inv_e_mem`).
-/

namespace Lamps

open Hash
open Houghton (Y)

/-! ### Heights move by at most one per letter -/

theorem ht_pY (y : Y) : ht (pY y) ≤ ht y + 1 := by
  obtain ⟨⟨_ | _ | _ | i, hi⟩, _ | j⟩ := y <;>
    first | omega | (show ht (Houghton.aInv _) ≤ _; simp only [Houghton.aInv, ht]; omega)
theorem ht_pY_inv (y : Y) : ht (pY⁻¹ y) ≤ ht y + 1 := by
  obtain ⟨⟨_ | _ | _ | i, hi⟩, _ | j⟩ := y <;>
    first | omega | (show ht (Houghton.aFun _) ≤ _; simp only [Houghton.aFun, ht]; omega)
theorem ht_qY (y : Y) : ht (qY y) ≤ ht y + 1 := by
  obtain ⟨⟨_ | _ | _ | i, hi⟩, _ | j⟩ := y <;>
    first | omega | (show ht (Houghton.bInv _) ≤ _; simp only [Houghton.bInv, ht]; omega)
theorem ht_qY_inv (y : Y) : ht (qY⁻¹ y) ≤ ht y + 1 := by
  obtain ⟨⟨_ | _ | _ | i, hi⟩, _ | j⟩ := y <;>
    first | omega | (show ht (Houghton.bFun _) ≤ _; simp only [Houghton.bFun, ht]; omega)

theorem ht_pow (f : Equiv.Perm Y) (h1 : ∀ y, ht (f y) ≤ ht y + 1) :
    ∀ (n : ℕ) (y : Y), ht ((f ^ n) y) ≤ ht y + n
  | 0, y => by simp
  | n + 1, y => by
    rw [pow_succ', Equiv.Perm.mul_apply]
    have := h1 ((f ^ n) y); have := ht_pow f h1 n y; omega

theorem ht_zpow (f : Equiv.Perm Y) (h1 : ∀ y, ht (f y) ≤ ht y + 1)
    (h2 : ∀ y, ht (f⁻¹ y) ≤ ht y + 1) (n : ℤ) (y : Y) : ht ((f ^ n) y) ≤ ht y + n.natAbs := by
  rcases n with n | n
  · rw [Int.ofNat_eq_natCast, zpow_natCast]; simpa using ht_pow f h1 n y
  · rw [zpow_negSucc, ← inv_pow]; simpa using ht_pow f⁻¹ h2 (n + 1) y

theorem ht_gz_inv (z : ℤ × ℤ) (y : Y) : ht ((gz z)⁻¹ y) ≤ ht y + z.1.natAbs + z.2.natAbs := by
  rw [gz, mul_inv_rev, ← zpow_neg, ← zpow_neg, Equiv.Perm.mul_apply]
  have a1 := ht_zpow pY ht_pY ht_pY_inv (-z.1) y
  have a2 := ht_zpow qY ht_qY ht_qY_inv (-z.2) ((pY ^ (-z.1)) y)
  rw [Int.natAbs_neg] at a1 a2
  omega

/-- For `z ∈ B_m`, `g_z⁻¹` maps `e₁, e₂` into `Y_{2m+3}`. -/
theorem gz_inv_e_mem (m : ℕ) (z : ℤ × ℤ) (hz1 : |z.1| ≤ m) (hz2 : |z.2| ≤ m) :
    (gz z)⁻¹ e1 ∈ YR (2 * m + 3) ∧ (gz z)⁻¹ e2 ∈ YR (2 * m + 3) := by
  have h1 := natAbs_le_of_abs_le hz1
  have h2 := natAbs_le_of_abs_le hz2
  have b1 := ht_gz_inv z e1
  have b2 := ht_gz_inv z e2
  simp only [mem_YR]
  simp only [ht, e1, e2] at b1 b2 ⊢
  omega

/-! ### The letters -/

lemma mk_single (i : Fin 5) (b : Bool) :
    FreeGroup.mk [(i, b)] = if b then FreeGroup.of i else (FreeGroup.of i)⁻¹ := by
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, FreeGroup.of, FreeGroup.inv_mk]; rfl
  · rfl

lemma lamp_inv (τ : S3) : (lamp ∅ τ)⁻¹ = lamp ∅ τ⁻¹ :=
  inv_eq_of_mul_eq_one_right (by rw [lamp_mul, mul_inv_cancel, lamp_one])

/-- Conjugation by the clock for letters with `π = 0`. -/
lemma rho_conj0 (z : ℤ × ℤ) (w : F) :
    ρΓ ((gzW (z + (0, 0)))⁻¹ * w * gzW z) = hV ((gz z)⁻¹) * ρΓ w * (hV ((gz z)⁻¹))⁻¹ := by
  have hz : z + (0, 0) = z := by ext <;> simp
  rw [hz, map_mul, map_mul, map_inv, rho_gzW, map_inv (hV), inv_inv]

lemma hV_conj_lamp (σ : Equiv.Perm Y) (τ : S3) : hV σ * lamp ∅ τ * (hV σ)⁻¹ = lamp ∅ τ := by
  rw [hV_lamp0, mul_assoc, mul_inv_cancel, mul_one]

lemma lam_lampKW {R : ℕ} {τ : S3} {w : Finset (PR R)} (h : (lampKW R τ).lam w ≠ 1) : w = ∅ := by
  by_contra hw; exact h (by simp [lampKW, hw])

/-- **Step 1** (`lem:clock` in `K_{W_R}`). -/
theorem letterCocycleSpec : LetterCocycleSpec := by
  intro m z hz1 hz2 l
  set R := 2 * m + 3 with hR
  obtain ⟨he1, he2⟩ := gz_inv_e_mem m z hz1 hz2
  set σ := (gz z)⁻¹ with hσ
  rcases l with ⟨i, b⟩
  -- p and q
  have hpq : ∀ (s : Equiv.Perm Y) (e : ℤ × ℤ) (w : F), ClockGen s e → ρΓ w = hV s →
      FreeGroup.mk [(i, b)] = w → piL (i, b) = e →
      ∃ γ : KW (PR R), realF R γ = ⇑(ρΓ ((gzW (z + piL (i, b)))⁻¹ * FreeGroup.mk [(i, b)] * gzW z)) ∧
        ∀ w w', γ.lam w ≠ 1 → γ.lam w' ≠ 1 → w = w' := by
    intro s e w hs hw hmk hpi
    have hg := (clock_restrict m z hz1 hz2 s e hs).1
    refine ⟨permKW R (restrictR R _ hg), ?_, fun w w' h => absurd rfl h⟩
    rw [realF_permKW, hmk, hpi, (rho_cocycle z (z + e) w s hw).1]
  -- the letters with `π = 0`: realized by `γ` with `realF γ = hV σ * G * (hV σ)⁻¹`
  have h0 : ∀ (w : F) (γ : KW (PR R)), piL (i, b) = (0, 0) → FreeGroup.mk [(i, b)] = w →
      realF R γ = ⇑(hV σ * ρΓ w * (hV σ)⁻¹) → (∀ w w', γ.lam w ≠ 1 → γ.lam w' ≠ 1 → w = w') →
      ∃ γ : KW (PR R), realF R γ = ⇑(ρΓ ((gzW (z + piL (i, b)))⁻¹ * FreeGroup.mk [(i, b)] * gzW z)) ∧
        ∀ w w', γ.lam w ≠ 1 → γ.lam w' ≠ 1 → w = w' := by
    intro w γ hpi hmk hγ hlam
    exact ⟨γ, by rw [hpi, hmk, rho_conj0, hγ], hlam⟩
  -- t
  have ht_conj : hV σ * tau {e1} * (hV σ)⁻¹ = tau {σ e1} := by
    rw [hV_conj_tau, Finset.map_singleton]; rfl
  have htau : realF R (tauKW R {⟨σ e1, he1⟩}) = ⇑(tau {σ e1}) := by
    rw [realF_tauKW, Finset.map_singleton]; rfl
  -- c
  have hx : (⟨σ e1, he1⟩ : PR R) ≠ ⟨σ e2, he2⟩ := by
    intro h; have := σ.injective (congrArg Subtype.val h); exact e1_ne_e2 this
  have hdP : ⇑(hV σ * dP * (hV σ)⁻¹) = realF R (tvKW R _ _ hx) := by
    rw [hV_conj_dP, realF_tvKW]
  have hlamL : ∀ σ' : Equiv.Perm Y, ∀ τ : S3, lamp ∅ τ * (hV σ')⁻¹ = (hV σ')⁻¹ * lamp ∅ τ := by
    intro σ' τ; rw [← map_inv, hV_lamp0]
  fin_cases i <;> cases b
  · exact hpq pY⁻¹ (-1, 0) p⁻¹ (Or.inr (Or.inl ⟨rfl, rfl⟩)) (by rw [map_inv, rho_p, map_inv])
      (by rw [mk_single]; rfl) rfl
  · exact hpq pY (1, 0) p (Or.inl ⟨rfl, rfl⟩) rho_p (by rw [mk_single]; rfl) rfl
  · exact hpq qY⁻¹ (0, -1) q⁻¹ (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))) (by rw [map_inv, rho_q, map_inv])
      (by rw [mk_single]; rfl) rfl
  · exact hpq qY (0, 1) q (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) rho_q (by rw [mk_single]; rfl) rfl
  · -- t⁻¹
    refine h0 t⁻¹ (tauKW R {⟨σ e1, he1⟩}) rfl (by rw [mk_single]; rfl) ?_ (fun w w' h => absurd rfl h)
    rw [map_inv ρΓ t, rho_t, tau_inv, ht_conj, htau]
  · -- t
    refine h0 t (tauKW R {⟨σ e1, he1⟩}) rfl (by rw [mk_single]; rfl) ?_ (fun w w' h => absurd rfl h)
    rw [rho_t, ht_conj, htau]
  · -- c⁻¹
    refine h0 c⁻¹ (KW.mul (lampKW R (sa * sb)⁻¹) (tvKW R _ _ hx)) rfl (by rw [mk_single]; rfl) ?_ ?_
    · have e : hV σ * ρΓ c⁻¹ * (hV σ)⁻¹ = lamp ∅ (sa * sb)⁻¹ * (hV σ * dP * (hV σ)⁻¹) := by
        rw [map_inv ρΓ c, rho_c, mul_inv_rev, dP_inv, lamp_inv, ← mul_assoc (hV σ), hV_lamp0]; group
      funext x
      rw [e, realF_mul, realF_lampKW, Equiv.Perm.mul_apply, ← hdP]
    · intro w w' h h'
      have key : ∀ w, (KW.mul (lampKW R (sa * sb)⁻¹) (tvKW R _ _ hx)).lam w =
          (lampKW R (sa * sb)⁻¹).lam w := fun w => by simp [KW.mul, tvKW]
      rw [key] at h h'
      rw [lam_lampKW h, lam_lampKW h']
  · -- c
    refine h0 c (KW.mul (tvKW R _ _ hx) (lampKW R (sa * sb))) rfl (by rw [mk_single]; rfl) ?_ ?_
    · have e : hV σ * ρΓ c * (hV σ)⁻¹ = (hV σ * dP * (hV σ)⁻¹) * lamp ∅ (sa * sb) := by
        rw [rho_c, mul_assoc (hV σ), mul_assoc dP, hlamL]; group
      funext x
      rw [e, realF_mul, realF_lampKW, Equiv.Perm.mul_apply, ← hdP]
    · intro w w' h h'
      have key : ∀ w, (KW.mul (tvKW R _ _ hx) (lampKW R (sa * sb))).lam w =
          (lampKW R (sa * sb)).lam ((tvKW R _ _ hx).g.symm w) := fun w => by simp [KW.mul, tvKW]
      rw [key] at h h'
      exact (tvKW R _ _ hx).g.symm.injective ((lam_lampKW h).trans (lam_lampKW h').symm)
  · -- a⁻¹
    refine h0 a⁻¹ (lampKW R sa⁻¹) rfl (by rw [mk_single]; rfl) ?_ ?_
    · rw [map_inv ρΓ a, rho_a, lamp_inv, hV_conj_lamp, realF_lampKW]
    · intro w w' h h'; rw [lam_lampKW h, lam_lampKW h']
  · -- a
    refine h0 a (lampKW R sa) rfl (by rw [mk_single]; rfl) ?_ ?_
    · rw [rho_a, hV_conj_lamp, realF_lampKW]
    · intro w w' h h'; rw [lam_lampKW h, lam_lampKW h']

end Lamps
