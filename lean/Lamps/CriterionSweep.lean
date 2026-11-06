import FiniteLean.Hypotheses.PermSweepBound
import Lamps.Criterion

/-!
# Theorem `thm:sweep` (Sweep counting criterion), permutation form: reduction to the entropy step

The proof of Theorem `thm:sweep` has four steps: relator errors (`transfer_model_gen`), native
rounding of each transported pair to an exact local `S₃`-action `u_i` (here: Houghton's
`roundInv`/`round3`, `u_i(a) = x_i`, `u_i(b) = x_i c_i`, within `10 ε` of the raw words on the six
normal forms), one ordered error `d([u_i(h), U_{>i}], 1) ≤ (Λ_N + 40 N) ε`, and the entropy estimate
"Entropy from this error". The last step (a sector argument with whole suffixes, not the pairwise
sector bound) is **not** formalized: it is the named hypothesis `PermSweepBound` below, stated in
exactly the form the reduction delivers (`T² ≤ 2 · 1/20000`, displacement `≥ 1/4`).
-/

namespace Lamps

open Finset Equiv
open Houghton (dH modelSizes profile)

section Sweep

variable {S ι : Type*}

/-- The sweep hypothesis of Theorem `thm:sweep`:
`Area_R([W_i(h), W_{i+1}(g_{i+1}) ⋯ W_N(g_N)]) ≤ Λ` for all `i`, `h ∈ 𝒩`, `g_j ∈ 𝒩`,
`W_i(g) = w_i g w_i⁻¹`. -/
def SweepAreaLE (R : ι → FreeGroup S) (a b : S) {N : ℕ} (w : Fin N → FreeGroup S) (Λ : ℕ) :
    Prop :=
  ∀ i (h : Fin 6) (g : Fin N → Fin 6),
    AreaLEGen R (commG (w i * nfG (FreeGroup.of a) (FreeGroup.of b) h * (w i)⁻¹)
      (sufW i fun j => w j * nfG (FreeGroup.of a) (FreeGroup.of b) (g j) * (w j)⁻¹)) Λ

/-- **Theorem `thm:sweep`, model form**, from the entropy step `PermSweepBound`. -/
theorem sweep_criterion_model (hS : PermSweepBound) (R : ι → FreeGroup S) (a b : S)
    (ia ib iab : ι) (hRa : R ia = FreeGroup.of a ^ 2) (hRb : R ib = FreeGroup.of b ^ 2)
    (hRab : R iab = (FreeGroup.of a * FreeGroup.of b) ^ 3) {N : ℕ} (hN : 1 ≤ N)
    (w : Fin N → FreeGroup S) (Λ : ℕ) (hw : SweepAreaLE R a b w Λ)
    {Ω : Type} [Fintype Ω] [DecidableEq Ω] (φ : FreeGroup S →* Perm Ω) (δ : ℝ)
    (hrel : ∀ k, dH (φ (R k)) 1 ≤ δ)
    (hab : 1 / 2 ≤ dH (φ (FreeGroup.of a * FreeGroup.of b)) 1)
    (hδ : ((Λ : ℝ) + 40 * N) * δ ≤ 1 / 20000) :
    (N : ℝ) / 16 ≤ Real.logb 2 (Fintype.card Ω) := by
  have hδ0 : 0 ≤ δ := (Houghton.dH_nonneg _ _).trans (hrel ia)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNδ : δ ≤ N * δ := by nlinarith
  have hΛδ : 0 ≤ (Λ : ℝ) * δ := mul_nonneg (Nat.cast_nonneg _) hδ0
  have hδs : δ ≤ 1 / 800000 := by nlinarith
  -- the conjugation homomorphisms `ψ_i = φ ∘ W_i`
  let ψ : Fin N → FreeGroup S →* Perm Ω := fun i => φ.comp (MulAut.conj (w i)).toMonoidHom
  have hψ : ∀ i z, ψ i z = φ (w i * z * (w i)⁻¹) := fun i z => rfl
  set A : Fin N → Perm Ω := fun i => ψ i (FreeGroup.of a) with hA
  set B : Fin N → Perm Ω := fun i => ψ i (FreeGroup.of b) with hB
  have hconj : ∀ i (z : FreeGroup S), ψ i z = φ (w i) * φ z * (φ (w i))⁻¹ := by
    intro i z; rw [hψ]; simp only [map_mul, map_inv]
  have hA2 : ∀ i, dH (A i * A i) 1 ≤ δ := by
    intro i
    rw [hA]; simp only
    rw [← map_mul, hconj, ← pow_two, ← hRa, Houghton.dH_conj]; exact hrel ia
  have hB2 : ∀ i, dH (B i * B i) 1 ≤ δ := by
    intro i
    rw [hB]; simp only
    rw [← map_mul, hconj, ← pow_two, ← hRb, Houghton.dH_conj]; exact hrel ib
  have h3 : ∀ i, dH ((A i * B i) ^ 3) 1 ≤ δ := by
    intro i
    rw [hA, hB]; simp only
    rw [← map_mul, ← map_pow, hconj, ← hRab, Houghton.dH_conj]; exact hrel iab
  have hγ : ∀ i, 1 / 2 ≤ dH (A i * B i) 1 := by
    intro i; rw [hA, hB]; simp only; rw [← map_mul, hconj, Houghton.dH_conj]; exact hab
  -- the exact actions
  set x := rx A with hx
  set c := rc A B with hc
  have hxA : ∀ i, dH (x i) (A i) ≤ δ := fun i => (Houghton.dH_roundInv _).trans (hA2 i)
  have hxc : ∀ i, dH (x i * c i) (B i) ≤ 8 * δ := by
    intro i
    have hT : dH (rT B i) (B i) ≤ δ := (Houghton.dH_roundInv _).trans (hB2 i)
    have hST : dH (rx A i * rT B i) (A i * B i) ≤ 2 * δ := by
      have := Houghton.dH_mul_le (rx A i) (rT B i) (A i) (B i); linarith [hxA i]
    have hcube : dH ((rx A i * rT B i) ^ 3) ((A i * B i) ^ 3) ≤ 3 * (2 * δ) := by
      have := Houghton.dH_pow_le (rx A i * rT B i) (A i * B i) 3
      push_cast at this; linarith
    have hr := Houghton.dH_round3 (rx A i * rT B i)
    have t1 := Houghton.dH_triangle ((rx A i * rT B i) ^ 3) ((A i * B i) ^ 3) 1
    have h7 : dH (c i) (rx A i * rT B i) ≤ 7 * δ := by
      rw [hc]; unfold rc; linarith [h3 i]
    have hxx : x i * (rx A i * rT B i) = rT B i := by
      rw [← mul_assoc, hx]; unfold rx; rw [Houghton.roundInv_mul_self, one_mul]
    have t := Houghton.dH_triangle (x i * c i) (x i * (rx A i * rT B i)) (B i)
    rw [Houghton.dH_mul_left, hxx] at t
    linarith
  have hu : ∀ i h, dH (nfG (x i) (x i * c i) h) (nfG (A i) (B i) h) ≤ 10 * δ := by
    intro i h
    have := dH_nfG _ _ _ _ δ (8 * δ) (hxA i) (hxc i) h; linarith
  have hnfψ : ∀ i h, nfG (A i) (B i) h = ψ i (nfG (FreeGroup.of a) (FreeGroup.of b) h) := by
    intro i h; rw [map_nfG]
  refine hS Ω N x c (fun i => Houghton.round3_pow_three _) (fun i => Houghton.roundInv_sq _)
    (fun i => Houghton.round3_conj _ _ (Houghton.roundInv_mul_self _)
      (Houghton.roundInv_mul_self _)) (fun i => ?_) (fun i h g => ?_)
  · have h := dH_rc A B δ hA2 hB2 h3 i
    have t := Houghton.dH_triangle (A i * B i) (c i) 1
    rw [Houghton.dH_comm (A i * B i) (c i)] at t
    linarith [hγ i]
  · set u := nfG (x i) (x i * c i) h
    set P := nfG (A i) (B i) h
    set U := sufW i fun j => nfG (x j) (x j * c j) (g j)
    set V := sufW i fun j => nfG (A j) (B j) (g j)
    have huP : dH u P ≤ 10 * δ := hu i h
    have hUV : dH U V ≤ N * (10 * δ) := dH_sufW i _ _ _ (by linarith) fun j => hu j (g j)
    have hPV : dH (P * V) (V * P) ≤ Λ * δ := by
      have harea := dH_le_of_areaLEGen R φ δ hrel hδ0 (hw i h g)
      rw [Houghton.dH_comm_eq]
      have e : φ (commG (w i * nfG (FreeGroup.of a) (FreeGroup.of b) h * (w i)⁻¹)
          (sufW i fun j => w j * nfG (FreeGroup.of a) (FreeGroup.of b) (g j) * (w j)⁻¹)) =
          P * V * P⁻¹ * V⁻¹ := by
        simp only [commG, map_mul, map_inv, map_sufW, P, V, hnfψ, hψ]
      rw [e] at harea; exact harea
    rw [commG, ← Houghton.dH_comm_eq]
    have e1 := Houghton.dH_mul_le u U P V
    have e2 := Houghton.dH_mul_le V P U u
    rw [Houghton.dH_comm V U, Houghton.dH_comm P u] at e2
    have t1 := Houghton.dH_triangle (u * U) (P * V) (U * u)
    have t2 := Houghton.dH_triangle (P * V) (V * P) (U * u)
    have : (Λ + 20 * N + 20 : ℝ) * δ ≤ ((Λ : ℝ) + 40 * N) * δ := by nlinarith
    linarith

end Sweep

/-! ### The chunk form -/

section SweepChunk

variable {G : Type*} [Group G] {S ι : Type*} [DecidableEq S] [Fintype S] [Fintype ι]

/-- **Theorem `thm:sweep` (Sweep counting criterion), permutation form**, from the entropy step
`PermSweepBound`: if `(Λ_N + 40 N)(2l - 1) ≤ r / 20000` then every model size `n` of `E` at
accuracy `r` has `log₂ n ≥ N/16` (and so does every finite value of `σ_E(r)`). -/
theorem sweep_criterion (hS : PermSweepBound)
    (π : FreeGroup S →* G) (R : ι → FreeGroup S) (a b : S) (ia ib iab : ι)
    (hRa : R ia = FreeGroup.of a ^ 2) (hRb : R ib = FreeGroup.of b ^ 2)
    (hRab : R iab = (FreeGroup.of a * FreeGroup.of b) ^ 3)
    (hR1 : ∀ k, π (R k) = 1) (hab1 : π (FreeGroup.of a * FreeGroup.of b) ≠ 1)
    {N : ℕ} (hN : 1 ≤ N) (w : Fin N → FreeGroup S) (Λ : ℕ) (hw : SweepAreaLE R a b w Λ)
    (r : ℝ) (hr : ((Λ : ℝ) + 40 * N) * (2 * maxLen R - 1) ≤ r / 20000) :
    (∀ n ∈ modelSizes (criterionChunk π R a b) r, (N : ℝ) / 16 ≤ Real.logb 2 n) ∧
      (∀ m : ℕ, profile (criterionChunk π R a b) r = m → (N : ℝ) / 16 ≤ Real.logb 2 m) := by
  have hmodel : ∀ n ∈ modelSizes (criterionChunk π R a b) r, (N : ℝ) / 16 ≤ Real.logb 2 n := by
    intro n hn
    obtain ⟨hn0, f, hf⟩ := hn
    have hl2 : 2 ≤ maxLen R := by
      have h := Finset.le_sup (f := fun k => (R k).toWord.length) (mem_univ ia)
      have h2 : (R ia).toWord.length = 2 := by rw [hRa]; exact FreeGroup.norm_of_pow a 2
      unfold maxLen; omega
    have hl2' : (2 : ℝ) ≤ maxLen R := by exact_mod_cast hl2
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hΛ0 : (0 : ℝ) ≤ Λ := Nat.cast_nonneg _
    have hr8 : (800000 : ℝ) ≤ r := by nlinarith
    have hrpos : 0 < r := by linarith
    obtain ⟨hrel, hab⟩ := transfer_model_gen hR1 hab1 (by omega) hf
    have hab' : 1 / 2 ≤ dH (phiOfG π f (FreeGroup.of a * FreeGroup.of b)) 1 := by
      have : 4 / r ≤ 1 / 2 := by rw [div_le_iff₀ hrpos]; linarith
      linarith
    have hδ : ((Λ : ℝ) + 40 * N) * ((2 * maxLen R - 1) / r) ≤ 1 / 20000 := by
      rw [← mul_div_assoc, div_le_iff₀ hrpos]; linarith
    simpa using sweep_criterion_model hS R a b ia ib iab hRa hRb hRab hN w Λ hw (phiOfG π f) _
      hrel hab' hδ
  exact ⟨hmodel, fun m hm => hmodel m (Houghton.mem_of_profile_eq hm)⟩

end SweepChunk

end Lamps
