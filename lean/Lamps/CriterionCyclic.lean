import Lamps.Criterion
import Lamps.HoughtonTools
import Houghton.Analysis.SSAFinal

/-!
# Corollary `cor:cyclic` (Transport by the powers of one element), permutation form

With `t ∈ S` and `Area_R([x, t^k y t^{-k}]) ≤ C k^p` (`x, y ∈ {a, b}`, `k ≥ 1`, `C ≥ 1`, `p ≥ 0`), the
transport words `w_i = t^i` (`0 ≤ i < N`) have pairwise areas `≤ C N^p`, and Theorem `thm:criterion`
gives `log₂ σ_E(r) ≥ ⌊(r / (10⁸ C (2l-1)))^{1/(p+1)}⌋ / 16` for `r > 1`.
-/

namespace Lamps

open Houghton (dH modelSizes profile)

section Cyclic

variable {S ι : Type*} {R : ι → FreeGroup S}

theorem commG_pow_shift (T x y : FreeGroup S) (i k : ℕ) :
    commG (T ^ i * x * (T ^ i)⁻¹) (T ^ (i + k) * y * (T ^ (i + k))⁻¹) =
      T ^ i * commG x (T ^ k * y * (T ^ k)⁻¹) * (T ^ i)⁻¹ := by
  simp only [commG, pow_add]; group

/-- The transport words `t^i` have pairwise areas `≤ ⌊C N^p⌋`. -/
theorem transportAreaLE_pow (a b t : S) (C p : ℝ) (hC : 0 ≤ C) (hp : 0 ≤ p)
    (hcyc : ∀ k : ℕ, 1 ≤ k → ∀ x ∈ [FreeGroup.of a, FreeGroup.of b],
      ∀ y ∈ [FreeGroup.of a, FreeGroup.of b],
      AreaLEGen R (commG x (FreeGroup.of t ^ k * y * (FreeGroup.of t ^ k)⁻¹)) ⌊C * (k : ℝ) ^ p⌋₊)
    (N : ℕ) :
    TransportAreaLE R a b (fun i : Fin N => FreeGroup.of t ^ (i : ℕ)) ⌊C * (N : ℝ) ^ p⌋₊ := by
  have hmono : ∀ k : ℕ, k ≤ N → ⌊C * (k : ℝ) ^ p⌋₊ ≤ ⌊C * (N : ℝ) ^ p⌋₊ := fun k hk =>
    Nat.floor_le_floor (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hk) hp) hC)
  intro i j hij x hx y hy
  have hne : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨k, hk⟩ : ∃ k, (j : ℕ) = i + k := ⟨j - i, by omega⟩
    have h := (hcyc k (by omega) x hx y hy).conj (FreeGroup.of t ^ (i : ℕ))
    refine (h.of_eq ?_).mono (hmono k (by omega))
    simp only; rw [hk, commG_pow_shift]
  · obtain ⟨k, hk⟩ : ∃ k, (i : ℕ) = j + k := ⟨i - j, by omega⟩
    have h := ((hcyc k (by omega) y hy x hx).conj (FreeGroup.of t ^ (j : ℕ))).inv
    refine (h.of_eq ?_).mono (hmono k (by omega))
    simp only; rw [hk, ← commG_pow_shift]; simp only [commG]; group

variable {G : Type*} [Group G] [DecidableEq S] [Fintype S] [Fintype ι]

/-- **Corollary `cor:cyclic`** (permutation form), assuming the sector bound. -/
theorem cyclic_criterion (hS : Houghton.PermSectorBound.{0})
    (π : FreeGroup S →* G) (R : ι → FreeGroup S) (a b t : S) (ia ib iab : ι)
    (hRa : R ia = FreeGroup.of a ^ 2) (hRb : R ib = FreeGroup.of b ^ 2)
    (hRab : R iab = (FreeGroup.of a * FreeGroup.of b) ^ 3)
    (hR1 : ∀ k, π (R k) = 1) (hab1 : π (FreeGroup.of a * FreeGroup.of b) ≠ 1)
    (C p : ℝ) (hC : 1 ≤ C) (hp : 0 ≤ p)
    (hcyc : ∀ k : ℕ, 1 ≤ k → ∀ x ∈ [FreeGroup.of a, FreeGroup.of b],
      ∀ y ∈ [FreeGroup.of a, FreeGroup.of b],
      AreaLEGen R (commG x (FreeGroup.of t ^ k * y * (FreeGroup.of t ^ k)⁻¹)) ⌊C * (k : ℝ) ^ p⌋₊)
    (r : ℝ) (hr : 1 < r) :
    (∀ n ∈ modelSizes (criterionChunk π R a b) r,
      (⌊(r / (10 ^ 8 * C * (2 * maxLen R - 1))) ^ (1 / (p + 1))⌋₊ : ℝ) / 16 ≤ Real.logb 2 n) ∧
    (∀ m : ℕ, profile (criterionChunk π R a b) r = m →
      (⌊(r / (10 ^ 8 * C * (2 * maxLen R - 1))) ^ (1 / (p + 1))⌋₊ : ℝ) / 16 ≤ Real.logb 2 m) := by
  set l : ℝ := ((maxLen R : ℕ) : ℝ) with hldef
  have hl2 : (2 : ℝ) ≤ l := by
    have h := Finset.le_sup (f := fun k => (R k).toWord.length) (Finset.mem_univ ia)
    have h2 : (R ia).toWord.length = 2 := by rw [hRa]; exact FreeGroup.norm_of_pow a 2
    have : 2 ≤ maxLen R := by unfold maxLen; omega
    rw [hldef]; exact_mod_cast this
  set K : ℝ := 10 ^ 8 * C * (2 * l - 1) with hK
  have hK0 : 0 < K := by rw [hK]; have : (0 : ℝ) < 2 * l - 1 := by linarith
                         positivity
  set X : ℝ := r / K with hX
  have hX0 : 0 ≤ X := div_nonneg (by linarith) hK0.le
  set N : ℕ := ⌊X ^ (1 / (p + 1))⌋₊ with hN
  have hmodel : ∀ n ∈ modelSizes (criterionChunk π R a b) r, (N : ℝ) / 16 ≤ Real.logb 2 n := by
    intro n hn
    rcases Nat.eq_zero_or_pos N with hN0 | hNpos
    · rw [hN0, Nat.cast_zero, zero_div]
      exact Real.logb_nonneg (by norm_num) (by exact_mod_cast hn.1)
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
    have hNp : (1 : ℝ) ≤ (N : ℝ) ^ p := Real.one_le_rpow hN1 hp
    have hΛ1 : 1 ≤ ⌊C * (N : ℝ) ^ p⌋₊ := Nat.le_floor (by push_cast; nlinarith)
    have hΛ : (⌊C * (N : ℝ) ^ p⌋₊ : ℝ) ≤ C * (N : ℝ) ^ p := Nat.floor_le (by positivity)
    have hNX : (N : ℝ) ^ (p + 1) ≤ X := by
      have h1 : (N : ℝ) ≤ X ^ (1 / (p + 1)) := Nat.floor_le (by positivity)
      calc (N : ℝ) ^ (p + 1) ≤ (X ^ (1 / (p + 1))) ^ (p + 1) :=
            Real.rpow_le_rpow (Nat.cast_nonneg _) h1 (by linarith)
        _ = X := by rw [← Real.rpow_mul hX0, one_div_mul_cancel (by linarith), Real.rpow_one]
    have hsplit : (N : ℝ) ^ (p + 1) = (N : ℝ) ^ p * N :=
      Real.rpow_add_one (by positivity) p
    have hr' : (10 : ℝ) ^ 8 * N * (⌊C * (N : ℝ) ^ p⌋₊ : ℕ) * (2 * maxLen R - 1) ≤ r := by
      rw [← hldef]
      have hl1 : (0 : ℝ) ≤ 2 * l - 1 := by linarith
      calc (10 : ℝ) ^ 8 * N * (⌊C * (N : ℝ) ^ p⌋₊ : ℕ) * (2 * l - 1)
          ≤ (10 : ℝ) ^ 8 * N * (C * (N : ℝ) ^ p) * (2 * l - 1) := by gcongr
        _ = K * (N : ℝ) ^ (p + 1) := by rw [hsplit, hK]; ring
        _ ≤ K * X := by gcongr
        _ = r := by rw [hX]; field_simp
    exact (counting_criterion hS π R a b ia ib iab hRa hRb hRab hR1 hab1
      (fun i : Fin N => FreeGroup.of t ^ (i : ℕ)) _ hΛ1
      (transportAreaLE_pow a b t C p (by linarith) hp hcyc N) r hr').1 n hn
  exact ⟨hmodel, fun m hm => hmodel m (Houghton.mem_of_profile_eq hm)⟩

/-- **Corollary `cor:cyclic`** (permutation form), unconditionally. -/
theorem cyclic_criterion_final
    (π : FreeGroup S →* G) (R : ι → FreeGroup S) (a b t : S) (ia ib iab : ι)
    (hRa : R ia = FreeGroup.of a ^ 2) (hRb : R ib = FreeGroup.of b ^ 2)
    (hRab : R iab = (FreeGroup.of a * FreeGroup.of b) ^ 3)
    (hR1 : ∀ k, π (R k) = 1) (hab1 : π (FreeGroup.of a * FreeGroup.of b) ≠ 1)
    (C p : ℝ) (hC : 1 ≤ C) (hp : 0 ≤ p)
    (hcyc : ∀ k : ℕ, 1 ≤ k → ∀ x ∈ [FreeGroup.of a, FreeGroup.of b],
      ∀ y ∈ [FreeGroup.of a, FreeGroup.of b],
      AreaLEGen R (commG x (FreeGroup.of t ^ k * y * (FreeGroup.of t ^ k)⁻¹)) ⌊C * (k : ℝ) ^ p⌋₊)
    (r : ℝ) (hr : 1 < r) :
    (∀ n ∈ modelSizes (criterionChunk π R a b) r,
      (⌊(r / (10 ^ 8 * C * (2 * maxLen R - 1))) ^ (1 / (p + 1))⌋₊ : ℝ) / 16 ≤ Real.logb 2 n) ∧
    (∀ m : ℕ, profile (criterionChunk π R a b) r = m →
      (⌊(r / (10 ^ 8 * C * (2 * maxLen R - 1))) ^ (1 / (p + 1))⌋₊ : ℝ) / 16 ≤ Real.logb 2 m) :=
  cyclic_criterion (Houghton.permSectorBound_of_SSA Houghton.qit_commutingPinchingSSA) π R a b t
    ia ib iab hRa hRb hRab hR1 hab1 C p hC hp hcyc r hr

end Cyclic

end Lamps
