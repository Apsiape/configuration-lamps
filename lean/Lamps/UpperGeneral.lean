import Lamps.UpperFinal
import Lamps.UpperCocycle

/-!
# Proposition `prop:upper` (hash models), general clause

Paper (`sections/part1-profile.tex`, Proposition `prop:upper`): *let `E'` be a chunk of `Γ` each of
whose elements is a product of at most `ℓ ≥ 1` of the generators `p, q, t, c, a` and their inverses.
Then `log σ_{E'}(r) ≤ 500 ℓ² r log(2 + r)` for `r > 1`* (`log = log₂`).

Formalization notes / deviations:
* "product of at most `ℓ` generators and inverses" is a letter word `L : List (Fin 5 × Bool)` of
  length `≤ ℓ` with `ρΓ' (FreeGroup.mk L) = g`; letter `(i, true)` is the `i`-th of `p, q, t, c, a`
  (`Lamps.Basic`), `(i, false)` its inverse.
* `E'` is any `Finset Γ` (no symmetry / `1 ∈ E'` assumption is needed).
* The range is `1 ≤ r`, which contains the paper's `r > 1`.
* The model form gives a model size `n` with `log₂ n ≤ 500 ℓ² r log₂(2+r)`; the profile form bounds
  `σ_{E'}(r) = Houghton.profile E' r` by such an `n`.
* Internally `k = ⌈log₂(8ℓ²r)⌉` (the paper writes `⌈log(4ℓ²r)⌉` but then uses `2^k < 8ℓ²r`).
-/

namespace Lamps

/-- **Proposition `prop:upper`, model form.** -/
theorem prop_upper (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (E' : Finset Γ)
    (hE : ∀ g ∈ E', ∃ L : List (Fin 5 × Bool), L.length ≤ ℓ ∧ ρΓ' (FreeGroup.mk L) = g)
    (r : ℝ) (hr : 1 ≤ r) :
    ∃ n ∈ Houghton.modelSizes E' r,
      Real.logb 2 (n : ℝ) ≤ 500 * (ℓ : ℝ) ^ 2 * r * Real.logb 2 (2 + r) := by
  obtain ⟨h1, h2⟩ := UpperArith.upper_arith ℓ hℓ r hr
  refine ⟨_, model_mem letterCocycleSpec ⌈8 * (ℓ : ℝ) * r⌉₊
    ⌈Real.logb 2 (8 * (ℓ : ℝ) ^ 2 * r)⌉₊ ℓ hℓ ?_ E' hE r ?_, ?_⟩
  · have hl : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg _
    have : (ℓ : ℝ) ≤ ⌈8 * (ℓ : ℝ) * r⌉₊ := le_trans (by nlinarith) (Nat.le_ceil _)
    exact_mod_cast this
  · rw [← one_div]; exact h1.le
  · rw [card_model]; exact h2

/-- **Proposition `prop:upper`, profile form:** `log₂ σ_{E'}(r) ≤ 500 ℓ² r log₂(2 + r)`, i.e.
`σ_{E'}(r) ≤ n` for some `n` with `log₂ n ≤ 500 ℓ² r log₂(2 + r)` (also `n ≤ 2^{500 ℓ² r log₂(2+r)}`). -/
theorem prop_upper_profile (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (E' : Finset Γ)
    (hE : ∀ g ∈ E', ∃ L : List (Fin 5 × Bool), L.length ≤ ℓ ∧ ρΓ' (FreeGroup.mk L) = g)
    (r : ℝ) (hr : 1 ≤ r) :
    ∃ n : ℕ, Houghton.profile E' r ≤ n ∧
      Real.logb 2 (n : ℝ) ≤ 500 * (ℓ : ℝ) ^ 2 * r * Real.logb 2 (2 + r) ∧
      (n : ℝ) ≤ 2 ^ (500 * (ℓ : ℝ) ^ 2 * r * Real.logb 2 (2 + r)) := by
  obtain ⟨n, hn, hle⟩ := prop_upper ℓ hℓ E' hE r hr
  have hpos : 0 < n := hn.1
  refine ⟨n, Houghton.profile_le_of_mem hn, hle, ?_⟩
  refine le_trans (Real.rpow_logb (b := 2) (by norm_num) (by norm_num) ?_).symm.le
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) hle)
  exact_mod_cast hpos

end Lamps
