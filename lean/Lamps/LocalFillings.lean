import Lamps.Exchange

/-!
# `lem:exchange` with a shift `p^j`, semantic form (Douglas–Mghirbi v1.2.0, Section `sec:fillings`)

`exchange_sem`: if `W`, `U` are words in `p, q` whose permutations are supported in a finite set
`A` of points `≤ n` of ray 1, `Z0` is a word in the letters of `K_k` such that
`ev2 (fK k Z0) * ev2 (P^j)⁻¹` is supported in a finite set `B` of such points and `fK k Z0`
fixes `1, …, k`, and `U` agrees with `W P^j` on `1, …, k`, then
`Area(W p^j f p^{-j} W⁻¹ · U f⁻¹ U⁻¹) ≤ 2 D + |Z0| + 10 |A ∪ B| n` for `δ_H(ℓ) ≤ D` at the
explicit length `ℓ = |W| + j + |U| + c (|Z0| + 10 |A ∪ B| n)`.
-/

namespace Lamps

open Houghton (Y ρH)

theorem exchange_sem (f : F) (K : Fin 2 → F) (k c n j : ℕ)
    (hfK : ∀ w, ιpq (fK k w) = FreeGroup.lift K w) (hS : ∀ i, AreaLE (comm f (K i)) 1)
    (hc : ∀ i : Fin 2, (![ζ k * P, ζ k * Q] i).norm ≤ c)
    (Z0 : FreeGroup (Fin 2)) (B : Finset Y)
    (hBpts : ∀ y ∈ B, ∃ u, 1 ≤ u ∧ u ≤ n ∧ y = pt u)
    (hZ0supp : ∀ y, y ∉ B → (ev2 (fK k Z0) * (ev2 (P ^ j))⁻¹) y = y)
    (hZ0fix : ∀ u, 1 ≤ u → u ≤ k → ev2 (fK k Z0) (pt u) = pt u)
    (W U : FreeGroup (Fin 2)) (A : Finset Y)
    (hApts : ∀ y ∈ A, ∃ u, 1 ≤ u ∧ u ≤ n ∧ y = pt u)
    (hW : ∀ y, y ∉ A → ev2 W y = y) (hU : ∀ y, y ∉ A → ev2 U y = y)
    (hagree : ∀ u, 1 ≤ u → u ≤ k → ev2 U (pt u) = ev2 (W * P ^ j) (pt u)) {D : ℕ}
    (hD : DehnLE (W.norm + j + U.norm + c * (Z0.norm + 10 * (A ∪ B).card * n)) D) :
    AreaLE (ιpq (W * P ^ j) * f * (ιpq (W * P ^ j))⁻¹ * (ιpq U * f⁻¹ * (ιpq U)⁻¹))
      (2 * D + (Z0.norm + 10 * (A ∪ B).card * n)) := by
  classical
  set g' := ev2 (fK k Z0) * (ev2 (W * P ^ j))⁻¹ * ev2 U with hg'
  have hsupp : ∀ y, y ∉ A ∪ B → g' y = y := by
    intro y hy
    rw [Finset.mem_union, not_or] at hy
    have hWinv : (ev2 W)⁻¹ y = y := by
      rw [Equiv.Perm.inv_eq_iff_eq]; exact (hW y hy.1).symm
    have e : g' = (ev2 (fK k Z0) * (ev2 (P ^ j))⁻¹) * ((ev2 W)⁻¹ * ev2 U) := by
      rw [hg', map_mul]; group
    rw [e, Equiv.Perm.mul_apply]
    have h2 : ((ev2 W)⁻¹ * ev2 U) y = y := by rw [Equiv.Perm.mul_apply, hU y hy.1, hWinv]
    rw [h2]
    exact hZ0supp y hy.2
  have hpts : ∀ y ∈ A ∪ B, ∃ u, 1 ≤ u ∧ u ≤ n ∧ y = pt u := by
    intro y hy
    rcases Finset.mem_union.mp hy with h | h
    · exact hApts y h
    · exact hBpts y h
  have hfix : ∀ u, 1 ≤ u → u ≤ k → g' (pt u) = pt u := by
    intro u h1 h2
    rw [hg', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hagree u h1 h2]
    rw [show (ev2 (W * P ^ j))⁻¹ ((ev2 (W * P ^ j)) (pt u)) = pt u from
      (ev2 (W * P ^ j)).symm_apply_apply (pt u), hZ0fix u h1 h2]
  obtain ⟨Z', hZ', hZ'len⟩ := exists_stab_Z k n (A ∪ B) g' hsupp hpts hfix
  set Z := Z0⁻¹ * Z' with hZ
  have hev : ev2 (fK k Z) = ev2 ((W * P ^ j)⁻¹ * U) := by
    rw [hZ, map_mul, map_mul, map_inv, hZ', hg']
    simp only [map_mul, map_inv]
    group
  have hZlen : Z.norm ≤ Z0.norm + 10 * (A ∪ B).card * n := by
    have := FreeGroup.norm_mul_le Z0⁻¹ Z'
    rw [FreeGroup.norm_inv_eq] at this
    exact this.trans (by
      have : Z'.norm ≤ 10 * (A ∪ B).card * n := hZ'len
      omega)
  have hm : ((W * P ^ j)⁻¹ * U * (fK k Z)⁻¹).toWord.length ≤
      W.norm + j + U.norm + c * (Z0.norm + 10 * (A ∪ B).card * n) := by
    have h1 := FreeGroup.norm_mul_le ((W * P ^ j)⁻¹ * U) (fK k Z)⁻¹
    have h2 := FreeGroup.norm_mul_le (W * P ^ j)⁻¹ U
    have h3 := FreeGroup.norm_mul_le W (P ^ j)
    have h4 := norm_lift_le ![ζ k * P, ζ k * Q] c hc Z
    have h5 : (P ^ j).norm = j := FreeGroup.norm_of_pow 0 j
    have h7 : ((W * P ^ j)⁻¹ * U * (fK k Z)⁻¹).norm ≤ ((W * P ^ j)⁻¹ * U).norm + (fK k Z).norm := by
      have := FreeGroup.norm_mul_le ((W * P ^ j)⁻¹ * U) (fK k Z)⁻¹
      rwa [FreeGroup.norm_inv_eq] at this
    have h8 : ((W * P ^ j)⁻¹ * U).norm ≤ (W * P ^ j).norm + U.norm := by
      have := FreeGroup.norm_mul_le (W * P ^ j)⁻¹ U
      rwa [FreeGroup.norm_inv_eq] at this
    rw [FreeGroup.norm_inv_eq] at h1 h2
    have h6 : (fK k Z).norm ≤ c * (Z0.norm + 10 * (A ∪ B).card * n) :=
      h4.trans (Nat.mul_le_mul_left _ hZlen)
    show ((W * P ^ j)⁻¹ * U * (fK k Z)⁻¹).norm ≤ _
    omega
  have h := exchange_gen f K k hfK hS (W * P ^ j) U Z hev hD hm
  have hZl : Z.toWord.length ≤ Z0.norm + 10 * (A ∪ B).card * n := hZlen
  exact h.mono (by omega)

/-! ### The instances `f = t` (`k = 1`, `j ≤ 2`) and `f = d` (`k = 2`, `j = 0`) -/

theorem ζ_one : ζ 1 = S := by simp [ζ, σk]

theorem fK1_of0 : fK 1 (FreeGroup.of 0) = S * P := by
  simp [fK, FreeGroup.lift_apply_of, ζ_one]

theorem pY_pt (x : ℕ) (hx : 1 ≤ x) : pY (pt x) = pt (x + 1) := by
  simpa using pY_pow_pt 1 x hx


theorem norm_P : P.norm = 1 := FreeGroup.norm_of 0
theorem norm_Q : Q.norm = 1 := FreeGroup.norm_of 1

theorem norm_S_le : S.norm ≤ 4 := by
  have h1 := FreeGroup.norm_mul_le (P * Q * P⁻¹) Q⁻¹
  have h2 := FreeGroup.norm_mul_le (P * Q) P⁻¹
  have h3 := FreeGroup.norm_mul_le P Q
  simp only [FreeGroup.norm_inv_eq, norm_P, norm_Q] at h1 h2 h3
  show (P * Q * P⁻¹ * Q⁻¹).norm ≤ 4
  omega

/-- The letters of `fK 1` (`K₁ = (s p, s q)`) have length at most `5`. -/
theorem hc1 : ∀ i : Fin 2, (![ζ 1 * P, ζ 1 * Q] i).norm ≤ 5 := by
  intro i
  fin_cases i
  · show (ζ 1 * P).norm ≤ 5
    have := FreeGroup.norm_mul_le (ζ 1) P
    rw [ζ_one, norm_P] at *; have := norm_S_le; omega
  · show (ζ 1 * Q).norm ≤ 5
    have := FreeGroup.norm_mul_le (ζ 1) Q
    rw [ζ_one, norm_Q] at *; have := norm_S_le; omega

theorem ζ_two : ζ 2 = P * S * P⁻¹ * S := by simp [ζ, σk, ζ_one]

/-- The letters of `fK 2` (`K₂ = (B s p, B s q)`) have length at most `11`. -/
theorem hc2 : ∀ i : Fin 2, (![ζ 2 * P, ζ 2 * Q] i).norm ≤ 11 := by
  have hζ : (ζ 2).norm ≤ 10 := by
    rw [ζ_two]
    have h1 := FreeGroup.norm_mul_le (P * S * P⁻¹) S
    have h2 := FreeGroup.norm_mul_le (P * S) P⁻¹
    have h3 := FreeGroup.norm_mul_le P S
    simp only [FreeGroup.norm_inv_eq, norm_P] at h1 h2 h3
    have := norm_S_le
    omega
  intro i
  fin_cases i
  · show (ζ 2 * P).norm ≤ 11
    have := FreeGroup.norm_mul_le (ζ 2) P
    rw [norm_P] at this; omega
  · show (ζ 2 * Q).norm ≤ 11
    have := FreeGroup.norm_mul_le (ζ 2) Q
    rw [norm_Q] at this; omega

theorem ev2_SP_pt1 : ev2 (S * P) (pt 1) = pt 1 := by
  rw [map_mul, ev2_S, ev2_P, Equiv.Perm.mul_apply, pY_pt 1 le_rfl]
  exact Equiv.swap_apply_right _ _

/-- Shift `j = 1`: `ev2 (fK 1 (of 0)) * ev2 (P)⁻¹ = (1 2)`. -/
theorem shift1_supp (y : Y) (hy : y ∉ ({pt 1, pt 2} : Finset Y)) :
    (ev2 (fK 1 (FreeGroup.of 0)) * (ev2 (P ^ 1))⁻¹) y = y := by
  have e : ev2 (fK 1 (FreeGroup.of 0)) * (ev2 (P ^ 1))⁻¹ = ev2 S := by
    rw [fK1_of0, pow_one, map_mul]; group
  rw [e, ev2_S]
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
  exact Equiv.swap_apply_of_ne_of_ne hy.1 hy.2

theorem shift1_fix (u : ℕ) (h1 : 1 ≤ u) (h2 : u ≤ 1) :
    ev2 (fK 1 (FreeGroup.of 0)) (pt u) = pt u := by
  obtain rfl : u = 1 := by omega
  rw [fK1_of0]; exact ev2_SP_pt1

/-- Shift `j = 2`: `ev2 (fK 1 (of 0)²) * ev2 (P²)⁻¹ = s · p s p⁻¹`, supported in `{1, 2, 3}`. -/
theorem shift2_supp (y : Y) (hy : y ∉ ({pt 1, pt 2, pt 3} : Finset Y)) :
    (ev2 (fK 1 (FreeGroup.of 0 ^ 2)) * (ev2 (P ^ 2))⁻¹) y = y := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
  have e : ev2 (fK 1 (FreeGroup.of 0 ^ 2)) * (ev2 (P ^ 2))⁻¹ =
      ev2 S * (ev2 P * ev2 S * (ev2 P)⁻¹) := by
    rw [map_pow, fK1_of0, map_pow, map_pow, map_mul, sq, sq]; group
  rw [e, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ev2_S, ev2_P]
  have hq : pY⁻¹ y ≠ pt 1 ∧ pY⁻¹ y ≠ pt 2 := by
    constructor
    · intro h; apply hy.2.1; rw [← pY.apply_symm_apply y]; exact congrArg pY h ▸ pY_pt 1 le_rfl
    · intro h; apply hy.2.2; rw [← pY.apply_symm_apply y]; exact congrArg pY h ▸ pY_pt 2 (by norm_num)
  rw [Equiv.swap_apply_of_ne_of_ne hq.1 hq.2, show pY (pY⁻¹ y) = y from pY.apply_symm_apply y]
  exact Equiv.swap_apply_of_ne_of_ne hy.1 hy.2.1

theorem shift2_fix (u : ℕ) (h1 : 1 ≤ u) (h2 : u ≤ 1) :
    ev2 (fK 1 (FreeGroup.of 0 ^ 2)) (pt u) = pt u := by
  obtain rfl : u = 1 := by omega
  rw [map_pow, fK1_of0, map_pow, sq, Equiv.Perm.mul_apply, ev2_SP_pt1, ev2_SP_pt1]

end Lamps
