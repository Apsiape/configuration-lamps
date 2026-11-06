import Lamps.Fillings
import Lamps.HoughtonWords
import Mathlib.Tactic.Linarith

/-!
# Lemma `lem:exchange` (change of transporter), semantic form

`exchange`: let `W, U` be words in `p, q` and `Z` a word in the two letters of `K₁` (for `f = t`,
`k = 1`) or `K₂` (for `f = d`, `k = 2`) such that `fK k Z` represents the same permutation as
`W⁻¹ U` (so `W⁻¹ U` lies in the stabilizer `H^{(k)}`).  If `δ_H(m) ≤ D` and the word
`N = W⁻¹ U (fK k Z)⁻¹` has reduced length `≤ m`, then
`Area(W f W⁻¹ · U f⁻¹ U⁻¹) ≤ 2 D + |Z|` (paper: `≤ 2 δ_H(1500 n) + 122 n`).
-/

namespace Lamps

open Houghton (Y ρH)

theorem ev2_eq_one_imp (w : FreeGroup (Fin 2)) (h : ev2 w = 1) : ρH (ιab w) = 1 := by
  rw [← lampsH_one_iff, rhoΓ_ιpq, h, map_one]

theorem lift_eq_kWord (K : Fin 2 → F) (Z : FreeGroup (Fin 2)) :
    FreeGroup.lift K Z = kWord K Z.toWord := by
  conv_lhs => rw [← FreeGroup.mk_toWord (x := Z)]
  rw [FreeGroup.lift_mk, kWord]
  congr 1
  apply List.map_congr_left
  intro x _
  cases x.2 <;> simp

/-- **Lemma `lem:exchange`**, generic in the pair `K` and the prototype `f`. -/
theorem exchange_gen (f : F) (K : Fin 2 → F) (k : ℕ)
    (hfK : ∀ w, ιpq (fK k w) = FreeGroup.lift K w) (hS : ∀ i, AreaLE (comm f (K i)) 1)
    (W U Z : FreeGroup (Fin 2)) (hev : ev2 (fK k Z) = ev2 (W⁻¹ * U)) {m D : ℕ}
    (hD : DehnLE m D) (hm : (W⁻¹ * U * (fK k Z)⁻¹).toWord.length ≤ m) :
    AreaLE (ιpq W * f * (ιpq W)⁻¹ * (ιpq U * f⁻¹ * (ιpq U)⁻¹)) (2 * D + Z.toWord.length) := by
  have h1 : ρH (ιab (W⁻¹ * U * (fK k Z)⁻¹)) = 1 := by
    apply ev2_eq_one_imp
    rw [map_mul, map_inv, ← hev, mul_inv_cancel]
  have hN := hD _ hm h1
  have hN' : AreaLE ((ιpq W)⁻¹ * ιpq U * (FreeGroup.lift K Z)⁻¹) D := by
    simpa [map_mul, map_inv, hfK] using hN
  have hZ : AreaLE (comm f (FreeGroup.lift K Z)) Z.toWord.length := by
    rw [lift_eq_kWord]
    exact areaLE_comm_kWord f K hS Z.toWord
  exact exchange_core f (ιpq W) (ιpq U) (FreeGroup.lift K Z) hN' hZ

theorem exchange_t (W U Z : FreeGroup (Fin 2)) (hev : ev2 (fK 1 Z) = ev2 (W⁻¹ * U)) {m D : ℕ}
    (hD : DehnLE m D) (hm : (W⁻¹ * U * (fK 1 Z)⁻¹).toWord.length ≤ m) :
    AreaLE (ιpq W * t * (ιpq W)⁻¹ * (ιpq U * t⁻¹ * (ιpq U)⁻¹)) (2 * D + Z.toWord.length) :=
  exchange_gen t K1 1 fK_one
    (by intro i; fin_cases i; exacts [AreaLEGen.rel 5, AreaLEGen.rel 6]) W U Z hev hD hm

theorem exchange_d (W U Z : FreeGroup (Fin 2)) (hev : ev2 (fK 2 Z) = ev2 (W⁻¹ * U)) {m D : ℕ}
    (hD : DehnLE m D) (hm : (W⁻¹ * U * (fK 2 Z)⁻¹).toWord.length ≤ m) :
    AreaLE (ιpq W * d * (ιpq W)⁻¹ * (ιpq U * d⁻¹ * (ιpq U)⁻¹)) (2 * D + Z.toWord.length) :=
  exchange_gen d K2 2 fK_two
    (by intro i; fin_cases i; exacts [AreaLEGen.rel 7, AreaLEGen.rel 8]) W U Z hev hD hm

/-- Reduced length is subadditive and inversion-invariant (for the length hypotheses). -/
theorem norm_mul_le' (x y : FreeGroup (Fin 2)) : (x * y).toWord.length ≤
    x.toWord.length + y.toWord.length := FreeGroup.norm_mul_le x y

theorem norm_inv' (x : FreeGroup (Fin 2)) : x⁻¹.toWord.length = x.toWord.length :=
  FreeGroup.norm_inv_eq

/-! ### Supports of products of transpositions -/

/-- The endpoints of a list of transpositions. -/
def ends (ts : List (ℕ × ℕ)) : Finset Y := (ts.map fun x => pt x.1).toFinset ∪
  (ts.map fun x => pt x.2).toFinset

theorem tprod_apply_of_not_mem (ts : List (ℕ × ℕ)) (y : Y) (hy : y ∉ ends ts) :
    tprod ts y = y := by
  induction ts with
  | nil => simp [tprod]
  | cons x ts ih =>
    simp only [ends, List.map_cons, List.toFinset_cons, Finset.mem_union, Finset.mem_insert,
      not_or] at hy
    have ih' := ih (by simp only [ends, Finset.mem_union, not_or]; exact ⟨hy.1.2, hy.2.2⟩)
    simp only [tprod, List.map_cons, List.prod_cons, Equiv.Perm.mul_apply] at ih' ⊢
    rw [ih']
    exact Equiv.swap_apply_of_ne_of_ne hy.1.1 hy.2.1

theorem card_ends_le (ts : List (ℕ × ℕ)) : (ends ts).card ≤ 2 * ts.length := by
  unfold ends
  refine (Finset.card_union_le _ _).trans ?_
  have h1 := List.toFinset_card_le (ts.map fun x => pt x.1)
  have h2 := List.toFinset_card_le (ts.map fun x => pt x.2)
  simp only [List.length_map] at h1 h2
  omega

/-- A stabilizer word: a permutation supported in a finite set `A` of points `≤ n` of ray 1 and
fixing `1, …, k` is `ev2 (fK k Z)` for a word `Z` in the letters of `K_k` with `|Z| ≤ 10 |A| n`
(Lemma `lem:stabilizers`(b), via L2's `stabilizer_word`). -/
theorem exists_stab_Z (k n : ℕ) (A : Finset Y) (g : Equiv.Perm Y)
    (hA : ∀ y, y ∉ A → g y = y) (hApts : ∀ y ∈ A, ∃ u, 1 ≤ u ∧ u ≤ n ∧ y = pt u)
    (hfix : ∀ u, 1 ≤ u → u ≤ k → g (pt u) = pt u) :
    ∃ Z : FreeGroup (Fin 2), ev2 (fK k Z) = g ∧ Z.toWord.length ≤ 10 * A.card * n := by
  classical
  by_cases hg : g = 1
  · exact ⟨1, by rw [map_one, map_one, hg], by simp⟩
  obtain ⟨y₀, hy₀⟩ : ∃ y, g y ≠ y := by
    by_contra hcon
    push Not at hcon
    exact hg (Equiv.ext hcon)
  set M := A.filter fun y => g y ≠ y with hMdef
  have hM : ∀ y, g y ≠ y ↔ y ∈ M := by
    intro y
    rw [hMdef, Finset.mem_filter]
    constructor
    · intro h; exact ⟨by_contra fun hy => h (hA y hy), h⟩
    · exact fun h => h.2
  have hpts : ∀ y ∈ M, ∃ u, k < u ∧ u ≤ n ∧ y = pt u := by
    intro y hy
    obtain ⟨u, hu1, hun, rfl⟩ := hApts y (Finset.mem_filter.mp hy).1
    refine ⟨u, ?_, hun, rfl⟩
    by_contra hku
    exact (hM _).mpr hy (hfix u hu1 (by omega))
  have hm : 2 ≤ M.card := by
    have h1 : y₀ ∈ M := (hM y₀).mp hy₀
    have h2 : g y₀ ∈ M := (hM _).mp (fun h => hy₀ (g.injective h))
    have hne : g y₀ ≠ y₀ := hy₀
    calc 2 = ({y₀, g y₀} : Finset Y).card := by rw [Finset.card_pair hne.symm]
      _ ≤ M.card := Finset.card_le_card (by
          intro z hz
          rcases Finset.mem_insert.mp hz with rfl | hz
          · exact h1
          · rw [Finset.mem_singleton.mp hz]; exact h2)
  obtain ⟨Z, hZ, hlen⟩ := stabilizer_word k n M g hM hpts hm
  refine ⟨Z, hZ, ?_⟩
  have hMA : M.card ≤ A.card := Finset.card_filter_le _ _
  have : 10 * (M.card - 1) * n ≤ 10 * A.card * n :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
  exact (le_of_lt hlen).trans this

/-- Reduced length under a substitution whose letters have length `≤ c`. -/
theorem norm_lift_le {G : Type*} [DecidableEq G] (f : Fin 2 → FreeGroup G) (c : ℕ)
    (hf : ∀ i, (f i).norm ≤ c) (w : FreeGroup (Fin 2)) :
    (FreeGroup.lift f w).norm ≤ c * w.toWord.length := by
  have key : ∀ L : List (Fin 2 × Bool),
      ((L.map fun x => cond x.2 (f x.1) (f x.1)⁻¹).prod).norm ≤ c * L.length := by
    intro L
    induction L with
    | nil => simp
    | cons x L ih =>
      rw [List.map_cons, List.prod_cons, List.length_cons]
      refine (FreeGroup.norm_mul_le _ _).trans ?_
      have hx : (cond x.2 (f x.1) (f x.1)⁻¹).norm ≤ c := by
        cases x.2 <;> simp [FreeGroup.norm_inv_eq, hf]
      nlinarith
  have e : FreeGroup.lift f w = (w.toWord.map fun x => cond x.2 (f x.1) (f x.1)⁻¹).prod := by
    conv_lhs => rw [← FreeGroup.mk_toWord (x := w)]
    exact FreeGroup.lift_mk
  rw [e]
  exact key _

/-- **`lem:exchange` for transporters that are products of transpositions** (`j = 0`).
`W = twprod tsW`, `U = twprod tsU` with at most `l` transpositions in total among the points
`1, …, n`, agreeing on the points `1, …, k`; then the change of transporter costs at most
`2 D + 20 l n` once `δ_H(|W| + |U| + c · 20 l n) ≤ D`, where `c` bounds the letters of `fK k`. -/
theorem exchange_twprod (f : F) (K : Fin 2 → F) (k c n l : ℕ)
    (hfK : ∀ w, ιpq (fK k w) = FreeGroup.lift K w) (hS : ∀ i, AreaLE (comm f (K i)) 1)
    (hc : ∀ i : Fin 2, (![ζ k * P, ζ k * Q] i).norm ≤ c)
    (tsW tsU : List (ℕ × ℕ)) (hl : tsW.length + tsU.length ≤ l)
    (hW : ∀ t ∈ tsW, 1 ≤ t.1 ∧ t.1 < t.2 ∧ t.2 ≤ n) (hU : ∀ t ∈ tsU, 1 ≤ t.1 ∧ t.1 < t.2 ∧ t.2 ≤ n)
    (hagree : ∀ u, 1 ≤ u → u ≤ k → tprod tsW (pt u) = tprod tsU (pt u))
    (hevW : ev2 (twprod tsW) = tprod tsW) (hevU : ev2 (twprod tsU) = tprod tsU) {D : ℕ}
    (hD : DehnLE ((twprod tsW).norm + (twprod tsU).norm + c * (20 * l * n)) D) :
    AreaLE (ιpq (twprod tsW) * f * (ιpq (twprod tsW))⁻¹ *
      (ιpq (twprod tsU) * f⁻¹ * (ιpq (twprod tsU))⁻¹)) (2 * D + 20 * l * n) := by
  classical
  set g := (tprod tsW)⁻¹ * tprod tsU with hg
  have hA : ∀ y, y ∉ ends tsW ∪ ends tsU → g y = y := by
    intro y hy
    rw [Finset.mem_union, not_or] at hy
    rw [hg, Equiv.Perm.mul_apply, tprod_apply_of_not_mem tsU y hy.2, Equiv.Perm.inv_eq_iff_eq,
      tprod_apply_of_not_mem tsW y hy.1]
  have hApts : ∀ y ∈ ends tsW ∪ ends tsU, ∃ u, 1 ≤ u ∧ u ≤ n ∧ y = pt u := by
    intro y hy
    simp only [ends, Finset.mem_union, List.mem_toFinset, List.mem_map] at hy
    rcases hy with ((⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩) | (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩))
    · have := hW t ht; exact ⟨t.1, by omega, by omega, rfl⟩
    · have := hW t ht; exact ⟨t.2, by omega, by omega, rfl⟩
    · have := hU t ht; exact ⟨t.1, by omega, by omega, rfl⟩
    · have := hU t ht; exact ⟨t.2, by omega, by omega, rfl⟩
  have hfix : ∀ u, 1 ≤ u → u ≤ k → g (pt u) = pt u := by
    intro u h1 h2
    rw [hg, Equiv.Perm.mul_apply, ← hagree u h1 h2]
    exact (tprod tsW).symm_apply_apply (pt u)
  obtain ⟨Z, hZ, hZlen⟩ := exists_stab_Z k n _ g hA hApts hfix
  have hcard : (ends tsW ∪ ends tsU).card ≤ 2 * l :=
    (Finset.card_union_le _ _).trans (by have := card_ends_le tsW; have := card_ends_le tsU; omega)
  have hZl : Z.toWord.length ≤ 20 * l * n :=
    hZlen.trans (by nlinarith [Nat.mul_le_mul_right n (Nat.mul_le_mul_left 10 hcard)])
  have hev : ev2 (fK k Z) = ev2 ((twprod tsW)⁻¹ * twprod tsU) := by
    rw [hZ, map_mul, map_inv, hevW, hevU]
  have hm : ((twprod tsW)⁻¹ * twprod tsU * (fK k Z)⁻¹).toWord.length ≤
      (twprod tsW).norm + (twprod tsU).norm + c * (20 * l * n) := by
    have h1 := FreeGroup.norm_mul_le ((twprod tsW)⁻¹ * twprod tsU) (fK k Z)⁻¹
    have h2 := FreeGroup.norm_mul_le (twprod tsW)⁻¹ (twprod tsU)
    have h3 := norm_lift_le ![ζ k * P, ζ k * Q] c hc Z
    rw [FreeGroup.norm_inv_eq] at h1 h2
    have h4 : (fK k Z).norm ≤ c * (20 * l * n) := h3.trans (Nat.mul_le_mul_left _ hZl)
    show ((twprod tsW)⁻¹ * twprod tsU * (fK k Z)⁻¹).norm ≤ _
    omega
  have h := exchange_gen f K k hfK hS _ _ Z hev hD hm
  exact h.mono (by omega)

end Lamps
