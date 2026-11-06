import Lamps.Group
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Tactic.Ring

/-!
# Lemmas `lem:transpositions` (H1) and `lem:stabilizers` (H2) of `app-houghton`

Words in `p, q` are elements of `FreeGroup (Fin 2)` (`P = of 0`, `Q = of 1`); in `Γ` they are read
through `ιpq`, and they act on `Y` (left action, Mathlib product) by `ev2 = θ ∘ ιab`, with
`ev2 P = pY`, `ev2 Q = qY` and `ρΓ (ιpq w) = hV (ev2 w)`. The point `x ≥ 1` of ray 1 is `pt x`.
Lengths are reduced lengths `FreeGroup.norm`.
-/

namespace Lamps

open Houghton (Y aPerm bPerm alPerm ρH)

/-- The letters `p, q` of `FreeGroup (Fin 2)`. -/
def P : FreeGroup (Fin 2) := FreeGroup.of 0
def Q : FreeGroup (Fin 2) := FreeGroup.of 1
/-- `α = [p, q]`. -/
def S : FreeGroup (Fin 2) := P * Q * P⁻¹ * Q⁻¹

/-- Evaluation of a word in `p, q` as a permutation of `Y` (left action). -/
def ev2 : FreeGroup (Fin 2) →* Equiv.Perm Y := θ.comp ιab

theorem ev2_P : ev2 P = pY := by
  show θ (ιab (FreeGroup.of 0)) = pY; simp [ιab, FreeGroup.lift_apply_of, θ_a]
theorem ev2_Q : ev2 Q = qY := by
  show θ (ιab (FreeGroup.of 1)) = qY; simp [ιab, FreeGroup.lift_apply_of, θ_b]

/-- The meaning in `Γ`: `ρΓ (ιpq w) = hV (ev2 w)`. -/
theorem rhoΓ_ιpq (w : FreeGroup (Fin 2)) : ρΓ (ιpq w) = hV (ev2 w) := by
  rw [← κ_ιab, MonoidHom.comp_apply, rho_κ_apply]; rfl

/-- The point `x ≥ 1` of ray 1. -/
def pt (x : ℕ) : Y := (0, x - 1)

theorem ev2_S : ev2 S = Equiv.swap (pt 1) (pt 2) := by
  simp only [S, map_mul, map_inv, ev2_P, ev2_Q, θ_comm_ab, Houghton.alPerm_eq_swap,
    Equiv.swap_inv]; rfl

theorem pY_pow_pt (j x : ℕ) (hx : 1 ≤ x) : (pY ^ j) (pt x) = pt (x + j) := by
  have := Houghton.aPerm_inv_pow_apply j (x - 1)
  simp only [pY, pt]; rw [this]; congr 1; omega

/-! ### (a) `σ_k` and `ω_{x,y}` -/

/-- `σ_k = p^k α p^{-k}`. -/
def σk (k : ℕ) : FreeGroup (Fin 2) := P ^ k * S * (P ^ k)⁻¹

theorem ev2_σk (k : ℕ) : ev2 (σk k) = Equiv.swap (pt (k + 1)) (pt (k + 2)) := by
  rw [σk, map_mul, map_mul, map_inv, ev2_S, map_pow, ev2_P, ← Equiv.swap_apply_apply,
    pY_pow_pt k 1 le_rfl, pY_pow_pt k 2 (by omega)]
  congr 2 <;> omega

/-- `ω_{x,y} = p^{x-1}(αp)^{y-x-1}(αp^{-1})^{y-x-1} α p^{1-x}`. -/
def ω (x y : ℕ) : FreeGroup (Fin 2) :=
  P ^ (x - 1) * (S * P) ^ (y - x - 1) * (S * P⁻¹) ^ (y - x - 1) * S * (P ^ (x - 1))⁻¹

/-- The free identity `ω_{x,y} = σ_{x-1} ω_{x+1,y} σ_{x-1}` (`y ≥ x + 2`). -/
theorem ω_step (x d : ℕ) (hx : 1 ≤ x) :
    ω x (x + 2 + d) = σk (x - 1) * ω (x + 1) (x + 2 + d) * σk (x - 1) := by
  obtain ⟨x, rfl⟩ : ∃ x', x = x' + 1 := ⟨x - 1, by omega⟩
  simp only [ω, σk, show x + 1 + 2 + d - (x + 1) - 1 = d + 1 by omega,
    show x + 1 + 2 + d - (x + 1 + 1) - 1 = d by omega, Nat.add_sub_cancel]
  rw [pow_succ' (S * P) d, pow_succ (S * P⁻¹) d, pow_succ P x]
  generalize (S * P) ^ d = U
  generalize (S * P⁻¹) ^ d = V
  group

theorem ω_base (x : ℕ) : ω x (x + 1) = σk (x - 1) := by
  simp [ω, σk, mul_assoc]

/-- Evaluation of `ω` under any substitution `f` whose `σ_j` are the shifted transpositions. -/
theorem ev_ω_gen (f : FreeGroup (Fin 2) →* FreeGroup (Fin 2)) (o : ℕ)
    (hσ : ∀ j, ev2 (f (σk j)) = Equiv.swap (pt (o + j + 1)) (pt (o + j + 2))) :
    ∀ d x, 1 ≤ x → ev2 (f (ω x (x + 1 + d))) = Equiv.swap (pt (o + x)) (pt (o + x + 1 + d))
  | 0, x, hx => by
    rw [ω_base, hσ]; congr 2 <;> omega
  | d + 1, x, hx => by
    rw [show x + 1 + (d + 1) = x + 2 + d by omega, ω_step x d hx, map_mul, map_mul, map_mul,
      map_mul, hσ, show x + 2 + d = x + 1 + 1 + d by omega, ev_ω_gen f o hσ d (x + 1) (by omega)]
    have e1 : o + (x - 1) + 1 = o + x := by omega
    have e2 : o + (x - 1) + 2 = o + (x + 1) := by omega
    rw [e1, e2]
    have hne1 : pt (o + x) ≠ pt (o + (x + 1)) := by simp [pt]; omega
    have hne2 : pt (o + x) ≠ pt (o + (x + 1) + 1 + d) := by simp [pt]; omega
    have hne3 : pt (o + (x + 1)) ≠ pt (o + (x + 1) + 1 + d) := by simp [pt]; omega
    rw [show Equiv.swap (pt (o + x)) (pt (o + (x + 1))) * Equiv.swap (pt (o + (x + 1)))
        (pt (o + (x + 1) + 1 + d)) * Equiv.swap (pt (o + x)) (pt (o + (x + 1))) =
        Equiv.swap ((Equiv.swap (pt (o + x)) (pt (o + (x + 1)))) (pt (o + (x + 1))))
          ((Equiv.swap (pt (o + x)) (pt (o + (x + 1)))) (pt (o + (x + 1) + 1 + d))) by
        rw [Equiv.swap_apply_apply, Equiv.swap_inv]]
    rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne (Ne.symm hne2) (Ne.symm hne3)]
    congr 2; omega

lemma norm_pow_le (w : FreeGroup (Fin 2)) : ∀ k : ℕ, FreeGroup.norm (w ^ k) ≤ k * FreeGroup.norm w
  | 0 => by simp
  | k + 1 => by
    rw [pow_succ]
    exact (FreeGroup.norm_mul_le _ _).trans (by have := norm_pow_le w k; rw [Nat.succ_mul]; omega)

lemma norm_S : FreeGroup.norm S ≤ 4 := by
  unfold S
  refine (FreeGroup.norm_mul_le _ _).trans ?_
  have h1 := FreeGroup.norm_mul_le (P * Q) P⁻¹
  have h2 := FreeGroup.norm_mul_le P Q
  simp only [FreeGroup.norm_inv_eq, P, Q, FreeGroup.norm_of] at h1 h2 ⊢
  omega

lemma norm_ω (x y : ℕ) : FreeGroup.norm (ω x y) ≤ 2 * (x - 1) + 10 * (y - x - 1) + 4 := by
  unfold ω
  have hP : FreeGroup.norm P = 1 := FreeGroup.norm_of _
  have a1 := norm_pow_le P (x - 1)
  have a2 := norm_pow_le (S * P) (y - x - 1)
  have a3 := norm_pow_le (S * P⁻¹) (y - x - 1)
  have b1 := FreeGroup.norm_mul_le S P
  have b2 := FreeGroup.norm_mul_le S P⁻¹
  have c1 := FreeGroup.norm_mul_le (P ^ (x - 1)) ((S * P) ^ (y - x - 1))
  have c2 := FreeGroup.norm_mul_le (P ^ (x - 1) * (S * P) ^ (y - x - 1)) ((S * P⁻¹) ^ (y - x - 1))
  have c3 := FreeGroup.norm_mul_le (P ^ (x - 1) * (S * P) ^ (y - x - 1) * (S * P⁻¹) ^ (y - x - 1)) S
  have c4 := FreeGroup.norm_mul_le
    (P ^ (x - 1) * (S * P) ^ (y - x - 1) * (S * P⁻¹) ^ (y - x - 1) * S) (P ^ (x - 1))⁻¹
  have hS := norm_S
  simp only [FreeGroup.norm_inv_eq, hP] at *
  have d2 : (y - x - 1) * FreeGroup.norm (S * P) ≤ (y - x - 1) * 5 := Nat.mul_le_mul_left _ (by omega)
  have d3 : (y - x - 1) * FreeGroup.norm (S * P⁻¹) ≤ (y - x - 1) * 5 :=
    Nat.mul_le_mul_left _ (by omega)
  omega

/-- **Lemma `lem:transpositions` (a)**: `σ_k = (k+1 k+2)`, and for `1 ≤ x < y` the word `ω_{x,y}`
represents `(x y)` and has length `≤ 10y - 8x - 8 < 10y`. -/
theorem transposition_word (x y : ℕ) (hx : 1 ≤ x) (hxy : x < y) :
    ev2 (ω x y) = Equiv.swap (pt x) (pt y) ∧ FreeGroup.norm (ω x y) + 8 * x + 8 ≤ 10 * y ∧
      FreeGroup.norm (ω x y) < 10 * y := by
  have h := ev_ω_gen (MonoidHom.id _) 0 (fun j => by simpa using ev2_σk j) (y - x - 1) x hx
  simp only [MonoidHom.id_apply, Nat.zero_add] at h
  rw [show x + 1 + (y - x - 1) = y by omega] at h
  refine ⟨h, ?_, ?_⟩ <;> have := norm_ω x y <;> omega

/-! ### (b) Permutations of `{1, …, n}` as products of transpositions -/

section PermWord

variable (E : FreeGroup (Fin 2) →* Equiv.Perm Y) (tw : ℕ → ℕ → FreeGroup (Fin 2)) (lo n : ℕ)

/-- The symmetric transposition word. -/
def twS (u v : ℕ) : FreeGroup (Fin 2) := if u < v then tw u v else tw v u

lemma pt_inj {u v : ℕ} (hu : 1 ≤ u) (hv : 1 ≤ v) (h : pt u = pt v) : u = v := by
  simp [pt] at h; omega

open Classical in
/-- Generic form of (b): with transposition words `tw u v` (`lo ≤ u < v ≤ n`) of length `≤ L`,
a permutation moving exactly the points of `M ⊆ {pt lo, …, pt n}` is a word of length
`≤ (|M| - 1) L`. -/
theorem perm_word_gen (L : ℕ)
    (htw : ∀ u v, lo ≤ u → u < v → v ≤ n → E (tw u v) = Equiv.swap (pt u) (pt v) ∧
      FreeGroup.norm (tw u v) ≤ L) :
    ∀ (c : ℕ) (M : Finset Y) (g : Equiv.Perm Y), M.card ≤ c → (∀ y, g y ≠ y ↔ y ∈ M) →
      (∀ y ∈ M, ∃ u, lo ≤ u ∧ u ≤ n ∧ y = pt u) →
      ∃ W, E W = g ∧ FreeGroup.norm W ≤ (M.card - 1) * L := by
  intro c
  induction c with
  | zero =>
    intro M g hc hM _
    have hM0 : M = ∅ := Finset.card_eq_zero.mp (by omega)
    refine ⟨1, ?_, by simp⟩
    refine Equiv.ext fun y => ?_
    rw [map_one, Equiv.Perm.coe_one, id]
    by_contra h; exact absurd ((hM y).mp (Ne.symm h)) (by simp [hM0])
  | succ c ih =>
    intro M g hc hM hpts
    by_cases hM0 : M = ∅
    · refine ⟨1, ?_, by simp⟩
      refine Equiv.ext fun y => ?_
      rw [map_one, Equiv.Perm.coe_one, id]
      by_contra h; exact absurd ((hM y).mp (Ne.symm h)) (by simp [hM0])
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hM0
    have hgx : g x ≠ x := (hM x).mpr hx
    have hgxM : g x ∈ M := (hM (g x)).mp (fun h => hgx (g.injective h))
    set g' := Equiv.swap x (g x) * g with hg'
    set M' := (M.erase x).filter (fun y => g' y ≠ y) with hM'
    have hM'iff : ∀ y, g' y ≠ y ↔ y ∈ M' := by
      intro y
      simp only [hM', Finset.mem_filter, Finset.mem_erase]
      constructor
      · intro h
        refine ⟨⟨?_, ?_⟩, h⟩
        · rintro rfl; apply h; simp [hg']
        · by_contra hy
          have hgy : g y = y := by by_contra h'; exact hy ((hM y).mp h')
          apply h
          have hyx : y ≠ x := by rintro rfl; exact hgx hgy
          have hygx : y ≠ g x := by intro e; apply hyx; apply g.injective; rw [hgy, ← e]
          simp [hg', hgy, Equiv.swap_apply_of_ne_of_ne hyx hygx]
      · exact fun h => h.2
    have hsub : M' ⊆ M.erase x := Finset.filter_subset _ _
    have hcard : M'.card + 1 ≤ M.card := by
      have := Finset.card_le_card hsub; rw [Finset.card_erase_of_mem hx] at this
      have : 1 ≤ M.card := Finset.card_pos.mpr ⟨x, hx⟩; omega
    have hcard2 : 2 ≤ M.card := by
      have : ({x, g x} : Finset Y) ⊆ M := by
        intro y hy; simp at hy; rcases hy with rfl | rfl <;> assumption
      have h2 := Finset.card_le_card this
      rw [Finset.card_pair (Ne.symm hgx)] at h2; exact h2
    obtain ⟨W', hW'1, hW'2⟩ := ih M' g' (by omega) hM'iff
      (fun y hy => hpts y (Finset.mem_of_mem_erase (hsub hy)))
    obtain ⟨u, hu1, hu2, rfl⟩ := hpts x hx
    obtain ⟨v, hv1, hv2, hv⟩ := hpts (g (pt u)) hgxM
    have huv : u ≠ v := by rintro rfl; exact hgx hv
    have hT : E (twS tw u v) = Equiv.swap (pt u) (g (pt u)) ∧ FreeGroup.norm (twS tw u v) ≤ L := by
      unfold twS
      split_ifs with h
      · rw [hv]; exact htw u v hu1 h hv2
      · rw [hv, Equiv.swap_comm]; exact htw v u hv1 (by omega) hu2
    refine ⟨twS tw u v * W', ?_, ?_⟩
    · rw [map_mul, hT.1, hW'1, hg', ← mul_assoc, Equiv.swap_mul_self, one_mul]
    · refine (FreeGroup.norm_mul_le _ _).trans ?_
      have h1 : (M'.card - 1) * L ≤ (M.card - 2) * L := Nat.mul_le_mul_right _ (by omega)
      have h2 : (M.card - 1) * L = (M.card - 2) * L + L := by
        rw [show M.card - 1 = (M.card - 2) + 1 by omega, Nat.succ_mul]
      omega

end PermWord

/-- **Lemma `lem:transpositions` (b)**: a permutation `g` of `Y` moving exactly the `m ≥ 2` points
of `M ⊆ {pt 1, …, pt n}` is represented by a word in `p, q` of length `< 10 (m - 1) n`. -/
theorem perm_word (n : ℕ) (M : Finset Y) (g : Equiv.Perm Y) (hM : ∀ y, g y ≠ y ↔ y ∈ M)
    (hpts : ∀ y ∈ M, ∃ u, 1 ≤ u ∧ u ≤ n ∧ y = pt u) (hm : 2 ≤ M.card) :
    ∃ W : FreeGroup (Fin 2), ev2 W = g ∧ FreeGroup.norm W < 10 * (M.card - 1) * n := by
  obtain ⟨y, hy⟩ := Finset.card_pos.mp (by omega : 0 < M.card)
  obtain ⟨u, hu1, hun, -⟩ := hpts y hy
  obtain ⟨W, h1, h2⟩ := perm_word_gen ev2 ω 1 n (10 * n - 1)
    (fun u v hu huv hvn => ⟨(transposition_word u v hu huv).1,
      by have := (transposition_word u v hu huv).2.2; omega⟩) M.card M g le_rfl hM hpts
  refine ⟨W, h1, lt_of_le_of_lt h2 ?_⟩
  have : (M.card - 1) * (10 * n - 1) < (M.card - 1) * (10 * n) :=
    Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
  calc (M.card - 1) * (10 * n - 1) < (M.card - 1) * (10 * n) := this
    _ = 10 * (M.card - 1) * n := by ring

/-! ### Lemma `lem:stabilizers`: the shift `g ↦ g^{[k]}` -/

/-- `θ_k`: `(1, j) ↦ (1, j + k)`, rays 2 and 3 fixed. -/
def sh (k : ℕ) (y : Y) : Y := if y.1 = 0 then ((0 : Fin 3), y.2 + k) else y
def unsh (k : ℕ) (y : Y) : Y := if y.1 = 0 then ((0 : Fin 3), y.2 - k) else y
/-- `g^{[k]}`: `θ_k g θ_k⁻¹` on the image of `θ_k`, the identity on `(1,1), …, (1,k)`. -/
def liftF (k : ℕ) (g : Y → Y) (y : Y) : Y := if y.1 = 0 ∧ y.2 < k then y else sh k (g (unsh k y))

lemma unsh_sh (k : ℕ) (z : Y) : unsh k (sh k z) = z := by
  obtain ⟨i, j⟩ := z
  by_cases h : i = 0
  · subst h; simp [sh, unsh]
  · simp [sh, unsh, h]

lemma sh_unsh (k : ℕ) (y : Y) (hy : ¬(y.1 = 0 ∧ y.2 < k)) : sh k (unsh k y) = y := by
  obtain ⟨i, j⟩ := y
  by_cases h : i = 0
  · subst h; simp only [true_and, not_lt] at hy; simp [sh, unsh]; omega
  · simp [sh, unsh, h]

lemma sh_not_first (k : ℕ) (z : Y) : ¬((sh k z).1 = 0 ∧ (sh k z).2 < k) := by
  unfold sh; split_ifs with h <;> simp_all

lemma liftF_sh (k : ℕ) (g : Y → Y) (z : Y) : liftF k g (sh k z) = sh k (g z) := by
  rw [liftF, if_neg (sh_not_first k z), unsh_sh]

lemma liftF_comp (k : ℕ) (g h : Y → Y) (y : Y) : liftF k g (liftF k h y) = liftF k (g ∘ h) y := by
  unfold liftF
  by_cases hy : y.1 = 0 ∧ y.2 < k
  · simp [hy]
  · rw [if_neg hy, if_neg hy, if_neg (sh_not_first k _), unsh_sh]; rfl

lemma sh_injective (k : ℕ) : Function.Injective (sh k) := fun a b h => by
  rw [← unsh_sh k a, h, unsh_sh]

/-- The isomorphism `H → H^{(k)}`, `g ↦ g^{[k]}` (on all permutations of `Y`). -/
def shiftHom (k : ℕ) : Equiv.Perm Y →* Equiv.Perm Y where
  toFun g := ⟨liftF k g, liftF k ⇑(g⁻¹), fun y => by
      rw [liftF_comp]; unfold liftF; split_ifs with h
      · rfl
      · simpa using sh_unsh k y h,
    fun y => by
      rw [liftF_comp]; unfold liftF; split_ifs with h
      · rfl
      · simpa using sh_unsh k y h⟩
  map_one' := by
    ext y : 1; show liftF k id y = y; unfold liftF; split_ifs with h
    · rfl
    · exact sh_unsh k y h
  map_mul' g h := by ext y : 1; show liftF k (g ∘ h) y = liftF k g (liftF k h y); rw [liftF_comp]

lemma shiftHom_apply (k : ℕ) (g : Equiv.Perm Y) (y : Y) : shiftHom k g y = liftF k g y := rfl

lemma shiftHom_swap (k : ℕ) (a b : Y) :
    shiftHom k (Equiv.swap a b) = Equiv.swap (sh k a) (sh k b) := by
  ext y : 1
  rw [shiftHom_apply]
  by_cases hy : y.1 = 0 ∧ y.2 < k
  · rw [liftF, if_pos hy, Equiv.swap_apply_of_ne_of_ne]
    · rintro rfl; exact sh_not_first k a hy
    · rintro rfl; exact sh_not_first k b hy
  · rw [← sh_unsh k y hy, liftF_sh, (sh_injective k).swap_apply]

lemma sh_pt (k x : ℕ) (hx : 1 ≤ x) : sh k (pt x) = pt (x + k) := by
  simp [sh, pt]; omega

/-- `ζ_k = σ_{k-1} ⋯ σ_1 σ_0`. -/
def ζ : ℕ → FreeGroup (Fin 2)
  | 0 => 1
  | k + 1 => σk k * ζ k

/-- The pointwise action of `ζ_k`: the cycle `(1,1) ↦ (1,k+1) ↦ (1,k) ↦ ⋯ ↦ (1,2) ↦ (1,1)`. -/
def zetaF (k : ℕ) (y : Y) : Y :=
  if y.1 = 0 ∧ y.2 = 0 then ((0 : Fin 3), k)
  else if y.1 = 0 ∧ y.2 ≤ k then ((0 : Fin 3), y.2 - 1) else y

lemma ev2_ζ_apply : ∀ (k : ℕ) (y : Y), ev2 (ζ k) y = zetaF k y
  | 0, ⟨i, j⟩ => by
    simp only [ζ, map_one, Equiv.Perm.coe_one, id, zetaF]
    split_ifs with h1 h2 <;> simp_all
  | k + 1, ⟨i, j⟩ => by
    rw [ζ, map_mul, Equiv.Perm.mul_apply, ev2_ζ_apply k, ev2_σk]
    simp only [pt, zetaF, Equiv.swap_apply_def]
    split_ifs <;> simp_all <;> omega

lemma pY_0 (j : ℕ) : pY ((0 : Fin 3), j) = ((0 : Fin 3), j + 1) := rfl
lemma pY_10 : pY ((1 : Fin 3), 0) = ((0 : Fin 3), 0) := rfl
lemma pY_1s (j : ℕ) : pY ((1 : Fin 3), j + 1) = ((1 : Fin 3), j) := rfl
lemma pY_2 (j : ℕ) : pY ((2 : Fin 3), j) = ((2 : Fin 3), j) := rfl
lemma qY_0 (j : ℕ) : qY ((0 : Fin 3), j) = ((0 : Fin 3), j + 1) := rfl
lemma qY_20 : qY ((2 : Fin 3), 0) = ((0 : Fin 3), 0) := rfl
lemma qY_2s (j : ℕ) : qY ((2 : Fin 3), j + 1) = ((2 : Fin 3), j) := rfl
lemma qY_1 (j : ℕ) : qY ((1 : Fin 3), j) = ((1 : Fin 3), j) := rfl

/-- **Lemma `lem:stabilizers` (a)**: `ζ_k p = p^{[k]}`. -/
theorem ev2_ζP (k : ℕ) : ev2 (ζ k * P) = shiftHom k pY := by
  ext y : 1
  rw [map_mul, Equiv.Perm.mul_apply, ev2_P, ev2_ζ_apply, shiftHom_apply]
  obtain ⟨⟨_ | _ | _ | i, hi⟩, j⟩ := y
  · rw [show ((⟨0, hi⟩ : Fin 3), j) = ((0 : Fin 3), j) from rfl, pY_0]
    simp only [zetaF, liftF, sh, unsh, pY_0, qY_0]
    split_ifs <;> simp_all [pY_0, qY_0] <;> omega
  · rcases j with _ | j
    · rw [show ((⟨1, hi⟩ : Fin 3), 0) = ((1 : Fin 3), 0) from rfl, pY_10]
      simp [zetaF, liftF, sh, unsh, pY_10]
    · rw [show ((⟨1, hi⟩ : Fin 3), j + 1) = ((1 : Fin 3), j + 1) from rfl, pY_1s]
      simp [zetaF, liftF, sh, unsh, pY_1s]
  · rw [show ((⟨2, hi⟩ : Fin 3), j) = ((2 : Fin 3), j) from rfl, pY_2]
    simp [zetaF, liftF, sh, unsh, pY_2]
  · omega

/-- **Lemma `lem:stabilizers` (a)**: `ζ_k q = q^{[k]}`. -/
theorem ev2_ζQ (k : ℕ) : ev2 (ζ k * Q) = shiftHom k qY := by
  ext y : 1
  rw [map_mul, Equiv.Perm.mul_apply, ev2_Q, ev2_ζ_apply, shiftHom_apply]
  obtain ⟨⟨_ | _ | _ | i, hi⟩, j⟩ := y
  · rw [show ((⟨0, hi⟩ : Fin 3), j) = ((0 : Fin 3), j) from rfl, qY_0]
    simp only [zetaF, liftF, sh, unsh, pY_0, qY_0]
    split_ifs <;> simp_all [pY_0, qY_0] <;> omega
  · rw [show ((⟨1, hi⟩ : Fin 3), j) = ((1 : Fin 3), j) from rfl, qY_1]
    simp [zetaF, liftF, sh, unsh, qY_1]
  · rcases j with _ | j
    · rw [show ((⟨2, hi⟩ : Fin 3), 0) = ((2 : Fin 3), 0) from rfl, qY_20]
      simp [zetaF, liftF, sh, unsh, qY_20]
    · rw [show ((⟨2, hi⟩ : Fin 3), j + 1) = ((2 : Fin 3), j + 1) from rfl, qY_2s]
      simp [zetaF, liftF, sh, unsh, qY_2s]
  · omega

/-- The substitution `p ↦ ζ_k p`, `q ↦ ζ_k q`: a word in the two letters of `K_k`. -/
def fK (k : ℕ) : FreeGroup (Fin 2) →* FreeGroup (Fin 2) := FreeGroup.lift ![ζ k * P, ζ k * Q]

/-- **Lemma `lem:stabilizers` (a)**: substituting `K_k` realises the isomorphism `g ↦ g^{[k]}`. -/
theorem ev2_fK (k : ℕ) (w : FreeGroup (Fin 2)) : ev2 (fK k w) = shiftHom k (ev2 w) := by
  have : ev2.comp (fK k) = (shiftHom k).comp ev2 := by
    apply FreeGroup.ext_hom; intro i; fin_cases i
    · show ev2 (fK k (FreeGroup.of 0)) = shiftHom k (ev2 P)
      simp only [fK, FreeGroup.lift_apply_of]; simpa [ev2_P] using ev2_ζP k
    · show ev2 (fK k (FreeGroup.of 1)) = shiftHom k (ev2 Q)
      simp only [fK, FreeGroup.lift_apply_of]; simpa [ev2_Q] using ev2_ζQ k
  exact DFunLike.congr_fun this w

/-- **Lemma `lem:stabilizers` (b)**: an element of `Σ_n ∩ H^{(k)}` moving exactly the `m ≥ 2`
points of `M ⊆ {pt (k+1), …, pt n}` is `W(ζ_k p, ζ_k q)` for a word `W` of length `< 10 (m-1) n`. -/
theorem stabilizer_word (k n : ℕ) (M : Finset Y) (g : Equiv.Perm Y) (hM : ∀ y, g y ≠ y ↔ y ∈ M)
    (hpts : ∀ y ∈ M, ∃ u, k < u ∧ u ≤ n ∧ y = pt u) (hm : 2 ≤ M.card) :
    ∃ W : FreeGroup (Fin 2), ev2 (fK k W) = g ∧ FreeGroup.norm W < 10 * (M.card - 1) * n := by
  obtain ⟨y, hy⟩ := Finset.card_pos.mp (by omega : 0 < M.card)
  obtain ⟨u, hu1, hun, -⟩ := hpts y hy
  obtain ⟨W, h1, h2⟩ := perm_word_gen (ev2.comp (fK k)) (fun u v => ω (u - k) (v - k)) (k + 1) n
    (10 * n - 1) (fun u v hu huv hvn => by
      obtain ⟨e1, -, e3⟩ := transposition_word (u - k) (v - k) (by omega) (by omega)
      refine ⟨?_, by omega⟩
      rw [MonoidHom.comp_apply, ev2_fK, e1, shiftHom_swap, sh_pt k _ (by omega),
        sh_pt k _ (by omega), Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega)])
    M.card M g le_rfl hM (fun y hy => by
      obtain ⟨u, h1, h2, h3⟩ := hpts y hy; exact ⟨u, h1, h2, h3⟩)
  refine ⟨W, h1, lt_of_le_of_lt h2 ?_⟩
  calc (M.card - 1) * (10 * n - 1) < (M.card - 1) * (10 * n) :=
        Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
    _ = 10 * (M.card - 1) * n := by ring

/-- For `k = 1, 2` the pairs `(ζ_k p, ζ_k q)` are `Lamps.K1`, `Lamps.K2`. -/
theorem fK_one (w : FreeGroup (Fin 2)) : ιpq (fK 1 w) = FreeGroup.lift K1 w := by
  have : ιpq.comp (fK 1) = FreeGroup.lift K1 := by
    apply FreeGroup.ext_hom; intro i; fin_cases i <;>
      simp [fK, ζ, σk, S, P, Q, ιpq, FreeGroup.lift_apply_of, K1, s, comm]
  exact DFunLike.congr_fun this w

theorem fK_two (w : FreeGroup (Fin 2)) : ιpq (fK 2 w) = FreeGroup.lift K2 w := by
  have : ιpq.comp (fK 2) = FreeGroup.lift K2 := by
    apply FreeGroup.ext_hom; intro i; fin_cases i <;>
      simp [fK, ζ, σk, S, P, Q, ιpq, FreeGroup.lift_apply_of, K2, B, s, comm, mul_assoc]
  exact DFunLike.congr_fun this w

/-! ### (c) Arrangement words `π[x₁, …, x_l]` -/

/-- The permutation of a list of transpositions `(u, v)` of points of ray 1. -/
def tprod (ts : List (ℕ × ℕ)) : Equiv.Perm Y := (ts.map fun t => Equiv.swap (pt t.1) (pt t.2)).prod

/-- The corresponding word `∏ ω_{u,v}`. -/
def twprod (ts : List (ℕ × ℕ)) : FreeGroup (Fin 2) := (ts.map fun t => ω t.1 t.2).prod

lemma tprod_fix (lo : ℕ) (hlo : 1 ≤ lo) : ∀ ts : List (ℕ × ℕ), (∀ t ∈ ts, lo + 1 ≤ t.1 ∧ t.1 < t.2) →
    tprod ts (pt lo) = pt lo
  | [], _ => rfl
  | t :: ts, h => by
    have ht := h t (by simp)
    have ih := tprod_fix lo hlo ts (fun t' ht' => h t' (by simp [ht']))
    show Equiv.swap (pt t.1) (pt t.2) (tprod ts (pt lo)) = pt lo
    rw [ih, Equiv.swap_apply_of_ne_of_ne]
    · intro e; have := pt_inj hlo (by omega) e; omega
    · intro e; have := pt_inj hlo (by omega) e; omega

lemma swap_pt_swap {lo x y : ℕ} (hlo : 1 ≤ lo) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    Equiv.swap (pt lo) (pt x) (pt (Equiv.swap lo x y)) = pt y := by
  rw [Equiv.swap_apply_def lo x y]
  split_ifs with h1 h2
  · rw [h1, Equiv.swap_apply_right]
  · rw [h2, Equiv.swap_apply_left]
  · rw [Equiv.swap_apply_of_ne_of_ne]
    · intro e; exact h1 (pt_inj hy hlo e)
    · intro e; exact h2 (pt_inj hy hx e)

theorem arrangement_gen (n : ℕ) : ∀ (xs : List ℕ) (lo : ℕ), 1 ≤ lo → xs.Nodup →
    (∀ x ∈ xs, lo ≤ x ∧ x ≤ n) →
    ∃ ts : List (ℕ × ℕ), ts.length ≤ xs.length ∧ (∀ t ∈ ts, lo ≤ t.1 ∧ t.1 < t.2 ∧ t.2 ≤ n) ∧
      ∀ m (hm : m < xs.length), tprod ts (pt (lo + m)) = pt xs[m]
  | [], lo, _, _, _ => ⟨[], le_rfl, by simp, fun m hm => by simp at hm⟩
  | x :: rest, lo, hlo, hnd, hxs => by
    have hx := hxs x (by simp)
    have hnd' := List.nodup_cons.mp hnd
    set r : Equiv.Perm ℕ := Equiv.swap lo x with hr
    have hrest : ∀ y ∈ rest.map r, lo + 1 ≤ y ∧ y ≤ n := by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
      have hzx : z ≠ x := fun e => hnd'.1 (e ▸ hz)
      have hz' := hxs z (by simp [hz])
      rw [hr, Equiv.swap_apply_def lo x z]
      by_cases h1 : z = lo
      · rw [if_pos h1]; subst h1; exact ⟨by omega, hx.2⟩
      · rw [if_neg h1, if_neg hzx]; exact ⟨by omega, hz'.2⟩
    obtain ⟨ts', hl', hts', hev'⟩ := arrangement_gen n (rest.map r) (lo + 1) (by omega)
      (hnd'.2.map r.injective) hrest
    have hprod : tprod ((if x = lo then [] else [(lo, x)]) ++ ts') =
        Equiv.swap (pt lo) (pt x) * tprod ts' := by
      split_ifs with h
      · subst h; simp [tprod, Equiv.swap_self]; rfl
      · simp [tprod]
    refine ⟨(if x = lo then [] else [(lo, x)]) ++ ts', ?_, ?_, ?_⟩
    · split_ifs <;>
        simp only [List.length_append, List.length_nil, List.length_cons, List.length_map,
          List.length_singleton] at hl' ⊢ <;> omega
    · intro t ht
      simp only [List.mem_append] at ht
      rcases ht with ht | ht
      · split_ifs at ht with h
        · simp at ht
        · simp at ht; subst ht; exact ⟨le_rfl, by omega, hx.2⟩
      · have := hts' t ht; exact ⟨by omega, this.2⟩
    · intro m hm
      rw [hprod, Equiv.Perm.mul_apply]
      rcases m with _ | m
      · rw [Nat.add_zero, tprod_fix lo hlo ts' (fun t ht => ⟨(hts' t ht).1, (hts' t ht).2.1⟩),
          Equiv.swap_apply_left]; rfl
      · simp only [List.length_cons] at hm
        have h1 := hev' m (by simp; omega)
        rw [show lo + (m + 1) = lo + 1 + m by omega, h1, List.getElem_map, List.getElem_cons_succ]
        have hy := hxs rest[m] (by simp)
        exact swap_pt_swap hlo (by omega) (by omega)
termination_by xs => xs.length
decreasing_by simp

lemma ev2_twprod : ∀ ts : List (ℕ × ℕ), (∀ t ∈ ts, 1 ≤ t.1 ∧ t.1 < t.2) →
    ev2 (twprod ts) = tprod ts
  | [], _ => by simp [twprod, tprod]
  | t :: ts, h => by
    have ht := h t (by simp)
    have ih := ev2_twprod ts (fun t' h' => h t' (by simp [h']))
    show ev2 (ω t.1 t.2 * twprod ts) = Equiv.swap (pt t.1) (pt t.2) * tprod ts
    rw [map_mul, (transposition_word t.1 t.2 ht.1 ht.2).1, ih]

lemma norm_twprod (n : ℕ) : ∀ ts : List (ℕ × ℕ), (∀ t ∈ ts, 1 ≤ t.1 ∧ t.1 < t.2 ∧ t.2 ≤ n) →
    FreeGroup.norm (twprod ts) + ts.length ≤ 10 * ts.length * n
  | [], _ => by simp [twprod]
  | t :: ts, h => by
    have ht := h t (by simp)
    have ih := norm_twprod n ts (fun t' h' => h t' (by simp [h']))
    have hw := (transposition_word t.1 t.2 ht.1 ht.2.1).2.2
    have hm := FreeGroup.norm_mul_le (ω t.1 t.2) (twprod ts)
    simp only [twprod, List.map_cons, List.prod_cons, List.length_cons] at *
    have : 10 * (ts.length + 1) * n = 10 * ts.length * n + 10 * n := by ring
    omega

/-- **Lemma `lem:transpositions` (c)**: for distinct `x₁, …, x_l ∈ {1, …, n}` there are at most
`l` transpositions `(u v)`, `1 ≤ u < v ≤ n`, whose product `π[x₁, …, x_l]` sends `m` to `x_m`
(`m ≤ l`); the product `W` of the words `ω_{u,v}` represents it with length `+ l ≤ 10 l n`
(so `< 10 l n` for `l ≥ 1`). -/
theorem arrangement_word (n : ℕ) (xs : List ℕ) (hnd : xs.Nodup) (hxs : ∀ x ∈ xs, 1 ≤ x ∧ x ≤ n) :
    ∃ ts : List (ℕ × ℕ), ts.length ≤ xs.length ∧ (∀ t ∈ ts, 1 ≤ t.1 ∧ t.1 < t.2 ∧ t.2 ≤ n) ∧
      (∀ m (hm : m < xs.length), tprod ts (pt (m + 1)) = pt xs[m]) ∧
      ev2 (twprod ts) = tprod ts ∧ FreeGroup.norm (twprod ts) + xs.length ≤ 10 * xs.length * n := by
  obtain ⟨ts, hl, hts, hev⟩ := arrangement_gen n xs 1 le_rfl hnd hxs
  refine ⟨ts, hl, hts, fun m hm => by rw [Nat.add_comm]; exact hev m hm,
    ev2_twprod ts (fun t ht => ⟨(hts t ht).1, (hts t ht).2.1⟩), ?_⟩
  have h := norm_twprod n ts hts
  have hn : xs.length = 0 ∨ 1 ≤ n := by
    rcases xs with _ | ⟨x, _⟩
    · left; rfl
    · right; have := hxs x (by simp); omega
  have h2 : 10 * ts.length * n + (xs.length - ts.length) ≤ 10 * xs.length * n := by
    rcases hn with hn | hn
    · have h0 : ts.length = 0 := by omega
      rw [h0, hn]; simp
    · have : 10 * xs.length * n = 10 * ts.length * n + 10 * (xs.length - ts.length) * n := by
        rw [← Nat.add_mul, ← Nat.mul_add, Nat.add_sub_cancel' hl]
      have : xs.length - ts.length ≤ 10 * (xs.length - ts.length) * n :=
        Nat.le_mul_of_pos_right _ hn |>.trans' (by omega)
      omega
  omega

/-- `lem:stabilizers` (b) for `k = 1` in `Γ`: `hV g = ρΓ (W(K₁))`. -/
theorem stabilizer_word_K1 (n : ℕ) (M : Finset Y) (g : Equiv.Perm Y) (hM : ∀ y, g y ≠ y ↔ y ∈ M)
    (hpts : ∀ y ∈ M, ∃ u, 1 < u ∧ u ≤ n ∧ y = pt u) (hm : 2 ≤ M.card) :
    ∃ W : FreeGroup (Fin 2), ρΓ (FreeGroup.lift K1 W) = hV g ∧
      FreeGroup.norm W < 10 * (M.card - 1) * n := by
  obtain ⟨W, h1, h2⟩ := stabilizer_word 1 n M g hM hpts hm
  exact ⟨W, by rw [← fK_one, rhoΓ_ιpq, h1], h2⟩

/-- `lem:stabilizers` (b) for `k = 2` in `Γ`: `hV g = ρΓ (W(K₂))`. -/
theorem stabilizer_word_K2 (n : ℕ) (M : Finset Y) (g : Equiv.Perm Y) (hM : ∀ y, g y ≠ y ↔ y ∈ M)
    (hpts : ∀ y ∈ M, ∃ u, 2 < u ∧ u ≤ n ∧ y = pt u) (hm : 2 ≤ M.card) :
    ∃ W : FreeGroup (Fin 2), ρΓ (FreeGroup.lift K2 W) = hV g ∧
      FreeGroup.norm W < 10 * (M.card - 1) * n := by
  obtain ⟨W, h1, h2⟩ := stabilizer_word 2 n M g hM hpts hm
  exact ⟨W, by rw [← fK_two, rhoΓ_ιpq, h1], h2⟩

end Lamps
