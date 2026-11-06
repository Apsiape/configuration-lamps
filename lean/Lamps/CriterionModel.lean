import FiniteLean.GroupTheory.Area.Transport
import FiniteLean.GroupTheory.Commutator
import Lamps.Basic
import Houghton.Analysis.DimensionPerm

/-!
# Theorem `thm:criterion` (Counting criterion), permutation form: the model form

Generalization of Proposition `prop:dimension-perm` of the Houghton paper (`Houghton.Analysis`) from
the transported pairs `σ_{3i}, σ_{3i+1}` of `H₃` to an arbitrary letter type `S`, an arbitrary family
of relators `R : ι → FreeGroup S` containing `a², b², (ab)³`, and arbitrary transport words
`w₁, …, w_N` whose pairwise commutators `[w_i x w_i⁻¹, w_j y w_j⁻¹]` (`x, y ∈ {a, b}`) have area
`≤ Λ` (Appendix `app:imported`, steps 1–3: transported copies, rounding, transport in measure).
The final (entropy) step is the sector bound `Houghton.PermSectorBound`, proved from strong
subadditivity in `Lamps/CriterionSSA.lean`.

All Hamming-distance tools and the rounding maps `roundInv`, `round3` are imported from
`Houghton.Analysis.Hamming`.
-/

namespace Lamps

open Finset Equiv
open Houghton (dH)

universe u

theorem comm_eq_commG (x y : F) : comm x y = commG x y := rfl

/-! ### Transport in measure for an arbitrary family of relators -/

/-! ### Rounding transported pairs to exact local `S₃`-actions (permutation form) -/

section Pairs

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {N : ℕ} (A B : Fin N → Perm Ω)

/-- The rounded involution near `A i` (`x_i = u_i(a)`). -/
def rx (i : Fin N) : Perm Ω := Houghton.roundInv (A i)

/-- The rounded involution near `B i`. -/
def rT (i : Fin N) : Perm Ω := Houghton.roundInv (B i)

/-- The rounded three-cycle (`c_i = u_i(ab)`). -/
def rc (i : Fin N) : Perm Ω := Houghton.round3 (rx A i * rT B i)

variable (δ : ℝ) (hA2 : ∀ i, dH (A i * A i) 1 ≤ δ) (hB2 : ∀ i, dH (B i * B i) 1 ≤ δ)
  (h3 : ∀ i, dH ((A i * B i) ^ 3) 1 ≤ δ)
include hA2 hB2 h3

theorem dH_rc (i : Fin N) : dH (rc A B i) (A i * B i) ≤ 9 * δ := by
  have h1 : dH (rx A i) (A i) ≤ δ := (Houghton.dH_roundInv _).trans (hA2 i)
  have h2 : dH (rT B i) (B i) ≤ δ := (Houghton.dH_roundInv _).trans (hB2 i)
  have hST : dH (rx A i * rT B i) (A i * B i) ≤ 2 * δ := by
    have := Houghton.dH_mul_le (rx A i) (rT B i) (A i) (B i); linarith
  have hcube : dH ((rx A i * rT B i) ^ 3) ((A i * B i) ^ 3) ≤ 3 * (2 * δ) := by
    have := Houghton.dH_pow_le (rx A i * rT B i) (A i * B i) 3
    push_cast at this; linarith
  have hr : dH (rc A B i) (rx A i * rT B i) ≤ dH ((rx A i * rT B i) ^ 3) 1 :=
    Houghton.dH_round3 _
  have t1 := Houghton.dH_triangle ((rx A i * rT B i) ^ 3) ((A i * B i) ^ 3) 1
  have t2 := Houghton.dH_triangle (rc A B i) (rx A i * rT B i) (A i * B i)
  linarith [h3 i]

variable (L : ℝ) (hfar : ∀ i j, i ≠ j → ∀ X Y : Perm Ω, (X = A i ∨ X = B i) →
    (Y = A j ∨ Y = B j) → dH (X * Y) (Y * X) ≤ L)
include hfar

theorem dH_rc_comm (i j : Fin N) (hij : i ≠ j) :
    dH (rc A B i * rc A B j) (rc A B j * rc A B i) ≤ 4 * L + 18 * δ + 18 * δ := by
  have fAA := hfar i j hij _ _ (Or.inl rfl) (Or.inl rfl)
  have fAB := hfar i j hij _ _ (Or.inl rfl) (Or.inr rfl)
  have fBA := hfar i j hij _ _ (Or.inr rfl) (Or.inl rfl)
  have fBB := hfar i j hij _ _ (Or.inr rfl) (Or.inr rfl)
  have m1 := Houghton.dH_mul_commutes (A i) (B i) (A j)
  have m2 := Houghton.dH_mul_commutes (A i) (B i) (B j)
  have mid := Houghton.dH_commutes_mul (A i * B i) (A j) (B j)
  have ci := dH_rc A B δ hA2 hB2 h3 i
  have cj := dH_rc A B δ hA2 hB2 h3 j
  have e1 := Houghton.dH_mul_le (rc A B i) (rc A B j) (A i * B i) (A j * B j)
  have e2 := Houghton.dH_mul_le (rc A B j) (rc A B i) (A j * B j) (A i * B i)
  rw [Houghton.dH_comm] at e2
  have t1 := Houghton.dH_triangle (rc A B i * rc A B j) (A i * B i * (A j * B j))
    (rc A B j * rc A B i)
  have t2 := Houghton.dH_triangle (A i * B i * (A j * B j)) (A j * B j * (A i * B i))
    (rc A B j * rc A B i)
  linarith

theorem dH_rx_comm (i j : Fin N) (hij : i ≠ j) :
    dH (rx A i * rc A B j) (rc A B j * rx A i) ≤ 2 * L + 20 * δ := by
  have fAA := hfar i j hij _ _ (Or.inl rfl) (Or.inl rfl)
  have fAB := hfar i j hij _ _ (Or.inl rfl) (Or.inr rfl)
  have mid := Houghton.dH_commutes_mul (A i) (A j) (B j)
  have xi : dH (rx A i) (A i) ≤ δ := (Houghton.dH_roundInv _).trans (hA2 i)
  have cj := dH_rc A B δ hA2 hB2 h3 j
  have e1 := Houghton.dH_mul_le (rx A i) (rc A B j) (A i) (A j * B j)
  have e2 := Houghton.dH_mul_le (rc A B j) (rx A i) (A j * B j) (A i)
  rw [Houghton.dH_comm] at e2
  have t1 := Houghton.dH_triangle (rx A i * rc A B j) (A i * (A j * B j)) (rc A B j * rx A i)
  have t2 := Houghton.dH_triangle (A i * (A j * B j)) (A j * B j * A i) (rc A B j * rx A i)
  linarith

end Pairs

/-- **Rounding and counting** (steps 2–3 of the proof of Theorem `thm:criterion`, permutation form):
transported pairs `A_i, B_i` with square/braid defects `≤ δ`, displaced products `A_i B_i`, and
cross commutators `≤ Λ δ` round to exact local `S₃`-actions satisfying the hypotheses of
`Houghton.PermSectorBound`, provided `10⁸ N max(1,Λ) δ ≤ 1`. -/
theorem exists_local_S3_of_pairs {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {N : ℕ}
    (A B : Fin N → Perm Ω) (δ : ℝ) (hδ0 : 0 ≤ δ) (hA2 : ∀ i, dH (A i * A i) 1 ≤ δ)
    (hB2 : ∀ i, dH (B i * B i) 1 ≤ δ) (h3 : ∀ i, dH ((A i * B i) ^ 3) 1 ≤ δ)
    (hγ : ∀ i, 1 / 2 ≤ dH (A i * B i) 1) (Λ : ℝ)
    (hfar : ∀ i j, i ≠ j → ∀ X Y : Perm Ω, (X = A i ∨ X = B i) → (Y = A j ∨ Y = B j) →
      dH (X * Y) (Y * X) ≤ Λ * δ)
    (hN : 1 ≤ N) (hδ : (10 : ℝ) ^ 8 * N * max 1 Λ * δ ≤ 1) :
    ∃ c x : Fin N → Perm Ω,
      (∀ i, c i ^ 3 = 1) ∧ (∀ i, x i ^ 2 = 1) ∧ (∀ i, x i * c i * x i = (c i)⁻¹) ∧
      (∀ i, (1 : ℝ) / 8 ≤ dH (c i) 1) ∧
      (∀ i, ∑ j ∈ univ.filter (· ≠ i), dH (c i * c j) (c j * c i) ≤ 1 / 40000) ∧
      (∀ i, ∑ j ∈ univ.filter (· ≠ i), dH (x i * c j) (c j * x i) ≤ 1 / 40000) := by
  set M : ℝ := max 1 Λ with hMdef
  have hM1 : (1 : ℝ) ≤ M := le_max_left _ _
  have hMΛ : Λ ≤ M := le_max_right _ _
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNM : (1 : ℝ) ≤ N * M := by nlinarith
  have hNMδ : (N : ℝ) * M * δ ≤ 1 / 10 ^ 8 := by
    rw [le_div_iff₀ (by norm_num)]; linarith
  have hδsmall : δ ≤ 1 / 10 ^ 8 := by
    have : δ ≤ N * M * δ := by nlinarith
    linarith
  have hΛδ : Λ * δ ≤ M * δ := mul_le_mul_of_nonneg_right hMΛ hδ0
  have hδM : δ ≤ M * δ := by nlinarith
  have hcard : ∀ i : Fin N, ((univ.filter (· ≠ i)).card : ℝ) ≤ N := by
    intro i
    have : (univ.filter (· ≠ i)).card ≤ N := (card_filter_le _ _).trans (by simp)
    exact_mod_cast this
  refine ⟨rc A B, rx A, fun i => Houghton.round3_pow_three _, fun i => Houghton.roundInv_sq _,
    fun i => Houghton.round3_conj _ _ (Houghton.roundInv_mul_self _)
      (Houghton.roundInv_mul_self _), ?_, ?_, ?_⟩
  · intro i
    have h := dH_rc A B δ hA2 hB2 h3 i
    have t := Houghton.dH_triangle (A i * B i) (rc A B i) 1
    rw [Houghton.dH_comm (A i * B i) (rc A B i)] at t
    linarith [hγ i]
  · intro i
    have hb : ∀ j ∈ univ.filter (· ≠ i),
        dH (rc A B i * rc A B j) (rc A B j * rc A B i) ≤ 40 * (M * δ) := by
      intro j hj
      have hij : i ≠ j := fun h => (mem_filter.mp hj).2 h.symm
      have := dH_rc_comm A B δ hA2 hB2 h3 (Λ * δ) hfar i j hij
      linarith
    calc ∑ j ∈ univ.filter (· ≠ i), dH (rc A B i * rc A B j) (rc A B j * rc A B i)
        ≤ (univ.filter (· ≠ i)).card • (40 * (M * δ)) := sum_le_card_nsmul _ _ _ hb
      _ ≤ (N : ℝ) * (40 * (M * δ)) := by
          rw [nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (hcard i) (by nlinarith)
      _ ≤ 1 / 40000 := by nlinarith
  · intro i
    have hb : ∀ j ∈ univ.filter (· ≠ i),
        dH (rx A i * rc A B j) (rc A B j * rx A i) ≤ 40 * (M * δ) := by
      intro j hj
      have hij : i ≠ j := fun h => (mem_filter.mp hj).2 h.symm
      have := dH_rx_comm A B δ hA2 hB2 h3 (Λ * δ) hfar i j hij
      linarith
    calc ∑ j ∈ univ.filter (· ≠ i), dH (rx A i * rc A B j) (rc A B j * rx A i)
        ≤ (univ.filter (· ≠ i)).card • (40 * (M * δ)) := sum_le_card_nsmul _ _ _ hb
      _ ≤ (N : ℝ) * (40 * (M * δ)) := by
          rw [nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (hcard i) (by nlinarith)
      _ ≤ 1 / 40000 := by nlinarith

/-! ### The model form -/

section Model

variable {S ι : Type*} (R : ι → FreeGroup S) (a b : S) (ia ib iab : ι)
  (hRa : R ia = FreeGroup.of a ^ 2) (hRb : R ib = FreeGroup.of b ^ 2)
  (hRab : R iab = (FreeGroup.of a * FreeGroup.of b) ^ 3)

/-- The area hypothesis of Theorem `thm:criterion`: `Area_R([w_i x w_i⁻¹, w_j y w_j⁻¹]) ≤ Λ` for
`i ≠ j` and `x, y ∈ {a, b}`. -/
def TransportAreaLE {N : ℕ} (w : Fin N → FreeGroup S) (Λ : ℕ) : Prop :=
  ∀ i j, i ≠ j → ∀ x ∈ [FreeGroup.of a, FreeGroup.of b], ∀ y ∈ [FreeGroup.of a, FreeGroup.of b],
    AreaLEGen R (commG (w i * x * (w i)⁻¹) (w j * y * (w j)⁻¹)) Λ

include hRa hRb hRab

/-- **Theorem `thm:criterion`, model form** (permutation case), from the sector bound: if
`φ : FreeGroup S →* Sym(Ω)` has all relator defects `≤ δ`, displaces `ab` on at least half of the
points, and `10⁸ N max(1,Λ) δ ≤ 1`, then `N/16 ≤ log₂ |Ω|`. -/
theorem counting_criterion_model (hS : Houghton.PermSectorBound.{u}) {N : ℕ}
    (w : Fin N → FreeGroup S) (Λ : ℕ) (hw : TransportAreaLE R a b w Λ)
    {Ω : Type u} [Fintype Ω] [DecidableEq Ω] (φ : FreeGroup S →* Perm Ω) (δ : ℝ)
    (hrel : ∀ k, dH (φ (R k)) 1 ≤ δ)
    (hab : 1 / 2 ≤ dH (φ (FreeGroup.of a * FreeGroup.of b)) 1)
    (hδ : (10 : ℝ) ^ 8 * N * max 1 (Λ : ℝ) * δ ≤ 1) :
    (N : ℝ) / 16 ≤ Real.logb 2 (Fintype.card Ω) := by
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · subst hN0
    simp only [Nat.cast_zero, zero_div]
    rcases Nat.eq_zero_or_pos (Fintype.card Ω) with h0 | h0
    · simp [h0]
    · exact Real.logb_nonneg (by norm_num) (by exact_mod_cast h0)
  have hδ0 : 0 ≤ δ := (Houghton.dH_nonneg _ _).trans (hrel ia)
  set A : Fin N → Perm Ω := fun i => φ (w i * FreeGroup.of a * (w i)⁻¹) with hA
  set B : Fin N → Perm Ω := fun i => φ (w i * FreeGroup.of b * (w i)⁻¹) with hB
  have hA2 : ∀ i, dH (A i * A i) 1 ≤ δ := by
    intro i
    have : A i * A i = φ (w i) * φ (R ia) * (φ (w i))⁻¹ := by
      simp only [hA, hRa, map_mul, map_inv, pow_two]; group
    rw [this, Houghton.dH_conj]; exact hrel ia
  have hB2 : ∀ i, dH (B i * B i) 1 ≤ δ := by
    intro i
    have : B i * B i = φ (w i) * φ (R ib) * (φ (w i))⁻¹ := by
      simp only [hB, hRb, map_mul, map_inv, pow_two]; group
    rw [this, Houghton.dH_conj]; exact hrel ib
  have hAB : ∀ i, A i * B i =
      φ (w i) * φ (FreeGroup.of a * FreeGroup.of b) * (φ (w i))⁻¹ := by
    intro i; simp only [hA, hB, map_mul, map_inv]; group
  have h3 : ∀ i, dH ((A i * B i) ^ 3) 1 ≤ δ := by
    intro i
    rw [hAB, conj_pow, ← map_pow, ← hRab, Houghton.dH_conj]; exact hrel iab
  have hγ : ∀ i, 1 / 2 ≤ dH (A i * B i) 1 := by
    intro i; rw [hAB, Houghton.dH_conj]; exact hab
  have hfar : ∀ i j, i ≠ j → ∀ X Y : Perm Ω, (X = A i ∨ X = B i) → (Y = A j ∨ Y = B j) →
      dH (X * Y) (Y * X) ≤ (Λ : ℝ) * δ := by
    intro i j hij X Y hX hY
    obtain ⟨x, hx, rfl⟩ : ∃ x ∈ [FreeGroup.of a, FreeGroup.of b],
        X = φ (w i * x * (w i)⁻¹) := by
      rcases hX with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., rfl⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), rfl⟩
    obtain ⟨y, hy, rfl⟩ : ∃ y ∈ [FreeGroup.of a, FreeGroup.of b],
        Y = φ (w j * y * (w j)⁻¹) := by
      rcases hY with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., rfl⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), rfl⟩
    have h := dH_le_of_areaLEGen R φ δ hrel hδ0 (hw i j hij x hx y hy)
    rw [Houghton.dH_comm_eq]
    simpa [commG, map_mul, map_inv] using h
  obtain ⟨c, x, h1, h2, h3', h4, h5, h6⟩ :=
    exists_local_S3_of_pairs A B δ hδ0 hA2 hB2 h3 hγ (Λ : ℝ) hfar hN hδ
  exact hS Ω N c x h1 h2 h3' h4 h5 h6

end Model

end Lamps
