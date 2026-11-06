import Lamps.UnitaryBasic

/-!
# The unitary counting criterion (Theorem `thm:criterion`, "Moreover"): blueprint and assembly

Blueprint (paper: `sections/criterion.tex`, `sections/app-imported.tex`):
* `UnitaryS3Round` — Lemma `lem:imp-s3round` (exact `S₃` rounding of unitaries);
* `UnitaryPhaseRobust` — Theorem `thm:imp-phase` (phase-robust sector bound), in the form with
  `â_i² ≤ (4/3)∑_{j>i} κ(c_i,c_j)²` and `b̂_i² ≤ (4/3)∑_{j≠i} κ(x_i,c_j)²` already substituted;
* `UnitaryMargin` — the numerics of the proof of `thm:criterion` (with `K_Δ`);
* proved here: the local interchange estimates for unitaries (`ud_cc_comm`, `ud_xc_comm`), from
  bi-invariance of `‖·‖₂` and transport in norm (`Lamps.UnitaryBasic`).
-/

namespace Lamps

open Finset Matrix

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- `χ(x) = h₂(min{2x/3, 2/3}) + min{2x/3, 2/3}` (bits). -/
noncomputable def chi (x : ℝ) : ℝ := Houghton.h2 (min (2 / 3 * x) (2 / 3)) + min (2 / 3 * x) (2 / 3)

/-- `K_Δ = √(80000 (1 + log₂(1/Δ)))/Δ`. -/
noncomputable def Kd (Δ : ℝ) : ℝ := Real.sqrt (80000 * (1 + Real.logb 2 (1 / Δ))) / Δ

/-- **Lemma `lem:imp-s3round`** (exact `S₃` rounding), in the form used by the criterion. -/
def UnitaryS3Round : Prop :=
  ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω] (A B : Matrix Ω Ω ℂ) (e : ℝ), IsU A → IsU B →
    ud (A * A) 1 ≤ e → ud (B * B) 1 ≤ e → ud ((A * B) ^ 3) 1 ≤ e →
    ∃ x c : Matrix Ω Ω ℂ, IsU x ∧ IsU c ∧ x * x = 1 ∧ c ^ 3 = 1 ∧ x * c * x = cᴴ ∧
      ud x A ≤ e ∧ ud c (A * B) ≤ 9 * e

/-- **Theorem `thm:imp-phase`** (phase-robust sector bound), with the bounds on `â_i, b̂_i`
substituted (the bracket is antitone in `â_i², b̂_i²`). -/
def UnitaryPhaseRobust : Prop :=
  ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω] (N : ℕ) (c x : Fin N → Matrix Ω Ω ℂ),
    (∀ i, IsU (c i)) → (∀ i, IsU (x i)) → (∀ i, c i ^ 3 = 1) → (∀ i, x i * x i = 1) →
    (∀ i, x i * c i * x i = (c i)ᴴ) →
    ∑ i, (((ud (c i) 1) ^ 2 - 4 / 3 * ∑ j ∈ univ.filter (i < ·), ud (c i * c j) (c j * c i) ^ 2) / 3
      - (4 / 3 * ∑ j ∈ univ.filter (· ≠ i), ud (x i * c j) (c j * x i) ^ 2) / (2 * Real.log 2)
      - chi (4 / 3 * ∑ j ∈ univ.filter (i < ·), ud (c i * c j) (c j * c i) ^ 2))
      ≤ Real.logb 2 (Fintype.card Ω)

/-- The numerics of the proof of the "Moreover" clause of `thm:criterion`, including the averaging
over copies (concavity of `χ`): if `d_i ≥ (Δ - 9/K_Δ)²`, `0 ≤ a_i ≤ 1`, `∑ a_i ≤ N · 3200/(3K_Δ²)`
and `b_i ≤ 1936/(3K_Δ²)`, then `∑_i [(d_i - a_i)/3 - b_i/(2 ln 2) - χ(a_i)] ≥ N Δ²/12`. -/
def UnitaryMargin : Prop :=
  ∀ (N : ℕ) (Δ : ℝ) (d a b : Fin N → ℝ), 0 < Δ → Δ ≤ 1 →
    (∀ i, (Δ - 9 / Kd Δ) ^ 2 ≤ d i) → (∀ i, 0 ≤ a i) → (∀ i, a i ≤ 1) →
    ∑ i, a i ≤ N * (3200 / (3 * Kd Δ ^ 2)) → (∀ i, b i ≤ 1936 / (3 * Kd Δ ^ 2)) →
    N * Δ ^ 2 / 12 ≤ ∑ i, ((d i - a i) / 3 - b i / (2 * Real.log 2) - chi (a i))

/-! ### Local interchange estimates for unitaries -/

lemma ud_mul_commutes {x y z : Matrix Ω Ω ℂ} (hx : IsU x) (hy : IsU y) :
    ud (x * y * z) (z * (x * y)) ≤ ud (x * z) (z * x) + ud (y * z) (z * y) := by
  calc ud (x * y * z) (z * (x * y)) ≤ ud (x * y * z) (x * z * y) + ud (x * z * y) (z * (x * y)) :=
        ud_triangle _ _ _
    _ = ud (y * z) (z * y) + ud (x * z) (z * x) := by
        congr 1
        · rw [Matrix.mul_assoc, Matrix.mul_assoc, ud_mul_left hx]
        · rw [← Matrix.mul_assoc, ud_mul_right hy]
    _ = _ := add_comm _ _

lemma ud_commutes_mul {x y z : Matrix Ω Ω ℂ} (hx : IsU x) (hy : IsU y) :
    ud (z * (x * y)) (x * y * z) ≤ ud (z * x) (x * z) + ud (z * y) (y * z) := by
  rw [ud_comm, ud_comm (z * x), ud_comm (z * y)]
  exact ud_mul_commutes hx hy

section Pairs

variable {N : ℕ} (A B x c : Fin N → Matrix Ω Ω ℂ) (e L : ℝ)
  (hA : ∀ i, IsU (A i)) (hB : ∀ i, IsU (B i)) (hx : ∀ i, IsU (x i)) (hc : ∀ i, IsU (c i))
  (hxA : ∀ i, ud (x i) (A i) ≤ e) (hcAB : ∀ i, ud (c i) (A i * B i) ≤ 9 * e)
  (hfar : ∀ i j, i ≠ j → ∀ X Y : Matrix Ω Ω ℂ, (X = A i ∨ X = B i) → (Y = A j ∨ Y = B j) →
    ud (X * Y) (Y * X) ≤ L)
include hA hB hx hc hxA hcAB hfar

/-- `κ(c_i, c_j) ≤ 4L + 36e`. -/
theorem ud_cc_comm (i j : Fin N) (hij : i ≠ j) :
    ud (c i * c j) (c j * c i) ≤ 4 * L + 36 * e := by
  have fAA := hfar i j hij _ _ (Or.inl rfl) (Or.inl rfl)
  have fAB := hfar i j hij _ _ (Or.inl rfl) (Or.inr rfl)
  have fBA := hfar i j hij _ _ (Or.inr rfl) (Or.inl rfl)
  have fBB := hfar i j hij _ _ (Or.inr rfl) (Or.inr rfl)
  have m1 := ud_mul_commutes (z := A j) (hA i) (hB i)
  have m2 := ud_mul_commutes (z := B j) (hA i) (hB i)
  have mid := ud_commutes_mul (z := A i * B i) (hA j) (hB j)
  have ci := hcAB i
  have cj := hcAB j
  have e1 := ud_mul_le (Y := c j) (X' := A i * B i) (hc i) ((hA j).mul (hB j))
  have e2 := ud_mul_le (Y := c i) (X' := A j * B j) (hc j) ((hA i).mul (hB i))
  rw [ud_comm (c j * c i)] at e2
  have t1 := ud_triangle (c i * c j) (A i * B i * (A j * B j)) (c j * c i)
  have t2 := ud_triangle (A i * B i * (A j * B j)) (A j * B j * (A i * B i)) (c j * c i)
  linarith

/-- `κ(x_i, c_j) ≤ 2L + 20e`. -/
theorem ud_xc_comm (i j : Fin N) (hij : i ≠ j) :
    ud (x i * c j) (c j * x i) ≤ 2 * L + 20 * e := by
  have fAA := hfar i j hij _ _ (Or.inl rfl) (Or.inl rfl)
  have fAB := hfar i j hij _ _ (Or.inl rfl) (Or.inr rfl)
  have mid := ud_commutes_mul (z := A i) (hA j) (hB j)
  have xi := hxA i
  have cj := hcAB j
  have e1 := ud_mul_le (Y := c j) (X' := A i) (hx i) ((hA j).mul (hB j))
  have e2 := ud_mul_le (Y := x i) (X' := A j * B j) (hc j) (hA i)
  rw [ud_comm (c j * x i)] at e2
  have t1 := ud_triangle (x i * c j) (A i * (A j * B j)) (c j * x i)
  have t2 := ud_triangle (A i * (A j * B j)) (A j * B j * A i) (c j * x i)
  linarith

end Pairs

/-! ### Assembly -/

lemma sum_lt_half {N : ℕ} (f : Fin N → Fin N → ℝ) (hf : ∀ i j, f i j = f j i) :
    2 * ∑ i, ∑ j ∈ univ.filter (i < ·), f i j = ∑ i, ∑ j ∈ univ.filter (· ≠ i), f i j := by
  have h1 : ∑ i, ∑ j ∈ univ.filter (i < ·), f i j = ∑ i, ∑ j, if i < j then f i j else 0 := by
    simp only [sum_filter]
  have h2 : ∑ i, ∑ j, (if i < j then f i j else 0) = ∑ i, ∑ j, if j < i then f i j else 0 := by
    rw [sum_comm]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    split_ifs <;> simp [hf]
  have h3 : ∑ i, ∑ j ∈ univ.filter (· ≠ i), f i j =
      ∑ i, ∑ j, ((if i < j then f i j else 0) + (if j < i then f i j else 0)) := by
    simp only [sum_filter]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.ne', not_lt.mpr h.le]
    · subst h; simp
    · simp [h, h.ne, not_lt.mpr h.le]
  rw [h3]
  simp only [sum_add_distrib]
  rw [← h1, ← h2, ← h1]
  ring

lemma Kd_ge {Δ : ℝ} (h0 : 0 < Δ) (h1 : Δ ≤ 1) : 9 / Δ ≤ Kd Δ := by
  unfold Kd
  have hL : 0 ≤ Real.logb 2 (1 / Δ) :=
    Real.logb_nonneg (by norm_num) (by rw [le_div_iff₀ h0]; linarith)
  have : (9 : ℝ) ≤ Real.sqrt (80000 * (1 + Real.logb 2 (1 / Δ))) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith
  exact div_le_div_of_nonneg_right this h0.le

lemma Kd_sq_ge {Δ : ℝ} (h0 : 0 < Δ) (h1 : Δ ≤ 1) : 80000 ≤ Kd Δ ^ 2 := by
  unfold Kd
  have hL : 0 ≤ Real.logb 2 (1 / Δ) :=
    Real.logb_nonneg (by norm_num) (by rw [le_div_iff₀ h0]; linarith)
  rw [div_pow, Real.sq_sqrt (by positivity), le_div_iff₀ (by positivity)]
  have : Δ ^ 2 ≤ 1 := by nlinarith
  nlinarith

/-- **Theorem `thm:criterion`, "Moreover" clause** (unitary counting criterion), from the three
analytic inputs. -/
theorem counting_criterion_unitary (hS3 : UnitaryS3Round) (hPR : UnitaryPhaseRobust)
    (hM : UnitaryMargin) {S ι : Type*} (R : ι → FreeGroup S) (a b : S) (ia ib iab : ι)
    (hRa : R ia = FreeGroup.of a ^ 2) (hRb : R ib = FreeGroup.of b ^ 2)
    (hRab : R iab = (FreeGroup.of a * FreeGroup.of b) ^ 3)
    {N : ℕ} (w : Fin N → FreeGroup S) (Λ : ℕ) (hΛ : 1 ≤ Λ) (hw : TransportAreaLE R a b w Λ)
    {Ω : Type} [Fintype Ω] [DecidableEq Ω] (φ : FreeGroup S →* Matrix.unitaryGroup Ω ℂ)
    (Δ e : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ ≤ 1) (hrel : ∀ k, ud (phiM φ (R k)) 1 ≤ e)
    (hab : Δ ≤ ud (phiM φ (FreeGroup.of a * FreeGroup.of b)) 1)
    (hK : Kd Δ * Real.sqrt N * Λ * e ≤ 1) :
    (N : ℝ) * Δ ^ 2 / 12 ≤ Real.logb 2 (Fintype.card Ω) := by
  have he : 0 ≤ e := (ud_nonneg _ _).trans (hrel ia)
  set K := Kd Δ with hKdef
  have hK9 : 9 / Δ ≤ K := Kd_ge hΔ0 hΔ1
  have hKpos : 0 < K := lt_of_lt_of_le (by positivity) hK9
  have hΛ1 : (1 : ℝ) ≤ Λ := by exact_mod_cast hΛ
  -- the transported pairs
  let Wg : Fin N → FreeGroup S → FreeGroup S := fun i g => w i * g * (w i)⁻¹
  let A : Fin N → Matrix Ω Ω ℂ := fun i => phiM φ (Wg i (FreeGroup.of a))
  let B : Fin N → Matrix Ω Ω ℂ := fun i => phiM φ (Wg i (FreeGroup.of b))
  have hconj : ∀ i (g : FreeGroup S), phiM φ (Wg i g) =
      phiM φ (w i) * phiM φ g * (phiM φ (w i))ᴴ := by
    intro i g; simp only [Wg, phiM_mul, phiM_inv]
  have hWmul : ∀ i (g h : FreeGroup S), Wg i g * Wg i h = Wg i (g * h) := by
    intro i g h; simp only [Wg]; group
  have hA : ∀ i, IsU (A i) := fun i => isU_phi φ _
  have hB : ∀ i, IsU (B i) := fun i => isU_phi φ _
  have hdef : ∀ i (g : FreeGroup S), ud (phiM φ (Wg i g)) 1 = ud (phiM φ g) 1 := by
    intro i g; rw [hconj, ud_conj_one (isU_phi φ _)]
  have hA2 : ∀ i, ud (A i * A i) 1 ≤ e := by
    intro i
    rw [show A i * A i = phiM φ (Wg i (R ia)) by
      rw [← phiM_mul, hWmul, hRa, pow_two], hdef]
    exact hrel ia
  have hB2 : ∀ i, ud (B i * B i) 1 ≤ e := by
    intro i
    rw [show B i * B i = phiM φ (Wg i (R ib)) by
      rw [← phiM_mul, hWmul, hRb, pow_two], hdef]
    exact hrel ib
  have hAB3 : ∀ i, ud ((A i * B i) ^ 3) 1 ≤ e := by
    intro i
    rw [show (A i * B i) ^ 3 = phiM φ (Wg i (R iab)) by
      rw [← phiM_mul, hWmul, hRab]
      simp only [pow_succ, pow_zero, one_mul, phiM_mul, ← hWmul], hdef]
    exact hrel iab
  -- rounding
  choose x c hx hc hx2 hc3 hxc hxA hcAB using
    fun i => hS3 Ω (A i) (B i) e (hA i) (hB i) (hA2 i) (hB2 i) (hAB3 i)
  -- displacement
  have hΔi : ∀ i, Δ - 9 * e ≤ ud (c i) 1 := by
    intro i
    have h1 : ud (A i * B i) 1 = ud (phiM φ (FreeGroup.of a * FreeGroup.of b)) 1 := by
      rw [show A i * B i = phiM φ (Wg i (FreeGroup.of a * FreeGroup.of b)) by
        rw [← phiM_mul, hWmul], hdef]
    have t := ud_triangle (A i * B i) (c i) 1
    have t2 : ud 1 (A i * B i) = ud (phiM φ (FreeGroup.of a * FreeGroup.of b)) 1 := by
      rw [ud_comm]; exact h1
    rw [ud_comm (A i * B i) (c i), h1] at t
    have := hcAB i
    linarith
  -- far commutators
  have hfar : ∀ i j, i ≠ j → ∀ X Y : Matrix Ω Ω ℂ, (X = A i ∨ X = B i) → (Y = A j ∨ Y = B j) →
      ud (X * Y) (Y * X) ≤ Λ * e := by
    intro i j hij X Y hX hY
    obtain ⟨gx, hgx, rfl⟩ : ∃ gx ∈ [FreeGroup.of a, FreeGroup.of b], X = phiM φ (Wg i gx) := by
      rcases hX with rfl | rfl
      · exact ⟨_, by simp, rfl⟩
      · exact ⟨_, by simp, rfl⟩
    obtain ⟨gy, hgy, rfl⟩ : ∃ gy ∈ [FreeGroup.of a, FreeGroup.of b], Y = phiM φ (Wg j gy) := by
      rcases hY with rfl | rfl
      · exact ⟨_, by simp, rfl⟩
      · exact ⟨_, by simp, rfl⟩
    have harea := hw i j hij gx hgx gy hgy
    have h := ud_le_of_areaLEGen R φ e hrel he harea
    have hY' := isU_phi φ (Wg j gy)
    have hX' := isU_phi φ (Wg i gx)
    have hYX : IsU (phiM φ (Wg j gy) * phiM φ (Wg i gx)) := hY'.mul hX'
    calc ud (phiM φ (Wg i gx) * phiM φ (Wg j gy)) (phiM φ (Wg j gy) * phiM φ (Wg i gx))
        = ud (phiM φ (Wg i gx) * phiM φ (Wg j gy) * (phiM φ (Wg j gy) * phiM φ (Wg i gx))ᴴ)
            (phiM φ (Wg j gy) * phiM φ (Wg i gx) * (phiM φ (Wg j gy) * phiM φ (Wg i gx))ᴴ) :=
          (ud_mul_right hYX.conjT _ _).symm
      _ = ud (phiM φ (commG (Wg i gx) (Wg j gy))) 1 := by
          rw [hYX.2, conjTranspose_mul]
          simp only [commG, phiM_mul, phiM_inv, Matrix.mul_assoc]
      _ ≤ Λ * e := h
  have hcc : ∀ i j, i ≠ j → ud (c i * c j) (c j * c i) ≤ 40 * (Λ * e) := by
    intro i j hij
    have := ud_cc_comm A B x c e (Λ * e) hA hB hx hc hxA hcAB hfar i j hij
    nlinarith
  have hxc' : ∀ i j, i ≠ j → ud (x i * c j) (c j * x i) ≤ 22 * (Λ * e) := by
    intro i j hij
    have := ud_xc_comm A B x c e (Λ * e) hA hB hx hc hxA hcAB hfar i j hij
    nlinarith
  -- the sector bound
  have hPR' := hPR Ω N c x hc hx hc3 hx2 hxc
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0
    simp only [Nat.cast_zero, zero_mul, zero_div]
    rcases Nat.eq_zero_or_pos (Fintype.card Ω) with hD | hD
    · simp [hD]
    · exact Real.logb_nonneg (by norm_num) (by exact_mod_cast hD)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  -- numerical consequences of `hK`
  have hsq : K ^ 2 * (N * Λ ^ 2 * e ^ 2) ≤ 1 := by
    have h0 : 0 ≤ K * Real.sqrt N * Λ * e := by positivity
    have := mul_le_mul hK hK h0 zero_le_one
    have hs : Real.sqrt N ^ 2 = N := Real.sq_sqrt (by positivity)
    nlinarith
  have hNL : (N : ℝ) * Λ ^ 2 * e ^ 2 ≤ 1 / K ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have heK : e ≤ 1 / K := by
    have hNΛ : (1 : ℝ) ≤ N * Λ ^ 2 := by nlinarith
    have h1 : e ^ 2 ≤ (N : ℝ) * Λ ^ 2 * e ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hNΛ (sq_nonneg e)]
    have h2 : e ^ 2 ≤ (1 / K) ^ 2 := by rw [div_pow, one_pow]; linarith
    have hKi : (0 : ℝ) < 1 / K := by positivity
    nlinarith
  set d : Fin N → ℝ := fun i => ud (c i) 1 ^ 2
  set aa : Fin N → ℝ := fun i =>
    4 / 3 * ∑ j ∈ univ.filter (i < ·), ud (c i * c j) (c j * c i) ^ 2
  set bb : Fin N → ℝ := fun i =>
    4 / 3 * ∑ j ∈ univ.filter (· ≠ i), ud (x i * c j) (c j * x i) ^ 2
  have hd : ∀ i, (Δ - 9 / K) ^ 2 ≤ d i := by
    intro i
    have h1 : 0 ≤ Δ - 9 / K := by
      have : 9 / K ≤ Δ := by
        rw [div_le_iff₀ hKpos]
        have := hK9
        rw [div_le_iff₀ hΔ0] at this
        linarith
      linarith
    have h2 : Δ - 9 / K ≤ ud (c i) 1 := by
      have := hΔi i
      have : 9 * e ≤ 9 * (1 / K) := by linarith [heK]
      have e9 : 9 * (1 / K) = 9 / K := by ring
      linarith
    exact pow_le_pow_left₀ h1 h2 2
  have haa0 : ∀ i, 0 ≤ aa i := fun i => by
    have := sum_nonneg (fun j (_ : j ∈ univ.filter (i < ·)) => sq_nonneg (ud (c i * c j) (c j * c i)))
    simp only [aa]; positivity
  have hcard : ∀ i : Fin N, ((univ.filter (· ≠ i)).card : ℝ) ≤ N := fun i => by
    have : (univ.filter (· ≠ i)).card ≤ N := (card_filter_le _ _).trans (by simp)
    exact_mod_cast this
  have hcc2 : ∀ i, ∑ j ∈ univ.filter (· ≠ i), ud (c i * c j) (c j * c i) ^ 2 ≤
      N * (1600 * (Λ ^ 2 * e ^ 2)) := by
    intro i
    calc ∑ j ∈ univ.filter (· ≠ i), ud (c i * c j) (c j * c i) ^ 2
        ≤ ∑ _j ∈ univ.filter (· ≠ i), (1600 * (Λ ^ 2 * e ^ 2)) := by
          refine sum_le_sum fun j hj => ?_
          have h := hcc i j (mem_filter.mp hj).2.symm
          have h0 := ud_nonneg (c i * c j) (c j * c i)
          nlinarith
      _ ≤ N * (1600 * (Λ ^ 2 * e ^ 2)) := by
          rw [sum_const, nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (hcard i) (by positivity)
  have hsumaa : ∑ i, aa i ≤ N * (3200 / (3 * K ^ 2)) := by
    have hsym := sum_lt_half (fun i j => ud (c i * c j) (c j * c i) ^ 2)
      (fun i j => by rw [ud_comm])
    have : ∑ i, ∑ j ∈ univ.filter (· ≠ i), ud (c i * c j) (c j * c i) ^ 2 ≤
        N * (N * (1600 * (Λ ^ 2 * e ^ 2))) := by
      calc _ ≤ ∑ _i : Fin N, N * (1600 * (Λ ^ 2 * e ^ 2)) := sum_le_sum fun i _ => hcc2 i
        _ = _ := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    have e1 : ∑ i, aa i = 4 / 3 * ∑ i, ∑ j ∈ univ.filter (i < ·), ud (c i * c j) (c j * c i) ^ 2 := by
      simp only [aa, mul_sum]
    rw [e1]
    have hK2 : 0 < K ^ 2 := by positivity
    have : (N : ℝ) * (N * (1600 * (Λ ^ 2 * e ^ 2))) ≤ N * (1600 / K ^ 2) := by
      have h := mul_le_mul_of_nonneg_left hNL (by positivity : (0 : ℝ) ≤ 1600 * N)
      have e2 : (N : ℝ) * (1600 / K ^ 2) = 1600 * N * (1 / K ^ 2) := by ring
      have e3 : (N : ℝ) * (N * (1600 * (Λ ^ 2 * e ^ 2))) = 1600 * N * (N * Λ ^ 2 * e ^ 2) := by ring
      rw [e2, e3]; exact h
    have h3 : (N : ℝ) * (1600 / K ^ 2) * (2 / 3) = N * (3200 / (3 * K ^ 2)) := by
      field_simp; ring
    nlinarith
  have hbb : ∀ i, bb i ≤ 1936 / (3 * K ^ 2) := by
    intro i
    have : ∑ j ∈ univ.filter (· ≠ i), ud (x i * c j) (c j * x i) ^ 2 ≤ N * (484 * (Λ ^ 2 * e ^ 2)) := by
      calc ∑ j ∈ univ.filter (· ≠ i), ud (x i * c j) (c j * x i) ^ 2
          ≤ ∑ _j ∈ univ.filter (· ≠ i), (484 * (Λ ^ 2 * e ^ 2)) := by
            refine sum_le_sum fun j hj => ?_
            have h := hxc' i j (mem_filter.mp hj).2.symm
            have h0 := ud_nonneg (x i * c j) (c j * x i)
            nlinarith
        _ ≤ N * (484 * (Λ ^ 2 * e ^ 2)) := by
            rw [sum_const, nsmul_eq_mul]
            exact mul_le_mul_of_nonneg_right (hcard i) (by positivity)
    have hK2 : 0 < K ^ 2 := by positivity
    have h4 : (N : ℝ) * (484 * (Λ ^ 2 * e ^ 2)) ≤ 484 / K ^ 2 := by
      have := mul_le_mul_of_nonneg_left hNL (by norm_num : (0 : ℝ) ≤ 484)
      rw [mul_div_assoc'] at this
      nlinarith
    have h5 : 4 / 3 * (484 / K ^ 2) = 1936 / (3 * K ^ 2) := by field_simp; ring
    simp only [bb]
    nlinarith
  have haa1 : ∀ i, aa i ≤ 1 := by
    intro i
    have hsub : ∑ j ∈ univ.filter (i < ·), ud (c i * c j) (c j * c i) ^ 2 ≤
        ∑ j ∈ univ.filter (· ≠ i), ud (c i * c j) (c j * c i) ^ 2 := by
      refine sum_le_sum_of_subset_of_nonneg (fun j hj => ?_) (fun j _ _ => sq_nonneg _)
      simp only [mem_filter, mem_univ, true_and] at hj ⊢
      exact hj.ne'
    have h2 := hcc2 i
    have hK80 := Kd_sq_ge hΔ0 hΔ1
    rw [← hKdef] at hK80
    have h3 : (N : ℝ) * (1600 * (Λ ^ 2 * e ^ 2)) ≤ 1600 / K ^ 2 := by
      have := mul_le_mul_of_nonneg_left hNL (by norm_num : (0 : ℝ) ≤ 1600)
      have e2 : (N : ℝ) * (1600 * (Λ ^ 2 * e ^ 2)) = 1600 * (N * Λ ^ 2 * e ^ 2) := by ring
      rw [e2]; linarith [show (1600 : ℝ) * (1 / K ^ 2) = 1600 / K ^ 2 by ring]
    have h4 : 1600 / K ^ 2 ≤ 1600 / 80000 := div_le_div_of_nonneg_left (by norm_num)
      (by norm_num) hK80
    simp only [aa]
    nlinarith
  have hmargin := hM N Δ d aa bb hΔ0 hΔ1 hd haa0 haa1 hsumaa hbb
  exact hmargin.trans hPR'

end Lamps
