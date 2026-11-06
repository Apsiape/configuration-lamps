import Lamps.UnitaryProjBasic
import Lamps.UnitaryPhaseFinal

/-!
# The projection estimates `UnitaryAhatProj` and `UnitaryBhatProj`

Both follow from `core_bound` (Lemma `lem:projections` for the averaging projections):
* `â_{i,t}² ≤ (4/3) ∑_{j>i} κ(cᵢ,cⱼ)²`: cancel the common unitary prefix, apply `core_bound` to
  `x = cᵢᵗ` and the unsigned projections `B_{cⱼ,+}` (`j > i`), with `‖x - B x‖² = ⅓‖xcⱼ - cⱼx‖²`
  and `‖cᵢᵗcⱼ - cⱼcᵢᵗ‖ ≤ ‖cᵢcⱼ - cⱼcᵢ‖` (`t ∈ {0,1,2}`, `cᵢ² = cᵢ*`).
* `b̂ᵢ² ≤ (4/3) ∑_{j≠i} κ(xᵢ,cⱼ)²`: `core_bound` for `x = xᵢ` with the signed projection at `j = i`,
  which fixes `xᵢ` because `xᵢ cᵢ xᵢ = cᵢ*`.
-/

namespace Lamps

open Finset Matrix ComplexConjugate

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

lemma ud_sq_nq (X Y : Matrix Ω Ω ℂ) : ud X Y ^ 2 = nq (X - Y) / Fintype.card Ω := by
  unfold ud uhs nq
  exact Real.sq_sqrt (div_nonneg (Houghton.nsq_nonneg _) (Nat.cast_nonneg _))

lemma nq_zero : nq (0 : Matrix Ω Ω ℂ) = 0 := by simp [nq, Houghton.nsq]

lemma pow_sandwich (A X : Matrix Ω Ω ℂ) (h : A * X * A = X) : ∀ n : ℕ, A ^ n * X * A ^ n = X
  | 0 => by rw [pow_zero, Matrix.one_mul, Matrix.mul_one]
  | n + 1 => by
    have e1 : A ^ (n + 1) = A * A ^ n := pow_succ' A n
    have e2 : A ^ (n + 1) = A ^ n * A := pow_succ A n
    calc A ^ (n + 1) * X * A ^ (n + 1) = (A * A ^ n) * X * (A ^ n * A) := by rw [← e1, ← e2]
      _ = A * (A ^ n * X * A ^ n) * A := by simp only [Matrix.mul_assoc]
      _ = X := by rw [pow_sandwich A X h n, h]

lemma cons_add_single_zero {N : ℕ} (a t : Fin 3) (h : Fin N → Fin 3) :
    (Fin.cons a h : Fin (N + 1) → Fin 3) + Pi.single 0 t = Fin.cons (a + t) h := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j <;> simp [Pi.single_apply]

lemma cons_add_single_succ {N : ℕ} (a t : Fin 3) (h : Fin N → Fin 3) (i : Fin N) :
    (Fin.cons a h : Fin (N + 1) → Fin 3) + Pi.single i.succ t =
      Fin.cons a (h + Pi.single i t) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j <;> simp [Pi.single_apply, Fin.succ_inj]

lemma flipS_false {N : ℕ} (h : Fin N → Fin 3) : flipS (fun _ => false) h = h := by
  funext j
  simp [flipS, sg]

lemma flipAt_eq_flipS {N : ℕ} (i : Fin N) (g : Fin N → Fin 3) :
    Houghton.flipAt i g = flipS (fun j => decide (j = i)) g := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [Houghton.flipAt, flipS, sg, Houghton.fl_eq_neg]
  · simp [Houghton.flipAt, flipS, sg, hj, Function.update_of_ne hj]

lemma kappa_pow {c d : Matrix Ω Ω ℂ} (hc : IsU c) (hc3 : c ^ 3 = 1) (t : Fin 3) :
    nq (c ^ t.val * d - d * c ^ t.val) ≤ nq (c * d - d * c) := by
  have ht : t.val = 0 ∨ t.val = 1 ∨ t.val = 2 := by omega
  rcases ht with h | h | h <;> rw [h]
  · rw [pow_zero, Matrix.one_mul, Matrix.mul_one, sub_self, nq_zero]
    exact nq_nonneg _
  · rw [pow_one]
  · rw [d_sq hc hc3]
    have e : cᴴ * d - d * cᴴ = cᴴ * ((d * c - c * d) * cᴴ) := by
      rw [Matrix.sub_mul, Matrix.mul_sub]
      simp only [Matrix.mul_assoc, hc.2, Matrix.mul_one]
      rw [← Matrix.mul_assoc cᴴ c, hc.1, Matrix.one_mul]
    have : nq (cᴴ * d - d * cᴴ) = nq (c * d - d * c) := by
      rw [e, nq_mul_left (U := cᴴ) (by rw [conjTranspose_conjTranspose]; exact hc.2),
        nq_mul_right (U := cᴴ) (by rw [conjTranspose_conjTranspose]; exact hc.1), ← neg_sub,
        nq_neg]
    exact this.le

lemma filt_zero {N : ℕ} (f : Fin (N + 1) → ℝ) :
    ∑ j ∈ univ.filter (fun j : Fin (N + 1) => 0 < j), f j = ∑ j : Fin N, f j.succ := by
  rw [sum_filter, Fin.sum_univ_succ]
  simp [Fin.succ_pos]

lemma filt_succ {N : ℕ} (f : Fin (N + 1) → ℝ) (i : Fin N) :
    ∑ j ∈ univ.filter (fun j : Fin (N + 1) => i.succ < j), f j =
      ∑ j ∈ univ.filter (fun j : Fin N => i < j), f j.succ := by
  rw [sum_filter, sum_filter, Fin.sum_univ_succ]
  simp [Fin.succ_lt_succ_iff]

/-- Unnormalized form of `â_{i,t}² ≤ aᵢ`. -/
theorem ahat_sum : ∀ (N : ℕ) (c : Fin N → Matrix Ω Ω ℂ), (∀ i, IsU (c i)) →
    (∀ i, c i ^ 3 = 1) → ∀ (i : Fin N) (t : Fin 3),
    ∑ g : Fin N → Fin 3, nq (fprodU c g * c i ^ t.val - fprodU c (g + Pi.single i t)) ≤
      3 ^ N * (4 / 3 * ∑ j ∈ univ.filter (i < ·), nq (c i * c j - c j * c i))
  | 0, _, _, _, i, _ => i.elim0
  | N + 1, c, hc, hc3, i, t => by
    rw [Houghton.sum_cons3]
    cases i using Fin.cases with
    | zero =>
      have e : ∀ (a : Fin 3) (h : Fin N → Fin 3),
          nq (fprodU c (Fin.cons a h) * c 0 ^ t.val - fprodU c (Fin.cons a h + Pi.single 0 t)) =
          nq (fprodU (fun j => c j.succ) h * c 0 ^ t.val -
            c 0 ^ t.val * fprodU (fun j => c j.succ) (flipS (fun _ => false) h)) := by
        intro a h
        rw [cons_add_single_zero, fprodU_cons, fprodU_cons, mpow_val_add (c 0) (hc3 0),
          flipS_false, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_sub]
        exact nq_mul_left ((hc 0).pow _).1 _
      simp only [e, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
      have core := core_bound (fun j => c j.succ) (fun _ => false) (fun j => hc _)
        (fun j => hc3 _) (c 0 ^ t.val)
      beta_reduce at core
      have hdef : ∀ j : Fin N, nq (c 0 ^ t.val - Bop (c j.succ) false (c 0 ^ t.val)) ≤
          1 / 3 * nq (c 0 * c j.succ - c j.succ * c 0) := by
        intro j
        rw [Bop_false_defect (hc _) (hc3 _)]
        have := kappa_pow (d := c j.succ) (hc 0) (hc3 0) t
        linarith
      have hs := sum_le_sum fun j (_ : j ∈ univ) => hdef j
      rw [← mul_sum] at hs
      rw [filt_zero]
      have h3 : (0 : ℝ) ≤ 3 ^ N := by positivity
      rw [pow_succ]
      nlinarith [mul_le_mul_of_nonneg_left hs h3]
    | succ i =>
      have e : ∀ (a : Fin 3) (h : Fin N → Fin 3),
          nq (fprodU c (Fin.cons a h) * c i.succ ^ t.val -
            fprodU c (Fin.cons a h + Pi.single i.succ t)) =
          nq (fprodU (fun j => c j.succ) h * c i.succ ^ t.val -
            fprodU (fun j => c j.succ) (h + Pi.single i t)) := by
        intro a h
        rw [cons_add_single_succ, fprodU_cons, fprodU_cons, Matrix.mul_assoc, ← Matrix.mul_sub]
        exact nq_mul_left ((hc 0).pow _).1 _
      simp only [e, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
      have ih := ahat_sum N (fun j => c j.succ) (fun j => hc _) (fun j => hc3 _) i t
      beta_reduce at ih
      rw [filt_succ]
      rw [pow_succ]
      nlinarith [ih]

/-- **Projection estimate for `â`**. -/
theorem unitaryAhatProj : UnitaryAhatProj := by
  intro Ω _ _ N c hc hc3 i
  have key : ∀ t : Fin 3, ahat2 c i t ≤ aCoef c i := by
    intro t
    have hs := ahat_sum N c hc hc3 i t
    have hD : (0 : ℝ) ≤ Fintype.card Ω := Nat.cast_nonneg _
    unfold ahat2 aCoef
    simp only [ud_sq_nq, ← sum_div]
    rw [div_le_iff₀ (by positivity)]
    refine (div_le_div_of_nonneg_right hs hD).trans (le_of_eq ?_)
    ring
  exact ⟨key 1, key 2⟩

lemma fix_of_rel {d X : Matrix Ω Ω ℂ} (hd : IsU d) (hd3 : d ^ 3 = 1) (hX : IsU X)
    (hXX : X * X = 1) (hrel : X * d * X = dᴴ) : ∀ k : Fin 3, Tm d true k X = X := by
  have hXh : Xᴴ = X := by
    calc Xᴴ = Xᴴ * (X * X) := by rw [hXX, Matrix.mul_one]
      _ = X := by rw [← Matrix.mul_assoc, hX.1, Matrix.one_mul]
  have h1 : X * (dᴴ * X) = d := by
    have := congrArg conjTranspose hrel
    rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hXh] at this
  have h2 : dᴴ * X = X * d := by
    calc dᴴ * X = X * X * (dᴴ * X) := by rw [hXX, Matrix.one_mul]
      _ = X * d := by rw [Matrix.mul_assoc, h1]
  have h3 : dᴴ * X * dᴴ = X := by rw [h2, Matrix.mul_assoc, hd.2, Matrix.mul_one]
  intro k
  show (d ^ k.val)ᴴ * X * d ^ (-k).val = X
  rw [pw_neg hd hd3, conjTranspose_pow]
  exact pow_sandwich _ _ h3 _

/-- Unnormalized form of `b̂ᵢ² ≤ bᵢ`. -/
theorem bhat_sum (N : ℕ) (c x : Fin N → Matrix Ω Ω ℂ) (hc : ∀ i, IsU (c i))
    (hx : ∀ i, IsU (x i)) (hc3 : ∀ i, c i ^ 3 = 1) (hxx : ∀ i, x i * x i = 1)
    (hrel : ∀ i, x i * c i * x i = (c i)ᴴ) (i : Fin N) :
    ∑ g : Fin N → Fin 3, nq (fprodU c g - x i * fprodU c (Houghton.flipAt i g) * (x i)ᴴ) ≤
      3 ^ N * (4 / 3 * ∑ j ∈ univ.filter (· ≠ i), nq (x i * c j - c j * x i)) := by
  have e : ∀ g, nq (fprodU c g - x i * fprodU c (Houghton.flipAt i g) * (x i)ᴴ) =
      nq (fprodU c g * x i - x i * fprodU c (flipS (fun j => decide (j = i)) g)) := by
    intro g
    rw [← nq_mul_right (hx i).2 (fprodU c g - x i * fprodU c (Houghton.flipAt i g) * (x i)ᴴ),
      Matrix.sub_mul, Matrix.mul_assoc (x i * fprodU c (Houghton.flipAt i g)) (x i)ᴴ (x i),
      (hx i).1, Matrix.mul_one, flipAt_eq_flipS]
  simp only [e]
  have core := core_bound c (fun j => decide (j = i)) hc hc3 (x i)
  beta_reduce at core
  have hsum : ∑ j, nq (x i - Bop (c j) (decide (j = i)) (x i)) =
      1 / 3 * ∑ j ∈ univ.filter (· ≠ i), nq (x i * c j - c j * x i) := by
    rw [mul_sum, sum_filter]
    refine sum_congr rfl fun j _ => ?_
    by_cases hj : j = i
    · rw [hj, show decide (i = i) = true from decide_eq_true rfl, Bop_true_fix (hc i) (hc3 i) (x i)
        (fix_of_rel (hc i) (hc3 i) (hx i) (hxx i) (hrel i)), sub_self, nq_zero]
      simp
    · rw [decide_eq_false hj, Bop_false_defect (hc j) (hc3 j)]
      simp [hj]
  rw [hsum] at core
  linarith

/-- **Projection estimate for `b̂`**. -/
theorem unitaryBhatProj : UnitaryBhatProj := by
  intro Ω _ _ N c x hc hx hc3 hxx hrel i
  have hs := bhat_sum N c x hc hx hc3 hxx hrel i
  have hD : (0 : ℝ) ≤ Fintype.card Ω := Nat.cast_nonneg _
  unfold bhat2 bCoef
  simp only [ud_sq_nq, ← sum_div]
  rw [div_le_iff₀ (by positivity)]
  refine (div_le_div_of_nonneg_right hs hD).trans (le_of_eq ?_)
  ring

end Lamps
