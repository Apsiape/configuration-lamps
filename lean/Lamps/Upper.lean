import FiniteLean.GroupTheory.Sofic.Profile
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Theorem A(b): affine hashing (Lemma `lem:hash`), counting form

Configurations of a finite set `P` of points are `Finset P` (`+` = `∆`). An affine hash
`η : 𝔽₂^P → 𝔽₂^k` is given by its parameters `h = (L, z)`, `L : P → 𝔽₂^k` (images of the basis
vectors) and `z : 𝔽₂^k`: `η_h(v) = ∑_{y ∈ v} L y + z`. "Probability over a uniform `η`" is counting
over the finite set `Hp P k` of parameters.

Proved here: the collision count `#{h | η_h v = η_h w} · 2^k = #Hp` for `v ≠ w`
(`collide_card`), and the union bound for injectivity on a set `S`
(`noninj_card_le`: at most `|S|(|S|-1)/2^k` of all parameters are not injective on `S`).
-/

namespace Lamps.Hash

open Finset
open scoped symmDiff

variable {P : Type*} [Fintype P] [DecidableEq P] (k : ℕ)

/-- Codes `𝔽₂^k`. -/
abbrev Code := Fin k → ZMod 2

/-- Hash parameters. -/
abbrev Hp (P : Type*) (k : ℕ) := (P → Code k) × Code k

/-- The affine hash `η_h(v) = ∑_{y ∈ v} L y + z`. -/
def evalH (h : Hp P k) (v : Finset P) : Code k := (∑ y ∈ v, h.1 y) + h.2

theorem code_add_self (x : Code k) : x + x = 0 := by
  funext i; simp only [Pi.add_apply, Pi.zero_apply]
  generalize x i = c; fin_cases c <;> rfl

theorem code_add_eq_zero_iff (x y : Code k) : x + y = 0 ↔ x = y := by
  constructor
  · intro h
    have := congrArg (· + y) h
    simp only [add_assoc, code_add_self, add_zero, zero_add] at this
    exact this
  · rintro rfl; exact code_add_self k x

theorem sum_eq_sum_ite (f : P → Code k) (v : Finset P) :
    ∑ y ∈ v, f y = ∑ y, if y ∈ v then f y else 0 := by
  rw [← Finset.sum_filter]; congr 1; ext y; simp

theorem sum_add_sum (f : P → Code k) (v w : Finset P) :
    ∑ y ∈ v, f y + ∑ y ∈ w, f y = ∑ y ∈ v ∆ w, f y := by
  rw [sum_eq_sum_ite, sum_eq_sum_ite k f w, sum_eq_sum_ite k f (v ∆ w), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hv : y ∈ v <;> by_cases hw : y ∈ w <;>
    simp [hv, hw, Finset.mem_symmDiff, code_add_self]

theorem evalH_eq_iff (h : Hp P k) (v w : Finset P) :
    evalH k h v = evalH k h w ↔ ∑ y ∈ v ∆ w, h.1 y = 0 := by
  unfold evalH
  rw [← sum_add_sum, code_add_eq_zero_iff, add_left_inj]

theorem card_code : Fintype.card (Code k) = 2 ^ k := by simp [ZMod.card]

/-- Shift the image of `y₀`. -/
def shiftH (y₀ : P) (c : Code k) : Hp P k ≃ Hp P k where
  toFun h := (Function.update h.1 y₀ (h.1 y₀ + c), h.2)
  invFun h := (Function.update h.1 y₀ (h.1 y₀ + c), h.2)
  left_inv h := by
    ext y : 2 <;> simp only
    · by_cases hy : y = y₀
      · subst hy; simp [add_assoc, code_add_self]
      · simp [Function.update_of_ne hy]
  right_inv h := by
    ext y : 2 <;> simp only
    · by_cases hy : y = y₀
      · subst hy; simp [add_assoc, code_add_self]
      · simp [Function.update_of_ne hy]

omit [Fintype P] in
theorem sum_shiftH (D : Finset P) {y₀ : P} (hy : y₀ ∈ D) (c : Code k) (h : Hp P k) :
    ∑ y ∈ D, (shiftH k y₀ c h).1 y = ∑ y ∈ D, h.1 y + c := by
  rw [← Finset.add_sum_erase D _ hy, ← Finset.add_sum_erase D _ hy]
  have : ∑ y ∈ D.erase y₀, (shiftH k y₀ c h).1 y = ∑ y ∈ D.erase y₀, h.1 y := by
    apply Finset.sum_congr rfl
    intro y hy'
    simp [shiftH, Function.update_of_ne (Finset.ne_of_mem_erase hy')]
  rw [this]
  simp only [shiftH, Equiv.coe_fn_mk, Function.update_self]
  rw [add_right_comm]

/-- All fibres of `h ↦ ∑_{y ∈ D} L y` have the same size when `D ≠ ∅`. -/
theorem fiber_card_eq (D : Finset P) {y₀ : P} (hy : y₀ ∈ D) (c : Code k) :
    (univ.filter fun h : Hp P k => ∑ y ∈ D, h.1 y = c).card =
      (univ.filter fun h : Hp P k => ∑ y ∈ D, h.1 y = 0).card := by
  apply Finset.card_equiv (shiftH k y₀ c)
  intro h
  simp only [mem_filter, mem_univ, true_and]
  rw [sum_shiftH k D hy, code_add_eq_zero_iff]

theorem zero_fiber_card (D : Finset P) {y₀ : P} (hy : y₀ ∈ D) :
    (univ.filter fun h : Hp P k => ∑ y ∈ D, h.1 y = 0).card * 2 ^ k = Fintype.card (Hp P k) := by
  have hsum : Fintype.card (Hp P k) =
      ∑ c : Code k, (univ.filter fun h : Hp P k => ∑ y ∈ D, h.1 y = c).card := by
    rw [← card_univ]
    exact Finset.card_eq_sum_card_fiberwise (fun _ _ => mem_univ _)
  rw [hsum, Finset.sum_congr rfl (fun c _ => fiber_card_eq k D hy c), sum_const, card_univ,
    card_code, smul_eq_mul, mul_comm]

/-- **Collision count** (proof of Lemma `lem:hash`): for `v ≠ w`, exactly a fraction `2^{-k}` of
the affine hashes collide on `v, w`. -/
theorem collide_card {v w : Finset P} (hvw : v ≠ w) :
    (univ.filter fun h : Hp P k => evalH k h v = evalH k h w).card * 2 ^ k =
      Fintype.card (Hp P k) := by
  obtain ⟨y₀, hy⟩ : (v ∆ w).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, ← Finset.bot_eq_empty, symmDiff_eq_bot]; exact hvw
  rw [← zero_fiber_card k (v ∆ w) hy]
  congr 2
  ext h; simp only [mem_filter, mem_univ, true_and, evalH_eq_iff]

/-- **Union bound**: the number of hashes that are not injective on `S` is at most
`|S| (|S| - 1) · #Hp / 2^k`. -/
theorem noninj_card_le (S : Finset (Finset P)) :
    (univ.filter fun h : Hp P k => ∃ v ∈ S, ∃ w ∈ S, v ≠ w ∧ evalH k h v = evalH k h w).card *
      2 ^ k ≤ S.offDiag.card * Fintype.card (Hp P k) := by
  have hsub : (univ.filter fun h : Hp P k => ∃ v ∈ S, ∃ w ∈ S, v ≠ w ∧ evalH k h v = evalH k h w) ⊆
      S.offDiag.biUnion fun vw => univ.filter fun h : Hp P k => evalH k h vw.1 = evalH k h vw.2 := by
    intro h hh
    simp only [mem_filter, mem_univ, true_and] at hh
    obtain ⟨v, hv, w, hw, hne, he⟩ := hh
    simp only [mem_biUnion, mem_offDiag, mem_filter, mem_univ, true_and]
    exact ⟨(v, w), ⟨hv, hw, hne⟩, he⟩
  calc _ ≤ (S.offDiag.biUnion fun vw =>
          univ.filter fun h : Hp P k => evalH k h vw.1 = evalH k h vw.2).card * 2 ^ k :=
        Nat.mul_le_mul_right _ (card_le_card hsub)
    _ ≤ (∑ vw ∈ S.offDiag, (univ.filter fun h : Hp P k => evalH k h vw.1 = evalH k h vw.2).card)
          * 2 ^ k := Nat.mul_le_mul_right _ card_biUnion_le
    _ = ∑ vw ∈ S.offDiag, (univ.filter fun h : Hp P k => evalH k h vw.1 = evalH k h vw.2).card
          * 2 ^ k := by rw [Finset.sum_mul]
    _ = ∑ _vw ∈ S.offDiag, Fintype.card (Hp P k) := by
          apply Finset.sum_congr rfl
          intro vw hvw
          exact collide_card k (mem_offDiag.mp hvw).2.2
    _ = S.offDiag.card * Fintype.card (Hp P k) := by rw [sum_const, smul_eq_mul]

end Lamps.Hash

/-! ### The size and error arithmetic of Proposition `prop:upper` -/

namespace Lamps.UpperArith

open Real

theorem log_two_gt_half : 1 / 2 < Real.log 2 := by
  have h := Real.add_one_lt_exp (x := -(1 / 2)) (by norm_num)
  have h2 : Real.exp (1 / 2) < 2 := by
    have : Real.exp (1 / 2) * Real.exp (-(1 / 2)) = 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (1 / 2)]
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  exact h2

/-- `log₂ x ≤ 2 (x - 1)` for `x ≥ 1`. -/
theorem logb_le (x : ℝ) (hx : 1 ≤ x) : Real.logb 2 x ≤ 2 * (x - 1) := by
  have h1 := Real.log_le_sub_one_of_pos (by linarith : 0 < x)
  have h2 := log_two_gt_half
  rw [Real.logb, div_le_iff₀ (by linarith)]
  nlinarith

/-- **Arithmetic of Proposition `prop:upper`** (with the ordered-pair union bound, hence `8ℓ²r`
in place of the paper's `4ℓ²r`): for `ℓ ≥ 1`, `r ≥ 1`, `m = ⌈8ℓr⌉`, `k = ⌈log₂(8ℓ²r)⌉`,
the error `8ℓ/(2m+1) + 2ℓ(2ℓ-1)/2^k` is `< 1/r`, and the model size
`(2m+1)² · 2^{k(6m+10)} · 6^{2^k}` has `log₂ ≤ 500 ℓ² r log₂(2+r)`. -/
theorem upper_arith (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (r : ℝ) (hr : 1 ≤ r) :
    (8 * ℓ / (2 * (⌈8 * ℓ * r⌉₊ : ℝ) + 1) +
        2 * ℓ * (2 * ℓ - 1) / (2 : ℝ) ^ ⌈Real.logb 2 (8 * ℓ ^ 2 * r)⌉₊ < 1 / r) ∧
    Real.logb 2 (((2 * ⌈8 * ℓ * r⌉₊ + 1) ^ 2 *
        2 ^ (⌈Real.logb 2 (8 * ℓ ^ 2 * r)⌉₊ * (6 * ⌈8 * ℓ * r⌉₊ + 10)) *
        6 ^ (2 ^ ⌈Real.logb 2 (8 * ℓ ^ 2 * r)⌉₊) : ℕ) : ℝ) ≤
      500 * ℓ ^ 2 * r * Real.logb 2 (2 + r) := by
  set m := ⌈8 * ℓ * r⌉₊ with hmdef
  set k := ⌈Real.logb 2 (8 * ℓ ^ 2 * r)⌉₊ with hkdef
  have hℓ' : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hr0 : 0 < r := by linarith
  have hℓr : 1 ≤ (ℓ : ℝ) * r := by nlinarith
  have hm1 : 8 * ℓ * r ≤ (m : ℝ) := Nat.le_ceil _
  have hm2 : (m : ℝ) < 8 * ℓ * r + 1 := Nat.ceil_lt_add_one (by positivity)
  have hX : 0 < 8 * (ℓ : ℝ) ^ 2 * r := by positivity
  have hk1 : Real.logb 2 (8 * ℓ ^ 2 * r) ≤ k := Nat.le_ceil _
  have hk0 : 0 ≤ Real.logb 2 (8 * ℓ ^ 2 * r) :=
    Real.logb_nonneg (by norm_num) (by nlinarith)
  have hk2 : (k : ℝ) < Real.logb 2 (8 * ℓ ^ 2 * r) + 1 := Nat.ceil_lt_add_one hk0
  have h2k1' : 8 * (ℓ : ℝ) ^ 2 * r ≤ (2 : ℝ) ^ (k : ℝ) :=
    (Real.rpow_logb (by norm_num) (by norm_num) hX).symm.le.trans
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) hk1)
  have h2k1 : 8 * (ℓ : ℝ) ^ 2 * r ≤ (2 : ℝ) ^ k := by rwa [Real.rpow_natCast] at h2k1'
  have h2k2' : (2 : ℝ) ^ (k : ℝ) < 16 * ℓ ^ 2 * r := by
    calc (2 : ℝ) ^ (k : ℝ) < (2 : ℝ) ^ (Real.logb 2 (8 * ℓ ^ 2 * r) + 1) :=
          Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hk2
      _ = 16 * ℓ ^ 2 * r := by
          rw [Real.rpow_add (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hX]; ring
  have h2k2 : (2 : ℝ) ^ k < 16 * ℓ ^ 2 * r := by rwa [Real.rpow_natCast] at h2k2'
  constructor
  · -- error bound
    have e1 : 8 * (ℓ : ℝ) / (2 * m + 1) < 1 / (2 * r) := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith
    have e2 : 2 * (ℓ : ℝ) * (2 * ℓ - 1) / (2 : ℝ) ^ k ≤ 1 / (2 * r) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    have : 1 / (2 * r) + 1 / (2 * r) = 1 / r := by field_simp; ring
    linarith
  · -- size bound
    have hL : 1 ≤ Real.logb 2 (2 + r) := by
      rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]; norm_num; linarith
    have hpos1 : (0 : ℝ) < ((2 * m + 1) ^ 2 : ℕ) := by positivity
    have hpos2 : (0 : ℝ) < ((2 ^ (k * (6 * m + 10))) : ℕ) := by positivity
    have hpos3 : (0 : ℝ) < ((6 ^ (2 ^ k)) : ℕ) := by positivity
    rw [Nat.cast_mul, Nat.cast_mul, Real.logb_mul (by positivity) (by positivity),
      Real.logb_mul (by positivity) (by positivity)]
    simp only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    rw [Real.logb_pow, Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
    -- the three terms
    have t1 : Real.logb 2 (2 * (m : ℝ) + 1) ≤ 36 * ℓ * r := by
      have := logb_le (2 * (m : ℝ) + 1) (by have : (0 : ℝ) ≤ m := Nat.cast_nonneg _; linarith)
      nlinarith
    have hlog6 : Real.logb 2 6 ≤ 3 := by
      rw [Real.logb_le_iff_le_rpow (by norm_num) (by norm_num)]
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
    have hlog6' : 0 ≤ Real.logb 2 6 := Real.logb_nonneg (by norm_num) (by norm_num)
    have t3 : (2 : ℝ) ^ k * Real.logb 2 6 ≤ 48 * ℓ ^ 2 * r := by nlinarith
    have hkb : (k : ℝ) ≤ 5 * ℓ * Real.logb 2 (2 + r) := by
      have hl := logb_le (ℓ : ℝ) hℓ'
      have hr' : Real.logb 2 r ≤ Real.logb 2 (2 + r) :=
        Real.logb_le_logb_of_le (by norm_num) hr0 (by linarith)
      have hsplit : Real.logb 2 (8 * ℓ ^ 2 * r) = 3 + 2 * Real.logb 2 ℓ + Real.logb 2 r := by
        rw [Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by norm_num)
          (by positivity), Real.logb_pow, show (8 : ℝ) = 2 ^ 3 by norm_num, Real.logb_pow,
          Real.logb_self_eq_one (by norm_num)]
        push_cast; ring
      nlinarith
    have hD : 6 * (m : ℝ) + 10 ≤ 64 * ℓ * r := by nlinarith
    have hk0' : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    have t2 : (k : ℝ) * (6 * m + 10) ≤ 320 * ℓ ^ 2 * r * Real.logb 2 (2 + r) := by
      have := mul_le_mul hkb hD (by positivity) (by positivity)
      nlinarith
    have a1 : (ℓ : ℝ) * r ≤ ℓ ^ 2 * r * Real.logb 2 (2 + r) := by
      have : (ℓ : ℝ) * r ≤ ℓ ^ 2 * r := by nlinarith
      have : (ℓ : ℝ) ^ 2 * r ≤ ℓ ^ 2 * r * Real.logb 2 (2 + r) := by
        have : 0 ≤ (ℓ : ℝ) ^ 2 * r := by positivity
        nlinarith
      linarith
    have a2 : (ℓ : ℝ) ^ 2 * r ≤ ℓ ^ 2 * r * Real.logb 2 (2 + r) := by
      have : 0 ≤ (ℓ : ℝ) ^ 2 * r := by positivity
      nlinarith
    push_cast
    nlinarith

end Lamps.UpperArith

/-! ### Hashed lamp functions (Lemma `lem:hash`, deterministic part) -/

namespace Lamps.Hash

variable {P : Type*} [Fintype P] [DecidableEq P] (k : ℕ)

/-- A lamp part with finite support, as an ordered list of (configuration, value) entries;
`lampFun L w` is the product, in list order, of the values at `w`. -/
def lampFun (L : List (Finset P × Equiv.Perm (Fin 3))) (w : Finset P) : Equiv.Perm (Fin 3) :=
  ((L.filter fun e => e.1 = w).map Prod.snd).prod

/-- The hashed lamp function `λ^η`: the product, in list order, of the values at configurations
hashed to `z`. -/
def hashLamp (h : Hp P k) (L : List (Finset P × Equiv.Perm (Fin 3))) (z : Code k) :
    Equiv.Perm (Fin 3) :=
  ((L.filter fun e => evalH k h e.1 = z).map Prod.snd).prod

/-- `η` is injective on the configurations of `L`. -/
def InjOn (h : Hp P k) (L : List (Finset P × Equiv.Perm (Fin 3))) : Prop :=
  ∀ e ∈ L, ∀ e' ∈ L, evalH k h e.1 = evalH k h e'.1 → e.1 = e'.1

/-- If `η` is injective on the support, `λ^η (η w) = λ w` for every configuration `w` of `L`. -/
theorem hashLamp_eval {h : Hp P k} {L : List (Finset P × Equiv.Perm (Fin 3))} (hinj : InjOn k h L)
    {e₀ : Finset P × Equiv.Perm (Fin 3)} (he₀ : e₀ ∈ L) :
    hashLamp k h L (evalH k h e₀.1) = lampFun L e₀.1 := by
  unfold hashLamp lampFun
  congr 2
  apply List.filter_congr
  intro e he
  simp only [decide_eq_decide]
  exact ⟨fun hh => hinj e he e₀ he₀ hh, fun hh => by rw [hh]⟩

/-- Off the hashed support, `λ^η = 1`. -/
theorem hashLamp_off {h : Hp P k} {L : List (Finset P × Equiv.Perm (Fin 3))} {z : Code k}
    (hz : ∀ e ∈ L, evalH k h e.1 ≠ z) : hashLamp k h L z = 1 := by
  unfold hashLamp
  rw [List.filter_eq_nil_iff.mpr (by intro e he; simpa using hz e he)]
  rfl

/-- If `η` is injective on the support, the hashed lamp functions of `L₁ ++ L₂` and of the pointwise
product agree: `(λ₁ λ₂)^η (η w) = λ₁(w) λ₂(w)` (Lemma `lem:hash`(i), lamp part). -/
theorem hashLamp_append_eval {h : Hp P k} {L₁ L₂ : List (Finset P × Equiv.Perm (Fin 3))}
    (hinj : InjOn k h (L₁ ++ L₂)) {e₀ : Finset P × Equiv.Perm (Fin 3)} (he₀ : e₀ ∈ L₁ ++ L₂) :
    hashLamp k h (L₁ ++ L₂) (evalH k h e₀.1) = lampFun L₁ e₀.1 * lampFun L₂ e₀.1 := by
  rw [hashLamp_eval k hinj he₀]
  unfold lampFun
  rw [List.filter_append, List.map_append, List.prod_append]

end Lamps.Hash

/-! ### Precomposition of hashes with affine generators (proof of Lemma `lem:hash`)

Precomposing an affine hash with a point permutation, a translation or a transvection of
`𝔽₂^P` is again an affine hash, and the induced map on parameters is a bijection; hence a uniform
hash stays uniform, and collision counts are preserved. -/

namespace Lamps.Hash

open Finset
open scoped symmDiff

variable {P : Type*} [Fintype P] [DecidableEq P] (k : ℕ)

/-- Parameters of `η ∘ (v ↦ g v)` for a point permutation `g`. -/
def precPerm (g : Equiv.Perm P) : Hp P k ≃ Hp P k where
  toFun h := (h.1 ∘ g, h.2)
  invFun h := (h.1 ∘ g.symm, h.2)
  left_inv h := by ext y : 2 <;> simp
  right_inv h := by ext y : 2 <;> simp

theorem evalH_precPerm (g : Equiv.Perm P) (h : Hp P k) (v : Finset P) :
    evalH k (precPerm k g h) v = evalH k h (v.map g.toEmbedding) := by
  simp [evalH, precPerm, Finset.sum_map]

/-- Parameters of `η ∘ τ_u`. -/
def precTau (u : Finset P) : Hp P k ≃ Hp P k where
  toFun h := (h.1, h.2 + ∑ y ∈ u, h.1 y)
  invFun h := (h.1, h.2 + ∑ y ∈ u, h.1 y)
  left_inv h := Prod.ext rfl (by simp only; rw [add_assoc, code_add_self, add_zero])
  right_inv h := Prod.ext rfl (by simp only; rw [add_assoc, code_add_self, add_zero])

theorem evalH_precTau (u : Finset P) (h : Hp P k) (v : Finset P) :
    evalH k (precTau k u h) v = evalH k h (v ∆ u) := by
  simp only [evalH, precTau, Equiv.coe_fn_mk, ← sum_add_sum]
  abel

/-- The transvection `E_{y←x}` on configurations: add `y` when `x` is present. -/
def tv (x y : P) (v : Finset P) : Finset P := if x ∈ v then v ∆ {y} else v

theorem update_twice (x y : P) (hxy : x ≠ y) (L : P → Code k) :
    Function.update (Function.update L x (L x + L y)) x
      (Function.update L x (L x + L y) x + Function.update L x (L x + L y) y) = L := by
  funext z
  by_cases hz : z = x
  · subst hz
    simp [Function.update_of_ne (Ne.symm hxy), add_assoc, code_add_self]
  · simp [Function.update_of_ne hz]

/-- Parameters of `η ∘ E_{y←x}`, `x ≠ y`. -/
def precTv (x y : P) (hxy : x ≠ y) : Hp P k ≃ Hp P k where
  toFun h := (Function.update h.1 x (h.1 x + h.1 y), h.2)
  invFun h := (Function.update h.1 x (h.1 x + h.1 y), h.2)
  left_inv h := Prod.ext (update_twice k x y hxy h.1) rfl
  right_inv h := Prod.ext (update_twice k x y hxy h.1) rfl

theorem evalH_precTv (x y : P) (hxy : x ≠ y) (h : Hp P k) (v : Finset P) :
    evalH k (precTv k x y hxy h) v = evalH k h (tv x y v) := by
  have key : ∑ z ∈ v, Function.update h.1 x (h.1 x + h.1 y) z =
      ∑ z ∈ v, h.1 z + (if x ∈ v then h.1 y else 0) := by
    by_cases hx : x ∈ v
    · rw [← Finset.add_sum_erase v _ hx, ← Finset.add_sum_erase v _ hx, ite_eq_left_of_eq_true _ _ (eq_true hx),
        Function.update_self]
      have : ∑ z ∈ v.erase x, Function.update h.1 x (h.1 x + h.1 y) z = ∑ z ∈ v.erase x, h.1 z :=
        Finset.sum_congr rfl fun z hz => Function.update_of_ne (Finset.ne_of_mem_erase hz) _ _
      rw [this, add_right_comm]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hx), add_zero]
      exact Finset.sum_congr rfl fun z hz =>
        Function.update_of_ne (fun hzx : z = x => hx (hzx ▸ hz)) _ _
  simp only [evalH, precTv, Equiv.coe_fn_mk, key, tv]
  split_ifs
  · rw [← sum_add_sum, Finset.sum_singleton]
  · rw [add_zero]

end Lamps.Hash
