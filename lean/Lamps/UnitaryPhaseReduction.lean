import Lamps.UnitaryPhaseFourier

/-!
# Reduction of `UnitaryPhaseRobust` to three analytic inputs

* `SharpPairEntropy`: `(u+w) ln 2 - (√u - √w)² ≤ η(u) + η(w) - η(u+w)` (the paper's
  `1 - h₂(t) ≤ (1 - 2√(t(1-t)))/ln 2`);
* `UnitaryEntropyBound`: `H(p) ≤ log₂ D + ∑ᵢ χ(aᵢ)` (Fourier state, SSA, single twirls, and the
  projection estimate `âᵢ² ≤ aᵢ`);
* `UnitaryBhatProj`: `b̂ᵢ² ≤ bᵢ` (projection estimate).
Proved here: the sharp chain-rule estimate and the assembly, using the exact marginal and the
Bhattacharyya bound of `UnitaryPhaseFourier`.
-/

namespace Lamps

open Finset Matrix Houghton

/-- The sharp two-point entropy inequality. -/
def SharpPairEntropy : Prop :=
  ∀ u w : ℝ, 0 ≤ u → 0 ≤ w →
    Real.log 2 * (u + w) - (u + w - 2 * (Real.sqrt u * Real.sqrt w)) ≤ ent u + ent w - ent (u + w)

lemma triple_bound_sharp (hH : SharpPairEntropy) (m u w : ℝ) (hm : 0 ≤ m) (hu : 0 ≤ u)
    (hw : 0 ≤ w) :
    Real.log 2 * (u + w) - (u + w - 2 * (Real.sqrt u * Real.sqrt w)) ≤
      ent m + ent u + ent w - ent (m + u + w) := by
  have h1 := hH u w hu hw
  have h2 := ent_add_le hm (add_nonneg hu hw)
  rw [← add_assoc] at h2
  linarith

theorem Ent_ge_sharp (hH : SharpPairEntropy) : ∀ (n : ℕ) (p : (Fin n → Fin 3) → ℝ), (∀ z, 0 ≤ p z) →
    ∑ i, (Real.log 2 * sAt i p - dAt i p) ≤ Ent p
  | 0, p, _ => by simp [Ent]
  | n + 1, p, hp => by
    let q : Fin 3 → (Fin n → Fin 3) → ℝ := fun a z' => p (Fin.cons a z')
    have hq0 : ∀ a z', 0 ≤ q a z' := fun a z' => hp _
    let m : Fin 3 → ℝ := fun a => ∑ z', q a z'
    have hm0 : ∀ a, 0 ≤ m a := fun a => sum_nonneg (fun z' _ => hq0 a z')
    have ih : ∀ a, ∑ i, (Real.log 2 * sAt i (q a) - dAt i (q a)) ≤ Ent (q a) :=
      fun a => Ent_ge_sharp hH n (q a) (hq0 a)
    -- decomposition of the entropy
    have hEnt : Ent p = ∑ a, Ent (q a) +
        (ent (m 0) + ent (m 1) + ent (m 2) - ent (m 0 + m 1 + m 2)) := by
      simp only [Ent]
      rw [sum_cons3 (fun z => ent (p z)), sum_cons3 (fun z => p z)]
      simp only [Fin.sum_univ_three, sum_sub_distrib]
      ring
    -- coordinate `0`
    have hs0 : sAt 0 p = m 1 + m 2 := by
      simp only [sAt]
      rw [sum_cons3]
      simp [Fin.sum_univ_three, m, q]
    have hd0 : dAt 0 p = m 1 + m 2 - 2 * ∑ z', Real.sqrt (q 1 z' * q 2 z') := by
      have fl1 : fl 1 = 2 := rfl
      have fl2 : fl 2 = 1 := rfl
      have e : ∀ z' : Fin n → Fin 3, Real.sqrt (p (Fin.cons 2 z') * p (Fin.cons 1 z')) =
          Real.sqrt (p (Fin.cons 1 z') * p (Fin.cons 2 z')) := fun z' => by rw [mul_comm]
      simp only [dAt]
      rw [sum_cons3, Fin.sum_univ_three]
      simp [flipAt_zero_cons, fl1, fl2, sum_sub_distrib, m, q, e]
      ring
    have hcs : ∑ z', Real.sqrt (q 1 z' * q 2 z') ≤ Real.sqrt (m 1) * Real.sqrt (m 2) := by
      calc ∑ z', Real.sqrt (q 1 z' * q 2 z') = ∑ z', Real.sqrt (q 1 z') * Real.sqrt (q 2 z') :=
            sum_congr rfl (fun z' _ => Real.sqrt_mul (hq0 1 z') _)
        _ ≤ _ := Real.sum_sqrt_mul_sqrt_le univ (hq0 1) (hq0 2)
    have hT0 : Real.log 2 * sAt 0 p - dAt 0 p ≤
        ent (m 0) + ent (m 1) + ent (m 2) - ent (m 0 + m 1 + m 2) := by
      have := triple_bound_sharp hH (m 0) (m 1) (m 2) (hm0 0) (hm0 1) (hm0 2)
      rw [hs0, hd0]
      linarith
    -- the other coordinates
    have hsucc : ∀ i : Fin n, Real.log 2 * sAt i.succ p - dAt i.succ p =
        ∑ a, (Real.log 2 * sAt i (q a) - dAt i (q a)) := by
      intro i
      have hs : sAt i.succ p = ∑ a, sAt i (q a) := by
        simp only [sAt]
        rw [sum_cons3]
        simp [q]
      have hd : dAt i.succ p = ∑ a, dAt i (q a) := by
        simp only [dAt]
        rw [sum_cons3]
        simp [q, flipAt_succ_cons]
      rw [hs, hd, mul_sum, ← sum_sub_distrib]
    rw [Fin.sum_univ_succ, hEnt]
    simp only [hsucc]
    rw [sum_comm]
    have := sum_le_sum (fun a (_ : a ∈ univ) => ih a)
    linarith


section Assembly

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {N : ℕ}

/-- `aᵢ = (4/3) ∑_{j>i} κ(cᵢ,cⱼ)²`. -/
noncomputable def aCoef (c : Fin N → Matrix Ω Ω ℂ) (i : Fin N) : ℝ :=
  4 / 3 * ∑ j ∈ univ.filter (i < ·), ud (c i * c j) (c j * c i) ^ 2

/-- `bᵢ = (4/3) ∑_{j≠i} κ(xᵢ,cⱼ)²`. -/
noncomputable def bCoef (c x : Fin N → Matrix Ω Ω ℂ) (i : Fin N) : ℝ :=
  4 / 3 * ∑ j ∈ univ.filter (· ≠ i), ud (x i * c j) (c j * x i) ^ 2

end Assembly

/-- The entropy bound for the sector distribution (Fourier state, SSA for the commuting twirls,
single-twirl bound with weight `≤ min(2âᵢ²/3, 2/3)`, and `âᵢ² ≤ aᵢ` by `lem:projections`). -/
def UnitaryEntropyBound : Prop :=
  ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω] (N : ℕ) (c : Fin N → Matrix Ω Ω ℂ),
    (∀ i, IsU (c i)) → (∀ i, c i ^ 3 = 1) → 0 < Fintype.card Ω →
    (∑ z, ent (pSecU c z)) / Real.log 2 ≤ Real.logb 2 (Fintype.card Ω) + ∑ i, chi (aCoef c i)

/-- The projection estimate `b̂ᵢ² ≤ bᵢ` (`lem:projections` for the maps `B_j`). -/
def UnitaryBhatProj : Prop :=
  ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω] (N : ℕ) (c x : Fin N → Matrix Ω Ω ℂ),
    (∀ i, IsU (c i)) → (∀ i, IsU (x i)) → (∀ i, c i ^ 3 = 1) → (∀ i, x i * x i = 1) →
    (∀ i, x i * c i * x i = (c i)ᴴ) → ∀ i, bhat2 c (x i) i ≤ bCoef c x i

lemma ud_empty {Ω : Type} [Fintype Ω] [DecidableEq Ω] (h : Fintype.card Ω = 0)
    (X Y : Matrix Ω Ω ℂ) : ud X Y = 0 := by
  simp [ud, uhs, h]

/-- **Reduction**: `UnitaryPhaseRobust` from the three analytic inputs. -/
theorem unitaryPhaseRobust_of (hH : SharpPairEntropy) (hE : UnitaryEntropyBound)
    (hB : UnitaryBhatProj) : UnitaryPhaseRobust := by
  intro Ω _ _ N c x hc hx hc3 hx2 hxc
  have hl2 := log_two_gt_half
  have hl2pos : 0 < Real.log 2 := by linarith
  have ha0 : ∀ i, 0 ≤ aCoef c i := fun i => by
    unfold aCoef; have := sum_nonneg fun j (_ : j ∈ univ.filter (i < ·)) =>
      sq_nonneg (ud (c i * c j) (c j * c i)); positivity
  have hb0 : ∀ i, 0 ≤ bCoef c x i := fun i => by
    unfold bCoef; have := sum_nonneg fun j (_ : j ∈ univ.filter (· ≠ i)) =>
      sq_nonneg (ud (x i * c j) (c j * x i)); positivity
  rcases Nat.eq_zero_or_pos (Fintype.card Ω) with hD0 | hD
  · -- trivial dimension
    have hz : ∀ i, ((ud (c i) 1) ^ 2 - 4 / 3 * ∑ j ∈ univ.filter (i < ·),
        ud (c i * c j) (c j * c i) ^ 2) / 3
        - (4 / 3 * ∑ j ∈ univ.filter (· ≠ i), ud (x i * c j) (c j * x i) ^ 2) / (2 * Real.log 2)
        - chi (4 / 3 * ∑ j ∈ univ.filter (i < ·), ud (c i * c j) (c j * c i) ^ 2) = 0 := by
      intro i
      simp only [ud_empty hD0]
      have hm : min (2 / 3 * (4 / 3 * ∑ j ∈ univ.filter (i < ·), (0 : ℝ) ^ 2)) (2 / 3) = 0 := by
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sum_const_zero,
          mul_zero]
        exact min_eq_left (by norm_num)
      simp only [chi, hm, Houghton.h2]
      simp
    rw [sum_eq_zero fun i _ => hz i, hD0]
    simp
  set p := pSecU c
  have hp0 : ∀ z, 0 ≤ p z := pSecU_nonneg c
  have hp1 : ∑ z, p z = 1 := sum_pSecU c hc hD
  have main := Ent_ge_sharp hH N p hp0
  have hEnt : Ent p = ∑ z, ent (p z) := by simp [Ent, hp1, ent_one]
  have hs : ∀ i, sAt i p = ud (c i) 1 ^ 2 / 3 := by
    intro i
    have := marginal_pSecU c hc hc3 hD i
    rw [← this]
    simp only [sAt, sum_filter, ne_eq, ite_not]
    rfl
  have hd : ∀ i, dAt i p ≤ bCoef c x i / 2 := by
    intro i
    have e : ∀ z, (if z i = 0 then 0 else p z - Real.sqrt (p z * p (flipAt i z))) =
        p z - Real.sqrt (p z * p (flipAt i z)) := by
      intro z
      split_ifs with hz
      · have hf : flipAt i z = z := by
          simp only [flipAt, hz]
          rw [show fl 0 = 0 from rfl, ← hz, Function.update_eq_self]
        rw [hf, Real.sqrt_mul_self (hp0 z), sub_self]
      · rfl
    have hbt := bhatt_pSecU c hc (x i) (hx i) hD i
    have hbb := hB Ω N c x hc hx hc3 hx2 hxc i
    simp only [dAt, e, sum_sub_distrib, hp1]
    linarith
  have hEB := hE Ω N c hc hc3 hD
  have hsum : ∑ i, (Real.log 2 * (ud (c i) 1 ^ 2 / 3) - bCoef c x i / 2) ≤ ∑ z, ent (p z) := by
    rw [← hEnt]
    refine le_trans ?_ main
    refine sum_le_sum fun i _ => ?_
    rw [hs i]
    linarith [hd i]
  rw [div_le_iff₀ hl2pos] at hEB
  have key : ∑ i, (ud (c i) 1 ^ 2 / 3 - bCoef c x i / (2 * Real.log 2)) ≤
      Real.logb 2 (Fintype.card Ω) + ∑ i, chi (aCoef c i) := by
    have e : ∑ i, (Real.log 2 * (ud (c i) 1 ^ 2 / 3) - bCoef c x i / 2) =
        Real.log 2 * ∑ i, (ud (c i) 1 ^ 2 / 3 - bCoef c x i / (2 * Real.log 2)) := by
      rw [mul_sum]
      refine sum_congr rfl fun i _ => ?_
      field_simp
    rw [e] at hsum
    have := hsum.trans hEB
    rw [mul_comm] at this
    nlinarith
  have hle : ∑ i, (((ud (c i) 1) ^ 2 - aCoef c i) / 3 - bCoef c x i / (2 * Real.log 2) -
      chi (aCoef c i)) ≤ ∑ i, (ud (c i) 1 ^ 2 / 3 - bCoef c x i / (2 * Real.log 2)) -
        ∑ i, chi (aCoef c i) := by
    rw [← sum_sub_distrib]
    refine sum_le_sum fun i _ => ?_
    have := ha0 i
    linarith
  have hfin := hle.trans (show ∑ i, (ud (c i) 1 ^ 2 / 3 - bCoef c x i / (2 * Real.log 2)) -
      ∑ i, chi (aCoef c i) ≤ Real.logb 2 (Fintype.card Ω) by linarith [key])
  simpa only [aCoef, bCoef] using hfin

/-- `UnitaryPhaseRobust` with `bᵢ/ln 2` in place of `bᵢ/(2 ln 2)` (what the factor-2 entropy
estimate `Houghton.Ent_ge` gives; the margin of `thm:criterion` still closes: `7941 ≤ 8333`). -/
def UnitaryPhaseRobustWeak : Prop :=
  ∀ (Ω : Type) [Fintype Ω] [DecidableEq Ω] (N : ℕ) (c x : Fin N → Matrix Ω Ω ℂ),
    (∀ i, IsU (c i)) → (∀ i, IsU (x i)) → (∀ i, c i ^ 3 = 1) → (∀ i, x i * x i = 1) →
    (∀ i, x i * c i * x i = (c i)ᴴ) →
    ∑ i, (((ud (c i) 1) ^ 2 - 4 / 3 * ∑ j ∈ univ.filter (i < ·), ud (c i * c j) (c j * c i) ^ 2) / 3
      - (4 / 3 * ∑ j ∈ univ.filter (· ≠ i), ud (x i * c j) (c j * x i) ^ 2) / (Real.log 2)
      - chi (4 / 3 * ∑ j ∈ univ.filter (i < ·), ud (c i * c j) (c j * c i) ^ 2))
      ≤ Real.logb 2 (Fintype.card Ω)

/-- **Reduction (weak constant)**: `UnitaryPhaseRobustWeak` from the two matrix inputs only. -/
theorem unitaryPhaseRobustWeak_of (hE : UnitaryEntropyBound) (hB : UnitaryBhatProj) :
    UnitaryPhaseRobustWeak := by
  intro Ω _ _ N c x hc hx hc3 hx2 hxc
  have hl2 := log_two_gt_half
  have hl2pos : 0 < Real.log 2 := by linarith
  have ha0 : ∀ i, 0 ≤ aCoef c i := fun i => by
    unfold aCoef; have := sum_nonneg fun j (_ : j ∈ univ.filter (i < ·)) =>
      sq_nonneg (ud (c i * c j) (c j * c i)); positivity
  have hb0 : ∀ i, 0 ≤ bCoef c x i := fun i => by
    unfold bCoef; have := sum_nonneg fun j (_ : j ∈ univ.filter (· ≠ i)) =>
      sq_nonneg (ud (x i * c j) (c j * x i)); positivity
  rcases Nat.eq_zero_or_pos (Fintype.card Ω) with hD0 | hD
  · -- trivial dimension
    have hz : ∀ i, ((ud (c i) 1) ^ 2 - 4 / 3 * ∑ j ∈ univ.filter (i < ·),
        ud (c i * c j) (c j * c i) ^ 2) / 3
        - (4 / 3 * ∑ j ∈ univ.filter (· ≠ i), ud (x i * c j) (c j * x i) ^ 2) / (Real.log 2)
        - chi (4 / 3 * ∑ j ∈ univ.filter (i < ·), ud (c i * c j) (c j * c i) ^ 2) = 0 := by
      intro i
      simp only [ud_empty hD0]
      have hm : min (2 / 3 * (4 / 3 * ∑ j ∈ univ.filter (i < ·), (0 : ℝ) ^ 2)) (2 / 3) = 0 := by
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sum_const_zero,
          mul_zero]
        exact min_eq_left (by norm_num)
      simp only [chi, hm, Houghton.h2]
      simp
    rw [sum_eq_zero fun i _ => hz i, hD0]
    simp
  set p := pSecU c
  have hp0 : ∀ z, 0 ≤ p z := pSecU_nonneg c
  have hp1 : ∑ z, p z = 1 := sum_pSecU c hc hD
  have main := Ent_ge N p hp0
  have hEnt : Ent p = ∑ z, ent (p z) := by simp [Ent, hp1, ent_one]
  have hs : ∀ i, sAt i p = ud (c i) 1 ^ 2 / 3 := by
    intro i
    have := marginal_pSecU c hc hc3 hD i
    rw [← this]
    simp only [sAt, sum_filter, ne_eq, ite_not]
    rfl
  have hd : ∀ i, dAt i p ≤ bCoef c x i / 2 := by
    intro i
    have e : ∀ z, (if z i = 0 then 0 else p z - Real.sqrt (p z * p (flipAt i z))) =
        p z - Real.sqrt (p z * p (flipAt i z)) := by
      intro z
      split_ifs with hz
      · have hf : flipAt i z = z := by
          simp only [flipAt, hz]
          rw [show fl 0 = 0 from rfl, ← hz, Function.update_eq_self]
        rw [hf, Real.sqrt_mul_self (hp0 z), sub_self]
      · rfl
    have hbt := bhatt_pSecU c hc (x i) (hx i) hD i
    have hbb := hB Ω N c x hc hx hc3 hx2 hxc i
    simp only [dAt, e, sum_sub_distrib, hp1]
    linarith
  have hEB := hE Ω N c hc hc3 hD
  have hsum : ∑ i, (Real.log 2 * (ud (c i) 1 ^ 2 / 3) - bCoef c x i) ≤ ∑ z, ent (p z) := by
    rw [← hEnt]
    refine le_trans ?_ main
    refine sum_le_sum fun i _ => ?_
    rw [hs i]
    linarith [hd i, hb0 i]
  rw [div_le_iff₀ hl2pos] at hEB
  have key : ∑ i, (ud (c i) 1 ^ 2 / 3 - bCoef c x i / (Real.log 2)) ≤
      Real.logb 2 (Fintype.card Ω) + ∑ i, chi (aCoef c i) := by
    have e : ∑ i, (Real.log 2 * (ud (c i) 1 ^ 2 / 3) - bCoef c x i) =
        Real.log 2 * ∑ i, (ud (c i) 1 ^ 2 / 3 - bCoef c x i / (Real.log 2)) := by
      rw [mul_sum]
      refine sum_congr rfl fun i _ => ?_
      field_simp
    rw [e] at hsum
    have := hsum.trans hEB
    rw [mul_comm] at this
    nlinarith
  have hle : ∑ i, (((ud (c i) 1) ^ 2 - aCoef c i) / 3 - bCoef c x i / (Real.log 2) -
      chi (aCoef c i)) ≤ ∑ i, (ud (c i) 1 ^ 2 / 3 - bCoef c x i / (Real.log 2)) -
        ∑ i, chi (aCoef c i) := by
    rw [← sum_sub_distrib]
    refine sum_le_sum fun i _ => ?_
    have := ha0 i
    linarith
  have hfin := hle.trans (show ∑ i, (ud (c i) 1 ^ 2 / 3 - bCoef c x i / (Real.log 2)) -
      ∑ i, chi (aCoef c i) ≤ Real.logb 2 (Fintype.card Ω) by linarith [key])
  simpa only [aCoef, bCoef] using hfin

end Lamps
