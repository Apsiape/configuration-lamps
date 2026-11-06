import Lamps.CriterionSweep
import Houghton.Analysis.SSAFinal

/-!
# Towards `PermSweepBound`: the sector-entropy upper bound under ordered (suffix) errors

Houghton's sector chain (`Houghton/Analysis/Sector*.lean`) for the state `ρ̂` built from
`fprod c g = c₀^{g₀} ⋯ c_{N-1}^{g_{N-1}}` (`g ∈ Z₃^N`) uses the commutation hypotheses in two places:

1. the single-twirl leakage (`weight_bound`), through
   `dH (fprod c g * c_i^t) (fprod c (g + t e_i)) = dH (c_i^t S) (S c_i^t)`, `S` the ordered suffix;
2. the flip symmetry `p(χ) ≈ p(flip_i χ)` (`bhatt_pSec`), through `x_i fprod c g x_i ≈
   fprod c (flip_i g)`, i.e. `x_i` commuting with the whole product (prefix **and** suffix).

Use 1 needs only suffix commutation, so the **upper bound** `H(p)/ln 2 ≤ log₂ D + N/100` holds under the
ordered-error hypothesis of Theorem `thm:sweep` (`sweep_sectorEntropy` below; all of (A), (B), (C) and
strong subadditivity are reused). Use 2 does not carry over: the sweep hypothesis gives no control of
`x_i` against the prefix. The paper instead works on `ℓ²(S₃^N)` with the right regular action, where
`R(x_i)` flips the `c_i`-label and `R(h_i) W ≈ W u_i(h)` needs only suffix commutation; formalizing
that state is the remaining gap (see the report).
-/

namespace Lamps

open Finset Equiv
open Houghton (dH)

/-- The ordered prefix `U_{<i}`. -/
def preW {M : Type*} [Monoid M] {N : ℕ} (i : Fin N) (U : Fin N → M) : M :=
  (((List.finRange N).filter fun j => j < i).map U).prod

theorem finRange_split : ∀ {N : ℕ} (i : Fin N),
    List.finRange N = (List.finRange N).filter (fun j => j < i) ++
      i :: (List.finRange N).filter (fun j => i < j)
  | 0, i => i.elim0
  | n + 1, i => by
    cases i using Fin.cases with
    | zero =>
      rw [List.finRange_succ]
      simp only [List.filter_cons, List.filter_map, Function.comp_def, Fin.succ_pos,
        decide_true, lt_self_iff_false, decide_false, Fin.not_lt_zero, List.filter_false,
        List.map_nil, List.nil_append, List.filter_true, Bool.cond_false, Bool.cond_true]
      rfl
    | succ i =>
      have ih := finRange_split i
      rw [List.finRange_succ]
      simp only [List.filter_cons, List.filter_map, Function.comp_def, Fin.succ_lt_succ_iff,
        Fin.succ_pos, decide_true, Fin.not_lt_zero, decide_false, Bool.cond_true, Bool.cond_false,
        List.cons_append, List.cons.injEq, true_and]
      conv_lhs => rw [ih]
      simp

theorem prod_ofFn_split {M : Type*} [Monoid M] {N : ℕ} (U : Fin N → M) (i : Fin N) :
    (List.ofFn U).prod = preW i U * U i * sufW i U := by
  rw [List.ofFn_eq_map, finRange_split i, List.map_append, List.map_cons, List.prod_append,
    List.prod_cons, preW, sufW, mul_assoc]

theorem preW_update {M : Type*} [Monoid M] {N : ℕ} (U : Fin N → M) (i : Fin N) (a : M) :
    preW i (Function.update U i a) = preW i U := by
  unfold preW; congr 1
  apply List.map_congr_left
  intro j hj
  have : j < i := by simpa using (List.mem_filter.mp hj).2
  rw [Function.update_of_ne (ne_of_lt this)]

theorem sufW_update {M : Type*} [Monoid M] {N : ℕ} (U : Fin N → M) (i : Fin N) (a : M) :
    sufW i (Function.update U i a) = sufW i U := by
  unfold sufW; congr 1
  apply List.map_congr_left
  intro j hj
  have : i < j := by simpa using (List.mem_filter.mp hj).2
  rw [Function.update_of_ne (ne_of_gt this)]

section Chain

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {N : ℕ}

/-- The twirl input of Houghton's chain is exactly the ordered (suffix) error. -/
theorem fprod_shift_eq (c : Fin N → Perm Ω) (hc : ∀ i, c i ^ 3 = 1) (g : Fin N → Fin 3)
    (i : Fin N) (t : Fin 3) :
    dH (Houghton.fprod c g * c i ^ t.val) (Houghton.fprod c (g + Pi.single i t)) =
      dH (c i ^ t.val * sufW i (fun j => c j ^ (g j).val))
        (sufW i (fun j => c j ^ (g j).val) * c i ^ t.val) := by
  set U : Fin N → Perm Ω := fun j => c j ^ (g j).val
  have hU : ∀ j, c j ^ ((g + Pi.single i t : Fin N → Fin 3) j).val = Function.update U i (c i ^ (g i + t).val) j := by
    intro j
    by_cases hj : j = i
    · subst hj; simp [U]
    · simp [U, hj]
  have e1 : Houghton.fprod c g = preW i U * U i * sufW i U := prod_ofFn_split U i
  have e2 : Houghton.fprod c (g + Pi.single i t) =
      preW i U * c i ^ (g i + t).val * sufW i U := by
    unfold Houghton.fprod
    rw [show (fun j => c j ^ ((g + Pi.single i t : Fin N → Fin 3) j).val) =
      Function.update U i (c i ^ (g i + t).val) from funext hU, prod_ofFn_split, preW_update,
      sufW_update, Function.update_self]
  have hpow : c i ^ (g i + t).val = c i ^ (g i).val * c i ^ t.val :=
    Houghton.pow_val_add _ (hc i) _ _
  rw [e1, e2, hpow, mul_assoc, mul_assoc, mul_assoc, Houghton.dH_mul_left, mul_assoc,
    Houghton.dH_mul_left, Houghton.dH_comm]

/-- **Sector-entropy upper bound under ordered errors**: if every `c_i^t` commutes with every
ordered suffix `c_{i+1}^{g_{i+1}} ⋯ c_{N-1}^{g_{N-1}}` up to `1/10000`, then
`H(p)/ln 2 ≤ log₂ D + N/100` for Houghton's sector distribution `p = pSec c`. -/
theorem sweep_sectorEntropy (c : Fin N → Perm Ω) (h1 : ∀ i, c i ^ 3 = 1)
    (hD : 0 < Fintype.card Ω)
    (hsw : ∀ i (t : Fin 3) (g : Fin N → Fin 3),
      dH (c i ^ t.val * sufW i (fun j => c j ^ (g j).val))
        (sufW i (fun j => c j ^ (g j).val) * c i ^ t.val) ≤ 1 / 10000) :
    (∑ z, Houghton.ent (Houghton.pSec c z)) / Real.log 2 ≤
      Real.logb 2 (Fintype.card Ω) + N / 100 := by
  have hl2 := Houghton.log_two_gt_half
  have hl2pos : 0 < Real.log 2 := by linarith
  -- (B) under ordered errors
  have hB : ∀ i, Houghton.vN (Houghton.pinch (Houghton.labelProj i) (Houghton.rhoSec c)) ≤
      Real.log (Fintype.card Ω) + 1 / 200 := by
    intro i
    have hε : ∀ t : Fin 3, ∀ g, dH (Houghton.fprod c g * c i ^ t.val)
        (Houghton.fprod c (g + Pi.single i t)) ≤ 1 / 10000 := by
      intro t g; rw [fprod_shift_eq c h1 g i t]; exact hsw i t g
    have hw := Houghton.weight_bound c hD i (1 / 10000) hε (by norm_num)
    rw [Houghton.sigma_eq c hD i]
    have hb := Houghton.genTwirlBound ((Fin N → Fin 3) × Ω) (Houghton.Pproj c) (Houghton.Zt i 1)
      (Houghton.Zt i 2) (Fintype.card Ω) (1 / 7500) (Houghton.Pproj_herm c)
      (Houghton.Pproj_idem c) (Houghton.Pproj_trace c) hD (Houghton.Zt_unitary i 1)
      (Houghton.Zt_unitary i 2) (by linarith) (by norm_num)
    have hn := Houghton.numeric_twirl
    linarith
  set L := Real.log (Fintype.card Ω) with hL
  have hSSA := Houghton.qit_commutingPinchingSSA ((Fin N → Fin 3) × Ω) (Fin 3) N
    (fun i => Houghton.labelProj i) (fun k => Houghton.labelProj_family k)
    (fun k l _ a b => Houghton.labelProj_comm k l a b) (Houghton.rhoSec c)
    (Houghton.rhoSec_density c hD)
  have hA' := Houghton.subStateEntropy Ω N c hD
  have hC' := Houghton.subSectorEntropy Ω N c hD
  have hsumB : ∑ k : Fin N, Houghton.vN (Houghton.pinch (Houghton.labelProj k)
      (Houghton.rhoSec c)) ≤ N * (L + 1 / 200) := by
    calc ∑ k : Fin N, Houghton.vN (Houghton.pinch (Houghton.labelProj k) (Houghton.rhoSec c))
        ≤ ∑ _k : Fin N, (L + 1 / 200) := sum_le_sum fun k _ => hB k
      _ = N * (L + 1 / 200) := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hent : ∑ z, Houghton.ent (Houghton.pSec c z) ≤ L + N / 200 := by
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      have h0 : ∑ z, Houghton.ent (Houghton.pSec c z) = 0 := by
        rw [Fintype.sum_unique]
        have := Houghton.sum_pSec c hD
        rw [Fintype.sum_unique] at this
        rw [this, Houghton.ent_one]
      rw [h0, Nat.cast_zero, zero_div, add_zero]
      exact Real.log_nonneg (by exact_mod_cast hD)
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have : Houghton.vN (Houghton.pinchAll (fun i => Houghton.labelProj i) (Houghton.rhoSec c)) ≤
        L + N / 200 := by
      have h' : ((N : ℝ) - 1) * L ≤ ((N : ℝ) - 1) * Houghton.vN (Houghton.rhoSec c) :=
        mul_le_mul_of_nonneg_left hA' (by linarith)
      nlinarith
    linarith
  rw [div_le_iff₀ hl2pos, Real.logb, add_mul, div_mul_cancel₀ _ hl2pos.ne']
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  nlinarith [mul_nonneg hN0 (le_of_lt (sub_pos.mpr hl2))]

/-- The positions of `1, c, c²` among the normal forms `nfG x (x c)`. -/
def cpos : Fin 3 → Fin 6 := ![0, 3, 4]

omit [Fintype Ω] [DecidableEq Ω] in
theorem nfG_cpos (x c : Perm Ω) (hx : x ^ 2 = 1) (hc : c ^ 3 = 1) (hxc : x * c * x = c⁻¹)
    (t : Fin 3) : nfG x (x * c) (cpos t) = c ^ t.val := by
  have hxx : x * x = 1 := by rw [← pow_two, hx]
  fin_cases t
  · simp [nfG, cpos]
  · simp [nfG, cpos, ← mul_assoc, hxx]
  · show x * c * x = c ^ 2
    rw [hxc, eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, hc]

/-- Under the hypotheses of `PermSweepBound`, the sector-entropy upper bound holds. -/
theorem sweep_sectorEntropy_of (x c : Fin N → Perm Ω) (h1 : ∀ i, c i ^ 3 = 1)
    (h2 : ∀ i, x i ^ 2 = 1) (h3 : ∀ i, x i * c i * x i = (c i)⁻¹) (hD : 0 < Fintype.card Ω)
    (hsw : ∀ i (h : Fin 6) (g : Fin N → Fin 6),
      dH (commG (nfG (x i) (x i * c i) h) (sufW i fun j => nfG (x j) (x j * c j) (g j))) 1 ≤
        1 / 20000) :
    (∑ z, Houghton.ent (Houghton.pSec c z)) / Real.log 2 ≤
      Real.logb 2 (Fintype.card Ω) + N / 100 := by
  refine sweep_sectorEntropy c h1 hD fun i t g => ?_
  have hn : ∀ j (s : Fin 3), nfG (x j) (x j * c j) (cpos s) = c j ^ s.val :=
    fun j s => nfG_cpos _ _ (h2 j) (h1 j) (h3 j) s
  have h := hsw i (cpos t) (fun j => cpos (g j))
  simp only [hn] at h
  rw [Houghton.dH_comm_eq]
  unfold commG at h
  linarith

end Chain

end Lamps
