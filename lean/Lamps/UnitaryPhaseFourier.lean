import Lamps.UnitaryCriterion

/-!
# Fourier picture for unitary local `ℤ/3` actions (towards `UnitaryPhaseRobust`)

For unitaries `c_i` with `c_i³ = 1`, `f(g) = c_1^{g_1} ⋯ c_N^{g_N}`, `M_χ = ∑_g ω^{-χ·g} f(g)` and the
sector distribution `p(χ) = ‖M_χ‖²_HS/(9^N D)`.  Proved here: `∑ p = 1` and the exact marginal
`Pr(χ_i ≠ 0) = ‖c_i - I‖₂²/3`.
-/

namespace Lamps

open Finset Matrix ComplexConjugate

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {N : ℕ}

lemma hip_eq_trace (A B : Matrix Ω Ω ℂ) : Houghton.hip A B = (Aᴴ * B).trace := by
  simp only [Houghton.hip, Matrix.trace, Matrix.diag, mul_apply, conjTranspose_apply]
  rw [sum_comm]
  rfl

lemma IsU.pow {U : Matrix Ω Ω ℂ} (hU : IsU U) : ∀ n : ℕ, IsU (U ^ n)
  | 0 => by rw [pow_zero]; exact IsU.one
  | n + 1 => by rw [pow_succ]; exact (hU.pow n).mul hU

lemma isU_ofFn_prod : ∀ {n : ℕ} (h : Fin n → Matrix Ω Ω ℂ), (∀ j, IsU (h j)) →
    IsU (List.ofFn h).prod
  | 0, _, _ => by simp [IsU.one]
  | n + 1, h, hh => by
    rw [List.ofFn_succ, List.prod_cons]
    exact (hh 0).mul (isU_ofFn_prod (fun j => h j.succ) fun j => hh j.succ)

lemma ofFn_update_prodU : ∀ {n : ℕ} (h : Fin n → Matrix Ω Ω ℂ), (∀ j, IsU (h j)) →
    ∀ i : Fin n, ∃ L R : Matrix Ω Ω ℂ, IsU L ∧ IsU R ∧
      ∀ a, (List.ofFn (Function.update h i a)).prod = L * a * R
  | 0, _, _, i => i.elim0
  | n + 1, h, hh, i => by
    cases i using Fin.cases with
    | zero =>
      refine ⟨1, (List.ofFn fun j : Fin n => h j.succ).prod, IsU.one,
        isU_ofFn_prod _ fun j => hh j.succ, fun a => ?_⟩
      have e0 : (fun j : Fin n => Function.update h 0 a j.succ) = fun j => h j.succ :=
        funext fun j => Function.update_of_ne (Fin.succ_ne_zero j) _ _
      rw [List.ofFn_succ, List.prod_cons, Function.update_self, e0, Matrix.one_mul]
    | succ i =>
      obtain ⟨L, R, hL, hR, hLR⟩ := ofFn_update_prodU (fun j : Fin n => h j.succ)
        (fun j => hh j.succ) i
      refine ⟨h 0 * L, R, (hh 0).mul hL, hR, fun a => ?_⟩
      rw [List.ofFn_succ, List.prod_cons, Function.update_of_ne (Fin.succ_ne_zero i).symm]
      have e : (fun j : Fin n => Function.update h i.succ a j.succ) =
          Function.update (fun j => h j.succ) i a :=
        Function.update_comp_eq_of_injective h (Fin.succ_injective n) i a
      rw [e, hLR]
      simp only [Matrix.mul_assoc]

/-- `f(g) = c_1^{g_1} ⋯ c_N^{g_N}`. -/
def fprodU (c : Fin N → Matrix Ω Ω ℂ) (g : Fin N → Fin 3) : Matrix Ω Ω ℂ :=
  (List.ofFn fun j => c j ^ (g j).val).prod

lemma isU_fprodU (c : Fin N → Matrix Ω Ω ℂ) (hc : ∀ i, IsU (c i)) (g : Fin N → Fin 3) :
    IsU (fprodU c g) :=
  isU_ofFn_prod _ fun j => (hc j).pow _

lemma mpow_mod3 (c : Matrix Ω Ω ℂ) (h : c ^ 3 = 1) (n : ℕ) : c ^ (n % 3) = c ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 3]
  rw [pow_add, pow_mul, h, one_pow, Matrix.one_mul]

lemma mpow_val_add (c : Matrix Ω Ω ℂ) (h : c ^ 3 = 1) (a b : Fin 3) :
    c ^ (a + b).val = c ^ a.val * c ^ b.val := by
  rw [Fin.val_add, mpow_mod3 c h, pow_add]

lemma fprodU_update (c : Fin N → Matrix Ω Ω ℂ) (hc : ∀ i, IsU (c i)) (g : Fin N → Fin 3)
    (i : Fin N) : ∃ L R : Matrix Ω Ω ℂ, IsU L ∧ IsU R ∧
      ∀ a : Fin 3, fprodU c (Function.update g i a) = L * c i ^ a.val * R := by
  obtain ⟨L, R, hL, hR, h⟩ :=
    ofFn_update_prodU (fun j => c j ^ (g j).val) (fun j => (hc j).pow _) i
  refine ⟨L, R, hL, hR, fun a => ?_⟩
  rw [← h]
  unfold fprodU
  congr 2
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Function.update_of_ne hj]

/-- `Tr(f(g)* f(g + k e_i)) = Tr(c_i^k)`. -/
lemma trace_fprodU_shift (c : Fin N → Matrix Ω Ω ℂ) (hc : ∀ i, IsU (c i))
    (hc3 : ∀ i, c i ^ 3 = 1) (g : Fin N → Fin 3) (i : Fin N) (k : Fin 3) :
    ((fprodU c g)ᴴ * fprodU c (g + Pi.single i k)).trace = (c i ^ k.val).trace := by
  obtain ⟨L, R, hL, hR, h⟩ := fprodU_update c hc g i
  have hg : fprodU c g = L * c i ^ (g i).val * R := by
    rw [← h]; congr; exact (Function.update_eq_self i g).symm
  have hP := (hc i).pow (g i).val
  rw [Houghton.shift_eq_update, h, hg, mpow_val_add _ (hc3 i)]
  rw [conjTranspose_mul, conjTranspose_mul]
  calc (Rᴴ * ((c i ^ (g i).val)ᴴ * Lᴴ) * (L * (c i ^ (g i).val * c i ^ k.val) * R)).trace
      = (Rᴴ * ((c i ^ (g i).val)ᴴ * (Lᴴ * L) * c i ^ (g i).val) * c i ^ k.val * R).trace := by
        simp only [Matrix.mul_assoc]
    _ = (R * (Rᴴ * c i ^ k.val)).trace := by
        rw [hL.1, Matrix.mul_one, hP.1, Matrix.mul_one, Matrix.trace_mul_comm]
    _ = _ := by rw [← Matrix.mul_assoc, hR.2, Matrix.one_mul]

/-! ### The sector distribution -/

/-- `M_χ = ∑_g ω^{-χ·g} f(g)`. -/
noncomputable def MsecU (c : Fin N → Matrix Ω Ω ℂ) (χ : Fin N → Fin 3) : Ω → Ω → ℂ :=
  Houghton.FT (fun g => fprodU c g) χ

/-- `p(χ) = ‖M_χ‖²/(9^N D)`. -/
noncomputable def pSecU (c : Fin N → Matrix Ω Ω ℂ) (χ : Fin N → Fin 3) : ℝ :=
  Houghton.nsq (MsecU c χ) / (9 ^ N * Fintype.card Ω)

lemma pSecU_nonneg (c : Fin N → Matrix Ω Ω ℂ) (χ : Fin N → Fin 3) : 0 ≤ pSecU c χ :=
  div_nonneg (Houghton.nsq_nonneg _) (by positivity)

lemma nsq_isU {U : Matrix Ω Ω ℂ} (hU : IsU U) : Houghton.nsq U = Fintype.card Ω := by
  have h := nsq_eq_trace U
  rw [hU.2, trace_one] at h
  exact_mod_cast h

lemma hip_isU {U : Matrix Ω Ω ℂ} (hU : IsU U) : Houghton.hip U U = Fintype.card Ω := by
  rw [hip_eq_trace, hU.1, trace_one]

lemma sum_nsq_MsecU (c : Fin N → Matrix Ω Ω ℂ) (hc : ∀ i, IsU (c i)) :
    ∑ χ, Houghton.nsq (MsecU c χ) = 9 ^ N * Fintype.card Ω := by
  have h := Houghton.parseval (fun g => fprodU c g) (fun g => fprodU c g)
  simp only [Houghton.hip_self, hip_isU (isU_fprodU c hc _), sum_const, card_univ,
    Houghton.card_G, nsmul_eq_mul] at h
  have h' : ((∑ χ, Houghton.nsq (MsecU c χ) : ℝ) : ℂ) = ((9 ^ N * Fintype.card Ω : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    simp only [MsecU]
    rw [h]
    push_cast
    rw [show (9 : ℂ) ^ N = 3 ^ N * 3 ^ N by rw [← mul_pow]; norm_num]
    ring
  exact_mod_cast h'

theorem sum_pSecU (c : Fin N → Matrix Ω Ω ℂ) (hc : ∀ i, IsU (c i))
    (hD : 0 < Fintype.card Ω) : ∑ χ, pSecU c χ = 1 := by
  simp only [pSecU, ← sum_div, sum_nsq_MsecU c hc]
  exact div_self (by positivity)

/-- `‖c - I‖₂² = 2 - 2 Re Tr(c)/D` for unitary `c`. -/
lemma ud_one_sq {c : Matrix Ω Ω ℂ} (hc : IsU c) (hD : 0 < Fintype.card Ω) :
    ud c 1 ^ 2 = 2 - 2 * (c.trace).re / Fintype.card Ω := by
  have hDR : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast hD
  have h0 : 0 ≤ Houghton.nsq (c - 1) / Fintype.card Ω := div_nonneg (Houghton.nsq_nonneg _) hDR.le
  have hsq : ud c 1 ^ 2 = Houghton.nsq (c - 1) / Fintype.card Ω := Real.sq_sqrt h0
  rw [hsq]
  have h := nsq_eq_trace (c - 1)
  rw [conjTranspose_sub, conjTranspose_one, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
    hc.2, Matrix.mul_one, Matrix.one_mul, Matrix.one_mul, trace_sub, trace_sub, trace_sub,
    trace_one, trace_conjTranspose] at h
  have hre := congrArg Complex.re h
  rw [Complex.ofReal_re] at hre
  have hre' : Houghton.nsq (c - 1) = 2 * (Fintype.card Ω : ℝ) - 2 * (c.trace).re := by
    refine hre.trans ?_
    simp only [Complex.sub_re, Complex.natCast_re, Complex.star_def, Complex.conj_re]
    ring
  calc Houghton.nsq (c - 1) / (Fintype.card Ω : ℝ)
      = (2 * (Fintype.card Ω : ℝ) - 2 * (c.trace).re) / Fintype.card Ω := by rw [hre']
    _ = 2 - 2 * (c.trace).re / Fintype.card Ω := by field_simp

/-- **Exact marginal**: `Pr(χ_i ≠ 0) = ‖c_i - I‖₂²/3`. -/
theorem marginal_pSecU (c : Fin N → Matrix Ω Ω ℂ) (hc : ∀ i, IsU (c i))
    (hc3 : ∀ i, c i ^ 3 = 1) (hD : 0 < Fintype.card Ω) (i : Fin N) :
    ∑ z ∈ univ.filter (fun z => z i ≠ 0), pSecU c z = ud (c i) 1 ^ 2 / 3 := by
  have hDR : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast hD
  have T : ∀ k : Fin 3, ∑ χ, Houghton.ech (k * χ i) * (Houghton.nsq (MsecU c χ) : ℂ) =
      9 ^ N * (c i ^ k.val).trace := by
    intro k
    have h := Houghton.parseval (fun g => fprodU c g) (fun g => fprodU c (g + Pi.single i k))
    have e1 : ∀ χ, Houghton.ech (k * χ i) * (Houghton.nsq (MsecU c χ) : ℂ) =
        Houghton.hip (Houghton.FT (fun g => fprodU c g) χ)
          (Houghton.FT (fun g => fprodU c (g + Pi.single i k)) χ) := by
      intro χ
      rw [← Houghton.hip_self, MsecU, ← Houghton.hip_smul]
      congr 1
      funext α β
      exact Houghton.FT_shift (fun g => fprodU c g) χ i k α β
    simp only [e1, h, hip_eq_trace, trace_fprodU_shift c hc hc3, sum_const, card_univ,
      Houghton.card_G, nsmul_eq_mul]
    rw [show (9 : ℂ) ^ N = 3 ^ N * 3 ^ N by rw [← mul_pow]; norm_num]
    push_cast
    ring
  have hc2 : (c i ^ 2).trace = star (c i).trace := by
    have : c i ^ 2 = (c i)ᴴ := by
      have h1 : c i ^ 2 * c i = 1 := by rw [← pow_succ, hc3 i]
      calc c i ^ 2 = c i ^ 2 * (c i * (c i)ᴴ) := by rw [(hc i).2, Matrix.mul_one]
        _ = (c i)ᴴ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
    rw [this, trace_conjTranspose]
  have S : ∑ χ, (if χ i = 0 then (3 : ℂ) else 0) * (Houghton.nsq (MsecU c χ) : ℂ) =
      9 ^ N * ((Fintype.card Ω : ℂ) + (c i).trace + star (c i).trace) := by
    have : ∀ χ : Fin N → Fin 3, (if χ i = 0 then (3 : ℂ) else 0) * (Houghton.nsq (MsecU c χ) : ℂ) =
        ∑ k : Fin 3, Houghton.ech (k * χ i) * (Houghton.nsq (MsecU c χ) : ℂ) := by
      intro χ; rw [← sum_mul, Houghton.sum_ech]
    rw [sum_congr rfl fun χ _ => this χ, sum_comm, Fin.sum_univ_three]
    simp only [T]
    rw [show ((2 : Fin 3).val) = 2 from rfl, hc2]
    simp
    ring
  have S2 : ∑ χ, (if χ i = 0 then 3 * Houghton.nsq (MsecU c χ) else 0) =
      9 ^ N * (Fintype.card Ω + 2 * (c i).trace.re) := by
    have e : ∀ χ : Fin N → Fin 3, (if χ i = 0 then (3 : ℂ) else 0) *
        (Houghton.nsq (MsecU c χ) : ℂ) =
        (((if χ i = 0 then 3 * Houghton.nsq (MsecU c χ) else 0) : ℝ) : ℂ) := by
      intro χ; split_ifs <;> simp
    simp only [e] at S
    rw [← Complex.ofReal_sum] at S
    have := congrArg Complex.re S
    rw [Complex.ofReal_re] at this
    rw [this]
    have h9 : ((9 : ℂ) ^ N) = (((9 : ℝ) ^ N : ℝ) : ℂ) := by push_cast; rfl
    rw [h9, Complex.re_ofReal_mul]
    simp only [Complex.add_re, Complex.natCast_re, Complex.star_def, Complex.conj_re]
    ring
  have S' : ∑ χ, (if χ i = 0 then Houghton.nsq (MsecU c χ) else 0) =
      9 ^ N * (Fintype.card Ω + 2 * (c i).trace.re) / 3 := by
    have : ∑ χ, (if χ i = 0 then 3 * Houghton.nsq (MsecU c χ) else 0) =
        3 * ∑ χ, (if χ i = 0 then Houghton.nsq (MsecU c χ) else 0) := by
      rw [mul_sum]; exact sum_congr rfl fun χ _ => by split_ifs <;> simp
    rw [this] at S2; linarith
  have htot := sum_nsq_MsecU c hc
  have hsplit : ∑ z ∈ univ.filter (fun z => z i ≠ 0), pSecU c z =
      (∑ χ, Houghton.nsq (MsecU c χ) - ∑ χ, (if χ i = 0 then Houghton.nsq (MsecU c χ) else 0)) /
        (9 ^ N * Fintype.card Ω) := by
    rw [sum_filter, ← sum_sub_distrib, sum_div]
    refine sum_congr rfl fun χ _ => ?_
    by_cases h : χ i = 0 <;> simp [pSecU, h]
  rw [hsplit, htot, S', ud_one_sq (hc i) hD]
  field_simp
  ring

end Lamps

namespace Lamps

open Finset Matrix ComplexConjugate

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {N : ℕ}

/-- View an array as a matrix. -/
def asM (A : Ω → Ω → ℂ) : Matrix Ω Ω ℂ := A

lemma FT_eq_sum (A : (Fin N → Fin 3) → Matrix Ω Ω ℂ) (χ : Fin N → Fin 3) :
    (Houghton.FT (fun g => A g) χ : Matrix Ω Ω ℂ) =
      ∑ g, Houghton.ech (-(Houghton.dot χ g)) • A g := by
  ext α β
  simp [Houghton.FT, Matrix.sum_apply]

lemma FT_conj (A : (Fin N → Fin 3) → Matrix Ω Ω ℂ) (x : Matrix Ω Ω ℂ) (χ : Fin N → Fin 3) :
    (Houghton.FT (fun g => x * A g * xᴴ) χ : Matrix Ω Ω ℂ) =
      x * asM (Houghton.FT (fun g => A g) χ) * xᴴ := by
  rw [asM, FT_eq_sum, FT_eq_sum, Finset.mul_sum, Finset.sum_mul]
  refine sum_congr rfl fun g _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul]

lemma nsq_conj_isU {x : Matrix Ω Ω ℂ} (hx : IsU x) (A : Matrix Ω Ω ℂ) :
    Houghton.nsq (x * A * xᴴ) = Houghton.nsq A := by
  rw [nsq_mul_right_unitary hx.conjT.2, nsq_mul_left_unitary hx.1]

/-- `Re Tr(Aᴴ B) = D - ‖A - B‖²_HS / 2` for unitaries. -/
lemma re_hip_isU {A B : Matrix Ω Ω ℂ} (hA : IsU A) (hB : IsU B) :
    (Houghton.hip A B).re = Fintype.card Ω - Houghton.nsq (A - B) / 2 := by
  have h := nsq_eq_trace (A - B)
  rw [conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hA.2, hB.2, trace_sub,
    trace_sub, trace_sub, trace_one] at h
  have hre := congrArg Complex.re h
  rw [Complex.ofReal_re] at hre
  rw [hip_eq_trace]
  have e1 : (B * Aᴴ).trace = star (A * Bᴴ).trace := by
    rw [← trace_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]
  have e2 : (Aᴴ * B).trace = (B * Aᴴ).trace := Matrix.trace_mul_comm _ _
  have hre' : Houghton.nsq (A - B) = 2 * (Fintype.card Ω : ℝ) - 2 * ((Aᴴ * B).trace).re := by
    refine hre.trans ?_
    rw [e2, e1]
    simp only [Complex.sub_re, Complex.natCast_re, Complex.star_def, Complex.conj_re]
    ring
  rw [hre']
  ring

/-- `b̂_i² = E_g ‖f(g) - x_i f(g⁽ⁱ⁾) x_i*‖₂²`. -/
noncomputable def bhat2 (c : Fin N → Matrix Ω Ω ℂ) (x : Matrix Ω Ω ℂ) (i : Fin N) : ℝ :=
  (∑ g, ud (fprodU c g) (x * fprodU c (Houghton.flipAt i g) * xᴴ) ^ 2) / 3 ^ N

/-- **Bhattacharyya bound**: `∑_χ √(p(χ) p(χ⁽ⁱ⁾)) ≥ 1 - b̂_i²/2`. -/
theorem bhatt_pSecU (c : Fin N → Matrix Ω Ω ℂ) (hc : ∀ i, IsU (c i)) (x : Matrix Ω Ω ℂ)
    (hx : IsU x) (hD : 0 < Fintype.card Ω) (i : Fin N) :
    1 - bhat2 c x i / 2 ≤ ∑ z, Real.sqrt (pSecU c z * pSecU c (Houghton.flipAt i z)) := by
  have hDR : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast hD
  have hKpos : (0 : ℝ) < 9 ^ N * Fintype.card Ω := by positivity
  set B : (Fin N → Fin 3) → Matrix Ω Ω ℂ := fun g => x * fprodU c (Houghton.flipAt i g) * xᴴ
  have hB : ∀ χ, (Houghton.FT (fun g => B g) χ : Matrix Ω Ω ℂ) =
      x * asM (MsecU c (Houghton.flipAt i χ)) * xᴴ := by
    intro χ
    have h1 := FT_conj (fun g => fprodU c (Houghton.flipAt i g)) x χ
    have h2 := Houghton.FT_flip (fun g => fprodU c g) i χ
    simp only [MsecU]
    rw [h2]
    exact h1
  -- termwise Cauchy–Schwarz
  have hterm : ∀ χ, (Houghton.hip (MsecU c χ) (Houghton.FT (fun g => B g) χ)).re /
      (9 ^ N * Fintype.card Ω) ≤ Real.sqrt (pSecU c χ * pSecU c (Houghton.flipAt i χ)) := by
    intro χ
    have hcs := Houghton.re_hip_le (MsecU c χ) (Houghton.FT (fun g => B g) χ)
    have hn : Houghton.nsq (Houghton.FT (fun g => B g) χ) = Houghton.nsq (MsecU c (Houghton.flipAt i χ)) := by
      have := nsq_conj_isU hx (asM (MsecU c (Houghton.flipAt i χ)))
      rw [← hB χ] at this
      exact this
    rw [hn] at hcs
    have e : Real.sqrt (pSecU c χ * pSecU c (Houghton.flipAt i χ)) =
        Real.sqrt (Houghton.nsq (MsecU c χ)) * Real.sqrt (Houghton.nsq (MsecU c (Houghton.flipAt i χ))) /
          (9 ^ N * Fintype.card Ω) := by
      unfold pSecU
      rw [div_mul_div_comm, Real.sqrt_div (mul_nonneg (Houghton.nsq_nonneg _)
        (Houghton.nsq_nonneg _)), Real.sqrt_mul (Houghton.nsq_nonneg _),
        Real.sqrt_mul_self hKpos.le]
    rw [e]
    exact div_le_div_of_nonneg_right hcs hKpos.le
  -- the total overlap
  have hsum : (∑ χ, Houghton.hip (MsecU c χ) (Houghton.FT (fun g => B g) χ)).re =
      3 ^ N * ∑ g, ((Fintype.card Ω : ℝ) - Houghton.nsq (fprodU c g - B g) / 2) := by
    have h := Houghton.parseval (fun g => fprodU c g) (fun g => B g)
    simp only [MsecU]
    rw [h, show (3 : ℂ) ^ N = (((3 : ℝ) ^ N : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul,
      Complex.re_sum]
    congr 1
    refine sum_congr rfl fun g _ => ?_
    exact re_hip_isU (isU_fprodU c hc g) ((hx.mul (isU_fprodU c hc _)).mul hx.conjT)
  have hud : ∀ g, Houghton.nsq (fprodU c g - B g) = Fintype.card Ω * ud (fprodU c g) (B g) ^ 2 := by
    intro g
    have h0 : 0 ≤ Houghton.nsq (fprodU c g - B g) / Fintype.card Ω :=
      div_nonneg (Houghton.nsq_nonneg _) hDR.le
    have hsq : ud (fprodU c g) (B g) ^ 2 = Houghton.nsq (fprodU c g - B g) / Fintype.card Ω :=
      Real.sq_sqrt h0
    rw [hsq]; field_simp
  have hval : (∑ χ, Houghton.hip (MsecU c χ) (Houghton.FT (fun g => B g) χ)).re /
      (9 ^ N * Fintype.card Ω) = 1 - bhat2 c x i / 2 := by
    rw [hsum]
    simp only [hud, bhat2]
    rw [sum_sub_distrib, sum_const, card_univ, Houghton.card_G, nsmul_eq_mul, ← sum_div,
      ← mul_sum]
    rw [show (9 : ℝ) ^ N = 3 ^ N * 3 ^ N by rw [← mul_pow]; norm_num]
    field_simp
    push_cast
    ring
  calc 1 - bhat2 c x i / 2
      = (∑ χ, Houghton.hip (MsecU c χ) (Houghton.FT (fun g => B g) χ)).re /
          (9 ^ N * Fintype.card Ω) := hval.symm
    _ = ∑ χ, (Houghton.hip (MsecU c χ) (Houghton.FT (fun g => B g) χ)).re /
          (9 ^ N * Fintype.card Ω) := by rw [Complex.re_sum, sum_div]
    _ ≤ _ := sum_le_sum fun χ _ => hterm χ

end Lamps
