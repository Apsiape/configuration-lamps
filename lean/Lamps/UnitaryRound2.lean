import Lamps.UnitaryRound
import Lamps.UnitaryRoundSpec

/-!
# Lemma `lem:imp-s3round` from pointwise rounding functions

`unitaryS3Round_of (h2 : ∃ r, RoundFn 2 r) (h3 : ∃ r, RoundFn 3 r) : UnitaryS3Round`.
For a unitary `U`, `uL U = (U + Uᴴ)/2` and `uR U = -i(U - Uᴴ)/2` are commuting Hermitian matrices
with `U = jC (a + b i)` (`eq_jC`), the joint spectrum lies on the unit circle (`supp_circle`), and
`rnd r U = jC (r (a + b i))` is a unitary (`isU_rnd`) with `(rnd r U)^k = 1` and
`‖rnd r U - U‖₂ ≤ ‖U^k - 1‖₂` for `r` with `RoundFn k r`, and it is conjugation-equivariant
(`conj_rnd`: `S (rnd r U) S = (rnd r U)ᴴ` for a Hermitian involution `S` with `S U S = Uᴴ`).
-/

namespace Lamps

open Matrix QIT Complex

variable {m : Type} [Fintype m] [DecidableEq m]

section Joint

variable {L R : Matrix m m ℂ}

lemma jJ_congr' (F G : ℝ → ℝ → ℝ)
    (h : ∀ a ∈ spf L, ∀ b ∈ spf R, jE L R a b ≠ 0 → F a b = G a b) : jJ L R F = jJ L R G := by
  unfold jJ
  refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
  by_cases h0 : jE L R a b = 0
  · simp [h0]
  · rw [h a ha b hb h0]

lemma jC_congr' (F G : ℝ → ℝ → ℂ)
    (h : ∀ a ∈ spf L, ∀ b ∈ spf R, jE L R a b ≠ 0 → F a b = G a b) : jC L R F = jC L R G := by
  unfold jC
  rw [jJ_congr' _ _ (fun a ha b hb h0 => by rw [h a ha b hb h0]),
    jJ_congr' (fun a b => (F a b).im) _ (fun a ha b hb h0 => by rw [h a ha b hb h0])]

lemma jC_pow (hLR : Commute L R) (hL : IsSelfAdjoint L) (hR : IsSelfAdjoint R) (F : ℝ → ℝ → ℂ)
    (k : ℕ) : jC L R F ^ k = jC L R (fun a b => F a b ^ k) := by
  induction k with
  | zero => simp only [pow_zero]; exact (jC_one hL hR).symm
  | succ k ih => rw [pow_succ, ih, jC_mul hLR]; simp only [pow_succ]

lemma jJ_eq_sum_cfc (G : ℝ → ℝ → ℝ) :
    jJ L R G = ∑ a ∈ spf L, sproj L a * cfc (fun b => G a b) R := by
  unfold jJ jE
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [cfc_expand, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by rw [mul_smul_comm]

/-- Conjugation by a Hermitian involution fixing `L` and negating `R` reflects `b ↦ -b`. -/
lemma conj_jC (hL : IsSelfAdjoint L) (hR : IsSelfAdjoint R) {S : Matrix m m ℂ}
    (hS : S * S = 1) (hSh : Sᴴ = S) (hSL : S * L * S = L) (hSR : S * R * S = -R)
    (F : ℝ → ℝ → ℂ) : S * jC L R F * S = jC L R (fun a b => F a (-b)) := by
  have hmem : S ∈ unitary (Matrix m m ℂ) := by
    rw [Unitary.mem_iff, star_eq_conjTranspose, hSh]; exact ⟨hS, hS⟩
  set φ := Unitary.conjStarAlgAut ℂ (Matrix m m ℂ) ⟨S, hmem⟩
  have hφ : ∀ X, φ X = S * X * S := fun X => by
    show S * X * star S = S * X * S
    rw [star_eq_conjTranspose, hSh]
  have hcont : Continuous φ := by
    have : (φ : Matrix m m ℂ → Matrix m m ℂ) = fun X => S * X * S := funext hφ
    rw [this]; fun_prop
  have hmap : ∀ (f : ℝ → ℝ) (A : Matrix m m ℂ), IsSelfAdjoint A → IsSelfAdjoint (φ A) →
      φ (cfc f A) = cfc f (φ A) := fun f A hA hA' =>
    StarAlgHomClass.map_cfc φ f A (contSp A f) hcont hA hA'
  have hφL : φ L = L := by rw [hφ, hSL]
  have hφR : φ R = -R := by rw [hφ, hSR]
  have hnR : IsSelfAdjoint (-R) := hR.neg
  have hJ : ∀ G : ℝ → ℝ → ℝ, φ (jJ L R G) = jJ L R (fun a b => G a (-b)) := by
    intro G
    rw [jJ_eq_sum_cfc, jJ_eq_sum_cfc, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_mul, sproj, hmap _ _ hL (by rw [hφL]; exact hL), hφL, hmap _ _ hR (by rw [hφR]; exact hnR), hφR,
      ← cfc_comp_neg (hf := Set.Finite.continuousOn
        ((Matrix.finite_real_spectrum (A := R)).image (fun x => -x)) _) (ha := hR)]
  rw [← hφ]
  unfold jC
  rw [map_add, map_smul, hJ, hJ]

end Joint

section Unitary

/-- `(U + Uᴴ)/2`. -/
noncomputable def uL (U : Matrix m m ℂ) : Matrix m m ℂ := (1 / 2 : ℝ) • (U + Uᴴ)

/-- `-i(U - Uᴴ)/2`. -/
noncomputable def uR (U : Matrix m m ℂ) : Matrix m m ℂ := (1 / 2 : ℝ) • ((-I) • (U - Uᴴ))

/-- Rounding of a unitary through a function `r : ℂ → ℂ` of its spectrum. -/
noncomputable def rnd (r : ℂ → ℂ) (U : Matrix m m ℂ) : Matrix m m ℂ :=
  jC (uL U) (uR U) (fun a b => r (a + b * I))

variable {U : Matrix m m ℂ}

omit [Fintype m] [DecidableEq m] in
lemma uL_sa (U : Matrix m m ℂ) : IsSelfAdjoint (uL U) := by
  unfold uL IsSelfAdjoint
  rw [star_smul, star_trivial, star_add]
  simp only [star_eq_conjTranspose, conjTranspose_conjTranspose]
  rw [add_comm]

omit [Fintype m] [DecidableEq m] in
lemma uR_sa (U : Matrix m m ℂ) : IsSelfAdjoint (uR U) := by
  unfold uR IsSelfAdjoint
  rw [star_smul, star_trivial, star_smul, star_sub]
  simp only [star_eq_conjTranspose, conjTranspose_conjTranspose]
  congr 1
  rw [show star (-I) = I by simp]
  rw [show Uᴴ - U = -(U - Uᴴ) by abel, smul_neg, ← neg_smul]

lemma uLR_comm (hU : IsU U) : Commute (uL U) (uR U) := by
  have hc : Commute U Uᴴ := by
    show U * Uᴴ = Uᴴ * U
    rw [hU.2, hU.1]
  have h1 : Commute (U + Uᴴ) (U - Uᴴ) :=
    ((Commute.refl U).sub_right hc).add_left (hc.symm.sub_right (Commute.refl _))
  exact ((h1.smul_right (-I)).smul_right (1 / 2 : ℝ)).smul_left (1 / 2 : ℝ)

lemma eq_jC (U : Matrix m m ℂ) : U = jC (uL U) (uR U) (fun a b => (a : ℂ) + b * I) := by
  unfold jC
  have e1 : jJ (uL U) (uR U) (fun a b => ((a : ℂ) + b * I).re) = uL U := by
    rw [jJ_congr _ (fun a _ => id a) (fun a _ b _ => by simp),
      ← jJ_left (uL_sa U) (uR_sa U), cfc_id ℝ (uL U) (uL_sa U)]
  have e2 : jJ (uL U) (uR U) (fun a b => ((a : ℂ) + b * I).im) = uR U := by
    rw [jJ_congr _ (fun _ b => id b) (fun a _ b _ => by simp),
      ← jJ_right (uL_sa U) (uR_sa U), cfc_id ℝ (uR U) (uR_sa U)]
  rw [e1, e2]
  ext i j
  simp only [uL, uR, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
    conjTranspose_apply, Complex.real_smul, smul_eq_mul]
  push_cast
  linear_combination ((1 / 2 : ℂ) * (U i j - star (U j i))) * I_sq

lemma supp_circle (hU : IsU U) {a b : ℝ} (ha : a ∈ spf (uL U)) (hb : b ∈ spf (uR U))
    (h0 : jE (uL U) (uR U) a b ≠ 0) : Complex.normSq ((a : ℂ) + b * I) = 1 := by
  have hLR := uLR_comm hU
  have hUU : U * Uᴴ = 1 := hU.2
  rw [eq_jC U, jC_star hLR, jC_mul hLR, ← jC_one (uL_sa U) (uR_sa U)] at hUU
  have e : jC (uL U) (uR U) (fun a b => ((a : ℂ) + b * I) * star ((a : ℂ) + b * I)) =
      jJ (uL U) (uR U) (fun a b => Complex.normSq ((a : ℂ) + b * I)) := by
    rw [← jC_real]
    congr 1
    funext a b
    rw [Complex.star_def, Complex.mul_conj]
  have e1 : jC (uL U) (uR U) (fun _ _ => (1 : ℂ)) = jJ (uL U) (uR U) (fun _ _ => (1 : ℝ)) := by
    rw [← jC_real]; simp only [Complex.ofReal_one]
  rw [e, e1] at hUU
  have h1 := congrArg (· * jE (uL U) (uR U) a b) hUU
  rw [jJ_mul_jE hLR _ ha hb, jJ_mul_jE hLR _ ha hb] at h1
  have h2 : (Complex.normSq ((a : ℂ) + b * I) - 1) • jE (uL U) (uR U) a b = 0 := by
    rw [sub_smul, h1, sub_self]
  rcases smul_eq_zero.1 h2 with h | h
  · linarith
  · exact absurd h h0

lemma isU_rnd (hU : IsU U) {r : ℂ → ℂ} {k : ℕ} (hr : RoundFn k r) : IsU (rnd r U) := by
  have hLR := uLR_comm hU
  have key : jC (uL U) (uR U) (fun a b => star (r (a + b * I)) * r (a + b * I)) = 1 := by
    rw [← jC_one (uL_sa U) (uR_sa U)]
    refine jC_congr' _ _ fun a ha b hb h0 => ?_
    have := (hr _ (supp_circle hU ha hb h0)).1
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, this, ofReal_one]
  have key' : jC (uL U) (uR U) (fun a b => r (a + b * I) * star (r (a + b * I))) = 1 := by
    rw [← key]; congr 1; funext a b; rw [mul_comm]
  unfold rnd
  refine ⟨?_, ?_⟩
  · rw [jC_star hLR, jC_mul hLR, key]
  · rw [jC_star hLR, jC_mul hLR, key']

lemma rnd_pow (hU : IsU U) {r : ℂ → ℂ} {k : ℕ} (hr : RoundFn k r) : rnd r U ^ k = 1 := by
  unfold rnd
  rw [jC_pow (uLR_comm hU) (uL_sa U) (uR_sa U), ← jC_one (uL_sa U) (uR_sa U)]
  exact jC_congr' _ _ fun a ha b hb h0 => (hr _ (supp_circle hU ha hb h0)).2.1

lemma ud_rnd_le (hU : IsU U) {r : ℂ → ℂ} {k : ℕ} (hr : RoundFn k r) :
    ud (rnd r U) U ≤ ud (U ^ k) 1 := by
  have hLR := uLR_comm hU
  have e1 : rnd r U - U = jC (uL U) (uR U) (fun a b => r (a + b * I) - (a + b * I)) := by
    unfold rnd
    rw [← jC_sub, ← eq_jC U]
  have e2 : U ^ k - 1 = jC (uL U) (uR U) (fun a b => ((a : ℂ) + b * I) ^ k - 1) := by
    rw [← jC_sub, ← jC_pow hLR (uL_sa U) (uR_sa U), ← eq_jC U, jC_one (uL_sa U) (uR_sa U)]
  unfold ud uhs
  rw [e1, e2]
  refine Real.sqrt_le_sqrt (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _))
  exact nsq_jC_le hLR _ _ (fun a b => Complex.normSq ((a : ℂ) + b * I) = 1)
    (fun a ha b hb h0 => supp_circle hU ha hb h0) (fun a b h => (hr _ h).2.2.1)

/-- Conjugation equivariance of the rounding. -/
lemma conj_rnd (hU : IsU U) {r : ℂ → ℂ} {k : ℕ} (hr : RoundFn k r) {S : Matrix m m ℂ}
    (hS : S * S = 1) (hSh : Sᴴ = S) (hSU : S * U * S = Uᴴ) : S * rnd r U * S = (rnd r U)ᴴ := by
  have hLR := uLR_comm hU
  have hSU' : S * Uᴴ * S = U := by
    have := congrArg conjTranspose hSU
    simpa [conjTranspose_mul, hSh, Matrix.mul_assoc] using this
  have hSL : S * uL U * S = uL U := by
    simp only [uL, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul]
    rw [hSU, hSU', add_comm]
  have hSR : S * uR U * S = -uR U := by
    simp only [uR, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul]
    rw [hSU, hSU', ← smul_neg, ← smul_neg, neg_sub]
  unfold rnd
  rw [conj_jC (uL_sa U) (uR_sa U) hS hSh hSL hSR, jC_star hLR]
  refine jC_congr' _ _ fun a ha b hb h0 => ?_
  have hc := (hr _ (supp_circle hU ha hb h0)).2.2.2
  rw [← Complex.star_def] at hc
  rw [← hc]
  congr 1
  simp

end Unitary

lemma ud_pow3_le {X Y : Matrix m m ℂ} (hX : IsU X) (hY : IsU Y) :
    ud (X ^ 3) (Y ^ 3) ≤ 3 * ud X Y := by
  have h2 : ud (X * X) (Y * Y) ≤ ud X Y + ud X Y := ud_mul_le hX hY
  have h3 : ud (X * X * X) (Y * Y * Y) ≤ ud (X * X) (Y * Y) + ud X Y := ud_mul_le (hX.mul hX) hY
  rw [pow_three', pow_three']
  linarith

/-- **Lemma `lem:imp-s3round`** (exact `S₃` rounding), from pointwise rounding functions to the
square roots and the cube roots of unity. -/
theorem unitaryS3Round_of (h2 : ∃ r, RoundFn 2 r) (h3 : ∃ r, RoundFn 3 r) : UnitaryS3Round := by
  obtain ⟨r2, hr2⟩ := h2
  obtain ⟨r3, hr3⟩ := h3
  intro Ω _ _ A B e hA hB hAA hBB hAB
  have hS : IsU (rnd r2 A) := isU_rnd hA hr2
  have hT : IsU (rnd r2 B) := isU_rnd hB hr2
  have hS2 : rnd r2 A * rnd r2 A = 1 := by rw [← pow_two]; exact rnd_pow hA hr2
  have hT2 : rnd r2 B * rnd r2 B = 1 := by rw [← pow_two]; exact rnd_pow hB hr2
  have herm : ∀ {X : Matrix Ω Ω ℂ}, IsU X → X * X = 1 → Xᴴ = X := fun hX hXX => by
    calc _ = _ * (_ * _) := by rw [hXX, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, hX.1, Matrix.one_mul]
  have hSh := herm hS hS2
  have hTh := herm hT hT2
  have hSA : ud (rnd r2 A) A ≤ e := (ud_rnd_le hA hr2).trans (by rw [pow_two]; exact hAA)
  have hTB : ud (rnd r2 B) B ≤ e := (ud_rnd_le hB hr2).trans (by rw [pow_two]; exact hBB)
  have hC : IsU (rnd r2 A * rnd r2 B) := hS.mul hT
  have hSCS : rnd r2 A * (rnd r2 A * rnd r2 B) * rnd r2 A = (rnd r2 A * rnd r2 B)ᴴ := by
    rw [conjTranspose_mul, hSh, hTh, ← Matrix.mul_assoc, hS2, Matrix.one_mul]
  have hCAB : ud (rnd r2 A * rnd r2 B) (A * B) ≤ 2 * e := by
    have := ud_mul_le (X := rnd r2 A) (Y := rnd r2 B) (X' := A) (Y' := B) hS hB
    linarith
  have hC3 : ud ((rnd r2 A * rnd r2 B) ^ 3) 1 ≤ 7 * e := by
    have h1 := ud_triangle ((rnd r2 A * rnd r2 B) ^ 3) ((A * B) ^ 3) 1
    have h2 := ud_pow3_le hC (hA.mul hB)
    linarith
  refine ⟨rnd r2 A, rnd r3 (rnd r2 A * rnd r2 B), hS, isU_rnd hC hr3, hS2, rnd_pow hC hr3,
    conj_rnd hC hr3 hS2 hSh hSCS, hSA, ?_⟩
  have h1 := ud_triangle (rnd r3 (rnd r2 A * rnd r2 B)) (rnd r2 A * rnd r2 B) (A * B)
  have h2 := ud_rnd_le hC hr3
  linarith

end Lamps
