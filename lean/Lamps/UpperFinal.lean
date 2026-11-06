import Lamps.UpperCocycleSpec
import Lamps.Chunk
import Houghton.Upper

/-!
# Theorem A(b): telescoping the letter cocycles (from `LetterCocycleSpec`)
-/

namespace Lamps

open Finset Hash

/-- The clock step of a word. -/
def piW (L : List (Fin 5 × Bool)) : ℤ × ℤ := (L.map piL).sum

theorem piL_abs (l : Fin 5 × Bool) : |(piL l).1| + |(piL l).2| ≤ 1 := by
  unfold piL; split_ifs <;> simp

namespace Hash

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- The identity of `K_W`. -/
def KW.one : KW P where
  g := Equiv.refl _
  hg := by intro v w; ext x; simp [Finset.mem_symmDiff]
  hgi := by intro v w; ext x; simp [Finset.mem_symmDiff]
  lam _ := 1

/-- The lamp support. -/
def supp (γ : KW P) : Finset (Finset P) := univ.filter fun w => γ.lam w ≠ 1

theorem mem_supp (γ : KW P) (w : Finset P) : w ∈ supp γ ↔ γ.lam w ≠ 1 := by simp [supp]

theorem supp_mul (γ₁ γ₂ : KW P) :
    supp (KW.mul γ₁ γ₂) ⊆ supp γ₁ ∪ (supp γ₂).map γ₁.g.toEmbedding := by
  intro w hw
  rw [mem_supp] at hw
  simp only [mem_union, mem_supp, mem_map_equiv]
  by_contra h
  push Not at h
  apply hw
  simp [KW.mul, h.1, h.2]

theorem card_supp_mul (γ₁ γ₂ : KW P) :
    (supp (KW.mul γ₁ γ₂)).card ≤ (supp γ₁).card + (supp γ₂).card :=
  (card_le_card (supp_mul γ₁ γ₂)).trans ((card_union_le _ _).trans (by simp))

theorem card_supp_one : (supp (KW.one : KW P)).card = 0 := by simp [supp, KW.one]

end Hash

/-- **Telescoping**: under `LetterCocycleSpec`, for `z ∈ B_{m - |L|}` the cocycle
`g_{z+π(L)}⁻¹ L g_z` of a word `L` is realized by an element of `K_{W_R}` with at most `|L|` lamps. -/
theorem telescope (hspec : LetterCocycleSpec) (m : ℕ) :
    ∀ (L : List (Fin 5 × Bool)) (z : ℤ × ℤ), |z.1| + L.length ≤ m → |z.2| + L.length ≤ m →
      ∃ γ : KW (PR (2 * m + 3)),
        realF (2 * m + 3) γ = ⇑(ρΓ ((gzW (z + piW L))⁻¹ * FreeGroup.mk L * gzW z)) ∧
        (supp γ).card ≤ L.length
  | [], z, _, _ => by
    refine ⟨KW.one, ?_, by simp [card_supp_one]⟩
    have h0 : (gzW (z + piW []))⁻¹ * FreeGroup.mk [] * gzW z = 1 := by
      rw [show FreeGroup.mk ([] : List (Fin 5 × Bool)) = 1 from rfl]
      simp [piW]
    rw [h0, map_one]
    funext ⟨v, s⟩
    show realF _ KW.one (v, s) = (v, s)
    simp only [realF, KW.one, Equiv.refl_apply, ite_self, one_mul, split]
  | l :: L, z, h1, h2 => by
    simp only [List.length_cons] at h1 h2
    obtain ⟨γ₂, hr₂, hs₂⟩ := telescope hspec m L z (by omega) (by omega)
    have hπ := piL_abs l
    have hL1 : |(piW L).1| ≤ L.length := by
      clear h1 h2 hr₂ hs₂ hπ
      induction L with
      | nil => simp [piW]
      | cons x L ih =>
        have := piL_abs x
        simp only [piW, List.map_cons, List.sum_cons, Prod.fst_add, List.length_cons] at ih ⊢
        have a1 := abs_add_le (piL x).1 (List.map piL L).sum.1
        have a2 := abs_nonneg (piL x).2
        push_cast; linarith
    have hL2 : |(piW L).2| ≤ L.length := by
      clear h1 h2 hr₂ hs₂ hπ hL1
      induction L with
      | nil => simp [piW]
      | cons x L ih =>
        have := piL_abs x
        simp only [piW, List.map_cons, List.sum_cons, Prod.snd_add, List.length_cons] at ih ⊢
        have a1 := abs_add_le (piL x).2 (List.map piL L).sum.2
        have a2 := abs_nonneg (piL x).1
        push_cast; linarith
    obtain ⟨γ₁, hr₁, hs₁⟩ := hspec m (z + piW L)
      (by simp only [Prod.fst_add]; have := abs_add_le z.1 (piW L).1; push_cast at h1 ⊢; linarith)
      (by simp only [Prod.snd_add]; have := abs_add_le z.2 (piW L).2; push_cast at h2 ⊢; linarith) l
    refine ⟨KW.mul γ₁ γ₂, ?_, ?_⟩
    · funext x
      rw [realF_mul, hr₁, hr₂]
      have hpi : z + piW (l :: L) = z + piW L + piL l := by
        simp only [piW, List.map_cons, List.sum_cons]; abel
      rw [hpi, ← Equiv.Perm.mul_apply, ← map_mul]
      congr 2
      rw [show FreeGroup.mk (l :: L) = FreeGroup.mk [l] * FreeGroup.mk L by
        rw [FreeGroup.mul_mk]; rfl]
      group
    · have := card_supp_mul γ₁ γ₂
      have h1' : (supp γ₁).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro a ha b hb
        rw [mem_supp] at ha hb
        exact hs₁ a b ha hb
      simp only [List.length_cons]; omega

/-! ### The clock step is well defined on `Γ` -/

theorem realF_far (R : ℕ) (γ : KW (PR R)) (y : Houghton.Y) (hy : y ∉ YR R) :
    realF R γ ({y}, 1) = ((γ.g ∅).map (embR R) ∪ {y}, 1) := by
  have hin : inner R {y} = ∅ := by
    ext x; simp only [inner, mem_subtype, mem_singleton, notMem_empty, iff_false]
    intro h; exact hy (h ▸ x.2)
  have hout : outer R {y} = {y} := by
    ext x; simp only [outer, mem_filter, mem_singleton]
    constructor
    · exact fun h => h.1
    · intro h; exact ⟨h, h ▸ hy⟩
  simp only [realF, hin, hout, singleton_ne_empty, if_false, one_mul]

theorem gz_ray1 (a b : ℤ) (j j' : ℕ) (h : (j' : ℤ) = j - a) :
    gz (a, b) ((1 : Fin 3), j) = (1, j') := by
  simp only [gz, Equiv.Perm.mul_apply]
  rw [isShift_qY.zpow_apply b 1 j j (by simp [δq]), isShift_pY.zpow_apply a 1 j j' (by
    simp [δp]; linarith)]

theorem gz_ray2 (a b : ℤ) (j j' : ℕ) (h : (j' : ℤ) = j - b) :
    gz (a, b) ((2 : Fin 3), j) = (2, j') := by
  simp only [gz, Equiv.Perm.mul_apply]
  rw [isShift_qY.zpow_apply b 2 j j' (by simp [δq]; linarith), isShift_pY.zpow_apply a 2 j' j'
    (by simp [δp])]

/-- If `hV δ ∘ realF γ = realF γ'`, then `δ` fixes every point outside `Y_R`
whose image is outside `Y_R`. -/
theorem fix_of_realF {R : ℕ} {γ γ' : KW (PR R)} {δ : Equiv.Perm Houghton.Y}
    (h : ∀ x, hV δ (realF R γ x) = realF R γ' x) (y : Houghton.Y) (hy : y ∉ YR R)
    (hδy : δ y ∉ YR R) : δ y = y := by
  have := congrArg Prod.fst (h ({y}, 1))
  rw [realF_far R γ y hy, realF_far R γ' y hy, hV_apply] at this
  have hm : δ y ∈ ((γ'.g ∅).map (embR R) ∪ {y}) := by
    simp only at this
    rw [← this]; simp
  rcases mem_union.mp hm with h1 | h1
  · obtain ⟨a, _, ha⟩ := mem_map.mp h1
    exact absurd (ha ▸ a.2) hδy
  · exact mem_singleton.mp h1

theorem piW_abs (L : List (Fin 5 × Bool)) : |(piW L).1| ≤ L.length ∧ |(piW L).2| ≤ L.length := by
  induction L with
  | nil => simp [piW]
  | cons x L ih =>
    have := piL_abs x
    simp only [piW, List.map_cons, List.sum_cons, Prod.fst_add, Prod.snd_add,
      List.length_cons] at ih ⊢
    have a1 := abs_add_le (piL x).1 (List.map piL L).sum.1
    have a2 := abs_add_le (piL x).2 (List.map piL L).sum.2
    have := abs_nonneg (piL x).1; have := abs_nonneg (piL x).2
    push_cast; constructor <;> linarith

/-- **`π` is well defined**: words representing the same element of `Γ` have the same clock step. -/
theorem piW_eq (hspec : LetterCocycleSpec) (L L' : List (Fin 5 × Bool))
    (h : ρΓ (FreeGroup.mk L) = ρΓ (FreeGroup.mk L')) : piW L = piW L' := by
  set m := L.length + L'.length
  obtain ⟨γ, hγ, -⟩ := telescope hspec m L 0 (by simp; omega) (by simp; omega)
  obtain ⟨γ', hγ', -⟩ := telescope hspec m L' 0 (by simp; omega) (by simp; omega)
  have hrel : ∀ x, hV ((gz (piW L'))⁻¹ * gz (piW L)) (realF _ γ x) = realF _ γ' x := by
    intro x
    rw [hγ, hγ', ← Equiv.Perm.mul_apply, map_mul hV, map_inv hV, ← rho_gzW, ← rho_gzW, ← map_inv,
      ← map_mul, ← map_mul]
    congr 1
    simp only [zero_add, map_mul, map_inv, h]
    group
  obtain ⟨b1, b2⟩ := piW_abs L
  obtain ⟨c1, c2⟩ := piW_abs L'
  set a := (piW L).1; set b := (piW L).2; set a' := (piW L').1; set b' := (piW L').2
  set J : ℕ := 2 * m + 3 + 2 * m + 2
  have hJ : (J : ℤ) = 4 * m + 5 := by simp [J]; ring
  -- ray 1
  have e1 : a = a' := by
    obtain ⟨j1, hj1⟩ : ∃ j1 : ℕ, (j1 : ℤ) = J - a := ⟨(J - a).toNat, by
      rw [Int.toNat_of_nonneg]; rw [abs_le] at b1; push_cast [m] at b1 ⊢; omega⟩
    obtain ⟨j2, hj2⟩ : ∃ j2 : ℕ, (j2 : ℤ) = j1 + a' := ⟨(j1 + a').toNat, by
      rw [Int.toNat_of_nonneg]; rw [abs_le] at b1 c1; push_cast [m] at b1 c1 hj1 ⊢; omega⟩
    have g1 : gz (piW L) ((1 : Fin 3), J) = (1, j1) := gz_ray1 a b J j1 hj1
    have g2 : gz (piW L') ((1 : Fin 3), j2) = (1, j1) := gz_ray1 a' b' j2 j1 (by omega)
    have hδ : ((gz (piW L'))⁻¹ * gz (piW L)) ((1 : Fin 3), J) = (1, j2) := by
      rw [Equiv.Perm.mul_apply, g1, Equiv.Perm.inv_eq_iff_eq, g2]
    have hfar1 : ((1 : Fin 3), J) ∉ YR (2 * m + 3) := by rw [mem_YR]; simp [ht, J]
    have hfar2 : ((gz (piW L'))⁻¹ * gz (piW L)) ((1 : Fin 3), J) ∉ YR (2 * m + 3) := by
      rw [hδ, mem_YR]; simp only [ht]; rw [abs_le] at b1 c1; push_cast [m] at b1 c1; omega
    have := fix_of_realF hrel _ hfar1 hfar2
    rw [hδ] at this
    have : j2 = J := by simpa using this
    omega
  have e2 : b = b' := by
    obtain ⟨j1, hj1⟩ : ∃ j1 : ℕ, (j1 : ℤ) = J - b := ⟨(J - b).toNat, by
      rw [Int.toNat_of_nonneg]; rw [abs_le] at b2; push_cast [m] at b2 ⊢; omega⟩
    obtain ⟨j2, hj2⟩ : ∃ j2 : ℕ, (j2 : ℤ) = j1 + b' := ⟨(j1 + b').toNat, by
      rw [Int.toNat_of_nonneg]; rw [abs_le] at b2 c2; push_cast [m] at b2 c2 hj1 ⊢; omega⟩
    have g1 : gz (piW L) ((2 : Fin 3), J) = (2, j1) := gz_ray2 a b J j1 hj1
    have g2 : gz (piW L') ((2 : Fin 3), j2) = (2, j1) := gz_ray2 a' b' j2 j1 (by omega)
    have hδ : ((gz (piW L'))⁻¹ * gz (piW L)) ((2 : Fin 3), J) = (2, j2) := by
      rw [Equiv.Perm.mul_apply, g1, Equiv.Perm.inv_eq_iff_eq, g2]
    have hfar1 : ((2 : Fin 3), J) ∉ YR (2 * m + 3) := by rw [mem_YR]; simp [ht, J]
    have hfar2 : ((gz (piW L'))⁻¹ * gz (piW L)) ((2 : Fin 3), J) ∉ YR (2 * m + 3) := by
      rw [hδ, mem_YR]; simp only [ht]; rw [abs_le] at b2 c2; push_cast [m] at b2 c2; omega
    have := fix_of_realF hrel _ hfar1 hfar2
    rw [hδ] at this
    have : j2 = J := by simpa using this
    omega
  exact Prod.ext e1 e2

/-! ### `Θ` depends only on the realization -/

namespace Hash

theorem realF_congr {R : ℕ} {γ γ' : KW (PR R)} (hg : γ.g = γ'.g) (hl : γ.lam = γ'.lam) :
    realF R γ = realF R γ' := by
  funext x; simp only [realF, hg, hl]

theorem KW_ext {P : Type*} [Fintype P] [DecidableEq P] {γ γ' : KW P} (hg : γ.g = γ'.g)
    (hl : γ.lam = γ'.lam) : γ = γ' := by
  cases γ; cases γ'; simp only at hg hl; subst hg; subst hl; rfl

theorem Theta_congr {R k : ℕ} {γ γ' : KW (PR R)} (h : realF R γ = realF R γ') :
    Theta k γ = Theta k γ' := by
  obtain ⟨hg, hl⟩ := realF_inj R (by funext x; exact congrFun h x)
  rw [KW_ext hg hl]

end Hash

/-! ### The torus clock -/

section clock

variable (m : ℕ)

/-- Integer representative in `[-m, m]` of a point of `ℤ/(2m+1)`. -/
def rep (x : ZMod (2 * m + 1)) : ℤ := (x.val : ℤ) - m

theorem rep_bound (x : ZMod (2 * m + 1)) : |rep m x| ≤ m := by
  have := ZMod.val_lt x
  rw [abs_le]; unfold rep; constructor <;> omega

theorem rep_add (x : ZMod (2 * m + 1)) (c : ℤ) (h : |rep m x + c| ≤ m) :
    rep m (x + (c : ZMod (2 * m + 1))) = rep m x + c := by
  rw [abs_le] at h
  have hx : x = (((x.val : ℤ)) : ZMod (2 * m + 1)) := by simp
  have key : x + (c : ZMod (2 * m + 1)) = (((x.val : ℤ) + c : ℤ) : ZMod (2 * m + 1)) := by
    conv_lhs => rw [hx]
    push_cast; ring
  have hval : (((((x.val : ℤ) + c : ℤ)) : ZMod (2 * m + 1)).val : ℤ) = (x.val : ℤ) + c := by
    rw [ZMod.val_intCast]; unfold rep at h
    apply Int.emod_eq_of_lt <;> push_cast <;> omega
  unfold rep at h ⊢
  rw [key, hval]; ring

theorem card_bad (ℓ : ℕ) :
    (Finset.univ.filter fun x : ZMod (2 * m + 1) => ¬ (|rep m x| + ℓ ≤ m)).card ≤ 2 * ℓ := by
  have hsub : (Finset.univ.filter fun x : ZMod (2 * m + 1) => ¬ (|rep m x| + ℓ ≤ m)).map
      ⟨ZMod.val, ZMod.val_injective _⟩ ⊆ Finset.range ℓ ∪ Finset.Ico (2 * m + 1 - ℓ) (2 * m + 1) := by
    intro n hn
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.Embedding.coeFn_mk] at hn
    obtain ⟨x, hx, rfl⟩ := hn
    have := ZMod.val_lt x
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
    unfold rep at hx
    rcases abs_cases ((x.val : ℤ) - m) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] at hx <;> omega
  have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  simp only [Finset.card_map, Finset.card_range, Nat.card_Ico] at this
  omega

end clock

/-! ### The model: a skew product over the torus clock -/

section model

variable (hspec : LetterCocycleSpec) (m k : ℕ)

abbrev Clk := ZMod (2 * m + 1) × ZMod (2 * m + 1)
abbrev Om := Hp (PR (2 * m + 3)) k × (Code k → Equiv.Perm (Fin 3))

def repC (x : Clk m) : ℤ × ℤ := (rep m x.1, rep m x.2)
def castC (c : ℤ × ℤ) : Clk m := ((c.1 : ZMod (2 * m + 1)), (c.2 : ZMod (2 * m + 1)))

theorem castC_add (c c' : ℤ × ℤ) : castC m (c + c') = castC m c + castC m c' := by
  simp [castC]

/-- Clocks where the telescoped cocycle of `L` is defined. -/
def GoodL (L : List (Fin 5 × Bool)) (x : Clk m) : Prop :=
  |rep m x.1| + L.length ≤ m ∧ |rep m x.2| + L.length ≤ m

open Classical in
/-- The telescoped cocycle of `L` at the clock `x`. -/
noncomputable def psiK (L : List (Fin 5 × Bool)) (x : Clk m) : KW (PR (2 * m + 3)) :=
  if h : GoodL m L x then Classical.choose (telescope hspec m L (repC m x) h.1 h.2) else KW.one

theorem psiK_spec {L : List (Fin 5 × Bool)} {x : Clk m} (h : GoodL m L x) :
    realF (2 * m + 3) (psiK hspec m L x) =
        ⇑(ρΓ ((gzW (repC m x + piW L))⁻¹ * FreeGroup.mk L * gzW (repC m x))) ∧
      (supp (psiK hspec m L x)).card ≤ L.length := by
  unfold psiK
  rw [dif_pos h]
  exact Classical.choose_spec (telescope hspec m L (repC m x) h.1 h.2)

open Classical in
/-- The fibre maps of the model. -/
noncomputable def TK (L : List (Fin 5 × Bool)) (x : Clk m) : Equiv.Perm (Om m k) :=
  if GoodL m L x then Theta k (psiK hspec m L x) else 1

/-- The model permutation of a word. -/
noncomputable def FK (L : List (Fin 5 × Bool)) : Equiv.Perm (Clk m × Om m k) :=
  Skew.skew (castC m (piW L)) (TK hspec m k L)

theorem piW_append (L L' : List (Fin 5 × Bool)) : piW (L ++ L') = piW L + piW L' := by
  simp [piW, List.map_append, List.sum_append]

theorem offDiag_le (S : Finset (Finset (PR (2 * m + 3)))) (n : ℕ) (h : S.card ≤ n) :
    S.offDiag.card ≤ n * (n - 1) := by
  rw [Finset.offDiag_card]
  calc S.card * S.card - S.card = S.card * (S.card - 1) := by
        rw [Nat.mul_sub_one]
    _ ≤ n * (n - 1) := Nat.mul_le_mul h (Nat.sub_le_sub_right h 1)

/-- **Defect at one clock** (Lemma `lem:hash`(i) along the cocycles): for words `L_g, L_h, L_gh`
of length `≤ ℓ` with `L_g L_h = L_gh` in `Γ`, at a clock with `|z_i| + 2ℓ ≤ m`, the two sides
differ on at most `2ℓ(2ℓ-1) |Ω| / 2^k` states. -/
theorem defect_clock (ℓ : ℕ) (Lg Lh Lgh : List (Fin 5 × Bool)) (hg : Lg.length ≤ ℓ)
    (hh : Lh.length ≤ ℓ) (hgh : Lgh.length ≤ ℓ)
    (hrel : ρΓ (FreeGroup.mk Lg * FreeGroup.mk Lh) = ρΓ (FreeGroup.mk Lgh))
    (x : Clk m) (hx1 : |rep m x.1| + 2 * ℓ ≤ m) (hx2 : |rep m x.2| + 2 * ℓ ≤ m) :
    (Finset.univ.filter fun ω : Om m k =>
        TK hspec m k Lg (x + castC m (piW Lh)) (TK hspec m k Lh x ω) ≠ TK hspec m k Lgh x ω).card *
        2 ^ k ≤ (2 * ℓ) * (2 * ℓ - 1) * Fintype.card (Om m k) := by
  have hπ : piW Lgh = piW Lg + piW Lh := by
    rw [← piW_append]; apply piW_eq hspec
    rw [← FreeGroup.mul_mk, hrel]
  obtain ⟨c1, c2⟩ := piW_abs Lh
  set x' := x + castC m (piW Lh)
  have hr1 : rep m x'.1 = rep m x.1 + (piW Lh).1 := by
    apply rep_add; have := abs_add_le (rep m x.1) (piW Lh).1; push_cast at *; linarith
  have hr2 : rep m x'.2 = rep m x.2 + (piW Lh).2 := by
    apply rep_add; have := abs_add_le (rep m x.2) (piW Lh).2; push_cast at *; linarith
  have hrep' : repC m x' = repC m x + piW Lh := by
    simp only [repC, hr1, hr2]; rfl
  have gh : GoodL m Lh x := ⟨by push_cast at *; omega, by push_cast at *; omega⟩
  have ggh : GoodL m Lgh x := ⟨by push_cast at *; omega, by push_cast at *; omega⟩
  have gg : GoodL m Lg x' := by
    refine ⟨?_, ?_⟩
    · rw [hr1]; have := abs_add_le (rep m x.1) (piW Lh).1; push_cast at *; linarith
    · rw [hr2]; have := abs_add_le (rep m x.2) (piW Lh).2; push_cast at *; linarith
  simp only [TK, if_pos gh, if_pos ggh, if_pos gg]
  obtain ⟨rg, sg⟩ := psiK_spec hspec m gg
  obtain ⟨rh, sh⟩ := psiK_spec hspec m gh
  obtain ⟨rgh, sgh⟩ := psiK_spec hspec m ggh
  set γ₁ := psiK hspec m Lg x'
  set γ₂ := psiK hspec m Lh x
  have hmul : Theta k (KW.mul γ₁ γ₂) = Theta k (psiK hspec m Lgh x) := by
    apply Theta_congr
    funext y
    rw [realF_mul, rg, rh, rgh, ← Equiv.Perm.mul_apply, ← map_mul, hrep', hπ]
    have : ρΓ ((gzW (repC m x + piW Lh + piW Lg))⁻¹ * FreeGroup.mk Lg *
        gzW (repC m x + piW Lh) * ((gzW (repC m x + piW Lh))⁻¹ * FreeGroup.mk Lh *
          gzW (repC m x))) = ρΓ ((gzW (repC m x + (piW Lg + piW Lh)))⁻¹ *
          (FreeGroup.mk Lg * FreeGroup.mk Lh) * gzW (repC m x)) := by
      congr 1; rw [show repC m x + piW Lh + piW Lg = repC m x + (piW Lg + piW Lh) by abel]; group
    rw [this, map_mul, map_mul, hrel, ← map_mul, ← map_mul]
  set S := supp γ₁ ∪ (supp γ₂).map γ₁.g.toEmbedding
  have hS : S.card ≤ 2 * ℓ :=
    (Finset.card_union_le _ _).trans (by simp only [Finset.card_map]; omega)
  have hcount := Theta_mul_card k γ₁ γ₂ S
    (fun w hw => Finset.mem_union_left _ ((mem_supp γ₁ w).mpr hw))
    (fun v hv => Finset.mem_union_right _ (Finset.mem_map_equiv.mpr (by
      rw [Equiv.symm_apply_apply]; exact (mem_supp γ₂ v).mpr hv)))
  rw [hmul] at hcount
  exact hcount.trans (Nat.mul_le_mul_right _ (offDiag_le m S _ hS))

/-- **Separation at one clock** (Lemma `lem:hash`(ii) along the cocycles): words of length `≤ ℓ`
representing different elements with the same clock step agree, at a clock with `|z_i| + ℓ ≤ m`,
on at most `2ℓ(2ℓ-1) |Ω| / 2^k` states. -/
theorem sep_clock (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (Lg Lh : List (Fin 5 × Bool)) (hg : Lg.length ≤ ℓ)
    (hh : Lh.length ≤ ℓ) (hne : ρΓ (FreeGroup.mk Lg) ≠ ρΓ (FreeGroup.mk Lh))
    (hπ : piW Lg = piW Lh) (x : Clk m) (hx1 : |rep m x.1| + ℓ ≤ m) (hx2 : |rep m x.2| + ℓ ≤ m) :
    (Finset.univ.filter fun ω : Om m k => TK hspec m k Lg x ω = TK hspec m k Lh x ω).card *
        2 ^ k ≤ (2 * ℓ) * (2 * ℓ - 1) * Fintype.card (Om m k) := by
  have gg : GoodL m Lg x := ⟨by push_cast at *; omega, by push_cast at *; omega⟩
  have gh : GoodL m Lh x := ⟨by push_cast at *; omega, by push_cast at *; omega⟩
  simp only [TK, if_pos gg, if_pos gh]
  obtain ⟨rg, sg⟩ := psiK_spec hspec m gg
  obtain ⟨rh, sh⟩ := psiK_spec hspec m gh
  set γ₁ := psiK hspec m Lg x
  set γ₂ := psiK hspec m Lh x
  have hdiff : γ₁.g ≠ γ₂.g ∨ ∃ w, γ₁.lam w ≠ γ₂.lam w := by
    by_contra hc
    push Not at hc
    have heq := realF_congr (R := 2 * m + 3) hc.1 (funext hc.2)
    rw [rg, rh, hπ] at heq
    apply hne
    have := congrArg (fun f => (ρΓ (gzW (repC m x + piW Lh))) * f * (ρΓ (gzW (repC m x)))⁻¹)
      (DFunLike.coe_injective heq)
    simp only [map_mul, map_inv] at this
    simpa [mul_assoc] using this
  set S := supp γ₁ ∪ supp γ₂
  have hS : S.card ≤ 2 * ℓ := (Finset.card_union_le _ _).trans (by omega)
  have hcount := Theta_ne_card k γ₁ γ₂ S
    (fun w hw => Finset.mem_union_left _ ((mem_supp γ₁ w).mpr hw))
    (fun w hw => Finset.mem_union_right _ ((mem_supp γ₂ w).mpr hw)) hdiff
  refine hcount.trans (Nat.mul_le_mul_right _ (max_le (offDiag_le m S _ hS) ?_))
  have : 1 ≤ 2 * ℓ - 1 := by omega
  nlinarith

/-! ### Summation over the clock -/

theorem sum_split {C : Type*} [Fintype C] (f : C → ℕ) (good : C → Prop) [DecidablePred good]
    (A B : ℝ) (hA : 0 ≤ A) (hgood : ∀ x, good x → (f x : ℝ) ≤ A) (hbad : ∀ x, (f x : ℝ) ≤ B) :
    (∑ x, (f x : ℝ)) ≤ Fintype.card C * A +
      (Finset.univ.filter fun x => ¬ good x).card * B := by
  calc (∑ x, (f x : ℝ)) ≤ ∑ x, (A + if good x then 0 else B) := by
        apply Finset.sum_le_sum; intro x _
        by_cases h : good x
        · simp [h, hgood x h]
        · simp only [h, if_false]; linarith [hbad x]
    _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul]

theorem card_bad2 (ℓ : ℕ) :
    (Finset.univ.filter fun x : Clk m => ¬ (|rep m x.1| + ℓ ≤ m ∧ |rep m x.2| + ℓ ≤ m)).card ≤
      2 * (2 * ℓ * (2 * m + 1)) := by
  have hsub : (Finset.univ.filter fun x : Clk m => ¬ (|rep m x.1| + ℓ ≤ m ∧ |rep m x.2| + ℓ ≤ m)) ⊆
      ((Finset.univ.filter fun a : ZMod (2 * m + 1) => ¬ (|rep m a| + ℓ ≤ m)) ×ˢ Finset.univ) ∪
      (Finset.univ ×ˢ (Finset.univ.filter fun a : ZMod (2 * m + 1) => ¬ (|rep m a| + ℓ ≤ m))) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and_or] at hx
    simp only [Finset.mem_union, Finset.mem_product, Finset.mem_filter, Finset.mem_univ,
      true_and, and_true]
    exact hx
  refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
  rw [Finset.card_product, Finset.card_product, Finset.card_univ, ZMod.card]
  have := card_bad m ℓ
  nlinarith

end model

section final

variable (hspec : LetterCocycleSpec) (m k : ℕ)

theorem Theta_one (R k : ℕ) : Theta k (KW.one : KW (PR R)) = 1 := by
  refine Equiv.ext fun ω => Prod.ext ?_ (funext fun z => ?_)
  · show compH k ω.1 (Equiv.refl _).symm = ω.1
    exact hp_ext k fun v => by
      rw [evalH_compH (P := PR R) k ω.1 (g := (Equiv.refl _).symm) (KW.one : KW (PR R)).hgi]; rfl
  · show hashF k (fun _ => 1) _ z * ω.2 z = ω.2 z
    rw [hashF_eq_one k _ _ _ (fun x hx => absurd rfl hx), one_mul]

theorem TK_nil : TK hspec m k [] = fun _ => 1 := by
  funext x
  unfold TK
  split_ifs with h
  · rw [← Theta_one (2 * m + 3) k]
    apply Theta_congr
    rw [(psiK_spec hspec m h).1]
    have : (gzW (repC m x + piW []))⁻¹ * FreeGroup.mk [] * gzW (repC m x) = 1 := by
      rw [show FreeGroup.mk ([] : List (Fin 5 × Bool)) = 1 from rfl]; simp [piW]
    rw [this, map_one]
    funext ⟨v, s⟩
    show (v, s) = realF _ KW.one (v, s)
    simp only [realF, KW.one, Equiv.refl_apply, ite_self, one_mul, split]
  · rfl

theorem FK_nil : FK hspec m k [] = 1 := by
  unfold FK
  rw [TK_nil]
  refine Equiv.ext fun x => ?_
  simp only [Skew.skew_apply, piW, castC, List.map_nil, List.sum_nil, Prod.fst_zero,
    Prod.snd_zero, Int.cast_zero, Equiv.Perm.coe_one, id_eq]
  exact Prod.ext (by simp [Prod.ext_iff]) rfl

open Classical in
/-- A word of length `≤ ℓ` for each element (the empty word for `1`). -/
noncomputable def wd (ℓ : ℕ) (g : Γ) : List (Fin 5 × Bool) :=
  if g = 1 then [] else
    if h : ∃ L : List (Fin 5 × Bool), L.length ≤ ℓ ∧ ρΓ' (FreeGroup.mk L) = g then
      Classical.choose h else []

theorem wd_spec (ℓ : ℕ) {g : Γ}
    (hg : ∃ L : List (Fin 5 × Bool), L.length ≤ ℓ ∧ ρΓ' (FreeGroup.mk L) = g) :
    (wd ℓ g).length ≤ ℓ ∧ ρΓ' (FreeGroup.mk (wd ℓ g)) = g := by
  unfold wd
  split_ifs with h1
  · subst h1; exact ⟨by simp, by rw [show FreeGroup.mk ([] : List (Fin 5 × Bool)) = 1 from rfl,
      map_one]⟩
  · exact Classical.choose_spec hg

theorem wd_one (ℓ : ℕ) : wd ℓ 1 = [] := by unfold wd; simp

theorem rho_of_rho' (w : F) : ρΓ w = (ρΓ' w : Equiv.Perm X) := rfl

theorem castC_inj (ℓ : ℕ) (hm : ℓ ≤ m) {c c' : ℤ × ℤ} (h1 : |c.1| ≤ ℓ) (h2 : |c.2| ≤ ℓ)
    (h1' : |c'.1| ≤ ℓ) (h2' : |c'.2| ≤ ℓ) (h : castC m c = castC m c') : c = c' := by
  simp only [castC, Prod.mk.injEq] at h
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub, ZMod.intCast_eq_intCast_iff_dvd_sub] at h
  obtain ⟨⟨q1, hq1⟩, ⟨q2, hq2⟩⟩ := h
  rw [abs_le] at h1 h2 h1' h2'
  have e1 : q1 = 0 := by
    by_contra hq; rcases lt_or_gt_of_ne hq with hq | hq <;> push_cast at hq1 <;> nlinarith
  have e2 : q2 = 0 := by
    by_contra hq; rcases lt_or_gt_of_ne hq with hq | hq <;> push_cast at hq2 <;> nlinarith
  rw [e1, mul_zero, sub_eq_zero] at hq1
  rw [e2, mul_zero, sub_eq_zero] at hq2
  exact Prod.ext hq1.symm hq2.symm

theorem card_Clk : Fintype.card (Clk m) = (2 * m + 1) * (2 * m + 1) := by
  simp [Clk, Fintype.card_prod, ZMod.card]

include hspec in
/-- **Proposition `prop:upper` (model)**: under `LetterCocycleSpec`, for every chunk `E'` whose
elements are products of at most `ℓ` letters, the hashed skew product on `Clk m × Om m k` is a
`(1 - r⁻¹)`-expansive `r⁻¹`-morphism as soon as `8ℓ/(2m+1) + 2ℓ(2ℓ-1)/2^k ≤ r⁻¹`. -/
theorem model_mem (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hm : ℓ ≤ m) (E' : Finset Γ)
    (hE : ∀ g ∈ E', ∃ L : List (Fin 5 × Bool), L.length ≤ ℓ ∧ ρΓ' (FreeGroup.mk L) = g)
    (r : ℝ) (herr : 8 * ℓ / (2 * m + 1 : ℝ) + 2 * ℓ * (2 * ℓ - 1) / 2 ^ k ≤ r⁻¹) :
    Fintype.card (Clk m × Om m k) ∈ Houghton.modelSizes E' r := by
  classical
  set e := Fintype.equivFin (Clk m × Om m k)
  set N : ℝ := 2 * m + 1 with hN
  have hNpos : (0 : ℝ) < N := by positivity
  have hOm : (0 : ℝ) < Fintype.card (Om m k) := by exact_mod_cast Fintype.card_pos
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have hX : (Fintype.card (Clk m × Om m k) : ℝ) = N * N * Fintype.card (Om m k) := by
    rw [Fintype.card_prod, card_Clk]; push_cast; ring
  set A : ℝ := 2 * ℓ * (2 * ℓ - 1) * Fintype.card (Om m k) / 2 ^ k with hA
  have hA0 : 0 ≤ A := by
    have : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    rw [hA]; apply div_nonneg _ h2k.le; apply mul_nonneg _ (Nat.cast_nonneg _); nlinarith
  have hAnat : ∀ n : ℕ, n * 2 ^ k ≤ (2 * ℓ) * (2 * ℓ - 1) * Fintype.card (Om m k) → (n : ℝ) ≤ A := by
    intro n hn
    rw [hA, le_div_iff₀ h2k]
    have : ((n * 2 ^ k : ℕ) : ℝ) ≤ (((2 * ℓ) * (2 * ℓ - 1) * Fintype.card (Om m k) : ℕ) : ℝ) := by
      exact_mod_cast hn
    have hsub : (((2 * ℓ - 1 : ℕ)) : ℝ) = 2 * ℓ - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    push_cast [hsub] at this
    linarith
  refine ⟨Fintype.card_pos, fun g => e.permCongr (FK hspec m k (wd ℓ g)), ⟨?_, ?_⟩, ?_⟩
  · -- `f 1 = 1`
    show e.permCongr (FK hspec m k (wd ℓ 1)) = 1
    rw [wd_one, FK_nil]; ext x; simp
  · -- defect
    intro x hx y hy hxy
    obtain ⟨lx, rx⟩ := wd_spec ℓ (hE x hx)
    obtain ⟨ly, ry⟩ := wd_spec ℓ (hE y hy)
    obtain ⟨lxy, rxy⟩ := wd_spec ℓ (hE _ hxy)
    set Lx := wd ℓ x; set Ly := wd ℓ y; set Lxy := wd ℓ (x * y)
    have hrel : ρΓ (FreeGroup.mk Lx * FreeGroup.mk Ly) = ρΓ (FreeGroup.mk Lxy) := by
      rw [rho_of_rho', rho_of_rho', map_mul, rx, ry, rxy]
    have hπ : piW Lxy = piW Lx + piW Ly := by
      rw [← piW_append]; apply piW_eq hspec; rw [← FreeGroup.mul_mk, hrel]
    show Houghton.dH (e.permCongr (FK hspec m k Lxy))
      (e.permCongr (FK hspec m k Lx) * e.permCongr (FK hspec m k Ly)) ≤ r⁻¹
    rw [← Equiv.permCongr_mul, Houghton.ham_permCongr, Houghton.ham_comm]
    have hF : FK hspec m k Lxy = Skew.skew (castC m (piW Lx) + castC m (piW Ly)) (TK hspec m k Lxy) := by
      unfold FK; rw [hπ, castC_add]
    unfold Houghton.dH
    rw [hF]
    have hcount := Skew.card_skew_mul_ne (castC m (piW Lx)) (castC m (piW Ly))
      (TK hspec m k Lx) (TK hspec m k Ly) (TK hspec m k Lxy)
    have hsum := sum_split (fun z : Clk m => (Finset.univ.filter fun ω : Om m k =>
        TK hspec m k Lx (z + castC m (piW Ly)) (TK hspec m k Ly z ω) ≠ TK hspec m k Lxy z ω).card)
      (fun z => |rep m z.1| + ((2 * ℓ : ℕ) : ℤ) ≤ m ∧ |rep m z.2| + ((2 * ℓ : ℕ) : ℤ) ≤ m) A
      (Fintype.card (Om m k)) hA0
      (fun z hz => hAnat _ (defect_clock hspec m k ℓ Lx Ly Lxy lx ly lxy hrel z
        (by have := hz.1; push_cast at this; exact this)
        (by have := hz.2; push_cast at this; exact this)))
      (fun z => by exact_mod_cast Finset.card_le_univ _)
    have hbad := card_bad2 m (2 * ℓ)
    have hcount' : ((Finset.univ.filter fun a : Clk m × Om m k =>
        (FK hspec m k Lx * FK hspec m k Ly) a ≠
          Skew.skew (castC m (piW Lx) + castC m (piW Ly)) (TK hspec m k Lxy) a).card : ℝ) ≤
        N * N * A + 8 * ℓ * N * Fintype.card (Om m k) := by
      have h1 : ((Finset.univ.filter fun a : Clk m × Om m k =>
          (FK hspec m k Lx * FK hspec m k Ly) a ≠
            Skew.skew (castC m (piW Lx) + castC m (piW Ly)) (TK hspec m k Lxy) a).card : ℝ) ≤
          ∑ z : Clk m, ((Finset.univ.filter fun ω : Om m k => TK hspec m k Lx (z + castC m (piW Ly))
            (TK hspec m k Ly z ω) ≠ TK hspec m k Lxy z ω).card : ℝ) := by
        exact_mod_cast hcount
      have h3 : ((Finset.univ.filter fun x : Clk m =>
          ¬(|rep m x.1| + ↑(2 * ℓ) ≤ ↑m ∧ |rep m x.2| + ↑(2 * ℓ) ≤ ↑m)).card : ℝ) ≤
          8 * ℓ * N := by
        have := hbad; rw [hN]; exact_mod_cast (by nlinarith : _ ≤ 8 * ℓ * (2 * m + 1))
      have hC : (Fintype.card (Clk m) : ℝ) = N * N := by rw [card_Clk]; push_cast; ring
      rw [hC] at hsum
      have hOm0 : (0 : ℝ) ≤ Fintype.card (Om m k) := Nat.cast_nonneg _
      nlinarith
    have hfil : (Finset.univ.filter fun a : Clk m × Om m k =>
        (FK hspec m k Lx * FK hspec m k Ly) a ≠
          Skew.skew (castC m (piW Lx) + castC m (piW Ly)) (TK hspec m k Lxy) a) =
        Finset.univ.filter fun a => (FK hspec m k Lx * FK hspec m k Ly) a ≠
          (Skew.skew (castC m (piW Lx) + castC m (piW Ly)) (TK hspec m k Lxy)) a := rfl
    rw [hX, div_le_iff₀ (by positivity)]
    calc _ ≤ N * N * A + 8 * ℓ * N * Fintype.card (Om m k) := hcount'
      _ = N * N * Fintype.card (Om m k) * (2 * ℓ * (2 * ℓ - 1) / 2 ^ k + 8 * ℓ / N) := by
          rw [hA]; field_simp
      _ ≤ N * N * Fintype.card (Om m k) * r⁻¹ := by
          apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = r⁻¹ * (N * N * Fintype.card (Om m k)) := by ring
  · -- separation
    intro x hx y hy hne
    obtain ⟨lx, rx⟩ := wd_spec ℓ (hE x hx)
    obtain ⟨ly, ry⟩ := wd_spec ℓ (hE y hy)
    set Lx := wd ℓ x; set Ly := wd ℓ y
    have hne' : ρΓ (FreeGroup.mk Lx) ≠ ρΓ (FreeGroup.mk Ly) := by
      rw [rho_of_rho', rho_of_rho', rx, ry]; exact fun h => hne (Subtype.ext h)
    show 1 - r⁻¹ ≤ Houghton.dH (e.permCongr (FK hspec m k Lx)) (e.permCongr (FK hspec m k Ly))
    rw [Houghton.ham_permCongr, Houghton.dH_eq_agree, hX]
    have hagree : (Houghton.agreeC (FK hspec m k Lx) (FK hspec m k Ly) : ℝ) ≤
        N * N * A + 4 * ℓ * N * Fintype.card (Om m k) := by
      have hsk := Skew.card_skew_eq (castC m (piW Lx)) (castC m (piW Ly)) (TK hspec m k Lx)
        (TK hspec m k Ly)
      unfold Houghton.agreeC
      change ((Finset.univ.filter fun a : Clk m × Om m k =>
        Skew.skew (castC m (piW Lx)) (TK hspec m k Lx) a =
          Skew.skew (castC m (piW Ly)) (TK hspec m k Ly) a).card : ℝ) ≤ _
      split_ifs at hsk with hc
      · obtain ⟨a1, a2⟩ := piW_abs Lx
        obtain ⟨b1, b2⟩ := piW_abs Ly
        have hπ : piW Lx = piW Ly := castC_inj m ℓ hm (a1.trans (by exact_mod_cast lx))
          (a2.trans (by exact_mod_cast lx)) (b1.trans (by exact_mod_cast ly))
          (b2.trans (by exact_mod_cast ly)) hc
        have hsum := sum_split (fun z : Clk m => (Finset.univ.filter fun ω : Om m k =>
            TK hspec m k Lx z ω = TK hspec m k Ly z ω).card)
          (fun z => |rep m z.1| + ((ℓ : ℕ) : ℤ) ≤ m ∧ |rep m z.2| + ((ℓ : ℕ) : ℤ) ≤ m) A
          (Fintype.card (Om m k)) hA0
          (fun z hz => hAnat _ (sep_clock hspec m k ℓ hℓ Lx Ly lx ly hne' hπ z hz.1 hz.2))
          (fun z => by exact_mod_cast Finset.card_le_univ _)
        have hbad := card_bad2 m ℓ
        have h3 : ((Finset.univ.filter fun x : Clk m =>
            ¬(|rep m x.1| + ((ℓ : ℕ) : ℤ) ≤ ↑m ∧ |rep m x.2| + ((ℓ : ℕ) : ℤ) ≤ ↑m)).card : ℝ) ≤
            4 * ℓ * N := by
          rw [hN]; exact_mod_cast (by nlinarith : _ ≤ 4 * ℓ * (2 * m + 1))
        have hC : (Fintype.card (Clk m) : ℝ) = N * N := by rw [card_Clk]; push_cast; ring
        rw [hC] at hsum
        have h1 : ((Finset.univ.filter fun a : Clk m × Om m k =>
            Skew.skew (castC m (piW Lx)) (TK hspec m k Lx) a =
              Skew.skew (castC m (piW Ly)) (TK hspec m k Ly) a).card : ℝ) ≤
            ∑ z : Clk m, ((Finset.univ.filter fun ω : Om m k =>
              TK hspec m k Lx z ω = TK hspec m k Ly z ω).card : ℝ) := by
          have h := (Nat.cast_le (α := ℝ)).mpr hsk; push_cast at h; convert h using 3; ext a; simp
        have hOm0 : (0 : ℝ) ≤ Fintype.card (Om m k) := Nat.cast_nonneg _
        nlinarith
      · have : ((Finset.univ.filter fun a : Clk m × Om m k =>
            Skew.skew (castC m (piW Lx)) (TK hspec m k Lx) a =
              Skew.skew (castC m (piW Ly)) (TK hspec m k Ly) a).card : ℝ) ≤ 0 := by
          have h := (Nat.cast_le (α := ℝ)).mpr hsk; push_cast at h; convert h using 3; ext a; simp
        have : (0 : ℝ) ≤ N * N * A + 4 * ℓ * N * Fintype.card (Om m k) := by positivity
        linarith
    have hfrac : (Houghton.agreeC (FK hspec m k Lx) (FK hspec m k Ly) : ℝ) /
        (N * N * Fintype.card (Om m k)) ≤ r⁻¹ := by
      rw [div_le_iff₀ (by positivity)]
      calc _ ≤ N * N * A + 4 * ℓ * N * Fintype.card (Om m k) := hagree
        _ = N * N * Fintype.card (Om m k) * (2 * ℓ * (2 * ℓ - 1) / 2 ^ k + 4 * ℓ / N) := by
            rw [hA]; field_simp
        _ ≤ N * N * Fintype.card (Om m k) * r⁻¹ := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            have : 4 * (ℓ : ℝ) / N ≤ 8 * ℓ / N := by
              apply div_le_div_of_nonneg_right _ hNpos.le; have : (0 : ℝ) ≤ ℓ := by positivity
              linarith
            linarith
        _ = r⁻¹ * (N * N * Fintype.card (Om m k)) := by ring
    linarith

end final

section theorem_upper

/-- Every word in `chunkWordsL` is the value of a letter word of length `≤ 24`. -/
theorem chunk_words : ∀ w ∈ chunkWordsL, ∃ L : List (Fin 5 × Bool), L.length ≤ 24 ∧
    FreeGroup.mk L = w := by
  intro w hw
  unfold chunkWordsL at hw
  rcases List.mem_append.mp hw with h | h
  · refine ⟨w.toWord, ?_, FreeGroup.mk_toWord⟩
    have key : ∀ v ∈ genWords, v.toWord.length ≤ 24 := by decide +kernel
    exact key w h
  · obtain ⟨i, -, hi⟩ := List.mem_flatMap.mp h
    unfold prefixesF at hi
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hi
    have key : ∀ i : Fin 25, (rel i).toWord.length ≤ 24 := by decide +kernel
    exact ⟨List.take j _, by rw [List.length_take]; exact (min_le_right _ _).trans (key i), rfl⟩

/-- Every element of the chunk `E` is the value of a letter word of length `≤ 24`. -/
theorem E_words (g : Γ) (hg : g ∈ E) :
    ∃ L : List (Fin 5 × Bool), L.length ≤ 24 ∧ ρΓ' (FreeGroup.mk L) = g := by
  classical
  unfold E at hg
  rcases Finset.mem_union.mp hg with h | h
  · rw [List.mem_toFinset] at h
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp h
    obtain ⟨L, hL, rfl⟩ := chunk_words w hw
    exact ⟨L, hL, rfl⟩
  · rw [List.mem_toFinset] at h
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp h
    obtain ⟨L, hL, rfl⟩ := chunk_words w hw
    exact ⟨FreeGroup.invRev L, by rw [FreeGroup.invRev_length]; exact hL,
      by rw [← FreeGroup.inv_mk, map_inv]⟩

/-- The size of the model. -/
theorem card_model (m k : ℕ) : Fintype.card (Clk m × Om m k) =
    (2 * m + 1) ^ 2 * 2 ^ (k * (6 * m + 10)) * 6 ^ (2 ^ k) := by
  have hP : Fintype.card (PR (2 * m + 3)) = 6 * m + 9 := by
    rw [Fintype.card_coe, YR, Finset.card_product, Finset.card_univ, Fintype.card_fin,
      Finset.card_range]; ring
  simp only [Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_fin, hP,
    Fintype.card_perm, Nat.factorial_succ, Nat.factorial_zero]
  ring

/-- **Upper bound for Theorem A (from the letter-cocycle interface).** For `r ≥ 2` the chunk `E`
has a sofic `1/r`-model of size at most `2 ^ (500 · 24² · r · log₂(2 + r))`. -/
theorem upper_bound_E (hspec : LetterCocycleSpec) (r : ℝ) (hr : 2 ≤ r) :
    ∃ n ∈ Houghton.modelSizes E r, (n : ℝ) ≤ 2 ^ (500 * 24 ^ 2 * r * Real.logb 2 (2 + r)) := by
  obtain ⟨h1, h2⟩ := UpperArith.upper_arith 24 (by norm_num) r (by linarith)
  refine ⟨_, model_mem hspec ⌈8 * ((24 : ℕ) : ℝ) * r⌉₊ ⌈Real.logb 2 (8 * ((24 : ℕ) : ℝ) ^ 2 * r)⌉₊
    24 (by norm_num) ?_ E E_words r ?_, ?_⟩
  · have : (24 : ℝ) ≤ ⌈8 * ((24 : ℕ) : ℝ) * r⌉₊ :=
      le_trans (by push_cast; nlinarith) (Nat.le_ceil _)
    exact_mod_cast this
  · rw [← one_div]; exact h1.le
  · rw [card_model]
    refine le_trans (Real.rpow_logb (b := 2) (by norm_num) (by norm_num) ?_).symm.le
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
    · positivity
    · rw [Nat.cast_ofNat] at h2
      exact h2

/-- **Profile form.** -/
theorem profile_upper_E (hspec : LetterCocycleSpec) (r : ℝ) (hr : 2 ≤ r) :
    ∃ n : ℕ, Houghton.profile E r ≤ n ∧
      (n : ℝ) ≤ 2 ^ (500 * 24 ^ 2 * r * Real.logb 2 (2 + r)) := by
  obtain ⟨n, hn, hle⟩ := upper_bound_E hspec r hr
  exact ⟨n, Houghton.profile_le_of_mem hn, hle⟩

end theorem_upper

end Lamps
