import Lamps.Upper
import Lamps.Clock
import Mathlib.Data.Fintype.Perm

/-!
# The hashed action `Θ` of the finite lamplighter group `K_W` (Lemma `lem:hash`)

`W = 𝔽₂^P` (configurations `Finset P`, `+ = ∆`); `K_W = S₃^W ⋊ AGL(W)`, an element is
`γ = (lam, g)` with `g` an affine bijection of `W`. The hash space is
`Ω = Hp P k × (Code k → S₃)` and `Θ_γ (η, u) = (η ∘ g⁻¹, lam^{η∘g⁻¹} · u)`, where `lam^η z` is the
product, in a fixed order of `W`, of the `lam w` with `η w = z`.
-/

namespace Lamps.Hash

open Finset
open scoped symmDiff

variable {P : Type*} [Fintype P] [DecidableEq P] (k : ℕ)

/-! ### Affine maps to codes and precomposition of hashes -/

/-- `f : W → 𝔽₂^k` is affine. -/
def IsAffineF (f : Finset P → Code k) : Prop := ∀ v w, f (v ∆ w) = f v + f w + f ∅

theorem affineF_eq (f : Finset P → Code k) (hf : IsAffineF k f) (v : Finset P) :
    f v = (∑ y ∈ v, (f {y} + f ∅)) + f ∅ := by
  induction v using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hs : insert a s = s ∆ {a} := by
      ext x; by_cases hx : x = a
      · subst hx; simp [Finset.mem_symmDiff, ha]
      · simp [Finset.mem_symmDiff, hx]
    rw [hs, hf, ih, ← hs, Finset.sum_insert ha]
    abel

theorem evalH_affine (h : Hp P k) : IsAffineF k (evalH k h) := by
  intro v w
  unfold evalH
  rw [← sum_add_sum, Finset.sum_empty, zero_add]
  have := code_add_self k h.2
  calc (∑ y ∈ v, h.1 y + ∑ y ∈ w, h.1 y) + h.2
      = (∑ y ∈ v, h.1 y + ∑ y ∈ w, h.1 y) + h.2 + (h.2 + h.2) := by rw [this, add_zero]
    _ = ∑ y ∈ v, h.1 y + h.2 + (∑ y ∈ w, h.1 y + h.2) + h.2 := by abel

/-- Parameters are determined by the hash function. -/
theorem hp_ext {h h' : Hp P k} (H : ∀ v, evalH k h v = evalH k h' v) : h = h' := by
  have h2 : h.2 = h'.2 := by simpa [evalH] using H ∅
  refine Prod.ext (funext fun y => ?_) h2
  have := H {y}
  simp only [evalH, Finset.sum_singleton, h2] at this
  exact add_right_cancel this

/-- `W`-affine bijections. -/
def IsAffine (g : Finset P ≃ Finset P) : Prop := ∀ v w, g (v ∆ w) = g v ∆ g w ∆ g ∅

/-- Parameters of `η ∘ g` for an affine `g`. -/
def compH (h : Hp P k) (g : Finset P ≃ Finset P) : Hp P k :=
  (fun y => evalH k h (g {y}) + evalH k h (g ∅), evalH k h (g ∅))

theorem evalH_compH (h : Hp P k) {g : Finset P ≃ Finset P} (hg : IsAffine g) (v : Finset P) :
    evalH k (compH k h g) v = evalH k h (g v) := by
  have hf : IsAffineF k (fun v => evalH k h (g v)) := by
    intro v w
    simp only
    rw [hg, evalH_affine, evalH_affine]
    have := code_add_self k (evalH k h (g ∅))
    calc evalH k h (g v) + evalH k h (g w) + evalH k h ∅ + evalH k h (g ∅) + evalH k h ∅
        = evalH k h (g v) + evalH k h (g w) + evalH k h (g ∅) + (evalH k h ∅ + evalH k h ∅) := by
          abel
      _ = _ := by rw [code_add_self, add_zero]
  rw [affineF_eq k _ hf v]
  rfl

/-- Precomposition by an affine bijection is a bijection of the parameter space. -/
def compEquiv (g : Finset P ≃ Finset P) (hg : IsAffine g) (hgi : IsAffine g.symm) :
    Hp P k ≃ Hp P k where
  toFun h := compH k h g
  invFun h := compH k h g.symm
  left_inv h := hp_ext k fun v => by
    rw [evalH_compH k _ hgi, evalH_compH k _ hg, Equiv.apply_symm_apply]
  right_inv h := hp_ext k fun v => by
    rw [evalH_compH k _ hg, evalH_compH k _ hgi, Equiv.symm_apply_apply]

/-! ### The group `K_W` and `Θ` -/

/-- Elements of `K_W`. -/
structure KW (P : Type*) [Fintype P] [DecidableEq P] where
  g : Finset P ≃ Finset P
  hg : IsAffine g
  hgi : IsAffine g.symm
  lam : Finset P → Equiv.Perm (Fin 3)

/-- A fixed enumeration of `W`. -/
noncomputable def allCfg : List (Finset P) := (Finset.univ : Finset (Finset P)).toList

/-- `lam^η`. -/
noncomputable def hashF (lam : Finset P → Equiv.Perm (Fin 3)) (h : Hp P k) (z : Code k) :
    Equiv.Perm (Fin 3) :=
  (((allCfg (P := P)).filter fun v => evalH k h v = z).map lam).prod

/-- **`Θ_γ`** as a permutation of `Ω = Hp × (Code k → S₃)`. -/
noncomputable def Theta (γ : KW P) : Equiv.Perm (Hp P k × (Code k → Equiv.Perm (Fin 3))) where
  toFun ω := (compEquiv k γ.g.symm γ.hgi (by simpa using γ.hg) ω.1,
    fun z => hashF k γ.lam (compEquiv k γ.g.symm γ.hgi (by simpa using γ.hg) ω.1) z * ω.2 z)
  invFun ω := ((compEquiv k γ.g.symm γ.hgi (by simpa using γ.hg)).symm ω.1,
    fun z => (hashF k γ.lam ω.1 z)⁻¹ * ω.2 z)
  left_inv ω := by
    refine Prod.ext (Equiv.symm_apply_apply _ _) (funext fun z => ?_)
    simp
  right_inv ω := by
    refine Prod.ext (Equiv.apply_symm_apply _ _) (funext fun z => ?_)
    simp

/-! ### Products with a single nontrivial factor -/

theorem prod_single {α G : Type*} [DecidableEq α] [Monoid G] (f : α → G) (a : α) :
    ∀ l : List α, l.Nodup → (∀ x ∈ l, x ≠ a → f x = 1) →
      (l.map f).prod = if a ∈ l then f a else 1
  | [], _, _ => by simp
  | x :: l, hl, hf => by
    rw [List.nodup_cons] at hl
    have ih := prod_single f a l hl.2 (fun y hy hya => hf y (List.mem_cons_of_mem _ hy) hya)
    rw [List.map_cons, List.prod_cons, ih]
    by_cases hx : x = a
    · subst hx; simp [hl.1]
    · rw [hf x List.mem_cons_self hx, one_mul]
      by_cases ha : a ∈ l
      · simp [ha]
      · have : a ∉ x :: l := by simp [Ne.symm hx, ha]
        simp [ha, this]

theorem mem_allCfg (v : Finset P) : v ∈ allCfg (P := P) := by simp [allCfg]

theorem nodup_allCfg : (allCfg (P := P)).Nodup := Finset.nodup_toList _

/-- Evaluation of `lam^η` when at most one configuration `a` of the support hashes to `z`. -/
theorem hashF_eq (lam : Finset P → Equiv.Perm (Fin 3)) (h : Hp P k) (z : Code k) (a : Finset P)
    (ha : ∀ x, lam x ≠ 1 → evalH k h x = z → x = a) :
    hashF k lam h z = if evalH k h a = z then lam a else 1 := by
  unfold hashF
  rw [prod_single lam a _ (nodup_allCfg.filter _)]
  · simp [mem_allCfg]
  · intro x hx hxa
    by_contra hne
    simp only [List.mem_filter, decide_eq_true_eq] at hx
    exact hxa (ha x hne hx.2)

theorem hashF_eq_one (lam : Finset P → Equiv.Perm (Fin 3)) (h : Hp P k) (z : Code k)
    (ha : ∀ x, lam x ≠ 1 → evalH k h x ≠ z) : hashF k lam h z = 1 := by
  unfold hashF
  apply List.prod_eq_one
  intro y hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  simp only [List.mem_filter, decide_eq_true_eq] at hx
  by_contra hne
  exact ha x hne hx.2

/-! ### Products in `K_W` and Lemma `lem:hash`(i) -/

theorem isAffine_trans {g h : Finset P ≃ Finset P} (hg : IsAffine g) (hh : IsAffine h) :
    IsAffine (h.trans g) := by
  intro v w
  simp only [Equiv.trans_apply]
  rw [hh, hg, hg (h v)]
  ext x; simp only [Finset.mem_symmDiff]; tauto

/-- The product in `K_W`: `(λ, g)(μ, h) = (λ · gμ, gh)`. -/
def KW.mul (γ₁ γ₂ : KW P) : KW P where
  g := γ₂.g.trans γ₁.g
  hg := isAffine_trans γ₁.hg γ₂.hg
  hgi := by
    rw [Equiv.symm_trans]
    exact isAffine_trans γ₂.hgi γ₁.hgi
  lam w := γ₁.lam w * γ₂.lam (γ₁.g.symm w)

theorem Theta_fst (γ : KW P) (ω : Hp P k × (Code k → Equiv.Perm (Fin 3))) (v : Finset P) :
    evalH k (Theta k γ ω).1 v = evalH k ω.1 (γ.g.symm v) :=
  evalH_compH k ω.1 γ.hgi v

theorem Theta_snd (γ : KW P) (ω : Hp P k × (Code k → Equiv.Perm (Fin 3))) (z : Code k) :
    (Theta k γ ω).2 z = hashF k γ.lam (Theta k γ ω).1 z * ω.2 z := rfl

/-- **Lemma `lem:hash`(i)**, pointwise: if the final hash `η' = η ∘ (g₁g₂)⁻¹` is injective on a set
`S` containing the support of `λ₁` and the image under `g₁` of the support of `λ₂`, then
`Θ_{γ₁} Θ_{γ₂} ω = Θ_{γ₁γ₂} ω`. -/
theorem Theta_mul (γ₁ γ₂ : KW P) (ω : Hp P k × (Code k → Equiv.Perm (Fin 3)))
    (S : Finset (Finset P)) (h1 : ∀ w, γ₁.lam w ≠ 1 → w ∈ S)
    (h2 : ∀ v, γ₂.lam v ≠ 1 → γ₁.g v ∈ S)
    (hinj : ∀ v ∈ S, ∀ w ∈ S, evalH k (Theta k (KW.mul γ₁ γ₂) ω).1 v =
      evalH k (Theta k (KW.mul γ₁ γ₂) ω).1 w → v = w) :
    Theta k γ₁ (Theta k γ₂ ω) = Theta k (KW.mul γ₁ γ₂) ω := by
  set η' := (Theta k (KW.mul γ₁ γ₂) ω).1 with hη'def
  have hfst : (Theta k γ₁ (Theta k γ₂ ω)).1 = η' := hp_ext k fun v => by
    rw [Theta_fst, Theta_fst, hη'def, Theta_fst]; rfl
  have hη2 : ∀ v, evalH k (Theta k γ₂ ω).1 v = evalH k η' (γ₁.g v) := by
    intro v; rw [← hfst, Theta_fst (γ := γ₁), Equiv.symm_apply_apply]
  refine Prod.ext hfst (funext fun z => ?_)
  rw [Theta_snd, Theta_snd, Theta_snd, hfst, ← mul_assoc]
  congr 1
  by_cases hz : ∃ w ∈ S, evalH k η' w = z
  · obtain ⟨w, hwS, hwz⟩ := hz
    have e1 : hashF k γ₁.lam η' z = γ₁.lam w := by
      rw [hashF_eq k _ _ _ w (fun x hx hxz => hinj x (h1 x hx) w hwS (hxz.trans hwz.symm)),
        if_pos hwz]
    have e2 : hashF k γ₂.lam (Theta k γ₂ ω).1 z = γ₂.lam (γ₁.g.symm w) := by
      rw [hashF_eq k _ _ _ (γ₁.g.symm w) (fun x hx hxz => by
        rw [hη2] at hxz
        have := hinj _ (h2 x hx) w hwS (hxz.trans hwz.symm)
        rw [← this, Equiv.symm_apply_apply]), if_pos (by rw [hη2, Equiv.apply_symm_apply, hwz])]
    have e3 : hashF k (KW.mul γ₁ γ₂).lam η' z = γ₁.lam w * γ₂.lam (γ₁.g.symm w) := by
      rw [hashF_eq k _ _ _ w (fun x hx hxz => by
        have hxS : x ∈ S := by
          by_cases hl : γ₁.lam x = 1
          · have : γ₂.lam (γ₁.g.symm x) ≠ 1 := by
              intro h; apply hx; simp [KW.mul, hl, h]
            have := h2 _ this; rwa [Equiv.apply_symm_apply] at this
          · exact h1 x hl
        exact hinj x hxS w hwS (hxz.trans hwz.symm)), if_pos hwz]
      rfl
    rw [e1, e2, e3]
  · push Not at hz
    have e1 : hashF k γ₁.lam η' z = 1 :=
      hashF_eq_one k _ _ _ fun x hx => hz x (h1 x hx)
    have e2 : hashF k γ₂.lam (Theta k γ₂ ω).1 z = 1 :=
      hashF_eq_one k _ _ _ fun x hx => by rw [hη2]; exact hz _ (h2 x hx)
    have e3 : hashF k (KW.mul γ₁ γ₂).lam η' z = 1 :=
      hashF_eq_one k _ _ _ fun x hx => by
        apply hz
        by_cases hl : γ₁.lam x = 1
        · have : γ₂.lam (γ₁.g.symm x) ≠ 1 := by
            intro h; apply hx; simp [KW.mul, hl, h]
          have := h2 _ this; rwa [Equiv.apply_symm_apply] at this
        · exact h1 x hl
    rw [e1, e2, e3, one_mul]

/-- Hashes not injective on `S`. -/
abbrev NonInj (S : Finset (Finset P)) (h : Hp P k) : Prop :=
  ∃ v ∈ S, ∃ w ∈ S, v ≠ w ∧ evalH k h v = evalH k h w

theorem nonInj_card_equiv (S : Finset (Finset P)) (e : Hp P k ≃ Hp P k) :
    (univ.filter fun h => NonInj k S (e h)).card = (univ.filter fun h => NonInj k S h).card :=
  Finset.card_equiv e (by intro h; simp only [mem_filter, mem_univ, true_and])

/-- **Lemma `lem:hash`(i), counting form**: `Θ_{γ₁} Θ_{γ₂} ω = Θ_{γ₁γ₂} ω` for all but at most
`|S|(|S|-1) · |Ω| / 2^k` states `ω`, when `S` contains the support of `λ₁` and `g₁(supp λ₂)`. -/
theorem Theta_mul_card (γ₁ γ₂ : KW P) (S : Finset (Finset P))
    (h1 : ∀ w, γ₁.lam w ≠ 1 → w ∈ S) (h2 : ∀ v, γ₂.lam v ≠ 1 → γ₁.g v ∈ S) :
    (univ.filter fun ω : Hp P k × (Code k → Equiv.Perm (Fin 3)) =>
        Theta k γ₁ (Theta k γ₂ ω) ≠ Theta k (KW.mul γ₁ γ₂) ω).card * 2 ^ k ≤
      S.offDiag.card * Fintype.card (Hp P k × (Code k → Equiv.Perm (Fin 3))) := by
  set e := compEquiv k (KW.mul γ₁ γ₂).g.symm (KW.mul γ₁ γ₂).hgi
    (by simpa using (KW.mul γ₁ γ₂).hg)
  have hsub : (univ.filter fun ω : Hp P k × (Code k → Equiv.Perm (Fin 3)) =>
        Theta k γ₁ (Theta k γ₂ ω) ≠ Theta k (KW.mul γ₁ γ₂) ω) ⊆
      (univ.filter fun h => NonInj k S (e h)) ×ˢ univ := by
    intro ω hω
    simp only [mem_filter, mem_univ, true_and] at hω
    simp only [mem_product, mem_filter, mem_univ, true_and, and_true]
    by_contra hni
    apply hω
    apply Theta_mul k γ₁ γ₂ ω S h1 h2
    intro v hv w hw hvw
    by_contra hne
    exact hni ⟨v, hv, w, hw, hne, hvw⟩
  have hc := card_le_card hsub
  rw [card_product, nonInj_card_equiv, card_univ] at hc
  have hn : (univ.filter fun h => NonInj k S h).card * 2 ^ k ≤
      S.offDiag.card * Fintype.card (Hp P k) := noninj_card_le k S
  rw [Fintype.card_prod]
  calc _ ≤ (univ.filter fun h => NonInj k S h).card *
          Fintype.card (Code k → Equiv.Perm (Fin 3)) * 2 ^ k := Nat.mul_le_mul_right _ hc
    _ = (univ.filter fun h => NonInj k S h).card * 2 ^ k *
          Fintype.card (Code k → Equiv.Perm (Fin 3)) := by ring
    _ ≤ S.offDiag.card * Fintype.card (Hp P k) * Fintype.card (Code k → Equiv.Perm (Fin 3)) :=
          Nat.mul_le_mul_right _ hn
    _ = _ := by ring

/-- **Lemma `lem:hash`(ii), counting form**: if `γ₁ ≠ γ₂` (different affine parts, or lamp parts
differing somewhere) and `S` contains both lamp supports, then `Θ_{γ₁} ω ≠ Θ_{γ₂} ω` for all but at
most `max(|S|(|S|-1), 1) · |Ω| / 2^k` states. -/
theorem Theta_ne_card (γ₁ γ₂ : KW P) (S : Finset (Finset P))
    (h1 : ∀ w, γ₁.lam w ≠ 1 → w ∈ S) (h2 : ∀ w, γ₂.lam w ≠ 1 → w ∈ S)
    (hne : γ₁.g ≠ γ₂.g ∨ ∃ w, γ₁.lam w ≠ γ₂.lam w) :
    (univ.filter fun ω : Hp P k × (Code k → Equiv.Perm (Fin 3)) =>
        Theta k γ₁ ω = Theta k γ₂ ω).card * 2 ^ k ≤
      max S.offDiag.card 1 * Fintype.card (Hp P k × (Code k → Equiv.Perm (Fin 3))) := by
  rw [Fintype.card_prod]
  by_cases hg : γ₁.g = γ₂.g
  · -- equal affine parts: lamps differ at some `w₀ ∈ S`
    have hl : ∃ w, γ₁.lam w ≠ γ₂.lam w := hne.resolve_left (not_not.mpr hg)
    obtain ⟨w₀, hw₀⟩ := hl
    have hw₀S : w₀ ∈ S := by
      by_cases h : γ₁.lam w₀ = 1
      · exact h2 w₀ (by rw [← h]; exact Ne.symm hw₀)
      · exact h1 w₀ h
    set e := compEquiv k γ₁.g.symm γ₁.hgi (by simpa using γ₁.hg)
    have hsub : (univ.filter fun ω : Hp P k × (Code k → Equiv.Perm (Fin 3)) =>
          Theta k γ₁ ω = Theta k γ₂ ω) ⊆ (univ.filter fun h => NonInj k S (e h)) ×ˢ univ := by
      intro ω hω
      simp only [mem_filter, mem_univ, true_and] at hω
      simp only [mem_product, mem_filter, mem_univ, true_and, and_true]
      by_contra hni
      have hinj : ∀ v ∈ S, ∀ w ∈ S, evalH k (e ω.1) v = evalH k (e ω.1) w → v = w := by
        intro v hv w hw hvw; by_contra hvw'; exact hni ⟨v, hv, w, hw, hvw', hvw⟩
      have hfst1 : (Theta k γ₁ ω).1 = e ω.1 := rfl
      have hfst2 : (Theta k γ₂ ω).1 = e ω.1 := by rw [← hω, hfst1]
      have hz := congrFun (congrArg Prod.snd hω) (evalH k (e ω.1) w₀)
      rw [Theta_snd, Theta_snd, hfst1, hfst2, mul_left_inj,
        hashF_eq k _ _ _ w₀ (fun x hx hxz => hinj x (h1 x hx) w₀ hw₀S hxz), if_pos rfl,
        hashF_eq k _ _ _ w₀ (fun x hx hxz => hinj x (h2 x hx) w₀ hw₀S hxz), if_pos rfl] at hz
      exact hw₀ hz
    have hc := card_le_card hsub
    rw [card_product, nonInj_card_equiv, card_univ] at hc
    have hn : (univ.filter fun h => NonInj k S h).card * 2 ^ k ≤
        S.offDiag.card * Fintype.card (Hp P k) := noninj_card_le k S
    calc _ ≤ (univ.filter fun h => NonInj k S h).card *
            Fintype.card (Code k → Equiv.Perm (Fin 3)) * 2 ^ k := Nat.mul_le_mul_right _ hc
      _ = (univ.filter fun h => NonInj k S h).card * 2 ^ k *
            Fintype.card (Code k → Equiv.Perm (Fin 3)) := by ring
      _ ≤ S.offDiag.card * Fintype.card (Hp P k) * Fintype.card (Code k → Equiv.Perm (Fin 3)) :=
            Nat.mul_le_mul_right _ hn
      _ ≤ _ := by
            rw [mul_assoc]; exact Nat.mul_le_mul_right _ (le_max_left _ _)
  · -- different affine parts: a single collision
    have hsy : γ₁.g.symm ≠ γ₂.g.symm := fun h => hg (by simpa using congrArg Equiv.symm h)
    obtain ⟨v₀, hv₀⟩ : ∃ v, γ₁.g.symm v ≠ γ₂.g.symm v := by
      by_contra hc; push Not at hc; exact hsy (Equiv.ext hc)
    have hsub : (univ.filter fun ω : Hp P k × (Code k → Equiv.Perm (Fin 3)) =>
          Theta k γ₁ ω = Theta k γ₂ ω) ⊆
        (univ.filter fun h : Hp P k => evalH k h (γ₁.g.symm v₀) = evalH k h (γ₂.g.symm v₀)) ×ˢ
          univ := by
      intro ω hω
      simp only [mem_filter, mem_univ, true_and] at hω
      simp only [mem_product, mem_filter, mem_univ, true_and, and_true]
      have := congrArg (fun x => evalH k x.1 v₀) hω
      simp only [Theta_fst] at this
      exact this
    have hc := card_le_card hsub
    rw [card_product, card_univ] at hc
    have hcol := collide_card k hv₀
    calc _ ≤ (univ.filter fun h : Hp P k => evalH k h (γ₁.g.symm v₀) =
              evalH k h (γ₂.g.symm v₀)).card * Fintype.card (Code k → Equiv.Perm (Fin 3)) * 2 ^ k :=
          Nat.mul_le_mul_right _ hc
      _ = Fintype.card (Hp P k) * Fintype.card (Code k → Equiv.Perm (Fin 3)) := by
          rw [mul_right_comm, hcol]
      _ ≤ _ := by
          have := Nat.mul_le_mul_right (Fintype.card (Hp P k) *
            Fintype.card (Code k → Equiv.Perm (Fin 3))) (le_max_right S.offDiag.card 1)
          rwa [one_mul] at this

end Lamps.Hash

/-! ### Skew products over a clock (the models of Proposition `prop:upper`)

A model is a skew product `(z, ω) ↦ (z + c, T_z ω)` over a finite clock group `C` (a torus
`ZMod n × ZMod n` makes every generator a genuine permutation). The defect and separation of such
models reduce to clockwise counts. -/

namespace Lamps.Skew

open Finset

variable {C Ω : Type*} [AddCommGroup C] [Fintype C] [DecidableEq C] [Fintype Ω] [DecidableEq Ω]

/-- The skew product `(z, ω) ↦ (z + c, T_z ω)`. -/
def skew (c : C) (T : C → Equiv.Perm Ω) : Equiv.Perm (C × Ω) where
  toFun x := (x.1 + c, T x.1 x.2)
  invFun x := (x.1 - c, (T (x.1 - c)).symm x.2)
  left_inv x := by simp
  right_inv x := by simp

theorem skew_apply (c : C) (T : C → Equiv.Perm Ω) (x : C × Ω) :
    skew c T x = (x.1 + c, T x.1 x.2) := rfl

/-- Disagreement of `F₁ F₂` and `F₃` is counted clock by clock. -/
theorem card_skew_mul_ne (c₁ c₂ : C) (T₁ T₂ T₃ : C → Equiv.Perm Ω) :
    (univ.filter fun x : C × Ω => (skew c₁ T₁ * skew c₂ T₂) x ≠ skew (c₁ + c₂) T₃ x).card ≤
      ∑ z, (univ.filter fun ω : Ω => T₁ (z + c₂) (T₂ z ω) ≠ T₃ z ω).card := by
  have hsub : (univ.filter fun x : C × Ω => (skew c₁ T₁ * skew c₂ T₂) x ≠ skew (c₁ + c₂) T₃ x) ⊆
      univ.biUnion fun z => (univ.filter fun ω : Ω => T₁ (z + c₂) (T₂ z ω) ≠ T₃ z ω).map
        ⟨fun ω => (z, ω), fun a b h => (Prod.ext_iff.mp h).2⟩ := by
    intro x hx
    rw [mem_filter] at hx
    have hx2 := hx.2
    rw [Equiv.Perm.mul_apply, skew_apply, skew_apply, skew_apply] at hx2
    simp only [mem_biUnion, mem_univ, true_and, mem_map, mem_filter]
    refine ⟨x.1, x.2, fun h => hx2 ?_, rfl⟩
    dsimp only
    rw [h, add_assoc, add_comm c₂ c₁]
  exact (card_le_card hsub).trans (card_biUnion_le.trans (le_of_eq (by simp)))

/-- Agreement of two skew products is counted clock by clock (and is empty if the clock steps
differ). -/
theorem card_skew_eq (c₁ c₂ : C) (T₁ T₂ : C → Equiv.Perm Ω) :
    (univ.filter fun x : C × Ω => skew c₁ T₁ x = skew c₂ T₂ x).card ≤
      if c₁ = c₂ then ∑ z, (univ.filter fun ω : Ω => T₁ z ω = T₂ z ω).card else 0 := by
  split_ifs with hc
  · subst hc
    have hsub : (univ.filter fun x : C × Ω => skew c₁ T₁ x = skew c₁ T₂ x) ⊆
        univ.biUnion fun z => (univ.filter fun ω : Ω => T₁ z ω = T₂ z ω).map
          ⟨fun ω => (z, ω), fun a b h => (Prod.ext_iff.mp h).2⟩ := by
      intro x hx
      simp only [mem_filter, mem_univ, true_and, skew_apply, Prod.mk.injEq] at hx
      simp only [mem_biUnion, mem_univ, true_and, mem_map, mem_filter, Function.Embedding.coeFn_mk]
      exact ⟨x.1, x.2, hx, rfl⟩
    exact (card_le_card hsub).trans (card_biUnion_le.trans (le_of_eq (by simp)))
  · apply le_of_eq
    rw [card_eq_zero, filter_eq_empty_iff]
    intro x _ h
    simp only [skew_apply, Prod.mk.injEq, add_right_inj] at h
    exact hc h.1

end Lamps.Skew

/-! ### Realizing `K_{W_R}` inside `Perm (V × S₃)`

`W_R = 𝔽₂^{Y_R}`; an element `(λ, g)` of `K_{W_R}` acts on `X = V × S₃` by acting on the `Y_R`-part
of a configuration and keeping the rest, with lamps only at configurations inside `Y_R`. -/

namespace Lamps.Hash

open Finset
open scoped symmDiff

variable (R : ℕ)

/-- The points of `Y_R`. -/
abbrev PR := {y : Houghton.Y // y ∈ YR R}

def embR : PR R ↪ Houghton.Y := Function.Embedding.subtype _

/-- The `Y_R`-part of a configuration. -/
def inner (v : Finset Houghton.Y) : Finset (PR R) := v.subtype (· ∈ YR R)
/-- The rest of a configuration. -/
def outer (v : Finset Houghton.Y) : Finset Houghton.Y := v.filter (· ∉ YR R)

theorem inner_union (A : Finset (PR R)) (o : Finset Houghton.Y) (ho : ∀ y ∈ o, y ∉ YR R) :
    inner R (A.map (embR R) ∪ o) = A := by
  ext x
  simp only [inner, mem_subtype, mem_union, mem_map, embR, Function.Embedding.coe_subtype]
  constructor
  · rintro (⟨a, ha, hax⟩ | h)
    · rwa [← Subtype.ext hax]
    · exact absurd x.2 (ho _ h)
  · intro hx; exact Or.inl ⟨x, hx, rfl⟩

theorem outer_union (A : Finset (PR R)) (o : Finset Houghton.Y) (ho : ∀ y ∈ o, y ∉ YR R) :
    outer R (A.map (embR R) ∪ o) = o := by
  ext y
  simp only [outer, mem_filter, mem_union, mem_map, embR, Function.Embedding.coe_subtype]
  constructor
  · rintro ⟨⟨a, _, rfl⟩ | h, hy⟩
    · exact absurd a.2 hy
    · exact h
  · intro h; exact ⟨Or.inr h, ho y h⟩

theorem outer_out (v : Finset Houghton.Y) : ∀ y ∈ outer R v, y ∉ YR R := by
  intro y hy; exact (mem_filter.mp hy).2

theorem split (v : Finset Houghton.Y) : (inner R v).map (embR R) ∪ outer R v = v := by
  ext y
  simp only [inner, outer, mem_union, mem_map, mem_subtype, mem_filter, embR,
    Function.Embedding.coe_subtype]
  constructor
  · rintro (⟨a, ha, rfl⟩ | ⟨h, _⟩)
    · exact ha
    · exact h
  · intro hy
    by_cases hR : y ∈ YR R
    · exact Or.inl ⟨⟨y, hR⟩, hy, rfl⟩
    · exact Or.inr ⟨hy, hR⟩

/-- The realization of `γ ∈ K_{W_R}` as a map of `X = V × S₃`. -/
def realF (γ : KW (PR R)) (x : Lamps.X) : Lamps.X :=
  ((γ.g (inner R x.1)).map (embR R) ∪ outer R x.1,
    (if outer R x.1 = ∅ then γ.lam (γ.g (inner R x.1)) else 1) * x.2)

/-- `real` is multiplicative. -/
theorem realF_mul (γ₁ γ₂ : KW (PR R)) (x : Lamps.X) :
    realF R (KW.mul γ₁ γ₂) x = realF R γ₁ (realF R γ₂ x) := by
  obtain ⟨v, s⟩ := x
  simp only [realF, inner_union R _ _ (outer_out R v), outer_union R _ _ (outer_out R v),
    KW.mul, Equiv.trans_apply, Equiv.symm_apply_apply]
  refine Prod.ext rfl ?_
  dsimp only
  split_ifs <;> simp [mul_assoc]

/-- `real` is injective: the realization determines the affine and the lamp part. -/
theorem realF_inj {γ₁ γ₂ : KW (PR R)} (h : realF R γ₁ = realF R γ₂) :
    γ₁.g = γ₂.g ∧ γ₁.lam = γ₂.lam := by
  have hout : ∀ w : Finset (PR R), outer R (w.map (embR R)) = ∅ := by
    intro w
    have := outer_union R w ∅ (by simp)
    simpa using this
  have hin : ∀ w : Finset (PR R), inner R (w.map (embR R)) = w := by
    intro w
    have := inner_union R w ∅ (by simp)
    simpa using this
  have hg : γ₁.g = γ₂.g := by
    ext w : 1
    have := congrArg Prod.fst (congrFun h (w.map (embR R), 1))
    simp only [realF, hin, hout, union_empty] at this
    exact Finset.map_injective _ this
  refine ⟨hg, funext fun w => ?_⟩
  have := congrArg Prod.snd (congrFun h ((γ₁.g.symm w).map (embR R), 1))
  simp only [realF, hin, hout, if_true, mul_one, Equiv.apply_symm_apply] at this
  rw [this, hg, Equiv.apply_symm_apply]

/-! ### The letter cocycles as elements of `K_{W_R}` -/

theorem isAffine_map (σ : Equiv.Perm (PR R)) : IsAffine σ.finsetCongr := by
  intro v w
  ext x
  simp only [Equiv.finsetCongr_apply, Finset.mem_map_equiv, Finset.mem_symmDiff, Finset.map_empty,
    Finset.notMem_empty]
  tauto

/-- A point permutation of `Y_R`. -/
def permKW (σ : Equiv.Perm (PR R)) : KW (PR R) where
  g := σ.finsetCongr
  hg := isAffine_map R σ
  hgi := by rw [Equiv.finsetCongr_symm]; exact isAffine_map R σ.symm
  lam _ := 1

theorem mem_first (A : Finset (PR R)) (v : Finset Houghton.Y) (y : Houghton.Y) :
    y ∈ A.map (embR R) ∪ outer R v ↔ (∃ h : y ∈ YR R, (⟨y, h⟩ : PR R) ∈ A) ∨ (y ∈ v ∧ y ∉ YR R) := by
  simp only [mem_union, mem_map, embR, Function.Embedding.coe_subtype, outer, mem_filter]
  constructor
  · rintro (⟨a, ha, rfl⟩ | h)
    · exact Or.inl ⟨a.2, ha⟩
    · exact Or.inr h
  · rintro (⟨h, ha⟩ | h)
    · exact Or.inl ⟨_, ha, rfl⟩
    · exact Or.inr h

theorem realF_permKW (g : Equiv.Perm Houghton.Y) (hg : SuppIn R g) :
    realF R (permKW R (restrictR R g hg)) = Lamps.hV g := by
  funext ⟨v, s⟩
  rw [Lamps.hV_apply]
  simp only [realF, permKW, ite_self, one_mul]
  refine Prod.ext ?_ rfl
  ext y
  rw [mem_first, Finset.mem_map_equiv]
  by_cases hy : y ∈ YR R
  · have hy' : g.symm y ∈ YR R := by
      rw [hg.mem_iff (g.symm y), Equiv.apply_symm_apply]; exact hy
    simp only [hy, not_true_eq_false, and_false, or_false, exists_true_left,
      Equiv.finsetCongr_apply, Finset.mem_map_equiv, inner, mem_subtype]
    constructor
    · intro h
      have : (restrictR R g hg).symm ⟨y, hy⟩ = ⟨g.symm y, hy'⟩ := by
        apply (restrictR R g hg).injective
        rw [Equiv.apply_symm_apply]; apply Subtype.ext
        rw [restrictR_apply, Equiv.apply_symm_apply]
      rw [this] at h; exact h
    · intro h
      have : (restrictR R g hg).symm ⟨y, hy⟩ = ⟨g.symm y, hy'⟩ := by
        apply (restrictR R g hg).injective
        rw [Equiv.apply_symm_apply]; apply Subtype.ext
        rw [restrictR_apply, Equiv.apply_symm_apply]
      rw [this]; exact h
  · have hfix : g.symm y = y := by
      have h1 : g y = y := hg y (by rw [mem_YR] at hy; omega)
      rw [Equiv.symm_apply_eq]; exact h1.symm
    rw [hfix]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩)
      · exact absurd h hy
      · exact h
    · intro h; exact Or.inr ⟨h, hy⟩

theorem isAffine_tau (u : Finset (PR R)) :
    IsAffine (P := PR R) ⟨fun v => v ∆ u, fun v => v ∆ u, fun v => by simp, fun v => by simp⟩ := by
  intro v w
  ext x; simp only [Equiv.coe_fn_mk, Finset.mem_symmDiff, Finset.notMem_empty]; tauto

/-- A translation of `W_R`. -/
def tauKW (u : Finset (PR R)) : KW (PR R) where
  g := ⟨fun v => v ∆ u, fun v => v ∆ u, fun v => by simp, fun v => by simp⟩
  hg := isAffine_tau R u
  hgi := isAffine_tau R u
  lam _ := 1

theorem mem_map_embR (A : Finset (PR R)) (y : Houghton.Y) :
    y ∈ A.map (embR R) ↔ ∃ h : y ∈ YR R, (⟨y, h⟩ : PR R) ∈ A := by
  simp only [mem_map, embR, Function.Embedding.coe_subtype]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ⟨a.2, ha⟩
  · rintro ⟨h, ha⟩; exact ⟨_, ha, rfl⟩

theorem realF_tauKW (u : Finset (PR R)) : realF R (tauKW R u) = Lamps.tau (u.map (embR R)) := by
  funext ⟨v, s⟩
  simp only [realF, tauKW, ite_self, one_mul, Lamps.tau, Equiv.coe_fn_mk]
  refine Prod.ext ?_ rfl
  ext y
  rw [mem_first]
  show _ ↔ y ∈ v ∆ u.map (embR R)
  rw [Finset.mem_symmDiff, mem_map_embR]
  by_cases hy : y ∈ YR R
  · simp [hy, Finset.mem_symmDiff, inner]
  · simp [hy]

/-- A lamp at the configuration `0 = ∅`. -/
def lampKW (σ : Equiv.Perm (Fin 3)) : KW (PR R) where
  g := Equiv.refl _
  hg := by intro v w; ext x; simp [Finset.mem_symmDiff]
  hgi := by intro v w; ext x; simp [Finset.mem_symmDiff]
  lam w := if w = ∅ then σ else 1

theorem inner_empty : inner R ∅ = ∅ := by ext x; simp [inner]

theorem inner_outer_empty (v : Finset Houghton.Y) :
    (outer R v = ∅ ∧ inner R v = ∅) ↔ v = ∅ := by
  constructor
  · rintro ⟨h1, h2⟩; rw [← split R v, h1, h2]; simp
  · rintro rfl; exact ⟨by simp [outer], inner_empty R⟩

theorem realF_lampKW (σ : Equiv.Perm (Fin 3)) : realF R (lampKW R σ) = Lamps.lamp ∅ σ := by
  funext ⟨v, s⟩
  simp only [realF, lampKW, Equiv.refl_apply, split]
  by_cases hv : v = ∅
  · subst hv
    simp [Lamps.lamp, inner_empty, outer]
  · have : ¬ (outer R v = ∅ ∧ inner R v = ∅) := fun h => hv ((inner_outer_empty R v).mp h)
    simp only [Lamps.lamp, Equiv.coe_fn_mk, hv, if_false]
    refine Prod.ext rfl ?_
    dsimp only
    by_cases ho : outer R v = ∅
    · have hi : inner R v ≠ ∅ := fun h => this ⟨ho, h⟩
      simp [ho, hi]
    · simp [ho]

theorem mem_tv {P : Type*} [DecidableEq P] (x y z : P) (v : Finset P) :
    z ∈ tv x y v ↔ ¬ (z ∈ v ↔ (z = y ∧ x ∈ v)) := by
  unfold tv
  split_ifs with hx
  · simp only [Finset.mem_symmDiff, Finset.mem_singleton]; tauto
  · tauto

theorem tv_tv {P : Type*} [DecidableEq P] (x y : P) (hxy : x ≠ y) (v : Finset P) :
    tv x y (tv x y v) = v := by
  ext z
  rw [mem_tv, mem_tv, mem_tv x y x]
  have : ¬ x = y := hxy
  tauto

theorem isAffine_tv (x y : PR R) (hxy : x ≠ y) :
    IsAffine (P := PR R) ⟨tv x y, tv x y, tv_tv x y hxy, tv_tv x y hxy⟩ := by
  intro v w
  ext z
  simp only [Equiv.coe_fn_mk, mem_tv, Finset.mem_symmDiff, Finset.notMem_empty]
  by_cases h3 : z = y
  · subst h3
    by_cases h1 : z ∈ v <;> by_cases h2 : z ∈ w <;> by_cases h4 : x ∈ v <;>
      by_cases h5 : x ∈ w <;> simp [h1, h2, h4, h5]
  · by_cases h1 : z ∈ v <;> by_cases h2 : z ∈ w <;> by_cases h4 : x ∈ v <;>
      by_cases h5 : x ∈ w <;> simp [h1, h2, h3, h4, h5]

/-- A transvection `E_{y←x}` of `W_R`. -/
def tvKW (x y : PR R) (hxy : x ≠ y) : KW (PR R) where
  g := ⟨tv x y, tv x y, tv_tv x y hxy, tv_tv x y hxy⟩
  hg := isAffine_tv R x y hxy
  hgi := isAffine_tv R x y hxy
  lam _ := 1

/-- The transvection `E_{y←x}` acting on `X`. -/
def tvX (x y : Houghton.Y) (v : Finset Houghton.Y × Lamps.S3) : Finset Houghton.Y × Lamps.S3 :=
  (tv x y v.1, v.2)

theorem realF_tvKW (x y : PR R) (hxy : x ≠ y) :
    realF R (tvKW R x y hxy) = tvX (x : Houghton.Y) (y : Houghton.Y) := by
  funext ⟨v, s⟩
  refine Prod.ext ?_ ?_
  · show (tv x y (inner R v)).map (embR R) ∪ outer R v = tv (x : Houghton.Y) y v
    ext z
    rw [mem_first, mem_tv]
    simp only [mem_tv]
    have hxin : x ∈ inner R v ↔ (x : Houghton.Y) ∈ v := by simp [inner]
    by_cases hz : z ∈ YR R
    · have hzy : (⟨z, hz⟩ : PR R) = y ↔ z = (y : Houghton.Y) := by
        constructor
        · intro h; rw [← h]
        · intro h; exact Subtype.ext h
      have hzin : (⟨z, hz⟩ : PR R) ∈ inner R v ↔ z ∈ v := by simp [inner]
      simp only [hz, exists_true_left, not_true_eq_false, and_false, or_false, hzy, hzin, hxin]
    · have hzy : z ≠ (y : Houghton.Y) := fun h => hz (h ▸ y.2)
      simp only [hz, not_false_eq_true, and_true, hzy, false_and, iff_false, not_not]
      constructor
      · rintro (⟨h, _⟩ | h)
        · exact h.elim
        · exact h
      · intro h; exact Or.inr h
  · show (if outer R v = ∅ then (1 : Lamps.S3) else 1) * s = s
    rw [ite_self, one_mul]

end Lamps.Hash

namespace Lamps

open Hash

/-- Conjugating the transvection `d = E_{2←1}` by a point permutation `σ` gives `E_{σ2←σ1}`. -/
theorem hV_conj_dP (σ : Equiv.Perm Houghton.Y) :
    ⇑(hV σ * dP * (hV σ)⁻¹) = tvX (σ e1) (σ e2) := by
  funext ⟨v, s⟩
  rw [← map_inv]
  simp only [Equiv.Perm.mul_apply, hV_apply, dP, Equiv.coe_fn_mk, dV, tvX, tv]
  have hmem : e1 ∈ v.map (σ⁻¹).toEmbedding ↔ σ e1 ∈ v := by
    rw [Finset.mem_map_equiv]; simp [← Equiv.Perm.inv_def]
  by_cases h : σ e1 ∈ v
  · rw [if_pos (hmem.mpr h), if_pos h, map_symmDiff', map_map_inv, Finset.map_singleton]
    rfl
  · rw [if_neg (fun h' => h (hmem.mp h')), if_neg h, map_map_inv]

end Lamps
