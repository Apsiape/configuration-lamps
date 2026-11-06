import Lamps.Group
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Elementary amenability of the configuration-lamps group

Lemma `lem:structure`(c) of Douglas–Mghirbi (configuration lamps), amenability half of
Theorem A(d): `Γ_elementaryAmenable : ElementaryAmenable Γ`.

* `ElementaryAmenable`: Chou's class EG [C. Chou, *Elementary amenable groups*, Illinois J. Math.
  24 (1980)]: the smallest class of groups containing all finite groups and all abelian groups and
  closed under subgroups, quotients (images under surjective homomorphisms), extensions and
  directed unions.  It is an inductive predicate on groups in a fixed universe `u`.
* `IsLocallyFinite`: every finite subset generates a finite subgroup;
  `IsLocallyFinite.elementaryAmenable`: locally finite groups are elementary amenable (directed
  union of their finitely generated, hence finite, subgroups).
* Route for `Γ` (equivalent to the paper's, with the kernel described intrinsically).  Let `Nfin`
  be the group of permutations `γ` of `X = V × S₃` that change configurations only inside some
  finite `J ⊆ Y`: `(γ x).1 ∆ x.1 ⊆ J` for all `x`.  Then
  1. `Nfin` is locally finite (`closure_finite_of_subset_Nfin`): elements with a common `J`
     preserve the blocks `{x : x.1 \ J = b} ≅ 𝒫(J) × S₃`, and a word in finitely many of them
     acts on a block through the finitely many restrictions of the generators to that block;
  2. `Γ ∩ Nfin` is normal in `Γ` (every element of `Γ` has bounded "configuration distortion",
     `Bounded`);
  3. `Γ / (Γ ∩ Nfin)` is abelian: `t, c, a ∈ Nfin` and `[p, q] = hV α⁻¹ ∈ Nfin`.
  Hence `Γ` is locally finite-by-abelian, so elementary amenable.  (`Γ ∩ Nfin` is the kernel of
  the paper's `π : Γ → ℤ²`; we do not need to identify it.)
-/

universe u

namespace Lamps

open Houghton (Y alPerm)
open scoped symmDiff

/-! ### Elementary amenable groups (Chou 1980) -/

/-- Chou's class of elementary amenable groups: the smallest class containing finite and abelian
groups, closed under subgroups, quotients, extensions and directed unions. -/
inductive ElementaryAmenable : (G : Type u) → [Group G] → Prop
  | of_finite (G : Type u) [Group G] [Finite G] : ElementaryAmenable G
  | of_comm (G : Type u) [Group G] (h : ∀ a b : G, a * b = b * a) : ElementaryAmenable G
  | subgroup {G : Type u} [Group G] (H : Subgroup G) :
      ElementaryAmenable G → ElementaryAmenable H
  | quotient {G H : Type u} [Group G] [Group H] (f : G →* H) (hf : Function.Surjective f) :
      ElementaryAmenable G → ElementaryAmenable H
  | extension {G : Type u} [Group G] (N : Subgroup G) [N.Normal] :
      ElementaryAmenable N → ElementaryAmenable (G ⧸ N) → ElementaryAmenable G
  | directedUnion {G : Type u} [Group G] (S : Set (Subgroup G)) (hdir : DirectedOn (· ≤ ·) S)
      (hcov : ∀ g : G, ∃ H ∈ S, g ∈ H) :
      (∀ H ∈ S, ElementaryAmenable H) → ElementaryAmenable G

/-- A group is locally finite if every finite subset generates a finite subgroup. -/
def IsLocallyFinite (G : Type*) [Group G] : Prop :=
  ∀ s : Set G, s.Finite → (Subgroup.closure s : Set G).Finite

/-- Locally finite groups are elementary amenable. -/
theorem IsLocallyFinite.elementaryAmenable {G : Type u} [Group G] (h : IsLocallyFinite G) :
    ElementaryAmenable G := by
  refine ElementaryAmenable.directedUnion
    {H | ∃ s : Set G, s.Finite ∧ H = Subgroup.closure s} ?_ ?_ ?_
  · rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    exact ⟨_, ⟨s ∪ t, hs.union ht, rfl⟩, Subgroup.closure_mono Set.subset_union_left,
      Subgroup.closure_mono Set.subset_union_right⟩
  · intro g
    exact ⟨_, ⟨{g}, Set.finite_singleton g, rfl⟩, Subgroup.subset_closure rfl⟩
  · rintro _ ⟨s, hs, rfl⟩
    have : Finite (Subgroup.closure s) := (h s hs).to_subtype
    exact ElementaryAmenable.of_finite _

/-- In a group, a finite submonoid is closed under inverses. -/
theorem inv_mem_of_finite {G : Type*} [Group G] (M : Submonoid G) (hM : (M : Set G).Finite)
    {x : G} (hx : x ∈ M) : x⁻¹ ∈ M := by
  have : Finite M := hM.to_subtype
  have key : ∀ a b : ℕ, a < b → x ^ a = x ^ b → x⁻¹ ∈ M := by
    intro a b hab h
    obtain ⟨k, rfl⟩ : ∃ k, b = a + (k + 1) := ⟨b - a - 1, by omega⟩
    have h1 : x ^ (k + 1) = 1 :=
      mul_left_cancel (show x ^ a * x ^ (k + 1) = x ^ a * 1 by rw [mul_one, ← pow_add]; exact h.symm)
    rw [pow_succ] at h1
    rw [← eq_inv_of_mul_eq_one_left h1]
    exact M.pow_mem hx k
  obtain ⟨i, j, hij, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => (⟨x ^ n, M.pow_mem hx n⟩ : M))
  have heq' : x ^ i = x ^ j := congrArg Subtype.val heq
  rcases hij.lt_or_gt with h | h
  · exact key i j h heq'
  · exact key j i h heq'.symm

/-- A subset of a finite submonoid of a group generates a finite subgroup. -/
theorem closure_finite_of_submonoid {G : Type*} [Group G] (s : Set G) (M : Submonoid G)
    (hM : (M : Set G).Finite) (hs : s ⊆ M) : (Subgroup.closure s : Set G).Finite := by
  let T : Subgroup G := { M with inv_mem' := fun hx => inv_mem_of_finite M hM hx }
  have hle : Subgroup.closure s ≤ T := (Subgroup.closure_le T).2 hs
  exact hM.subset fun x hx => hle hx

/-! ### Permutations changing configurations in a finite set -/

/-- Permutations of `X = V × S₃` that change configurations only inside a finite set of points. -/
def Nfin : Subgroup (Equiv.Perm X) where
  carrier := {γ | ∃ J : Finset Y, ∀ x, (γ x).1 ∆ x.1 ⊆ J}
  one_mem' := ⟨∅, fun x => by simp⟩
  mul_mem' := by
    rintro γ δ ⟨J, hJ⟩ ⟨K, hK⟩
    refine ⟨J ∪ K, fun x => ?_⟩
    rw [Equiv.Perm.mul_apply]
    show (γ (δ x)).1 ∆ x.1 ≤ J ⊔ K
    exact le_trans (symmDiff_triangle _ (δ x).1 _) (sup_le_sup (hJ _) (hK x))
  inv_mem' := by
    rintro γ ⟨J, hJ⟩
    refine ⟨J, fun x => ?_⟩
    have := hJ (γ⁻¹ x)
    have e : γ (γ⁻¹ x) = x := by simp
    rwa [e, symmDiff_comm] at this

section Blocks

variable (J : Finset Y)

/-- Local coordinates on a block: the part inside `J`, and the `S₃` coordinate. -/
abbrev Cell := ↥J.powerset × S3

/-- The block of `x`: its configuration outside `J`. -/
def key (x : X) : V := x.1 \ J

/-- The local coordinate of `x` in its block. -/
def loc (x : X) : Cell J := (⟨x.1 ∩ J, Finset.mem_powerset.2 Finset.inter_subset_right⟩, x.2)

/-- Reconstruct a point from its block and local coordinate. -/
def recon (b : V) (z : Cell J) : X := (b ∪ z.1.1, z.2)

theorem recon_key_loc (x : X) : recon J (key J x) (loc J x) = x := by
  simp [recon, key, loc, Finset.sdiff_union_inter]

theorem key_eq_of {γ : Equiv.Perm X} (h : ∀ x, (γ x).1 ∆ x.1 ⊆ J) (x : X) :
    key J (γ x) = key J x := by
  ext y
  simp only [key, Finset.mem_sdiff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    by_contra h3
    exact h2 (h x (Finset.mem_symmDiff.2 (Or.inl ⟨h1, h3⟩)))
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    by_contra h3
    exact h2 (h x (Finset.mem_symmDiff.2 (Or.inr ⟨h1, h3⟩)))

/-- Finitely many permutations changing configurations only inside `J` generate a finite group. -/
theorem closure_finite_of_forall (s : Set (Equiv.Perm X)) (hs : s.Finite)
    (hJ : ∀ γ ∈ s, ∀ x, (γ x).1 ∆ x.1 ⊆ J) : (Subgroup.closure s : Set (Equiv.Perm X)).Finite := by
  classical
  have : Finite s := hs.to_subtype
  -- the type of a block: the restrictions of the generators to it
  let τ : V → (s → Cell J → Cell J) := fun b g z => loc J (g.1 (recon J b z))
  let M : Submonoid (Equiv.Perm X) :=
    { carrier := {δ | (∀ x, key J (δ x) = key J x) ∧
        ∃ Φ : (s → Cell J → Cell J) → Cell J → Cell J, ∀ x, loc J (δ x) = Φ (τ (key J x)) (loc J x)}
      one_mem' := ⟨fun x => rfl, fun _ z => z, fun x => rfl⟩
      mul_mem' := by
        rintro δ₁ δ₂ ⟨k₁, Φ₁, h₁⟩ ⟨k₂, Φ₂, h₂⟩
        refine ⟨fun x => ?_, fun T z => Φ₁ T (Φ₂ T z), fun x => ?_⟩
        · rw [Equiv.Perm.mul_apply, k₁, k₂]
        · rw [Equiv.Perm.mul_apply, h₁, k₂, h₂] }
  have hsM : s ⊆ M := by
    intro g hg
    refine ⟨key_eq_of J (hJ g hg), fun T => T ⟨g, hg⟩, fun x => ?_⟩
    show loc J (g x) = loc J (g (recon J (key J x) (loc J x)))
    rw [recon_key_loc]
  let F : ((s → Cell J → Cell J) → Cell J → Cell J) → X → X :=
    fun Φ x => recon J (key J x) (Φ (τ (key J x)) (loc J x))
  have hMF : (M : Set (Equiv.Perm X)) ⊆ DFunLike.coe ⁻¹' Set.range F := by
    rintro δ ⟨k, Φ, h⟩
    refine ⟨Φ, funext fun x => ?_⟩
    show recon J (key J x) (Φ (τ (key J x)) (loc J x)) = δ x
    rw [← h, ← k, recon_key_loc]
  have hMfin : (M : Set (Equiv.Perm X)).Finite :=
    ((Set.finite_range F).preimage DFunLike.coe_injective.injOn).subset hMF
  exact closure_finite_of_submonoid s M hMfin hsM

end Blocks

/-- **`Nfin` is locally finite.** -/
theorem closure_finite_of_subset_Nfin (s : Set (Equiv.Perm X)) (hs : s.Finite) (hN : s ⊆ Nfin) :
    (Subgroup.closure s : Set (Equiv.Perm X)).Finite := by
  classical
  let f : Equiv.Perm X → Finset Y := fun γ => if h : γ ∈ Nfin then h.choose else ∅
  refine closure_finite_of_forall (hs.toFinset.biUnion f) s hs fun γ hγ x => ?_
  have hγN := hN hγ
  have h1 : (γ x).1 ∆ x.1 ⊆ f γ := by
    have e : f γ = hγN.choose := by
      simp only [f]
      split_ifs with h
      · rfl
      · exact absurd hγN h
    rw [e]
    exact hγN.choose_spec x
  exact h1.trans (Finset.subset_biUnion_of_mem f (hs.mem_toFinset.2 hγ))

/-! ### Bounded distortion and normality -/

/-- `g` distorts configuration differences boundedly. -/
def Bounded (g : Equiv.Perm X) : Prop :=
  ∃ Φ : Finset Y → Finset Y, ∀ x y : X, ∀ J : Finset Y, x.1 ∆ y.1 ⊆ J → (g x).1 ∆ (g y).1 ⊆ Φ J

theorem Bounded.mul {g h : Equiv.Perm X} (hg : Bounded g) (hh : Bounded h) : Bounded (g * h) := by
  obtain ⟨Φ, hΦ⟩ := hg
  obtain ⟨Ψ, hΨ⟩ := hh
  exact ⟨Φ ∘ Ψ, fun x y J hxy => hΦ _ _ _ (hΨ x y J hxy)⟩

theorem bounded_of_mem_Nfin {g : Equiv.Perm X} (hg : g ∈ Nfin) : Bounded g := by
  obtain ⟨K, hK⟩ := hg
  refine ⟨fun J => K ⊔ (J ⊔ K), fun x y J hxy => ?_⟩
  have h1 := hK x
  have h2 := hK y
  rw [symmDiff_comm] at h2
  show (g x).1 ∆ (g y).1 ≤ K ⊔ (J ⊔ K)
  calc (g x).1 ∆ (g y).1 ≤ (g x).1 ∆ x.1 ⊔ x.1 ∆ (g y).1 := symmDiff_triangle _ _ _
    _ ≤ (g x).1 ∆ x.1 ⊔ (x.1 ∆ y.1 ⊔ y.1 ∆ (g y).1) :=
        sup_le_sup_left (symmDiff_triangle _ _ _) _
    _ ≤ K ⊔ (J ⊔ K) := sup_le_sup h1 (sup_le_sup hxy h2)

theorem bounded_hV (g : Equiv.Perm Y) : Bounded (hV g) :=
  ⟨fun J => J.map g.toEmbedding, fun x y J hxy => by
    simp only [hV_apply]
    rw [← map_symmDiff']
    exact Finset.map_subset_map.2 hxy⟩

/-- Conjugation by a boundedly distorting permutation preserves `Nfin`. -/
theorem conj_mem_Nfin {g n : Equiv.Perm X} (hg : Bounded g) (hn : n ∈ Nfin) :
    g * n * g⁻¹ ∈ Nfin := by
  obtain ⟨Φ, hΦ⟩ := hg
  obtain ⟨J, hJ⟩ := hn
  refine ⟨Φ J, fun x => ?_⟩
  have := hΦ (n (g⁻¹ x)) (g⁻¹ x) J (hJ _)
  simpa [Equiv.Perm.mul_apply] using this

/-- Permutations that, together with their inverses, have bounded distortion. -/
def Bd : Subgroup (Equiv.Perm X) where
  carrier := {g | Bounded g ∧ Bounded g⁻¹}
  one_mem' := ⟨⟨id, fun x y J h => by simpa using h⟩, ⟨id, fun x y J h => by simpa using h⟩⟩
  mul_mem' := by
    rintro g h ⟨a1, a2⟩ ⟨b1, b2⟩
    refine ⟨a1.mul b1, ?_⟩
    rw [mul_inv_rev]
    exact b2.mul a2
  inv_mem' := by
    rintro g ⟨a1, a2⟩
    exact ⟨a2, by rwa [inv_inv]⟩

theorem Nfin_le_Bd : Nfin ≤ Bd := fun _ hg =>
  ⟨bounded_of_mem_Nfin hg, bounded_of_mem_Nfin (Nfin.inv_mem hg)⟩

theorem hV_mem_Bd (g : Equiv.Perm Y) : hV g ∈ Bd :=
  ⟨bounded_hV g, by rw [← map_inv]; exact bounded_hV _⟩

/-! ### The generators -/

theorem tau_mem_Nfin (u : V) : tau u ∈ Nfin := by
  refine ⟨u, fun x => ?_⟩
  show (x.1 ∆ u) ∆ x.1 ⊆ u
  rw [symmDiff_comm, symmDiff_symmDiff_cancel_left]

theorem lamp_fst (u : V) (σ : S3) (x : X) : (lamp u σ x).1 = x.1 := by
  simp only [lamp, Equiv.coe_fn_mk]
  split_ifs <;> rfl

theorem lamp_mem_Nfin (u : V) (σ : S3) : lamp u σ ∈ Nfin :=
  ⟨∅, fun x => by simp [lamp_fst]⟩

theorem dP_mem_Nfin : dP ∈ Nfin := by
  refine ⟨{e2}, fun x => ?_⟩
  show dV x.1 ∆ x.1 ⊆ {e2}
  unfold dV
  split_ifs
  · rw [symmDiff_comm, symmDiff_symmDiff_cancel_left]
  · simp

theorem hV_mem_Nfin (g : Equiv.Perm Y) (K0 : Finset Y) (hg : ∀ y, y ∉ K0 → g y = y) :
    hV g ∈ Nfin := by
  classical
  refine ⟨K0 ∪ K0.map g.toEmbedding, fun x => ?_⟩
  intro z hz
  rw [hV_apply, Finset.mem_symmDiff] at hz
  rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 h1
    by_cases hyK : y ∈ K0
    · exact Finset.mem_union_right _ (Finset.mem_map_of_mem _ hyK)
    · exfalso
      apply h2
      simp only [Equiv.toEmbedding_apply]
      rw [hg y hyK]
      exact hy
  · by_cases hzK : z ∈ K0
    · exact Finset.mem_union_left _ hzK
    · exfalso
      exact h2 (Finset.mem_map.2 ⟨z, h1, by simp [hg z hzK]⟩)

theorem rho_s_mem_Nfin : ρΓ s ∈ Nfin := by
  rw [rho_s, Houghton.alPerm_eq_swap, Equiv.swap_inv]
  refine hV_mem_Nfin _ {((0 : Fin 3), 0), ((0 : Fin 3), 1)} fun y hy => ?_
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
  exact Equiv.swap_apply_of_ne_of_ne hy.1 hy.2

theorem rho_t_mem_Nfin : ρΓ t ∈ Nfin := by rw [rho_t]; exact tau_mem_Nfin _
theorem rho_c_mem_Nfin : ρΓ c ∈ Nfin := by
  rw [rho_c]; exact Nfin.mul_mem dP_mem_Nfin (lamp_mem_Nfin _ _)
theorem rho_a_mem_Nfin : ρΓ a ∈ Nfin := by rw [rho_a]; exact lamp_mem_Nfin _ _

theorem Γ_le_Bd : Γ ≤ Bd := by
  refine FreeGroup.range_lift_le ?_
  rintro _ ⟨i, rfl⟩
  have h : gen i = ρΓ (FreeGroup.of i) := by simp [ρΓ]
  rw [h]
  fin_cases i
  · exact (rho_p ▸ hV_mem_Bd pY : ρΓ p ∈ Bd)
  · exact (rho_q ▸ hV_mem_Bd qY : ρΓ q ∈ Bd)
  · exact Nfin_le_Bd rho_t_mem_Nfin
  · exact Nfin_le_Bd rho_c_mem_Nfin
  · exact Nfin_le_Bd rho_a_mem_Nfin

/-! ### `Γ` is locally finite-by-abelian -/

/-- `Γ ∩ Nfin`, as a subgroup of `Γ`. -/
def ΓN : Subgroup Γ := Nfin.subgroupOf Γ

instance ΓN_normal : ΓN.Normal :=
  ⟨fun n hn g => by
    rw [ΓN, Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact conj_mem_Nfin (Γ_le_Bd g.2).1 hn⟩

theorem ΓN_locallyFinite : IsLocallyFinite ΓN := by
  intro s hs
  let φ : ΓN →* Equiv.Perm X := Γ.subtype.comp ΓN.subtype
  have hφ : Function.Injective φ := Subtype.val_injective.comp Subtype.val_injective
  have himg : φ '' s ⊆ Nfin := by
    rintro _ ⟨k, -, rfl⟩
    exact k.2
  have hfin := closure_finite_of_subset_Nfin _ (hs.image φ) himg
  have hsub : (Subgroup.closure s : Set ΓN) ⊆ φ ⁻¹' (Subgroup.closure (φ '' s) : Set _) := by
    intro x hx
    rw [Set.mem_preimage, SetLike.mem_coe, ← MonoidHom.map_closure]
    exact Subgroup.mem_map_of_mem φ hx
  exact (hfin.preimage hφ.injOn).subset hsub

theorem quotient_comm (x y : Γ ⧸ ΓN) : x * y = y * x := by
  let π : F →* Γ ⧸ ΓN := (QuotientGroup.mk' ΓN).comp ρΓ.rangeRestrict
  have hπ : Function.Surjective π :=
    (QuotientGroup.mk'_surjective ΓN).comp ρΓ.rangeRestrict_surjective
  have hone : ∀ w, ρΓ w ∈ Nfin → π w = 1 := fun w hw => by
    show ((ρΓ.rangeRestrict w : Γ) : Γ ⧸ ΓN) = 1
    rw [QuotientGroup.eq_one_iff, ΓN, Subgroup.mem_subgroupOf]
    exact hw
  have hpq : π p * π q = π q * π p := by
    rw [← commutatorElement_eq_one_iff_mul_comm, commutatorElement_def, ← map_inv, ← map_inv,
      ← map_mul, ← map_mul, ← map_mul]
    exact hone _ rho_s_mem_Nfin
  have hof : ∀ i : Fin 5, π (FreeGroup.of i) = 1 ∨ π (FreeGroup.of i) = π p ∨
      π (FreeGroup.of i) = π q := by
    intro i
    fin_cases i
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
    · exact Or.inl (hone _ rho_t_mem_Nfin)
    · exact Or.inl (hone _ rho_c_mem_Nfin)
    · exact Or.inl (hone _ rho_a_mem_Nfin)
  have hgen : ∀ i j : Fin 5, Commute (π (FreeGroup.of i)) (π (FreeGroup.of j)) := by
    intro i j
    rcases hof i with hi | hi | hi
    · rw [hi]; exact Commute.one_left _
    all_goals rcases hof j with hj | hj | hj
    all_goals first
      | (rw [hj]; exact Commute.one_right _)
      | (rw [hi, hj]; exact hpq)
      | (rw [hi, hj]; exact hpq.symm)
      | (rw [hi, hj])
  have h1 : ∀ (w : F) (j : Fin 5), Commute (π w) (π (FreeGroup.of j)) := by
    intro w j
    induction w using FreeGroup.induction_on with
    | one => rw [map_one]; exact Commute.one_left _
    | of i => exact hgen i j
    | inv_of i h => rw [map_inv]; exact h.inv_left
    | mul w₁ w₂ h₁ h₂ => rw [map_mul]; exact h₁.mul_left h₂
  have hall : ∀ v w : F, Commute (π v) (π w) := by
    intro v w
    induction w using FreeGroup.induction_on with
    | one => rw [map_one]; exact Commute.one_right _
    | of j => exact h1 v j
    | inv_of j h => rw [map_inv]; exact h.inv_right
    | mul w₁ w₂ h₁ h₂ => rw [map_mul]; exact h₁.mul_right h₂
  obtain ⟨v, rfl⟩ := hπ x
  obtain ⟨w, rfl⟩ := hπ y
  exact (hall v w).eq

/-- **Lemma `lem:structure`(c), amenability half of Theorem A(d)**: `Γ` is elementary
amenable. -/
theorem Γ_elementaryAmenable : ElementaryAmenable Γ :=
  ElementaryAmenable.extension ΓN ΓN_locallyFinite.elementaryAmenable
    (ElementaryAmenable.of_comm _ quotient_comm)

end Lamps
