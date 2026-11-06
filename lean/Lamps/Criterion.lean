import Lamps.CriterionModel
import FiniteLean.GroupTheory.Sofic.Profile
import Mathlib.GroupTheory.FreeGroup.Reduce

/-!
# Theorem `thm:criterion` (Counting criterion), permutation form: the chunk form

For a group `G`, letters `S` with an evaluation `π : FreeGroup S →* G`, relators `R : ι → FreeGroup S`
with `π (R k) = 1` and `a², b², (ab)³` among them, and `π (ab) ≠ 1`, the chunk `E` consists of `1`,
`S^{±1}`, the elements represented by the prefixes of the (freely reduced, `FreeGroup.toWord`) words
of `R` and of `ab`, and the inverses of these elements. With `l` the largest length of a word of `R`
(`maxLen R`), every model size `n` of `E` at accuracy `r ≥ 10⁸ N Λ (2l - 1)` satisfies
`N/16 ≤ log₂ n`.

The transfer from a chunk model to a homomorphism `FreeGroup S →* Sym_n` (Appendix `app:imported`,
"Relator errors") generalizes `Houghton.transfer_model`, which is specific to `H₃`; the chain
estimate `chain_bound_gen` is `Houghton.chain_bound` with an arbitrary letter type. Chunks,
`ε`-morphisms, model sizes and the profile are those of `Houghton/Profile.lean` (generic in the group).
-/

namespace Lamps

open Finset Equiv
open Houghton (dH IsEpsMorphism IsExpansive IsSoficModel modelSizes profile)

/-! ### The chain estimate, for an arbitrary letter type -/

section chain

variable {G : Type*} [Group G] {L : Type*} {n : ℕ}

/-- Telescoping along the prefixes of a word: each letter costs one multiplication defect `ε`
(except the first, merged with `f 1 = 1`) plus the letter's own error `c l`
(`Houghton.chain_bound` for an arbitrary letter type `L`). -/
theorem chain_bound_gen (E : Finset G) (ε : ℝ) (f : G → Perm (Fin n))
    (hf : IsEpsMorphism E ε f) (g : L → G) (ψ : L → Perm (Fin n))
    (c : L → ℝ) (hc : ∀ l, dH (f (g l)) (ψ l) ≤ c l) (hg : ∀ l, g l ∈ E) :
    ∀ ws : List L, (∀ k, ((ws.take k).map g).prod ∈ E) →
      dH (f (ws.map g).prod) (ws.map ψ).prod ≤ (ws.length.pred : ℝ) * ε + (ws.map c).sum := by
  intro ws
  induction ws using List.reverseRecOn with
  | nil => intro _; simp [hf.1, Houghton.ham_self]
  | append_singleton ws l ih =>
    intro hpre
    have hpre' : ∀ k, ((ws.take k).map g).prod ∈ E := by
      intro k
      rcases le_total k ws.length with h | h
      · have := hpre k; rwa [List.take_append_of_le_length h] at this
      · have := hpre ws.length
        rwa [List.take_append_of_le_length le_rfl, List.take_length,
          ← List.take_of_length_le h] at this
    have hws : (ws.map g).prod ∈ E := by
      have := hpre' ws.length; rwa [List.take_length] at this
    have hall : (ws.map g).prod * g l ∈ E := by
      have := hpre (ws.length + 1)
      rw [List.take_of_length_le (by simp)] at this
      simpa using this
    have ih' := ih hpre'
    have key : dH (f ((ws.map g).prod * g l)) ((ws.map ψ).prod * ψ l) ≤
        (if ws = [] then 0 else ε) + dH (f (ws.map g).prod) (ws.map ψ).prod + c l := by
      have hmerge : dH (f ((ws.map g).prod * g l)) (f (ws.map g).prod * f (g l)) ≤
          if ws = [] then 0 else ε := by
        split_ifs with h0
        · subst h0; simp [hf.1, Houghton.ham_self]
        · exact hf.2 _ hws (g l) (hg l) hall
      have h2 := Houghton.ham_mul_right (f (ws.map g).prod) (ws.map ψ).prod (f (g l))
      have h3 := Houghton.ham_mul_left (ws.map ψ).prod (f (g l)) (ψ l)
      have t1 := Houghton.ham_triangle (f ((ws.map g).prod * g l))
        (f (ws.map g).prod * f (g l)) ((ws.map ψ).prod * ψ l)
      have t2 := Houghton.ham_triangle (f (ws.map g).prod * f (g l))
        ((ws.map ψ).prod * f (g l)) ((ws.map ψ).prod * ψ l)
      linarith [hc l]
    simp only [List.map_append, List.map_cons, List.map_nil, List.prod_append, List.prod_cons,
      List.prod_nil, mul_one, List.sum_append, List.sum_cons, List.sum_nil, add_zero,
      List.length_append, List.length_cons, List.length_nil]
    refine key.trans ?_
    rcases eq_or_ne ws [] with h0 | h0
    · subst h0; simp [hf.1, Houghton.ham_self]
    · simp only [h0, ↓reduceIte]
      have hlen : (ws.length.pred : ℝ) + 1 = ws.length := by
        have : ws.length ≠ 0 := by simpa using h0
        have : ws.length.pred + 1 = ws.length := Nat.succ_pred_eq_of_ne_zero this
        exact_mod_cast this
      have hmul : (ws.length : ℝ) * ε = ws.length.pred * ε + ε := by rw [← hlen]; ring
      simp only [Nat.pred_eq_sub_one, Nat.add_sub_cancel, zero_add]
      linarith

end chain

/-! ### The chunk `E` -/

section Chunk

variable {G : Type*} [Group G] {S ι : Type*} [DecidableEq S]

/-- The prefixes (as elements of the free group) of the freely reduced word of `w`. -/
def wordPrefixes (w : FreeGroup S) : List (FreeGroup S) :=
  (List.range (w.toWord.length + 1)).map fun k => FreeGroup.mk (w.toWord.take k)

theorem mk_take_mem_wordPrefixes (w : FreeGroup S) (k : ℕ) :
    FreeGroup.mk (w.toWord.take k) ∈ wordPrefixes w := by
  rcases le_total k w.toWord.length with h | h
  · exact List.mem_map.mpr ⟨k, List.mem_range.mpr (by omega), rfl⟩
  · rw [List.take_of_length_le h]
    exact List.mem_map.mpr ⟨w.toWord.length, List.mem_range.mpr (by omega),
      by rw [List.take_length]⟩

variable [Fintype S] [Fintype ι]

/-- The words whose values (and their inverses) form the chunk: `1`, `s^{±1}` (`s ∈ S`), the prefixes
of the reduced words of `R`, and the prefixes of the reduced word of `ab`. -/
def criterionWords (R : ι → FreeGroup S) (a b : S) : Finset (FreeGroup S) :=
  insert 1 (univ.image FreeGroup.of ∪ univ.image (fun s => (FreeGroup.of s)⁻¹) ∪
    univ.biUnion (fun k => (wordPrefixes (R k)).toFinset) ∪
    (wordPrefixes (FreeGroup.of a * FreeGroup.of b)).toFinset)

open Classical in
/-- **The chunk `E` of Theorem `thm:criterion`**: `1`, `S^{±1}`, the prefixes of the words of `R`
and of `ab`, and the inverses of these elements (evaluated in `G` by `π`). -/
noncomputable def criterionChunk (π : FreeGroup S →* G) (R : ι → FreeGroup S) (a b : S) :
    Finset G :=
  (criterionWords R a b).image π ∪ (criterionWords R a b).image fun w => (π w)⁻¹

/-- `l`: the largest length of a (freely reduced) word of `R`. -/
def maxLen (R : ι → FreeGroup S) : ℕ := univ.sup fun k => (R k).toWord.length

variable (π : FreeGroup S →* G) (R : ι → FreeGroup S) (a b : S)

theorem mem_criterionChunk {w : FreeGroup S} (hw : w ∈ criterionWords R a b) :
    π w ∈ criterionChunk π R a b := by
  classical
  unfold criterionChunk
  exact mem_union_left _ (mem_image_of_mem _ hw)

theorem inv_mem_criterionChunk {w : FreeGroup S} (hw : w ∈ criterionWords R a b) :
    (π w)⁻¹ ∈ criterionChunk π R a b := by
  classical
  unfold criterionChunk
  exact mem_union_right _ (mem_image_of_mem (fun w => (π w)⁻¹) hw)

theorem one_mem_criterionChunk : (1 : G) ∈ criterionChunk π R a b := by
  simpa using mem_criterionChunk π R a b (mem_insert_self _ _)

theorem of_mem_criterionChunk (s : S) : π (FreeGroup.of s) ∈ criterionChunk π R a b := by
  apply mem_criterionChunk
  simp [criterionWords]

theorem of_inv_mem_criterionChunk (s : S) :
    (π (FreeGroup.of s))⁻¹ ∈ criterionChunk π R a b :=
  inv_mem_criterionChunk π R a b (by simp [criterionWords])

theorem relPrefix_mem_criterionChunk (k : ι) (j : ℕ) :
    π (FreeGroup.mk ((R k).toWord.take j)) ∈ criterionChunk π R a b := by
  apply mem_criterionChunk
  simp only [criterionWords, mem_insert, mem_union, mem_biUnion, mem_univ, true_and,
    List.mem_toFinset]
  exact Or.inr (Or.inl (Or.inr ⟨k, mk_take_mem_wordPrefixes _ _⟩))

theorem abPrefix_mem_criterionChunk (j : ℕ) :
    π (FreeGroup.mk ((FreeGroup.of a * FreeGroup.of b).toWord.take j)) ∈
      criterionChunk π R a b := by
  apply mem_criterionChunk
  simp only [criterionWords, mem_insert, mem_union, List.mem_toFinset]
  exact Or.inr (Or.inr (mk_take_mem_wordPrefixes _ _))

end Chunk

/-! ### The transfer from a chunk model to a homomorphism of the free group -/

section Transfer

variable {G : Type*} [Group G] {S ι : Type*} [DecidableEq S] [Fintype S] [Fintype ι]
  (π : FreeGroup S →* G) (R : ι → FreeGroup S) (a b : S) {n : ℕ}

/-- The homomorphism `φ_f : FreeGroup S →* Sym_n`, `φ_f(s) = f(s)`. -/
def phiOfG (f : G → Perm (Fin n)) : FreeGroup S →* Perm (Fin n) :=
  FreeGroup.lift fun s => f (π (FreeGroup.of s))

omit [DecidableEq S] [Fintype S] in
theorem mk_eq_prod_letters (l : List (S × Bool)) :
    FreeGroup.mk l = (l.map fun x => FreeGroup.mk [x]).prod := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.map_cons, List.prod_cons, ← ih, FreeGroup.mul_mk]; rfl

theorem eps_nonneg_of {E : Finset G} {ε : ℝ} {f : G → Perm (Fin n)}
    (hf : IsEpsMorphism E ε f) (h1 : (1 : G) ∈ E) : 0 ≤ ε :=
  (Houghton.ham_nonneg _ _).trans (hf.2 1 h1 1 h1 (by simpa using h1))

variable {π R a b}

/-- Each letter `s^{±1}` costs at most `ε`. -/
theorem letter_bound {ε : ℝ} {f : G → Perm (Fin n)}
    (hf : IsEpsMorphism (criterionChunk π R a b) ε f) (x : S × Bool) :
    dH (f (π (FreeGroup.mk [x]))) (phiOfG π f (FreeGroup.mk [x])) ≤ ε := by
  have hε := eps_nonneg_of hf (one_mem_criterionChunk π R a b)
  obtain ⟨s, e⟩ := x
  have hof : phiOfG π f (FreeGroup.of s) = f (π (FreeGroup.of s)) := by simp [phiOfG]
  cases e with
  | true =>
    change dH (f (π (FreeGroup.of s))) (phiOfG π f (FreeGroup.of s)) ≤ ε
    rw [hof, Houghton.ham_self]; exact hε
  | false =>
    have hinv : (FreeGroup.mk [(s, false)] : FreeGroup S) = (FreeGroup.of s)⁻¹ := by
      rw [FreeGroup.of, FreeGroup.inv_mk]; rfl
    rw [hinv, map_inv, map_inv, hof]
    set y := π (FreeGroup.of s)
    have hm := hf.2 y (of_mem_criterionChunk π R a b s) y⁻¹
      (of_inv_mem_criterionChunk π R a b s) (by simpa using one_mem_criterionChunk π R a b)
    rw [mul_inv_cancel, hf.1] at hm
    calc dH (f y⁻¹) (f y)⁻¹ = dH (f y * f y⁻¹) (f y * (f y)⁻¹) :=
          (Houghton.ham_mul_left _ _ _).symm
      _ = dH 1 (f y * f y⁻¹) := by rw [mul_inv_cancel, Houghton.ham_comm]
      _ ≤ ε := hm

/-- A word all of whose prefixes lie in `E` is evaluated by `φ_f` within `(m - 1 + m) ε`, `m` its
length. -/
theorem word_bound_gen {ε : ℝ} {f : G → Perm (Fin n)}
    (hf : IsEpsMorphism (criterionChunk π R a b) ε f) (w : FreeGroup S)
    (hpre : ∀ k, π (FreeGroup.mk (w.toWord.take k)) ∈ criterionChunk π R a b) :
    dH (f (π w)) (phiOfG π f w) ≤
      (w.toWord.length.pred : ℝ) * ε + w.toWord.length * ε := by
  have e1 : ∀ v : List (S × Bool),
      π (FreeGroup.mk v) = (v.map fun x => π (FreeGroup.mk [x])).prod := by
    intro v; rw [mk_eq_prod_letters, map_list_prod, List.map_map]; rfl
  have e2 : ∀ v : List (S × Bool),
      phiOfG π f (FreeGroup.mk v) = (v.map fun x => phiOfG π f (FreeGroup.mk [x])).prod := by
    intro v; rw [mk_eq_prod_letters, map_list_prod, List.map_map]; rfl
  have key := chain_bound_gen (criterionChunk π R a b) ε f hf
    (fun x => π (FreeGroup.mk [x])) (fun x => phiOfG π f (FreeGroup.mk [x])) (fun _ => ε)
    (letter_bound hf) (fun x => by
      obtain ⟨s, e⟩ := x
      cases e
      · have : (FreeGroup.mk [(s, false)] : FreeGroup S) = (FreeGroup.of s)⁻¹ := by
          rw [FreeGroup.of, FreeGroup.inv_mk]; rfl
        simp only [this, map_inv]; exact of_inv_mem_criterionChunk π R a b s
      · exact of_mem_criterionChunk π R a b s)
    w.toWord (fun k => by rw [← e1]; exact hpre k)
  rw [← e1, ← e2, FreeGroup.mk_toWord] at key
  simpa [List.sum_replicate, List.map_const'] using key

/-- **Transfer** (Appendix `app:imported`, "Relator errors"): from a `(1 - r⁻¹)`-expansive
`r⁻¹`-morphism `f : E → Sym_n`, every relator has defect `≤ (2l - 1)/r` under `φ_f`, and
`dH (φ_f (ab)) 1 ≥ 1 - 4/r`. -/
theorem transfer_model_gen (hR1 : ∀ k, π (R k) = 1)
    (hab1 : π (FreeGroup.of a * FreeGroup.of b) ≠ 1) (hl : 1 ≤ maxLen R) {r : ℝ}
    {f : G → Perm (Fin n)} (hf : IsSoficModel (criterionChunk π R a b) r f) :
    (∀ k, dH (phiOfG π f (R k)) 1 ≤ (2 * maxLen R - 1) / r) ∧
      1 - 4 / r ≤ dH (phiOfG π f (FreeGroup.of a * FreeGroup.of b)) 1 := by
  have hε := eps_nonneg_of hf.1 (one_mem_criterionChunk π R a b)
  refine ⟨fun k => ?_, ?_⟩
  · have h := word_bound_gen hf.1 (R k) (relPrefix_mem_criterionChunk π R a b k)
    rw [hR1, hf.1.1, Houghton.ham_comm] at h
    refine h.trans ?_
    have hm : (R k).toWord.length ≤ maxLen R :=
      Finset.le_sup (f := fun k => (R k).toWord.length) (mem_univ k)
    have hl' : (1 : ℝ) ≤ maxLen R := by exact_mod_cast hl
    rw [div_eq_mul_inv]
    rcases Nat.eq_zero_or_pos (R k).toWord.length with h0 | h0
    · rw [h0]; simp only [Nat.pred_zero, CharP.cast_eq_zero, zero_mul, add_zero]
      exact mul_nonneg (by linarith) hε
    · have hpred : ((R k).toWord.length.pred : ℝ) = (R k).toWord.length - 1 := by
        rw [Nat.pred_eq_sub_one, Nat.cast_sub h0, Nat.cast_one]
      have hm' : ((R k).toWord.length : ℝ) ≤ maxLen R := by exact_mod_cast hm
      rw [hpred]; nlinarith
  · have h := word_bound_gen hf.1 _ (abPrefix_mem_criterionChunk π R a b)
    have hlen : (FreeGroup.of a * FreeGroup.of b).toWord.length ≤ 2 := by
      have := FreeGroup.norm_mul_le (FreeGroup.of a) (FreeGroup.of b)
      simp only [FreeGroup.norm_of] at this
      exact this
    have hlen' : ((FreeGroup.of a * FreeGroup.of b).toWord.length : ℝ) ≤ 2 := by
      exact_mod_cast hlen
    have hpred : ((FreeGroup.of a * FreeGroup.of b).toWord.length.pred : ℝ) ≤ 1 := by
      have : (FreeGroup.of a * FreeGroup.of b).toWord.length.pred ≤ 1 := by
        rw [Nat.pred_eq_sub_one]; omega
      exact_mod_cast this
    have hsep := hf.2 _ (abPrefix_mem_criterionChunk π R a b
      (FreeGroup.of a * FreeGroup.of b).toWord.length) 1 (one_mem_criterionChunk π R a b)
      (by rw [List.take_length, FreeGroup.mk_toWord]; exact hab1)
    rw [List.take_length, FreeGroup.mk_toWord, hf.1.1] at hsep
    have t := Houghton.ham_triangle (f (π (FreeGroup.of a * FreeGroup.of b)))
      (phiOfG π f (FreeGroup.of a * FreeGroup.of b)) 1
    rw [div_eq_mul_inv]
    nlinarith

end Transfer

/-! ### Theorem `thm:criterion` -/

section Criterion

variable {G : Type*} [Group G] {S ι : Type*} [DecidableEq S] [Fintype S] [Fintype ι]

/-- **Theorem `thm:criterion` (Counting criterion), permutation form, assuming the sector bound.**
Let `π : FreeGroup S →* G`, `R : ι → FreeGroup S` with `π (R k) = 1`, `R ia = a²`, `R ib = b²`,
`R iab = (ab)³`, and `π (ab) ≠ 1`; let `l = maxLen R` and `E = criterionChunk π R a b`. If
`Area_R([w_i x w_i⁻¹, w_j y w_j⁻¹]) ≤ Λ` for `i ≠ j`, `x, y ∈ {a, b}`, with `Λ ≥ 1`, then for every
`r ≥ 10⁸ N Λ (2l - 1)` every model size `n` of `E` at accuracy `r` has `log₂ n ≥ N/16`; in
particular `log₂ σ_E(r) ≥ N/16` whenever `σ_E(r)` is finite. -/
theorem counting_criterion (hS : Houghton.PermSectorBound.{0})
    (π : FreeGroup S →* G) (R : ι → FreeGroup S) (a b : S) (ia ib iab : ι)
    (hRa : R ia = FreeGroup.of a ^ 2) (hRb : R ib = FreeGroup.of b ^ 2)
    (hRab : R iab = (FreeGroup.of a * FreeGroup.of b) ^ 3)
    (hR1 : ∀ k, π (R k) = 1) (hab1 : π (FreeGroup.of a * FreeGroup.of b) ≠ 1)
    {N : ℕ} (w : Fin N → FreeGroup S) (Λ : ℕ) (hΛ : 1 ≤ Λ) (hw : TransportAreaLE R a b w Λ)
    (r : ℝ) (hr : (10 : ℝ) ^ 8 * N * Λ * (2 * maxLen R - 1) ≤ r) :
    (∀ n ∈ modelSizes (criterionChunk π R a b) r, (N : ℝ) / 16 ≤ Real.logb 2 n) ∧
      (∀ m : ℕ, profile (criterionChunk π R a b) r = m → (N : ℝ) / 16 ≤ Real.logb 2 m) := by
  have hmodel : ∀ n ∈ modelSizes (criterionChunk π R a b) r, (N : ℝ) / 16 ≤ Real.logb 2 n := by
    intro n hn
    obtain ⟨hn0, f, hf⟩ := hn
    rcases Nat.eq_zero_or_pos N with hN0 | hN
    · subst hN0
      simp only [Nat.cast_zero, zero_div]
      exact Real.logb_nonneg (by norm_num) (by exact_mod_cast hn0)
    have hl2 : 2 ≤ maxLen R := by
      have h := Finset.le_sup (f := fun k => (R k).toWord.length) (mem_univ ia)
      have h2 : (R ia).toWord.length = 2 := by
        rw [hRa]; exact FreeGroup.norm_of_pow a 2
      unfold maxLen; omega
    have hl2' : (2 : ℝ) ≤ maxLen R := by exact_mod_cast hl2
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hΛ1 : (1 : ℝ) ≤ Λ := by exact_mod_cast hΛ
    have hNΛ : (1 : ℝ) ≤ N * Λ := by nlinarith
    have hr8 : (10 : ℝ) ^ 8 ≤ r := by
      have : (10 : ℝ) ^ 8 ≤ (10 : ℝ) ^ 8 * N * Λ * (2 * maxLen R - 1) := by
        have : (1 : ℝ) ≤ N * Λ * (2 * maxLen R - 1) := by nlinarith
        nlinarith
      linarith
    have hrpos : 0 < r := by linarith
    obtain ⟨hrel, hab⟩ := transfer_model_gen hR1 hab1 (by omega) hf
    have hab' : 1 / 2 ≤ dH (phiOfG π f (FreeGroup.of a * FreeGroup.of b)) 1 := by
      have : 4 / r ≤ 1 / 2 := by rw [div_le_iff₀ hrpos]; linarith
      linarith
    have hδ : (10 : ℝ) ^ 8 * N * max 1 (Λ : ℝ) * ((2 * maxLen R - 1) / r) ≤ 1 := by
      rw [max_eq_right hΛ1, ← mul_div_assoc, div_le_one hrpos]; exact hr
    have := counting_criterion_model R a b ia ib iab hRa hRb hRab hS w Λ hw (phiOfG π f) _ hrel
      hab' hδ
    simpa using this
  exact ⟨hmodel, fun m hm => hmodel m (Houghton.mem_of_profile_eq hm)⟩

/-- Model sizes are antitone in the chunk: a model of `E` restricts to a model of any `E' ⊆ E`. -/
theorem modelSizes_anti {G : Type*} [Group G] {E E' : Finset G} (h : E' ⊆ E) (r : ℝ) :
    modelSizes E r ⊆ modelSizes E' r := by
  rintro n ⟨hn, f, ⟨h1, hm⟩, he⟩
  exact ⟨hn, f, ⟨h1, fun x hx y hy hxy => hm x (h hx) y (h hy) (h hxy)⟩,
    fun x hx y hy hne => he x (h hx) y (h hy) hne⟩

/-- **Theorem `thm:criterion` for any larger chunk** `E ⊇ criterionChunk π R a b` (e.g. the chunk of
Theorem A, via `E⁺ ⊆ E`). -/
theorem counting_criterion_of_subset (hS : Houghton.PermSectorBound.{0})
    (π : FreeGroup S →* G) (R : ι → FreeGroup S) (a b : S) (ia ib iab : ι)
    (hRa : R ia = FreeGroup.of a ^ 2) (hRb : R ib = FreeGroup.of b ^ 2)
    (hRab : R iab = (FreeGroup.of a * FreeGroup.of b) ^ 3)
    (hR1 : ∀ k, π (R k) = 1) (hab1 : π (FreeGroup.of a * FreeGroup.of b) ≠ 1)
    {N : ℕ} (w : Fin N → FreeGroup S) (Λ : ℕ) (hΛ : 1 ≤ Λ) (hw : TransportAreaLE R a b w Λ)
    (r : ℝ) (hr : (10 : ℝ) ^ 8 * N * Λ * (2 * maxLen R - 1) ≤ r)
    (E : Finset G) (hE : criterionChunk π R a b ⊆ E) :
    (∀ n ∈ modelSizes E r, (N : ℝ) / 16 ≤ Real.logb 2 n) ∧
      (∀ m : ℕ, profile E r = m → (N : ℝ) / 16 ≤ Real.logb 2 m) := by
  have h := (counting_criterion hS π R a b ia ib iab hRa hRb hRab hR1 hab1 w Λ hΛ hw r hr).1
  have hmodel : ∀ n ∈ modelSizes E r, (N : ℝ) / 16 ≤ Real.logb 2 n :=
    fun n hn => h n (modelSizes_anti hE r hn)
  exact ⟨hmodel, fun m hm => hmodel m (Houghton.mem_of_profile_eq hm)⟩

end Criterion

end Lamps
