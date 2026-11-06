import Lamps.Group
import Mathlib.GroupTheory.FreeGroup.Reduce

/-!
# The chunk `E` of Theorem A

`E ⊆ Γ` consists of `1`, the generators `p, q, t, c, a` and their inverses, the elements represented
by the prefixes of the 25 freely reduced relation words (`FreeGroup.toWord`), and the inverses of
these elements.
-/

namespace Lamps

/-- The evaluation map onto `Γ`. -/
def ρΓ' : F →* Γ := ρΓ.rangeRestrict

/-- The prefixes (as elements of `F`) of the freely reduced word of `w`. -/
def prefixesF (w : F) : List F :=
  (List.range (w.toWord.length + 1)).map fun k => FreeGroup.mk (w.toWord.take k)

/-- The generators, their inverses and `1`. -/
def genWords : List F := [1, p, q, t, c, a, p⁻¹, q⁻¹, t⁻¹, c⁻¹, a⁻¹]

/-- All words whose values (and inverses) form `E`. -/
def chunkWordsL : List F := genWords ++ (List.finRange 25).flatMap fun i => prefixesF (rel i)

open Classical in
/-- **The chunk `E` of Theorem A.** -/
noncomputable def E : Finset Γ :=
  (chunkWordsL.map ρΓ').toFinset ∪ (chunkWordsL.map fun w => (ρΓ' w)⁻¹).toFinset

theorem mem_E_of {w : F} (hw : w ∈ chunkWordsL) : ρΓ' w ∈ E := by
  classical
  unfold E; apply Finset.mem_union_left; rw [List.mem_toFinset]
  exact List.mem_map.mpr ⟨w, hw, rfl⟩

theorem inv_mem_E_of {w : F} (hw : w ∈ chunkWordsL) : (ρΓ' w)⁻¹ ∈ E := by
  classical
  unfold E; apply Finset.mem_union_right; rw [List.mem_toFinset]
  exact List.mem_map.mpr ⟨w, hw, rfl⟩

theorem one_mem_E : (1 : Γ) ∈ E := by
  have := mem_E_of (w := 1) (List.mem_append_left _ (by
    unfold genWords; simp only [List.mem_cons, true_or]))
  simpa using this

theorem inv_mem_E {x : Γ} (hx : x ∈ E) : x⁻¹ ∈ E := by
  classical
  unfold E at hx ⊢
  rcases Finset.mem_union.mp hx with h | h
  · apply Finset.mem_union_right
    rw [List.mem_toFinset] at h ⊢
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp h
    exact List.mem_map.mpr ⟨w, hw, rfl⟩
  · apply Finset.mem_union_left
    rw [List.mem_toFinset] at h ⊢
    obtain ⟨w, hw, hx⟩ := List.mem_map.mp h
    rw [← hx, inv_inv]
    exact List.mem_map.mpr ⟨w, hw, rfl⟩

theorem prefix_mem_E (i : Fin 25) (k : ℕ) (hk : k ≤ (rel i).toWord.length) :
    ρΓ' (FreeGroup.mk ((rel i).toWord.take k)) ∈ E := by
  apply mem_E_of
  simp only [chunkWordsL, List.mem_append, List.mem_flatMap, List.mem_finRange, true_and]
  right
  exact ⟨i, List.mem_map.mpr ⟨k, List.mem_range.mpr (by omega), rfl⟩⟩

theorem mem_E_of_eq {x : F} (j : Fin 25) (k : ℕ) (hk : k ≤ (rel j).toWord.length)
    (h : FreeGroup.mk ((rel j).toWord.take k) = x) : ρΓ' x ∈ E := by
  rw [← h]; exact prefix_mem_E j k hk

/-- **`E⁺ ⊆ E`** (proof of Theorem A): with `S⁺ = S ∪ {b}`, `b = a c⁴`, and
`R⁺ = R ∪ {b⁻¹ a c⁴, b², (ab)³}`, the new elements of the chunk `E⁺` are `b^{±1}`, the prefixes
`b⁻¹, c⁻⁴, c⁻³, c⁻², c⁻¹` of `b⁻¹ a c⁴`, the prefixes `b, ab, aba, abab, ababa` of `b²`, `(ab)³`, and
their inverses; all lie in `E`. -/
theorem Eplus_sub :
    (∀ x ∈ [b, a * b, a * b * a, a * b * a * b, a * b * a * b * a, c ^ 2, c ^ 3, c, a],
      ρΓ' x ∈ E ∧ (ρΓ' x)⁻¹ ∈ E) ∧ ρΓ' (c ^ 4) ∈ E ∧ (ρΓ' (c ^ 4))⁻¹ ∈ E := by
  have hb : ρΓ' b ∈ E := mem_E_of_eq 19 5 (by decide +kernel) (by decide +kernel)
  have hab : ρΓ' (a * b) ∈ E := mem_E_of_eq 20 6 (by decide +kernel) (by decide +kernel)
  have haba : ρΓ' (a * b * a) ∈ E := mem_E_of_eq 20 7 (by decide +kernel) (by decide +kernel)
  have habab : ρΓ' (a * b * a * b) ∈ E := mem_E_of_eq 20 12 (by decide +kernel) (by decide +kernel)
  have hababa : ρΓ' (a * b * a * b * a) ∈ E := mem_E_of_eq 20 13 (by decide +kernel) (by decide +kernel)
  have hc2 : ρΓ' (c ^ 2) ∈ E := mem_E_of_eq 7 2 (by decide +kernel) (by decide +kernel)
  have hc3 : ρΓ' (c ^ 3) ∈ E := mem_E_of_eq 7 3 (by decide +kernel) (by decide +kernel)
  have hc : ρΓ' c ∈ E := mem_E_of (List.mem_append_left _ (by
    unfold genWords; simp only [List.mem_cons, true_or, or_true]))
  have ha : ρΓ' a ∈ E := mem_E_of (List.mem_append_left _ (by
    unfold genWords; simp only [List.mem_cons, true_or, or_true]))
  have hc4 : ρΓ' (c ^ 4) = ρΓ' (a * b) := Subtype.ext (by
    show ρΓ (c ^ 4) = ρΓ (a * b); rw [map_pow]; exact structure_a.2.2)
  refine ⟨?_, by rw [hc4]; exact hab, by rw [hc4]; exact inv_mem_E hab⟩
  have key : ∀ y : F, ρΓ' y ∈ E → ρΓ' y ∈ E ∧ (ρΓ' y)⁻¹ ∈ E := fun y h => ⟨h, inv_mem_E h⟩
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨key _ hb, key _ hab, key _ haba, key _ habab, key _ hababa, key _ hc2, key _ hc3,
    key _ hc, key _ ha⟩

end Lamps
