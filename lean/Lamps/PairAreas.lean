import Lamps.Fillings
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Pair areas (Douglas–Mghirbi v1.2.0, Theorem `thm:pair-area`), abstract form

Given words `τ i` (`i : Fin N`) and `X i j` satisfying the four local identities of Lemma
`lem:local-filling` with area at most `L` (`LocalIds`), and `T u = ∏_{i ∈ supp u, increasing} τ i`,
`pair_area_abstract` bounds the area of `[T_u x T_u⁻¹, T_w y T_w⁻¹]` (`u ≠ w`, `x, y ∈ {a, b}`) by
`(20 N² + 28 N + 1) L ≤ 49 N² L`.  The proof follows the paper: one translation word
(`nf`: normal form by toggling, parity of counts), normalized clearing into a pivot (`G`),
and a single local filling.
-/

namespace Lamps
namespace PairArea

theorem AreaEqGen.congr {S ι : Type*} {R : ι → FreeGroup S} {u v u' v' : FreeGroup S} {n : ℕ}
    (h : AreaEqGen R u v n) (hu : u = u') (hv : v = v') : AreaEqGen R u' v' n := hu ▸ hv ▸ h

variable {N : ℕ} (τ : Fin N → F)

/-- The product of the `τ i` along a list. -/
def P (l : List (Fin N)) : F := (l.map τ).prod

@[simp] theorem P_nil : P τ [] = 1 := rfl
@[simp] theorem P_cons (i : Fin N) (l : List (Fin N)) : P τ (i :: l) = τ i * P τ l := by
  simp [P]
theorem P_append (l m : List (Fin N)) : P τ (l ++ m) = P τ l * P τ m := by simp [P]

/-- Insert `i` in order, or cancel it against an equal entry. -/
def toggle (i : Fin N) : List (Fin N) → List (Fin N)
  | [] => [i]
  | j :: l => if i < j then i :: j :: l else if i = j then l else j :: toggle i l

/-- Normal form: toggle the entries in from the right. -/
def nf : List (Fin N) → List (Fin N)
  | [] => []
  | i :: l => toggle i (nf l)

/-- The four local identities of Lemma `lem:local-filling`, with area at most `L`. -/
structure LocalIds (X : Fin N → Fin N → F) (L : ℕ) : Prop where
  sq : ∀ i, AreaLE (τ i * τ i) L
  swap : ∀ i j, i ≠ j → AreaLE (comm (τ i) (τ j)) L
  conj_ne : ∀ i j k, i ≠ j → k ≠ j → AreaLE (X i j * τ k * (X i j)⁻¹ * (τ k)⁻¹) L
  conj_eq : ∀ i j, i ≠ j → AreaLE (X i j * τ j * (X i j)⁻¹ * (τ i)⁻¹ * (τ j)⁻¹) L
  commX : ∀ i j, i ≠ j → ∀ x ∈ [a, b], AreaLE (comm (X i j) x) L
  locD : ∀ i, ∀ x ∈ [a, b], ∀ y ∈ [a, b], AreaLE (comm x (τ i * y * (τ i)⁻¹)) L

/-! ### Combinatorics of `toggle` and `nf` -/

theorem length_toggle_le (i : Fin N) (m : List (Fin N)) : (toggle i m).length ≤ m.length + 1 := by
  induction m with
  | nil => simp [toggle]
  | cons j m ih =>
    simp only [toggle]
    split_ifs
    · simp only [List.length_cons]; omega
    · simp only [List.length_cons]; omega
    · simp only [List.length_cons]; omega

theorem length_nf_le (l : List (Fin N)) : (nf l).length ≤ l.length := by
  induction l with
  | nil => simp [nf]
  | cons i l ih => simp only [nf, List.length_cons]; exact (length_toggle_le i _).trans (by omega)

theorem mem_toggle {i x : Fin N} {m : List (Fin N)} (hx : x ∈ toggle i m) : x = i ∨ x ∈ m := by
  induction m with
  | nil => simp [toggle] at hx; exact Or.inl hx
  | cons j m ih =>
    simp only [toggle] at hx
    split_ifs at hx with h1 h2
    · simp only [List.mem_cons] at hx ⊢; tauto
    · exact Or.inr (List.mem_cons_of_mem _ hx)
    · simp only [List.mem_cons] at hx ⊢
      rcases hx with hx | hx
      · exact Or.inr (Or.inl hx)
      · rcases ih hx with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)

theorem pairwise_toggle (i : Fin N) {m : List (Fin N)} (hm : m.Pairwise (· < ·)) :
    (toggle i m).Pairwise (· < ·) := by
  induction m with
  | nil => simp [toggle]
  | cons j m ih =>
    rw [List.pairwise_cons] at hm
    simp only [toggle]
    split_ifs with h1 h2
    · rw [List.pairwise_cons, List.pairwise_cons]
      refine ⟨?_, hm.1, hm.2⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact h1
      · exact h1.trans (hm.1 x hx)
    · exact hm.2
    · rw [List.pairwise_cons]
      refine ⟨?_, ih hm.2⟩
      intro x hx
      rcases mem_toggle hx with rfl | hx
      · exact lt_of_le_of_ne (not_lt.mp h1) (fun e => h2 e.symm)
      · exact hm.1 x hx

theorem pairwise_nf (l : List (Fin N)) : (nf l).Pairwise (· < ·) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons i l ih => exact pairwise_toggle i ih

theorem count_toggle (i k : Fin N) (m : List (Fin N)) :
    (toggle i m).count k % 2 = (m.count k + if i = k then 1 else 0) % 2 := by
  induction m with
  | nil =>
    simp only [toggle, List.count_cons, List.count_nil, beq_iff_eq]
    all_goals (split_ifs <;> omega)
  | cons j m ih =>
    by_cases h1 : i < j
    · simp only [toggle, h1, ↓reduceIte, List.count_cons, beq_iff_eq]
      all_goals (split_ifs <;> omega)
    · by_cases h2 : i = j
      · subst h2
        simp only [toggle, lt_irrefl, ↓reduceIte, List.count_cons, beq_iff_eq]
        all_goals (split_ifs <;> omega)
      · simp only [toggle, h1, h2, ↓reduceIte, List.count_cons, beq_iff_eq]
        all_goals (split_ifs at * <;> omega)

theorem count_nf (k : Fin N) (l : List (Fin N)) : (nf l).count k % 2 = l.count k % 2 := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    have h := count_toggle i k (nf l)
    simp only [nf, List.count_cons, beq_iff_eq]
    split_ifs at * <;> omega

/-! ### Areas -/

variable {τ} {X : Fin N → Fin N → F} {L : ℕ}

theorem inv_eq (h : LocalIds τ X L) (i : Fin N) : AreaEqGen rel (τ i)⁻¹ (τ i) L := by
  unfold AreaEqGen
  exact (h.sq i).inv.of_eq (by group)

theorem toggle_area (h : LocalIds τ X L) (i : Fin N) (m : List (Fin N)) :
    AreaEqGen rel (τ i * P τ m) (P τ (toggle i m)) ((m.length + 1) * L) := by
  induction m with
  | nil =>
    simp only [toggle, P_cons, P_nil]
    exact (AreaEqGen.refl _).mono (Nat.zero_le _)
  | cons j m ih =>
    simp only [toggle]
    split_ifs with h1 h2
    · simp only [P_cons]
      exact (AreaEqGen.refl _).mono (Nat.zero_le _)
    · rw [← h2]
      unfold AreaEqGen
      refine ((h.sq i).of_eq (by simp only [P_cons]; group)).mono ?_
      simp only [List.length_cons]; nlinarith
    · have s1 : AreaEqGen rel (τ i * P τ (j :: m)) (τ j * (τ i * P τ m)) L := by
        unfold AreaEqGen
        exact (h.swap i j h2).of_eq (by simp only [P_cons, comm]; group)
      have s2 := (AreaEqGen.refl (R := rel) (τ j)).mul ih
      refine (AreaEqGen.congr (s1.trans s2) rfl (by simp only [P_cons])).mono ?_
      simp only [List.length_cons]; nlinarith

theorem nf_area (h : LocalIds τ X L) (l : List (Fin N)) :
    AreaEqGen rel (P τ l) (P τ (nf l)) (l.length * (l.length + 1) * L) := by
  induction l with
  | nil => exact (AreaEqGen.refl _).mono (Nat.zero_le _)
  | cons i l ih =>
    have s1 := (AreaEqGen.refl (R := rel) (τ i)).mul ih
    have s2 := toggle_area h i (nf l)
    have hl := length_nf_le l
    have h3 : ((nf l).length + 1) * L ≤ (l.length + 1) * L := Nat.mul_le_mul_right _ (by omega)
    refine (AreaEqGen.congr (s1.trans s2) (by simp only [P_cons]) (by simp only [nf])).mono ?_
    simp only [List.length_cons]; nlinarith

theorem inv_P (h : LocalIds τ X L) (l : List (Fin N)) :
    AreaEqGen rel (P τ l)⁻¹ (P τ l.reverse) (l.length * L) := by
  induction l with
  | nil =>
    exact AreaEqGen.congr ((AreaEqGen.refl (R := rel) (1 : F)).mono (Nat.zero_le _))
      (by simp) (by simp)
  | cons i l ih =>
    have s := ih.mul (inv_eq h i)
    refine (AreaEqGen.congr s (by simp only [P_cons, mul_inv_rev])
      (by simp only [List.reverse_cons, P_append, P_cons, P_nil, mul_one])).mono ?_
    simp only [List.length_cons]; nlinarith

/-! ### Clearing -/

/-- `G j m = X_{i_k j} ⋯ X_{i_1 j}` for `m = [i₁, …, i_k]` (rightmost transvection first). -/
def G (X : Fin N → Fin N → F) (j : Fin N) : List (Fin N) → F
  | [] => 1
  | i :: m => G X j m * X i j

theorem conj_P_ne (h : LocalIds τ X L) {i j : Fin N} (hij : i ≠ j) (l : List (Fin N))
    (hl : ∀ k ∈ l, k ≠ j) : AreaEqGen rel (X i j * P τ l * (X i j)⁻¹) (P τ l) (l.length * L) := by
  induction l with
  | nil =>
    exact AreaEqGen.congr ((AreaEqGen.refl (R := rel) (1 : F)).mono (Nat.zero_le _))
      (by simp) (by simp)
  | cons k l ih =>
    have e1 : AreaEqGen rel (X i j * τ k * (X i j)⁻¹) (τ k) L :=
      h.conj_ne i j k hij (hl k List.mem_cons_self)
    have s := e1.mul (ih fun k' hk' => hl k' (List.mem_cons_of_mem _ hk'))
    refine (AreaEqGen.congr s (by simp only [P_cons]; group) (by simp only [P_cons])).mono ?_
    simp only [List.length_cons]; nlinarith

theorem clear_area (h : LocalIds τ X L) (j : Fin N) (m : List (Fin N)) (hnd : (j :: m).Nodup) :
    AreaEqGen rel (G X j m * P τ (j :: m) * (G X j m)⁻¹) (τ j) (m.length * (m.length + 3) * L) := by
  induction m with
  | nil =>
    exact AreaEqGen.congr ((AreaEqGen.refl (R := rel) (τ j)).mono (Nat.zero_le _))
      (by simp [G]) rfl
  | cons i m ih =>
    rw [List.nodup_cons, List.mem_cons, not_or, List.nodup_cons] at hnd
    obtain ⟨⟨hji, hjm⟩, him, hm⟩ := hnd
    have hij : i ≠ j := fun e => hji e.symm
    have ih' := ih (List.nodup_cons.mpr ⟨hjm, hm⟩)
    have e1 : AreaEqGen rel (X i j * τ j * (X i j)⁻¹) (τ j * τ i) L := by
      unfold AreaEqGen
      exact (h.conj_eq i j hij).of_eq (by group)
    have e2 : AreaEqGen rel (X i j * τ i * (X i j)⁻¹) (τ i) L := h.conj_ne i j i hij hij
    have e3 := conj_P_ne h hij m (fun k hk e => hjm (e ▸ hk))
    have e4 : AreaEqGen rel (τ j * τ i * (τ i * P τ m)) (τ j * P τ m) L := by
      unfold AreaEqGen
      exact ((h.sq i).conj (τ j)).of_eq (by group)
    have s1 := ((e1.mul (e2.mul e3)).trans e4)
    have s2 := (s1.conj (G X j m)).trans ih'
    refine (AreaEqGen.congr s2 (by simp only [G, P_cons]; group) rfl).mono ?_
    simp only [List.length_cons]; nlinarith

theorem comm_G (h : LocalIds τ X L) (j : Fin N) (z : F) (hz : z ∈ [a, b]) (m : List (Fin N))
    (hjm : j ∉ m) : AreaLE (comm (G X j m) z) (m.length * L) := by
  induction m with
  | nil => exact (AreaLEGen.of_eq_one (R := rel) (w := comm (G X j []) z) (by simp [G, comm])).mono (Nat.zero_le _)
  | cons i m ih =>
    rw [List.mem_cons, not_or] at hjm
    have hij : i ≠ j := fun e => hjm.1 e.symm
    have s := ((h.commX i j hij z hz).conj (G X j m)).mul (ih hjm.2)
    refine (s.of_eq ?_).mono ?_
    · simp only [G]; rw [comm_mul_left]
    · simp only [List.length_cons]; nlinarith

/-! ### The theorem -/

/-- The support of `u`, in increasing order. -/
def S (u : Fin N → Bool) : List (Fin N) := (List.finRange N).filter fun i => u i

/-- `T_u = ∏_{i ∈ supp u} τ i`, in increasing order. -/
def T (τ : Fin N → F) (u : Fin N → Bool) : F := P τ (S u)

theorem count_S (u : Fin N → Bool) (k : Fin N) : (S u).count k = if u k then 1 else 0 := by
  unfold S
  split_ifs with hk
  · rw [List.count_filter (by simpa using hk)]
    have h1 := List.nodup_iff_count_le_one.mp (List.nodup_finRange N) k
    have h2 : 0 < (List.finRange N).count k := List.count_pos_iff.mpr (List.mem_finRange k)
    omega
  · exact List.count_eq_zero_of_not_mem (by simp [hk])

theorem length_S (u : Fin N → Bool) : (S u).length ≤ N := by
  unfold S
  exact (List.length_filter_le _ _).trans (by simp)

/-- **Theorem `thm:pair-area`, abstract form.** -/
theorem pair_area_abstract (h : LocalIds τ X L) (u w : Fin N → Bool) (huw : u ≠ w)
    (x : F) (hx : x ∈ [a, b]) (y : F) (hy : y ∈ [a, b]) :
    AreaLE (comm (T τ u * x * (T τ u)⁻¹) (T τ w * y * (T τ w)⁻¹))
      ((20 * N ^ 2 + 28 * N + 1) * L) := by
  classical
  set l := (S u).reverse ++ S w with hl
  -- the normal form is nonempty and without repetitions
  obtain ⟨k, hk⟩ := Function.ne_iff.mp huw
  have hcount : (nf l).count k % 2 = 1 := by
    rw [count_nf, hl, List.count_append, List.count_reverse, count_S, count_S]
    cases hu : u k <;> cases hw : w k <;> simp_all
  have hnd : (nf l).Nodup := (pairwise_nf l).imp ne_of_lt
  obtain ⟨j, m', hm⟩ : ∃ j m', nf l = j :: m' := by
    rcases hnf : nf l with _ | ⟨j, m'⟩
    · rw [hnf] at hcount; simp at hcount
    · exact ⟨j, m', rfl⟩
  rw [hm] at hnd
  have hmN : m'.length + 1 ≤ N := by
    have := hnd.length_le_card; simpa using this
  have hjm : j ∉ m' := (List.nodup_cons.mp hnd).1
  have hlen : l.length ≤ 2 * N := by
    rw [hl, List.length_append, List.length_reverse]
    have := length_S u; have := length_S w; omega
  -- Step 1: `Z = T_u⁻¹ T_w ≈ P (nf l)`
  set Z := (T τ u)⁻¹ * T τ w with hZ
  have c1 : AreaEqGen rel Z (P τ l) ((S u).length * L + 0) :=
    AreaEqGen.congr ((inv_P h (S u)).mul (AreaEqGen.refl (T τ w))) rfl
      (by rw [hl, P_append]; rfl)
  have c2 := nf_area h l
  rw [hm] at c2
  -- Step 2: clearing
  have c3 : AreaEqGen rel (P τ (j :: m')) ((G X j m')⁻¹ * τ j * (G X j m')) (m'.length * (m'.length + 3) * L) :=
    AreaEqGen.congr ((clear_area h j m' hnd).conj (G X j m')⁻¹) (by group) (by group)
  have cZ := (c1.trans c2).trans c3
  set c := (S u).length * L + 0 + l.length * (l.length + 1) * L + m'.length * (m'.length + 3) * L
    with hc
  -- Step 3
  have hZy : AreaEqGen rel (Z * y * Z⁻¹) (((G X j m')⁻¹ * τ j * (G X j m')) * y * ((G X j m')⁻¹ * τ j * (G X j m'))⁻¹)
      (c + 0 + c) := (cZ.mul (AreaEqGen.refl y)).mul cZ.inv
  have k1 := AreaEqGen.comm (AreaEqGen.refl (R := rel) x) hZy
  have hGy : AreaEqGen rel ((G X j m') * y * (G X j m')⁻¹) y (m'.length * L) := by
    unfold AreaEqGen
    exact (comm_G h j y hy m' hjm).of_eq (by simp only [comm])
  have hGx : AreaEqGen rel ((G X j m') * x * (G X j m')⁻¹) x (m'.length * L) := by
    unfold AreaEqGen
    exact (comm_G h j x hx m' hjm).of_eq (by simp only [comm])
  have k2 : AreaEqGen rel (((G X j m')⁻¹ * τ j * (G X j m')) * y * ((G X j m')⁻¹ * τ j * (G X j m'))⁻¹)
      ((G X j m')⁻¹ * (τ j * y * (τ j)⁻¹) * (G X j m')) (m'.length * L) :=
    AreaEqGen.congr (hGy.conj ((G X j m')⁻¹ * τ j)) (by group) (by group)
  have k3 := AreaEqGen.comm (AreaEqGen.refl (R := rel) x) k2
  have k4 : AreaEqGen rel (comm x ((G X j m')⁻¹ * (τ j * y * (τ j)⁻¹) * (G X j m')))
      ((G X j m')⁻¹ * comm x (τ j * y * (τ j)⁻¹) * (G X j m')) (2 * (m'.length * L) + 2 * 0) :=
    AreaEqGen.congr ((AreaEqGen.comm hGx (AreaEqGen.refl (τ j * y * (τ j)⁻¹))).conj (G X j m')⁻¹)
      (by simp only [comm]; group) (by group)
  have k5 : AreaLE ((G X j m')⁻¹ * comm x (τ j * y * (τ j)⁻¹) * (G X j m')) L := by
    have := (h.locD j x hx y hy).conj (G X j m')⁻¹
    simpa using this
  have hcomm := AreaLEGen.of_areaEq (k1.trans (k3.trans k4)) k5
  have e : comm (T τ u * x * (T τ u)⁻¹) (T τ w * y * (T τ w)⁻¹) =
      T τ u * comm x (Z * y * Z⁻¹) * (T τ u)⁻¹ := by
    rw [hZ]; simp only [comm]; group
  rw [e]
  refine (hcomm.conj (T τ u)).mono ?_
  have b1 : (S u).length * L ≤ N * L := Nat.mul_le_mul_right _ (length_S u)
  have b2 : l.length * (l.length + 1) * L ≤ 2 * N * (2 * N + 1) * L :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul hlen (by omega))
  have b3 : m'.length * (m'.length + 3) * L ≤ N * (N + 3) * L :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul (by omega) (by omega))
  have b4 : m'.length * L ≤ N * L := Nat.mul_le_mul_right _ (by omega)
  rw [hc]
  nlinarith [b1, b2, b3, b4]

end PairArea
end Lamps
