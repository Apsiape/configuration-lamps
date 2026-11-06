import Lamps.Criterion
import Lamps.Chunk
import Lamps.Interfaces

/-!
# Theorem A(a): the lower bound `log₂ σ_E(r) ≥ c r / (log₂ r)^{2 + p_H}`

Proof of Theorem `thm:main-group`(a) (Section `sec:profile`, "Proof of Theorem A"):

* `S⁺` = the five generators `p, q, t, c, a` (letters `0–4`) and `b` (letter `5`), with evaluation
  `πP = ρΓ' ∘ σ6`, where `σ6 : FreeGroup (Fin 6) →* F` expands the letter `5` to the word `b = a c⁴`.
* `R⁺` (`relP`) = the 25 relations of `R` (lifted along `ι6 : F → FreeGroup (Fin 6)`) and the three
  words `b⁻¹ a c⁴`, `b²`, `(ab)³` in the letters of `S⁺`; its largest reduced length is `24`
  (`maxLen_relP`).
* The chunk of Theorem `thm:criterion` for `S⁺, R⁺` is contained in `E` (`criterionChunk_sub_E`,
  via `Eplus_sub`).
* The transport words are the `2^N` words `T_u` of `PairAreaStatement` (the polynomial form of
  Theorem `thm:pair-area`, taken as the hypothesis `hP`), lifted to `S⁺`; their commutators have
  `R⁺`-area `≤ Λ_N + 4` (each of the at most four letters `b^{±1}` costs one relation `b⁻¹ a c⁴`).
* `Lamps.HoughtonTools` (area algebra) cannot be imported next to `Houghton.Analysis` (both define
  `Houghton.hc`), so the few `AreaLEGen` facts needed are reproved here (`areaTA_*`).
* Arithmetic: with `K₀ = 10⁸ (C+4)(2l-1)`, `X = r / ((log₂ r)^κ K₀)` and `N = ⌊log₂ ⌊X⌋⌋`, the
  criterion applies when `X ≥ 2`; for `X < 2` the trivial bound `log₂ σ_E(r) ≥ 1` (since `ab ≠ 1`)
  suffices. (This choice of `N` replaces the paper's `⌊log r' − κ log log r'⌋`; same conclusion.)
-/

namespace Lamps

open Houghton (dH modelSizes profile)

/-- Words in the six letters of `S⁺`: `0–4 = p, q, t, c, a` and `5 = b`. -/
abbrev F6 := FreeGroup (Fin 6)

/-- The inclusion of the five-letter words. -/
def ι6 : F →* F6 := FreeGroup.map Fin.castSucc

/-- The letter `b` of `S⁺`. -/
def bP : F6 := FreeGroup.of 5

/-- Expansion of the letter `b` into the word `a c⁴`. -/
def σ6 : F6 →* F :=
  FreeGroup.lift fun i : Fin 6 => if h : (i : ℕ) < 5 then FreeGroup.of ⟨i, h⟩ else b

/-- The evaluation `S⁺ → Γ`. -/
def πP : F6 →* Γ := ρΓ'.comp σ6

/-- `R⁺`: the 25 relations and `b⁻¹ a c⁴`, `b²`, `(ab)³`. -/
def relP : Fin 25 ⊕ Fin 3 → F6 :=
  Sum.elim (fun i => ι6 (rel i)) ![bP⁻¹ * ι6 a * ι6 c ^ 4, bP ^ 2, (FreeGroup.of 4 * bP) ^ 3]

theorem σ6_ι6 (x : F) : σ6 (ι6 x) = x := by
  have h : σ6.comp ι6 = MonoidHom.id F := by
    ext i
    simp only [MonoidHom.comp_apply, ι6, FreeGroup.map.of, σ6, FreeGroup.lift_apply_of,
      MonoidHom.id_apply]
    split_ifs with h
    · rfl
    · exact absurd (by simp) h
  exact DFunLike.congr_fun h x

theorem σ6_bP : σ6 bP = b := by
  simp only [σ6, bP, FreeGroup.lift_apply_of]; rfl

theorem σ6_of4 : σ6 (FreeGroup.of 4) = a := by
  simp only [σ6, FreeGroup.lift_apply_of]; rfl

theorem ι6_a : ι6 a = FreeGroup.of 4 := by simp only [ι6, a, FreeGroup.map.of]; rfl

theorem ρΓ'_eq_one {w : F} (h : ρΓ w = 1) : ρΓ' w = 1 := Subtype.ext h

theorem ρΓ'_ne_one {w : F} (h : ρΓ w ≠ 1) : ρΓ' w ≠ 1 := by
  intro h'; apply h
  have := congrArg Subtype.val h'
  rwa [ρΓ', MonoidHom.coe_rangeRestrict, OneMemClass.coe_one] at this

theorem πP_apply (x : F6) : πP x = ρΓ' (σ6 x) := rfl

theorem rel18 : rel 18 = a ^ 2 := by decide +kernel
theorem rel19 : rel 19 = b ^ 2 := by decide +kernel
theorem rel20 : rel 20 = (a * b) ^ 3 := by decide +kernel

theorem relP_one (k : Fin 25 ⊕ Fin 3) : πP (relP k) = 1 := by
  rcases k with i | k
  · simp only [relP, Sum.elim_inl, πP, MonoidHom.comp_apply, σ6_ι6]
    exact ρΓ'_eq_one (rho_rel i)
  · fin_cases k
    · show πP (bP⁻¹ * ι6 a * ι6 c ^ 4) = 1
      rw [πP_apply]
      have e : σ6 (bP⁻¹ * ι6 a * ι6 c ^ 4) = 1 := by
        simp only [map_mul, map_inv, map_pow, σ6_ι6, σ6_bP, b]; group
      rw [e, map_one]
    · show πP (bP ^ 2) = 1
      rw [πP_apply, map_pow, σ6_bP, ← rel19]
      exact ρΓ'_eq_one (rho_rel 19)
    · show πP ((FreeGroup.of 4 * bP) ^ 3) = 1
      rw [πP_apply, map_pow, map_mul,
        σ6_bP, σ6_of4, ← rel20]
      exact ρΓ'_eq_one (rho_rel 20)

theorem ab_ne_one : πP (FreeGroup.of 4 * FreeGroup.of 5) ≠ 1 := by
  rw [πP_apply, map_mul, show (FreeGroup.of 5 : F6) = bP from rfl, σ6_bP, σ6_of4]
  exact ρΓ'_ne_one rho_ab_ne_one

theorem relP_a : relP (Sum.inl 18) = FreeGroup.of 4 ^ 2 := by
  simp only [relP, Sum.elim_inl]; rw [rel18, map_pow, ι6_a]

/-- The longest reduced word of `R⁺` has length `l = 24`. -/
theorem maxLen_relP : maxLen relP = 24 := by decide +kernel

/-! ### `E⁺ ⊆ E` -/

theorem toWord_map_inj {α β : Type*} [DecidableEq α] [DecidableEq β] {f : α → β}
    (hf : Function.Injective f) (x : FreeGroup α) :
    (FreeGroup.map f x).toWord = x.toWord.map fun p => (f p.1, p.2) := by
  conv_lhs => rw [← FreeGroup.mk_toWord (x := x)]
  rw [FreeGroup.map.mk, FreeGroup.toWord_mk, FreeGroup.IsReduced.reduce_eq]
  have h := FreeGroup.isReduced_toWord (x := x)
  unfold FreeGroup.IsReduced at h ⊢
  rw [List.isChain_map]
  exact h.imp fun p q hpq e => hpq (hf e)

/-- The good words: their values lie in `E`. -/
def goodWords : List F :=
  [1, p, q, t, c, a, b, b⁻¹, a * b, a * b * a, a * b * a * b, a * b * a * b * a, (c ^ 4)⁻¹,
    (c ^ 3)⁻¹, (c ^ 2)⁻¹, c⁻¹]

theorem good_mem_E : ∀ y ∈ goodWords, ρΓ' y ∈ E := by
  obtain ⟨h1, h4, h4'⟩ := Eplus_sub
  simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true] at h1
  obtain ⟨hb, hab, haba, habab, hababa, hc2, hc3, hc, ha⟩ := h1
  have hg : ∀ y ∈ genWords, ρΓ' y ∈ E := fun y hy => mem_E_of (List.mem_append_left _ hy)
  simp only [goodWords, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true, map_inv]
  exact ⟨hg _ (by simp [genWords]), hg _ (by simp [genWords]), hg _ (by simp [genWords]),
    hg _ (by simp [genWords]), hg _ (by simp [genWords]), hg _ (by simp [genWords]), hb.1, hb.2,
    hab.1, haba.1, habab.1, hababa.1, h4', hc3.2, hc2.2, hc.2⟩

theorem new_prefixes_good : ∀ k : Fin 3, ∀ j < (relP (Sum.inr k)).toWord.length,
    σ6 (FreeGroup.mk ((relP (Sum.inr k)).toWord.take j)) ∈ goodWords := by
  decide +kernel

theorem ab_prefixes_good : ∀ j ≤ (FreeGroup.of 4 * FreeGroup.of 5 : F6).toWord.length,
    σ6 (FreeGroup.mk ((FreeGroup.of 4 * FreeGroup.of 5 : F6).toWord.take j)) ∈ goodWords := by
  decide +kernel

theorem gens_good : ∀ s : Fin 6, σ6 (FreeGroup.of s) ∈ goodWords := by decide +kernel

/-- **`E⁺ ⊆ E`**: the chunk of Theorem `thm:criterion` for `S⁺, R⁺` lies in the chunk `E`. -/
theorem criterionChunk_sub_E : criterionChunk πP relP 4 5 ⊆ E := by
  have hπ : ∀ x, πP x = ρΓ' (σ6 x) := fun _ => rfl
  have hpre : ∀ (w : F6) (j : ℕ), FreeGroup.mk (w.toWord.take j) ∈ wordPrefixes w →
      ∃ j' ≤ w.toWord.length, FreeGroup.mk (w.toWord.take j) = FreeGroup.mk (w.toWord.take j') := by
    intro w j _
    exact ⟨min j w.toWord.length, min_le_right _ _, by
      rcases le_total j w.toWord.length with h | h
      · rw [min_eq_left h]
      · rw [min_eq_right h, List.take_of_length_le h, List.take_length]⟩
  have key : ∀ w ∈ criterionWords relP 4 5, πP w ∈ E := by
    intro w hw
    simp only [criterionWords, Finset.mem_insert, Finset.mem_union, Finset.mem_image,
      Finset.mem_univ, true_and, Finset.mem_biUnion, List.mem_toFinset] at hw
    rcases hw with rfl | ((⟨s, rfl⟩ | ⟨s, rfl⟩) | ⟨k, hk⟩) | hk
    · rw [map_one]; exact one_mem_E
    · rw [hπ]; exact good_mem_E _ (gens_good s)
    · rw [map_inv, hπ]; exact inv_mem_E (good_mem_E _ (gens_good s))
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hk
      have hj' : j ≤ (relP k).toWord.length := by have := List.mem_range.mp hj; omega
      rcases k with i | k
      · have e : (relP (Sum.inl i)).toWord =
            (rel i).toWord.map fun p => (Fin.castSucc p.1, p.2) :=
          toWord_map_inj (Fin.castSucc_injective 5) (rel i)
        have hw : FreeGroup.mk ((relP (Sum.inl i)).toWord.take j) =
            ι6 (FreeGroup.mk ((rel i).toWord.take j)) := by
          rw [e, ← List.map_take]; simp only [ι6, FreeGroup.map.mk]
        rw [hw, hπ, σ6_ι6]
        rw [e, List.length_map] at hj'
        exact prefix_mem_E i j hj'
      · rcases lt_or_eq_of_le hj' with hlt | heq
        · rw [hπ]; exact good_mem_E _ (new_prefixes_good k j hlt)
        · rw [heq, List.take_length, FreeGroup.mk_toWord, relP_one]; exact one_mem_E
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hk
      rw [hπ]; exact good_mem_E _ (ab_prefixes_good j (by have := List.mem_range.mp hj; omega))
  intro x hx
  unfold criterionChunk at hx
  rcases (@Finset.mem_union _ (Classical.decEq _) _ _ _).mp hx with h | h
  · obtain ⟨w, hw, rfl⟩ := (@Finset.mem_image _ _ (Classical.decEq _) _ _ _).mp h
    exact key w hw
  · obtain ⟨w, hw, rfl⟩ := (@Finset.mem_image _ _ (Classical.decEq _) _ _ _).mp h
    exact inv_mem_E (key w hw)

/-! ### Areas with respect to `R⁺` -/

/-! ### Area algebra (`AreaLEGen`), reproved locally -/

section AreaTA

variable {S ι : Type*} {R : ι → FreeGroup S}

theorem areaTA_mono {w : FreeGroup S} {n m : ℕ} (h : AreaLEGen R w n) (hnm : n ≤ m) :
    AreaLEGen R w m := by
  obtain ⟨cs, hl, hp⟩ := h; exact ⟨cs, hl.trans hnm, hp⟩

theorem areaTA_one : AreaLEGen R 1 0 := ⟨[], le_rfl, by simp⟩

theorem areaTA_of_eq {w w' : FreeGroup S} {n : ℕ} (h : AreaLEGen R w n) (e : w = w') :
    AreaLEGen R w' n := e ▸ h

theorem areaTA_rel (k : ι) (e : Bool) :
    AreaLEGen R (if e then R k else (R k)⁻¹) 1 :=
  ⟨[(1, k, e)], le_rfl, by simp⟩

theorem areaTA_mul {u v : FreeGroup S} {n m : ℕ} (hu : AreaLEGen R u n) (hv : AreaLEGen R v m) :
    AreaLEGen R (u * v) (n + m) := by
  obtain ⟨cs, hl, rfl⟩ := hu
  obtain ⟨ds, hl', rfl⟩ := hv
  exact ⟨cs ++ ds, by simp only [List.length_append]; omega, by simp⟩

theorem areaTA_conj {w : FreeGroup S} {n : ℕ} (g : FreeGroup S) (h : AreaLEGen R w n) :
    AreaLEGen R (g * w * g⁻¹) n := by
  obtain ⟨cs, hl, rfl⟩ := h
  refine ⟨cs.map fun x => (g * x.1, x.2), by simpa using hl, ?_⟩
  show ((cs.map fun x => (g * x.1, x.2)).map (cellW R)).prod = g * (cs.map (cellW R)).prod * g⁻¹
  clear hl
  induction cs with
  | nil => simp
  | cons x cs ih =>
    simp only [List.map_cons, List.prod_cons] at ih ⊢
    rw [ih]
    simp only [cellW]; group

end AreaTA

/-- `R`-areas lift to `R⁺`-areas along `ι6`. -/
theorem areaTA_ι6 {w : F} {n : ℕ} (h : AreaLE w n) : AreaLEGen relP (ι6 w) n := by
  obtain ⟨cs, hl, rfl⟩ := h
  refine ⟨cs.map fun x => (ι6 x.1, Sum.inl x.2.1, x.2.2), by simpa using hl, ?_⟩
  show _ = ι6 (cs.map (cellW rel)).prod
  rw [map_list_prod, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  rintro ⟨g, k, e⟩ -
  cases e <;> simp [cellW, relP]

/-- Perturbing both entries of a commutator by `Z, W` costs `2 Area(Z) + 2 Area(W)`. -/
theorem areaLEGen_commG_mul {S ι : Type*} {R : ι → FreeGroup S} {P Q Z W : FreeGroup S}
    {n z w : ℕ} (h : AreaLEGen R (commG P Q) n) (hZ : AreaLEGen R Z z) (hW : AreaLEGen R W w)
    (hZ' : AreaLEGen R Z⁻¹ z) (hW' : AreaLEGen R W⁻¹ w) :
    AreaLEGen R (commG (P * Z) (Q * W)) (z + w + z + w + n) := by
  have := areaTA_mul (areaTA_mul (areaTA_mul (areaTA_mul (areaTA_conj P hZ)
    (areaTA_conj (P * Q) hW)) (areaTA_conj (P * Q) hZ')) (areaTA_conj (P * Q * P⁻¹) hW')) h
  exact areaTA_of_eq this (by simp only [commG]; group)

theorem letter_split (x : F6) (hx : x ∈ [FreeGroup.of 4, FreeGroup.of 5]) :
    ∃ x' ∈ [a, b], ∃ Z, x = ι6 x' * Z ∧ AreaLEGen relP Z 1 ∧ AreaLEGen relP Z⁻¹ 1 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact ⟨a, by simp, 1, by rw [ι6_a, mul_one], areaTA_mono areaTA_one (by norm_num),
      areaTA_mono (by simpa using (areaTA_one : AreaLEGen relP 1 0)) (by norm_num)⟩
  · refine ⟨b, by simp, (relP (Sum.inr 0))⁻¹, ?_, by simpa using areaTA_rel (R := relP) _ false,
      by simpa using areaTA_rel (R := relP) (Sum.inr 0) true⟩
    show FreeGroup.of 5 = ι6 (a * c ^ 4) * (bP⁻¹ * ι6 a * ι6 c ^ 4)⁻¹
    simp only [map_mul, map_pow, bP]; group

/-- The `R⁺`-area of the lifted commutators is at most `Λ_N + 4`. -/
theorem transportAreaLE_lift {N M : ℕ} (T : (Fin N → Bool) → F) (n : ℕ)
    (hT : ∀ u w : Fin N → Bool, u ≠ w → ∀ x ∈ [a, b], ∀ y ∈ [a, b],
      AreaLE (comm (T u * x * (T u)⁻¹) (T w * y * (T w)⁻¹)) n)
    (e : Fin M ≃ (Fin N → Bool)) :
    TransportAreaLE relP 4 5 (fun i => ι6 (T (e i))) (n + 4) := by
  intro i j hij x hx y hy
  obtain ⟨x', hx', Z, rfl, hZ, hZ'⟩ := letter_split x hx
  obtain ⟨y', hy', W, rfl, hW, hW'⟩ := letter_split y hy
  have h0 := areaTA_ι6 (hT (e i) (e j) (fun h => hij (e.injective h)) x' hx' y' hy')
  have h1 : AreaLEGen relP (commG (ι6 (T (e i)) * ι6 x' * (ι6 (T (e i)))⁻¹)
      (ι6 (T (e j)) * ι6 y' * (ι6 (T (e j)))⁻¹)) n :=
    areaTA_of_eq h0 (by simp only [comm, commG, map_mul, map_inv])
  have h2 := areaLEGen_commG_mul h1 (areaTA_conj (ι6 (T (e i))) hZ) (areaTA_conj (ι6 (T (e j))) hW)
    (areaTA_of_eq (areaTA_conj (ι6 (T (e i))) hZ') (by group))
    (areaTA_of_eq (areaTA_conj (ι6 (T (e j))) hW') (by group))
  exact areaTA_mono (areaTA_of_eq h2 (by simp only [commG]; group)) (by omega)

/-! ### Theorem A(a) -/

theorem two_le_of_model {r : ℝ} (hr : 2 ≤ r) {m : ℕ} (hm : m ∈ modelSizes E r) : 2 ≤ m := by
  obtain ⟨hm0, f, -, hfe⟩ := hm
  by_contra hlt
  have hm1 : m = 1 := by omega
  subst hm1
  have hab : ρΓ' (a * b) ∈ E := by
    obtain ⟨h1, -, -⟩ := Eplus_sub
    simp only [List.forall_mem_cons] at h1
    exact h1.2.1.1
  have hne : ρΓ' (a * b) ≠ 1 := ρΓ'_ne_one rho_ab_ne_one
  have h := hfe _ hab 1 one_mem_E hne
  rw [Subsingleton.elim (f (ρΓ' (a * b))) (f 1), Houghton.ham_self] at h
  have : r⁻¹ ≤ 1 / 2 := by rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hr
  linarith

/-- **Theorem A(a)** (Theorem `thm:main-group`(a)), from the pair-area theorem (`hP`) and the
sector bound (`hS`): there is `c > 0` with `log₂ σ_E(r) ≥ c r / (log₂ r)^{2 + p_H}` for every `r ≥ 2`
(for every finite value `m` of the profile). -/
theorem theoremA_a (hP : PairAreaStatement) (hS : Houghton.PermSectorBound.{0}) :
    ∃ c > 0, ∀ r ≥ 2, ∀ m : ℕ, profile E r = m →
      c * r / (Real.logb 2 r) ^ (2 + pH) ≤ Real.logb 2 m := by
  obtain ⟨C, hC, hT⟩ := hP
  set κ : ℝ := 2 + pH with hκdef
  have hκ : 0 ≤ κ := by
    have : 0 ≤ Real.logb 2 107 := Real.logb_nonneg (by norm_num) (by norm_num)
    simp only [hκdef, pH]; linarith
  set l : ℝ := ((maxLen relP : ℕ) : ℝ) with hldef
  have hl : (1 : ℝ) ≤ 2 * l - 1 := by
    have : (maxLen relP : ℝ) = 24 := by rw [maxLen_relP]; norm_num
    rw [hldef, this]; norm_num
  set K₀ : ℝ := 10 ^ 8 * (C + 4) * (2 * l - 1) with hK₀
  have hK₀1 : 1 ≤ K₀ := by
    have : (1 : ℝ) ≤ 10 ^ 8 * (C + 4) := by nlinarith
    nlinarith
  have hK₀0 : 0 < K₀ := by linarith
  refine ⟨1 / (32 * K₀), by positivity, fun r hr m hm => ?_⟩
  have hr0 : 0 < r := by linarith
  have hmE := Houghton.mem_of_profile_eq hm
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast two_le_of_model hr hmE
  have hlogm : 1 ≤ Real.logb 2 m := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]; simpa using hm2
  set L := Real.logb 2 r with hLdef
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_logb_iff_rpow_le (by norm_num) hr0]; simpa using hr
  have hLκ : 1 ≤ L ^ κ := Real.one_le_rpow hL1 hκ
  set X := r / (L ^ κ * K₀) with hX
  have hXeq : 1 / (32 * K₀) * r / L ^ κ = X / 32 := by
    rw [hX]; field_simp
  rw [hXeq]
  rcases lt_or_ge X 2 with hX2 | hX2
  · linarith
  -- the criterion applies
  set n0 := ⌊X⌋₊ with hn0
  have hn02 : 2 ≤ n0 := Nat.le_floor (by simpa using hX2)
  set N := Nat.log 2 n0 with hN
  have hN1 : 1 ≤ N := Nat.log_pos (by norm_num) hn02
  have h2N : ((2 ^ N : ℕ) : ℝ) ≤ X := by
    have : 2 ^ N ≤ n0 := Nat.pow_log_le_self 2 (by omega)
    exact (Nat.cast_le.mpr this).trans (Nat.floor_le (by linarith))
  have hX2N : X < 2 * ((2 ^ N : ℕ) : ℝ) := by
    have h1 : n0 < 2 ^ (N + 1) := Nat.lt_pow_succ_log_self (by norm_num) n0
    have h2 : X < n0 + 1 := Nat.lt_floor_add_one X
    have h3 : (n0 : ℝ) + 1 ≤ ((2 ^ (N + 1) : ℕ) : ℝ) := by exact_mod_cast h1
    have h4 : ((2 ^ (N + 1) : ℕ) : ℝ) = 2 * ((2 ^ N : ℕ) : ℝ) := by push_cast; ring
    linarith
  have hXr : X ≤ r := by
    rw [hX, div_le_iff₀ (by positivity)]
    have : 1 ≤ L ^ κ * K₀ := by nlinarith
    nlinarith
  have hNL : (N : ℝ) ≤ L := by
    rw [hLdef, Real.le_logb_iff_rpow_le (by norm_num) hr0, Real.rpow_natCast]
    have : ((2 ^ N : ℕ) : ℝ) = (2 : ℝ) ^ N := by push_cast; rfl
    linarith
  have hNκ : (N : ℝ) ^ κ ≤ L ^ κ := Real.rpow_le_rpow (Nat.cast_nonneg _) hNL hκ
  have hNκ1 : (1 : ℝ) ≤ (N : ℝ) ^ κ := Real.one_le_rpow (by exact_mod_cast hN1) hκ
  obtain ⟨T, hTa⟩ := hT N hN1
  let e : Fin (2 ^ N) ≃ (Fin N → Bool) :=
    (Fintype.equivFinOfCardEq (by simp : Fintype.card (Fin N → Bool) = 2 ^ N)).symm
  set Λ := ⌊C * (N : ℝ) ^ (2 + pH)⌋₊ + 4 with hΛ
  have hw := transportAreaLE_lift T _ hTa e
  have hΛle : (Λ : ℝ) ≤ (C + 4) * (N : ℝ) ^ κ := by
    have : ((⌊C * (N : ℝ) ^ (2 + pH)⌋₊ : ℕ) : ℝ) ≤ C * (N : ℝ) ^ κ :=
      Nat.floor_le (by positivity)
    rw [hΛ]; push_cast; nlinarith
  have hr' : (10 : ℝ) ^ 8 * ((2 ^ N : ℕ) : ℝ) * (Λ : ℝ) * (2 * maxLen relP - 1) ≤ r := by
    rw [← hldef]
    have hpos : (0 : ℝ) ≤ ((2 ^ N : ℕ) : ℝ) := Nat.cast_nonneg _
    calc (10 : ℝ) ^ 8 * ((2 ^ N : ℕ) : ℝ) * (Λ : ℝ) * (2 * l - 1)
        ≤ (10 : ℝ) ^ 8 * ((2 ^ N : ℕ) : ℝ) * ((C + 4) * (N : ℝ) ^ κ) * (2 * l - 1) := by
          gcongr
      _ = ((2 ^ N : ℕ) : ℝ) * (N : ℝ) ^ κ * K₀ := by rw [hK₀]; ring
      _ ≤ X * L ^ κ * K₀ := by gcongr
      _ = r := by rw [hX]; field_simp
  have hcrit := (counting_criterion_of_subset hS πP relP 4 5 (Sum.inl 18) (Sum.inr 1) (Sum.inr 2)
    relP_a rfl rfl relP_one ab_ne_one (fun i => ι6 (T (e i))) Λ (by omega) hw r hr' E
    criterionChunk_sub_E).2 m hm
  linarith

end Lamps
