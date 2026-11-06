import Lamps.Group
import Houghton.DehnFinal

/-!
# Tools from Houghton's group for the configuration-lamps paper (Douglas–Mghirbi v1.2.0, Part I)

* Area algebra for `AreaLEGen` (any family of relators): monotonicity, products, conjugation,
  inversion, transport along homomorphisms of free groups (`AreaLEGen.map`), and the relative
  area `AreaEqGen`.
* The Tietze map `κ : Houghton.F → Lamps.F` (`a ↦ p`, `b ↦ q`, `α ↦ s = [p,q]`; defined in
  `Lamps.Group`) sends Johnson's relators `r₁, r₂, r₃, r₅` to the family **H** (`rel 0`–`rel 3`) and
  `r₄ = [a,b] α⁻¹` to `1`; hence `Houghton.AreaLE w k → AreaLE (κ w) k` (`areaLE_κ`).
* The Dehn bound of `P_H` (`app-houghton`, `eq:PH`, Proposition `prop:dehn`): `DehnLE m D` says that
  every word in `p, q` of reduced length `≤ m` representing `1` in `H` has area `≤ D` for `R`; by
  `Houghton.dehn_bound` (L2) and `lampsH_one_iff` (L1), `DehnLE m (400 m⁴ (1 + A))` whenever
  `AstarLE (4m+2) A` (`dehnLE_of_astar`), i.e. `δ_H(m) ≤ 400 m⁴ (1 + A*(4m+2))`.
-/

namespace Lamps

open Houghton (AstarLE ρH)

section AreaGen

variable {S ι : Type*} {R : ι → FreeGroup S}

theorem AreaLEGen.mono {w : FreeGroup S} {n m : ℕ} (h : AreaLEGen R w n) (hnm : n ≤ m) :
    AreaLEGen R w m := by
  obtain ⟨cs, hl, hp⟩ := h
  exact ⟨cs, hl.trans hnm, hp⟩

theorem AreaLEGen.one : AreaLEGen R 1 0 := ⟨[], le_rfl, by simp⟩

theorem AreaLEGen.of_eq_one {w : FreeGroup S} (e : w = 1) : AreaLEGen R w 0 := e ▸ AreaLEGen.one

/-- One cell `g r^{±1} g⁻¹`. -/
def cellG (R : ι → FreeGroup S) (x : FreeGroup S × ι × Bool) : FreeGroup S :=
  x.1 * (if x.2.2 then R x.2.1 else (R x.2.1)⁻¹) * x.1⁻¹

theorem areaLEGen_iff {w : FreeGroup S} {n : ℕ} :
    AreaLEGen R w n ↔ ∃ cs : List (FreeGroup S × ι × Bool), cs.length ≤ n ∧
      (cs.map (cellG R)).prod = w := Iff.rfl

theorem AreaLEGen.mul {u v : FreeGroup S} {n m : ℕ} (hu : AreaLEGen R u n)
    (hv : AreaLEGen R v m) : AreaLEGen R (u * v) (n + m) := by
  obtain ⟨cs, hl, hp⟩ := areaLEGen_iff.mp hu
  obtain ⟨ds, hl', hp'⟩ := areaLEGen_iff.mp hv
  refine areaLEGen_iff.mpr ⟨cs ++ ds, by rw [List.length_append]; omega, ?_⟩
  rw [List.map_append, List.prod_append, hp, hp']

theorem AreaLEGen.rel (i : ι) : AreaLEGen R (R i) 1 :=
  areaLEGen_iff.mpr ⟨[(1, i, true)], by simp, by simp [cellG]⟩

theorem prod_map_cellG_conj (g : FreeGroup S) (cs : List (FreeGroup S × ι × Bool)) :
    ((cs.map fun x => (g * x.1, x.2)).map (cellG R)).prod = g * (cs.map (cellG R)).prod * g⁻¹ := by
  induction cs with
  | nil => simp
  | cons x cs ih =>
    rw [List.map_cons, List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons]
    simp only [cellG]
    group

theorem AreaLEGen.conj {w : FreeGroup S} {n : ℕ} (g : FreeGroup S) (h : AreaLEGen R w n) :
    AreaLEGen R (g * w * g⁻¹) n := by
  obtain ⟨cs, hl, hp⟩ := areaLEGen_iff.mp h
  exact areaLEGen_iff.mpr ⟨cs.map fun x => (g * x.1, x.2), by simpa using hl,
    by rw [prod_map_cellG_conj, hp]⟩

theorem prod_map_cellG_inv (cs : List (FreeGroup S × ι × Bool)) :
    ((cs.map fun x => (x.1, x.2.1, !x.2.2)).reverse.map (cellG R)).prod =
      ((cs.map (cellG R)).prod)⁻¹ := by
  induction cs with
  | nil => simp
  | cons x cs ih =>
    rw [List.map_cons, List.reverse_cons, List.map_append, List.prod_append, ih,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, List.map_cons,
      List.prod_cons, mul_inv_rev]
    congr 1
    obtain ⟨g, i, e⟩ := x
    cases e <;> simp [cellG, mul_assoc]

theorem AreaLEGen.inv {w : FreeGroup S} {n : ℕ} (h : AreaLEGen R w n) :
    AreaLEGen R w⁻¹ n := by
  obtain ⟨cs, hl, hp⟩ := areaLEGen_iff.mp h
  exact areaLEGen_iff.mpr ⟨(cs.map fun x => (x.1, x.2.1, !x.2.2)).reverse, by simpa using hl,
    by rw [prod_map_cellG_inv, hp]⟩

theorem AreaLEGen.of_eq {w w' : FreeGroup S} {n : ℕ} (h : AreaLEGen R w n) (e : w = w') :
    AreaLEGen R w' n := e ▸ h

/-- Transport of area along a homomorphism sending each relator to a relator, an inverse
relator, or `1`. -/
theorem AreaLEGen.map {S' ι' : Type*} {R' : ι' → FreeGroup S'} (f : FreeGroup S →* FreeGroup S')
    (hf : ∀ i, AreaLEGen R' (f (R i)) 1) {w : FreeGroup S} {n : ℕ} (h : AreaLEGen R w n) :
    AreaLEGen R' (f w) n := by
  obtain ⟨cs, hl, hp⟩ := areaLEGen_iff.mp h
  subst hp
  have key : ∀ cs : List (FreeGroup S × ι × Bool),
      AreaLEGen R' (f (cs.map (cellG R)).prod) cs.length := by
    intro cs
    induction cs with
    | nil => exact AreaLEGen.of_eq_one (by simp)
    | cons x cs ih =>
      rw [List.map_cons, List.prod_cons, map_mul, List.length_cons, add_comm]
      refine AreaLEGen.mul ?_ ih
      simp only [cellG, map_mul, map_inv]
      apply AreaLEGen.conj
      split_ifs
      · exact hf _
      · rw [map_inv]; exact (hf _).inv
  exact (key cs).mono hl

/-- Relative area: `AreaEqGen R u v n` iff `Area_R(u v⁻¹) ≤ n` (replacing `v` by `u` costs `n`). -/
def AreaEqGen (R : ι → FreeGroup S) (u v : FreeGroup S) (n : ℕ) : Prop := AreaLEGen R (u * v⁻¹) n

theorem AreaEqGen.refl (u : FreeGroup S) : AreaEqGen R u u 0 :=
  AreaLEGen.of_eq_one (mul_inv_cancel u)

theorem AreaEqGen.symm {u v : FreeGroup S} {n : ℕ} (h : AreaEqGen R u v n) :
    AreaEqGen R v u n := by
  unfold AreaEqGen at *
  simpa using h.inv

theorem AreaEqGen.trans {u v w : FreeGroup S} {n m : ℕ} (h₁ : AreaEqGen R u v n)
    (h₂ : AreaEqGen R v w m) : AreaEqGen R u w (n + m) := by
  unfold AreaEqGen at *
  exact (h₁.mul h₂).of_eq (by group)

theorem AreaEqGen.mul {u v u' v' : FreeGroup S} {n m : ℕ} (h₁ : AreaEqGen R u v n)
    (h₂ : AreaEqGen R u' v' m) : AreaEqGen R (u * u') (v * v') (n + m) := by
  unfold AreaEqGen at *
  exact (h₁.mul (h₂.conj v)).of_eq (by group)

theorem AreaEqGen.inv {u v : FreeGroup S} {n : ℕ} (h : AreaEqGen R u v n) :
    AreaEqGen R u⁻¹ v⁻¹ n := by
  unfold AreaEqGen at *
  exact (h.inv.conj v⁻¹).of_eq (by group)

theorem AreaEqGen.conj {u v : FreeGroup S} {n : ℕ} (g : FreeGroup S) (h : AreaEqGen R u v n) :
    AreaEqGen R (g * u * g⁻¹) (g * v * g⁻¹) n := by
  unfold AreaEqGen at *
  exact (h.conj g).of_eq (by group)

theorem AreaEqGen.mono {u v : FreeGroup S} {n m : ℕ} (h : AreaEqGen R u v n) (hnm : n ≤ m) :
    AreaEqGen R u v m := AreaLEGen.mono h hnm

theorem AreaLEGen.of_areaEq {u v : FreeGroup S} {n m : ℕ} (h : AreaEqGen R u v n)
    (hv : AreaLEGen R v m) : AreaLEGen R u (n + m) :=
  (AreaLEGen.mul h hv).of_eq (by group)

end AreaGen

/-! ### Commutators with products -/

theorem comm_mul_left (g h x : F) : comm (g * h) x = g * comm h x * g⁻¹ * comm g x := by
  simp only [comm]; group

theorem comm_inv_left (g x : F) : comm g⁻¹ x = g⁻¹ * (comm g x)⁻¹ * g := by
  simp only [comm]; group

/-- `Area([L.prod, x]) ≤ ∑ Area([g, x])` over the letters `g` of `L`, each of area `≤ 1`. -/
theorem areaLE_comm_prod (x : F) (L : List F) (hL : ∀ g ∈ L, AreaLE (comm g x) 1) :
    AreaLE (comm L.prod x) L.length := by
  induction L with
  | nil => exact AreaLEGen.of_eq_one (by simp [comm])
  | cons g L ih =>
    rw [List.prod_cons, comm_mul_left, List.length_cons]
    have h1 := (ih fun g' hg' => hL g' (List.mem_cons_of_mem _ hg')).conj g
    exact (h1.mul (hL g (List.mem_cons_self))).mono (by omega)

theorem areaLE_comm_inv_left {g x : F} {n : ℕ} (h : AreaLE (comm g x) n) :
    AreaLE (comm g⁻¹ x) n := by
  rw [comm_inv_left]
  simpa using h.inv.conj g⁻¹

theorem areaLE_comm_symm {g x : F} {n : ℕ} (h : AreaLE (comm g x) n) : AreaLE (comm x g) n := by
  have e : comm x g = (comm g x)⁻¹ := by simp only [comm]; group
  rw [e]; exact h.inv

/-! ### The Tietze map -/

theorem κ_rel0 : κ Houghton.r₁ = rel 0 := by
  simp [Houghton.r₁, rel, κ_α]
theorem κ_rel1 : κ Houghton.r₂ = rel 1 := by
  simp [Houghton.r₂, rel, κ_α, κ_a]
theorem κ_rel2 : κ Houghton.r₃ = rel 2 := by
  simp [Houghton.r₃, Houghton.comm, rel, comm, κ_α, κ_a]
theorem κ_rel3 : κ Houghton.r₄ = 1 := by
  simp [Houghton.r₄, κ_α, κ_a, κ_b, s, comm]
theorem κ_rel4 : κ Houghton.r₅ = rel 3 := by
  simp [Houghton.r₅, rel, κ_α, κ_a, κ_b, mul_assoc]

/-- Every relator of Johnson's presentation goes to a relator of the family **H** or to `1`. -/
theorem κ_relLE (i : Fin 5) : AreaLE (κ (Houghton.rel i)) 1 := by
  fin_cases i
  · exact (AreaLEGen.rel 0).of_eq κ_rel0.symm
  · exact (AreaLEGen.rel 1).of_eq κ_rel1.symm
  · exact (AreaLEGen.rel 2).of_eq κ_rel2.symm
  · exact (AreaLEGen.of_eq_one κ_rel3).mono (Nat.zero_le 1)
  · exact (AreaLEGen.rel 3).of_eq κ_rel4.symm

/-- **Tietze transfer.** Areas for Johnson's presentation `P_J` bound areas for `R`. -/
theorem areaLE_κ {w : Houghton.F} {k : ℕ} (h : Houghton.AreaLE w k) : AreaLE (κ w) k :=
  AreaLEGen.map (R := Houghton.rel) κ κ_relLE h

/-! ### The Dehn function of `P_H` -/

/-- `δ_H(m) ≤ D` (for the family **H** of `R`): every word in `p, q` of reduced length at most `m`
representing `1` in `H` has area at most `D`. -/
def DehnLE (m D : ℕ) : Prop :=
  ∀ w : FreeGroup (Fin 2), w.toWord.length ≤ m → ρH (ιab w) = 1 → AreaLE (ιpq w) D

theorem DehnLE.mono {m m' D D' : ℕ} (h : DehnLE m D) (hm : m' ≤ m) (hD : D ≤ D') :
    DehnLE m' D' := fun w hw h1 => (h w (hw.trans hm) h1).mono hD

theorem ιab_eq_map : ιab = FreeGroup.map (fun i : Fin 2 => (Fin.castSucc i : Fin 3)) := by
  apply FreeGroup.ext_hom
  intro i
  fin_cases i <;> rfl

theorem length_toWord_ιab (w : FreeGroup (Fin 2)) :
    (ιab w).toWord.length ≤ w.toWord.length := by
  have h : ιab w = FreeGroup.mk (w.toWord.map fun x => ((Fin.castSucc x.1 : Fin 3), x.2)) := by
    conv_lhs => rw [← FreeGroup.mk_toWord (x := w)]
    rw [ιab_eq_map, FreeGroup.map.mk]
  rw [h]
  have h3 := FreeGroup.norm_mk_le (L₁ := w.toWord.map fun x => ((Fin.castSucc x.1 : Fin 3), x.2))
  rw [List.length_map] at h3
  exact h3

/-- **`δ_H(m) ≤ 400 m⁴ (1 + A*(4m+2))`**, from `Houghton.dehn_bound` (L2) and the Tietze map. -/
theorem dehnLE_of_astar {m A : ℕ} (hm : 1 ≤ m) (hA : AstarLE (4 * m + 2) A) :
    DehnLE m (400 * m ^ 4 * (1 + A)) := by
  intro w hw h1
  have h := Houghton.dehn_bound m hm (ιab w) ((length_toWord_ιab w).trans hw) h1 A hA
  have h2 := areaLE_κ h
  rwa [← MonoidHom.comp_apply, κ_ιab] at h2

/-- The same, for words in `p, q` representing `1` in `Γ` (via `lampsH_one_iff`). -/
theorem dehnLE_of_astar_Γ {m A : ℕ} (hm : 1 ≤ m) (hA : AstarLE (4 * m + 2) A)
    (w : FreeGroup (Fin 2)) (hw : w.toWord.length ≤ m) (h1 : ρΓ (ιpq w) = 1) :
    AreaLE (ιpq w) (400 * m ^ 4 * (1 + A)) :=
  dehnLE_of_astar hm hA w hw ((lampsH_one_iff w).mp h1)

end Lamps
