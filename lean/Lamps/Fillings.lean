import Lamps.HoughtonTools

/-!
# Local fillings (Douglas–Mghirbi v1.2.0, Section `sec:fillings`), syntactic parts

* `exchange_core`: the algebraic core of Lemma `lem:exchange`: if `N = W⁻¹ U Z⁻¹` has area `≤ δ`
  and `[f, Z]` has area `≤ m`, then `W f W⁻¹ · U f⁻¹ U⁻¹` has area `≤ 2δ + m`.
* `areaLE_comm_K1`, `areaLE_comm_K2`: `Area([f, Z]) ≤ |Z|` for words `Z` in the letters of `K₁`
  (`f = t`) or `K₂` (`f = d`), by the family **S**.
* `localFilling_c`: Lemma `lem:local-filling`(c): `Area([U d U⁻¹, x]) ≤ 2|U| + 1` for a word `U`
  in `p, q` and `x ∈ {a, b}` (`b = a c⁴`), by the families **Z**.
* `localFilling_d`: Lemma `lem:local-filling`(d): `Area([x, τ y τ⁻¹]) ≤ 4|U| + 1`, `τ = U t U⁻¹`,
  by the families **Z** and **P**.
Here `|U|` is the reduced length of `U ∈ FreeGroup (Fin 2)` and the word in `F` is `ιpq U`.
-/

namespace Lamps

theorem AreaEqGen.comm {u v u' v' : F} {n m : ℕ} (h₁ : AreaEqGen rel u u' n)
    (h₂ : AreaEqGen rel v v' m) :
    AreaEqGen rel (Lamps.comm u v) (Lamps.comm u' v') (2 * n + 2 * m) := by
  simp only [Lamps.comm]
  have := ((h₁.mul h₂).mul h₁.inv).mul h₂.inv
  exact this.mono (by omega)

/-- **Core of Lemma `lem:exchange`.** -/
theorem exchange_core (f W U Z : F) {δ m : ℕ} (hN : AreaLE (W⁻¹ * U * Z⁻¹) δ)
    (hZ : AreaLE (comm f Z) m) : AreaLE (W * f * W⁻¹ * (U * f⁻¹ * U⁻¹)) (2 * δ + m) := by
  have e : W * f * W⁻¹ * (U * f⁻¹ * U⁻¹) =
      W * ((f * (W⁻¹ * U * Z⁻¹) * f⁻¹) * comm f Z * (W⁻¹ * U * Z⁻¹)⁻¹) * W⁻¹ := by
    simp only [comm]; group
  rw [e]
  refine AreaLEGen.conj W ?_
  have h := ((hN.conj f).mul hZ).mul hN.inv
  exact h.mono (by omega)

/-! ### Commuting letters -/

/-- The letters `p, q` written as a word. -/
def pqLetter (x : Fin 2 × Bool) : F := if x.2 then ![p, q] x.1 else (![p, q] x.1)⁻¹

theorem ιpq_eq_prod (w : FreeGroup (Fin 2)) : ιpq w = (w.toWord.map pqLetter).prod := by
  conv_lhs => rw [← FreeGroup.mk_toWord (x := w)]
  rw [ιpq, FreeGroup.lift_mk]
  congr 1
  apply List.map_congr_left
  intro x _
  cases h : x.2 <;> simp [pqLetter, h]

/-- `b = a c⁴` and `[c³, b] = [c³, a]` freely. -/
theorem comm_d_b : comm d b = comm d a := by
  simp only [comm, d, b]; group

theorem areaLE_comm_pq (x : F) (hx : x = a ∨ x = b) (g : Fin 2 × Bool) :
    AreaLE (comm (pqLetter g) x) 1 := by
  have base : ∀ i : Fin 2, AreaLE (comm (![p, q] i) x) 1 := by
    intro i
    fin_cases i <;> rcases hx with rfl | rfl
    · exact AreaLEGen.rel 9
    · exact AreaLEGen.rel 10
    · exact AreaLEGen.rel 11
    · exact AreaLEGen.rel 12
  obtain ⟨i, e⟩ := g
  cases e
  · exact areaLE_comm_inv_left (base i)
  · exact base i

theorem areaLE_comm_ιpq (x : F) (hx : x = a ∨ x = b) (w : FreeGroup (Fin 2)) :
    AreaLE (comm (ιpq w) x) w.toWord.length := by
  rw [ιpq_eq_prod]
  have h := areaLE_comm_prod x (w.toWord.map pqLetter) (by
    intro g hg
    obtain ⟨y, -, rfl⟩ := List.mem_map.mp hg
    exact areaLE_comm_pq x hx y)
  simpa using h

theorem areaLE_comm_d (x : F) (hx : x = a ∨ x = b) : AreaLE (comm d x) 1 := by
  rcases hx with rfl | rfl
  · exact AreaLEGen.rel 13
  · rw [comm_d_b]; exact AreaLEGen.rel 13

/-- **Lemma `lem:local-filling`(c).** -/
theorem localFilling_c (U : FreeGroup (Fin 2)) (x : F) (hx : x = a ∨ x = b) :
    AreaLE (comm (ιpq U * d * (ιpq U)⁻¹) x) (2 * U.toWord.length + 1) := by
  have hU := areaLE_comm_ιpq x hx U
  have h3 : AreaLE ((ιpq U * d) * comm (ιpq U)⁻¹ x * (ιpq U * d)⁻¹ *
      ((ιpq U) * comm d x * (ιpq U)⁻¹ * comm (ιpq U) x)) (U.toWord.length + (1 + U.toWord.length)) :=
    ((areaLE_comm_inv_left hU).conj (ιpq U * d)).mul (((areaLE_comm_d x hx).conj (ιpq U)).mul hU)
  refine (h3.of_eq ?_).mono (by omega)
  simp only [comm]; group

/-- **Lemma `lem:local-filling`(d).** -/
theorem localFilling_d (U : FreeGroup (Fin 2)) (x y : F) (hx : x = a ∨ x = b)
    (hy : y = a ∨ y = b) :
    AreaLE (comm x ((ιpq U * t * (ιpq U)⁻¹) * y * (ιpq U * t * (ιpq U)⁻¹)⁻¹))
      (4 * U.toWord.length + 1) := by
  let V := ιpq U
  have hP : AreaLE (comm x (t * y * t⁻¹)) 1 := by
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact AreaLEGen.rel 21
    · exact AreaLEGen.rel 22
    · exact AreaLEGen.rel 23
    · exact AreaLEGen.rel 24
  -- replacing `V⁻¹ z V` by `z` costs `|U|`
  have hrep : ∀ z : F, (z = a ∨ z = b) → AreaEqGen rel (V⁻¹ * z * V) z U.toWord.length := by
    intro z hz
    unfold AreaEqGen
    have h : AreaLE (comm V⁻¹ z) U.toWord.length := areaLE_comm_inv_left (areaLE_comm_ιpq z hz U)
    exact h.of_eq (by simp only [comm]; group)
  have hE := AreaEqGen.comm (hrep x hx) ((hrep y hy).conj t)
  have h0 := AreaLEGen.of_areaEq hE hP
  have h1 : AreaLE (comm (V⁻¹ * x * V) (t * (V⁻¹ * y * V) * t⁻¹)) (4 * U.toWord.length + 1) :=
    h0.mono (by omega)
  have e : comm x ((V * t * V⁻¹) * y * (V * t * V⁻¹)⁻¹) =
      V * comm (V⁻¹ * x * V) (t * (V⁻¹ * y * V) * t⁻¹) * V⁻¹ := by
    simp only [comm]; group
  rw [e]
  exact h1.conj V

end Lamps

namespace Lamps

/-! ### Family **S**: `Area([f, Z]) ≤ |Z|` for words `Z` in the letters of `K₁` / `K₂` -/

/-- The word `Z = K_{i₁}^{±1} ⋯ K_{i_m}^{±1}` in the letters of a pair `K`. -/
def kWord (K : Fin 2 → F) (Z : List (Fin 2 × Bool)) : F :=
  (Z.map fun x => if x.2 then K x.1 else (K x.1)⁻¹).prod

theorem areaLE_comm_kWord (f : F) (K : Fin 2 → F) (hK : ∀ i, AreaLE (comm f (K i)) 1)
    (Z : List (Fin 2 × Bool)) : AreaLE (comm f (kWord K Z)) Z.length := by
  apply areaLE_comm_symm
  have h := areaLE_comm_prod f (Z.map fun x => if x.2 then K x.1 else (K x.1)⁻¹) (by
    intro g hg
    obtain ⟨⟨i, e⟩, -, rfl⟩ := List.mem_map.mp hg
    cases e
    · show AreaLE (comm (K i)⁻¹ f) 1
      exact areaLE_comm_inv_left (areaLE_comm_symm (hK i))
    · show AreaLE (comm (K i) f) 1
      exact areaLE_comm_symm (hK i))
  simpa [kWord] using h

/-- Family **S** for `t` and `K₁`. -/
theorem areaLE_comm_t_K1 (Z : List (Fin 2 × Bool)) : AreaLE (comm t (kWord K1 Z)) Z.length :=
  areaLE_comm_kWord t K1 (by intro i; fin_cases i; exacts [AreaLEGen.rel 5, AreaLEGen.rel 6]) Z

/-- Family **S** for `d` and `K₂`. -/
theorem areaLE_comm_d_K2 (Z : List (Fin 2 × Bool)) : AreaLE (comm d (kWord K2 Z)) Z.length :=
  areaLE_comm_kWord d K2 (by intro i; fin_cases i; exacts [AreaLEGen.rel 7, AreaLEGen.rel 8]) Z

end Lamps
