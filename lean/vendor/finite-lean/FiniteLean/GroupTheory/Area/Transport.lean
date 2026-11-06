import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Base
import FiniteLean.GroupTheory.Area.Basic
import FiniteLean.GroupTheory.Permutations.Hamming

namespace Lamps
open Finset Equiv
open Houghton (dH)
section Transport

variable {S ι : Type*} {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- One cell `g r^{±1} g⁻¹` of `AreaLEGen`. -/
def cellW (R : ι → FreeGroup S) (x : FreeGroup S × ι × Bool) : FreeGroup S :=
  x.1 * (if x.2.2 then R x.2.1 else (R x.2.1)⁻¹) * x.1⁻¹

/-- **Transport in measure**: if every relator has defect `≤ δ`, a word of area `≤ n` has defect
`≤ n δ`. -/
theorem dH_le_of_areaLEGen (R : ι → FreeGroup S) (φ : FreeGroup S →* Perm Ω) (δ : ℝ)
    (hrel : ∀ k, dH (φ (R k)) 1 ≤ δ) (hδ : 0 ≤ δ) {w : FreeGroup S} {n : ℕ}
    (h : AreaLEGen R w n) : dH (φ w) 1 ≤ n * δ := by
  obtain ⟨cs, hlen, rfl⟩ := h
  have hcell : ∀ x, dH (φ (cellW R x)) 1 ≤ δ := by
    rintro ⟨z, k, e⟩
    simp only [cellW, map_mul, map_inv, Houghton.dH_conj]
    cases e
    · simp only [Bool.false_eq_true, ite_false, map_inv, Houghton.dH_inv_one]; exact hrel k
    · simp only [ite_true]; exact hrel k
  have key : ∀ cs : List (FreeGroup S × ι × Bool),
      dH (φ (cs.map (cellW R)).prod) 1 ≤ cs.length * δ := by
    intro cs
    induction cs with
    | nil => simp [Houghton.dH_self]
    | cons c cs ih =>
      rw [List.map_cons, List.prod_cons, map_mul, List.length_cons]
      calc dH (φ (cellW R c) * φ (cs.map (cellW R)).prod) 1
          ≤ dH (φ (cellW R c) * φ (cs.map (cellW R)).prod) (φ (cellW R c)) +
              dH (φ (cellW R c)) 1 := Houghton.dH_triangle _ _ _
        _ = dH (φ (cs.map (cellW R)).prod) 1 + dH (φ (cellW R c)) 1 := by
            rw [Houghton.dH_mul_self_left]
        _ ≤ cs.length * δ + δ := add_le_add ih (hcell c)
        _ = ((cs.length + 1 : ℕ) : ℝ) * δ := by rw [Nat.cast_succ, add_mul, one_mul]
  calc dH (φ (cs.map (cellW R)).prod) 1 ≤ cs.length * δ := key cs
    _ ≤ n * δ := mul_le_mul_of_nonneg_right (by exact_mod_cast hlen) hδ

end Transport


end Lamps
