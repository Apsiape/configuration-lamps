import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.ENat.Lattice
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Basic.Finite.Prod
import Mathlib.GroupTheory.FreeGroup.Reduce
import FiniteLean.GroupTheory.Permutations.Hamming
import Mathlib.Data.Fin.VecNotation

namespace Lamps
open Finset Equiv
open Houghton (dH)
/-- The six normal forms `1, s, t, st, ts, sts` of `S₃ = ⟨s, t⟩` (the paper's `𝒩 = {1,a,b,ab,ba,aba}`). -/
def nfG {M : Type*} [Monoid M] (s t : M) : Fin 6 → M := ![1, s, t, s * t, t * s, s * t * s]

theorem map_nfG {M M' : Type*} [Monoid M] [Monoid M'] (f : M →* M') (s t : M) (h : Fin 6) :
    f (nfG s t h) = nfG (f s) (f t) h := by
  fin_cases h <;> simp [nfG]

/-- The ordered suffix `U_{>i} = U_{i+1} ⋯ U_{N}`. -/
def sufW {M : Type*} [Monoid M] {N : ℕ} (i : Fin N) (U : Fin N → M) : M :=
  (((List.finRange N).filter fun j => i < j).map U).prod

theorem map_sufW {M M' : Type*} [Monoid M] [Monoid M'] (f : M →* M') {N : ℕ} (i : Fin N)
    (U : Fin N → M) : f (sufW i U) = sufW i (fun j => f (U j)) := by
  simp only [sufW, map_list_prod, List.map_map]; rfl

section Perm

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem dH_nfG (s t s' t' : Perm Ω) (es et : ℝ) (hs : dH s s' ≤ es) (ht : dH t t' ≤ et)
    (h : Fin 6) : dH (nfG s t h) (nfG s' t' h) ≤ 2 * es + et := by
  have hs0 := (Houghton.dH_nonneg s s').trans hs
  have ht0 := (Houghton.dH_nonneg t t').trans ht
  have m1 := Houghton.dH_mul_le s t s' t'
  have m2 := Houghton.dH_mul_le t s t' s'
  have m3 := Houghton.dH_mul_le (s * t) s (s' * t') s'
  fin_cases h <;> simp [nfG, Houghton.dH_self] <;> linarith

theorem dH_list_prod {κ : Type*} (U V : κ → Perm Ω) (e : ℝ) (he : ∀ j, dH (U j) (V j) ≤ e) :
    ∀ L : List κ, dH ((L.map U).prod) ((L.map V).prod) ≤ L.length * e := by
  intro L
  induction L with
  | nil => simp [Houghton.dH_self]
  | cons j L ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, Nat.cast_succ]
    have := Houghton.dH_mul_le (U j) (L.map U).prod (V j) (L.map V).prod
    linarith [he j]

theorem dH_sufW {N : ℕ} (i : Fin N) (U V : Fin N → Perm Ω) (e : ℝ) (he0 : 0 ≤ e)
    (he : ∀ j, dH (U j) (V j) ≤ e) : dH (sufW i U) (sufW i V) ≤ N * e := by
  refine (dH_list_prod U V e he _).trans (mul_le_mul_of_nonneg_right ?_ he0)
  have := List.length_filter_le (fun j => decide (i < j)) (List.finRange N)
  rw [List.length_finRange] at this
  exact_mod_cast this

end Perm


end Lamps
