import Lamps.PairSpec
import Lamps.LocalFillings

/-!
# The local identities (Lemma `lem:local-filling`): an instance of `LocalIdsFamily`

With `n = max 3 N` and `u_i = i + 1`, the transporters are arrangement words (Lemma
`lem:arrangement`): `τ_i = U_i t U_i⁻¹` with `U_i(1) = u_i`, and `X_{ij} = U_{ij} d U_{ij}⁻¹` with
`U_{ij}(1, 2) = (u_j, u_i)`. Each local identity is moved, by Lemma `lem:exchange`
(`exchange_sem`), to a conjugate of one relator of the families `Q`, `C`, `A`; the remaining two
are the local fillings (a), (b) of `Lamps/Fillings.lean`. We prove `LocalIdsFamily 2000 700`.
-/

namespace Lamps

open Houghton (Y ρH)

/-- The transpositions of an arrangement word for `xs` (Lemma `lem:arrangement`). -/
noncomputable def arrTs (n : ℕ) (xs : List ℕ) : List (ℕ × ℕ) :=
  if h : xs.Nodup ∧ ∀ x ∈ xs, 1 ≤ x ∧ x ≤ n then Classical.choose (arrangement_word n xs h.1 h.2)
  else []

/-- Conjugation by the image of a word in `p, q`. -/
def cj (w : FreeGroup (Fin 2)) (f : F) : F := ιpq w * f * (ιpq w)⁻¹

/-- An arrangement word on at most three points of `{1, …, n}`. -/
structure Arr (n : ℕ) (ts : List (ℕ × ℕ)) : Prop where
  len : ts.length ≤ 3
  pts : ∀ x ∈ ts, 1 ≤ x.1 ∧ x.1 < x.2 ∧ x.2 ≤ n
  ev : ev2 (twprod ts) = tprod ts
  norm : (twprod ts).norm ≤ 30 * n

theorem arr_of (n : ℕ) (xs : List ℕ) (hnd : xs.Nodup) (hxs : ∀ x ∈ xs, 1 ≤ x ∧ x ≤ n)
    (h3 : xs.length ≤ 3) :
    Arr n (arrTs n xs) ∧ ∀ m (hm : m < xs.length), tprod (arrTs n xs) (pt (m + 1)) = pt xs[m] := by
  have h : xs.Nodup ∧ ∀ x ∈ xs, 1 ≤ x ∧ x ≤ n := ⟨hnd, hxs⟩
  have e : arrTs n xs = Classical.choose (arrangement_word n xs h.1 h.2) := dif_pos h
  obtain ⟨h1, h2, h3', h4, h5⟩ := Classical.choose_spec (arrangement_word n xs h.1 h.2)
  rw [e]
  refine ⟨⟨by omega, h2, h4, ?_⟩, h3'⟩
  have : 10 * xs.length * n ≤ 30 * n := Nat.mul_le_mul_right n (by omega)
  omega

theorem pts_ok {N n : ℕ} (hNn : N ≤ n) (l : List (Fin N)) :
    ∀ x ∈ l.map (fun i => i.val + 1), 1 ≤ x ∧ x ≤ n := by
  intro x hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
  have := i.isLt
  omega

theorem nodup_ok {N : ℕ} (l : List (Fin N)) (h : l.Nodup) :
    (l.map (fun i => i.val + 1)).Nodup :=
  h.map (fun i j e => Fin.ext (by have e' : i.val + 1 = j.val + 1 := e; omega))

theorem arr1 {N n : ℕ} (hNn : N ≤ n) (i : Fin N) :
    Arr n (arrTs n [i.val + 1]) ∧ tprod (arrTs n [i.val + 1]) (pt 1) = pt (i.val + 1) := by
  obtain ⟨h1, h2⟩ := arr_of n [i.val + 1] (by simp) (pts_ok hNn [i]) (by simp)
  exact ⟨h1, h2 0 (by simp)⟩

theorem arr2 {N n : ℕ} (hNn : N ≤ n) (i j : Fin N) (hij : i ≠ j) :
    Arr n (arrTs n [i.val + 1, j.val + 1]) ∧
      tprod (arrTs n [i.val + 1, j.val + 1]) (pt 1) = pt (i.val + 1) ∧
      tprod (arrTs n [i.val + 1, j.val + 1]) (pt 2) = pt (j.val + 1) := by
  obtain ⟨h1, h2⟩ := arr_of n [i.val + 1, j.val + 1] (nodup_ok [i, j] (by simp [hij]))
    (pts_ok hNn [i, j]) (by simp)
  exact ⟨h1, h2 0 (by simp), h2 1 (by simp)⟩

theorem arr3 {N n : ℕ} (hNn : N ≤ n) (i j k : Fin N) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Arr n (arrTs n [i.val + 1, j.val + 1, k.val + 1]) ∧
      tprod (arrTs n [i.val + 1, j.val + 1, k.val + 1]) (pt 1) = pt (i.val + 1) ∧
      tprod (arrTs n [i.val + 1, j.val + 1, k.val + 1]) (pt 2) = pt (j.val + 1) ∧
      tprod (arrTs n [i.val + 1, j.val + 1, k.val + 1]) (pt 3) = pt (k.val + 1) := by
  obtain ⟨h1, h2⟩ := arr_of n [i.val + 1, j.val + 1, k.val + 1]
    (nodup_ok [i, j, k] (by simp [hij, hik, hjk])) (pts_ok hNn [i, j, k]) (by simp)
  exact ⟨h1, h2 0 (by simp), h2 1 (by simp), h2 2 (by simp)⟩

/-- Lemma `lem:exchange` for arrangement words, with a shift `P^j` (`j ≤ 2`). -/
theorem exch (f : F) (K : Fin 2 → F) (k c n j : ℕ)
    (hfK : ∀ w, ιpq (fK k w) = FreeGroup.lift K w) (hS : ∀ i, AreaLE (comm f (K i)) 1)
    (hc : ∀ i : Fin 2, (![ζ k * P, ζ k * Q] i).norm ≤ c) (hc' : c ≤ 11)
    (Z0 : FreeGroup (Fin 2)) (hZ0 : Z0.norm ≤ 2) (B : Finset Y) (hB : B.card ≤ 3)
    (hBpts : ∀ y ∈ B, ∃ u, 1 ≤ u ∧ u ≤ n ∧ y = pt u)
    (hZ0supp : ∀ y, y ∉ B → (ev2 (fK k Z0) * (ev2 (P ^ j))⁻¹) y = y)
    (hZ0fix : ∀ u, 1 ≤ u → u ≤ k → ev2 (fK k Z0) (pt u) = pt u) (hj : j ≤ 2) (hn : 3 ≤ n)
    (tsW tsU : List (ℕ × ℕ)) (hW : Arr n tsW) (hU : Arr n tsU)
    (hag : ∀ u, 1 ≤ u → u ≤ k → tprod tsU (pt u) = tprod tsW (pt (u + j)))
    {D : ℕ} (hD : DehnLE (2000 * n) D) :
    AreaEqGen rel (cj (twprod tsU) f) (cj (twprod tsW * P ^ j) f) (2 * D + 2 + 150 * n) := by
  have hApts : ∀ y ∈ ends tsW ∪ ends tsU, ∃ u, 1 ≤ u ∧ u ≤ n ∧ y = pt u := by
    intro y hy
    simp only [ends, Finset.mem_union, List.mem_toFinset, List.mem_map] at hy
    rcases hy with ((⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩) | (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩))
    · have := hW.pts t ht; exact ⟨t.1, by omega, by omega, rfl⟩
    · have := hW.pts t ht; exact ⟨t.2, by omega, by omega, rfl⟩
    · have := hU.pts t ht; exact ⟨t.1, by omega, by omega, rfl⟩
    · have := hU.pts t ht; exact ⟨t.2, by omega, by omega, rfl⟩
  have hcard : (ends tsW ∪ ends tsU ∪ B).card ≤ 15 := by
    have h1 := Finset.card_union_le (ends tsW ∪ ends tsU) B
    have h2 := Finset.card_union_le (ends tsW) (ends tsU)
    have h3 := card_ends_le tsW
    have h4 := card_ends_le tsU
    have h5 := hW.len
    have h6 := hU.len
    omega
  have hZB : Z0.norm + 10 * (ends tsW ∪ ends tsU ∪ B).card * n ≤ 2 + 150 * n := by
    have := Nat.mul_le_mul_right n (Nat.mul_le_mul_left 10 hcard)
    omega
  have hcZ : c * (Z0.norm + 10 * (ends tsW ∪ ends tsU ∪ B).card * n) ≤ 11 * (2 + 150 * n) :=
    Nat.mul_le_mul hc' hZB
  have hlen : (twprod tsW).norm + j + (twprod tsU).norm +
      c * (Z0.norm + 10 * (ends tsW ∪ ends tsU ∪ B).card * n) ≤ 2000 * n := by
    have := hW.norm
    have := hU.norm
    omega
  have hmain := exchange_sem f K k c n j hfK hS hc Z0 B hBpts hZ0supp hZ0fix (twprod tsW)
    (twprod tsU) (ends tsW ∪ ends tsU) hApts
    (fun y hy => by
      rw [Finset.mem_union, not_or] at hy
      rw [hW.ev]; exact tprod_apply_of_not_mem tsW y hy.1)
    (fun y hy => by
      rw [Finset.mem_union, not_or] at hy
      rw [hU.ev]; exact tprod_apply_of_not_mem tsU y hy.2)
    (fun u h1 h2 => by
      rw [map_mul, Equiv.Perm.mul_apply, map_pow, ev2_P, pY_pow_pt j u h1, hW.ev, hU.ev]
      exact hag u h1 h2) (hD.mono hlen le_rfl)
  unfold AreaEqGen
  refine (hmain.inv.mono (by omega)).of_eq ?_
  simp only [cj]
  generalize ιpq (twprod tsW * P ^ j) = V
  generalize ιpq (twprod tsU) = U
  group

theorem hK1 : ∀ i, AreaLE (comm t (K1 i)) 1 := by
  intro i; fin_cases i; exacts [AreaLEGen.rel 5, AreaLEGen.rel 6]

theorem hK2 : ∀ i, AreaLE (comm d (K2 i)) 1 := by
  intro i; fin_cases i; exacts [AreaLEGen.rel 7, AreaLEGen.rel 8]

theorem norm_of0_sq : (FreeGroup.of (0 : Fin 2) ^ 2).norm ≤ 2 := by
  have := FreeGroup.norm_mul_le (FreeGroup.of (0 : Fin 2)) (FreeGroup.of 0)
  rw [FreeGroup.norm_of] at this
  rw [sq]; omega

section Exch
variable {n D : ℕ} (hn : 3 ≤ n) (hD : DehnLE (2000 * n) D) (tsW tsU : List (ℕ × ℕ))
  (hW : Arr n tsW) (hU : Arr n tsU)
include hn hD hW hU

theorem exT0 (hag : tprod tsU (pt 1) = tprod tsW (pt 1)) :
    AreaEqGen rel (cj (twprod tsU) t) (cj (twprod tsW) t) (2 * D + 2 + 150 * n) := by
  have h := exch t K1 1 5 n 0 fK_one hK1 hc1 (by norm_num) 1 (by simp [FreeGroup.norm]) ∅
    (by simp) (by simp) (fun y _ => by simp) (fun u _ _ => by simp) (by norm_num) hn
    tsW tsU hW hU (fun u h1 h2 => by obtain rfl : u = 1 := (by omega); exact hag) hD
  rwa [pow_zero, mul_one] at h

theorem exT1 (hag : tprod tsU (pt 1) = tprod tsW (pt 2)) :
    AreaEqGen rel (cj (twprod tsU) t) (cj (twprod tsW * P ^ 1) t) (2 * D + 2 + 150 * n) :=
  exch t K1 1 5 n 1 fK_one hK1 hc1 (by norm_num) (FreeGroup.of 0)
    ((FreeGroup.norm_of _).trans_le (by norm_num)) {pt 1, pt 2}
    (Finset.card_le_two.trans (by norm_num))
    (by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      exacts [⟨1, le_rfl, by omega, rfl⟩, ⟨2, by omega, by omega, rfl⟩])
    shift1_supp shift1_fix (by norm_num) hn tsW tsU hW hU
    (fun u h1 h2 => by obtain rfl : u = 1 := (by omega); exact hag) hD

theorem exT2 (hag : tprod tsU (pt 1) = tprod tsW (pt 3)) :
    AreaEqGen rel (cj (twprod tsU) t) (cj (twprod tsW * P ^ 2) t) (2 * D + 2 + 150 * n) :=
  exch t K1 1 5 n 2 fK_one hK1 hc1 (by norm_num) (FreeGroup.of 0 ^ 2) norm_of0_sq
    {pt 1, pt 2, pt 3} Finset.card_le_three
    (by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl
      exacts [⟨1, le_rfl, by omega, rfl⟩, ⟨2, by omega, by omega, rfl⟩,
        ⟨3, by omega, hn, rfl⟩])
    shift2_supp shift2_fix (by norm_num) hn tsW tsU hW hU
    (fun u h1 h2 => by obtain rfl : u = 1 := (by omega); exact hag) hD

theorem exD0 (hag1 : tprod tsU (pt 1) = tprod tsW (pt 1))
    (hag2 : tprod tsU (pt 2) = tprod tsW (pt 2)) :
    AreaEqGen rel (cj (twprod tsU) d) (cj (twprod tsW) d) (2 * D + 2 + 150 * n) := by
  have h := exch d K2 2 11 n 0 fK_two hK2 hc2 le_rfl 1 (by simp [FreeGroup.norm]) ∅
    (by simp) (by simp) (fun y _ => by simp) (fun u _ _ => by simp) (by norm_num) hn
    tsW tsU hW hU (fun u h1 h2 => by
      rcases (by omega : u = 1 ∨ u = 2) with rfl | rfl
      exacts [hag1, hag2]) hD
  rwa [pow_zero, mul_one] at h

end Exch

theorem ιpq_P : ιpq P = p := by simp [ιpq, P, p]

/-- `τ_i = U_i t U_i⁻¹` with `U_i(1) = i + 1`. -/
noncomputable def τc (N n : ℕ) (i : Fin N) : F := cj (twprod (arrTs n [i.val + 1])) t

/-- `X_{ij} = U_{ij} d U_{ij}⁻¹` with `U_{ij}(1, 2) = (j + 1, i + 1)`. -/
noncomputable def Xc (N n : ℕ) (i j : Fin N) : F :=
  cj (twprod (arrTs n [j.val + 1, i.val + 1])) d

theorem localIds_main (N n D : ℕ) (hn : 3 ≤ n) (hNn : N ≤ n) (hD : DehnLE (2000 * n) D) :
    PairArea.LocalIds (τc N n) (Xc N n) (10 * D + 700 * n) where
  sq i := by
    have h4 : AreaLE (t ^ 2) 1 := AreaLEGen.rel 4
    refine ((h4.conj (ιpq (twprod (arrTs n [i.val + 1])))).of_eq ?_).mono (by omega)
    simp only [τc, cj, pow_two]
    group
  swap i j hij := by
    obtain ⟨hW, hW1, hW2⟩ := arr2 hNn i j hij
    obtain ⟨hUi, hUi1⟩ := arr1 hNn i
    obtain ⟨hUj, hUj1⟩ := arr1 hNn j
    have e1 := exT0 hn hD _ _ hW hUi (hUi1.trans hW1.symm)
    have e2 := exT1 hn hD _ _ hW hUj (hUj1.trans hW2.symm)
    have h14 : AreaLE (comm (tm 1) (tm 2)) 1 := AreaLEGen.rel 14
    refine (AreaLEGen.of_areaEq (AreaEqGen.comm e1 e2)
      ((h14.conj (ιpq (twprod (arrTs n [i.val + 1, j.val + 1])))).of_eq ?_)).mono ?_
    · simp only [cj, Lamps.comm, tm, map_mul, ιpq_P, Nat.sub_self, pow_zero, pow_one]
      generalize ιpq (twprod (arrTs n [i.val + 1, j.val + 1])) = V
      group
    · omega
  conj_ne i j k hij hkj := by
    obtain ⟨hW, hW1, hW2⟩ := arr2 hNn j i hij.symm
    by_cases hki : k = i
    · subst hki
      obtain ⟨hUk, hUk1⟩ := arr1 hNn k
      have e := exT1 hn hD _ _ hW hUk (hUk1.trans hW2.symm)
      have h16 : AreaLE (comm d (tm 2)) 1 := AreaLEGen.rel 16
      refine (AreaLEGen.of_areaEq ((((AreaEqGen.refl (R := rel) (Xc N n k j)).mul e).mul
        (AreaEqGen.refl (R := rel) (Xc N n k j)⁻¹)).mul e.inv)
        ((h16.conj (ιpq (twprod (arrTs n [j.val + 1, k.val + 1])))).of_eq ?_)).mono ?_
      · simp only [Xc, cj, Lamps.comm, tm, map_mul, ιpq_P, pow_one]
        generalize ιpq (twprod (arrTs n [j.val + 1, k.val + 1])) = V
        group
      · omega
    · obtain ⟨hW', hW'1, hW'2, hW'3⟩ := arr3 hNn j i k hij.symm (Ne.symm hkj) (Ne.symm hki)
      obtain ⟨hUk, hUk1⟩ := arr1 hNn k
      have eX := exD0 hn hD _ _ hW' hW (hW1.trans hW'1.symm) (hW2.trans hW'2.symm)
      have ek := exT2 hn hD _ _ hW' hUk (hUk1.trans hW'3.symm)
      have h17 : AreaLE (comm d (tm 3)) 1 := AreaLEGen.rel 17
      refine (AreaLEGen.of_areaEq (((eX.mul ek).mul eX.inv).mul ek.inv)
        ((h17.conj (ιpq (twprod (arrTs n [j.val + 1, i.val + 1, k.val + 1])))).of_eq ?_)).mono ?_
      · simp only [cj, Lamps.comm, tm, map_mul, map_pow, ιpq_P]
        generalize ιpq (twprod (arrTs n [j.val + 1, i.val + 1, k.val + 1])) = V
        group
      · omega
  conj_eq i j hij := by
    obtain ⟨hW, hW1, hW2⟩ := arr2 hNn j i hij.symm
    obtain ⟨hUi, hUi1⟩ := arr1 hNn i
    obtain ⟨hUj, hUj1⟩ := arr1 hNn j
    have ej := exT0 hn hD _ _ hW hUj (hUj1.trans hW1.symm)
    have ei := exT1 hn hD _ _ hW hUi (hUi1.trans hW2.symm)
    have h15 : AreaLE (d * tm 1 * d⁻¹ * (tm 1 * tm 2)⁻¹) 1 := AreaLEGen.rel 15
    refine (AreaLEGen.of_areaEq (((((AreaEqGen.refl (R := rel) (Xc N n i j)).mul ej).mul
      (AreaEqGen.refl (R := rel) (Xc N n i j)⁻¹)).mul ei.inv).mul ej.inv)
      ((h15.conj (ιpq (twprod (arrTs n [j.val + 1, i.val + 1])))).of_eq ?_)).mono ?_
    · simp only [Xc, cj, tm, map_mul, ιpq_P, Nat.sub_self, pow_zero, pow_one]
      generalize ιpq (twprod (arrTs n [j.val + 1, i.val + 1])) = V
      group
    · omega
  commX i j hij x hx := by
    have hx' : x = a ∨ x = b := by simpa using hx
    have h := localFilling_c (twprod (arrTs n [j.val + 1, i.val + 1])) x hx'
    have hl : (twprod (arrTs n [j.val + 1, i.val + 1])).toWord.length ≤ 30 * n :=
      (arr2 hNn j i hij.symm).1.norm
    exact h.mono (by omega)
  locD i x hx y hy := by
    have hx' : x = a ∨ x = b := by simpa using hx
    have hy' : y = a ∨ y = b := by simpa using hy
    have h := localFilling_d (twprod (arrTs n [i.val + 1])) x y hx' hy'
    have hl : (twprod (arrTs n [i.val + 1])).toWord.length ≤ 30 * n := (arr1 hNn i).1.norm
    exact h.mono (by omega)

/-- **The local identities** (Lemma `lem:local-filling`): `LocalIdsFamily 2000 700`. -/
theorem localIdsFamily : LocalIdsFamily 2000 700 := fun N _ D hD =>
  ⟨τc N (max 3 N), Xc N (max 3 N),
    localIds_main N (max 3 N) D (le_max_left _ _) (le_max_right _ _) hD⟩

end Lamps
