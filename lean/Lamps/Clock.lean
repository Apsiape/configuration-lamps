import Lamps.Group
import Mathlib.Tactic.Group

/-!
# Lemma `lem:clock` (part 1, `prop:upper`): the clock cocycles of `p, q` are supported in `Y_R`

Heights: the point `(i, j) : Y = Fin 3 × ℕ` is the paper's `(i+1, j+1)`, of height `ht y = j + 1`.
`pY, qY` act on every ray as translations by `δp = (+1, -1, 0)`, `δq = (+1, 0, -1)` as long as the
point stays in the ray (`IsShift`). Hence (sharp form of the paper's claim)
`[pY^{y₁}, qY^{y₂}]` fixes every point of height `> |y₁| + |y₂|` (`comm_fix`), and for `z ∈ B_m`
the cocycles `g_{z+π(s)}⁻¹ s g_z` and `g_z s g_{z+π(s)}⁻¹` of `s = p^{±1}, q^{±1}` fix every point of
height `> 2m + 2`, so they restrict to permutations of `Y_R`, `R = 2m + 3` (`clock`, `clockRestrict`).
-/

namespace Lamps

open Houghton (Y aPerm bPerm)

/-- Height of a point (`(i, j)` is the paper's `(i+1, j+1)`). -/
def ht (y : Y) : ℕ := y.2 + 1

/-- `g` is supported in `Y_R`: it fixes every point of height `> R`. -/
def SuppIn (R : ℕ) (g : Equiv.Perm Y) : Prop := ∀ y : Y, R < ht y → g y = y

/-- `Y_R` as a finset. -/
def YR (R : ℕ) : Finset Y := Finset.univ ×ˢ Finset.range R

theorem mem_YR (R : ℕ) (y : Y) : y ∈ YR R ↔ ht y ≤ R := by
  simp [YR, ht]; omega

/-! ### Translations along the rays -/

/-- `f` translates ray `i` by `δ i ∈ {-1, 0, 1}` wherever source and target lie in the ray. -/
def IsShift (f : Equiv.Perm Y) (δ : Fin 3 → ℤ) : Prop :=
  (∀ i, δ i = -1 ∨ δ i = 0 ∨ δ i = 1) ∧
    ∀ (i : Fin 3) (j j' : ℕ), (j' : ℤ) = j + δ i → f (i, j) = (i, j')

def δp : Fin 3 → ℤ := ![1, -1, 0]
def δq : Fin 3 → ℤ := ![1, 0, -1]

theorem isShift_pY : IsShift pY δp := by
  refine ⟨fun i => by fin_cases i <;> simp [δp], fun i j j' h => ?_⟩
  fin_cases i
  · obtain rfl : j' = j + 1 := by simp [δp] at h; omega
    rfl
  · obtain ⟨j, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by simp [δp] at h; omega⟩
    obtain rfl : j' = j := by simp [δp] at h; omega
    rfl
  · obtain rfl : j' = j := by simp [δp] at h; omega
    rfl

theorem isShift_qY : IsShift qY δq := by
  refine ⟨fun i => by fin_cases i <;> simp [δq], fun i j j' h => ?_⟩
  fin_cases i
  · obtain rfl : j' = j + 1 := by simp [δq] at h; omega
    rfl
  · obtain rfl : j' = j := by simp [δq] at h; omega
    rfl
  · obtain ⟨j, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by simp [δq] at h; omega⟩
    obtain rfl : j' = j := by simp [δq] at h; omega
    rfl

theorem IsShift.inv {f : Equiv.Perm Y} {δ : Fin 3 → ℤ} (h : IsShift f δ) : IsShift f⁻¹ (-δ) := by
  refine ⟨fun i => by rcases h.1 i with h1 | h1 | h1 <;> simp [h1], fun i j j' hj => ?_⟩
  rw [Equiv.Perm.inv_eq_iff_eq]
  exact (h.2 i j' j (by simp at hj; omega)).symm

theorem IsShift.pow_apply {f : Equiv.Perm Y} {δ : Fin 3 → ℤ} (h : IsShift f δ) :
    ∀ (n : ℕ) (i : Fin 3) (j j' : ℕ), (j' : ℤ) = j + n * δ i → (f ^ n) (i, j) = (i, j')
  | 0, i, j, j', hj => by simp at hj; simp [hj]
  | n + 1, i, j, j', hj => by
    obtain ⟨j1, hj1⟩ : ∃ j1 : ℕ, (j1 : ℤ) = j + n * δ i :=
      ⟨((j : ℤ) + n * δ i).toNat, Int.toNat_of_nonneg (by
        rcases h.1 i with h1 | h1 | h1 <;> rw [h1] at hj ⊢ <;> push_cast at hj ⊢ <;> omega)⟩
    rw [pow_succ', Equiv.Perm.mul_apply, h.pow_apply n i j j1 hj1]
    exact h.2 i j1 j' (by push_cast at hj; rw [hj, hj1]; ring)

theorem IsShift.zpow_apply {f : Equiv.Perm Y} {δ : Fin 3 → ℤ} (h : IsShift f δ) (n : ℤ)
    (i : Fin 3) (j j' : ℕ) (hj : (j' : ℤ) = j + n * δ i) : (f ^ n) (i, j) = (i, j') := by
  rcases n with n | n
  · rw [Int.ofNat_eq_natCast, zpow_natCast]; exact h.pow_apply n i j j' (by simpa using hj)
  · rw [zpow_negSucc, ← inv_pow]
    exact h.inv.pow_apply (n + 1) i j j' (by rw [hj, Int.negSucc_eq]; simp; ring)

lemma mul_delta_bound (y d : ℤ) (hd : d = -1 ∨ d = 0 ∨ d = 1) : -|y| ≤ y * d ∧ y * d ≤ |y| := by
  rcases hd with rfl | rfl | rfl
  · simp only [mul_neg, mul_one]; exact ⟨neg_le_neg (le_abs_self y), neg_le_abs y⟩
  · simp
  · simp only [mul_one]; exact ⟨neg_abs_le y, le_abs_self y⟩

/-- A shift power applied to a point high enough stays computable. -/
lemma shift_exists {f : Equiv.Perm Y} {δ : Fin 3 → ℤ} (h : IsShift f δ) (n : ℤ) (i : Fin 3)
    (j : ℕ) (hj : |n| ≤ j) : ∃ j' : ℕ, (j' : ℤ) = j + n * δ i ∧ (f ^ n) (i, j) = (i, j') := by
  have hb := mul_delta_bound n (δ i) (h.1 i)
  have hx0 : 0 ≤ (j : ℤ) + n * δ i := by omega
  exact ⟨((j : ℤ) + n * δ i).toNat, Int.toNat_of_nonneg hx0,
    h.zpow_apply n i j _ (Int.toNat_of_nonneg hx0)⟩

/-! ### The commutator -/

/-- **`[p^{y₁}, q^{y₂}]` fixes every point of height `> |y₁| + |y₂|`** (the paper states `> |y₁|+|y₂|+1`). -/
theorem comm_fix (y₁ y₂ : ℤ) : SuppIn (y₁.natAbs + y₂.natAbs)
    (pY ^ y₁ * qY ^ y₂ * (pY ^ y₁)⁻¹ * (qY ^ y₂)⁻¹) := by
  rintro ⟨i, j⟩ hy
  simp only [ht] at hy
  have hj : |y₁| + |y₂| ≤ (j : ℤ) := by
    have := Int.natCast_natAbs y₁; have := Int.natCast_natAbs y₂; omega
  have bp := mul_delta_bound y₁ (δp i) (isShift_pY.1 i)
  have bq := mul_delta_bound y₂ (δq i) (isShift_qY.1 i)
  simp only [Equiv.Perm.mul_apply, ← zpow_neg]
  obtain ⟨j1, e1, h1⟩ := shift_exists isShift_qY (-y₂) i j (by rw [abs_neg]; omega)
  rw [h1]
  obtain ⟨j2, e2, h2⟩ := shift_exists isShift_pY (-y₁) i j1
    (by rw [abs_neg]; rw [e1, neg_mul]; omega)
  rw [h2]
  rw [isShift_qY.zpow_apply y₂ i j2 ((j : ℤ) - y₁ * δp i).toNat
    (by rw [Int.toNat_of_nonneg (by omega), e2, e1]; ring)]
  rw [isShift_pY.zpow_apply y₁ i _ j (by rw [Int.toNat_of_nonneg (by omega)]; ring)]

lemma SuppIn.mono {R R' : ℕ} {g : Equiv.Perm Y} (h : SuppIn R g) (hR : R ≤ R') : SuppIn R' g :=
  fun y hy => h y (by omega)

lemma SuppIn.inv {R : ℕ} {g : Equiv.Perm Y} (h : SuppIn R g) : SuppIn R g⁻¹ := fun y hy => by
  rw [Equiv.Perm.inv_eq_iff_eq]; exact (h y hy).symm

lemma SuppIn.one (R : ℕ) : SuppIn R 1 := fun _ _ => rfl

/-- Conjugating by a shift power enlarges the support height by at most `|n|`. -/
lemma SuppIn.conj {f : Equiv.Perm Y} {δ : Fin 3 → ℤ} (hf : IsShift f δ) {R : ℕ} {C : Equiv.Perm Y}
    (hC : SuppIn R C) (n : ℤ) : SuppIn (R + n.natAbs) (f ^ n * C * (f ^ n)⁻¹) := by
  rintro ⟨i, j⟩ hy
  simp only [ht] at hy
  have hn := Int.natCast_natAbs n
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← zpow_neg]
  obtain ⟨j', e, h⟩ := shift_exists hf (-n) i j (by rw [abs_neg]; omega)
  rw [h, hC (i, j') (by
    have := mul_delta_bound (-n) (δ i) (hf.1 i); simp only [ht]; rw [abs_neg] at this; omega)]
  rw [← h, ← Equiv.Perm.mul_apply, ← zpow_add, add_neg_cancel, zpow_zero, Equiv.Perm.one_apply]

/-! ### The clock cocycles (`lem:clock`) -/

/-- `g_z = p^{z₁} q^{z₂}` acting on `Y`. -/
def gz (z : ℤ × ℤ) : Equiv.Perm Y := pY ^ z.1 * qY ^ z.2

lemma natAbs_le_of_abs_le {x : ℤ} {m : ℕ} (h : |x| ≤ m) : x.natAbs ≤ m := by
  have := Int.natCast_natAbs x; omega

lemma clock_aux_p (z1 z2 e : ℤ) (m : ℕ) (hz1 : z1.natAbs ≤ m) (hz2 : z2.natAbs ≤ m)
    (he : e.natAbs = 1) :
    (gz (z1 + e, z2))⁻¹ * pY ^ e * gz (z1, z2) = 1 ∧
      SuppIn (2 * m + 1) (gz (z1, z2) * pY ^ e * (gz (z1 + e, z2))⁻¹) := by
  constructor
  · simp only [gz, zpow_add]; group
  · have hC' := SuppIn.conj isShift_pY (comm_fix e z2).inv z1
    have e1 : gz (z1, z2) * pY ^ e * (gz (z1 + e, z2))⁻¹ =
        pY ^ z1 * (pY ^ e * qY ^ z2 * (pY ^ e)⁻¹ * (qY ^ z2)⁻¹)⁻¹ * (pY ^ z1)⁻¹ := by
      simp only [gz, zpow_add]; group
    rw [e1]
    exact hC'.mono (by omega)

lemma clock_aux_q (z1 z2 e : ℤ) (m : ℕ) (hz1 : z1.natAbs ≤ m) (hz2 : z2.natAbs ≤ m)
    (he : e.natAbs = 1) :
    SuppIn (2 * m + 2) ((gz (z1, z2 + e))⁻¹ * qY ^ e * gz (z1, z2)) ∧
      gz (z1, z2) * qY ^ e * (gz (z1, z2 + e))⁻¹ = 1 := by
  constructor
  · have hC' := SuppIn.conj isShift_qY (comm_fix (-z1) e) (-(z2 + e))
    have e1 : (gz (z1, z2 + e))⁻¹ * qY ^ e * gz (z1, z2) =
        qY ^ (-(z2 + e)) * (pY ^ (-z1) * qY ^ e * (pY ^ (-z1))⁻¹ * (qY ^ e)⁻¹) *
          (qY ^ (-(z2 + e)))⁻¹ := by
      simp only [gz, zpow_add, zpow_neg]; group
    rw [e1]
    refine hC'.mono ?_
    have h1 := Int.natAbs_add_le z2 e
    rw [Int.natAbs_neg, Int.natAbs_neg]
    omega
  · simp only [gz, zpow_add]; group

/-- The four generators `s = p^{±1}, q^{±1}` with their clock increments `π(s)`. -/
def ClockGen (s : Equiv.Perm Y) (e : ℤ × ℤ) : Prop :=
  (s = pY ∧ e = (1, 0)) ∨ (s = pY⁻¹ ∧ e = (-1, 0)) ∨ (s = qY ∧ e = (0, 1)) ∨ (s = qY⁻¹ ∧ e = (0, -1))

/-- **Lemma `lem:clock`** (permutation part): for `z ∈ B_m` and `s = p^{±1}, q^{±1}` with clock
increment `π(s) = e`, both `g_{z+e}⁻¹ s g_z` and `g_z s g_{z+e}⁻¹` fix every point of height
`> 2m + 2` (one of them is `1`). -/
theorem clock (m : ℕ) (z : ℤ × ℤ) (hz1 : |z.1| ≤ m) (hz2 : |z.2| ≤ m) (s : Equiv.Perm Y)
    (e : ℤ × ℤ) (hs : ClockGen s e) :
    SuppIn (2 * m + 2) ((gz (z + e))⁻¹ * s * gz z) ∧
      SuppIn (2 * m + 2) (gz z * s * (gz (z + e))⁻¹) := by
  obtain ⟨z1, z2⟩ := z
  have h1 := natAbs_le_of_abs_le hz1
  have h2 := natAbs_le_of_abs_le hz2
  simp only at h1 h2
  rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [Prod.mk_add_mk, add_zero]
  · obtain ⟨a1, a2⟩ := clock_aux_p z1 z2 1 m h1 h2 rfl
    rw [zpow_one] at a1 a2
    exact ⟨by rw [a1]; exact SuppIn.one _, a2.mono (by omega)⟩
  · obtain ⟨a1, a2⟩ := clock_aux_p z1 z2 (-1) m h1 h2 rfl
    rw [zpow_neg, zpow_one] at a1 a2
    exact ⟨by rw [a1]; exact SuppIn.one _, a2.mono (by omega)⟩
  · obtain ⟨a1, a2⟩ := clock_aux_q z1 z2 1 m h1 h2 rfl
    rw [zpow_one] at a1 a2
    exact ⟨a1, by rw [a2]; exact SuppIn.one _⟩
  · obtain ⟨a1, a2⟩ := clock_aux_q z1 z2 (-1) m h1 h2 rfl
    rw [zpow_neg, zpow_one] at a1 a2
    exact ⟨a1, by rw [a2]; exact SuppIn.one _⟩

/-! ### Restriction to `Y_R` and the bridge to `Γ` -/

lemma SuppIn.mem_iff {R : ℕ} {g : Equiv.Perm Y} (h : SuppIn R g) (y : Y) :
    y ∈ YR R ↔ g y ∈ YR R := by
  rw [mem_YR, mem_YR]
  constructor
  · intro hy
    by_contra hgy
    have := h (g y) (by omega)
    rw [g.injective this] at hgy; exact hgy hy
  · intro hgy
    by_contra hy
    rw [h y (by omega)] at hgy; exact hy hgy

/-- The restriction of a permutation supported in `Y_R` to a permutation of the finite set `Y_R`. -/
def restrictR (R : ℕ) (g : Equiv.Perm Y) (h : SuppIn R g) : Equiv.Perm (YR R) :=
  g.subtypePerm (fun y => (h.mem_iff y).symm)

theorem restrictR_apply (R : ℕ) (g : Equiv.Perm Y) (h : SuppIn R g) (y : YR R) :
    (restrictR R g h y : Y) = g y := rfl

/-- **Lemma `lem:clock`, restricted form** (`R = 2m + 3`): the clock cocycles of `p^{±1}, q^{±1}`
on the box `B_m` are permutations of `Y_R` extended by the identity. -/
theorem clock_restrict (m : ℕ) (z : ℤ × ℤ) (hz1 : |z.1| ≤ m) (hz2 : |z.2| ≤ m)
    (s : Equiv.Perm Y) (e : ℤ × ℤ) (hs : ClockGen s e) :
    SuppIn (2 * m + 3) ((gz (z + e))⁻¹ * s * gz z) ∧
      SuppIn (2 * m + 3) (gz z * s * (gz (z + e))⁻¹) :=
  ⟨(clock m z hz1 hz2 s e hs).1.mono (by omega), (clock m z hz1 hz2 s e hs).2.mono (by omega)⟩

/-- `g_z = p^{z₁} q^{z₂}` as a word, and its action on `X`. -/
def gzW (z : ℤ × ℤ) : F := p ^ z.1 * q ^ z.2

theorem rho_gzW (z : ℤ × ℤ) : ρΓ (gzW z) = hV (gz z) := by
  simp [gzW, gz, map_mul, map_zpow, rho_p, rho_q]

/-- The cocycles as elements of `Γ`: if the word `w` acts as `hV s`, the words
`g_{z'}⁻¹ w g_z` and `g_z w g_{z'}⁻¹` act as `hV` of the corresponding permutations. -/
theorem rho_cocycle (z z' : ℤ × ℤ) (w : F) (s : Equiv.Perm Y) (hw : ρΓ w = hV s) :
    ρΓ ((gzW z')⁻¹ * w * gzW z) = hV ((gz z')⁻¹ * s * gz z) ∧
      ρΓ (gzW z * w * (gzW z')⁻¹) = hV (gz z * s * (gz z')⁻¹) := by
  simp only [map_mul, map_inv, rho_gzW, hw, and_self]

/-- The four letters `p^{±1}, q^{±1}` of `Γ` act as `hV` of the four `ClockGen` permutations. -/
theorem rho_clockGen : ρΓ p = hV pY ∧ ρΓ p⁻¹ = hV pY⁻¹ ∧ ρΓ q = hV qY ∧ ρΓ q⁻¹ = hV qY⁻¹ :=
  ⟨rho_p, by rw [map_inv, rho_p, map_inv], rho_q, by rw [map_inv, rho_q, map_inv]⟩

/-- A permutation supported in `Y_R` maps configurations inside `Y_R` to configurations inside `Y_R`
and fixes every configuration of points of height `> R`. -/
theorem SuppIn.map_YR {R : ℕ} {g : Equiv.Perm Y} (h : SuppIn R g) (v : Finset Y) :
    (v ⊆ YR R → v.map g.toEmbedding ⊆ YR R) ∧
      ((∀ y ∈ v, R < ht y) → v.map g.toEmbedding = v) := by
  constructor
  · intro hv y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
    exact (h.mem_iff x).mp (hv hx)
  · intro hv
    ext y
    simp only [Finset.mem_map, Equiv.coe_toEmbedding]
    constructor
    · rintro ⟨x, hx, rfl⟩; rw [h x (hv x hx)]; exact hx
    · intro hy; exact ⟨y, hy, h y (hv y hy)⟩

end Lamps
