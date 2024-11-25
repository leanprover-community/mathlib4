/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Data.Finsupp.Lex
import Mathlib.Data.Finsupp.WellFounded
import Mathlib.Data.List.TFAE
import Mathlib.Data.Finsupp.MonomialOrder

/-! # Degree and leading coefficient of polynomials with respect to a monomial order

We consider a type `σ` of indeterminates and a commutative semiring `R`
and a monomial order `m : MonomialOrder σ`.

* `m.degree f` is the degree of `f` for the monomial ordering `m`

* `m.lCoeff f` is the leading coefficient of `f` for the monomial ordering `m`

* `m.lCoeff_ne_zero_iff f` asserts that this coefficient is nonzero iff `f ≠ 0`.

* in a field, `m.lCoeff_is_unit_iff f` asserts that this coefficient is a unit iff `f ≠ 0`.

* `m.degree_add_le` : the `m.degree` of `f + g` is smaller than or equal to the supremum
of those of `f` and `g`

* `m.degree_add_of_lt h` : the `m.degree` of `f + g` is equal to that of `f`
if the `m.degree` of `g` is strictly smaller than that `f`

* `m.lCoeff_add_of_lt h`: then, the leading coefficient of `f + g` is that of `f` .

* `m.degree_add_of_ne h` : the `m.degree` of `f + g` is equal to that the supremum
of those of `f` and `g` if they are distinct

* `m.degree_sub_le` : the `m.degree` of `f - g` is smaller than or equal to the supremum
of those of `f` and `g`

* `m.degree_sub_of_lt h` : the `m.degree` of `f - g` is equal to that of `f`
if the `m.degree` of `g` is strictly smaller than that `f`

* `m.lCoeff_sub_of_lt h`: then, the leading coefficient of `f - g` is that of `f` .

* `m.degree_mul_le`: the `m.degree` of `f * g` is smaller than or equal to the sum of those of
`f` and `g`.

* `m.degree_mul_of_isRegular_left`, `m.degree_mul_of_isRegular_right` and `m.degree_mul`
assert the  equality when the leading coefficient of `f` or `g` is regular,
or when `R` is a domain and `f` and `g` are nonzero.

* `m.lCoeff_mul_of_isRegular_left`, `m.lCoeff_mul_of_isRegular_right`  and `m.lCoeff_mul`
say that `m.lCoeff (f * g) = m.lCoeff f * m.lCoeff g`

## Reference

[Becker-Weispfenning1993]

-/

namespace MonomialOrder

open MvPolynomial

open scoped MonomialOrder

variable {σ : Type*} {m : MonomialOrder σ}

section Semiring

variable {R : Type*} [CommSemiring R]

variable (m) in
/-- the degree of a multivariate polynomial with respect to a monomial ordering -/
def degree {R : Type*} [CommSemiring R] (f : MvPolynomial σ R) : σ →₀ ℕ :=
  m.toSyn.symm (f.support.sup m.toSyn)

variable (m) in
/-- the leading coefficient of a multivariate polynomial with respect to a monomial ordering -/
def lCoeff {R : Type*} [CommSemiring R] (f : MvPolynomial σ R) : R :=
  f.coeff (m.degree f)

@[simp]
theorem degree_zero : m.degree (0 : MvPolynomial σ R) = 0 := by
  simp [degree]

@[simp]
theorem lCoeff_zero : m.lCoeff (0 : MvPolynomial σ R) = 0 := by
  simp [degree, lCoeff]

theorem degree_monomial_le {d : σ →₀ ℕ} (c : R) :
    m.degree (monomial d c) ≼[m] d := by
  simp only [degree, AddEquiv.apply_symm_apply]
  apply le_trans (Finset.sup_mono support_monomial_subset)
  simp only [Finset.sup_singleton, le_refl]

theorem degree_monomial {d : σ →₀ ℕ} (c : R) [Decidable (c = 0)] :
    m.degree (monomial d c) = if c = 0 then 0 else d := by
  simp only [degree, support_monomial]
  split_ifs with hc <;> simp

@[simp]
theorem lCoeff_monomial {d : σ →₀ ℕ} (c : R) :
    m.lCoeff (monomial d c) = c := by
  classical
  simp only [lCoeff, degree_monomial]
  split_ifs with hc <;> simp [hc]

theorem degree_le_iff {f : MvPolynomial σ R} {d : σ →₀ ℕ} :
    m.degree f ≼[m] d ↔ ∀ c ∈ f.support, c ≼[m] d := by
  unfold degree
  simp only [AddEquiv.apply_symm_apply, Finset.sup_le_iff, mem_support_iff, ne_eq]

theorem degree_lt_iff {f : MvPolynomial σ R} {d : σ →₀ ℕ} (hd : 0 ≺[m] d) :
    m.degree f ≺[m] d ↔ ∀ c ∈ f.support, c ≺[m] d := by
  simp only [map_zero] at hd
  unfold degree
  simp only [AddEquiv.apply_symm_apply]
  exact Finset.sup_lt_iff hd

theorem le_degree {f : MvPolynomial σ R} {d : σ →₀ ℕ} (hd : d ∈ f.support) :
    d ≼[m] m.degree f := by
  unfold degree
  simp only [AddEquiv.apply_symm_apply, Finset.le_sup hd]

theorem coeff_eq_zero_of_lt {f : MvPolynomial σ R} {d : σ →₀ ℕ} (hd : m.degree f ≺[m] d) :
    f.coeff d = 0 := by
  rw [← not_le] at hd
  by_contra hf
  apply hd (m.le_degree (mem_support_iff.mpr hf))
theorem lCoeff_ne_zero_iff {f : MvPolynomial σ R} :
    m.lCoeff f ≠ 0 ↔ f ≠ 0 := by
  constructor
  · rw [not_imp_not]
    intro hf
    rw [hf, lCoeff_zero]
  · intro hf
    rw [← support_nonempty] at hf
    rw [lCoeff, ← mem_support_iff, degree]
    suffices f.support.sup m.toSyn ∈ m.toSyn '' f.support by
      obtain ⟨d, hd, hd'⟩ := this
      rw [← hd', AddEquiv.symm_apply_apply]
      exact hd
    exact Finset.sup_mem_of_nonempty hf

@[simp]
theorem lCoeff_eq_zero_iff {f : MvPolynomial σ R} :
    lCoeff m f = 0 ↔ f = 0 := by
  simp only [← not_iff_not, lCoeff_ne_zero_iff]

theorem coeff_degree_ne_zero_iff {f : MvPolynomial σ R} :
    f.coeff (m.degree f) ≠ 0 ↔ f ≠ 0 :=
  m.lCoeff_ne_zero_iff

@[simp]
theorem coeff_degree_eq_zero_iff {f : MvPolynomial σ R} :
    f.coeff (m.degree f) = 0 ↔ f = 0 :=
  m.lCoeff_eq_zero_iff

theorem degree_eq_zero_iff_totalDegree_eq_zero {f : MvPolynomial σ R} :
    m.degree f = 0 ↔ f.totalDegree = 0 := by
  rw [← m.toSyn.injective.eq_iff]
  rw [map_zero, ← m.bot_eq_zero, eq_bot_iff, m.bot_eq_zero, ← m.toSyn.map_zero]
  rw [degree_le_iff]
  rw [totalDegree_eq_zero_iff]
  apply forall_congr'
  intro d
  apply imp_congr (rfl.to_iff)
  rw [map_zero, ← m.bot_eq_zero, ← eq_bot_iff, m.bot_eq_zero]
  simp only [EmbeddingLike.map_eq_zero_iff]
  exact Finsupp.ext_iff

@[simp]
theorem degree_C (r : R) :
    m.degree (C r) = 0 := by
  rw [degree_eq_zero_iff_totalDegree_eq_zero, totalDegree_C]

theorem degree_add_le {f g : MvPolynomial σ R} :
    m.toSyn (m.degree (f + g)) ≤ m.toSyn (m.degree f) ⊔ m.toSyn (m.degree g) := by
  conv_rhs => rw [← m.toSyn.apply_symm_apply (_ ⊔ _)]
  rw [degree_le_iff]
  simp only [AddEquiv.apply_symm_apply, le_sup_iff]
  intro b hb
  by_cases hf : b ∈ f.support
  · left
    exact m.le_degree hf
  · right
    apply m.le_degree
    simp only [not_mem_support_iff] at hf
    simpa only [mem_support_iff, coeff_add, hf, zero_add] using hb

theorem degree_add_of_lt {f g : MvPolynomial σ R} (h : m.degree g ≺[m] m.degree f) :
    m.degree (f + g) = m.degree f := by
  apply m.toSyn.injective
  apply le_antisymm
  · apply le_trans degree_add_le
    simp only [sup_le_iff, le_refl, true_and, le_of_lt h]
  · apply le_degree
    rw [mem_support_iff, coeff_add, m.coeff_eq_zero_of_lt h, add_zero, ← lCoeff, lCoeff_ne_zero_iff]
    intro hf
    rw [← not_le, hf] at h
    apply h
    simp only [degree_zero, map_zero]
    apply bot_le

theorem lCoeff_add_of_lt {f g : MvPolynomial σ R} (h : m.degree g ≺[m] m.degree f) :
    m.lCoeff (f + g) = m.lCoeff f := by
  simp only [lCoeff, m.degree_add_of_lt h, coeff_add, coeff_eq_zero_of_lt h, add_zero]

theorem degree_add_of_ne {f g : MvPolynomial σ R}
    (h : m.degree f ≠ m.degree g) :
    m.toSyn (m.degree (f + g)) = m.toSyn (m.degree f) ⊔ m.toSyn (m.degree g) := by
  by_cases h' : m.degree g ≺[m] m.degree f
  · simp [degree_add_of_lt h', left_eq_sup, le_of_lt h']
  · rw [not_lt, le_iff_eq_or_lt, Classical.or_iff_not_imp_left, EmbeddingLike.apply_eq_iff_eq] at h'
    rw [add_comm, degree_add_of_lt (h' h), right_eq_sup]
    simp only [le_of_lt (h' h)]

theorem degree_mul_le {f g : MvPolynomial σ R} :
    m.degree (f * g) ≼[m] m.degree f + m.degree g := by
  classical
  rw [degree_le_iff]
  intro c
  rw [← not_lt, mem_support_iff, not_imp_not]
  intro hc
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨d, e⟩ hde
  simp only [Finset.mem_antidiagonal] at hde
  dsimp only
  by_cases hd : m.degree f ≺[m] d
  · rw [m.coeff_eq_zero_of_lt hd, zero_mul]
  · suffices m.degree g ≺[m] e by
      rw [m.coeff_eq_zero_of_lt this, mul_zero]
    simp only [not_lt] at hd
    apply lt_of_add_lt_add_left (a := m.toSyn d)
    simp only [← map_add, hde]
    apply lt_of_le_of_lt _ hc
    simp only [map_add]
    exact add_le_add_right hd _

/-- Multiplicativity of leading coefficients -/
theorem coeff_mul_of_degree_add {f g : MvPolynomial σ R} :
    (f * g).coeff (m.degree f + m.degree g) = m.lCoeff f * m.lCoeff g := by
  classical
  rw [coeff_mul]
  rw [Finset.sum_eq_single (m.degree f, m.degree g)]
  · rfl
  · rintro ⟨c, d⟩ hcd h
    simp only [Finset.mem_antidiagonal] at hcd
    by_cases hf : m.degree f ≺[m] c
    · rw [m.coeff_eq_zero_of_lt hf, zero_mul]
    · suffices m.degree g ≺[m] d by
        rw [coeff_eq_zero_of_lt this, mul_zero]
      apply lt_of_add_lt_add_left (a := m.toSyn c)
      simp only [← map_add, hcd]
      simp only [map_add]
      rw [← not_le]
      intro h'; apply hf
      simp only [le_iff_eq_or_lt] at h'
      cases h' with
      | inl h' =>
        simp only [← map_add, EmbeddingLike.apply_eq_iff_eq, add_left_inj] at h'
        exfalso
        apply h
        simp only [h', Prod.mk.injEq, true_and]
        simpa [h'] using hcd
      | inr h' =>
        exact lt_of_add_lt_add_right h'
  · simp

/-- Multiplicativity of leading coefficients -/
theorem degree_mul_of_isRegular_left {f g : MvPolynomial σ R}
    (hf : IsRegular (m.lCoeff f)) (hg : g ≠ 0) :
    m.degree (f * g) = m.degree f + m.degree g := by
  apply m.toSyn.injective
  apply le_antisymm degree_mul_le
  apply le_degree
  rw [mem_support_iff, coeff_mul_of_degree_add]
  simp only [ne_eq, hf, IsRegular.left, IsLeftRegular.mul_left_eq_zero_iff,
    lCoeff_eq_zero_iff]
  exact hg

/-- Multiplicativity of leading coefficients -/
theorem lCoeff_mul_of_isRegular_left {f g : MvPolynomial σ R}
    (hf : IsRegular (m.lCoeff f)) (hg : g ≠ 0) :
    m.lCoeff (f * g) = m.lCoeff f * m.lCoeff g := by
  simp only [lCoeff, degree_mul_of_isRegular_left hf hg, coeff_mul_of_degree_add]

/-- Multiplicativity of leading coefficients -/
theorem degree_mul_of_isRegular_right {f g : MvPolynomial σ R}
    (hf : f ≠ 0) (hg : IsRegular (m.lCoeff g)) :
    m.degree (f * g) = m.degree f + m.degree g := by
  rw [mul_comm, m.degree_mul_of_isRegular_left hg hf, add_comm]

/-- Multiplicativity of leading coefficients -/
theorem lCoeff_mul_of_isRegular_right {f g : MvPolynomial σ R}
    (hf : f ≠ 0) (hg : IsRegular (m.lCoeff g)) :
    m.lCoeff (f * g) = m.lCoeff f * m.lCoeff g := by
  simp only [lCoeff, degree_mul_of_isRegular_right hf hg, coeff_mul_of_degree_add]

/-- Degree of product -/
theorem degree_mul [IsDomain R] {f g : MvPolynomial σ R} (hf : f ≠ 0) (hg : g ≠ 0) :
    m.degree (f * g) = m.degree f + m.degree g :=
  degree_mul_of_isRegular_left (isRegular_of_ne_zero (lCoeff_ne_zero_iff.mpr hf)) hg

/-- Degree of of product -/
theorem degree_mul_of_nonzero_mul [IsDomain R] {f g : MvPolynomial σ R} (hfg : f * g ≠ 0) :
    m.degree (f * g) = m.degree f + m.degree g :=
  degree_mul (left_ne_zero_of_mul hfg) (right_ne_zero_of_mul hfg)

/-- Multiplicativity of leading coefficients -/
theorem lCoeff_mul [IsDomain R] {f g : MvPolynomial σ R}
    (hf : f ≠ 0) (hg : g ≠ 0) :
    m.lCoeff (f * g) = m.lCoeff f * m.lCoeff g := by
  rw [lCoeff, degree_mul hf hg, ← coeff_mul_of_degree_add]

theorem degree_smul_le {r : R} {f : MvPolynomial σ R} :
    m.degree (r • f) ≼[m] m.degree f := by
  rw [smul_eq_C_mul]
  apply le_of_le_of_eq degree_mul_le
  simp

theorem degree_smul {r : R} (hr : IsRegular r) {f : MvPolynomial σ R} :
    m.degree (r • f) = m.degree f := by
  by_cases hf : f = 0
  · simp [hf]
  apply m.toSyn.injective
  apply le_antisymm degree_smul_le
  apply le_degree
  simp only [mem_support_iff, smul_eq_C_mul]
  rw [← zero_add (degree m f), ← degree_C r, coeff_mul_of_degree_add]
  simp [lCoeff, hr.left.mul_left_eq_zero_iff, hf]

theorem eq_C_of_degree_eq_zero {f : MvPolynomial σ R} (hf : m.degree f = 0) :
    f = C (m.lCoeff f) := by
  ext d
  simp only [lCoeff, hf]
  classical
  by_cases hd : d = 0
  · simp [hd]
  · rw [coeff_C, if_neg (Ne.symm hd)]
    apply coeff_eq_zero_of_lt (m := m)
    rw [hf, map_zero, lt_iff_le_and_ne, ne_eq, eq_comm, EmbeddingLike.map_eq_zero_iff]
    exact ⟨bot_le, hd⟩

end Semiring

section Ring

variable {R : Type*} [CommRing R]

@[simp]
theorem degree_neg {f : MvPolynomial σ R} :
    m.degree (-f) = m.degree f := by
  unfold degree
  rw [support_neg]

theorem degree_sub_le {f g : MvPolynomial σ R} :
    m.toSyn (m.degree (f - g)) ≤ m.toSyn (m.degree f) ⊔ m.toSyn (m.degree g) := by
  rw [sub_eq_add_neg]
  apply le_of_le_of_eq m.degree_add_le
  rw [degree_neg]

theorem degree_sub_of_lt {f g : MvPolynomial σ R} (h : m.degree g ≺[m] m.degree f) :
    m.degree (f - g) = m.degree f := by
  rw [sub_eq_add_neg]
  apply degree_add_of_lt
  simp only [degree_neg, h]

theorem lCoeff_sub_of_lt {f g : MvPolynomial σ R} (h : m.degree g ≺[m] m.degree f) :
    m.lCoeff (f - g) = m.lCoeff f := by
  rw [sub_eq_add_neg]
  apply lCoeff_add_of_lt
  simp only [degree_neg, h]

end Ring

section Field

variable {R : Type*} [Field R]

theorem lCoeff_is_unit_iff {f : MvPolynomial σ R} :
    IsUnit (m.lCoeff f) ↔ f ≠ 0 := by
  simp only [isUnit_iff_ne_zero, ne_eq, lCoeff_eq_zero_iff]

end Field

end MonomialOrder
