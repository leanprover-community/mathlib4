/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos Fernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/

import Mathlib.Data.ENat.Basic
import Mathlib.Data.Finsupp.Weight
import Mathlib.RingTheory.MvPowerSeries.Basic

/-! # Order of multivariate power series

We work with `MvPowerSeries σ R`, for `Semiring R`, and `w : σ → ℕ`

## Weighted Order

- `MvPowerSeries.weightedOrder`: the weighted order of a multivariate power series,
with respect to `w`, as an element of `ℕ∞`.

- `MvPowerSeries.weightedOrder_zero`: the weighted order of `0` is `0`.

- `MvPowerSeries.ne_zero_iff_weightedOrder_finite`: a multivariate power series is nonzero if
and only if its weighted order is finite.

- `MvPowerSeries.exists_coeff_ne_zero_of_weightedOrder`: if the weighted order is finite,
then there exists a nonzero coefficient of weight the weighted order.

- `MvPowerSeries.weightedOrder_le` : if a coefficient is nonzero, then the weighted order is at
most the weight of that exponent.

- `MvPowerSeries.coeff_eq_zero_of_lt_weightedOrder`: all coefficients of weights strictly less
than the weighted order vanish

- `MvPowerSeries.weightedOrder_eq_top_iff`: the weighted order of `f` is `⊤` if and only `f = 0`.

- `MvPowerSeries.nat_le_weightedOrder`: if all coefficients of weight `< n` vanish, then the
weighted order is at least `n`.

- `MvPowerSeries.weightedOrder_eq_nat_iff`: the weighted order is some integer `n` iff there
exists a nonzero coefficient of weight `n`, and all coefficients of strictly smaller weight vanish.

- `MvPowerSeries.weightedOrder_monomial`, `MvPowerSeries.weightedOrder_monomial_of_ne_zero`:
the weighted order of a monomial, of a monomial with nonzero coefficient.

- `MvPowerSeries.min_weightedOrder_le_add`: the order of the sum of two multivariate power series
is at least the minimum of their orders.

- `MvPowerSeries.weightedOrder_add_of_weightedOrder_ne`: the weighted_order of the sum of two
formal power series is the minimum of their orders if their orders differ.

- `MvPowerSeries.le_weightedOrder_mul`: the weighted_order of the product of two formal power
series is at least the sum of their orders.

- `MvPowerSeries.coeff_mul_left_one_sub_of_lt_weightedOrder`,
`MvPowerSeries.coeff_mul_right_one_sub_of_lt_weightedOrder`: the coefficients of `f * (1 - g)`
and `(1 - g) * f` in weights strictly less than the weighted order of `g`.

- `MvPowerSeries.coeff_mul_prod_one_sub_of_lt_weightedOrder`: the coefficients of
`f * Π i in s, (1 - g i)`, in weights strictly less than the weighted orders of `g i`, for `i ∈ s`.

## Order

- `MvPowerSeries.order`: the weighted order, for `w = (1 : σ → ℕ)`.

- `MvPowerSeries.ne_zero_iff_order_finite`: `f` is nonzero iff its order is finite.

- `MvPowerSeries.order_eq_top_iff`: the order of `f` is infinite iff  `f = 0`.

- `MvPowerSeries.exists_coeff_ne_zero_of_order`: if the order is finite, then there exists a
nonzero coefficient of degree equal to the order.

- `MvPowerSeries.order_le` : if a coefficient of some degree is nonzero, then the order
is at least that degree.

- `MvPowerSeries.nat_le_order`: if all coefficients of degree strictly smaller than some integer
vanish, then the order is at at least that integer.

- `MvPowerSeries.order_eq_nat_iff`:  the order of a power series is an integer `n` iff there exists
a nonzero coefficient in that degree, and all coefficients below that degree vanish.

- `MvPowerSeries.order_monomial`, `MvPowerSeries.order_monomial_of_ne_zero`: the order of a
monomial, with a non zero coefficient

- `MvPowerSeries.min_order_le_add`: the order of a sum of two power series is at least the minimum
of their orders.

- `MvPowerSeries.order_add_of_order_ne`: the order of a sum of two power series of distinct orders
is the minimum of their orders.

- `MvPowerSeries.order_mul_ge`: the order of a product of two power series is at least the sum of
their orders.

- `MvPowerSeries.coeff_mul_left_one_sub_of_lt_order`,
`MvPowerSeries.coeff_mul_right_one_sub_of_lt_order`: the coefficients of `f * (1 - g)` and
`(1 - g) * f` below the order of `g` coincide with that of `f`.

- `MvPowerSeries.coeff_mul_prod_one_sub_of_lt_order`: the coefficients of `f * Π i in s, (1 - g i)`
coincide with that of `f` below the minimum of the orders of the `g i`, for `i ∈ s`.

## Homogeneous components

- `MvPowerSeries.weightedHomogeneousComponent`, `MvPowerSeries.homogeneousComponent`: the power
series which is the sum of all monomials of given weighted degree, resp. degree.

NOTE:
Under `Finite σ`, one can use `Finsupp.finite_of_degree_le` and `Finsupp.finite_of_weight_le` to
show that they have finite support, hence correspond to `MvPolynomial`.

However, when `σ` is finite, this is not necessarily an `MvPolynomial`.
(For example: the homogeneous components of degree 1 of the multivariate power
series, all of which coefficients are `1`, is the sum of all indeterminates.)

TODO: Define a coercion to MvPolynomial.

-/

namespace MvPowerSeries

noncomputable section

open ENat WithTop Finsupp

variable {σ R : Type*} [Semiring R]

section WeightedOrder

variable (w : σ → ℕ) {f g : MvPowerSeries σ R}

theorem ne_zero_iff_exists_coeff_ne_zero_and_weight :
    f ≠ 0 ↔ (∃ n : ℕ, ∃ d : σ →₀ ℕ, coeff R d f ≠ 0 ∧ weight w d = n) := by
  refine not_iff_not.mp ?_
  simp only [ne_eq, not_not, not_exists, not_and, forall_apply_eq_imp_iff₂, imp_false]
  exact MvPowerSeries.ext_iff

/-- The weighted order of a mv_power_series -/
def weightedOrder (f : MvPowerSeries σ R) : ℕ∞ := by
  classical
  exact dite (f = 0) (fun _ => ⊤) fun h =>
    Nat.find ((ne_zero_iff_exists_coeff_ne_zero_and_weight w).mp h)

@[simp] theorem weightedOrder_zero : (0 : MvPowerSeries σ R).weightedOrder w = ⊤ := by
  rw [weightedOrder, dif_pos rfl]

theorem ne_zero_iff_weightedOrder_finite :
    f ≠ 0 ↔ (f.weightedOrder w).toNat = f.weightedOrder w := by
  simp only [weightedOrder, ne_eq, coe_toNat_eq_self, dite_eq_left_iff,
    ENat.coe_ne_top, imp_false, not_not]

/-- The `0` power series is the unique power series with infinite order. -/
@[simp]
theorem weightedOrder_eq_top_iff :
    f.weightedOrder w = ⊤ ↔ f = 0 := by
  rw [← not_iff_not, ← ne_eq, ← ne_eq,   ne_zero_iff_weightedOrder_finite w, coe_toNat_eq_self]

/-- If the order of a formal power series `f` is finite,
then some coefficient of weight equal to the order of `f` is nonzero. -/
theorem exists_coeff_ne_zero_and_weightedOrder
    (h : (toNat (f.weightedOrder w) : ℕ∞) = f.weightedOrder w) :
    ∃ d, coeff R d f ≠ 0 ∧ weight w d = f.weightedOrder w := by
  classical
  simp_rw [weightedOrder, dif_neg ((ne_zero_iff_weightedOrder_finite w).mpr h), Nat.cast_inj]
  generalize_proofs h1
  exact Nat.find_spec h1

/-- If the `d`th coefficient of a formal power series is nonzero,
then the weighted order of the power series is less than or equal to `weight d w`. -/
theorem weightedOrder_le {d : σ →₀ ℕ} (h : coeff R d f ≠ 0) :
    f.weightedOrder w ≤ weight w d := by
  rw [weightedOrder, dif_neg]
  · simp only [ne_eq, Nat.cast_le, Nat.find_le_iff]
    exact ⟨weight w d, le_rfl, d, h, rfl⟩
  · exact (f.ne_zero_iff_exists_coeff_ne_zero_and_weight w).mpr ⟨weight w d, d, h, rfl⟩

/-- The `n`th coefficient of a formal power series is `0` if `n` is strictly
smaller than the order of the power series. -/
theorem coeff_eq_zero_of_lt_weightedOrder {d : σ →₀ ℕ} (h : (weight w d) < f.weightedOrder w) :
    coeff R d f = 0 := by
  contrapose! h; exact weightedOrder_le w h

/-- The order of a formal power series is at least `n` if
the `d`th coefficient is `0` for all `d` such that `weight w d < n`. -/
theorem nat_le_weightedOrder {n : ℕ} (h : ∀ d, weight w d < n → coeff R d f = 0) :
    n ≤ f.weightedOrder w := by
  by_contra! H
  have : (f.weightedOrder w).toNat = f.weightedOrder w := by
    rw [coe_toNat_eq_self]; exact ne_top_of_lt H
  obtain ⟨d, hfd, hd⟩ := exists_coeff_ne_zero_and_weightedOrder w this
  rw [← hd, Nat.cast_lt] at H
  exact hfd (h d H)

/-- The order of a formal power series is at least `n` if
the `d`th coefficient is `0` for all `d` such that `weight w d < n`. -/
theorem le_weightedOrder {n : ℕ∞} (h : ∀ d : σ →₀ ℕ, weight w d < n → coeff R d f = 0) :
    n ≤ f.weightedOrder w := by
  cases n
  · rw [top_le_iff, weightedOrder_eq_top_iff]
    ext d; exact h d (ENat.coe_lt_top _)
  · apply nat_le_weightedOrder;
    simpa only [ENat.some_eq_coe, Nat.cast_lt] using h

/-- The order of a formal power series is exactly `n` if and only if some coefficient of weight `n`
is nonzero, and the `d`th coefficient is `0` for all `d` such that `weight w d < n`. -/
theorem weightedOrder_eq_nat {n : ℕ} :
    f.weightedOrder w = n ↔
      (∃ d, coeff R d f ≠ 0 ∧ weight w d = n) ∧ ∀ d, weight w d < n → coeff R d f = 0 := by
  constructor
  · intro h
    obtain ⟨d, hd⟩ := f.exists_coeff_ne_zero_and_weightedOrder w (by simp only [h, toNat_coe])
    exact ⟨⟨d, by simpa [h, Nat.cast_inj, ne_eq] using hd⟩,
      fun e he ↦ f.coeff_eq_zero_of_lt_weightedOrder w (by simp only [h, Nat.cast_lt, he])⟩
  · rintro ⟨⟨d, hd', hd⟩, h⟩
    exact le_antisymm (hd.symm ▸ f.weightedOrder_le w hd') (nat_le_weightedOrder w h)

/-- The weighted_order of the monomial `a*X^d` is infinite if `a = 0` and `weight w d` otherwise. -/
theorem weightedOrder_monomial {d : σ →₀ ℕ} {a : R} [Decidable (a = 0)] :
    weightedOrder w (monomial R d a) = if a = 0 then (⊤ : ℕ∞) else weight w d := by
  classical
  split_ifs with h
  · rw [h, weightedOrder_eq_top_iff, LinearMap.map_zero]
  · rw [weightedOrder_eq_nat]
    constructor
    · use d
      simp only [coeff_monomial_same, ne_eq, h, not_false_eq_true, and_self]
    · intro b hb
      rw [coeff_monomial, if_neg]
      intro h
      simp only [h, lt_self_iff_false] at hb

/-- The order of the monomial `a*X^n` is `n` if `a ≠ 0`. -/
theorem weightedOrder_monomial_of_ne_zero {d : σ →₀ ℕ} {a : R} (h : a ≠ 0) :
    weightedOrder w (monomial R d a) = weight w d := by
  classical
  rw [weightedOrder_monomial, if_neg h]


/-- The order of the sum of two formal power series is at least the minimum of their orders. -/
theorem min_weightedOrder_le_add :
    min (f.weightedOrder w) (g.weightedOrder w) ≤ (f + g).weightedOrder w := by
  apply le_weightedOrder w
  simp (config := { contextual := true }) only
    [coeff_eq_zero_of_lt_weightedOrder w, lt_min_iff, map_add, add_zero,
      eq_self_iff_true, imp_true_iff]

private theorem weightedOrder_add_of_weightedOrder_lt.aux
    (H : f.weightedOrder w < g.weightedOrder w) :
    (f + g).weightedOrder w = f.weightedOrder w := by
  obtain ⟨n, hn : (n : ℕ∞) = _⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt H)
  rw [← hn, weightedOrder_eq_nat]
  obtain ⟨d, hd', hd⟩ := ((weightedOrder_eq_nat w).mp hn.symm).1
  constructor
  · refine ⟨d, ?_, hd⟩
    rw [← hn, ← hd] at H
    rw [(coeff _ _).map_add, coeff_eq_zero_of_lt_weightedOrder w H, add_zero]
    exact hd'
  · intro b hb
    suffices weight w b < weightedOrder w f by
      rw [(coeff _ _).map_add, coeff_eq_zero_of_lt_weightedOrder w this,
        coeff_eq_zero_of_lt_weightedOrder w (lt_trans this H), add_zero]
    rw [← hn, Nat.cast_lt]
    exact hb

/-- The weighted_order of the sum of two formal power series
 is the minimum of their orders if their orders differ. -/
theorem weightedOrder_add_of_weightedOrder_ne (h : f.weightedOrder w ≠ g.weightedOrder w) :
    weightedOrder w (f + g) = weightedOrder w f ⊓ weightedOrder w g := by
  refine le_antisymm ?_ (min_weightedOrder_le_add w)
  by_cases H₁ : f.weightedOrder w < g.weightedOrder w
  · simp only [le_inf_iff, weightedOrder_add_of_weightedOrder_lt.aux w H₁]
    exact ⟨le_rfl, le_of_lt H₁⟩
  · by_cases H₂ : g.weightedOrder w < f.weightedOrder w
    · simp only [add_comm f g, le_inf_iff, weightedOrder_add_of_weightedOrder_lt.aux w H₂]
      exact ⟨le_of_lt H₂, le_rfl⟩
    · exact absurd (le_antisymm (not_lt.1 H₂) (not_lt.1 H₁)) h

/-- The weighted_order of the product of two formal power series
 is at least the sum of their orders. -/
theorem le_weightedOrder_mul :
    f.weightedOrder w + g.weightedOrder w ≤ weightedOrder w (f * g) := by
  classical
  apply le_weightedOrder
  intro d hd
  rw [coeff_mul, Finset.sum_eq_zero]
  rintro ⟨i, j⟩ hij
  by_cases hi : weight w i < f.weightedOrder w
  · rw [coeff_eq_zero_of_lt_weightedOrder w hi, MulZeroClass.zero_mul]
  · by_cases hj : weight w j < g.weightedOrder w
    · rw [coeff_eq_zero_of_lt_weightedOrder w hj, MulZeroClass.mul_zero]
    · rw [not_lt] at hi hj
      simp only [Finset.mem_antidiagonal] at hij
      exfalso
      apply ne_of_lt (lt_of_lt_of_le hd <| add_le_add hi hj)
      rw [← hij, map_add, Nat.cast_add]

alias weightedOrder_mul_ge := le_weightedOrder_mul

section Ring

variable {R : Type*} [Ring R] {f g : MvPowerSeries σ R}

theorem coeff_mul_left_one_sub_of_lt_weightedOrder
    {d : σ →₀ ℕ} (h : (weight w d) < g.weightedOrder w) :
    coeff R d (f * (1 - g)) = coeff R d f := by
  simp only [mul_sub, mul_one, _root_.map_sub, sub_eq_self]
  apply coeff_eq_zero_of_lt_weightedOrder w
  exact lt_of_lt_of_le (lt_of_lt_of_le h le_add_self) (le_weightedOrder_mul w)

theorem coeff_mul_right_one_sub_of_lt_weightedOrder
    {d : σ →₀ ℕ} (h : (weight w d) < g.weightedOrder w) :
    coeff R d ((1 - g) * f) = coeff R d f := by
  simp only [sub_mul, one_mul, _root_.map_sub, sub_eq_self]
  apply coeff_eq_zero_of_lt_weightedOrder w
  apply lt_of_lt_of_le (lt_of_lt_of_le h le_self_add) (le_weightedOrder_mul w)

theorem coeff_mul_prod_one_sub_of_lt_weightedOrder {R ι : Type*} [CommRing R] (d : σ →₀ ℕ)
    (s : Finset ι) (f : MvPowerSeries σ R) (g : ι → MvPowerSeries σ R) :
    (∀ i ∈ s, (weight w d) < weightedOrder w (g i)) →
      coeff R d (f * ∏ i ∈ s, (1 - g i)) = coeff R d f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [imp_true_iff, Finset.prod_empty, mul_one, eq_self_iff_true]
  | @insert a s ha ih =>
    intro h
    simp only [Finset.mem_insert, forall_eq_or_imp] at h
    rw [Finset.prod_insert ha, ← mul_assoc, mul_right_comm,
      coeff_mul_left_one_sub_of_lt_weightedOrder w h.1, ih h.2]

end Ring

end WeightedOrder

section Order

variable {f g : MvPowerSeries σ R}

theorem eq_zero_iff_forall_coeff_eq_zero_and :
    f = 0 ↔ (∀ d : σ →₀ ℕ, coeff R d f = 0) :=
  MvPowerSeries.ext_iff

theorem ne_zero_iff_exists_coeff_ne_zero_and_degree :
    f ≠ 0 ↔ (∃ n : ℕ, ∃ d : σ →₀ ℕ, coeff R d f ≠ 0 ∧ degree d = n) := by
  simp_rw [degree_eq_weight_one]
  exact ne_zero_iff_exists_coeff_ne_zero_and_weight (fun _ => 1)

/-- The order of a mv_power_series -/
def order (f : MvPowerSeries σ R) : ℕ∞ := weightedOrder (fun _ => 1) f

@[simp]
theorem order_zero : (0 : MvPowerSeries σ R).order = ⊤ :=
  weightedOrder_zero _

theorem ne_zero_iff_order_finite : f ≠ 0 ↔ f.order.toNat = f.order :=
  ne_zero_iff_weightedOrder_finite 1

/-- The `0` power series is the unique power series with infinite order. -/
@[simp] theorem order_eq_top_iff : f.order = ⊤ ↔ f = 0 :=
  weightedOrder_eq_top_iff _

/-- If the order of a formal power series `f` is finite,
then some coefficient of degree the order of `f` is nonzero. -/
theorem exists_coeff_ne_zero_and_order (h : f.order.toNat = f.order) :
    ∃ d : σ →₀ ℕ, coeff R d f ≠ 0 ∧ degree d = f.order := by
  simp_rw [degree_eq_weight_one]
  exact exists_coeff_ne_zero_and_weightedOrder _ h

/-- If the `d`th coefficient of a formal power series is nonzero,
then the order of the power series is less than or equal to `degree d`. -/
theorem order_le {d : σ →₀ ℕ} (h : coeff R d f ≠ 0) : f.order ≤ degree d := by
  rw [degree_eq_weight_one]
  exact weightedOrder_le _ h

/-- The `n`th coefficient of a formal power series is `0` if `n` is strictly
smaller than the order of the power series. -/
theorem coeff_of_lt_order {d : σ →₀ ℕ} (h : degree d < f.order) :
    coeff R d f = 0 := by
  rw [degree_eq_weight_one] at h
  exact coeff_eq_zero_of_lt_weightedOrder _ h

/-- The order of a formal power series is at least `n` if
the `d`th coefficient is `0` for all `d` such that `degree d < n`. -/
theorem nat_le_order {n : ℕ} (h : ∀ d, degree d < n → coeff R d f = 0) :
    n ≤ f.order := by
  simp_rw [degree_eq_weight_one] at h
  exact nat_le_weightedOrder _ h

/-- The order of a formal power series is at least `n` if
the `d`th coefficient is `0` for all `d` such that `degree d < n`. -/
theorem le_order {n : ℕ∞} (h : ∀ d : σ →₀ ℕ, degree d < n → coeff R d f = 0) :
    n ≤ f.order := by
  simp_rw [degree_eq_weight_one] at h
  exact le_weightedOrder _ h

/-- The order of a formal power series is exactly `n` some coefficient
of degree `n` is nonzero,
and the `d`th coefficient is `0` for all `d` such that `degree d < n`. -/
theorem order_eq_nat {n : ℕ} :
    f.order = n ↔
      (∃ d, coeff R d f ≠ 0 ∧ degree d = n) ∧ ∀ d, degree d < n → coeff R d f = 0 := by
  simp_rw [degree_eq_weight_one]
  exact weightedOrder_eq_nat _

/-- The order of the monomial `a*X^d` is infinite if `a = 0` and `degree d` otherwise. -/
theorem order_monomial {d : σ →₀ ℕ} {a : R} [Decidable (a = 0)] :
    order (monomial R d a) = if a = 0 then (⊤ : ℕ∞) else ↑(degree d) := by
  rw [degree_eq_weight_one]
  exact weightedOrder_monomial _

/-- The order of the monomial `a*X^n` is `n` if `a ≠ 0`. -/
theorem order_monomial_of_ne_zero {d : σ →₀ ℕ} {a : R} (h : a ≠ 0) :
    order (monomial R d a) = degree d := by
  rw [degree_eq_weight_one]
  exact weightedOrder_monomial_of_ne_zero _ h

/-- The order of the sum of two formal power series
 is at least the minimum of their orders. -/
theorem min_order_le_add : min f.order g.order ≤ (f + g).order :=
  min_weightedOrder_le_add _

/-- The order of the sum of two formal power series
 is the minimum of their orders if their orders differ. -/
theorem order_add_of_order_ne (h : f.order ≠ g.order) :
    order (f + g) = order f ⊓ order g :=
  weightedOrder_add_of_weightedOrder_ne _ h

/-- The order of the product of two formal power series
 is at least the sum of their orders. -/
theorem le_order_mul : f.order + g.order ≤ order (f * g) :=
  le_weightedOrder_mul _

alias order_mul_ge := le_order_mul

section Ring

variable {R : Type*} [Ring R] {f g : MvPowerSeries σ R}

theorem coeff_mul_left_one_sub_of_lt_order (d : σ →₀ ℕ) (h : degree d < g.order) :
    coeff R d (f * (1 - g)) = coeff R d f := by
  rw [degree_eq_weight_one] at h
  exact coeff_mul_left_one_sub_of_lt_weightedOrder _ h

theorem coeff_mul_right_one_sub_of_lt_order (d : σ →₀ ℕ) (h : degree d < g.order) :
    coeff R d ((1 - g) * f) = coeff R d f := by
  rw [degree_eq_weight_one] at h
  exact coeff_mul_right_one_sub_of_lt_weightedOrder _ h

theorem coeff_mul_prod_one_sub_of_lt_order {R ι : Type*} [CommRing R] (d : σ →₀ ℕ) (s : Finset ι)
    (f : MvPowerSeries σ R) (g : ι → MvPowerSeries σ R) :
    (∀ i ∈ s, degree d < order (g i)) → coeff R d (f * ∏ i ∈ s, (1 - g i)) = coeff R d f := by
  rw [degree_eq_weight_one]
  exact coeff_mul_prod_one_sub_of_lt_weightedOrder _ d s f g

end Ring

end Order

section HomogeneousComponent

variable (w : σ → ℕ)

/-- The weighted homogeneous components of an `MvPowerSeries f`. -/
def weightedHomogeneousComponent (p : ℕ) : MvPowerSeries σ R →ₗ[R] MvPowerSeries σ R
    where
  toFun f d := if weight w d = p then coeff R d f else 0
  map_add' f g := by
    ext d
    simp only [map_add, coeff_apply, Pi.add_apply]
    split_ifs with h
    · rfl
    · rw [add_zero]
  map_smul' a f := by
    ext d
    simp only [id_eq, eq_mpr_eq_cast, AddHom.toFun_eq_coe, AddHom.coe_mk, map_smul,
      smul_eq_mul, RingHom.id_apply, coeff_apply, mul_ite, MulZeroClass.mul_zero]

theorem coeff_weightedHomogeneousComponent (p : ℕ) (d : σ →₀ ℕ) (f : MvPowerSeries σ R) :
    coeff R d (weightedHomogeneousComponent w p f) =
      if weight w d = p then coeff R d f else 0 :=
  rfl

/-- The homogeneous components of an `MvPowerSeries` -/
def homogeneousComponent (p : ℕ) : MvPowerSeries σ R →ₗ[R] MvPowerSeries σ R :=
  weightedHomogeneousComponent 1 p

theorem coeff_homogeneousComponent (p : ℕ) (d : σ →₀ ℕ) (f : MvPowerSeries σ R) :
    coeff R d (homogeneousComponent p f) =
      if degree d = p then coeff R d f else 0 := by
  rw [degree_eq_weight_one]
  exact coeff_weightedHomogeneousComponent 1 p d f

end HomogeneousComponent

end

end MvPowerSeries
