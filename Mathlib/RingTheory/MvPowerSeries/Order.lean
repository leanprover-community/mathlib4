/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos Fernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos Fernandez
-/


import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Finsupp.Weight

namespace MvPowerSeries

noncomputable section

open ENat WithTop Finsupp

open scoped BigOperators

variable {σ R : Type*} [Semiring R]

section WeightedOrder

variable (w : σ → ℕ) (f : MvPowerSeries σ R)

theorem _root_.Finsupp.finite_of_weight_le [Finite σ]
    (hw : ∀ x, w x ≠ 0) (n : ℕ) :
    {d : σ →₀ ℕ | weight w d ≤ n}.Finite := by
  classical
  set fg := Finset.antidiagonal (Finsupp.equivFunOnFinite.symm (Function.const σ n)) with hfg
  suffices {d : σ →₀ ℕ | weight w d ≤ n} ⊆ ↑(fg.image fun uv => uv.fst) by
    apply Set.Finite.subset _ this
    apply Finset.finite_toSet
  intro d hd
  rw [hfg]
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe,
    Finset.mem_antidiagonal, Prod.exists, exists_and_right, exists_eq_right]
  use Finsupp.equivFunOnFinite.symm (Function.const σ n) - d
  ext x
  simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
    Finsupp.equivFunOnFinite_symm_apply_toFun, Function.const_apply]
  rw [add_comm]
  apply Nat.sub_add_cancel
  apply le_trans (le_weight w (hw x) d)
  simpa only [Set.mem_setOf_eq] using hd

/-
/-- The weight of a monomial -/
def weight : (σ →₀ ℕ) →+ ℕ where
  toFun d      := d.sum fun x y => w x * y
  map_zero'    := Finsupp.sum_zero_index
  map_add' x y := by
    dsimp only
    rw [Finsupp.sum_add_index']
    · intro i; rw [MulZeroClass.mul_zero]
    · intro i m n; rw [mul_add]

theorem weight_apply (d : σ →₀ ℕ) : weight w d = d.sum fun x => Mul.mul (w x) := by
  simp only [weight]; rfl

theorem le_weight (x : σ) (hx : w x ≠ 0) (d : σ →₀ ℕ) : d x ≤ weight w d := by
  classical
  simp only [weight_apply, Finsupp.sum]
  by_cases hxd : x ∈ d.support
  · rw [Finset.sum_eq_add_sum_diff_singleton hxd]
    refine' le_trans _ (Nat.le_add_right _ _)
    exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hx)
  simp only [Finsupp.mem_support_iff, Classical.not_not] at hxd
  rw [hxd]
  apply zero_le

-/

theorem ne_zero_iff_exists_coeff_ne_zero_of_weight
    (f : MvPowerSeries σ R):
    f ≠ 0 ↔ (∃ n : ℕ, ∃ d : σ →₀ ℕ, weight w d = n ∧ coeff R d f ≠ 0) := by
  refine not_iff_not.mp ?_
  push_neg
  refine ⟨?_, fun h ↦ MvPowerSeries.ext_iff.mpr (fun d ↦ h _ d rfl)⟩
  rintro rfl n d _
  exact coeff_zero _

/-- The weighted order of a mv_power_series -/
def weightedOrder (f : MvPowerSeries σ R) : ℕ∞ := by
  classical
  exact dite (f = 0) (fun _ => ⊤) fun h =>
    Nat.find ((ne_zero_iff_exists_coeff_ne_zero_of_weight w f).mp h)

@[simp] theorem weightedOrder_zero : (0 : MvPowerSeries σ R).weightedOrder w = ⊤ := by
  rw [weightedOrder, dif_pos rfl]

theorem weightedOrder_finite_iff_ne_zero :
    ↑(toNat (f.weightedOrder w)) = f.weightedOrder w ↔ f ≠ 0 := by
  simp only [weightedOrder]
  constructor
  · split_ifs with h <;> intro H
    · exfalso
      apply ENat.coe_ne_top _ H
    · exact h
  · intro h
    simp only [h, not_false_iff, dif_neg, toNat_coe]

/-- If the order of a formal power series `f` is finite,
then some coefficient of weight equal to the order of `f` is nonzero.-/
theorem exists_coeff_ne_zero_of_weightedOrder
    (h : ↑(toNat (f.weightedOrder w)) = f.weightedOrder w) :
    ∃ d, ↑(weight w d) = f.weightedOrder w ∧ coeff R d f ≠ 0 := by
  classical
  simp_rw [weightedOrder, dif_neg ((weightedOrder_finite_iff_ne_zero _ f).mp h), Nat.cast_inj]
  generalize_proofs h1
  exact Nat.find_spec h1

/-- If the `d`th coefficient of a formal power series is nonzero,
then the weighted order of the power series is less than or equal to `weight d w`.-/
theorem weightedOrder_le {d : σ →₀ ℕ} (h : coeff R d f ≠ 0) :
    f.weightedOrder w ≤ weight w d := by
  classical
  rw [weightedOrder, dif_neg]
  · simp only [ne_eq, Nat.cast_le, Nat.find_le_iff]
    exact ⟨weight w d, le_rfl, d, rfl, h⟩
  · exact (f.ne_zero_iff_exists_coeff_ne_zero_of_weight w).mpr ⟨weight w d, d, rfl, h⟩

/-- The `n`th coefficient of a formal power series is `0` if `n` is strictly
smaller than the order of the power series.-/
theorem coeff_of_lt_weightedOrder {d : σ →₀ ℕ} (h : ↑(weight w d) < f.weightedOrder w) :
    coeff R d f = 0 := by
  contrapose! h; exact weightedOrder_le w f h

/-- The `0` power series is the unique power series with infinite order.-/
@[simp]
theorem weightedOrder_eq_top_iff {f : MvPowerSeries σ R} :
    f.weightedOrder w = ⊤ ↔ f = 0 := by
  constructor
  · intro h
    ext d
    rw [(coeff R d).map_zero, coeff_of_lt_weightedOrder w]
    rw [h]
    exact WithTop.coe_lt_top _
  · rintro rfl
    exact weightedOrder_zero w

/-- The order of a formal power series is at least `n` if
the `d`th coefficient is `0` for all `d` such that `weight w d < n`.-/
theorem nat_le_weightedOrder {f : MvPowerSeries σ R} {n : ℕ}
    (h : ∀ d, weight w d < n → coeff R d f = 0) : ↑n ≤ f.weightedOrder w := by
  by_contra H; rw [not_le] at H
  have : ↑(toNat (f.weightedOrder w)) = f.weightedOrder w := by
    rw [coe_toNat_eq_self]; exact ne_top_of_lt H
  obtain ⟨d, hd, hfd⟩ := exists_coeff_ne_zero_of_weightedOrder w f this
  rw [← hd, Nat.cast_lt] at H
  exact hfd (h d H)

/-- The order of a formal power series is at least `n` if
the `d`th coefficient is `0` for all `d` such that `weight w d < n`.-/
theorem le_weightedOrder {f : MvPowerSeries σ R} {n : ℕ∞}
    (h : ∀ d : σ →₀ ℕ, ↑(weight w d) < n → coeff R d f = 0) : n ≤ f.weightedOrder w := by
  cases n
  · rw [top_le_iff, weightedOrder_eq_top_iff]
    ext d; exact h d (coe_lt_top _)
  · apply nat_le_weightedOrder;
    simpa only [ENat.some_eq_coe, Nat.cast_lt] using h

/-- The order of a formal power series is exactly `n` if and only if some coefficient of weight `n`
is nonzero, and the `d`th coefficient is `0` for all `d` such that `weight w d < n`.-/
theorem weightedOrder_eq_nat {f : MvPowerSeries σ R} {n : ℕ} :
    f.weightedOrder w = n ↔
      (∃ d, weight w d = n ∧ coeff R d f ≠ 0) ∧ ∀ d, weight w d < n → coeff R d f = 0 := by
  classical
  rcases eq_or_ne f 0 with (rfl | hf)
  · simp only [weightedOrder_zero, ENat.top_ne_coe, map_zero, ne_eq, not_true, and_false,
      exists_false, implies_true, forall_const, and_true]
  · simp only [weightedOrder, dif_neg hf, ne_eq, Nat.cast_inj, Nat.find_eq_iff]
    apply and_congr_right'
    simp only [not_exists, not_and, Classical.not_not, imp_forall_iff]
    rw [forall_swap]
    apply forall_congr'
    intro d
    constructor
    · intro h hd
      exact h (weight w d) hd rfl
    · intro h m hm hd; rw [← hd] at hm; exact h hm

/-- The order of the sum of two formal power series is at least the minimum of their orders.-/
theorem le_weightedOrder_add (f g : MvPowerSeries σ R) :
    min (f.weightedOrder w) (g.weightedOrder w) ≤ (f + g).weightedOrder w := by
  apply le_weightedOrder w
  simp (config := { contextual := true }) only [coeff_of_lt_weightedOrder w, lt_min_iff, map_add,
    add_zero, eq_self_iff_true, imp_true_iff]

private theorem weightedOrder_add_of_weightedOrder_lt.aux {f g : MvPowerSeries σ R}
    (H : f.weightedOrder w < g.weightedOrder w) :
    (f + g).weightedOrder w = f.weightedOrder w := by
  obtain ⟨n, hn⟩ := ne_top_iff_exists.mp (ne_top_of_lt H)
  erw [← hn, weightedOrder_eq_nat]
  obtain ⟨d, hd, hd'⟩ := ((weightedOrder_eq_nat w).mp hn.symm).1
  constructor
  · use d; use hd
    rw [← hn, ← hd] at H
    rw [(coeff _ _).map_add, coeff_of_lt_weightedOrder w g H, add_zero]
    exact hd'
  · intro b hb
    suffices ↑(weight w b) < weightedOrder w f by
      rw [(coeff _ _).map_add, coeff_of_lt_weightedOrder w f this,
        coeff_of_lt_weightedOrder w g (lt_trans this H), add_zero]
    rw [← hn, ENat.some_eq_coe, Nat.cast_lt]
    exact hb

/-- The weighted_order of the sum of two formal power series
 is the minimum of their orders if their orders differ.-/
theorem weightedOrder_add_of_weightedOrder_eq {f g : MvPowerSeries σ R}
    (h : f.weightedOrder w ≠ g.weightedOrder w) :
    weightedOrder w (f + g) = weightedOrder w f ⊓ weightedOrder w g := by
  refine le_antisymm ?_ (le_weightedOrder_add w _ _)
  by_cases H₁ : f.weightedOrder w < g.weightedOrder w
  · simp only [le_inf_iff, weightedOrder_add_of_weightedOrder_lt.aux w H₁]
    exact ⟨le_rfl, le_of_lt H₁⟩
  · by_cases H₂ : g.weightedOrder w < f.weightedOrder w
    · simp only [add_comm f g, le_inf_iff, weightedOrder_add_of_weightedOrder_lt.aux w H₂]
      exact ⟨le_of_lt H₂, le_rfl⟩
    · exact absurd (le_antisymm (not_lt.1 H₂) (not_lt.1 H₁)) h

/-- The weighted_order of the product of two formal power series
 is at least the sum of their orders.-/
theorem weightedOrder_mul_ge [DecidableEq σ] (f g : MvPowerSeries σ R) :
    f.weightedOrder w + g.weightedOrder w ≤ weightedOrder w (f * g) := by
  apply le_weightedOrder
  intro d hd
  rw [coeff_mul, Finset.sum_eq_zero]
  rintro ⟨i, j⟩ hij
  by_cases hi : ↑(weight w i) < f.weightedOrder w
  · rw [coeff_of_lt_weightedOrder w f hi, MulZeroClass.zero_mul]
  · by_cases hj : ↑(weight w j) < g.weightedOrder w
    · rw [coeff_of_lt_weightedOrder w g hj, MulZeroClass.mul_zero]
    · rw [not_lt] at hi hj
      simp only [Finset.mem_antidiagonal] at hij
      exfalso
      apply ne_of_lt (lt_of_lt_of_le hd <| add_le_add hi hj)
      rw [← hij, map_add, Nat.cast_add]

/-- The weighted_order of the monomial `a*X^d` is infinite if `a = 0` and `weight w d` otherwise.-/
theorem weightedOrder_monomial (d : σ →₀ ℕ) (a : R) [Decidable (a = 0)] :
    weightedOrder w (monomial R d a) = if a = 0 then (⊤ : ℕ∞) else weight w d := by
  classical
  split_ifs with h
  · rw [h, weightedOrder_eq_top_iff, LinearMap.map_zero]
  · rw [weightedOrder_eq_nat]
    constructor
    · use d; simp only [coeff_monomial_same, eq_self_iff_true, ne_eq, true_and_iff]; exact h
    · intro b hb
      rw [coeff_monomial, if_neg]
      intro h
      simp only [h, lt_self_iff_false] at hb

/-- The order of the monomial `a*X^n` is `n` if `a ≠ 0`.-/
theorem weightedOrder_monomial_of_ne_zero (d : σ →₀ ℕ) (a : R) (h : a ≠ 0) :
    weightedOrder w (monomial R d a) = weight w d := by
  classical
  rw [weightedOrder_monomial, if_neg h]

/-- If `weight w d` is strictly smaller than the weighted_order of `g`, then the `d`th coefficient
of its product with any other power series is `0`. -/
theorem coeff_mul_of_lt_weightedOrder [DecidableEq σ] (f : MvPowerSeries σ R)
    {g : MvPowerSeries σ R} {d : σ →₀ ℕ} (h : ↑(weight w d) < g.weightedOrder w) :
    coeff R d (f * g) = 0 := by
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨i, j⟩ hij
  apply mul_eq_zero_of_right (coeff R i f)
  apply coeff_of_lt_weightedOrder w g (lt_of_le_of_lt _ h)
  simp only [Finset.mem_antidiagonal] at hij
  simp only [← hij, map_add, Nat.cast_add, self_le_add_left]

theorem coeff_mul_one_sub_of_lt_weightedOrder [DecidableEq σ] {R : Type _} [CommRing R]
    {f g : MvPowerSeries σ R} (d : σ →₀ ℕ) (h : ↑(weight w d) < g.weightedOrder w) :
    coeff R d (f * (1 - g)) = coeff R d f := by
  simp only [coeff_mul_of_lt_weightedOrder w f h, mul_sub, mul_one, _root_.map_sub, sub_zero]

theorem coeff_mul_prod_one_sub_of_lt_weightedOrder {R ι : Type _} [CommRing R] (d : σ →₀ ℕ)
    (s : Finset ι) (f : MvPowerSeries σ R) (g : ι → MvPowerSeries σ R) :
    (∀ i ∈ s, ↑(weight w d) < weightedOrder w (g i)) →
      coeff R d (f * ∏ i in s, (1 - g i)) = coeff R d f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [imp_true_iff, Finset.prod_empty, mul_one, eq_self_iff_true]
  | @insert a s ha ih =>
    intro h
    simp only [Finset.mem_insert, forall_eq_or_imp] at h
    rw [Finset.prod_insert ha, ← mul_assoc, mul_right_comm,
      coeff_mul_one_sub_of_lt_weightedOrder w _ h.1]
    exact ih h.2

end WeightedOrder

section Order

variable (f : MvPowerSeries σ R)

/-
/-- The degree of a monomial -/
def degree : (σ →₀ ℕ) →+ ℕ := weight fun _ => 1

theorem degree_apply (d : σ →₀ ℕ) : degree d = d.sum fun _ => id := by
  rw [degree, weight_apply]
  apply congr_arg
  ext _ n
  have h_eq : Mul.mul 1 n = 1 * n := by rfl -- Why is this needed?
  rw [h_eq, id_eq, one_mul]

theorem degree_eq_zero_iff (d : σ →₀ ℕ) : degree d = 0 ↔ d = 0 := by
  simp only [degree, weight, one_mul, AddMonoidHom.coe_mk, Finsupp.sum, Finset.sum_eq_zero_iff,
    Finsupp.mem_support_iff, _root_.not_imp_self, DFunLike.ext_iff, Finsupp.coe_zero, Pi.zero_apply,
    ZeroHom.coe_mk, Finset.sum_eq_zero_iff, Finsupp.mem_support_iff, ne_eq]

theorem le_degree (x : σ) (d : σ →₀ ℕ) : d x ≤ degree d := by
  convert le_weight _ x _ d
  exact NeZero.ne 1

-/

theorem _root_.Finsupp.finite_of_degree_le [Finite σ] (n : ℕ) :
    {f : σ →₀ ℕ | degree f ≤ n}.Finite := by
  simp_rw [degree_eq_weight_one]
  refine finite_of_weight_le (Function.const σ 1) ?_ n
  intro _
  simp only [Function.const_apply, ne_eq, one_ne_zero, not_false_eq_true]

theorem ne_zero_iff_exists_coeff_ne_zero_of_degree :
    f ≠ 0 ↔ (∃ n : ℕ, ∃ d : σ →₀ ℕ, degree d = n ∧ coeff R d f ≠ 0) := by
  simp_rw [degree_eq_weight_one]
  exact ne_zero_iff_exists_coeff_ne_zero_of_weight (fun _ => 1) f

/-- The order of a mv_power_series -/
def order (f : MvPowerSeries σ R) : ℕ∞ := weightedOrder (fun _ => 1) f

@[simp]
theorem order_zero : (0 : MvPowerSeries σ R).order = ⊤ :=
  weightedOrder_zero _

theorem order_finite_iff_ne_zero : ↑(toNat f.order) = f.order ↔ f ≠ 0 :=
  weightedOrder_finite_iff_ne_zero _ f

/-- If the order of a formal power series `f` is finite,
then some coefficient of degree the order of `f` is nonzero.-/
theorem exists_coeff_ne_zero_of_order (h : ↑(toNat f.order) = f.order) :
    ∃ d : σ →₀ ℕ, ↑(degree d) = f.order ∧ coeff R d f ≠ 0 := by
  simp_rw [degree_eq_weight_one]
  exact exists_coeff_ne_zero_of_weightedOrder _ f h

/-- If the `d`th coefficient of a formal power series is nonzero,
then the order of the power series is less than or equal to `degree d`. -/
theorem order_le (d : σ →₀ ℕ) (h : coeff R d f ≠ 0) : f.order ≤ degree d := by
  rw [degree_eq_weight_one]
  exact weightedOrder_le _ f h

/-- The `n`th coefficient of a formal power series is `0` if `n` is strictly
smaller than the order of the power series.-/
theorem coeff_of_lt_order (d : σ →₀ ℕ) (h : ↑(degree d) < f.order) :
    coeff R d f = 0 := by
  rw [degree_eq_weight_one] at h
  exact coeff_of_lt_weightedOrder _ f h

/-- The `0` power series is the unique power series with infinite order.-/
@[simp] theorem order_eq_top {f : MvPowerSeries σ R} :
    f.order = ⊤ ↔ f = 0 :=
  weightedOrder_eq_top_iff _

/-- The order of a formal power series is at least `n` if
the `d`th coefficient is `0` for all `d` such that `degree d < n`.-/
theorem nat_le_order {f : MvPowerSeries σ R} {n : ℕ}
    (h : ∀ d, degree d < n → coeff R d f = 0) : ↑n ≤ f.order := by
  simp_rw [degree_eq_weight_one] at h
  exact nat_le_weightedOrder _ h

/-- The order of a formal power series is at least `n` if
the `d`th coefficient is `0` for all `d` such that `degree d < n`.-/
theorem le_order {f : MvPowerSeries σ R} {n : ℕ∞}
    (h : ∀ d : σ →₀ ℕ, ↑(degree d) < n → coeff R d f = 0) : n ≤ f.order := by
  simp_rw [degree_eq_weight_one] at h
  exact le_weightedOrder _ h

/-- The order of a formal power series is exactly `n` some coefficient
of degree `n` is nonzero,
and the `d`th coefficient is `0` for all `d` such that `degree d < n`.-/
theorem order_eq_nat {f : MvPowerSeries σ R} {n : ℕ} :
    f.order = n ↔
      (∃ d, degree d = n ∧ coeff R d f ≠ 0) ∧
        ∀ d, degree d < n → coeff R d f = 0 := by
  simp_rw [degree_eq_weight_one]
  exact weightedOrder_eq_nat _

/-- The order of the sum of two formal power series
 is at least the minimum of their orders.-/
theorem le_order_add (f g : MvPowerSeries σ R) :
    min f.order g.order ≤ (f + g).order :=
  le_weightedOrder_add _ f g

/-- The order of the sum of two formal power series
 is the minimum of their orders if their orders differ.-/
theorem order_add_of_order_eq {f g : MvPowerSeries σ R} (h : f.order ≠ g.order) :
    order (f + g) = order f ⊓ order g :=
  weightedOrder_add_of_weightedOrder_eq _ h

/-- The order of the product of two formal power series
 is at least the sum of their orders.-/
theorem order_mul_ge [DecidableEq σ] (f g : MvPowerSeries σ R) : f.order + g.order ≤ order (f * g) :=
  weightedOrder_mul_ge _ f g

/-- The order of the monomial `a*X^d` is infinite if `a = 0` and `degree d` otherwise.-/
theorem order_monomial (d : σ →₀ ℕ) (a : R) [Decidable (a = 0)] :
    order (monomial R d a) = if a = 0 then (⊤ : ℕ∞) else degree d := by
  rw [degree_eq_weight_one]
  exact weightedOrder_monomial _ d a

/-- The order of the monomial `a*X^n` is `n` if `a ≠ 0`.-/
theorem order_monomial_of_ne_zero (d : σ →₀ ℕ) {a : R} (h : a ≠ 0) :
    order (monomial R d a) = degree d := by
  rw [degree_eq_weight_one]
  exact weightedOrder_monomial_of_ne_zero _ d a h

/-- If `degree d` is strictly smaller than the order of `g`, then the `d`th coefficient of its
product with any other power series is `0`. -/
theorem coeff_mul_of_lt_order [DecidableEq σ] {f g : MvPowerSeries σ R} {d : σ →₀ ℕ}
    (h : ↑(degree d) < g.order) : coeff R d (f * g) = 0 := by
  rw [degree_eq_weight_one] at h
  exact coeff_mul_of_lt_weightedOrder _ f h

theorem coeff_mul_one_sub_of_lt_order [DecidableEq σ] {R : Type _} [CommRing R]
    {f g : MvPowerSeries σ R} (d : σ →₀ ℕ) (h : ↑(degree d) < g.order) :
    coeff R d (f * (1 - g)) = coeff R d f := by
  rw [degree_eq_weight_one] at h
  exact coeff_mul_one_sub_of_lt_weightedOrder _ d h

theorem coeff_mul_prod_one_sub_of_lt_order {R ι : Type _} [CommRing R] (d : σ →₀ ℕ) (s : Finset ι)
    (f : MvPowerSeries σ R) (g : ι → MvPowerSeries σ R) :
    (∀ i ∈ s, ↑(degree d) < order (g i)) → coeff R d (f * ∏ i in s, (1 - g i)) = coeff R d f := by
  rw [degree_eq_weight_one]
  exact coeff_mul_prod_one_sub_of_lt_weightedOrder _ d s f g

end Order

section HomogeneousComponent

variable (w : σ → ℕ)

/-- Given an `mv_power_series f`, it returns the homogeneous component of degree `p`. -/
def homogeneousComponent (p : ℕ) : MvPowerSeries σ R →ₗ[R] MvPowerSeries σ R
    where
  toFun f d := ite (weight w d = p) (coeff R d f) 0
  map_add' f g := by
    classical
    ext d
    simp only [map_add, coeff_apply, Pi.add_apply]
    split_ifs with h
    · rfl
    · rw [add_zero]
  map_smul' a f := by
    ext d
    simp only [id_eq, eq_mpr_eq_cast, AddHom.toFun_eq_coe, AddHom.coe_mk, map_smul,
      smul_eq_mul, RingHom.id_apply, coeff_apply, mul_ite, MulZeroClass.mul_zero]



theorem coeff_homogeneousComponent (p : ℕ) (d : σ →₀ ℕ) (f : MvPowerSeries σ R) :
    coeff R d (homogeneousComponent w p f) = ite (weight w d = p) (coeff R d f) 0 :=
  rfl

end HomogeneousComponent

end

end MvPowerSeries
