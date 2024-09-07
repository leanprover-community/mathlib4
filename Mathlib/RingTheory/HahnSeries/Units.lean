/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Scott Carnahan
-/
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# Invertibility of Hahn Series
For any element of strictly positive order in a Hahn series ring over `R`, we define an `R`-algebra
homomorphism from the ring of formal power series over `R`.  We use this homomorphism to show that
This theory is applied to characterize invertible Hahn series whose coefficients are in a
commutative domain.

## Main Definitions
  * A `HahnSeries.SummableFamily` is a family of Hahn series such that the union of the supports
  is partially well-ordered and only finitely many are nonzero at any given coefficient. Note that
  this is different from `Summable` in the valuation topology, because there are topologically
  summable families that do not satisfy the axioms of `HahnSeries.SummableFamily`, and formally
  summable families whose sums do not converge topologically.
  * The formal sum, `HahnSeries.SummableFamily.hsum` can be bundled as a `LinearMap` via
  `HahnSeries.SummableFamily.lsum`.

## Main results
  * If `R` is a commutative domain, and `Γ` is a linearly ordered additive commutative group, then
  a Hahn series is a unit if and only if its leading term is a unit in `R`.

## TODO
  * Ring hom from `MVPowerSeries`.

## Main results

  * `isUnit_of_isUnit_leadingCoeff` : A Hahn Series with invertible leading coefficient is
    invertible.
  * `isUnit_iff` : If the coefficient ring is a domain, then any invertible Hahn series has
    invertible leading coefficient.
  * A HahnSeries module structure on summable families.

## References
- [J. van der Hoeven, *Operators on Generalized Power Series*][van_der_hoeven]
-/

open Finset Function

open Pointwise

noncomputable section

variable {Γ Γ' R V α β : Type*}

namespace HahnSeries

namespace SummableFamily

section powers

theorem support_pow_subset_closure [OrderedCancelAddCommMonoid Γ] [Semiring R] (x : HahnSeries Γ R)
    (n : ℕ) : support (x ^ n) ⊆ AddSubmonoid.closure (support x) := by
  induction n with
  | zero =>
    intro g hn
    rw [pow_zero] at hn
    rw [eq_of_mem_support_single hn, SetLike.mem_coe]
    exact AddSubmonoid.zero_mem _
  | succ n ih =>
    intro g hn
    obtain ⟨i, hi, j, hj, rfl⟩ := support_mul_subset_add_support hn
    exact SetLike.mem_coe.2 (AddSubmonoid.add_mem _ (ih hi) (AddSubmonoid.subset_closure hj))

theorem isPWO_iUnion_support_powers [LinearOrderedCancelAddCommMonoid Γ] [Semiring R]
    (x : HahnSeries Γ R) (hx : 0 ≤ x.order) :
    (⋃ n : ℕ, (x ^ n).support).IsPWO :=
  (x.isPWO_support'.addSubmonoid_closure
    fun _ hg => le_trans hx (order_le_of_coeff_ne_zero (Function.mem_support.mp hg))).mono
    (Set.iUnion_subset fun n => support_pow_subset_closure x n)

theorem powers_co_support_zero [OrderedCancelAddCommMonoid Γ] [Semiring R] (g : Γ) :
    {a | ¬((0 : HahnSeries Γ R) ^ a).coeff g = 0} ⊆ {0} := by
  simp_all only [Set.subset_singleton_iff, Set.mem_setOf_eq]
  intro n hn
  by_contra h'
  simp_all only [ne_eq, not_false_eq_true, zero_pow, zero_coeff, not_true_eq_false]

variable [LinearOrderedCancelAddCommMonoid Γ] [CommRing R]

theorem support_smul_MVpow_subset_closure {Γ} {R} [OrderedCancelAddCommMonoid Γ] [CommSemiring R]
    (σ : Type*) [Fintype σ] (φ : MvPowerSeries σ R) (x : σ →₀ HahnSeries Γ R) (n : σ →₀ ℕ) :
    support (MvPowerSeries.coeff R n φ • ∏ i, ((x i) ^ (n i) : HahnSeries Γ R)) ⊆
      AddSubmonoid.closure (⋃ i : σ, (x i).support) := by
  refine (Function.support_const_smul_subset (MvPowerSeries.coeff R n φ)
    (∏ i, x i ^ n i).coeff).trans (Finset.cons_induction ?_ ?_ univ)
  · rw [prod_empty, ← single_zero_one]
    have h₂ : 0 ∈ AddSubmonoid.closure (⋃ i, (x i).support) := by
      exact AddSubmonoid.zero_mem (AddSubmonoid.closure (⋃ i, (x i).support))
    intro g hg
    simp_all
  · intro i _ _ hx
    rw [prod_cons]
    have hi : (x i ^ n i).support ⊆ AddSubmonoid.closure (⋃ i, (x i).support) :=
      (support_pow_subset_closure (x i) (n i)).trans <| AddSubmonoid.closure_mono <|
        Set.subset_iUnion_of_subset i fun ⦃a⦄ a ↦ a
    exact (support_mul_subset_add_support (x := x i ^ n i)).trans (AddSubmonoid.add_subset hi hx)

lemma supp_eq_univ_of_pos' (σ : Type*) (y : σ →₀ HahnSeries Γ R)
    (hy : ∀ i : σ, 0 < (y i).order) : y.support = Set.univ (α := σ) := by
  have hy₁ : ∀ i : σ, y i ≠ 0 := fun i => ne_zero_of_order_ne (ne_of_gt (hy i))
  exact Set.eq_univ_of_univ_subset fun i _ => by simp_all

/-- A finsupp whose every element has positive order has fintype source. -/
def Fintype_of_pos_order (σ : Type*) (y : σ →₀ HahnSeries Γ R)
    (hy : ∀ i : σ, 0 < (y i).order) : Fintype σ := by
  refine Set.fintypeOfFiniteUniv ?_
  rw [← supp_eq_univ_of_pos' σ y hy]
  exact finite_toSet y.support

theorem isPWO_iUnion_support_MVpow' (σ : Type*) (φ : MvPowerSeries σ R) (x : σ →₀ HahnSeries Γ R)
    (hx : ∀ i : σ, 0 < (x i).order) :
    letI : Fintype σ := Fintype_of_pos_order σ x hx
    (⋃ n : σ →₀ ℕ, (MvPowerSeries.coeff R n φ • ∏ i, (x i) ^ (n i)).support).IsPWO := by
  letI : Fintype σ := Fintype_of_pos_order σ x hx
  refine Set.IsPWO.mono ?_ (Set.iUnion_subset fun n => support_smul_MVpow_subset_closure σ φ x n)
  refine Set.IsPWO.addSubmonoid_closure (fun g hg => ?_) ?_
  · simp only [Set.mem_iUnion, mem_support, ne_eq] at hg
    obtain ⟨i, hi⟩ := hg
    exact (le_of_lt (hx i)).trans (order_le_of_coeff_ne_zero hi)
  · have h : ⋃ i, (x i).support =
        (⋃ i ∈ x.support, (x i).support) ∪ (⋃ i ∉ x.support, (x i).support) := by
      classical
      simp_rw [← Set.iUnion_ite, ite_id (x _).support]
    rw [h, Set.isPWO_union]
    refine ⟨(isPWO_bUnion x.support).mpr fun i _ ↦ isPWO_support (x i), ?_⟩
    have h : (⋃ i, ⋃ (_ : i ∉ x.support), (x i).support) = ∅ := by
      simp_all only [Finsupp.mem_support_iff, ne_eq, not_not, support_zero, Set.iUnion_empty,
        Set.union_empty]
    exact h ▸ Set.isPWO_empty

theorem pow_finite_co_support {x : HahnSeries Γ R} (hx : 0 < x.orderTop) (g : Γ) :
    Set.Finite {a | ((fun n ↦ x ^ n) a).coeff g ≠ 0} := by
  have hpwo : Set.IsPWO (⋃ n, support (x ^ n)) :=
    isPWO_iUnion_support_powers x (zero_le_orderTop_iff.mp <| le_of_lt hx)
  by_cases hox : x = 0
  · exact hox ▸ Set.Finite.subset (Set.finite_singleton 0) (powers_co_support_zero g)
  by_cases hg : g ∈ ⋃ n : ℕ, { g | (x ^ n).coeff g ≠ 0 }
  swap; · exact Set.finite_empty.subset fun n hn => hg (Set.mem_iUnion.2 ⟨n, hn⟩)
  apply hpwo.isWF.induction hg
  intro y ys hy
  refine
    ((((addAntidiagonal x.isPWO_support hpwo y).finite_toSet.biUnion fun ij hij =>
                  hy ij.snd ?_ ?_).image
              Nat.succ).union
          (Set.finite_singleton 0)).subset
      ?_
  · exact (mem_addAntidiagonal.1 (mem_coe.1 hij)).2.1
  · obtain ⟨hi, _, rfl⟩ := mem_addAntidiagonal.1 (mem_coe.1 hij)
    exact lt_add_of_pos_left ij.2 <| lt_of_lt_of_le ((zero_lt_orderTop_iff hox).mp hx) <|
      order_le_of_coeff_ne_zero <| Function.mem_support.mp hi
  · rintro (_ | n) hn
    · exact Set.mem_union_right _ (Set.mem_singleton 0)
    · obtain ⟨i, hi, j, hj, rfl⟩ := support_mul_subset_add_support hn
      refine Set.mem_union_left _ ⟨n, Set.mem_iUnion.2 ⟨⟨j, i⟩, Set.mem_iUnion.2 ⟨?_, hi⟩⟩, rfl⟩
      simp only [mem_coe, mem_addAntidiagonal, mem_support, ne_eq, Set.mem_iUnion]
      exact ⟨hj, ⟨n, hi⟩, add_comm j i⟩

/-! Use PiFamily and pi_finite_co_support
theorem pi_power_finite_co_support {σ : Type*} (y : σ →₀ HahnSeries Γ R)
    (hy : ∀ i, 0 < (y i).order) (g : Γ) :
    letI : Fintype σ := Fintype_of_pos_order σ y hy
    {a | ((fun (n : σ →₀ ℕ) => ∏ i, y i ^ n i) a).coeff g ≠ 0}.Finite := by
  letI : Fintype σ := Fintype_of_pos_order σ y hy

  induction (univ (α := σ)) using cons_induction with
  | empty =>
    simp_rw [prod_empty]
    sorry
  | cons => sorry

/-- A summable family of Hahn series given by substituting the multivariable power series generators
into positive order Hahn series.-/
def mvPowerSeriesFamily {σ : Type*} (φ : MvPowerSeries σ R) (y : σ →₀ HahnSeries Γ R)
    (hy : ∀ i, 0 < (y i).order) : SummableFamily Γ R (σ →₀ ℕ) where
  toFun n :=
    letI : Fintype σ := Fintype_of_pos_order σ y hy
    MvPowerSeries.coeff R n φ • ∏ i, y i ^ n i
  isPWO_iUnion_support' := isPWO_iUnion_support_MVpow' σ φ y (fun i => hy i)
  finite_co_support' g :=
    Set.Finite.subset (pi_power_finite_co_support y hy g) fun n hn hng => (by simp_all)
-/

variable {x : HahnSeries Γ R}

/-- Powers of an element of positive orderTop form a summable family. -/
@[simps]
def powers (hx : 0 < x.orderTop) : SummableFamily Γ R ℕ where
  toFun n := x ^ n
  isPWO_iUnion_support' := isPWO_iUnion_support_powers x (zero_le_orderTop_iff.mp <| le_of_lt hx)
  finite_co_support' g := pow_finite_co_support hx g

@[simp]
theorem coe_powers (hx : 0 < x.orderTop) : ⇑(powers hx) = HPow.hPow x :=
  rfl

theorem embDomain_succ_smul_powers (hx : 0 < x.orderTop) :
    (x • powers hx).embDomain ⟨Nat.succ, Nat.succ_injective⟩ =
      powers hx - ofFinsupp (Finsupp.single 0 1) := by
  apply SummableFamily.ext
  rintro (_ | n)
  · rw [embDomain_notin_range, sub_apply, powers_toFun, pow_zero, coe_ofFinsupp,
      Finsupp.single_eq_same, sub_self]
    rw [Set.mem_range, not_exists]
    exact Nat.succ_ne_zero
  · refine Eq.trans (embDomain_image _ ⟨Nat.succ, Nat.succ_injective⟩) ?_
    rw [smul_apply, powers_toFun, coe_sub, coe_powers, Pi.sub_apply, coe_ofFinsupp, pow_succ',
      Finsupp.single_eq_of_ne (Nat.zero_ne_add_one n), sub_zero, of_symm_smul_of_eq_mul]

theorem one_sub_self_mul_hsum_powers (hx : 0 < x.orderTop) : (1 - x) * (powers hx).hsum = 1 := by
  rw [← hsum_smul, sub_smul 1 x (powers hx), one_smul, hsum_sub, ←
    hsum_embDomain (x • powers hx) ⟨Nat.succ, Nat.succ_injective⟩, embDomain_succ_smul_powers]
  simp only [hsum_sub, hsum_ofFinsupp, id_eq, Finsupp.sum_single_index, sub_sub_cancel]

end powers

end SummableFamily

section Inversion

variable [LinearOrderedAddCommGroup Γ]

section CommRing

variable [CommRing R]

theorem one_minus_single_mul (x y : HahnSeries Γ R) (r : R) (hr : r * x.leadingCoeff = 1)
    (hxy : x = y + x.leadingTerm) : 1 - single (-order x) r * x = -(single (-x.order) r * y) := by
  nth_rw 2 [hxy]
  rw [mul_add, leadingTerm_eq, single_mul_single, ← leadingCoeff_eq, hr, neg_add_cancel,
    sub_add_eq_sub_sub_swap, sub_eq_neg_self, sub_eq_zero_of_eq]
  exact rfl

theorem unit_aux (x : HahnSeries Γ R) {r : R} (hr : r * x.leadingCoeff = 1) :
    0 < (1 - single (-x.order) r * x).orderTop := by
  let y := (x - x.leadingTerm)
  by_cases hy : y = 0
  · have hrx : (single (-order x)) r * x = 1 := by
      nth_rw 2 [eq_of_sub_eq_zero hy]
      simp only [leadingTerm_eq, single_mul_single, neg_add_cancel, hr, ← leadingCoeff_eq]
      exact rfl
    simp only [hrx, sub_self, orderTop_zero, WithTop.zero_lt_top]
  have hr' : ∀ (s : R), r * s = 0 → s = 0 :=
    fun s hs => by rw [← one_mul s, ← hr, mul_right_comm, hs, zero_mul]
  have hy' : 0 < (single (-x.order) r * y).order := by
    rw [(order_mul_single_of_nonzero_divisor hr' hy), lt_neg_add_iff_lt]
    exact order_lt_add_single_support_order (sub_add_cancel x x.leadingTerm).symm hy
  simp only [one_minus_single_mul x y r hr (sub_add_cancel x x.leadingTerm).symm, orderTop_neg]
  exact zero_lt_orderTop_of_order hy'

theorem isUnit_of_isUnit_leadingCoeff {x : HahnSeries Γ R} (hx : IsUnit x.leadingCoeff) :
    IsUnit x := by
  let ⟨⟨u, i, ui, iu⟩, h⟩ := hx
  rw [Units.val_mk] at h
  rw [h] at iu
  have h' := SummableFamily.one_sub_self_mul_hsum_powers (unit_aux x iu)
  rw [sub_sub_cancel] at h'
  exact isUnit_of_mul_isUnit_right (isUnit_of_mul_eq_one _ _ h')

theorem isUnit_iff [IsDomain R] {x : HahnSeries Γ R} :
    IsUnit x ↔ IsUnit (x.leadingCoeff) := by
  refine { mp := ?mp, mpr := isUnit_of_isUnit_leadingCoeff }
  rintro ⟨⟨u, i, ui, iu⟩, rfl⟩
  refine
    isUnit_of_mul_eq_one (u.leadingCoeff) (i.leadingCoeff)
      ((mul_coeff_order_add_order u i).symm.trans ?_)
  rw [ui, one_coeff, if_pos]
  rw [← order_mul (left_ne_zero_of_mul_eq_one ui) (right_ne_zero_of_mul_eq_one ui), ui, order_one]

end CommRing

open Classical in
instance instField [Field R] : Field (HahnSeries Γ R) where
  __ : IsDomain (HahnSeries Γ R) := inferInstance
  inv x :=
    if x0 : x = 0 then 0
    else
      (single (-x.order)) (x.leadingCoeff)⁻¹ *
        (SummableFamily.powers (unit_aux x (inv_mul_cancel₀ (leadingCoeff_ne_iff.mpr x0)))).hsum
  inv_zero := dif_pos rfl
  mul_inv_cancel x x0 := (congr rfl (dif_neg x0)).trans <| by
    have h :=
      SummableFamily.one_sub_self_mul_hsum_powers
        (unit_aux x (inv_mul_cancel₀ (leadingCoeff_ne_iff.mpr x0)))
    rw [sub_sub_cancel] at h
    rw [← mul_assoc, mul_comm x, h]
  nnqsmul := _
  nnqsmul_def := fun q a => rfl
  qsmul := _
  qsmul_def := fun q a => rfl

end Inversion

end HahnSeries
