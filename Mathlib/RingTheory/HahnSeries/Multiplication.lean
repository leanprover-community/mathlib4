/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Scott Carnahan
-/
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.GroupWithZero.Regular
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Finset.MulAntidiagonal
import Mathlib.Data.Finset.SMulAntidiagonal
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.RingTheory.HahnSeries.Addition

/-!
# Multiplicative properties of Hahn series
If `Γ` is ordered and `R` has zero, then `HahnSeries Γ R` consists of formal series over `Γ` with
coefficients in `R`, whose supports are partially well-ordered. This module introduces
multiplication and scalar multiplication on Hahn series. If `Γ` is an ordered cancellative
commutative additive monoid and `R` is a semiring, then we get a semiring structure on
`HahnSeries Γ R`. If `Γ` has an ordered vector-addition on `Γ'` and `R` has a scalar multiplication
on `V`, we define `HahnModule Γ' R V` as a type alias for `HahnSeries Γ' V` that admits a scalar
multiplication from `HahnSeries Γ R`. The scalar action of `R` on `HahnSeries Γ R` is compatible
with the action of `HahnSeries Γ R` on `HahnModule Γ' R V`.

## Main Definitions
* `HahnModule` is a type alias for `HahnSeries`, which we use for defining scalar multiplication
  of `HahnSeries Γ R` on `HahnModule Γ' R V` for an `R`-module `V`, where `Γ'` admits an ordered
  cancellative vector addition operation from `Γ`. The type alias allows us to avoid a potential
  instance diamond.
* `HahnModule.of` is the isomorphism from `HahnSeries Γ V` to `HahnModule Γ R V`.
* `HahnSeries.C` is the `constant term` ring homomorphism `R →+* HahnSeries Γ R`.
* `HahnSeries.embDomainRingHom` is the ring homomorphism `HahnSeries Γ R →+* HahnSeries Γ' R`
  induced by an order embedding `Γ ↪o Γ'`.

## Main results
* If `R` is a (commutative) (semi-)ring, then so is `HahnSeries Γ R`.
* If `V` is an `R`-module, then `HahnModule Γ' R V` is a `HahnSeries Γ R`-module.

## TODO
The following may be useful for composing vertex operators, but they seem to take time.
* rightTensorMap: `HahnModule Γ' R U ⊗[R] V →ₗ[R] HahnModule Γ' R (U ⊗[R] V)`
* leftTensorMap: `U ⊗[R] HahnModule Γ' R V →ₗ[R] HahnModule Γ' R (U ⊗[R] V)`

## References
- [J. van der Hoeven, *Operators on Generalized Power Series*][van_der_hoeven]
-/

open Finset Function Pointwise

noncomputable section

variable {Γ Γ' R S V : Type*}

namespace HahnSeries

variable [Zero Γ] [PartialOrder Γ]

instance [Zero R] [One R] : One (HahnSeries Γ R) where one := single 0 1
instance [Zero R] [NatCast R] : NatCast (HahnSeries Γ R) where natCast n := single 0 n
instance [Zero R] [IntCast R] : IntCast (HahnSeries Γ R) where intCast z := single 0 z
instance [Zero R] [NNRatCast R] : NNRatCast (HahnSeries Γ R) where nnratCast q := single 0 q
instance [Zero R] [RatCast R] : RatCast (HahnSeries Γ R) where ratCast q := single 0 q

open Classical in
@[simp]
theorem coeff_one [Zero R] [One R] {a : Γ} :
    (1 : HahnSeries Γ R).coeff a = if a = 0 then 1 else 0 :=
  coeff_single

@[deprecated (since := "2025-01-31")] alias one_coeff := coeff_one

@[simp] theorem single_zero_one [Zero R] [One R] : single (0 : Γ) (1 : R) = 1 := rfl
theorem single_zero_natCast [Zero R] [NatCast R] (n : ℕ) : single (0 : Γ) (n : R) = n := rfl
theorem single_zero_intCast [Zero R] [IntCast R] (z : ℤ) : single (0 : Γ) (z : R) = z := rfl
theorem single_zero_nnratCast [Zero R] [NNRatCast R] (q : ℚ≥0) : single (0 : Γ) (q : R) = q := rfl
theorem single_zero_ratCast [Zero R] [RatCast R] (q : ℚ) : single (0 : Γ) (q : R) = q := rfl

theorem single_zero_ofNat [Zero R] [NatCast R] (n : ℕ) [n.AtLeastTwo] :
    single (0 : Γ) (ofNat(n) : R) = ofNat(n) := rfl

@[simp]
theorem support_one [MulZeroOneClass R] [Nontrivial R] : support (1 : HahnSeries Γ R) = {0} :=
  support_single_of_ne one_ne_zero

@[simp]
theorem orderTop_one [MulZeroOneClass R] [Nontrivial R] : orderTop (1 : HahnSeries Γ R) = 0 := by
  rw [← single_zero_one, orderTop_single one_ne_zero, WithTop.coe_eq_zero]

@[simp]
theorem order_one [MulZeroOneClass R] : order (1 : HahnSeries Γ R) = 0 := by
  cases subsingleton_or_nontrivial R
  · rw [Subsingleton.elim (1 : HahnSeries Γ R) 0, order_zero]
  · exact order_single one_ne_zero

@[simp]
theorem leadingCoeff_one [MulZeroOneClass R] : (1 : HahnSeries Γ R).leadingCoeff = 1 := by
  simp [leadingCoeff_eq]

@[simp]
protected lemma map_one [MonoidWithZero R] [MonoidWithZero S] (f : R →*₀ S) :
    (1 : HahnSeries Γ R).map f = (1 : HahnSeries Γ S) :=
  HahnSeries.map_single (a := (0 : Γ)) f.toZeroHom |>.trans <| congrArg _ <| f.map_one

instance [AddCommMonoidWithOne R] : AddCommMonoidWithOne (HahnSeries Γ R) where
  natCast_zero := by simp [← single_zero_natCast]
  natCast_succ n := by simp [← single_zero_natCast]

instance [AddCommGroupWithOne R] : AddCommGroupWithOne (HahnSeries Γ R) where
  intCast_ofNat n := by simp [← single_zero_natCast, ← single_zero_intCast]
  intCast_negSucc n := by simp [← single_zero_natCast, ← single_zero_intCast]

end HahnSeries

/-- We introduce a type alias for `HahnSeries` in order to work with scalar multiplication by
series. If we wrote a `SMul (HahnSeries Γ R) (HahnSeries Γ V)` instance, then when
`V = HahnSeries Γ R`, we would have two different actions of `HahnSeries Γ R` on `HahnSeries Γ V`.
See `Mathlib/Algebra/Polynomial/Module.lean` for more discussion on this problem. -/
@[nolint unusedArguments]
def HahnModule (Γ R V : Type*) [PartialOrder Γ] [Zero V] [SMul R V] :=
  HahnSeries Γ V

namespace HahnModule

section

variable [PartialOrder Γ] [Zero V] [SMul R V]

/-- The casting function to the type synonym. -/
def of (R : Type*) [SMul R V] : HahnSeries Γ V ≃ HahnModule Γ R V :=
  Equiv.refl _

/-- Recursion principle to reduce a result about the synonym to the original type. -/
@[elab_as_elim]
def rec {motive : HahnModule Γ R V → Sort*} (h : ∀ x : HahnSeries Γ V, motive (of R x)) :
    ∀ x, motive x :=
  fun x => h <| (of R).symm x

@[ext]
theorem ext (x y : HahnModule Γ R V) (h : ((of R).symm x).coeff = ((of R).symm y).coeff) : x = y :=
  (of R).symm.injective <| HahnSeries.coeff_inj.1 h

end

section SMul

variable [PartialOrder Γ] [AddCommMonoid V] [SMul R V]

instance instAddCommMonoid : AddCommMonoid (HahnModule Γ R V) :=
  inferInstanceAs <| AddCommMonoid (HahnSeries Γ V)
instance instBaseSMul {V} [Monoid R] [AddMonoid V] [DistribMulAction R V] :
    SMul R (HahnModule Γ R V) :=
  inferInstanceAs <| SMul R (HahnSeries Γ V)

@[simp] theorem of_zero : of R (0 : HahnSeries Γ V) = 0 := rfl
@[simp] theorem of_add (x y : HahnSeries Γ V) : of R (x + y) = of R x + of R y := rfl

@[simp] theorem of_symm_zero : (of R).symm (0 : HahnModule Γ R V) = 0 := rfl
@[simp] theorem of_symm_add (x y : HahnModule Γ R V) :
    (of R).symm (x + y) = (of R).symm x + (of R).symm y := rfl

variable [PartialOrder Γ'] [VAdd Γ Γ'] [IsOrderedCancelVAdd Γ Γ']

instance instSMul [Zero R] : SMul (HahnSeries Γ R) (HahnModule Γ' R V) where
  smul x y := (of R) {
    coeff := fun a =>
      ∑ ij ∈ VAddAntidiagonal x.isPWO_support ((of R).symm y).isPWO_support a,
        x.coeff ij.fst • ((of R).symm y).coeff ij.snd
    isPWO_support' :=
        haveI h :
          { a : Γ' |
              (∑ ij ∈ VAddAntidiagonal x.isPWO_support ((of R).symm y).isPWO_support a,
                  x.coeff ij.fst • ((of R).symm y).coeff ij.snd) ≠ 0 } ⊆
            { a : Γ' | (VAddAntidiagonal x.isPWO_support
              ((of R).symm y).isPWO_support a).Nonempty } := by
          intro a ha
          contrapose! ha
          simp [not_nonempty_iff_eq_empty.1 ha]
        isPWO_support_vaddAntidiagonal.mono h }

theorem coeff_smul [Zero R] (x : HahnSeries Γ R) (y : HahnModule Γ' R V) (a : Γ') :
    ((of R).symm <| x • y).coeff a =
      ∑ ij ∈ VAddAntidiagonal x.isPWO_support ((of R).symm y).isPWO_support a,
        x.coeff ij.fst • ((of R).symm y).coeff ij.snd :=
  rfl

@[deprecated (since := "2025-01-31")] alias smul_coeff := coeff_smul

end SMul

section SMulZeroClass

variable [PartialOrder Γ] [PartialOrder Γ'] [VAdd Γ Γ'] [IsOrderedCancelVAdd Γ Γ']
  [AddCommMonoid V]

instance instBaseSMulZeroClass [SMulZeroClass R V] :
    SMulZeroClass R (HahnModule Γ R V) :=
  inferInstanceAs <| SMulZeroClass R (HahnSeries Γ V)

@[simp] theorem of_smul [SMulZeroClass R V] (r : R) (x : HahnSeries Γ V) :
    (of R) (r • x) = r • (of R) x := rfl
@[simp] theorem of_symm_smul [SMulZeroClass R V] (r : R) (x : HahnModule Γ R V) :
    (of R).symm (r • x) = r • (of R).symm x := rfl

variable [Zero R]

instance instSMulZeroClass [SMulZeroClass R V] :
    SMulZeroClass (HahnSeries Γ R) (HahnModule Γ' R V) where
  smul_zero x := by
    ext
    simp [coeff_smul]

theorem coeff_smul_right [SMulZeroClass R V] {x : HahnSeries Γ R} {y : HahnModule Γ' R V} {a : Γ'}
    {s : Set Γ'} (hs : s.IsPWO) (hys : ((of R).symm y).support ⊆ s) :
    ((of R).symm <| x • y).coeff a =
      ∑ ij ∈ VAddAntidiagonal x.isPWO_support hs a,
        x.coeff ij.fst • ((of R).symm y).coeff ij.snd := by
  classical
  rw [coeff_smul]
  apply sum_subset_zero_on_sdiff (vaddAntidiagonal_mono_right hys) _ fun _ _ => rfl
  intro b hb
  simp only [not_and, mem_sdiff, mem_vaddAntidiagonal, HahnSeries.mem_support, not_imp_not] at hb
  rw [hb.2 hb.1.1 hb.1.2.2, smul_zero]

@[deprecated (since := "2025-01-31")] alias smul_coeff_right := coeff_smul_right

theorem coeff_smul_left [SMulWithZero R V] {x : HahnSeries Γ R}
    {y : HahnModule Γ' R V} {a : Γ'} {s : Set Γ}
    (hs : s.IsPWO) (hxs : x.support ⊆ s) :
    ((of R).symm <| x • y).coeff a =
      ∑ ij ∈ VAddAntidiagonal hs ((of R).symm y).isPWO_support a,
        x.coeff ij.fst • ((of R).symm y).coeff ij.snd := by
  classical
  rw [coeff_smul]
  apply sum_subset_zero_on_sdiff (vaddAntidiagonal_mono_left hxs) _ fun _ _ => rfl
  intro b hb
  simp only [not_and', mem_sdiff, mem_vaddAntidiagonal, HahnSeries.mem_support, not_ne_iff] at hb
  rw [hb.2 ⟨hb.1.2.1, hb.1.2.2⟩, zero_smul]

@[deprecated (since := "2025-01-31")] alias smul_coeff_left := coeff_smul_left

end SMulZeroClass

section DistribSMul

variable [PartialOrder Γ] [PartialOrder Γ'] [VAdd Γ Γ'] [IsOrderedCancelVAdd Γ Γ'] [AddCommMonoid V]

theorem smul_add [Zero R] [DistribSMul R V] (x : HahnSeries Γ R) (y z : HahnModule Γ' R V) :
    x • (y + z) = x • y + x • z := by
  ext k
  have hwf := ((of R).symm y).isPWO_support.union ((of R).symm z).isPWO_support
  rw [coeff_smul_right hwf, of_symm_add]
  · simp_all only [HahnSeries.coeff_add', Pi.add_apply, of_symm_add]
    rw [coeff_smul_right hwf Set.subset_union_right,
      coeff_smul_right hwf Set.subset_union_left]
    simp_all [sum_add_distrib]
  · intro b
    simp_all only [Set.isPWO_union, HahnSeries.isPWO_support, and_self, of_symm_add,
      HahnSeries.coeff_add', Pi.add_apply, ne_eq, Set.mem_union, HahnSeries.mem_support]
    contrapose!
    intro h
    rw [h.1, h.2, add_zero]

instance instDistribSMul [MonoidWithZero R] [DistribSMul R V] : DistribSMul (HahnSeries Γ R)
    (HahnModule Γ' R V) where
  smul_add := smul_add

theorem add_smul [AddCommMonoid R] [SMulWithZero R V] {x y : HahnSeries Γ R}
    {z : HahnModule Γ' R V} (h : ∀ (r s : R) (u : V), (r + s) • u = r • u + s • u) :
    (x + y) • z = x • z + y • z := by
  ext a
  have hwf := x.isPWO_support.union y.isPWO_support
  rw [coeff_smul_left hwf, HahnSeries.coeff_add', of_symm_add]
  · simp_all only [Pi.add_apply, HahnSeries.coeff_add']
    rw [coeff_smul_left hwf Set.subset_union_right,
      coeff_smul_left hwf Set.subset_union_left]
    simp only [sum_add_distrib]
  · intro b
    simp_all only [Set.isPWO_union, HahnSeries.isPWO_support, and_self, HahnSeries.mem_support,
      HahnSeries.coeff_add, ne_eq, Set.mem_union]
    contrapose!
    intro h
    rw [h.1, h.2, add_zero]

theorem coeff_single_smul_vadd [MulZeroClass R] [SMulWithZero R V] {r : R} {x : HahnModule Γ' R V}
    {a : Γ'} {b : Γ} :
    ((of R).symm (HahnSeries.single b r • x)).coeff (b +ᵥ a) = r • ((of R).symm x).coeff a := by
  by_cases hr : r = 0
  · simp_all only [map_zero, zero_smul, coeff_smul, HahnSeries.support_zero, HahnSeries.coeff_zero,
    sum_const_zero]
  simp only [hr, coeff_smul, coeff_smul, HahnSeries.support_single_of_ne, ne_eq, not_false_iff]
  by_cases hx : ((of R).symm x).coeff a = 0
  · simp only [hx, smul_zero]
    rw [sum_congr _ fun _ _ => rfl, sum_empty]
    ext ⟨a1, a2⟩
    simp only [notMem_empty, not_and, Set.mem_singleton_iff,
      mem_vaddAntidiagonal, iff_false]
    rintro rfl h2 h1
    rw [IsCancelVAdd.left_cancel a1 a2 a h1] at h2
    exact h2 hx
  trans ∑ ij ∈ {(b, a)},
    (HahnSeries.single b r).coeff ij.fst • ((of R).symm x).coeff ij.snd
  · apply sum_congr _ fun _ _ => rfl
    ext ⟨a1, a2⟩
    simp only [Set.mem_singleton_iff, Prod.mk_inj, mem_vaddAntidiagonal, mem_singleton]
    constructor
    · rintro ⟨rfl, _, h1⟩
      exact ⟨rfl, IsCancelVAdd.left_cancel a1 a2 a h1⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨rfl, by exact hx, rfl⟩
  · simp

@[deprecated (since := "2025-01-31")] alias single_smul_coeff_add := coeff_single_smul_vadd

theorem coeff_single_zero_smul {Γ} [AddCommMonoid Γ] [PartialOrder Γ] [AddAction Γ Γ']
    [IsOrderedCancelVAdd Γ Γ'] [MulZeroClass R] [SMulWithZero R V] {r : R}
    {x : HahnModule Γ' R V} {a : Γ'} :
    ((of R).symm ((HahnSeries.single 0 r : HahnSeries Γ R) • x)).coeff a =
    r • ((of R).symm x).coeff a := by
  nth_rw 1 [← zero_vadd Γ a]
  exact coeff_single_smul_vadd

@[deprecated (since := "2025-01-31")] alias single_zero_smul_coeff := coeff_single_zero_smul

@[simp]
theorem single_zero_smul_eq_smul (Γ) [AddCommMonoid Γ] [PartialOrder Γ] [AddAction Γ Γ']
    [IsOrderedCancelVAdd Γ Γ'] [MulZeroClass R] [SMulWithZero R V] {r : R}
    {x : HahnModule Γ' R V} :
    (HahnSeries.single (0 : Γ) r) • x = r • x := by
  ext
  exact coeff_single_zero_smul

@[simp]
theorem zero_smul' [Zero R] [SMulWithZero R V] {x : HahnModule Γ' R V} :
    (0 : HahnSeries Γ R) • x = 0 := by
  ext
  simp [coeff_smul]

@[simp]
theorem one_smul' {Γ} [AddCommMonoid Γ] [PartialOrder Γ] [AddAction Γ Γ'] [IsOrderedCancelVAdd Γ Γ']
    [MonoidWithZero R] [MulActionWithZero R V] {x : HahnModule Γ' R V} :
    (1 : HahnSeries Γ R) • x = x := by
  ext g
  exact coeff_single_zero_smul.trans (one_smul R (x.coeff g))

theorem support_smul_subset_vadd_support' [MulZeroClass R] [SMulWithZero R V] {x : HahnSeries Γ R}
    {y : HahnModule Γ' R V} :
    ((of R).symm (x • y)).support ⊆ x.support +ᵥ ((of R).symm y).support := by
  apply Set.Subset.trans (fun x hx => _) support_vaddAntidiagonal_subset_vadd
  · exact x.isPWO_support
  · exact y.isPWO_support
  intro x hx
  contrapose! hx
  simp only [Set.mem_setOf_eq, not_nonempty_iff_eq_empty] at hx
  simp [hx, coeff_smul]

theorem support_smul_subset_vadd_support [MulZeroClass R] [SMulWithZero R V] {x : HahnSeries Γ R}
    {y : HahnModule Γ' R V} :
    ((of R).symm (x • y)).support ⊆ x.support +ᵥ ((of R).symm y).support := by
  exact support_smul_subset_vadd_support'

theorem orderTop_vAdd_le_orderTop_smul {Γ Γ'} [LinearOrder Γ] [LinearOrder Γ'] [VAdd Γ Γ']
    [IsOrderedCancelVAdd Γ Γ'] [MulZeroClass R] [SMulWithZero R V] {x : HahnSeries Γ R}
    [VAdd (WithTop Γ) (WithTop Γ')] {y : HahnModule Γ' R V}
    (h : ∀ (γ : Γ) (γ' : Γ'), γ +ᵥ γ' = (γ : WithTop Γ) +ᵥ (γ' : WithTop Γ')) :
    x.orderTop +ᵥ ((of R).symm y).orderTop ≤ ((of R).symm (x • y)).orderTop := by
  by_cases hx : x = 0; · simp_all
  by_cases hy : y = 0; · simp_all
  have hhy : ((of R).symm y) ≠ 0 := hy
  rw [HahnSeries.orderTop_of_ne hx, HahnSeries.orderTop_of_ne hhy, ← h,
      ← Set.IsWF.min_vadd]
  by_cases hxy : (of R).symm (x • y) = 0
  · rw [hxy, HahnSeries.orderTop_zero]
    exact OrderTop.le_top (α := WithTop Γ') _
  · rw [HahnSeries.orderTop_of_ne hxy, WithTop.coe_le_coe]
    exact Set.IsWF.min_le_min_of_subset support_smul_subset_vadd_support

theorem coeff_smul_order_add_order {Γ}
    [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ] [Zero R]
    [SMulWithZero R V] (x : HahnSeries Γ R) (y : HahnModule Γ R V) :
    ((of R).symm (x • y)).coeff (x.order + ((of R).symm y).order) =
    x.leadingCoeff • ((of R).symm y).leadingCoeff := by
  by_cases hx : x = (0 : HahnSeries Γ R); · simp [HahnSeries.coeff_zero, hx]
  by_cases hy : (of R).symm y = 0; · simp [hy, coeff_smul]
  rw [HahnSeries.order_of_ne hx, HahnSeries.order_of_ne hy, coeff_smul,
    HahnSeries.leadingCoeff_of_ne hx, HahnSeries.leadingCoeff_of_ne hy, ← vadd_eq_add,
    Finset.vaddAntidiagonal_min_vadd_min, Finset.sum_singleton]

@[deprecated (since := "2025-01-31")] alias smul_coeff_order_add_order := coeff_smul_order_add_order

end DistribSMul

end HahnModule

variable [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]

namespace HahnSeries

instance [NonUnitalNonAssocSemiring R] : Mul (HahnSeries Γ R) where
  mul x y := (HahnModule.of R).symm (x • HahnModule.of R y)

theorem of_symm_smul_of_eq_mul [NonUnitalNonAssocSemiring R] {x y : HahnSeries Γ R} :
    (HahnModule.of R).symm (x • HahnModule.of R y) = x * y := rfl

theorem coeff_mul [NonUnitalNonAssocSemiring R] {x y : HahnSeries Γ R} {a : Γ} :
    (x * y).coeff a =
      ∑ ij ∈ addAntidiagonal x.isPWO_support y.isPWO_support a, x.coeff ij.fst * y.coeff ij.snd :=
  rfl

@[deprecated (since := "2025-01-31")] alias mul_coeff := coeff_mul

protected lemma map_mul [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] (f : R →ₙ+* S)
    {x y : HahnSeries Γ R} : (x * y).map f = (x.map f : HahnSeries Γ S) * (y.map f) := by
  ext
  simp only [map_coeff, coeff_mul, map_sum, map_mul]
  refine Eq.symm (sum_subset (fun gh hgh => ?_) (fun gh hgh hz => ?_))
  · simp_all only [mem_addAntidiagonal, mem_support, map_coeff, ne_eq, and_true]
    exact ⟨fun h => hgh.1 (map_zero f ▸ congrArg f h), fun h => hgh.2.1 (map_zero f ▸ congrArg f h)⟩
  · simp_all only [mem_addAntidiagonal, mem_support, ne_eq, map_coeff, and_true,
      not_and, not_not]
    by_cases h : f (x.coeff gh.1) = 0
    · exact mul_eq_zero_of_left h (f (y.coeff gh.2))
    · exact mul_eq_zero_of_right (f (x.coeff gh.1)) (hz h)

theorem coeff_mul_left' [NonUnitalNonAssocSemiring R] {x y : HahnSeries Γ R} {a : Γ} {s : Set Γ}
    (hs : s.IsPWO) (hxs : x.support ⊆ s) :
    (x * y).coeff a =
      ∑ ij ∈ addAntidiagonal hs y.isPWO_support a, x.coeff ij.fst * y.coeff ij.snd :=
  HahnModule.coeff_smul_left hs hxs

@[deprecated (since := "2025-01-31")] alias mul_coeff_left' := coeff_mul_left'

theorem coeff_mul_right' [NonUnitalNonAssocSemiring R] {x y : HahnSeries Γ R} {a : Γ} {s : Set Γ}
    (hs : s.IsPWO) (hys : y.support ⊆ s) :
    (x * y).coeff a =
      ∑ ij ∈ addAntidiagonal x.isPWO_support hs a, x.coeff ij.fst * y.coeff ij.snd :=
  HahnModule.coeff_smul_right hs hys

@[deprecated (since := "2025-01-31")] alias mul_coeff_right' := coeff_mul_right'

instance [NonUnitalNonAssocSemiring R] : Distrib (HahnSeries Γ R) :=
  { inferInstanceAs (Mul (HahnSeries Γ R)),
    inferInstanceAs (Add (HahnSeries Γ R)) with
    left_distrib := fun x y z => by
      simp only [← of_symm_smul_of_eq_mul]
      exact HahnModule.smul_add x y z
    right_distrib := fun x y z => by
      simp only [← of_symm_smul_of_eq_mul]
      refine HahnModule.add_smul ?_
      simp only [smul_eq_mul]
      exact add_mul }

theorem coeff_single_mul_add [NonUnitalNonAssocSemiring R] {r : R} {x : HahnSeries Γ R} {a : Γ}
    {b : Γ} : (single b r * x).coeff (a + b) = r * x.coeff a := by
  rw [← of_symm_smul_of_eq_mul, add_comm, ← vadd_eq_add]
  exact HahnModule.coeff_single_smul_vadd

@[deprecated (since := "2025-01-31")] alias single_mul_coeff_add := coeff_single_mul_add

theorem coeff_mul_single_add [NonUnitalNonAssocSemiring R] {r : R} {x : HahnSeries Γ R} {a : Γ}
    {b : Γ} : (x * single b r).coeff (a + b) = x.coeff a * r := by
  by_cases hr : r = 0
  · simp [hr, coeff_mul]
  simp only [hr, coeff_mul, support_single_of_ne, Ne, not_false_iff]
  by_cases hx : x.coeff a = 0
  · simp only [hx, zero_mul]
    rw [sum_congr _ fun _ _ => rfl, sum_empty]
    ext ⟨a1, a2⟩
    simp only [notMem_empty, not_and, Set.mem_singleton_iff,
      mem_addAntidiagonal, iff_false]
    rintro h2 rfl h1
    rw [← add_right_cancel h1] at hx
    exact h2 hx
  trans ∑ ij ∈ {(a, b)}, x.coeff ij.fst * (single b r).coeff ij.snd
  · apply sum_congr _ fun _ _ => rfl
    ext ⟨a1, a2⟩
    simp only [Set.mem_singleton_iff, Prod.mk_inj, mem_addAntidiagonal, mem_singleton]
    constructor
    · rintro ⟨_, rfl, h1⟩
      exact ⟨add_right_cancel h1, rfl⟩
    · rintro ⟨rfl, rfl⟩
      simp [hx]
  · simp

@[deprecated (since := "2025-01-31")] alias mul_single_coeff_add := coeff_mul_single_add

@[simp]
theorem coeff_mul_single_zero [NonUnitalNonAssocSemiring R] {r : R} {x : HahnSeries Γ R} {a : Γ} :
    (x * single 0 r).coeff a = x.coeff a * r := by rw [← add_zero a, coeff_mul_single_add, add_zero]

@[deprecated (since := "2025-01-31")] alias mul_single_zero_coeff := coeff_mul_single_zero

theorem coeff_single_zero_mul [NonUnitalNonAssocSemiring R] {r : R} {x : HahnSeries Γ R} {a : Γ} :
    ((single 0 r : HahnSeries Γ R) * x).coeff a = r * x.coeff a := by
  rw [← add_zero a, coeff_single_mul_add, add_zero]

@[deprecated (since := "2025-01-31")] alias single_zero_mul_coeff := coeff_single_zero_mul

@[simp]
theorem single_zero_mul_eq_smul [Semiring R] {r : R} {x : HahnSeries Γ R} :
    single 0 r * x = r • x := by
  ext
  exact coeff_single_zero_mul

theorem support_mul_subset_add_support [NonUnitalNonAssocSemiring R] {x y : HahnSeries Γ R} :
    support (x * y) ⊆ support x + support y := by
  rw [← of_symm_smul_of_eq_mul, ← vadd_eq_add]
  exact HahnModule.support_smul_subset_vadd_support

section orderLemmas

variable {Γ : Type*} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [NonUnitalNonAssocSemiring R]

theorem coeff_mul_order_add_order (x y : HahnSeries Γ R) :
    (x * y).coeff (x.order + y.order) = x.leadingCoeff * y.leadingCoeff := by
  simp only [← of_symm_smul_of_eq_mul]
  exact HahnModule.coeff_smul_order_add_order x y

@[deprecated (since := "2025-01-31")] alias mul_coeff_order_add_order := coeff_mul_order_add_order

theorem orderTop_add_le_mul {x y : HahnSeries Γ R} :
    x.orderTop + y.orderTop ≤ (x * y).orderTop := by
  rw [← smul_eq_mul]
  exact HahnModule.orderTop_vAdd_le_orderTop_smul fun i j ↦ rfl

theorem order_mul_of_nonzero {x y : HahnSeries Γ R}
    (h : x.leadingCoeff * y.leadingCoeff ≠ 0) : (x * y).order = x.order + y.order := by
  have hx : x.leadingCoeff ≠ 0 := by aesop
  have hy : y.leadingCoeff ≠ 0 := by aesop
  have hxy : (x * y).coeff (x.order + y.order) ≠ 0 :=
    ne_of_eq_of_ne (coeff_mul_order_add_order x y) h
  refine le_antisymm (order_le_of_coeff_ne_zero
    (Eq.mpr (congrArg (fun _a ↦ _a ≠ 0) (coeff_mul_order_add_order x y)) h)) ?_
  rw [order_of_ne <| leadingCoeff_ne_iff.mp hx, order_of_ne <| leadingCoeff_ne_iff.mp hy,
    order_of_ne <| ne_zero_of_coeff_ne_zero hxy, ← Set.IsWF.min_add]
  exact Set.IsWF.min_le_min_of_subset support_mul_subset_add_support

theorem order_single_mul_of_isRegular {g : Γ} {r : R} (hr : IsRegular r)
    {x : HahnSeries Γ R} (hx : x ≠ 0) : (((single g) r) * x).order = g + x.order := by
  obtain _|_ := subsingleton_or_nontrivial R
  · exact (hx <| Subsingleton.eq_zero x).elim
  have hrx : ((single g) r).leadingCoeff * x.leadingCoeff ≠ 0 := by
    rwa [leadingCoeff_of_single, ne_eq, hr.left.mul_left_eq_zero_iff, leadingCoeff_eq_iff]
  rw [order_mul_of_nonzero hrx, order_single <| IsRegular.ne_zero hr]

end orderLemmas

private theorem mul_assoc' [NonUnitalSemiring R] (x y z : HahnSeries Γ R) :
    x * y * z = x * (y * z) := by
  ext b
  rw [coeff_mul_left' (x.isPWO_support.add y.isPWO_support) support_mul_subset_add_support,
    coeff_mul_right' (y.isPWO_support.add z.isPWO_support) support_mul_subset_add_support]
  simp only [coeff_mul, sum_mul, mul_sum, sum_sigma']
  apply Finset.sum_nbij' (fun ⟨⟨_i, j⟩, ⟨k, l⟩⟩ ↦ ⟨(k, l + j), (l, j)⟩)
    (fun ⟨⟨i, _j⟩, ⟨k, l⟩⟩ ↦ ⟨(i + k, l), (i, k)⟩) <;>
    aesop (add safe Set.add_mem_add) (add simp [add_assoc, mul_assoc])

instance [NonUnitalNonAssocSemiring R] : NonUnitalNonAssocSemiring (HahnSeries Γ R) :=
  { inferInstanceAs (AddCommMonoid (HahnSeries Γ R)),
    inferInstanceAs (Distrib (HahnSeries Γ R)) with
    zero_mul := fun _ => by
      ext
      simp [coeff_mul]
    mul_zero := fun _ => by
      ext
      simp [coeff_mul] }

instance [NonUnitalSemiring R] : NonUnitalSemiring (HahnSeries Γ R) :=
  { inferInstanceAs (NonUnitalNonAssocSemiring (HahnSeries Γ R)) with
    mul_assoc := mul_assoc' }

instance [NonAssocSemiring R] : NonAssocSemiring (HahnSeries Γ R) :=
  { inferInstanceAs (AddMonoidWithOne (HahnSeries Γ R)),
    inferInstanceAs (NonUnitalNonAssocSemiring (HahnSeries Γ R)) with
    one_mul := fun x => by
      ext
      exact coeff_single_zero_mul.trans (one_mul _)
    mul_one := fun x => by
      ext
      exact coeff_mul_single_zero.trans (mul_one _) }

instance [Semiring R] : Semiring (HahnSeries Γ R) :=
  { inferInstanceAs (NonAssocSemiring (HahnSeries Γ R)),
    inferInstanceAs (NonUnitalSemiring (HahnSeries Γ R)) with }

instance [NonUnitalCommSemiring R] : NonUnitalCommSemiring (HahnSeries Γ R) where
  __ : NonUnitalSemiring (HahnSeries Γ R) := inferInstance
  mul_comm x y := by
    ext
    simp_rw [coeff_mul, mul_comm]
    exact Finset.sum_equiv (Equiv.prodComm _ _) (fun _ ↦ swap_mem_addAntidiagonal.symm) <| by simp

instance [CommSemiring R] : CommSemiring (HahnSeries Γ R) :=
  { inferInstanceAs (NonUnitalCommSemiring (HahnSeries Γ R)),
    inferInstanceAs (Semiring (HahnSeries Γ R)) with }

instance [NonUnitalNonAssocRing R] : NonUnitalNonAssocRing (HahnSeries Γ R) :=
  { inferInstanceAs (NonUnitalNonAssocSemiring (HahnSeries Γ R)),
    inferInstanceAs (AddGroup (HahnSeries Γ R)) with }

instance [NonUnitalRing R] : NonUnitalRing (HahnSeries Γ R) :=
  { inferInstanceAs (NonUnitalNonAssocRing (HahnSeries Γ R)),
    inferInstanceAs (NonUnitalSemiring (HahnSeries Γ R)) with }

instance [NonAssocRing R] : NonAssocRing (HahnSeries Γ R) :=
  { inferInstanceAs (NonUnitalNonAssocRing (HahnSeries Γ R)),
    inferInstanceAs (NonAssocSemiring (HahnSeries Γ R)),
    inferInstanceAs (AddGroupWithOne (HahnSeries Γ R)) with }

instance [Ring R] : Ring (HahnSeries Γ R) :=
  { inferInstanceAs (Semiring (HahnSeries Γ R)),
    inferInstanceAs (AddCommGroupWithOne (HahnSeries Γ R)) with }

instance [NonUnitalCommRing R] : NonUnitalCommRing (HahnSeries Γ R) :=
  { inferInstanceAs (NonUnitalCommSemiring (HahnSeries Γ R)),
    inferInstanceAs (NonUnitalRing (HahnSeries Γ R)) with }

instance [CommRing R] : CommRing (HahnSeries Γ R) :=
  { inferInstanceAs (CommSemiring (HahnSeries Γ R)),
    inferInstanceAs (Ring (HahnSeries Γ R)) with }

theorem orderTop_nsmul_le_orderTop_pow {Γ}
    [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
    [Semiring R] {x : HahnSeries Γ R} {n : ℕ} : n • x.orderTop ≤ (x ^ n).orderTop := by
  induction n with
  | zero =>
    simp only [zero_smul, pow_zero]
    by_cases h : (0 : R) = 1
    · simp [subsingleton_iff_zero_eq_one.mp h]
    · simp [nontrivial_of_ne 0 1 h]
  | succ n ih =>
    rw [add_nsmul, pow_add]
    calc
      n • x.orderTop + 1 • x.orderTop ≤ (x ^ n).orderTop + 1 • x.orderTop :=
        add_le_add_right ih (1 • x.orderTop)
      (x ^ n).orderTop + 1 • x.orderTop = (x ^ n).orderTop + x.orderTop := by rw [one_nsmul]
      (x ^ n).orderTop + x.orderTop ≤ (x ^ n * x).orderTop := orderTop_add_le_mul
      (x ^ n * x).orderTop ≤ (x ^ n * x ^ 1).orderTop := by rw [pow_one]

end HahnSeries

namespace HahnModule

variable [PartialOrder Γ'] [AddAction Γ Γ'] [IsOrderedCancelVAdd Γ Γ'] [AddCommMonoid V]

private theorem mul_smul' [Semiring R] [Module R V] (x y : HahnSeries Γ R)
    (z : HahnModule Γ' R V) : (x * y) • z = x • (y • z) := by
  ext b
  rw [coeff_smul_left (x.isPWO_support.add y.isPWO_support)
    HahnSeries.support_mul_subset_add_support, coeff_smul_right
    (y.isPWO_support.vadd ((of R).symm z).isPWO_support) support_smul_subset_vadd_support]
  simp only [HahnSeries.coeff_mul, coeff_smul, sum_smul, smul_sum, sum_sigma']
  apply Finset.sum_nbij' (fun ⟨⟨_i, j⟩, ⟨k, l⟩⟩ ↦ ⟨(k, l +ᵥ j), (l, j)⟩)
    (fun ⟨⟨i, _j⟩, ⟨k, l⟩⟩ ↦ ⟨(i + k, l), (i, k)⟩) <;>
    aesop (add safe [Set.vadd_mem_vadd, Set.add_mem_add]) (add simp [add_vadd, mul_smul])

instance instBaseModule [Semiring R] [Module R V] : Module R (HahnModule Γ' R V) :=
  inferInstanceAs <| Module R (HahnSeries Γ' V)

instance instModule [Semiring R] [Module R V] : Module (HahnSeries Γ R)
    (HahnModule Γ' R V) := {
  inferInstanceAs (DistribSMul (HahnSeries Γ R) (HahnModule Γ' R V)) with
  mul_smul := mul_smul'
  one_smul := fun _ => one_smul'
  add_smul := fun _ _ _ => add_smul Module.add_smul
  zero_smul := fun _ => zero_smul' }

instance [Zero R] {S : Type*} [Zero S] [SMul R S] [SMulWithZero R V] [SMulWithZero S V]
    [IsScalarTower R S V] : IsScalarTower R S (HahnSeries Γ V) where
  smul_assoc r s a := by
    ext
    simp

instance [Semiring R] [Module R V] : IsScalarTower R (HahnSeries Γ R) (HahnModule Γ' R V) where
  smul_assoc r x a := by
    rw [← HahnSeries.single_zero_mul_eq_smul, mul_smul', ← single_zero_smul_eq_smul Γ]

instance SMulCommClass [CommSemiring R] [Module R V] :
    SMulCommClass R (HahnSeries Γ R) (HahnModule Γ' R V) where
  smul_comm r x y := by
    rw [← single_zero_smul_eq_smul Γ, ← mul_smul', mul_comm, mul_smul', single_zero_smul_eq_smul Γ]

instance instNoZeroSMulDivisors {Γ} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
    [Zero R] [SMulWithZero R V] [NoZeroSMulDivisors R V] :
    NoZeroSMulDivisors (HahnSeries Γ R) (HahnModule Γ R V) where
  eq_zero_or_eq_zero_of_smul_eq_zero {x y} hxy := by
    contrapose! hxy
    simp only [ne_eq]
    rw [HahnModule.ext_iff, funext_iff, not_forall]
    refine ⟨x.order + ((of R).symm y).order, ?_⟩
    rw [coeff_smul_order_add_order x y, of_symm_zero, HahnSeries.coeff_zero, smul_eq_zero, not_or]
    constructor
    · exact HahnSeries.leadingCoeff_ne_iff.mpr hxy.1
    · exact HahnSeries.leadingCoeff_ne_iff.mpr hxy.2

end HahnModule

namespace HahnSeries

instance {Γ} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
    [NonUnitalNonAssocSemiring R] [NoZeroDivisors R] :
    NoZeroDivisors (HahnSeries Γ R) where
  eq_zero_or_eq_zero_of_mul_eq_zero {x y} xy := by
    haveI : NoZeroSMulDivisors (HahnSeries Γ R) (HahnSeries Γ R) :=
      HahnModule.instNoZeroSMulDivisors
    exact eq_zero_or_eq_zero_of_smul_eq_zero xy

instance {Γ} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ] [Ring R] [IsDomain R] :
    IsDomain (HahnSeries Γ R) :=
  NoZeroDivisors.to_isDomain _

theorem orderTop_add_orderTop_le_orderTop_mul {Γ}
    [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
    [NonUnitalNonAssocSemiring R] {x y : HahnSeries Γ R} :
    x.orderTop + y.orderTop ≤ (x * y).orderTop := by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  by_cases hxy : x * y = 0
  · simp [hxy]
  rw [orderTop_of_ne hx, orderTop_of_ne hy, orderTop_of_ne hxy, ← WithTop.coe_add,
    WithTop.coe_le_coe, ← Set.IsWF.min_add]
  exact Set.IsWF.min_le_min_of_subset support_mul_subset_add_support

@[simp]
theorem order_mul {Γ} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
    [NonUnitalNonAssocSemiring R]
    [NoZeroDivisors R] {x y : HahnSeries Γ R} (hx : x ≠ 0) (hy : y ≠ 0) :
    (x * y).order = x.order + y.order := by
  apply le_antisymm
  · apply order_le_of_coeff_ne_zero
    rw [coeff_mul_order_add_order x y]
    exact mul_ne_zero (leadingCoeff_ne_iff.mpr hx) (leadingCoeff_ne_iff.mpr hy)
  · rw [order_of_ne hx, order_of_ne hy, order_of_ne (mul_ne_zero hx hy), ← Set.IsWF.min_add]
    exact Set.IsWF.min_le_min_of_subset support_mul_subset_add_support

@[simp]
theorem order_pow {Γ} [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
    [Semiring R] [NoZeroDivisors R]
    (x : HahnSeries Γ R) (n : ℕ) : (x ^ n).order = n • x.order := by
  induction' n with h IH
  · simp
  rcases eq_or_ne x 0 with (rfl | hx)
  · simp
  rw [pow_succ, order_mul (pow_ne_zero _ hx) hx, succ_nsmul, IH]

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring R]

@[simp]
theorem single_mul_single {a b : Γ} {r s : R} :
    single a r * single b s = single (a + b) (r * s) := by
  ext x
  by_cases h : x = a + b
  · rw [h, coeff_mul_single_add]
    simp
  · rw [coeff_single_of_ne h, coeff_mul, sum_eq_zero]
    simp_rw [mem_addAntidiagonal]
    rintro ⟨y, z⟩ ⟨hy, hz, rfl⟩
    rw [eq_of_mem_support_single hy, eq_of_mem_support_single hz] at h
    exact (h rfl).elim

end NonUnitalNonAssocSemiring

section Semiring

variable [Semiring R]

@[simp]
theorem single_pow (a : Γ) (n : ℕ) (r : R) : single a r ^ n = single (n • a) (r ^ n) := by
  induction' n with n IH
  · ext; simp only [pow_zero, coeff_one, zero_smul, coeff_single]
  · rw [pow_succ, pow_succ, IH, single_mul_single, succ_nsmul]

end Semiring

section NonAssocSemiring

variable [NonAssocSemiring R]

/-- `C a` is the constant Hahn Series `a`. `C` is provided as a ring homomorphism. -/
@[simps]
def C : R →+* HahnSeries Γ R where
  toFun := single 0
  map_zero' := single_eq_zero
  map_one' := rfl
  map_add' x y := by
    ext a
    by_cases h : a = 0 <;> simp [h]
  map_mul' x y := by rw [single_mul_single, zero_add]

theorem C_zero : C (0 : R) = (0 : HahnSeries Γ R) :=
  C.map_zero

theorem C_one : C (1 : R) = (1 : HahnSeries Γ R) :=
  C.map_one

theorem map_C [NonAssocSemiring S] (a : R) (f : R →+* S) :
    ((C a).map f : HahnSeries Γ S) = C (f a) := by
  ext g
  by_cases h : g = 0 <;> simp [h]

theorem C_injective : Function.Injective (C : R → HahnSeries Γ R) := by
  intro r s rs
  rw [HahnSeries.ext_iff, funext_iff] at rs
  have h := rs 0
  rwa [C_apply, coeff_single_same, C_apply, coeff_single_same] at h

theorem C_ne_zero {r : R} (h : r ≠ 0) : (C r : HahnSeries Γ R) ≠ 0 := by
  contrapose! h
  rw [← C_zero] at h
  exact C_injective h

theorem order_C {r : R} : order (C r : HahnSeries Γ R) = 0 := by
  by_cases h : r = 0
  · rw [h, C_zero, order_zero]
  · exact order_single h

end NonAssocSemiring

section Semiring

variable [Semiring R]

theorem C_mul_eq_smul {r : R} {x : HahnSeries Γ R} : C r * x = r • x :=
  single_zero_mul_eq_smul

end Semiring

section Domain

variable {Γ' : Type*} [AddCommMonoid Γ'] [PartialOrder Γ'] [IsOrderedCancelAddMonoid Γ']

theorem embDomain_mul [NonUnitalNonAssocSemiring R] (f : Γ ↪o Γ')
    (hf : ∀ x y, f (x + y) = f x + f y) (x y : HahnSeries Γ R) :
    embDomain f (x * y) = embDomain f x * embDomain f y := by
  ext g
  by_cases hg : g ∈ Set.range f
  · obtain ⟨g, rfl⟩ := hg
    simp only [coeff_mul, embDomain_coeff]
    trans
      ∑ ij ∈
        (addAntidiagonal x.isPWO_support y.isPWO_support g).map
          (f.toEmbedding.prodMap f.toEmbedding),
        (embDomain f x).coeff ij.1 * (embDomain f y).coeff ij.2
    · simp
    apply sum_subset
    · rintro ⟨i, j⟩ hij
      simp only [mem_map, mem_addAntidiagonal,
        Function.Embedding.coe_prodMap, mem_support, Prod.exists] at hij
      obtain ⟨i, j, ⟨hx, hy, rfl⟩, rfl, rfl⟩ := hij
      simp [hx, hy, hf]
    · rintro ⟨_, _⟩ h1 h2
      contrapose! h2
      obtain ⟨i, _, rfl⟩ := support_embDomain_subset (ne_zero_and_ne_zero_of_mul h2).1
      obtain ⟨j, _, rfl⟩ := support_embDomain_subset (ne_zero_and_ne_zero_of_mul h2).2
      simp only [mem_map, mem_addAntidiagonal,
        Function.Embedding.coe_prodMap, mem_support, Prod.exists]
      simp only [mem_addAntidiagonal, embDomain_coeff, mem_support, ← hf,
        OrderEmbedding.eq_iff_eq] at h1
      exact ⟨i, j, h1, rfl⟩
  · rw [embDomain_notin_range hg, eq_comm]
    contrapose! hg
    obtain ⟨_, hi, _, hj, rfl⟩ := support_mul_subset_add_support ((mem_support _ _).2 hg)
    obtain ⟨i, _, rfl⟩ := support_embDomain_subset hi
    obtain ⟨j, _, rfl⟩ := support_embDomain_subset hj
    exact ⟨i + j, hf i j⟩

omit [IsOrderedCancelAddMonoid Γ] [IsOrderedCancelAddMonoid Γ'] in
theorem embDomain_one [NonAssocSemiring R] (f : Γ ↪o Γ') (hf : f 0 = 0) :
    embDomain f (1 : HahnSeries Γ R) = (1 : HahnSeries Γ' R) :=
  embDomain_single.trans <| hf.symm ▸ rfl

/-- Extending the domain of Hahn series is a ring homomorphism. -/
@[simps]
def embDomainRingHom [NonAssocSemiring R] (f : Γ →+ Γ') (hfi : Function.Injective f)
    (hf : ∀ g g' : Γ, f g ≤ f g' ↔ g ≤ g') : HahnSeries Γ R →+* HahnSeries Γ' R where
  toFun := embDomain ⟨⟨f, hfi⟩, hf _ _⟩
  map_one' := embDomain_one _ f.map_zero
  map_mul' := embDomain_mul _ f.map_add
  map_zero' := embDomain_zero
  map_add' := embDomain_add _

theorem embDomainRingHom_C [NonAssocSemiring R] {f : Γ →+ Γ'} {hfi : Function.Injective f}
    {hf : ∀ g g' : Γ, f g ≤ f g' ↔ g ≤ g'} {r : R} : embDomainRingHom f hfi hf (C r) = C r :=
  embDomain_single.trans (by simp)

end Domain

section Algebra

variable [CommSemiring R] {A : Type*} [Semiring A] [Algebra R A]

instance : Algebra R (HahnSeries Γ A) where
  algebraMap := C.comp (algebraMap R A)
  smul_def' r x := by
    ext
    simp
  commutes' r x := by
    ext
    simp only [coeff_smul, single_zero_mul_eq_smul, RingHom.coe_comp, C_apply,
      Function.comp_apply, algebraMap_smul, coeff_mul_single_zero]
    rw [← Algebra.commutes, Algebra.smul_def]

theorem C_eq_algebraMap : C = algebraMap R (HahnSeries Γ R) :=
  rfl

theorem algebraMap_apply {r : R} : algebraMap R (HahnSeries Γ A) r = C (algebraMap R A r) :=
  rfl

instance [Nontrivial Γ] [Nontrivial R] : Nontrivial (Subalgebra R (HahnSeries Γ R)) :=
  ⟨⟨⊥, ⊤, by
      rw [Ne, SetLike.ext_iff, not_forall]
      obtain ⟨a, ha⟩ := exists_ne (0 : Γ)
      refine ⟨single a 1, ?_⟩
      simp only [Algebra.mem_bot, not_exists, Set.mem_range, iff_true, Algebra.mem_top]
      intro x
      rw [HahnSeries.ext_iff, funext_iff, not_forall]
      refine ⟨a, ?_⟩
      rw [coeff_single_same, algebraMap_apply, C_apply, coeff_single_of_ne ha]
      exact zero_ne_one⟩⟩

section Domain

variable {Γ' : Type*} [AddCommMonoid Γ'] [PartialOrder Γ'] [IsOrderedCancelAddMonoid Γ']

/-- Extending the domain of Hahn series is an algebra homomorphism. -/
@[simps!]
def embDomainAlgHom (f : Γ →+ Γ') (hfi : Function.Injective f)
    (hf : ∀ g g' : Γ, f g ≤ f g' ↔ g ≤ g') : HahnSeries Γ A →ₐ[R] HahnSeries Γ' A :=
  { embDomainRingHom f hfi hf with commutes' := fun _ => embDomainRingHom_C (hf := hf) }

end Domain

end Algebra

end HahnSeries
