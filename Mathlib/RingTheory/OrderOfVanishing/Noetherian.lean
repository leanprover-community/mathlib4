/-
Copyright (c) 2025 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/

module

public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Valuation.Discrete.Basic
public import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.Order.GroupWithZero.WithZero
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike

/-!
# Order of vanishing in Noetherian rings.

In this file we define various properties of the order of vanishing in Noetherian rings, including
 some API for computing the order of vanishing in discrete valuation rings.
-/

@[expose] public section

variable {R : Type*} [CommRing R]

namespace Ring

section NoetherianDimLEOne

variable {R : Type*} [CommRing R]
variable [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

open scoped nonZeroDivisors
/--
Order of vanishing function as a monoid homomorphism
-/
noncomputable
def ordMonoidHom : R⁰ →* Multiplicative ℕ where
  toFun x := .ofAdd <| (Ring.ord R x).toNat
  map_one' := by simp [OneMemClass.coe_one, isUnit_one, ord_of_isUnit]
  map_mul' x y := by simp [ord_mul, ENat.toNat_add (ord_ne_top x.2) (ord_ne_top y.2)]

@[simp]
lemma ordMonoidHom_eq_ord (x : R⁰) : (ordMonoidHom x).toAdd = Ring.ord R x :=
  (ENat.coe_toNat (ord_ne_top x.2))

@[simp]
lemma ordMonoidWithZeroHom_eq_ordMonoidHom [Nontrivial R] (x : R⁰) :
    .coe (.ofAdd ((ordMonoidHom x).toAdd : ℤ)) = ordMonoidWithZeroHom R x := by
  simp only [SetLike.coe_mem, ordMonoidWithZeroHom_eq_ord, ordMonoidHom, MonoidHom.coe_mk,
    OneHom.coe_mk, toAdd_ofAdd]
  rw [← ENat.coe_lift (ord R x.1) (ord_lt_top x.2), ENat.recTopCoe_coe,
    ENat.coe_lift, ENat.lift_eq_toNat_of_lt_top]

/--
Analogue of `ord_ne_top` for `ordMonoidWithZeroHom`.
-/
lemma ordMonoidWithZeroHom_ne_zero [Nontrivial R] {a : R} (ha : a ∈ nonZeroDivisors R) :
    ordMonoidWithZeroHom R a ≠ 0 := by
  lift a to R⁰ using ha
  simp [← ordMonoidWithZeroHom_eq_ordMonoidHom]

variable [Nontrivial R]

/--
Helper lemma to pass between the orders on `ℕ∞` and `ℤᵐ⁰` (which notably have different behaviour at
`∞`). Note that here we're using the fact that the order of any non zero divisor is finite, hence
the assumptions on the ring.
-/
lemma ord_le_iff {a b : R} (ha : a ∈ nonZeroDivisors R) (hb : b ∈ nonZeroDivisors R) :
    ord R a ≤ ord R b ↔ ordMonoidWithZeroHom R a ≤ ordMonoidWithZeroHom R b := by
  lift a to R⁰ using ha
  lift b to R⁰ using hb
  simp [← ordMonoidWithZeroHom_eq_ordMonoidHom, ← ordMonoidHom_eq_ord]

end NoetherianDimLEOne

section IsDiscreteValuationRing

variable [IsDomain R] [IsDiscreteValuationRing R]

/--
In a discrete valuation ring, `ord R x` is the same as `addVal R x`. We prefer the second spelling
here for most purposes.
-/
@[simp]
lemma ord_eq_addVal (x : R) : ord R x = IsDiscreteValuationRing.addVal R x := by
  by_cases hx : x = 0
  · simp only [ord, hx, AddValuation.map_zero]
    subst hx
    by_contra!
    rw [Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian] at this
    have art := this.2
    rw [Ideal.span_singleton_zero] at art
    have : IsArtinianRing R :=
      (LinearEquiv.isArtinian_iff (Submodule.quotEquivOfEqBot ⊥ rfl).symm).mpr art
    exact (IsDiscreteValuationRing.not_krullDimLE_zero R) (PrimeSpectrum.instKrullDimLEOfNatNat R)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨m, α, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
  rw [ord_mul, ord_pow, ord_of_irreducible hϖ]
  · simp [IsDiscreteValuationRing.addVal_uniformizer hϖ]
  all_goals simp_all [Irreducible.ne_zero hϖ]

open IsDiscreteValuationRing

lemma ord_eq_iff_associated (x y : R) :
    ord R x = ord R y ↔ Associated x y := by simp [addVal_eq_iff_associated]

/--
For `x y : R` where `R` is a discrete valuation ring, we have that
`min (ord R x) (ord R y) ≤ ord R (x + y)`. It should be noted that the order
we're using here is the order on `ℕ∞`, where `⊤` is greater than everything else.
This is relevant since when we're working with `ordFrac` we work with `ℤᵐ⁰`, where the
order instance has the `0` element less than everything else.
-/
theorem ord_add (x y : R) : min (Ring.ord R x) (Ring.ord R y) ≤ Ring.ord R (x + y) := by
  grw [ord_eq_addVal x, ord_eq_addVal y, ord_eq_addVal (x + y), IsDiscreteValuationRing.addVal_add]

end IsDiscreteValuationRing

section ordFrac

variable [IsDomain R] [IsNoetherianRing R] [KrullDimLE 1 R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/--
For any nonzero `x : R`, `ordFrac R (algebraMap R K x) ≥ 1`. Note here that this last
expression is in `ℤᵐ⁰`, so the syntax may be slightly different than expected. Namely,
the `1` here is `WithZero.exp 0`, and so would usually be written as `0` in the additive
context. Further, the order here is different to similar lemmas involving `Ring.ord`, since
here the order is on `ℤᵐ⁰` has the `∞` element less than everything else, whereas in `Ring.ord`
we work with the order on `ℕ∞` where the `∞` element is interpreted as a `⊤` element.
-/
lemma ordFrac_ge_one_of_ne_zero {x : R} (hx : x ≠ 0) :
    1 ≤ ordFrac R (algebraMap R K x) := by
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (ord_ne_top (a := x) (by simpa))
  simp_rw [ordFrac_eq_ord R hx, ordMonoidWithZeroHom_eq_coe _ (by simpa) hm.symm,
    WithZero.one_le_coe, ← ofAdd_zero, Multiplicative.ofAdd_le, Nat.cast_nonneg _]

lemma ordFrac_le_smul {S : Type*} [CommRing S] [Algebra S R] [Algebra S K]
    [IsScalarTower S R K] (a : S) (ha : algebraMap S R a ≠ 0) (f : K) :
    Ring.ordFrac R f ≤ Ring.ordFrac R (a • f) := by
  by_cases j : f = 0
  · simp [j]
  suffices ordFrac R f ≤ ordFrac R (algebraMap S K a • f) by simp_all only [ne_eq,
    algebraMap_smul]
  simp only [smul_eq_mul, map_mul]
  apply le_mul_of_one_le_left'
  simp [IsScalarTower.algebraMap_eq S R K, ordFrac_ge_one_of_ne_zero ha]

@[simp]
lemma ordFrac_of_isUnit {x : R} (hx : IsUnit x) : ordFrac R (algebraMap R K x) = 1 := by
  simp [ordFrac_eq_ord R (IsUnit.ne_zero hx), IsUnit.mem_nonZeroDivisors hx,
      ordMonoidWithZeroHom_eq_ord, ord_of_isUnit hx]

end ordFrac
section IsDiscreteValuationRing

variable [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

lemma ordMonoidWithZeroHom_eq_intValuation {x : R} (h : x ∈ nonZeroDivisors R) :
    (ordMonoidWithZeroHom R) x = ((IsDiscreteValuationRing.maximalIdeal R).intValuation x)⁻¹ := by
  simp [ordMonoidWithZeroHom_eq_ord h, IsDiscreteValuationRing.intValuation_maximalIdeal]

lemma ordFrac_eq_intValuation {x : R} (h : x ≠ 0) : (ordFrac R) ((algebraMap R K) x) =
    ((IsDiscreteValuationRing.maximalIdeal R).intValuation x)⁻¹ := by
  rw [ordFrac_eq_ord R h,
      ordMonoidWithZeroHom_eq_intValuation (mem_nonZeroDivisors_of_ne_zero h)]

theorem ordFrac_eq_inverse_comp_valuation :
    ordFrac R = MonoidWithZeroHom.comp MonoidWithZero.inverse
    ((IsDiscreteValuationRing.maximalIdeal R).valuation K).toMonoidWithZeroHom := by
  ext a
  by_cases ha : a = 0
  · simp_all
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := R) a
  simp_all [ordFrac_eq_intValuation _, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDiscreteValuationRing.intValuation_maximalIdeal]

theorem ordFrac_eq_valuation_inv (x : K) :
    ordFrac R x = ((IsDiscreteValuationRing.maximalIdeal R).valuation K x)⁻¹ := by
  simp [ordFrac_eq_inverse_comp_valuation]

lemma ordFrac_irreducible
    {ϖ : R} (hϖ : Irreducible ϖ) : ordFrac R (algebraMap R K ϖ) = WithZero.exp 1 := by
  simp [ordFrac_eq_valuation_inv, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDiscreteValuationRing.intValuation_maximalIdeal,
    IsDiscreteValuationRing.addVal_uniformizer hϖ, ← WithZero.exp_eq_coe_ofAdd]

open IsDedekindDomain HeightOneSpectrum

lemma isUnit_iff_ordFrac_one_of_isDiscreteValuationRing {x : R} :
    IsUnit x ↔ ordFrac R (algebraMap R K x) = 1 := by
  simp [ordFrac_eq_valuation_inv, IsDiscreteValuationRing.maximalIdeal]

lemma mker_ordFrac_eq_isUnitSubmonoid :
    MonoidHom.mker (ordFrac R) = (IsUnit.submonoid R).map (algebraMap R K) := by
  rw [ordFrac_eq_inverse_comp_valuation, ← MonoidWithZeroHom.comap_mker,
      MonoidWithZeroHom.mker_inverse]
  exact IsDiscreteValuationRing.mker_valuation_eq_isUnitSubmonoid

/--
For `x y : R`, if `x + y ≠ 0` then `min (ordFrac R x) (ordFrac R y) ≤ ordFrac R (x + y)`. The
condition that `x + y ≠ 0` is used to guarantee that all the elements we're taking `ordFrac` of
are nonzero, meaning none of them will be `0` in `ℤᵐ⁰`. This allows us to use `ord_add` (which
uses the ordering on `ℕ∞`), since these orders correspond on non `⊤` elements.
-/
theorem ordFrac_add (x y : K) (h1 : x + y ≠ 0) :
    min (Ring.ordFrac R x) (Ring.ordFrac R y) ≤ Ring.ordFrac R (x + y) := by
  simp only [ordFrac_eq_valuation_inv]
  grw [Valuation.map_add, min_inv_inv_le]
  simpa [WithZero.pos_iff_ne_zero]

theorem associated_of_ordFrac_eq (x y : K)
    (h : ordFrac R x = ordFrac R y) : ∃ u : Rˣ, u • x = y := by
  rw [ordFrac_eq_valuation_inv, ordFrac_eq_valuation_inv, inv_inj] at h
  exact IsDiscreteValuationRing.associated_of_valuation_eq _ _ h

end IsDiscreteValuationRing

end Ring
