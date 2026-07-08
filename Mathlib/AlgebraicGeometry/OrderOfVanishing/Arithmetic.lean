/-
Copyright (c) 2026 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
import Mathlib.AlgebraicGeometry.OrderOfVanishing
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Arithmetic of the order of vanishing

This file fleshes out the API for `AlgebraicGeometry.Scheme.ord`, the order of vanishing of a
rational function on a locally Noetherian integral scheme at a codimension-one point.

Contents:

* arithmetic: `ord_one`, `ord_inv`, `ord_zpow`, `ord_prod`;
* the dictionary between the local ring at a codimension-one point `x` with
  `IsDiscreteValuationRing 𝒪_{X,x}` and orders of vanishing: uniformizer powers have the
  expected order (`ord_zpow_algebraMap_irreducible`), germs have nonnegative order
  (`ord_algebraMap_nonneg`), the maximal ideal is cut out by `1 ≤ ord`
  (`mem_maximalIdeal_iff_one_le_ord`), and the image of `𝒪_{X,x}` in the function field is
  exactly the functions of nonnegative order (`mem_range_algebraMap_iff_ord_nonneg`);
* orders of vanishing of sections of a chart, where membership in the prime ideal attached to
  a point of an affine chart measures vanishing (`one_le_ord_algebraMap_section_iff` and
  companions);
* the prime ideal attached to a point of an affine chart (`IsAffineOpen.primeIdealOf`)
  remembers the coheight of the point (`IsAffineOpen.height_primeIdealOf`) and the
  specialization order (`IsAffineOpen.primeIdealOf_le_primeIdealOf_iff`).
-/

open AlgebraicGeometry Scheme CategoryTheory Order Opposite TopologicalSpace

universe u

variable {X : Scheme.{u}}

/--
On a scheme, a specialization between two points of coheight one is an equality: a strict
specialization would raise the coheight.
-/
lemma Specializes.eq_of_coheight_eq_one {z x : X}
    (h : z ⤳ x) (hz : coheight z = 1) (hx : coheight x = 1) : z = x := by
  have hxz : x ≤ z := h
  by_cases hzx : z ≤ x
  · exact (Specializes.antisymm h (hzx : x ⤳ z)).eq
  · have hbound := Order.coheight_add_one_le (lt_of_le_not_ge hxz hzx)
    rw [hz, hx] at hbound
    norm_num at hbound

/-!
### The prime ideal attached to a point of an affine chart

For an affine open `U` and a point `w : U`, the stalk at `w` is the localization of `Γ(X, U)`
at `hU.primeIdealOf w`; this prime remembers the coheight of `w` and the specialization order.
-/

namespace AlgebraicGeometry.IsAffineOpen

/-- The height of the prime ideal attached to a point of an affine open is the coheight of
the point: both compute the Krull dimension of the local ring. -/
lemma height_primeIdealOf {U : X.Opens} (hU : IsAffineOpen U) (w : U) :
    (hU.primeIdealOf w).asIdeal.height = coheight (w : X) := by
  haveI : Nonempty U := ⟨w⟩
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf w
  haveI := hU.isLocalization_stalk w
  have h1 : ringKrullDim (X.presheaf.stalk (w : X)) = (hU.primeIdealOf w).asIdeal.height :=
    IsLocalization.AtPrime.ringKrullDim_eq_height _ _
  have h2 := ringKrullDim_stalk_eq_coheight (w : X)
  rw [h1] at h2
  exact_mod_cast h2

/-- Specialization of points of an affine chart corresponds to inclusion of the attached
prime ideals. -/
lemma primeIdealOf_le_primeIdealOf_iff {U : X.Opens} (hU : IsAffineOpen U) (w x : U) :
    (hU.primeIdealOf w).asIdeal ≤ (hU.primeIdealOf x).asIdeal ↔ (w : X) ⤳ (x : X) := by
  constructor
  · intro h
    have := ((PrimeSpectrum.le_iff_specializes _ _).mp h).map hU.fromSpec.continuous
    rwa [hU.fromSpec_primeIdealOf, hU.fromSpec_primeIdealOf] at this
  · intro h
    refine (PrimeSpectrum.le_iff_specializes _ _).mpr
      (hU.fromSpec.isOpenEmbedding.toIsEmbedding.toIsInducing.specializes_iff.mp ?_)
    rw [hU.fromSpec_primeIdealOf, hU.fromSpec_primeIdealOf]
    exact h

/-- Distinct points of an affine chart have distinct attached prime ideals. -/
lemma primeIdealOf_injective {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Injective hU.primeIdealOf := fun w x h => by
  have h1 := hU.fromSpec_primeIdealOf w
  rw [h, hU.fromSpec_primeIdealOf] at h1
  exact Subtype.ext h1.symm

end AlgebraicGeometry.IsAffineOpen

namespace AlgebraicGeometry.Scheme

variable [IsIntegral X] [IsLocallyNoetherian X]

/-! ### Arithmetic of the order of vanishing -/

/-- The order of vanishing of `1` is zero. -/
@[simp]
lemma ord_one {z : X} : X.ord 1 z = 0 := by
  by_cases hz : coheight z = 1
  · have h := X.ord_mul hz (one_ne_zero (α := X.functionField)) one_ne_zero
    rw [mul_one] at h
    omega
  · exact X.ord_eq_zero_of_coheight_neq_one hz 1

/-- The order of vanishing of an inverse is the negative of the order. -/
lemma ord_inv {z : X} (hz : coheight z = 1) {f : X.functionField} (hf : f ≠ 0) :
    X.ord f⁻¹ z = - X.ord f z := by
  have h := X.ord_mul hz hf (inv_ne_zero hf)
  rw [mul_inv_cancel₀ hf, ord_one] at h
  omega

/-- The order of vanishing of an integer power is the multiple of the order. -/
lemma ord_zpow {z : X} (hz : coheight z = 1) {f : X.functionField} (hf : f ≠ 0) (n : ℤ) :
    X.ord (f ^ n) z = n * X.ord f z := by
  have h1 : X.ordHom z hz f = WithZero.exp (X.ord f z) := by
    rw [WithZero.exp_eq_coe_ofAdd]
    exact (X.ord_eq_iff hz hf).mp rfl
  rw [X.ord_eq_iff hz (zpow_ne_zero n hf), map_zpow₀, h1, ← WithZero.exp_zsmul,
    smul_eq_mul, WithZero.exp_eq_coe_ofAdd]

/-- The order of vanishing of a finite product of nonzero rational functions is the sum of
the orders. -/
lemma ord_prod {ι : Type*} (T : Finset ι) (F : ι → X.functionField)
    (hF : ∀ i ∈ T, F i ≠ 0) {z : X} (hz : coheight z = 1) :
    X.ord (∏ i ∈ T, F i) z = ∑ i ∈ T, X.ord (F i) z := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T haT ih =>
    have hprod : (∏ i ∈ T, F i) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i hi => hF i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert haT, Finset.sum_insert haT,
      X.ord_mul hz (hF a (Finset.mem_insert_self a T)) hprod,
      ih fun i hi => hF i (Finset.mem_insert_of_mem hi)]

/-! ### The order of vanishing at a point with discrete valuation ring stalk -/

omit [IsLocallyNoetherian X] in
/--
Nonzero elements of the local ring at a point map to nonzero rational functions.
-/
lemma algebraMap_functionField_ne_zero {x : X}
    {a : ↑(X.presheaf.stalk x)} (ha : a ≠ 0) :
    algebraMap (X.presheaf.stalk x) X.functionField a ≠ 0 :=
  (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr ha

variable {x : X} (hx : coheight x = 1) [IsDiscreteValuationRing (X.presheaf.stalk x)]

include hx

/--
The order of vanishing of an integer power of a uniformizer at `x` is the exponent.
-/
lemma ord_zpow_algebraMap_irreducible {ϖ : X.presheaf.stalk x} (hϖ : Irreducible ϖ) (n : ℤ) :
    X.ord ((algebraMap (X.presheaf.stalk x) X.functionField ϖ) ^ n) x = n := by
  have h1 : ordHom x hx (algebraMap (X.presheaf.stalk x) X.functionField ϖ) = WithZero.exp 1 :=
    Ring.ordFrac_irreducible hϖ
  rw [ord_eq_iff hx (zpow_ne_zero n (algebraMap_functionField_ne_zero hϖ.ne_zero)),
    map_zpow₀, h1, ← WithZero.exp_zsmul, smul_eq_mul, mul_one, WithZero.exp_eq_coe_ofAdd]

omit [IsDiscreteValuationRing (X.presheaf.stalk x)] in
/--
Rational functions coming from the local ring at `x` have nonnegative order of vanishing.
-/
lemma ord_algebraMap_nonneg {a : ↑(X.presheaf.stalk x)} (ha : a ≠ 0) :
    0 ≤ X.ord (algebraMap (X.presheaf.stalk x) X.functionField a) x := by
  haveI : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight hx
  rw [le_ord_iff hx (algebraMap_functionField_ne_zero ha), ofAdd_zero, WithZero.coe_one]
  exact Ring.ordFrac_ge_one_of_ne_zero ha

/--
A nonzero element of the local ring at a codimension one point `x` lies in the maximal ideal
iff the corresponding rational function vanishes at `x` to order at least one.
-/
lemma mem_maximalIdeal_iff_one_le_ord {a : ↑(X.presheaf.stalk x)} (ha : a ≠ 0) :
    a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ↔
      1 ≤ X.ord (algebraMap (X.presheaf.stalk x) X.functionField a) x := by
  have hnn := ord_algebraMap_nonneg hx ha
  have hiff : IsUnit a ↔
      X.ord (algebraMap (X.presheaf.stalk x) X.functionField a) x = 0 := by
    rw [ord_eq_iff hx (algebraMap_functionField_ne_zero ha), ofAdd_zero, WithZero.coe_one]
    exact Ring.isUnit_iff_ordFrac_one_of_isDiscreteValuationRing (K := X.functionField)
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hiff]
  omega

/--
The image of the local ring at a codimension-one point `x` in the function field consists
exactly of the rational functions of nonnegative order of vanishing at `x`.
-/
lemma mem_range_algebraMap_iff_ord_nonneg (z : X.functionField) :
    (∃ a, algebraMap (X.presheaf.stalk x) X.functionField a = z) ↔ (z ≠ 0 → 0 ≤ X.ord z x) := by
  constructor
  · rintro ⟨a, rfl⟩ hz
    exact ord_algebraMap_nonneg hx fun h => hz (by simp [h])
  · intro h
    rcases eq_or_ne z 0 with rfl | hz
    · exact ⟨0, map_zero _⟩
    refine IsDiscreteValuationRing.exists_lift_of_le_one ?_
    have h1 : (1 : WithZero (Multiplicative ℤ)) ≤ Ring.ordFrac (X.presheaf.stalk x) z := by
      have h0 := (le_ord_iff hx hz (n := 0)).mp (h hz)
      rwa [ofAdd_zero, WithZero.coe_one] at h0
    rw [Ring.ordFrac_eq_valuation_inv] at h1
    exact (one_le_inv₀ (WithZero.pos_iff_ne_zero.mpr
      ((Valuation.ne_zero_iff _).mpr hz))).mp h1

/-- The image in the function field of a unit of the local ring at a codimension-one point has
order of vanishing zero. -/
lemma ord_algebraMap_eq_zero_of_isUnit {a : X.presheaf.stalk x} (ha : IsUnit a) :
    X.ord (algebraMap (X.presheaf.stalk x) X.functionField a) x = 0 := by
  have hane : a ≠ 0 := ha.ne_zero
  refine le_antisymm ?_ (ord_algebraMap_nonneg hx hane)
  by_contra hlt
  push Not at hlt
  exact mem_nonunits_iff.mp ((mem_maximalIdeal_iff_one_le_ord hx hane).mpr (by omega)) ha

/-- The image in the function field of `u * ϖ ^ n`, for `u` a unit and `ϖ` irreducible in the
local ring at a codimension-one point, has order of vanishing `n`. -/
lemma ord_algebraMap_unit_mul_pow {ϖ : X.presheaf.stalk x} (hϖ : Irreducible ϖ)
    (u : (X.presheaf.stalk x)ˣ) (n : ℕ) :
    X.ord (algebraMap (X.presheaf.stalk x) X.functionField ((u : X.presheaf.stalk x) * ϖ ^ n))
      x = n := by
  have hne1 : algebraMap (X.presheaf.stalk x) X.functionField (u : X.presheaf.stalk x) ≠ 0 :=
    algebraMap_functionField_ne_zero u.isUnit.ne_zero
  have hne2 : (algebraMap (X.presheaf.stalk x) X.functionField ϖ) ^ n ≠ 0 :=
    pow_ne_zero n (algebraMap_functionField_ne_zero hϖ.ne_zero)
  rw [map_mul, map_pow, X.ord_mul hx hne1 hne2, ord_algebraMap_eq_zero_of_isUnit hx u.isUnit,
    ← zpow_natCast (algebraMap (X.presheaf.stalk x) X.functionField ϖ) n,
    ord_zpow_algebraMap_irreducible hx hϖ (n : ℤ), zero_add]

omit hx [IsDiscreteValuationRing (X.presheaf.stalk x)]

omit [IsLocallyNoetherian X] in
/-- The image of a germ in the function field does not depend on the point at which the germ
is taken. -/
lemma algebraMap_germ_eq_algebraMap_germ {W : X.Opens} {z : X} (hxW : x ∈ W) (hzW : z ∈ W)
    (s : Γ(X, W)) :
    algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ W x hxW s) =
      algebraMap (X.presheaf.stalk z) X.functionField (X.presheaf.germ W z hzW s) := by
  haveI : Nonempty W := ⟨⟨x, hxW⟩⟩
  rw [Scheme.algebraMap_germ_eq_germToFunctionField hxW,
    Scheme.algebraMap_germ_eq_germToFunctionField hzW]

/-!
### Orders of vanishing of sections of a chart

For a section `r : Γ(X, U)` with nonzero image in the function field, membership of `r` in the
prime attached to a codimension-one point `w` of the chart measures whether (the image of) `r`
vanishes at `w`. Stating these at subtype points `w : U` lets the ambient
`algebra_section_stalk` instances apply.
-/

variable {U : X.Opens} [Nonempty U]

omit [IsLocallyNoetherian X] in
/-- A section with nonzero image in the function field has nonzero germs. -/
lemma algebraMap_section_stalk_ne_zero (w : U) {r : Γ(X, U)}
    (hr : algebraMap Γ(X, U) X.functionField r ≠ 0) :
    algebraMap Γ(X, U) (X.presheaf.stalk (w : X)) r ≠ 0 := fun h0 =>
  hr (by rw [IsScalarTower.algebraMap_apply Γ(X, U) (X.presheaf.stalk (w : X)) X.functionField,
    h0, map_zero])

/-- Sections have nonnegative order of vanishing at every codimension-one point of the chart
with discrete valuation ring stalk. -/
lemma ord_algebraMap_section_nonneg (w : U) (hw : coheight (w : X) = 1)
    [IsDiscreteValuationRing (X.presheaf.stalk (w : X))] {r : Γ(X, U)}
    (hr : algebraMap Γ(X, U) X.functionField r ≠ 0) :
    0 ≤ X.ord (algebraMap Γ(X, U) X.functionField r) (w : X) := by
  rw [IsScalarTower.algebraMap_apply Γ(X, U) (X.presheaf.stalk (w : X)) X.functionField]
  exact ord_algebraMap_nonneg hw (algebraMap_section_stalk_ne_zero w hr)

/-- A section vanishes at a codimension-one point of an affine chart if and only if it lies
in the attached prime ideal. -/
lemma one_le_ord_algebraMap_section_iff (hU : IsAffineOpen U)
    (w : U) (hw : coheight (w : X) = 1)
    [IsDiscreteValuationRing (X.presheaf.stalk (w : X))] {r : Γ(X, U)}
    (hr : algebraMap Γ(X, U) X.functionField r ≠ 0) :
    1 ≤ X.ord (algebraMap Γ(X, U) X.functionField r) (w : X) ↔
      r ∈ (hU.primeIdealOf w).asIdeal := by
  haveI := hU.isLocalization_stalk w
  rw [IsScalarTower.algebraMap_apply Γ(X, U) (X.presheaf.stalk (w : X)) X.functionField,
    ← mem_maximalIdeal_iff_one_le_ord hw (algebraMap_section_stalk_ne_zero w hr)]
  exact IsLocalization.AtPrime.to_map_mem_maximal_iff _ (hU.primeIdealOf w).asIdeal r

/-- A section not in the prime attached to a codimension-one point of an affine chart has
order of vanishing zero there. -/
lemma ord_algebraMap_section_eq_zero_of_notMem (hU : IsAffineOpen U) (w : U)
    (hw : coheight (w : X) = 1) [IsDiscreteValuationRing (X.presheaf.stalk (w : X))]
    {r : Γ(X, U)} (hr : algebraMap Γ(X, U) X.functionField r ≠ 0)
    (hmem : r ∉ (hU.primeIdealOf w).asIdeal) :
    X.ord (algebraMap Γ(X, U) X.functionField r) (w : X) = 0 := by
  have h1 := ord_algebraMap_section_nonneg w hw hr
  have h2 : ¬ 1 ≤ X.ord (algebraMap Γ(X, U) X.functionField r) (w : X) := fun h =>
    hmem ((one_le_ord_algebraMap_section_iff hU w hw hr).mp h)
  omega

end AlgebraicGeometry.Scheme
