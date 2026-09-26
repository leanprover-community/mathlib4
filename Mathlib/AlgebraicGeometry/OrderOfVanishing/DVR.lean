/-
Copyright (c) 2026 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
module

public import Mathlib.AlgebraicGeometry.OrderOfVanishing.Basic

/-!
# Order of vanishing at a point whose local ring is a discrete valuation ring

This file collects the results about `AlgebraicGeometry.Scheme.ord`, the order of vanishing of
an element of the function field of a locally Noetherian integral scheme, that need the local
ring at the point in question to be a discrete valuation ring. The results that do not are in
`Mathlib/AlgebraicGeometry/OrderOfVanishing/Basic.lean`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory IsLocalRing Order TopologicalSpace WithZero

universe u

variable {X : Scheme.{u}}

namespace AlgebraicGeometry.Scheme

variable [IsIntegral X] [IsLocallyNoetherian X] {x : X}
  [IsDiscreteValuationRing (X.presheaf.stalk x)]

lemma ord_add {f g : X.functionField} (hfg : f + g ≠ 0) :
    min (ord f x) (ord g x) ≤ ord (f + g) x := by
  by_cases hf : f = 0
  · simp [hf]
  by_cases hg : g = 0
  · simp [hg]
  by_cases! hx : coheight x ≠ 1
  · simp [hx]
  rw [inf_le_iff, ord_le_ord_iff hx hx hf hfg, ord_le_ord_iff hx hx hg hfg]
  exact inf_le_iff.mp <| Ring.ordFrac_add (R := X.presheaf.stalk x) _ _ hfg

lemma ord_algebraMap_irreducible (hx : coheight x = 1) {ϖ : X.presheaf.stalk x}
    (hϖ : Irreducible ϖ) :
    ord (algebraMap (X.presheaf.stalk x) X.functionField ϖ) x = 1 := by
  have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  rw [ord_eq_iff hx (algebraMap_functionField_ne_zero hϖ.ne_zero),
    ← WithZero.exp_eq_coe_ofAdd]
  exact Ring.ordFrac_irreducible hϖ

lemma ord_zpow_algebraMap_irreducible (hx : coheight x = 1) {ϖ : X.presheaf.stalk x}
    (hϖ : Irreducible ϖ) (n : ℤ) :
    ord ((algebraMap (X.presheaf.stalk x) X.functionField ϖ) ^ n) x = n := by
  rw [ord_zpow (algebraMap_functionField_ne_zero hϖ.ne_zero),
    ord_algebraMap_irreducible hx hϖ, mul_one]

lemma mem_maximalIdeal_iff_one_le_ord (hx : coheight x = 1) {a : X.presheaf.stalk x}
    (ha : a ≠ 0) :
    a ∈ maximalIdeal (X.presheaf.stalk x) ↔
      1 ≤ ord (algebraMap (X.presheaf.stalk x) X.functionField a) x := by
  have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  have hnn := ord_algebraMap_nonneg ha
  have hiff : IsUnit a ↔ ord (algebraMap (X.presheaf.stalk x) X.functionField a) x = 0 := by
    rw [ord_eq_iff hx (algebraMap_functionField_ne_zero ha), ofAdd_zero]
    exact Ring.isUnit_iff_ordFrac_one_of_isDiscreteValuationRing (K := X.functionField)
  rw [mem_maximalIdeal, mem_nonunits_iff, hiff]
  omega

lemma mem_range_algebraMap_iff_ord_nonneg (hx : coheight x = 1) (f : X.functionField) :
    (∃ a, algebraMap (X.presheaf.stalk x) X.functionField a = f) ↔ 0 ≤ ord f x := by
  have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  constructor
  · rintro ⟨a, rfl⟩
    obtain rfl | ha := eq_or_ne a 0
    · simp
    · exact ord_algebraMap_nonneg ha
  · intro h
    obtain rfl | hf := eq_or_ne f 0
    · exact ⟨0, map_zero _⟩
    refine IsDiscreteValuationRing.exists_lift_of_le_one ?_
    have h1 : (1 : ℤᵐ⁰) ≤ Ring.ordFrac (X.presheaf.stalk x) f := by
      have h0 := (le_ord_iff hx hf (n := 0)).mp h
      rwa [ofAdd_zero, WithZero.coe_one] at h0
    rw [Ring.ordFrac_eq_valuation_inv] at h1
    exact (one_le_inv₀ (WithZero.pos_iff_ne_zero.mpr
      ((Valuation.ne_zero_iff _).mpr hf))).mp h1

/-- If an element of the local ring at a codimension-one point factors as a unit times the
`n`-th power of a uniformizer, then the rational function it determines has order of vanishing
`n`. This is the scheme-level form of `IsDiscreteValuationRing.addVal_def`. -/
lemma ord_algebraMap_eq_of_eq_unit_mul_pow (hx : coheight x = 1) (a : X.presheaf.stalk x)
    (u : (X.presheaf.stalk x)ˣ) {ϖ : X.presheaf.stalk x} (hϖ : Irreducible ϖ) (n : ℕ)
    (ha : a = u * ϖ ^ n) :
    ord (algebraMap (X.presheaf.stalk x) X.functionField a) x = n := by
  subst ha
  rw [map_mul, map_pow,
    ord_mul (algebraMap_functionField_ne_zero u.isUnit.ne_zero)
      (pow_ne_zero n (algebraMap_functionField_ne_zero hϖ.ne_zero)),
    ord_algebraMap_eq_zero_of_isUnit u.isUnit,
    ord_pow (algebraMap_functionField_ne_zero hϖ.ne_zero),
    ord_algebraMap_irreducible hx hϖ, mul_one, zero_add]

section BasicOpen

variable {U : X.Opens} [Nonempty U]

lemma one_le_ord_iff_notMem_basicOpen (w : U) (hw : coheight (w : X) = 1)
    [IsDiscreteValuationRing (X.presheaf.stalk (w : X))] {r : Γ(X, U)}
    (hr : algebraMap Γ(X, U) X.functionField r ≠ 0) :
    1 ≤ ord (algebraMap Γ(X, U) X.functionField r) (w : X) ↔ (w : X) ∉ X.basicOpen r := by
  rw [IsScalarTower.algebraMap_apply Γ(X, U) (X.presheaf.stalk (w : X)) X.functionField,
    ← mem_maximalIdeal_iff_one_le_ord hw (algebraMap_section_stalk_ne_zero w hr),
    X.mem_basicOpen' r w, ← IsLocalRing.notMem_maximalIdeal, not_not,
    TopCat.Presheaf.stalk_open_algebraMap]

lemma ord_eq_zero_of_mem_basicOpen (w : U)
    [IsDiscreteValuationRing (X.presheaf.stalk (w : X))] {r : Γ(X, U)}
    (hr : algebraMap Γ(X, U) X.functionField r ≠ 0) (hmem : (w : X) ∈ X.basicOpen r) :
    ord (algebraMap Γ(X, U) X.functionField r) (w : X) = 0 := by
  by_cases! hw : coheight (w : X) ≠ 1
  · simp [hw]
  have h1 := ord_algebraMap_section_nonneg w hr
  have h2 : ¬ 1 ≤ ord (algebraMap Γ(X, U) X.functionField r) (w : X) := fun h =>
    (one_le_ord_iff_notMem_basicOpen w hw hr).mp h hmem
  omega

end BasicOpen

end AlgebraicGeometry.Scheme
