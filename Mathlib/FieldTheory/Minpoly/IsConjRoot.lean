/-
Copyright (c) 2024 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.FieldTheory.Adjoin
import Mathlib.FieldTheory.Normal

/-!
# Conjugate roots

This file specialize to the property of conjugate roots. Being conjuagte root over some ring `K`
means that the two elements have the same minimal polynomial over `K`.

## Main definitions

* `IsConjRoot`: `IsConjRoot K x y` means `y` is a conjugate root of `x` over `K`.

## Main results

* `IsConjRoot.iff_eq_algEquiv`: Let `L / K` be a normal field extension. For any two elements `x`
and `y` in `L`, `IsConjRoot K x y` is equivalent to the existence of an algebra equivalence
`σ : L ≃ₐ[K] L` such that `y = σ x`.
* `not_mem_iff_exists_ne`: Let `L / K` be a normal field extension. For any element `x` in `L`, if
the minimal polynomial of `x` splits in `L`, then `x` is not in the `K` iff there exists a different
conjugate root of `x` over `K`.

## TODO
Add `IsConjRoot.smul` stating that if `x` and `y` are conjugate roots, then so are `r • x` and
`r • y`.

## Tags
conjugate root, minimal polynomial

1. name -- finished
2. condition
3. add docstring
4. check head statement
-/


open Polynomial minpoly IntermediateField

variable {R S A : Type*} [CommRing R] [CommRing S] [Ring A] [Algebra R A] [Algebra R S]
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra K A]

variable (R) in
def IsConjRoot (x x' : A) : Prop := (minpoly R x) = (minpoly R x')

theorem isConjRoot_def {x x' : A} : IsConjRoot R x x' ↔ minpoly R x = minpoly R x' := Iff.rfl

namespace IsConjRoot

theorem refl {x : A} : IsConjRoot R x x := rfl

theorem symm {x x' : A} (h : IsConjRoot R x x') : IsConjRoot R x' x := Eq.symm h

theorem trans {x x' x'': A} (h₁ : IsConjRoot R x x') (h₂ : IsConjRoot R x' x'') :
    IsConjRoot R x x'' := Eq.trans h₁ h₂

theorem add_algebraMap {A} [CommRing A] [Algebra K A] {x x' : A} (r : K) (h : IsConjRoot K x x') :
    IsConjRoot K (x + algebraMap K A r) (x' + algebraMap K A r) := by
  rw [isConjRoot_def, minpoly.add_algebraMap x r, minpoly.add_algebraMap x' r, h]

theorem sub_algebraMap {A} [CommRing A] [Algebra K A] {x x' : A} (r : K) (h : IsConjRoot K x x') :
    IsConjRoot K (x - algebraMap K A r) (x' - algebraMap K A r) := by
  simpa only [sub_eq_add_neg, map_neg] using add_algebraMap (-r) h

theorem neg {A} [CommRing A] [Algebra K A] {x x' : A} (h : IsConjRoot K x x') :
    IsConjRoot K (-x) (-x') := by
  rw [isConjRoot_def, minpoly.neg x, minpoly.neg x', h]

theorem aeval_eq_zero {x x' : A} (h : IsConjRoot R x x') : aeval x' (minpoly R x) = 0 :=
  h ▸ minpoly.aeval R x'

end IsConjRoot

open IsConjRoot

/--
A general form of `isConjRoot_algHom_iff`, only assuming `Function.Injective f`,
instead of `DivisionRing A`.
-/
theorem isConjRoot_algHom_iff' {B} [Ring B] [Algebra R B] {x x' : A} (f : A →ₐ[R] B)
    (hf : Function.Injective f) : IsConjRoot R (f x) (f x') ↔ IsConjRoot R x x' := by
  rw [isConjRoot_def, isConjRoot_def, algHom_eq f hf, algHom_eq f hf]

theorem isConjRoot_algHom_iff {A} [DivisionRing A] [Algebra R A] {B} [Ring B] [Nontrivial B]
    [Algebra R B] {x x' : A} (f : A →ₐ[R] B) : IsConjRoot R (f x) (f x') ↔ IsConjRoot R x x' :=
  isConjRoot_algHom_iff' f f.injective

theorem isConjRoot_of_aeval_eq_zero [IsDomain A] [Nontrivial A] {x x' : A} (hx : IsIntegral K x)
    (h : aeval x' (minpoly K x) = 0) : IsConjRoot K x x' :=
  minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hx) h (minpoly.monic hx)

theorem isConjRoot_iff_aeval_eq_zero [IsDomain A] [Nontrivial A] {x x' : A}
    (h : IsIntegral K x) : IsConjRoot K x x' ↔ aeval x' (minpoly K x) = 0 :=
  ⟨IsConjRoot.aeval_eq_zero, isConjRoot_of_aeval_eq_zero h⟩

@[simp]
theorem isConjRoot_of_algEquiv (x : A) (s : A ≃ₐ[R] A) : IsConjRoot R x (s x) :=
  Eq.symm (minpoly.algEquiv_eq s x)

@[simp]
theorem isConjRoot_of_algEquiv₂ (x : A) (s₁ s₂ : A ≃ₐ[R] A) : IsConjRoot R (s₁ x) (s₂ x) :=
  isConjRoot_def.mpr <| (minpoly.algEquiv_eq s₂ x) ▸ (minpoly.algEquiv_eq s₁ x)

theorem IsConjRoot.exists_algEquiv [Normal K L] {x x': L} (h : IsConjRoot K x x') :
    ∃ σ : L ≃ₐ[K] L, σ x = x' := by
  obtain ⟨σ, hσ⟩ :=
    exists_algHom_of_splits_of_aeval (normal_iff.mp inferInstance) (h ▸ minpoly.aeval K x')
  exact ⟨AlgEquiv.ofBijective σ (σ.normal_bijective _ _ _), hσ⟩

theorem isConjRoot_iff_exists_algEquiv [Normal K L] {x x' : L} :
    IsConjRoot K x x' ↔ ∃ σ : L ≃ₐ[K] L, σ x = x' :=
  ⟨exists_algEquiv, fun ⟨_, h⟩ => h ▸ isConjRoot_of_algEquiv _ _⟩

theorem IsConjRoot.of_isScalarTower {A} [CommRing A] [Algebra K A] [Algebra L A]
    [IsScalarTower K L A] [IsDomain A] [Nontrivial A] {x x' : A} (hx : IsIntegral K x)
    (h : IsConjRoot L x x') : IsConjRoot K x x' :=
  isConjRoot_of_aeval_eq_zero hx <| minpoly.aeval_of_isScalarTower K x x' (aeval_eq_zero h)

theorem isConjRoot_iff_mem_aroots {A} [CommRing A] [IsDomain A] [Nontrivial A] [Algebra K A]
    {x x' : A} (h : IsIntegral K x) : IsConjRoot K x x' ↔ x' ∈ (minpoly K x).aroots A := by
  rw [Polynomial.mem_aroots, isConjRoot_iff_aeval_eq_zero h]
  simp only [iff_and_self]
  exact fun _ => minpoly.ne_zero h

theorem isConjRoot_iff_mem_minpoly_rootSet {A} [CommRing A] [IsDomain A] [Algebra K A] {x x' : A}
    (h : IsIntegral K x) : IsConjRoot K x x' ↔ x' ∈ (minpoly K x).rootSet A :=
  (isConjRoot_iff_mem_aroots h).trans (by simp [rootSet])

namespace IsConjRoot

theorem isIntegral {x x' : A} (hx : IsIntegral R x) (h : IsConjRoot R x x') :
    IsIntegral R x' :=
  ⟨minpoly R x, minpoly.monic hx, h ▸ minpoly.aeval R x'⟩

/--
A general form of `IsConjRoot.eq_of_isConjRoot_algebraMap`, only assuming `Nontrivial R`,
`NoZeroSMulDivisors R A` and `Function.Injective (algebraMap R A)` instead of `Field R`.
-/
theorem eq_algebraMap' [Nontrivial R] {A} [CommRing A] [IsDomain A] [Algebra R A]
    [NoZeroSMulDivisors R A] {r : R} {x : A} (h : IsConjRoot R x (algebraMap R A r))
    (hf : Function.Injective (algebraMap R A)) : x = algebraMap R A r := by
  rw [IsConjRoot, minpoly.eq_X_sub_C_of_algebraMap_inj _ hf] at h
  have : x ∈ (X - C r).aroots A := by
    rw [mem_aroots]
    simp [X_sub_C_ne_zero, h ▸ minpoly.aeval R x]
  simpa [aroots_X_sub_C] using this

theorem eq_algebraMap {A} [CommRing A] [IsDomain A] [Nontrivial A] [Algebra K A]
    {r : K} {x : A} (h : IsConjRoot K x (algebraMap K A r)) : x = algebraMap K A r :=
  eq_algebraMap' h (algebraMap K A).injective

/--
A general form of `IsConjRoot.eq_zero`, only assuming `Nontrivial R`,
`NoZeroSMulDivisors R A` and `Function.Injective (algebraMap R A)` instead of `Field R`.
-/
theorem eq_zero' [Nontrivial R] {A} [CommRing A] [IsDomain A] [Algebra R A]
    [NoZeroSMulDivisors R A] {x : A} (h : IsConjRoot R x 0)
    (hf : Function.Injective (algebraMap R A)) : x = 0 :=
  (algebraMap R A).map_zero ▸ (eq_algebraMap' ((algebraMap R A).map_zero ▸ h) hf)

theorem eq_zero {A} [CommRing A] [IsDomain A] [Algebra K A] {x : A}
    (h : IsConjRoot K x 0) : x = 0 :=
  eq_zero' h (algebraMap K A).injective

end IsConjRoot

/--
A general form of `IsConjRoot.iff_eq_zero'`, only assuming `Nontrivial R`,
`NoZeroSMulDivisors R A` and `Function.Injective (algebraMap R A)` instead of `Field R`.
-/
theorem isConjRoot_zero_iff_eq_zero' {A} [Nontrivial R] [CommRing A] [IsDomain A] [Algebra R A]
    [NoZeroSMulDivisors R A] {x : A} (hf : Function.Injective (algebraMap R A)) :
    IsConjRoot R x 0 ↔ x = 0 :=
  ⟨fun h => eq_zero' h hf, fun h => h.symm ▸ rfl⟩

@[simp]
theorem isConjRoot_zero_iff_eq_zero {A} [CommRing A] [IsDomain A] [Algebra K A]
    {x : A} :
    IsConjRoot K x 0 ↔ x = 0 :=
  isConjRoot_zero_iff_eq_zero' (algebraMap K A).injective

namespace IsConjRoot

/--
A general form of `IsConjRoot.ne_zero'`, only assuming `Nontrivial R`,
`NoZeroSMulDivisors R A` and `Function.Injective (algebraMap R A)` instead of `Field R`.
-/
theorem ne_zero' {A} [Nontrivial R] [CommRing A] [IsDomain A] [Algebra R A]
    [NoZeroSMulDivisors R A] {x x' : A} (hx : x ≠ 0) (h : IsConjRoot R x x')
    (hf : Function.Injective (algebraMap R A)) : x' ≠ 0 :=
  fun h' => hx (eq_zero' (h' ▸ h) hf)

theorem ne_zero {A} [CommRing A] [IsDomain A] [Algebra K A] {x x' : A}
    (hx : x ≠ 0) (h : IsConjRoot K x x') : x' ≠ 0 :=
  ne_zero' hx h (algebraMap K A).injective

end IsConjRoot

theorem not_mem_iff_exists_ne_and_isConjRoot {x : L} (h : IsSeparable K x)
    (sp : (minpoly K x).Splits (algebraMap K L)) :
    x ∉ (⊥ : Subalgebra K L) ↔ ∃ x' : L, x ≠ x' ∧ IsConjRoot K x x' := by
  calc
    _ ↔ 2 ≤ (minpoly K x).natDegree := (minpoly.two_le_natDegree_iff h.isIntegral).symm
    _ ↔ 2 ≤ Fintype.card ((minpoly K x).rootSet L) :=
      (Polynomial.card_rootSet_eq_natDegree h sp) ▸ Iff.rfl
    _ ↔ Nontrivial ((minpoly K x).rootSet L) := Fintype.one_lt_card_iff_nontrivial
    _ ↔ ∃ x' : ((minpoly K x).rootSet L), ↑x' ≠ x :=
      (nontrivial_iff_exists_ne ⟨x, mem_rootSet.mpr ⟨minpoly.ne_zero h.isIntegral,
          minpoly.aeval K x⟩⟩).trans ⟨fun ⟨x', hx'⟩ => ⟨x', Subtype.coe_ne_coe.mpr hx'⟩,
          fun ⟨x', hx'⟩ => ⟨x', Subtype.coe_ne_coe.mp hx'⟩⟩
    _ ↔ _ :=
      ⟨fun ⟨⟨x', hx'⟩, hne⟩ => ⟨x', ⟨hne.symm,
          (isConjRoot_iff_mem_minpoly_rootSet h.isIntegral).mpr hx'⟩⟩,
          fun ⟨x', hne, hx'⟩ => ⟨⟨x',
          (isConjRoot_iff_mem_minpoly_rootSet h.isIntegral).mp hx'⟩, hne.symm⟩⟩
