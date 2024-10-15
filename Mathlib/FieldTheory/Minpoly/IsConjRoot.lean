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
* `not_mem_iff_exist_ne`: Let `L / K` be a normal field extension. For any element `x` in `L`, if
the minimal polynomial of `x` splits in `L`, then `x` is not in the `K` iff there exists a different
conjugate root of `x` over `K`.
## TODO
Add `IsConjRoot.smul` stating that if `x` and `y` are conjugate roots, then so are `r • x` and
`r • y`.

## Tags
conjugate root, minimal polynomial
-/


open Polynomial minpoly IntermediateField

variable {R S A : Type*} [CommRing R] [CommRing S] [Ring A] [Algebra R A] [Algebra R S]
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra K A]

variable (R) in
def IsConjRoot (x x' : A) : Prop := (minpoly R x) = (minpoly R x')

namespace IsConjRoot

theorem refl {x : A} : IsConjRoot R x x := rfl

theorem symm {x x' : A} (h : IsConjRoot R x x') : IsConjRoot R x' x := Eq.symm h

theorem trans {x x' x'': A} (h₁ : IsConjRoot R x x') (h₂ : IsConjRoot R x' x'') :
    IsConjRoot R x x'' := Eq.trans h₁ h₂

theorem _root_.isConjRoot_def {x x' : A} : IsConjRoot R x x' ↔ minpoly R x = minpoly R x' := Iff.rfl

theorem aeval_eq_zero {x x' : A} (h : IsConjRoot R x x') : aeval x' (minpoly R x) = 0 :=
  h ▸ minpoly.aeval R x'

theorem of_aeval_eq_zero [IsDomain A] [Nontrivial A] {x x' : A} (hx : IsIntegral K x)
    (h : aeval x' (minpoly K x) = 0) : IsConjRoot K x x' :=
  minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hx) h (minpoly.monic hx)

theorem iff_aeval_eq_zero [IsDomain A] [Nontrivial A] {x x' : A}
    (h : IsIntegral K x) : IsConjRoot K x x' ↔ aeval x' (minpoly K x) = 0 :=
  ⟨aeval_eq_zero, of_aeval_eq_zero h⟩

theorem of_algEquiv (x : A) (s : A ≃ₐ[R] A) : IsConjRoot R x (s x) :=
  Eq.symm (minpoly.algEquiv_eq s x)

theorem of_algEquiv₂ (x : A) (s₁ s₂ : A ≃ₐ[R] A) : IsConjRoot R (s₁ x) (s₂ x) :=
  isConjRoot_def.mpr <| (minpoly.algEquiv_eq s₂ x) ▸ (minpoly.algEquiv_eq s₁ x)

theorem exist_algEquiv [Normal K L] {x x': L} (h : IsConjRoot K x x') :
    ∃ σ : L ≃ₐ[K] L, σ x = x' := by
  obtain ⟨σ, hσ⟩ :=
    exists_algHom_of_splits_of_aeval (normal_iff.mp inferInstance) (h ▸ minpoly.aeval K x')
  exact ⟨AlgEquiv.ofBijective σ (σ.normal_bijective _ _ _), hσ⟩

theorem iff_exist_algEquiv [Normal K L] {x x' : L} :
    IsConjRoot K x x' ↔ ∃ σ : L ≃ₐ[K] L, σ x = x' :=
  ⟨exist_algEquiv, fun ⟨_, h⟩ => h ▸ of_algEquiv _ _⟩

theorem iff_mem_aroots {A} [CommRing A] [IsDomain A] [Nontrivial A] [Algebra K A] {x x' : A}
    (h : IsIntegral K x) : IsConjRoot K x x' ↔ x' ∈ (minpoly K x).aroots A := by
  rw [Polynomial.mem_aroots, iff_aeval_eq_zero h]
  simp only [iff_and_self]
  exact fun _ => minpoly.ne_zero h

theorem iff_mem_minpoly_rootSet {A} [CommRing A] [IsDomain A] [Algebra K A] {x x' : A}
    (h : IsIntegral K x) : IsConjRoot K x x' ↔ x' ∈ (minpoly K x).rootSet A :=
  (iff_mem_aroots h).trans (by simp [rootSet])

theorem isIntegral {x x' : A} (hx : IsIntegral R x) (h : IsConjRoot R x x') :
    IsIntegral R x' :=
  ⟨minpoly R x, minpoly.monic hx, h ▸ minpoly.aeval R x'⟩

/--
A general form of `IsConjRoot.eq_of_isConjRoot_algebraMap`, only assuming `Nontrivial R`,
`NoZeroSMulDivisors R A` and `Function.Injective (algebraMap R A)` instead of `Field R`.
-/
theorem eq_of_isConjRoot_algebraMap' [Nontrivial R] {A} [CommRing A] [IsDomain A] [Algebra R A]
    [NoZeroSMulDivisors R A] {r : R} {x : A} (h : IsConjRoot R x (algebraMap R A r))
    (hf : Function.Injective (algebraMap R A)) : x = algebraMap R A r := by
  rw [IsConjRoot, minpoly.eq_X_sub_C_of_algebraMap_inj _ hf] at h
  have : x ∈ (X - C r).aroots A := by
    rw [mem_aroots]
    simp [X_sub_C_ne_zero, h ▸ minpoly.aeval R x]
  simpa [aroots_X_sub_C] using this

theorem eq_of_isConjRoot_algebraMap {A} [CommRing A] [IsDomain A] [Nontrivial A] [Algebra K A]
    {r : K} {x : A} (h : IsConjRoot K x (algebraMap K A r)) : x = algebraMap K A r :=
  eq_of_isConjRoot_algebraMap' h (algebraMap K A).injective

/--
A general form of `IsConjRoot.eq_zero`, only assuming `Nontrivial R`,
`NoZeroSMulDivisors R A` and `Function.Injective (algebraMap R A)` instead of `Field R`.
-/
theorem eq_zero' [Nontrivial R] {A} [CommRing A] [IsDomain A] [Algebra R A]
    [NoZeroSMulDivisors R A] {x : A} (h : IsConjRoot R x 0)
    (hf : Function.Injective (algebraMap R A)) : x = 0 :=
  (algebraMap R A).map_zero ▸ (eq_of_isConjRoot_algebraMap' ((algebraMap R A).map_zero ▸ h) hf)

theorem eq_zero {A} [CommRing A] [IsDomain A] [Algebra K A] {x : A}
    (h : IsConjRoot K x 0) : x = 0 :=
  eq_zero' h (algebraMap K A).injective

/--
A general form of `IsConjRoot.iff_eq_zero'`, only assuming `Nontrivial R`,
`NoZeroSMulDivisors R A` and `Function.Injective (algebraMap R A)` instead of `Field R`.
-/
theorem iff_eq_zero' {A} [Nontrivial R] [CommRing A] [IsDomain A] [Algebra R A]
    [NoZeroSMulDivisors R A] {x : A} (hf : Function.Injective (algebraMap R A)) :
    IsConjRoot R x 0 ↔ x = 0 :=
  ⟨fun h => eq_zero' h hf, fun h => h.symm ▸ rfl⟩

theorem iff_eq_zero {A} [CommRing A] [IsDomain A] [Algebra K A]
    {x : A} :
    IsConjRoot K x 0 ↔ x = 0 :=
  iff_eq_zero' (algebraMap K A).injective

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

theorem not_mem_iff_exist_ne {x : L} (h : IsSeparable K x)
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
      ⟨fun ⟨⟨x', hx'⟩, hne⟩ => ⟨x', ⟨hne.symm, (iff_mem_minpoly_rootSet h.isIntegral).mpr hx'⟩⟩,
          fun ⟨x', hne, hx'⟩ => ⟨⟨x', (iff_mem_minpoly_rootSet h.isIntegral).mp hx'⟩, hne.symm⟩⟩

variable (R) in
theorem of_isScalarTower {A} [CommRing A] [Algebra K A] [Algebra L A] [IsScalarTower K L A]
    [IsDomain A] [Nontrivial A] {x x' : A} (hx : IsIntegral K x) (h : IsConjRoot L x x') :
    IsConjRoot K x x' :=
  of_aeval_eq_zero hx <| minpoly.aeval_of_isScalarTower K x x' (aeval_eq_zero h)

theorem algHom_iff {B} [Ring B] [Algebra R B] {x x' : A} (f : A →ₐ[R] B)
    (hf : Function.Injective f) :
    IsConjRoot R (f x) (f x') ↔ IsConjRoot R x x' := by
  rw [isConjRoot_def, isConjRoot_def, algHom_eq f hf, algHom_eq f hf]

theorem add_algebraMap {A} [CommRing A] [Algebra K A] {x x' : A} (r : K) (h : IsConjRoot K x x') :
    IsConjRoot K (x + algebraMap K A r) (x' + algebraMap K A r) := by
  rw [isConjRoot_def, minpoly.add_algebraMap x r, minpoly.add_algebraMap x' r, h]

theorem sub_algebraMap {A} [CommRing A] [Algebra K A] {x x' : A} (r : K) (h : IsConjRoot K x x') :
    IsConjRoot K (x - algebraMap K A r) (x' - algebraMap K A r) := by
  simpa only [sub_eq_add_neg, map_neg] using add_algebraMap (-r) h

theorem neg {A} [CommRing A] [Algebra K A] {x x' : A} (h : IsConjRoot K x x') :
    IsConjRoot K (-x) (-x') := by
  rw [isConjRoot_def, minpoly.neg x, minpoly.neg x', h]

end IsConjRoot
