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
means that the two elements have the same minial polynomial over `K`.

## Main definitions

* `IsConjRoot`: `IsConjRoot K x y` means `y` is a conjugate root of `x` over `K`.

## Main results

* `IsConjRoot.iff_eq_algEquiv`: Let `L / K` be a normal field extension. For any two elements `x`
and `y` in `L`, `IsConjRoot K x y` is equivalent to the existence of an algebra equivalence
`σ : L ≃ₐ[K] L` such that `y = σ x`.
* `not_mem_iff_exist_ne`: Let `L / K` be a normal field extension. For any element `x` in `L`,

-/


open Polynomial minpoly IntermediateField

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
variable {K L : Type*} [Field K] [Field L] [Algebra K L]

variable (R) in
def IsConjRoot (x x' : A) : Prop := (minpoly R x) = (minpoly R x')

namespace IsConjRoot

theorem refl {x : A} : IsConjRoot R x x := rfl

theorem symm {x x' : A} (h : IsConjRoot R x x') : IsConjRoot R x' x := Eq.symm h

theorem trans {x x' x'': A} (h₁ : IsConjRoot R x x') (h₂ : IsConjRoot R x' x'') :
    IsConjRoot R x x'' := Eq.trans h₁ h₂

theorem of_minpoly_eq {x x' : A} (h : minpoly R x = minpoly R x') : IsConjRoot R x x' := h

theorem of_algEquiv (x : A) (s : A ≃ₐ[R] A) : IsConjRoot R x (s x) :=
  Eq.symm (minpoly.algEquiv_eq s x)

theorem of_algEquiv₂ (x : A) (s₁ s₂ : A ≃ₐ[R] A) : IsConjRoot R (s₁ x) (s₂ x) :=
  of_minpoly_eq <| (minpoly.algEquiv_eq s₂ x) ▸ (minpoly.algEquiv_eq s₁ x)

theorem exist_algEquiv [Normal K L] {x x': L} (h : IsConjRoot K x x') :
    ∃ σ : L ≃ₐ[K] L, x' = σ x := by
  obtain ⟨σ, hσ⟩ :=
    exists_algHom_of_splits_of_aeval (normal_iff.mp inferInstance) (h ▸ minpoly.aeval K x')
  exact ⟨AlgEquiv.ofBijective σ (σ.normal_bijective _ _ _), hσ.symm⟩

theorem iff_exist_algEquiv [Normal K L] {x x' : L} :
    IsConjRoot K x x' ↔ ∃ σ : L ≃ₐ[K] L, x' = σ x :=
  ⟨exist_algEquiv, fun ⟨_, h⟩ => h ▸ of_algEquiv _ _⟩

theorem iff_mem_aroots [CommRing A] [IsDomain A] [Algebra R A] {x x' : A} :
    IsConjRoot R x x' ↔ x' ∈ (minpoly R x).aroots A := sorry

theorem iff_mem_minpoly_rootSet [CommRing A] [IsDomain A] [Algebra R A] {x x' : A} :
    IsConjRoot R x x' ↔ x' ∈ (minpoly R x).rootSet A := sorry

theorem eq_of_degree_minpoly_eq_one {x x' : A} (h : IsConjRoot R x x')
    (g : degree (minpoly R x) = 1) : x = x' := by
  sorry

theorem eq_of_natDegree_minpoly_eq_one {x x' : A} (h : IsConjRoot R x x')
    (g : natDegree (minpoly R x) = 1) : x = x' := sorry

#check Polynomial.aroots
open Polynomial
theorem card_rootSet_eq_natDegree {K L} [Field K] [Field L] [Algebra K L] {p : K[X]}
    (hsep : p.Separable) (hp : p.Splits (algebraMap K L)) :
    Nat.card (p.rootSet L) = p.natDegree := sorry

-- seperable implies root number = degree
-- when degree >= 1, and split the aroot multiset and root set are not empty -- convert to Prod
-- Polynomial.nodup_aroots_iff_of_splits
-- Add `Polynomial.Splits` not `Normal`
#check Polynomial.card_rootSet_eq_natDegree
theorem not_mem_iff_exist_ne {x : L} (h : IsSeparable K x)
    (sp : (minpoly K x).Splits (algebraMap K L)) :
    x ∉ (⊥ : Subalgebra K L) ↔ ∃ x' : L, x ≠ x' ∧ IsConjRoot K x x' := by
  constructor
  · intro hbot

-- `should decide what is the definition when both x, x' are trancendental over R`

variable (R) in
theorem of_isScalarTower {S : Type*} [CommRing S] [Algebra R S] [Algebra S A]
    [IsScalarTower R S A] {x x' : A} (h : IsConjRoot S x x') : IsConjRoot R x x' := sorry
-- minpoly.aeval_of_isScalarTower

-- isIntegral_algHom_iff
theorem algHom_iff {B} [Ring B] [Algebra R B] {x x' : A} (f : A →ₐ[R] B)
    (hf : Function.Injective f) :
  IsConjRoot R (f x) (f x') ↔ IsConjRoot R x x' := sorry

theorem add_algebraMap {x x' : A} (r : R) (h : IsConjRoot R x x') :
    IsConjRoot R (x + algebraMap R A r) (x' + algebraMap R A r) := sorry
-- minpoly.add_algebraMap
-- `should decide what is the definition when both x, x' are trancendental over R`

/-

theorem eq_of_isConjRoot_algebraMap {r : R} {x : A} (h : IsConjRoot R x (algebraMap R A r)) :
    x = algebraMap R A r := sorry

theorem neg {x x' : A} (r : R) (h : IsConjRoot R x x') :  IsConjRoot R (-x) (-x') := sorry

theorem sub_algebraMap {x x' : A} (r : R) (h : IsConjRoot R x x') :
    IsConjRoot R (x - algebraMap R A r) (x' - algebraMap R A r) := sorry

theorem smul {x x' : A} (r : R) (h : IsConjRoot R x x') :  IsConjRoot R (r • x) (r • x') := sorry

variable {K} in
theorem isIntegral {x x' : L} (hx : IsIntegral K x) (h : IsConjRoot K x x') :
    IsIntegral K x' := by sorry

theorem iff_eq_zero {x : A} : IsConjRoot R 0 x ↔ x = 0 := sorry

theorem ne_zero {x x' : A} (hx : x ≠ 0) (h : IsConjRoot R x x') : x' ≠ 0 := sorry
-/
end IsConjRoot
