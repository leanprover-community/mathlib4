/-
Copyright (c) 2025 Bernhard Reinke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bernhard Reinke, Ray Shang
-/

module

public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Ring.Associator
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.Data.DFinsupp.BigOperators

/-!
# Category algebra of a linear category

This file defines the category algebra of a preadditive category `C` that is linear over a
commutative semiring `R`.

## Main definitions

- `CategoryAlgebra R C`: the category algebra of `C` over `R`, defined
  as the direct sum of the morphism spaces `X ⟶ Y` over all pairs `(X, Y) : C × C`.
- `CategoryAlgebra.of X Y f`: The canonical  `R`-linear inclusion of an element `f : X ⟶ Y`
   into `CategoryAlgebra R C`.
- `Hom R C A`: a structure for a composition-respecting family of
  `R`-linear maps from the Hom sets of `C` to a non-unital `R`-algebra `A`
- `lift F`: the canonical map from `CategoryAlgebra R C` to
   a non-unital `R`-algebra `A`, lifted from `F : Hom R C A`.
- `UnitalHom R C A`: a structure for a composition-respecting family of
  `R`-linear maps from the Hom sets of `C` to `R`-algebra `A`, extending `Hom R C A`
- `unitalLift F`: the canonical map from `CategoryAlgebra R C` to
   a `R`-algebra `A`, lifted from `F : UnitalHom R C A`.

## Main results

- `CategoryAlgebra R C` is a non-unital `R`-algebra.
- If `C` has finitely many objects (`Fintype C`), then `CategoryAlgebra R C`
  is a `R`-algebra.
- `CategoryTheory.Linear.CategoryAlgebra.liftEquiv`: `Hom R C A` and `CategoryAlgebra R C →ₙₐ[R] A`
  are equivalent types.
- `CategoryTheory.Linear.CategoryAlgebra.unitalLiftEquiv`: `Hom R C A` and
  `CategoryAlgebra R C →ₐ[R] A` are equivalent types.

## Implementation notes

A non-unital `R`-algebra `A` is the following:
   ```lean
   variable [CommSemiring R] [NonUnitalSemiring A]
   variable [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
   ```
This convention follows the convention declared in the implementation notes
of  `Mathlib/Algebra/Algebra/Defs.lean`.

-/

@[expose] public section

universe w' w v u

namespace CategoryTheory.Linear

open DirectSum
open CategoryTheory.Preadditive

/-- The category algebra constructed from a commutative semiring `R` and an `R`-linear category `C`.
By using `abbrev`, the category algebra inherits all module properties directly from
the underlying direct sum. -/
@[nolint unusedArguments]
abbrev CategoryAlgebra (R : Type w) (C : Type u) [CommSemiring R] [Category.{v} C] [Preadditive C]
    [Linear R C] := ⨁ (x : C × C), x.1 ⟶ x.2

namespace CategoryAlgebra

variable {R : Type w} [CommSemiring R] {C : Type u} [Category.{v} C] [Preadditive C]
  [Linear R C] [DecidableEq C]

/-- The canonical inclusion of a morphism `f : a ⟶ b` into the category algebra. -/
protected def of (x y : C) : (x ⟶ y) →ₗ[R] CategoryAlgebra R C :=
    DirectSum.lof R (C × C) (fun x ↦ x.1 ⟶ x.2) (x, y)

/-- Two additive homomorphisms out of the category algebra are equal if they agree on
all canonical inclusions of morphisms. -/
@[ext 10000]
theorem addHom_ext {γ : Type w'} [AddZeroClass γ] {f g : CategoryAlgebra R C →+ γ}
    (h : ∀ (x y : C) (f' : x ⟶ y), f (CategoryAlgebra.of x y f') = g (CategoryAlgebra.of x y f')) :
    f = g := DFinsupp.addHom_ext (fun x => h x.1 x.2)

/-- The canonical inclusion `of a b f` is definitionally equal to the single entry
in the direct sum at index `(a, b)` with value `f`. -/
theorem of_eq_single (x y : C) (f : x ⟶ y) :
    (CategoryAlgebra.of x y f : CategoryAlgebra R C) =
    DFinsupp.single (x,y) f := by rfl

/-- A helper function to define multiplication on the category algebra.
Returns the composition of two morphisms if their intermediate objects are strictly equal,
and `0` otherwise. -/
def comp₀ (x y z w : C) : (x ⟶ y) →+ (z ⟶ w) →+ (x ⟶ w) :=
  if h : y = z then
    { toFun := fun f ↦ compHom (f ≫ eqToHom h)
      map_add' := fun f₁ f₂ ↦ by simp
      map_zero' := by simp }
  else
    0

/-- `comp₀` satisfies a generalized associativity relation across composable objects. -/
theorem comp₀_assoc (x₁ y₁ x₂ y₂ x₃ y₃ : C) (f : x₁ ⟶ y₁) (g : x₂ ⟶ y₂) (h : x₃ ⟶ y₃) :
    ((comp₀ x₁ y₂ x₃ y₃) (((comp₀ x₁ y₁ x₂ y₂) f) g)) h =
    ((comp₀ x₁ y₁ x₂ y₃) f) (((comp₀ x₂ y₂ x₃ y₃) g) h) := by
  by_cases h₁₂ : y₁ = x₂ <;>
    by_cases h₂₃ : y₂ = x₃ <;>
    simp [comp₀, h₁₂, h₂₃, compHom, Preadditive.leftComp]


/-- The multiplication on the category algebra, defined by linearly extending
the composition of morphisms across the direct sum. -/
def mul' : CategoryAlgebra R C →+ CategoryAlgebra R C →+ CategoryAlgebra R C :=
  DFinsupp.sumAddHom₂ (fun x y ↦ AddMonoidHom.compr₂
  (comp₀ x.1 x.2 y.1 y.2) (CategoryAlgebra.of x.1 y.2).toAddMonoidHom)

instance : Mul (CategoryAlgebra R C) := ⟨fun f g => mul' f g⟩

/-- Unfold lemma for the multiplication operation on the category algebra. -/
theorem mul_def (f g : CategoryAlgebra R C) :
    f * g = DFinsupp.sumAddHom₂ (fun x y ↦ AddMonoidHom.compr₂
    (comp₀ x.1 x.2 y.1 y.2) (CategoryAlgebra.of x.1 y.2).toAddMonoidHom) f g := rfl

instance : NonUnitalNonAssocSemiring (CategoryAlgebra R C) where
  left_distrib := fun x y z => by simp [mul_def]
  right_distrib := fun x y z => by simp [mul_def]
  zero_mul := fun x => by simp [mul_def]
  mul_zero := fun x => by simp [mul_def]

/-- The product of two basis elements evaluates to their composition (via `comp₀`) included
back into the category algebra. -/
theorem mul_of (x₁ y₁ x₂ y₂ : C) (f : x₁ ⟶ y₁) (g : x₂ ⟶ y₂) :
    (CategoryAlgebra.of x₁ y₁ f) * (CategoryAlgebra.of x₂ y₂ g : (CategoryAlgebra R C)) =
    CategoryAlgebra.of x₁ y₂ (comp₀ x₁ y₁ x₂ y₂ f g) := by
  rw [mul_def, CategoryAlgebra.of_eq_single, CategoryAlgebra.of_eq_single,
     DFinsupp.sumAddHom₂_single]
  rfl

/-- Associativity of multiplication on the category algebra, expressed as an equality
of trilinear maps. -/
theorem mul_assoc' :
    AddMonoidHom.mulLeft₃ (R := (CategoryAlgebra R C)) = AddMonoidHom.mulRight₃ := by
  ext x₁ y₁ f x₂ y₂ g x₃ y₃ h i
  change (((CategoryAlgebra.of x₁ y₁ f * CategoryAlgebra.of x₂ y₂ g)
          * CategoryAlgebra.of x₃ y₃ h : CategoryAlgebra R C) i)
          = ((CategoryAlgebra.of x₁ y₁ f * (CategoryAlgebra.of x₂ y₂ g
          * CategoryAlgebra.of x₃ y₃ h) : CategoryAlgebra R C) i)
  rw [mul_of, mul_of, mul_of, mul_of, comp₀_assoc]

instance : NonUnitalSemiring (CategoryAlgebra R C) where
  mul_assoc x y z := by
    have h : AddMonoidHom.mulLeft₃ x y z = AddMonoidHom.mulRight₃ x y z := by
      ext
      simp only [mul_assoc']
    exact h

instance : IsScalarTower R (CategoryAlgebra R C) (CategoryAlgebra R C) where
  smul_assoc r x y := by
    refine DirectSum.induction_on x ?_ ?_ ?_
    · rw [smul_zero, zero_smul, smul_zero]
    · rintro ⟨x₁, y₁⟩ f
      refine DirectSum.induction_on y ?_ ?_ ?_
      · simp
      · rintro ⟨x₂, y₂⟩ g
        change (r • (CategoryAlgebra.of x₁ y₁ f : CategoryAlgebra R C))
          * CategoryAlgebra.of x₂ y₂ g
          = r • (CategoryAlgebra.of x₁ y₁ f * CategoryAlgebra.of x₂ y₂ g)
        rw [← LinearMap.map_smul, mul_of, mul_of, ← LinearMap.map_smul, comp₀]
        split_ifs with h
        · cases h
          congr 1
          change ((r • f) ≫ eqToHom rfl) ≫ g = r • ((f ≫ eqToHom rfl) ≫ g)
          rw [eqToHom_refl, Category.comp_id, Category.comp_id, smul_comp]
        · change CategoryAlgebra.of x₁ y₂ (0 : x₁ ⟶ y₂)
            = CategoryAlgebra.of x₁ y₂ (r • (0 : x₁ ⟶ y₂))
          rw [smul_zero]
      · intro x' y' hx' hy'
        simp only [smul_add]
        rw [hx', hy']
    · intro x' y' hx' hy'
      change (r • x') * y = r • (x' * y) at hx'
      change (r • y') * y = r • (y' * y) at hy'
      rw [smul_add]
      change (r • x' + r • y') * y = r • ((x' + y') * y)
      rw [add_mul, add_mul, smul_add, hx', hy']

instance : SMulCommClass R (CategoryAlgebra R C) (CategoryAlgebra R C) where
  smul_comm r x y := by
    refine DirectSum.induction_on x ?_ ?_ ?_
    · rw [zero_smul, smul_zero, zero_smul]
    · rintro ⟨x₁, y₁⟩ f
      refine DirectSum.induction_on y ?_ ?_ ?_
      · simp
      · rintro ⟨x₂, y₂⟩ g
        change r • (CategoryAlgebra.of x₁ y₁ f * CategoryAlgebra.of x₂ y₂ g)
          = CategoryAlgebra.of x₁ y₁ f * (r • (CategoryAlgebra.of x₂ y₂ g : CategoryAlgebra R C))
        rw [← LinearMap.map_smul, mul_of, mul_of, ← LinearMap.map_smul, comp₀]
        split_ifs with h
        · cases h
          congr 1
          change r • ((f ≫ eqToHom rfl) ≫ g) = (f ≫ eqToHom rfl) ≫ (r • g)
          rw [eqToHom_refl, Category.comp_id, comp_smul]
        · change CategoryAlgebra.of x₁ y₂ (r • (0 : x₁ ⟶ y₂))
            = CategoryAlgebra.of x₁ y₂ (0 : x₁ ⟶ y₂)
          rw [smul_zero]
      · intro x' y' hx' hy'
        simp only [smul_add, hx', hy']
    · intro x' y' hx' hy'
      change r • (x' * y) = x' * (r • y) at hx'
      change r • (y' * y) = y' * (r • y) at hy'
      rw [← smul_assoc]
      change (r • (x' + y')) * y = (x' + y') * (r • y)
      rw [smul_add, add_mul, add_mul, ← hx', ← hy']
      change (r • x' )• y + (r • y') • y = r • (x' • y) + r • (y' • y)
      rw [smul_assoc, smul_assoc]

section UniversalProperty

variable {A : Type*} [NonUnitalNonAssocSemiring A] [Module R A]
variable [IsScalarTower R A A] [SMulCommClass R A A]

/-- The data of a representation of a linear category `C` in a non-unital algebra `A`.
This consists of a family of linear maps for each hom-set that preserve category composition,
and annihilate each other when domains and codomains do not match. -/
@[ext]
structure Hom (R : Type w) [CommSemiring R]
    (C : Type u) [Category.{v} C] [Preadditive C] [Linear R C]
    (A : Type*) [NonUnitalNonAssocSemiring A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] where
  /-- The underlying family of linear maps evaluating on each hom-set. -/
  toFun : ∀ (x y : C), (x ⟶ y) →ₗ[R] A
  /-- The family of maps preserves category composition. -/
  map_comp : ∀ {x y z : C} (f : x ⟶ y) (g : y ⟶ z),
    toFun x z (f ≫ g) = toFun x y f * toFun y z g
  /-- The maps annihilate each other when domains and codomains do not match. -/
  map_ortho : ∀ {x y z w : C} (f : x ⟶ y) (g : z ⟶ w),
    y ≠ z → toFun x y f * toFun z w g = 0

instance : CoeFun (Hom R C A) (fun _ ↦ ∀ x y : C, (x ⟶ y) →ₗ[R] A) where
  coe rep := rep.toFun

variable (rep : Hom R C A)

/-- The universal extension of a composition-preserving family of maps
to a global non-unital algebra homomorphism on the category algebra. -/
def lift : CategoryAlgebra R C →ₙₐ[R] A :=
  { DirectSum.toModule R (C × C) A (fun z ↦ rep z.1 z.2) with
    map_zero' := map_zero _
    map_mul' := fun x y => by
      let l := DirectSum.toModule R (C × C) A (fun z ↦ rep z.1 z.2)
      change l (x * y) = l x * l y
      refine DirectSum.induction_on x ?_ ?_ ?_
      · simp
      · rintro ⟨x₁, y₁⟩ f
        refine DirectSum.induction_on y ?_ ?_ ?_
        · simp
        · rintro ⟨x₂, y₂⟩ g
          change l ((CategoryAlgebra.of x₁ y₁ f : CategoryAlgebra R C)
            * (CategoryAlgebra.of x₂ y₂ g : CategoryAlgebra R C))
            = l (CategoryAlgebra.of x₁ y₁ f : CategoryAlgebra R C)
            * l (CategoryAlgebra.of x₂ y₂ g : CategoryAlgebra R C)
          rw [CategoryAlgebra.mul_of, CategoryAlgebra.comp₀]
          split_ifs with h
          · cases h
            change l (DirectSum.lof R _ _ _ _)
              = l (DirectSum.lof R _ _ _ _) * l (DirectSum.lof R _ _ _ _)
            rw [DirectSum.toModule_lof, DirectSum.toModule_lof, DirectSum.toModule_lof]
            change rep.toFun x₁ y₂ ((f ≫ eqToHom rfl) ≫ g) = rep.toFun x₁ y₁ f * rep.toFun y₁ y₂ g
            rw [eqToHom_refl, Category.comp_id, rep.map_comp]
          · change l (DirectSum.lof R _ _ _ _)
              = l (DirectSum.lof R _ _ _ _) * l (DirectSum.lof R _ _ _ _)
            rw [DirectSum.toModule_lof, DirectSum.toModule_lof, DirectSum.toModule_lof,
                rep.map_ortho f g h]
            change rep.toFun x₁ y₂ 0 = 0
            exact map_zero (rep.toFun x₁ y₂)
        · intro y' y'' hy' hy''
          rw [mul_add, map_add, map_add, hy', hy'', mul_add]
      · intro x' x'' hx' hx''
        rw [add_mul, map_add, map_add, hx', hx'', add_mul] }

/-- The lift evaluates exactly to the underlying map on the canonical inclusions. -/
@[simp]
theorem lift_of (x y : C) (f : x ⟶ y) :
    lift rep (CategoryAlgebra.of x y f) = rep x y f := by
  change DirectSum.toModule R (C × C) A (fun z ↦ rep z.1 z.2)
    (DirectSum.lof R (C × C) (fun z ↦ z.1 ⟶ z.2) (x, y) f) = _
  rw [DirectSum.toModule_lof]

/-- The uniqueness part of the universal property: any non-unital algebra homomorphism
that agrees on the generators with `rep` must be exactly `lift rep`. -/
theorem lift_unique (φ : CategoryAlgebra R C →ₙₐ[R] A)
    (hφ_of : ∀ x y (f : x ⟶ y), φ (CategoryAlgebra.of x y f) = rep x y f) :
    φ = lift rep := by
  apply DFunLike.ext
  intro x
  refine DirectSum.induction_on x ?_ ?_ ?_
  · simp
  · rintro ⟨x₁, y₁⟩ f
    change φ (CategoryAlgebra.of x₁ y₁ f) = lift rep (CategoryAlgebra.of x₁ y₁ f)
    rw [hφ_of, lift_of]
  · intro x' y' hx' hy'
    rw [map_add, map_add, hx', hy']

/-- The universal property of the category algebra, expressed as an equivalence
of types between `Hom R C A` and `CategoryAlgebra R C →ₙₐ[R] A`. -/
def liftEquiv : Hom R C A ≃ (CategoryAlgebra R C →ₙₐ[R] A) where
  toFun := lift
  invFun φ := {
    toFun x y := (φ : CategoryAlgebra R C →ₗ[R] A).comp (CategoryAlgebra.of x y)
    map_comp := fun {x y z} f g ↦ by
      change φ (CategoryAlgebra.of x z (f ≫ g)) =
        φ (CategoryAlgebra.of x y f) * φ (CategoryAlgebra.of y z g)
      rw [← map_mul]
      congr 1
      rw [CategoryAlgebra.mul_of, CategoryAlgebra.comp₀]
      split_ifs with h
      · cases h
        change CategoryAlgebra.of x z (f ≫ g) = CategoryAlgebra.of x z ((f ≫ eqToHom rfl) ≫ g)
        simp
      · contradiction
    map_ortho := fun {x y z w} f g h_neq ↦ by
      change φ (CategoryAlgebra.of x y f) * φ (CategoryAlgebra.of z w g) = 0
      rw [← map_mul, CategoryAlgebra.mul_of, CategoryAlgebra.comp₀, dite_eq_right h_neq]
      change φ (CategoryAlgebra.of x w 0) = 0
      simp
  }
  left_inv rep := by
    ext x y f
    exact lift_of rep x y f
  right_inv φ := by
    symm
    apply lift_unique
    intro x y f
    rfl

end UniversalProperty

section Unital

variable [Fintype C]
/-- The identity element of the category algebra, defined as the sum of the identity
morphisms of all objects. This is well-defined since `C` is `Fintype`. -/
def one' : CategoryAlgebra R C :=  ∑ x : C, (CategoryAlgebra.of x x (𝟙 x))

instance : One (CategoryAlgebra R C) := ⟨one'⟩

/-- Unfold lemma for the identity element of the category algebra. -/
theorem one_def : (1 : CategoryAlgebra R C) = ∑ x : C, (CategoryAlgebra.of x x (𝟙 x)) := rfl

/- `CategoryAlgebra R C` for `Fintype C` is a semiring. -/
instance : Semiring (CategoryAlgebra R C) where
  one_mul := by
    have h : (AddMonoidHom.mulLeft (1 : (CategoryAlgebra R C)) = (AddMonoidHom.id _)) := by
      ext x₁ y₁ f z
      rw [AddMonoidHom.mulLeft, one_def]
      simp only [Finset.sum_mul]
      rw [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      simp only [mul_of]
      rw [AddMonoidHom.id_apply, Finset.sum_eq_single_of_mem x₁ (Finset.mem_univ _)]
      · rw [comp₀, dite_eq_left rfl]
        simp only [AddMonoidHom.coe_mk]
        rw [ZeroHom.coe_mk,compHom]
        simp only [Preadditive.leftComp, AddMonoidHom.mk'_apply]
        rw [eqToHom_refl]
        simp
      · intro x₂ _ h
        rw [comp₀, dite_eq_right h]
        simp only [AddMonoidHom.zero_apply]
        rw [map_zero]
    apply DFunLike.congr_fun (h₁ := h)
  mul_one := by
    have h : (AddMonoidHom.mulRight (1 : (CategoryAlgebra R C)) = (AddMonoidHom.id _)) := by
      ext x₁ y₁ f
      rw [AddMonoidHom.mulRight, one_def]
      simp only [Finset.mul_sum]
      rw [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      simp only [mul_of]
      rw [AddMonoidHom.id_apply, Finset.sum_eq_single_of_mem y₁ (Finset.mem_univ _)]
      · rw [comp₀, dite_eq_left rfl]
        simp only [AddMonoidHom.coe_mk]
        rw [ZeroHom.coe_mk, compHom]
        simp only[Preadditive.leftComp, AddMonoidHom.mk'_apply]
        rw [eqToHom_refl]
        simp
      · intro y₂ _ h
        rw [comp₀, dite_eq_right h.symm]
        simp only [AddMonoidHom.zero_apply]
        rw [map_zero]
    apply DFunLike.congr_fun (h₁ := h)

/- `CategoryAlgebra R C` for `Fintype C` is a unital algebra. -/
instance : Algebra R (CategoryAlgebra R C) where
  algebraMap :=
    { toFun := fun r ↦ r • (1 : CategoryAlgebra R C)
      map_one' := one_smul R 1
      map_zero' := zero_smul R 1
      map_add' := fun r s ↦ add_smul r s 1
      map_mul' := fun r s ↦ by
        nth_rw 1 [← mul_one 1]
        rw [smul_mul_smul_comm] }
  commutes' := fun r x ↦ by
    change (r • 1) * x = x * (r • 1)
    rw [mul_smul_one, smul_one_mul]
  smul_def' := fun r x ↦ by
    change r • x = (r • 1) * x
    rw [smul_one_mul]

section UnitalUniversalProperty

variable {R C A : Type*} [CommSemiring R] [Category C] [Preadditive C] [Linear R C]
    [Fintype C] [Semiring A] [Algebra R A] [DecidableEq C]

variable (R C A)

/-- `UnitalHom` extends `Hom` for morphisms to algebras, where the sum of the
identities maps to `1`. -/
@[ext]
structure UnitalHom extends Hom R C A where
  /- Identity is mapped to identity. -/
  map_one' : ∑ x : C, toFun x x (𝟙 x) = 1

variable {R C A}

instance : CoeFun (UnitalHom R C A) (fun _ ↦ ∀ x y : C, (x ⟶ y) →ₗ[R] A) where
  coe rep := rep.toFun


/-- The universal extension of a composition-preserving family of maps
to a global algebra homomorphism on the category algebra. -/
def unitalLift (rep : UnitalHom R C A) : CategoryAlgebra R C →ₐ[R] A :=
  let baseLift := lift rep.toHom
  { baseLift with
    map_one' := by
      change lift rep.toHom (∑ x : C, CategoryAlgebra.of x x (𝟙 x)) = 1
      rw [map_sum]
      simp only [lift_of]
      exact rep.map_one'
    commutes' := fun r ↦ by
      change lift rep.toHom (r • 1) = algebraMap R A r
      have h_one : lift rep.toHom 1 = 1 := by
        change lift rep.toHom (∑ x : C, CategoryAlgebra.of x x (𝟙 x)) = 1
        rw [map_sum]
        simp only [lift_of]
        exact rep.map_one'
      rw [map_smul, h_one, Algebra.algebraMap_eq_smul_one] }

/-- The universal property of the category algebra, expressed as an equivalence
of types between `UnitalHom R C A` and `CategoryAlgebra R C →ₐ[R] A`. -/
def unitalLiftEquiv : UnitalHom R C A ≃ (CategoryAlgebra R C →ₐ[R] A) where
  toFun  := unitalLift
  invFun φ := {
    toHom := liftEquiv.symm (φ : CategoryAlgebra R C →ₙₐ[R] A)
    map_one' := by
      have h_one := φ.map_one
      rw [one_def, map_sum] at h_one
      exact h_one
  }
  left_inv rep := by
    ext x y f
    exact lift_of rep.toHom x y f
  right_inv φ := by
    apply DFunLike.ext
    intro x
    exact DFunLike.congr_fun (liftEquiv.right_inv (φ : CategoryAlgebra R C →ₙₐ[R] A)) x

end UnitalUniversalProperty
end Unital
end CategoryAlgebra
end CategoryTheory.Linear
