/-
Copyright (c) 2025 Bernhard Reinke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bernhard Reinke, Ray Shang
-/

module


public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Ring.Associator
public import Mathlib.CategoryTheory.Linear.Basic


/-!
# Category algebra of a linear category

This file defines the category algebra of a preadditive category `C` that is linear over a
commutative semiring `R`.

## Main definitions

* `CategoryAlgebra R C`: the category algebra of `C` over `R`, defined
  as the direct sum of the morphism spaces `X ⟶ Y` over all pairs `(X, Y) : C × C`.
* `CategoryAlgebra.of X Y f`: The canonical  `R`-linear inclusion of an element `f : X ⟶ Y`
   into `CategoryAlgebra R C`.
* `Hom R C A`: a structure for a composition-respecting family of
  `R`-linear maps from the Hom sets of `C` to a non-unital `R`-algebra `A`
* `lift F`: the canonical map from `CategoryAlgebra R C` to
   a non-unital `R`-algebra `A`, lifted from `F : Hom R C A`.
* `UnitalHom R C A`: a structure for a composition-respecting family of
  `R`-linear maps from the Hom sets of `C` to `R`-algebra `A`, extending `Hom R C A`
* `unitalLift F`: the canonical map from `CategoryAlgebra R C` to
   a `R`-algebra `A`, lifted from `F : UnitalHom R C A`.

## Main results

* `CategoryAlgebra R C` is a non-unital `R`-algebra.
* If `C` has finitely many objects (`Fintype C`), then `CategoryAlgebra R C`
  is a `R`-algebra.
* `CategoryTheory.Linear.CategoryAlgebra.liftEquiv`: `Hom R C A` and `CategoryAlgebra R C →ₙₐ[R] A`
  are equivalent types.
* `CategoryTheory.Linear.CategoryAlgebra.unitalLiftEquiv`: `Hom R C A` and
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
  [Linear R C] := ⨁ (p : C × C), p.1 ⟶ p.2

namespace CategoryAlgebra

variable {R : Type w} [CommSemiring R] {C : Type u} [Category.{v} C] [Preadditive C]
  [Linear R C] [DecidableEq C]

/-- The canonical inclusion of a morphism `f : a ⟶ b` into the category algebra. -/
protected def of (a b : C) : (a ⟶ b) →ₗ[R] CategoryAlgebra R C :=
  DirectSum.lof R (C × C) (fun p ↦ p.1 ⟶ p.2) (a, b)

/-- Two additive homomorphisms out of the category algebra are equal if they agree on
all canonical inclusions of morphisms. -/
@[ext 10000]
theorem addHom_ext {γ : Type w'} [AddZeroClass γ] ⦃f g : CategoryAlgebra R C →+ γ⦄
    (H : ∀ (X Y : C) (y : X ⟶ Y), f (CategoryAlgebra.of X Y y) = g (CategoryAlgebra.of X Y y)) :
    f = g := DFinsupp.addHom_ext (fun p => H p.1 p.2)

/-- The canonical inclusion `of a b f` is definitionally equal to the single entry
in the direct sum at index `(a, b)` with value `f`. -/
theorem of_eq_single (a b : C) (f : a ⟶ b) :
    (CategoryAlgebra.of a b f : CategoryAlgebra R C) =
    DFinsupp.single (a,b) f := by rfl

/-- A helper function to define multiplication on the category algebra.
Returns the composition of two morphisms if their intermediate objects are strictly equal,
and `0` otherwise. -/
def comp₀ (X Y Z W : C) : (X ⟶ Y) →+ (Z ⟶ W) →+ (X ⟶ W) :=
  if h : Y = Z then
    { toFun := fun f ↦ compHom (f ≫ eqToHom h)
      map_add' := fun f₁ f₂ ↦ by
        simp only [CategoryTheory.Preadditive.add_comp, map_add]
      map_zero' := by
        simp only [CategoryTheory.Limits.zero_comp, map_zero] }
  else
    0

/-- `comp₀` satisfies a generalized associativity relation across composable objects. -/
theorem comp₀_assoc (X₁ Y₁ X₂ Y₂ X₃ Y₃ : C) (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) (h : X₃ ⟶ Y₃) :
    ((comp₀ X₁ Y₂ X₃ Y₃) (((comp₀ X₁ Y₁ X₂ Y₂) f) g)) h =
    ((comp₀ X₁ Y₁ X₂ Y₃) f) (((comp₀ X₂ Y₂ X₃ Y₃) g) h) := by
  by_cases h₁₂ : Y₁ = X₂ <;> by_cases h₂₃ : Y₂ = X₃
  · simp only [comp₀, dif_pos h₁₂, dif_pos h₂₃, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      compHom, Preadditive.leftComp, AddMonoidHom.mk'_apply, Category.assoc]
  · simp only [comp₀, dif_pos h₁₂, dif_neg h₂₃, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      compHom, Preadditive.leftComp, AddMonoidHom.mk'_apply, AddMonoidHom.zero_apply,
      map_zero]
  · simp only [comp₀, dif_neg h₁₂, dif_pos h₂₃, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      compHom, Preadditive.leftComp, AddMonoidHom.mk'_apply, AddMonoidHom.zero_apply,
      map_zero]
  · simp only [comp₀, dif_neg h₁₂, dif_neg h₂₃, AddMonoidHom.zero_apply]

/-- The multiplication on the category algebra, defined by linearly extending
the composition of morphisms across the direct sum. -/
def mul' : CategoryAlgebra R C →+ CategoryAlgebra R C →+ CategoryAlgebra R C :=
  DFinsupp.sumAddHom₂ (fun q p ↦ AddMonoidHom.compr₂
  (comp₀ q.1 q.2 p.1 p.2) (CategoryAlgebra.of q.1 p.2).toAddMonoidHom)

instance : Mul (CategoryAlgebra R C) := ⟨fun f g => mul' f g⟩

/-- Unfold lemma for the multiplication operation on the category algebra. -/
theorem mul_def (f g : CategoryAlgebra R C) :
    f * g = DFinsupp.sumAddHom₂ (fun q p ↦ AddMonoidHom.compr₂
    (comp₀ q.1 q.2 p.1 p.2) (CategoryAlgebra.of q.1 p.2).toAddMonoidHom) f g := rfl

attribute [irreducible] mul'

instance : NonUnitalNonAssocSemiring (CategoryAlgebra R C) where
  left_distrib := fun a b c => by simp only [mul_def]; erw [map_add]
  right_distrib := fun a b c => by simp only [mul_def]; erw [map_add, AddMonoidHom.add_apply]
  zero_mul := fun a => by simp only [mul_def]; erw [map_zero]; rfl
  mul_zero := fun a => by simp only [mul_def]; erw [map_zero]

/-- The product of two basis elements evaluates to their composition (via `comp₀`) included
back into the category algebra. -/
theorem mul_of (X₁ Y₁ X₂ Y₂ : C) (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (CategoryAlgebra.of X₁ Y₁ f) * (CategoryAlgebra.of X₂ Y₂ g : (CategoryAlgebra R C)) =
    CategoryAlgebra.of X₁ Y₂ (comp₀ X₁ Y₁ X₂ Y₂ f g) := by
  rw [mul_def]
  rw [CategoryAlgebra.of_eq_single, CategoryAlgebra.of_eq_single]
  rw [DFinsupp.sumAddHom₂_single]
  rfl

/-- Associativity of multiplication on the category algebra, expressed as an equality
of trilinear maps. -/
theorem mul_assoc' :
  AddMonoidHom.mulLeft₃ (R := (CategoryAlgebra R C)) = AddMonoidHom.mulRight₃ := by
  ext X₁ Y₁ f X₂ Y₂ g X₃ Y₃ h i
  change (((CategoryAlgebra.of X₁ Y₁ f * CategoryAlgebra.of X₂ Y₂ g)
          * CategoryAlgebra.of X₃ Y₃ h : CategoryAlgebra R C) i) =
         ((CategoryAlgebra.of X₁ Y₁ f * (CategoryAlgebra.of X₂ Y₂ g
         * CategoryAlgebra.of X₃ Y₃ h) : CategoryAlgebra R C) i)
  rw [mul_of, mul_of, mul_of, mul_of]
  rw [comp₀_assoc]

instance : NonUnitalSemiring (CategoryAlgebra R C) where
  mul_assoc a b c := by
    have h : AddMonoidHom.mulLeft₃ a b c = AddMonoidHom.mulRight₃ a b c := by
      ext
      simp only [mul_assoc']
    exact h

instance : IsScalarTower R (CategoryAlgebra R C) (CategoryAlgebra R C) where
  smul_assoc r a b := by
    refine DirectSum.induction_on a ?_ ?_ ?_
    · rw [smul_zero, zero_smul, smul_zero]
    · rintro ⟨X₁, Y₁⟩ f
      refine DirectSum.induction_on b ?_ ?_ ?_
      · simp only [smul_zero]
      · rintro ⟨X₂, Y₂⟩ g
        change (r • (CategoryAlgebra.of X₁ Y₁ f : CategoryAlgebra R C)) *
          CategoryAlgebra.of X₂ Y₂ g = r • (CategoryAlgebra.of X₁ Y₁ f * CategoryAlgebra.of X₂ Y₂ g)
        rw [← LinearMap.map_smul, mul_of, mul_of, ← LinearMap.map_smul]
        dsimp only [comp₀]
        split_ifs with h
        · cases h
          congr 1
          change ((r • f) ≫ eqToHom rfl) ≫ g = r • ((f ≫ eqToHom rfl) ≫ g)
          rw [eqToHom_refl, Category.comp_id, Category.comp_id]
          rw [smul_comp]
        · change CategoryAlgebra.of X₁ Y₂ (0 : X₁ ⟶ Y₂)
          = CategoryAlgebra.of X₁ Y₂ (r • (0 : X₁ ⟶ Y₂))
          rw [smul_zero]
      · intro x y hx hy
        simp only [smul_add, hx, hy]
    · intro x y hx hy
      change (r • x) * b = r • (x * b) at hx
      change (r • y) * b = r • (y * b) at hy
      rw [smul_add]
      change (r • x + r • y) * b = r • ((x + y) * b)
      rw [add_mul, add_mul, smul_add, hx, hy]

instance : SMulCommClass R (CategoryAlgebra R C) (CategoryAlgebra R C) where
  smul_comm r a b := by
    refine DirectSum.induction_on a ?_ ?_ ?_
    · rw [zero_smul, smul_zero, zero_smul]
    · rintro ⟨X₁, Y₁⟩ f
      refine DirectSum.induction_on b ?_ ?_ ?_
      · simp only [smul_zero]
      · rintro ⟨X₂, Y₂⟩ g
        change r • (CategoryAlgebra.of X₁ Y₁ f * CategoryAlgebra.of X₂ Y₂ g) =
          CategoryAlgebra.of X₁ Y₁ f *
            (r • (CategoryAlgebra.of X₂ Y₂ g : CategoryAlgebra R C))
        rw [← LinearMap.map_smul, mul_of, mul_of, ← LinearMap.map_smul]
        dsimp only [comp₀]
        split_ifs with h
        · cases h
          congr 1
          change r • ((f ≫ eqToHom rfl) ≫ g) = (f ≫ eqToHom rfl) ≫ (r • g)
          rw [eqToHom_refl, Category.comp_id]
          rw [comp_smul]
        · change CategoryAlgebra.of X₁ Y₂ (r • (0 : X₁ ⟶ Y₂))
          = CategoryAlgebra.of X₁ Y₂ (0 : X₁ ⟶ Y₂)
          rw [smul_zero]
      · intro x y hx hy
        simp only [smul_add, hx, hy]
    · intro x y hx hy
      change r • (x * b) = x * (r • b) at hx
      change r • (y * b) = y * (r • b) at hy
      rw [← smul_assoc]
      change (r • (x + y)) * b = (x + y) * (r • b)
      rw [smul_add, add_mul, add_mul]
      rw [← hx, ← hy]
      change (r • x )• b + (r • y) • b = r • (x • b) + r • (y • b)
      rw [smul_assoc, smul_assoc]

section UniversalProperty
set_option linter.style.whitespace false

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
  toFun : ∀ (X Y : C), (X ⟶ Y) →ₗ[R] A
  /-- The family of maps preserves category composition. -/
  map_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
    toFun X Z (f ≫ g) = toFun X Y f * toFun Y Z g
  /-- The maps annihilate each other when domains and codomains do not match. -/
  map_ortho : ∀ {X Y Z W : C} (f : X ⟶ Y) (g : Z ⟶ W),
    Y ≠ Z → toFun X Y f * toFun Z W g = 0

instance : CoeFun (Hom R C A) (fun _ ↦ ∀ X Y : C, (X ⟶ Y) →ₗ[R] A) where
  coe F := F.toFun

variable (F : Hom R C A)

/-- The universal extension of a composition-preserving family of maps
to a global non-unital algebra homomorphism on the category algebra. -/
def lift : CategoryAlgebra R C →ₙₐ[R] A :=
{ DirectSum.toModule R (C × C) A (fun p ↦ F p.1 p.2) with
    map_zero' := map_zero _
    map_mul' := fun a b => by
      -- Define L locally so we can use its coercions cleanly
      let L := DirectSum.toModule R (C × C) A (fun p ↦ F p.1 p.2)
      change L (a * b) = L a * L b
      refine DirectSum.induction_on a ?_ ?_ ?_
      · simp only [zero_mul, map_zero]
      · rintro ⟨X₁, Y₁⟩ f
        refine DirectSum.induction_on b ?_ ?_ ?_
        · simp only [mul_zero, map_zero]
        · rintro ⟨X₂, Y₂⟩ g
          change L ((CategoryAlgebra.of X₁ Y₁ f : CategoryAlgebra R C)
            * (CategoryAlgebra.of X₂ Y₂ g : CategoryAlgebra R C)) =
            L (CategoryAlgebra.of X₁ Y₁ f : CategoryAlgebra R C)
            * L (CategoryAlgebra.of X₂ Y₂ g : CategoryAlgebra R C)
          rw [CategoryAlgebra.mul_of]
          dsimp only [CategoryAlgebra.comp₀]
          split_ifs with h
          · cases h
            change L (DirectSum.lof R _ _ _ _)
            = L (DirectSum.lof R _ _ _ _) * L (DirectSum.lof R _ _ _ _)
            rw [DirectSum.toModule_lof, DirectSum.toModule_lof, DirectSum.toModule_lof]
            change F.toFun X₁ Y₂ ((f ≫ eqToHom rfl) ≫ g) = F.toFun X₁ Y₁ f * F.toFun Y₁ Y₂ g
            rw [eqToHom_refl, Category.comp_id]
            rw [F.map_comp]
          · change L (DirectSum.lof R _ _ _ _)
            = L (DirectSum.lof R _ _ _ _) * L (DirectSum.lof R _ _ _ _)
            rw [DirectSum.toModule_lof, DirectSum.toModule_lof, DirectSum.toModule_lof]
            rw [F.map_ortho f g h]
            change F.toFun X₁ Y₂ 0 = 0
            exact map_zero (F.toFun X₁ Y₂)
        · intro x y hx hy
          rw [mul_add, map_add, map_add, hx, hy, mul_add]
      · intro x y hx hy
        rw [add_mul, map_add, map_add, hx, hy, add_mul] }

/-- The lift evaluates exactly to the underlying map on the canonical inclusions. -/
@[simp]
theorem lift_of (X Y : C) (f : X ⟶ Y) :
    lift F (CategoryAlgebra.of X Y f) = F X Y f := by
  change DirectSum.toModule R (C × C) A (fun p ↦ F p.1 p.2)
    (DirectSum.lof R (C × C) (fun p ↦ p.1 ⟶ p.2) (X, Y) f) = _
  rw [DirectSum.toModule_lof]

/-- The uniqueness part of the universal property: any non-unital algebra homomorphism
that agrees on the generators with `F` must be exactly `lift F`. -/
theorem lift_unique (φ : CategoryAlgebra R C →ₙₐ[R] A)
    (hφ_of : ∀ X Y (f : X ⟶ Y), φ (CategoryAlgebra.of X Y f) = F X Y f) :
    φ = lift F := by
  apply DFunLike.ext
  intro x
  refine DirectSum.induction_on x ?_ ?_ ?_
  · simp only [map_zero]
  · rintro ⟨X, Y⟩ f
    change φ (CategoryAlgebra.of X Y f) = lift F (CategoryAlgebra.of X Y f)
    rw [hφ_of, lift_of]
  · intro a b ha hb
    rw [map_add, map_add, ha, hb]

/-- The universal property of the category algebra, expressed as an equivalence
of types between `Hom R C A` and `CategoryAlgebra R C →ₙₐ[R] A`. -/
def liftEquiv : Hom R C A ≃ (CategoryAlgebra R C →ₙₐ[R] A) where
  toFun := lift
  invFun φ := {
    toFun X Y := (φ : CategoryAlgebra R C →ₗ[R] A).comp (CategoryAlgebra.of X Y)
    map_comp := fun {X Y Z} f g ↦ by
      change φ (CategoryAlgebra.of X Z (f ≫ g)) =
        φ (CategoryAlgebra.of X Y f) * φ (CategoryAlgebra.of Y Z g)
      rw [← map_mul]
      congr 1
      rw [CategoryAlgebra.mul_of]
      dsimp only [CategoryAlgebra.comp₀]
      split_ifs with h
      · cases h
        change CategoryAlgebra.of X Z (f ≫ g) = CategoryAlgebra.of X Z ((f ≫ eqToHom rfl) ≫ g)
        simp only [eqToHom_refl, Category.comp_id]
      · contradiction
    map_ortho := fun {X Y Z W} f g h_neq ↦ by
      change φ (CategoryAlgebra.of X Y f) * φ (CategoryAlgebra.of Z W g) = 0
      rw [← map_mul]
      rw [CategoryAlgebra.mul_of]
      dsimp only [CategoryAlgebra.comp₀]
      rw [dif_neg h_neq]
      change φ (CategoryAlgebra.of X W 0) = 0
      simp only [map_zero]
  }
  left_inv F := by
    ext X Y f
    exact lift_of F X Y f
  right_inv φ := by
    symm
    apply lift_unique
    intro X Y f
    rfl

end UniversalProperty

section Unital

variable [Fintype C]

/-- The identity element of the category algebra, defined as the sum of the identity
morphisms of all objects. This is well-defined since `C` is `Fintype`. -/
def one' : CategoryAlgebra R C :=  ∑ i : C, (CategoryAlgebra.of i i (𝟙 i))

instance : One (CategoryAlgebra R C) := ⟨one'⟩

/-- Unfold lemma for the identity element of the category algebra. -/
theorem one_def : (1 : CategoryAlgebra R C) = ∑ i : C, (CategoryAlgebra.of i i (𝟙 i)) := rfl

/- `CategoryAlgebra R C` for `Fintype C` is a semiring. -/
instance : Semiring (CategoryAlgebra R C) where
  one_mul := by
    have H : (AddMonoidHom.mulLeft (1 : (CategoryAlgebra R C)) = (AddMonoidHom.id _)) := by
      ext X₁ Y₁ f i
      simp only [AddMonoidHom.mulLeft, one_def, Finset.sum_mul, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
        mul_of, AddMonoidHom.id_apply]
      rw [Finset.sum_eq_single_of_mem X₁ (Finset.mem_univ _)]
      · dsimp only [comp₀]
        rw [dif_pos rfl]
        simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, compHom, Preadditive.leftComp,
          AddMonoidHom.mk'_apply, eqToHom_refl, Category.id_comp, Category.comp_id]
      · intro b _ h
        dsimp only [comp₀]
        rw [dif_neg h]
        simp only [AddMonoidHom.zero_apply, map_zero]
    apply DFunLike.congr_fun (h₁ := H)
  mul_one := by
    have H : (AddMonoidHom.mulRight (1 : (CategoryAlgebra R C)) = (AddMonoidHom.id _)) := by
      ext X₁ Y₁ f
      simp only [AddMonoidHom.mulRight, one_def, Finset.mul_sum, AddMonoidHom.coe_mk,
        ZeroHom.coe_mk, mul_of, AddMonoidHom.id_apply]
      rw [Finset.sum_eq_single_of_mem Y₁ (Finset.mem_univ _)]
      · dsimp only [comp₀]
        rw [dif_pos rfl]
        simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, compHom, Preadditive.leftComp,
          AddMonoidHom.mk'_apply, eqToHom_refl, Category.comp_id]
      · intro b _ h
        dsimp only [comp₀]
        rw [dif_neg h.symm]
        simp only [AddMonoidHom.zero_apply, map_zero]
    apply DFunLike.congr_fun (h₁ := H)

/- `CategoryAlgebra R C` for `Fintype C` is a unital algebra. -/
instance : Algebra R (CategoryAlgebra R C) where
  algebraMap :=
    { toFun := fun r ↦ r • (1 : CategoryAlgebra R C)
      map_one' := one_smul R 1
      map_zero' := zero_smul R 1
      map_add' := fun r s ↦ add_smul r s 1
      map_mul' := fun r s ↦ by
        nth_rw 1 [← mul_one 1]
        rw [smul_mul_smul_comm]
         }
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
  map_one' : ∑ i : C, toFun i i (𝟙 i) = 1

variable {R C A}

instance : CoeFun (UnitalHom R C A) (fun _ ↦ ∀ X Y : C, (X ⟶ Y) →ₗ[R] A) where
  coe F := F.toFun


/-- The universal extension of a composition-preserving family of maps
to a global algebra homomorphism on the category algebra. -/
def unitalLift (F : UnitalHom R C A) : CategoryAlgebra R C →ₐ[R] A :=
  let baseLift := lift F.toHom
  { baseLift with
    map_one' := by
      change lift F.toHom (∑ i : C, CategoryAlgebra.of i i (𝟙 i)) = 1
      rw [map_sum]
      simp only [lift_of]
      exact F.map_one'
    commutes' := fun r ↦ by
      change lift F.toHom (r • 1) = algebraMap R A r
      have h_one : lift F.toHom 1 = 1 := by
        change lift F.toHom (∑ i : C, CategoryAlgebra.of i i (𝟙 i)) = 1
        rw [map_sum]
        simp only [lift_of]
        exact F.map_one'
      rw [map_smul, h_one, Algebra.algebraMap_eq_smul_one] }

/-- The universal property of the category algebra, expressed as an equivalence
of types between `UnitalHom R C A` and `CategoryAlgebra R C →ₐ[R] A`. -/
def unitalLiftEquiv : UnitalHom R C A ≃ (CategoryAlgebra R C →ₐ[R] A) where
  toFun  := unitalLift
  invFun φ := {
    toHom := liftEquiv.symm (φ : CategoryAlgebra R C →ₙₐ[R] A)
    map_one' := by
      have h_one := φ.map_one
      rw [one_def] at h_one
      rw [map_sum] at h_one
      exact h_one
  }
  left_inv F := by
    ext X Y f
    exact lift_of F.toHom X Y f
  right_inv φ := by
    apply DFunLike.ext
    intro x
    exact DFunLike.congr_fun (liftEquiv.right_inv (φ : CategoryAlgebra R C →ₙₐ[R] A)) x

end UnitalUniversalProperty
end Unital
end CategoryAlgebra
end CategoryTheory.Linear
