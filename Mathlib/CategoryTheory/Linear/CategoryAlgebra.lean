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
    [Linear R C] := ⨁ (x : C), ⨁ (y : C), x ⟶ y

namespace CategoryAlgebra

variable (R : Type w) [CommSemiring R] {C : Type u} [Category.{v} C] [Preadditive C]
  [Linear R C] [DecidableEq C]

/-- The canonical inclusion of a morphism `f : a ⟶ b` into the category algebra. -/
protected def of (x y : C) : (x ⟶ y) →ₗ[R] CategoryAlgebra R C :=
  DirectSum.lof R C _ x ∘ₗ DirectSum.lof R _ _ y

/-- Two additive homomorphisms out of the category algebra are equal if they agree on
all canonical inclusions of morphisms. -/
@[ext high]
theorem addHom_ext {γ : Type w'} [AddZeroClass γ] {f g : CategoryAlgebra R C →+ γ}
    (h : ∀ (x y : C) (f' : x ⟶ y), f (.of R x y f') = g (.of R x y f')) :
    f = g := by
  apply DirectSum.addHom_ext
  intro x y
  induction y using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | of y q => exact h ..
  | add y y' hy hy' =>
    rw [map_add, map_add, hy, hy']
    simp

/-- The canonical inclusion `of a b f` is definitionally equal to the single entry
in the direct sum at index `(a, b)` with value `f`. -/
theorem of_eq_single (x y : C) (f : x ⟶ y) :
    (CategoryAlgebra.of R x y f : CategoryAlgebra R C) =
    DirectSum.of _ x (DirectSum.of _ y f) :=
    rfl

/-- Multiply a basis morphism `f : x ⟶ y` across the inner sum `⨁ w, y ⟶ w`. -/
def compInner (x y : C) (f : x ⟶ y) : (⨁ w, y ⟶ w) →ₗ[R] (⨁ w, x ⟶ w) :=
  DirectSum.toModule R C (⨁ w, x ⟶ w) (fun w ↦
    DirectSum.lof R C (fun w' ↦ x ⟶ w') w ∘ₗ CategoryTheory.Linear.leftComp R w f)

lemma compInner_add (x y : C) (f₁ f₂ : x ⟶ y) :
    compInner R x y (f₁ + f₂) = compInner R x y f₁ + compInner R x y f₂ := by
  ext w g
  rw [compInner, compInner, compInner]
  simp

lemma compInner_smul (x y : C) (r : R) (f : x ⟶ y) :
    compInner R x y (r • f) = r • compInner R x y f := by
  ext w g
  rw [compInner, compInner]
  simp

/-- Multiply a basis morphism `f : x ⟶ y` with the entire category algebra. -/
def compSingle (x y : C) (f : x ⟶ y) : CategoryAlgebra R C →ₗ[R] CategoryAlgebra R C :=
  (DirectSum.lof R C (fun z ↦ ⨁ w, z ⟶ w) x) ∘ₗ (compInner R x y f)
  ∘ₗ (DirectSum.component R C (fun z ↦ ⨁ w, z ⟶ w) y)

lemma compSingle_add (x y : C) (f₁ f₂ : x ⟶ y) :
    compSingle R x y (f₁ + f₂) = compSingle R x y f₁ + compSingle R x y f₂ := by
  rw [compSingle, compInner_add, LinearMap.add_comp, LinearMap.comp_add]
  rfl

lemma compSingle_smul (x y : C) (r : R) (f : x ⟶ y) :
    compSingle R x y (r • f) = r • compSingle R x y f := by
  rw [compSingle, compInner_smul, LinearMap.smul_comp, LinearMap.comp_smul]
  rfl

/-- The full bilinear multiplication map for the category algebra. -/
def mul' : CategoryAlgebra R C →ₗ[R] (CategoryAlgebra R C →ₗ[R] CategoryAlgebra R C) :=
  DirectSum.toModule R C _ (fun x ↦
    DirectSum.toModule R C _ (fun y ↦
      { toFun := fun f ↦ compSingle R x y f
        map_add' := fun f₁ f₂ ↦ compSingle_add R x y f₁ f₂
        map_smul' := fun r f => compSingle_smul R x y r f }))

instance : Mul (CategoryAlgebra R C) := ⟨fun f g => mul' R f g⟩

lemma mul_def (x y : CategoryAlgebra R C) : x * y = mul' R x y := rfl

-- Unwraps `*` back into `compSingle` when applied to a basis element on the left.
lemma of_mul (x y : C) (f : x ⟶ y) (b : CategoryAlgebra R C) :
    CategoryAlgebra.of R x y f * b = compSingle R x y f b := by
  rw [mul_def, mul', CategoryAlgebra.of, LinearMap.comp_apply]
  rw [DirectSum.toModule_lof, DirectSum.toModule_lof]
  rfl

/-- When the domain and codomain match, they compose. -/
lemma compSingle_of_eq (x y z : C) (f : x ⟶ y) (g : y ⟶ z) :
    compSingle R x y f (CategoryAlgebra.of R y z g) = CategoryAlgebra.of R x z (f ≫ g) := by
  rw [compSingle, LinearMap.comp_apply, LinearMap.comp_apply]
  have h_eval : DirectSum.component R C (fun a ↦ ⨁ b, a ⟶ b) y (CategoryAlgebra.of R y z g) =
      DirectSum.lof R C (fun b ↦ y ⟶ b) z g :=
    DFinsupp.single_eq_same
  rw [h_eval, compInner, DirectSum.toModule_lof, LinearMap.comp_apply]
  rfl

/-- When the domain and codomain mismatch, the projection yields 0. -/
lemma compSingle_of_ne {x y z w : C} (h : y ≠ z) (f : x ⟶ y) (g : z ⟶ w) :
    compSingle R x y f (CategoryAlgebra.of R z w g) = 0 := by
  rw [compSingle, LinearMap.comp_apply, LinearMap.comp_apply]
  have h_eval : DirectSum.component R C (fun a ↦ ⨁ b, a ⟶ b) y (CategoryAlgebra.of R z w g) = 0 :=
    DFinsupp.single_eq_of_ne h
  rw [h_eval, map_zero, map_zero]

lemma zero_mul' (x : CategoryAlgebra R C) : 0 * x = 0 := by
  rw [mul_def, map_zero, LinearMap.zero_apply]

lemma mul_zero' (x : CategoryAlgebra R C) : x * 0 = 0 := by
  rw [mul_def, map_zero]

/-- Multiplication satisfies a generalized associativity relation across basis morphisms. -/
theorem of_mul_assoc (x₁ y₁ x₂ y₂ x₃ y₃ : C) (f : x₁ ⟶ y₁) (g : x₂ ⟶ y₂) (h : x₃ ⟶ y₃) :
    (CategoryAlgebra.of R x₁ y₁ f * CategoryAlgebra.of R x₂ y₂ g) * CategoryAlgebra.of R x₃ y₃ h
    = CategoryAlgebra.of R x₁ y₁ f
    * (CategoryAlgebra.of R x₂ y₂ g * CategoryAlgebra.of R x₃ y₃ h) := by
  by_cases h12 : y₁ = x₂ <;> by_cases h23 : y₂ = x₃
  · subst h12 h23
    rw [of_mul, of_mul, of_mul, compSingle_of_eq R, compSingle_of_eq R, compSingle_of_eq R, of_mul]
    rw [compSingle_of_eq R, Category.assoc]
  · subst h12
    rw [of_mul, of_mul, of_mul, compSingle_of_ne R h23, compSingle_of_eq R, of_mul]
    rw [compSingle_of_ne R h23, map_zero]
  · subst h23
    rw [of_mul, of_mul, of_mul, compSingle_of_ne R h12, zero_mul', compSingle_of_eq R]
    rw [compSingle_of_ne R h12]
  · rw [of_mul, of_mul, of_mul, compSingle_of_ne R h12, zero_mul', compSingle_of_ne R h23, map_zero]

lemma mul_add' (x y z : CategoryAlgebra R C) : x * (y + z) = x * y + x * z := by
  rw [mul_def, mul_def, mul_def, map_add]

lemma add_mul' (x y z : CategoryAlgebra R C) : (x + y) * z = x * z + y * z := by
  rw [mul_def, mul_def, mul_def, map_add, LinearMap.add_apply]

/-- A custom induction principle to unwrap the nested direct sums of the category algebra. -/
@[elab_as_elim]
lemma induction {P : CategoryAlgebra R C → Prop}
    (h_zero : P 0)
    (h_add : ∀ a b, P a → P b → P (a + b))
    (h_of : ∀ x y (f : x ⟶ y), P (CategoryAlgebra.of R x y f))
    (x : CategoryAlgebra R C) : P x := by
  refine DirectSum.induction_on x h_zero ?_ h_add
  intro x₁ vx
  refine DirectSum.induction_on vx ?_ (h_of x₁) ?_
  · rw [map_zero]
    exact h_zero
  · intro a b ha hb
    rw [map_add]
    exact h_add _ _ ha hb

/-- Associativity of multiplication on the entire category algebra. -/
lemma mul_assoc' (x y z : CategoryAlgebra R C) :
    (x * y) * z = x * (y * z) := by
  induction x using CategoryAlgebra.induction with
  | h_zero => rw [zero_mul', zero_mul',zero_mul']
  | h_add _ _ h1 h2 => rw [add_mul', add_mul', add_mul', h1, h2]
  | h_of x₁ y₁ f =>
    induction y using CategoryAlgebra.induction with
    | h_zero => rw [mul_zero', zero_mul', mul_zero']
    | h_add _ _ h1 h2 => rw [add_mul', mul_add', mul_add', add_mul', h1, h2]
    | h_of x₂ y₂ g =>
      induction z using CategoryAlgebra.induction with
      | h_zero => rw [mul_zero', mul_zero', mul_zero']
      | h_add _ _ h1 h2 => rw [mul_add', mul_add', mul_add', h1, h2]
      | h_of x₃ y₃ h => exact of_mul_assoc R x₁ y₁ x₂ y₂ x₃ y₃ f g h

instance : NonUnitalSemiring (CategoryAlgebra R C) where
  zero_mul := zero_mul' R
  mul_zero := mul_zero' R
  left_distrib := mul_add' R
  right_distrib  := add_mul' R
  mul_assoc := mul_assoc' R

instance : IsScalarTower R (CategoryAlgebra R C) (CategoryAlgebra R C) where
  smul_assoc r x y := by
    rw [smul_eq_mul, smul_eq_mul, mul_def, mul_def, LinearMap.map_smul, LinearMap.smul_apply]

instance : SMulCommClass R (CategoryAlgebra R C) (CategoryAlgebra R C) where
  smul_comm r x y := by
    rw [smul_eq_mul, smul_eq_mul]
    exact (LinearMap.map_smul (mul' R x) r y).symm

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

/-- A helper linear map to construct the universal extension by double-unwrapping the direct sum. -/
def liftMap : CategoryAlgebra R C →ₗ[R] A :=
  DirectSum.toModule R C A (fun x ↦
    DirectSum.toModule R C A (fun y ↦ rep x y))

lemma liftMap_of (x y : C) (f : x ⟶ y) :
    liftMap R rep (CategoryAlgebra.of R x y f) = rep x y f := by
  rw [liftMap, CategoryAlgebra.of, LinearMap.comp_apply]
  rw [DirectSum.toModule_lof, DirectSum.toModule_lof]

lemma liftMap_toFun (x : CategoryAlgebra R C) : (liftMap R rep).toFun x = liftMap R rep x := rfl

/-- The universal extension of a composition-preserving family of maps
to a global non-unital algebra homomorphism on the category algebra. -/
def lift : CategoryAlgebra R C →ₙₐ[R] A :=
  { liftMap R rep with
    map_zero' := map_zero _
    map_mul' := fun a b ↦ by
      induction a using CategoryAlgebra.induction with
      | h_zero => rw [zero_mul, liftMap_toFun, liftMap_toFun, map_zero, zero_mul]
      | h_add a₁ a₂ h1 h2 =>
        rw [liftMap_toFun, liftMap_toFun, liftMap_toFun] at h1 h2
        rw [liftMap_toFun, liftMap_toFun, liftMap_toFun, add_mul, map_add, map_add]
        rw [h1, h2, add_mul]
      | h_of x₁ y₁ f =>
        induction b using CategoryAlgebra.induction with
        | h_zero => rw [liftMap_toFun, liftMap_toFun, liftMap_toFun, mul_zero, map_zero, mul_zero]
        | h_add b₁ b₂ h1 h2 =>
          rw [liftMap_toFun, liftMap_toFun, liftMap_toFun] at h1 h2
          rw [liftMap_toFun, liftMap_toFun, liftMap_toFun]
          rw [mul_add, map_add, h1, h2, map_add, mul_add]
        | h_of x₂ y₂ g =>
          by_cases h : y₁ = x₂
          · subst h
            rw [of_mul, liftMap_toFun, liftMap_toFun, liftMap_toFun, compSingle_of_eq R]
            rw [liftMap_of, liftMap_of, liftMap_of, Hom.map_comp]
          · rw [of_mul, compSingle_of_ne R h, liftMap_toFun, liftMap_toFun, liftMap_toFun]
            rw [liftMap_of, liftMap_of, rep.map_ortho f g h, map_zero] }

/-- The lift evaluates exactly to the underlying map on the canonical inclusions. -/
theorem lift_of (x y : C) (f : x ⟶ y) :
    lift R rep (CategoryAlgebra.of R x y f) = rep x y f :=
  liftMap_of R rep x y f

/-- The uniqueness part of the universal property: any non-unital algebra homomorphism
that agrees on the generators with `rep` must be exactly `lift rep`. -/
theorem lift_unique (φ : CategoryAlgebra R C →ₙₐ[R] A)
    (hφ_of : ∀ x y (f : x ⟶ y), φ (CategoryAlgebra.of R x y f) = rep x y f) :
    φ = lift R rep := by
  apply DFunLike.ext
  intro x
  induction x using CategoryAlgebra.induction with
  | h_zero => rw [map_zero, map_zero]
  | h_add a b ha hb => rw [map_add, map_add, ha, hb]
  | h_of x y f => rw [hφ_of, lift_of]

/-- The universal property of the category algebra, expressed as an equivalence
of types between `Hom R C A` and `CategoryAlgebra R C →ₙₐ[R] A`. -/
def liftEquiv : Hom R C A ≃ (CategoryAlgebra R C →ₙₐ[R] A) where
  toFun := lift R
  invFun φ := {
    toFun := fun x y ↦ (φ : CategoryAlgebra R C →ₗ[R] A).comp (CategoryAlgebra.of R x y)
    map_comp := fun {x y z} f g ↦ by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply]
      rw [← compSingle_of_eq]
      rw [← of_mul]
      exact map_mul φ _ _
    map_ortho := fun {x y z w} f g h_neq ↦ by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, ← map_zero φ]
      rw [← compSingle_of_ne R h_neq f g, ← of_mul]
      exact (map_mul φ _ _).symm
  }
  left_inv rep := by
    ext x y f
    exact lift_of R rep x y f
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
def one' : CategoryAlgebra R C := ∑ x : C, CategoryAlgebra.of R x x (𝟙 x)

instance : One (CategoryAlgebra R C) := ⟨one' R⟩

/-- Unfold lemma for the identity element of the category algebra. -/
lemma one_def : (1 : CategoryAlgebra R C) = ∑ x : C, CategoryAlgebra.of R x x (𝟙 x) := rfl

/- `CategoryAlgebra R C` for `Fintype C` is a semiring. -/
instance : Semiring (CategoryAlgebra R C) where
  one_mul := fun x ↦ by
    induction x using CategoryAlgebra.induction with
    | h_zero => rw [mul_zero]
    | h_add a b ha hb => rw [mul_add, ha, hb]
    | h_of x y f =>
      rw [one_def, Finset.sum_mul]
      have h_eq : CategoryAlgebra.of R x x (𝟙 x) * CategoryAlgebra.of R x y f
                  = CategoryAlgebra.of R x y f := by
        rw [of_mul, compSingle_of_eq R, Category.id_comp]
      rw [Finset.sum_eq_single_of_mem x (Finset.mem_univ x)]
      · exact h_eq
      · intro w _ h_ne
        rw [of_mul, compSingle_of_ne R h_ne]
  mul_one := fun x ↦ by
    induction x using CategoryAlgebra.induction with
    | h_zero => rw [zero_mul]
    | h_add a b ha hb => rw [add_mul, ha, hb]
    | h_of x y f =>
      rw [one_def, Finset.mul_sum]
      have h_eq : CategoryAlgebra.of R x y f * CategoryAlgebra.of R y y (𝟙 y)
                  = CategoryAlgebra.of R x y f := by
        rw [of_mul, compSingle_of_eq R, Category.comp_id]
      rw [Finset.sum_eq_single_of_mem y (Finset.mem_univ y)]
      · exact h_eq
      · intro w _ h_ne
        rw [of_mul, compSingle_of_ne R h_ne.symm]

/- `CategoryAlgebra R C` for `Fintype C` is a unital algebra. -/
instance : Algebra R (CategoryAlgebra R C) where
  algebraMap :=
    { toFun := fun r ↦ r • (1 : CategoryAlgebra R C)
      map_one' := one_smul R 1
      map_zero' := zero_smul R 1
      map_add' := fun r s ↦ add_smul r s 1
      map_mul' := fun r s ↦ by rw [mul_smul, smul_mul_assoc, one_mul] }
  commutes' := fun r x ↦ by simp
  smul_def' := fun r x ↦ by simp

section UnitalUniversalProperty

variable {A : Type*} [Semiring A] [Algebra R A]
variable (C A)

/-- `UnitalHom` extends `Hom` for morphisms to algebras, where the sum of the
identities maps to `1`. -/
@[ext]
structure UnitalHom extends Hom R C A where
  /- Identity is mapped to identity. -/
  map_one' : ∑ x : C, toFun x x (𝟙 x) = 1

variable {C A}

instance : CoeFun (UnitalHom R C A) (fun _ ↦ ∀ x y : C, (x ⟶ y) →ₗ[R] A) where
  coe rep := rep.toFun

@[simp]
lemma lift_one (rep : UnitalHom R C A) : lift R rep.toHom 1 = 1 := by
  rw [one_def, map_sum]
  rw [← rep.map_one']
  apply Finset.sum_congr rfl
  intro x _
  rw [lift_of R rep.toHom]

/-- The universal extension of a composition-preserving family of maps
to a global algebra homomorphism on the category algebra. -/
def unitalLift (rep : UnitalHom R C A) : CategoryAlgebra R C →ₐ[R] A :=
  { lift R rep.toHom with
    map_one' := lift_one R rep
    commutes' := fun r ↦ by
      rw [NonUnitalAlgHom.toFun_eq_coe, Algebra.algebraMap_eq_smul_one]
      rw [map_smul, lift_one R rep, Algebra.algebraMap_eq_smul_one] }

/-- The universal property of the category algebra, expressed as an equivalence
of types between `UnitalHom R C A` and `CategoryAlgebra R C →ₐ[R] A`. -/
def unitalLiftEquiv : UnitalHom R C A ≃ (CategoryAlgebra R C →ₐ[R] A) where
  toFun  := unitalLift R
  invFun φ := {
    toHom := (liftEquiv R).symm (φ : CategoryAlgebra R C →ₙₐ[R] A)
    map_one' := by
      have h_one := φ.map_one
      rw [one_def, map_sum] at h_one
      exact h_one
  }
  left_inv rep := by
    ext x y f
    exact lift_of R rep.toHom x y f
  right_inv φ := by
    apply DFunLike.ext
    intro x
    exact DFunLike.congr_fun ((liftEquiv R).right_inv (φ : CategoryAlgebra R C →ₙₐ[R] A)) x

end UnitalUniversalProperty
end Unital
end CategoryAlgebra
end CategoryTheory.Linear
