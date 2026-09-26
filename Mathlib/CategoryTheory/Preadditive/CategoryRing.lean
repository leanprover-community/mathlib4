/-
Copyright (c) 2025 Bernhard Reinke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bernhard Reinke, Ray Shang
-/

module

public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.CategoryTheory.Linear.Basic

/-!
# Category ring of a preadditive category

Given a preadditive category `C`, its category ring `CategoryRing C` is the non-unital ring
whose underlying additive group is the direct sum of all of its morphism groups `X ⟶ Y`, and
whose multiplication is induced by composition: the product of a morphism `f : X ⟶ Y` with a
morphism `g : Z ⟶ W` is `f ≫ g` when `Y = Z`, and `0` otherwise. When `C` is `R`-linear this ring
is a (non-unital) `R`-algebra, and when `C` has finitely many objects it is unital, with
unit `∑ X, 𝟙 X`.

This file formalizes `CategoryRing C` and its structure and universal property
when `C` is preadditive, `R`-linear, finite type, and both finite type and `R`-linear. For example,
when `C` is merely preadditive, the universal property of `CategoryRing C` is: non-unital ring
homomorphisms out of `CategoryRing C` correspond to `LiftData`, the data of a
compatible family of additive maps `(X ⟶ Y) →+ A` for a `NonUnitalNonAssocSemiring A`.

## Main definitions

* `CategoryRing C`: the category ring of a preadditive category `C`.
* `CategoryRing.of`: the canonical inclusion map `(X ⟶ Y) →+ CategoryRing C` for all `X Y : C`.
* `LiftData`: the structure for the data of a compatible family of additive maps `(X ⟶ Y) →+ A` for
  a `NonUnitalNonAssocSemiring A`.
* `CategoryRing.lift`: the non-unital ring homomorphism `CategoryRing C →ₙ+* A` induced by
  an instance of `LiftData`.
* `LinearLiftData`: an extension of `LiftData` when `C` is `R`-linear and `A` is a
  non-unital `R`-algebra. The additive maps to `A` are compatible with scalar multiplication.
* `linearLift`: the non-unital `R`-algebra homomorphism `CategoryRing C →ₙₐ[R] A`
  induced by an instance of `LinearLiftData`.
* `UnitalLiftData`: an extension of `LiftData` when `C` is finite type and `A` is a semiring.
  The sum of the images of the identity morphisms is required to be the unit in `A`.
* `unitalLift`: the ring homomorphism `CategoryRing C →+* A` induced by an instance
  of `UnitalLiftData`.
* `UnitalLinearLiftData`: an extension of `LinearLiftData` and `UnitalLiftData` when `C` is
  both `R`-linear and finite type, and `A` is a `R`-algebra.
* `unitalLinearLift`: the `R`-algebra homomorphism `CategoryRing C →ₐ[R] A` induced by an instance
  of `UnitalLinearLiftData`.

## Main results

* `CategoryRing C` is a non-unital ring when `C` is preadditive.
* `CategoryRing C` is a non-unital `R`-algebra when `C` is also `R`-linear.
* `CategoryRing C` is a ring when `C` is finite type.
* `CategoryRing C` is a `R`-algebra when `C` is also `R`-linear and finite type.
* `liftEquiv`: an equivalence of types `LiftData C A ≃ (CategoryRing C →ₙ+* A)`.
* `linearLiftEquiv`: an equivalence of types `LinearLiftData R C A ≃ (CategoryRing C →ₙₐ[R] A)`
* `unitalLiftEquiv`: an equivalence of types `UnitalLiftData C A ≃ (CategoryRing C →+* A)`.
* `unitalLinearLiftEquiv`: an equivalence of
  types `UnitalLinearLiftData R C A ≃ (CategoryRing C →ₐ[R] A)`.

## Implementation notes

* `CategoryRing C` is defined as a doubly-indexed direct sum `⨁ X, ⨁ Y, X ⟶ Y`, rather than as a
single direct sum indexed by pairs `(X, Y) : C × C`, to avoid as much as possible propositional
equality of objects in `C`.

* A non-unital `R`-algebra `A` is the following:
   ```lean
   variable [CommSemiring R] [NonUnitalSemiring A]
   variable [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
   ```
  This convention follows the convention declared in the implementation notes
  of  `Mathlib/Algebra/Algebra/Defs.lean`.

-/

@[expose] public section

universe w' w v u

namespace CategoryTheory.Preadditive

open DirectSum
open CategoryTheory.Preadditive

/-- The category ring constructed from a preadditive category `C`. -/
abbrev CategoryRing (C : Type u) [Category.{v} C] [Preadditive C] := ⨁ (X : C), ⨁ (Y : C), X ⟶ Y

namespace CategoryRing

variable {C : Type u} [Category.{v} C] [Preadditive C]

lemma leftComp_apply {X Y W : C} (f : X ⟶ Y) (g : Y ⟶ W) :
    CategoryTheory.Preadditive.leftComp W f g = f ≫ g :=
  rfl

variable [DecidableEq C]

/-- The canonical inclusion of a morphism `f : X ⟶ Y` into `CategoryRing C`. -/
protected def of (X Y : C) : (X ⟶ Y) →+ CategoryRing C :=
  (DirectSum.of (fun Z ↦ ⨁ W, Z ⟶ W) X).comp (DirectSum.of (fun W ↦ X ⟶ W) Y)

/-- Two additive maps out of `CategoryRing C` agree if they agree on every basis
morphism. Tagged `@[ext high]` so that the `ext` tactic targets basis morphisms directly, rather
than the generic `AddMonoidHom` extensionality lemma for the underlying (singly-indexed) direct
sum. -/
@[ext high]
theorem addHom_ext {γ : Type w'} [AddZeroClass γ] {f g : CategoryRing C →+ γ}
    (h : ∀ (X Y : C) (f' : X ⟶ Y), f (CategoryRing.of X Y f') = g (CategoryRing.of X Y f')) :
    f = g := by
  apply DirectSum.addHom_ext
  intro X y
  induction y using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | of Y f' => exact h ..
  | add Y Y' hy hy' =>
    rw [map_add, map_add, hy, hy']
    simp

/-- A custom induction principle to unwrap the nested direct sums of `CategoryRing C`. -/
@[elab_as_elim]
protected lemma induction {P : CategoryRing C → Prop}
    (h_zero : P 0)
    (h_add : ∀ a b, P a → P b → P (a + b))
    (h_of : ∀ X Y (f : X ⟶ Y), P (CategoryRing.of X Y f))
    (x : CategoryRing C) : P x := by
  refine DirectSum.induction_on x h_zero ?_ h_add
  intro X v
  refine DirectSum.induction_on v ?_ (h_of X) ?_
  · rw [map_zero]
    exact h_zero
  · intro a b ha hb
    rw [map_add]
    exact h_add _ _ ha hb

/-- Multiply a basis morphism `f : X ⟶ Y` across the inner sum `⨁ W, Y ⟶ W`. -/
def compInner (X Y : C) (f : X ⟶ Y) : (⨁ W, Y ⟶ W) →+ (⨁ W, X ⟶ W) :=
  DirectSum.toAddMonoid (fun W ↦
    (DirectSum.of (fun W' ↦ X ⟶ W') W).comp (CategoryTheory.Preadditive.leftComp W f))

lemma compInner_add (X Y : C) (f₁ f₂ : X ⟶ Y) :
    compInner X Y (f₁ + f₂) = compInner X Y f₁ + compInner X Y f₂ := by
  ext W g
  rw [AddMonoidHom.add_comp, AddMonoidHom.add_apply, compInner, compInner, compInner]
  rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply]
  rw [DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of]
  rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply]
  rw [leftComp_apply, leftComp_apply, leftComp_apply, add_comp, map_add]

lemma compInner_zero (X Y : C) : compInner X Y 0 = 0 := by
  ext W g
  rw [AddMonoidHom.zero_comp, AddMonoidHom.zero_apply, compInner, AddMonoidHom.comp_apply]
  rw [DirectSum.toAddMonoid_of, AddMonoidHom.comp_apply, leftComp_apply]
  rw [CategoryTheory.Limits.zero_comp, map_zero]

/-- Additive projection out of the category ring onto the sum of all morphisms with source `Y`. -/
protected def projSource (Y : C) : CategoryRing C →+ ⨁ W, Y ⟶ W where
  toFun V := V Y
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Multiply a basis morphism `f : X ⟶ Y` with the entire category ring. -/
def compSingle (X Y : C) (f : X ⟶ Y) : CategoryRing C →+ CategoryRing C :=
  (DirectSum.of (fun Z ↦ ⨁ W, Z ⟶ W) X).comp ((compInner X Y f).comp (CategoryRing.projSource Y))

lemma compSingle_zero (X Y : C) : compSingle X Y 0 = 0 := by
  rw [compSingle, compInner_zero, AddMonoidHom.zero_comp, AddMonoidHom.comp_zero]

lemma compSingle_add (X Y : C) (f₁ f₂ : X ⟶ Y) :
    compSingle X Y (f₁ + f₂) = compSingle X Y f₁ + compSingle X Y f₂ := by
  rw [compSingle, compSingle, compSingle, compInner_add, AddMonoidHom.add_comp]
  rw [AddMonoidHom.comp_add]

/-- The full bilinear multiplication map for the category ring bundled as an AddMonoidHom. -/
def mul' : CategoryRing C →+ CategoryRing C →+ CategoryRing C :=
  DirectSum.toAddMonoid (fun X ↦
    DirectSum.toAddMonoid (fun Y ↦
      { toFun := fun f ↦ compSingle X Y f
        map_zero' := compSingle_zero X Y
        map_add' := fun f₁ f₂ ↦ compSingle_add X Y f₁ f₂ }))

instance : Mul (CategoryRing C) := ⟨fun f g => mul' f g⟩

lemma mul_def (x y : CategoryRing C) : x * y = mul' x y := rfl

/-- Multiplying a basis morphism against the entire category ring on the left unwraps `*` back
into `compSingle`. -/
lemma of_mul (X Y : C) (f : X ⟶ Y) (b : CategoryRing C) :
    CategoryRing.of X Y f * b = compSingle X Y f b := by
  rw [mul_def, mul', CategoryRing.of, AddMonoidHom.comp_apply]
  rw [DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of]
  rfl

/-- When the domain and codomain match, `compSingle f g` yields
`f ≫ g`. -/
lemma compSingle_of_eq (X Y Z : C) (f : X ⟶ Y) (g : Y ⟶ Z) :
    compSingle X Y f (CategoryRing.of Y Z g) = CategoryRing.of X Z (f ≫ g) := by
  rw [compSingle, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply]
  have h_eval : CategoryRing.projSource Y (CategoryRing.of Y Z g)
      = DirectSum.of (fun W ↦ Y ⟶ W) Z g :=
    DFinsupp.single_eq_same
  rw [h_eval, compInner, DirectSum.toAddMonoid_of, AddMonoidHom.comp_apply, leftComp_apply]
  rfl

/-- When the domain and codomain mismatch, `compSingle` yields 0. -/
lemma compSingle_of_ne {X Y Z W : C} (h : Y ≠ Z) (f : X ⟶ Y) (g : Z ⟶ W) :
    compSingle X Y f (CategoryRing.of Z W g) = 0 := by
  rw [compSingle, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply]
  have h_eval : CategoryRing.projSource Y (CategoryRing.of Z W g) = 0 := DFinsupp.single_eq_of_ne h
  rw [h_eval, map_zero, map_zero]

lemma zero_mul' (x : CategoryRing C) : 0 * x = 0 := by
  rw [mul_def, map_zero, AddMonoidHom.zero_apply]

lemma mul_zero' (x : CategoryRing C) : x * 0 = 0 := by
  rw [mul_def, map_zero]

/-- Multiplication satisfies a generalized associativity relation across basis morphisms. -/
theorem of_mul_assoc (X₁ Y₁ X₂ Y₂ X₃ Y₃ : C) (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) (h : X₃ ⟶ Y₃) :
    (CategoryRing.of X₁ Y₁ f * CategoryRing.of X₂ Y₂ g) * CategoryRing.of X₃ Y₃ h
    = CategoryRing.of X₁ Y₁ f
    * (CategoryRing.of X₂ Y₂ g * CategoryRing.of X₃ Y₃ h) := by
  by_cases h12 : Y₁ = X₂ <;> by_cases h23 : Y₂ = X₃
  · subst h12 h23
    rw [of_mul, compSingle_of_eq, of_mul, compSingle_of_eq, of_mul, of_mul, compSingle_of_eq]
    rw [compSingle_of_eq, Category.assoc]
  · subst h12
    rw [of_mul, compSingle_of_eq, of_mul, compSingle_of_ne h23, of_mul, of_mul]
    rw [compSingle_of_ne h23, map_zero]
  · subst h23
    rw [of_mul, compSingle_of_ne h12, zero_mul', of_mul, of_mul, compSingle_of_eq]
    rw [compSingle_of_ne h12]
  · rw [of_mul, compSingle_of_ne h12, zero_mul', of_mul, of_mul, compSingle_of_ne h23, map_zero]

lemma mul_add' (x y z : CategoryRing C) : x * (y + z) = x * y + x * z := by
  rw [mul_def, mul_def, mul_def, map_add]

lemma add_mul' (x y z : CategoryRing C) : (x + y) * z = x * z + y * z := by
  rw [mul_def, mul_def, mul_def, map_add, AddMonoidHom.add_apply]

/-- The multiplication on `CategoryRing C` is associative. -/
lemma mul_assoc' (x y z : CategoryRing C) :
    (x * y) * z = x * (y * z) := by
  induction x using CategoryRing.induction with
  | h_zero => rw [zero_mul', zero_mul', zero_mul']
  | h_add _ _ h1 h2 => rw [add_mul', add_mul', add_mul', h1, h2]
  | h_of X₁ Y₁ f =>
    induction y using CategoryRing.induction with
    | h_zero => rw [mul_zero', zero_mul', mul_zero']
    | h_add _ _ h1 h2 => rw [add_mul', mul_add', mul_add', add_mul', h1, h2]
    | h_of X₂ Y₂ g =>
      induction z using CategoryRing.induction with
      | h_zero => rw [mul_zero', mul_zero', mul_zero']
      | h_add _ _ h1 h2 => rw [mul_add', mul_add', mul_add', h1, h2]
      | h_of X₃ Y₃ h => exact of_mul_assoc X₁ Y₁ X₂ Y₂ X₃ Y₃ f g h

instance : NonUnitalRing (CategoryRing C) where
  zero_mul := zero_mul'
  mul_zero := mul_zero'
  left_distrib := mul_add'
  right_distrib  := add_mul'
  mul_assoc := mul_assoc'

section Linear

variable (R : Type w) [CommSemiring R] [Linear R C]

/-- The canonical inclusion of a morphism `f : X ⟶ Y` into the category ring, bundled as a
linear map. -/
protected def lof (X Y : C) : (X ⟶ Y) →ₗ[R] CategoryRing C :=
  (DirectSum.lof R C (fun Z ↦ ⨁ W, Z ⟶ W) X).comp (DirectSum.lof R C (fun W ↦ X ⟶ W) Y)

lemma lof_eq_of (X Y : C) (f : X ⟶ Y) : CategoryRing.lof R X Y f = CategoryRing.of X Y f :=
  rfl

/-- Evaluates scalar multiplication pushed through the basis inclusion. -/
lemma of_smul (X Y : C) (r : R) (f : X ⟶ Y) :
    CategoryRing.of X Y (r • f) = r • CategoryRing.of X Y f := by
  have h_lin := LinearMap.map_smul (CategoryRing.lof R X Y) r f
  rw [lof_eq_of, lof_eq_of] at h_lin
  exact h_lin

instance : IsScalarTower R (CategoryRing C) (CategoryRing C) where
  smul_assoc r a b := by
    revert a b
    apply CategoryRing.induction
    · intro b
      rw [smul_zero, zero_smul, smul_zero]
    · intro a₁ a₂ ha₁ ha₂ b
      conv_lhs => rw [smul_add, smul_eq_mul, add_mul, ← smul_eq_mul, ← smul_eq_mul]
      conv_rhs => rw [smul_eq_mul, add_mul, ← smul_eq_mul, ← smul_eq_mul, smul_add]
      rw [ha₁ b, ha₂ b]
    · intro X Y f
      apply CategoryRing.induction
      · rw [smul_zero, smul_zero, smul_zero]
      · intro b₁ b₂ hb₁ hb₂
        rw [smul_add, hb₁, hb₂, smul_add, smul_add]
      · intro Z W g
        by_cases h : Y = Z
        · subst h
          rw [← of_smul R X Y r f, smul_eq_mul, of_mul, compSingle_of_eq, smul_eq_mul, of_mul]
          rw [compSingle_of_eq, CategoryTheory.Linear.smul_comp, of_smul R]
        · rw [← of_smul R X Y r f, smul_eq_mul, of_mul, compSingle_of_ne h, smul_eq_mul, of_mul]
          rw [compSingle_of_ne h, smul_zero]

instance : SMulCommClass R (CategoryRing C) (CategoryRing C) where
  smul_comm r a b := by
    revert a b
    apply CategoryRing.induction
    · intro b
      rw [zero_smul, smul_zero, zero_smul]
    · intro a₁ a₂ ha₁ ha₂ b
      conv_lhs => rw [smul_eq_mul, add_mul, ← smul_eq_mul, ← smul_eq_mul, smul_add]
      conv_rhs => rw [smul_eq_mul, add_mul, ← smul_eq_mul, ← smul_eq_mul]
      rw [ha₁ b, ha₂ b]
    · intro X Y f
      apply CategoryRing.induction
      · rw [smul_zero, smul_zero, smul_zero]
      · intro b₁ b₂ hb₁ hb₂
        rw [smul_add, smul_add, hb₁, hb₂, smul_add, smul_add]
      · intro Z W g
        by_cases h : Y = Z
        · subst h
          rw [← of_smul R Y W r g, smul_eq_mul, of_mul, compSingle_of_eq, smul_eq_mul, of_mul]
          rw [compSingle_of_eq, CategoryTheory.Linear.comp_smul, of_smul R]
        · rw [← of_smul R Z W r g, smul_eq_mul, of_mul, compSingle_of_ne h, smul_eq_mul, of_mul]
          rw [compSingle_of_ne h, smul_zero]

end Linear

section Unital

variable [Fintype C]

/-- When `C` with finitely many objects, the unit of `CategoryRing C` is the sum of the identity
morphisms, `∑ X, 𝟙 X`. -/
def one' : CategoryRing C := ∑ X : C, CategoryRing.of X X (𝟙 X)

instance : One (CategoryRing C) := ⟨one'⟩

lemma one_def : (1 : CategoryRing C) = ∑ X : C, CategoryRing.of X X (𝟙 X) := rfl

lemma one_mul' (a : CategoryRing C) : 1 * a = a := by
  induction a using CategoryRing.induction with
  | h_zero => rw [mul_zero]
  | h_add a b ha hb => rw [mul_add, ha, hb]
  | h_of Y Z g =>
    have hvanish : ∀ X ≠ Y, CategoryRing.of X X (𝟙 X) * CategoryRing.of Y Z g = 0 := by
      intro X hxy
      rw [of_mul, compSingle_of_ne hxy]
    rw [one_def, Finset.sum_mul, Fintype.sum_eq_single Y hvanish, of_mul, compSingle_of_eq,
      Category.id_comp]

lemma mul_one' (a : CategoryRing C) : a * 1 = a := by
  induction a using CategoryRing.induction with
  | h_zero => rw [zero_mul]
  | h_add a b ha hb => rw [add_mul, ha, hb]
  | h_of X Y f =>
    have hvanish : ∀ Z ≠ Y, CategoryRing.of X Y f * CategoryRing.of Z Z (𝟙 Z) = 0 := by
      intro Z hzy
      rw [of_mul, compSingle_of_ne hzy.symm]
    rw [one_def, Finset.mul_sum, Fintype.sum_eq_single Y hvanish, of_mul, compSingle_of_eq,
      Category.comp_id]

instance : Ring (CategoryRing C) :=
  { (inferInstance : NonUnitalRing (CategoryRing C)),
    (inferInstance : AddCommGroup (CategoryRing C)) with
    one_mul := one_mul'
    mul_one := mul_one' }

end Unital

section UnitalLinear

variable (R : Type w) [CommSemiring R] [Linear R C] [Fintype C]

instance : Algebra R (CategoryRing C) :=
  Algebra.ofModule smul_mul_assoc mul_smul_comm

end UnitalLinear

section UniversalPropertyPreadditive

variable {A : Type*} [NonUnitalNonAssocSemiring A]

/-- The data needed to build a non-unital ring homomorphism out of `CategoryRing C` via
`CategoryRing.lift`: a compatible family of additive maps out of each morphism-set of `C`, valued
in a fixed `NonUnitalNonAssocSemiring A`. Compatibility means multiplicativity along composition
(`map_comp`) and vanishing on non-composable pairs (`map_ortho`). -/
@[ext]
structure LiftData (C : Type u) [Category.{v} C] [Preadditive C]
    (A : Type*) [NonUnitalNonAssocSemiring A] where
  /-- The underlying family of additive maps, one for each morphism-set of `C`. -/
  toFun : ∀ (X Y : C), (X ⟶ Y) →+ A
  /-- The family is multiplicative along composition of morphisms. -/
  map_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), toFun X Z (f ≫ g) = toFun X Y f * toFun Y Z g
  /-- The family vanishes on pairs of morphisms that are not composable. -/
  map_ortho : ∀ {X Y Z W : C} (f : X ⟶ Y) (g : Z ⟶ W), Y ≠ Z → toFun X Y f * toFun Z W g = 0

instance : CoeFun (LiftData C A) (fun _ ↦ ∀ X Y : C, (X ⟶ Y) →+ A) where
  coe data := data.toFun

/-- Restrict an additive map out of the category ring along the basis inclusion
`CategoryRing.of X Y`, to get an additive map on `X → Y`. -/
def restrictOf {F : Type*} [FunLike F (CategoryRing C) A]
    [AddMonoidHomClass F (CategoryRing C) A] (φ : F) (X Y : C) : (X ⟶ Y) →+ A where
  toFun f := φ (CategoryRing.of X Y f)
  map_zero' := by rw [map_zero, map_zero]
  map_add' f₁ f₂ := by rw [map_add, map_add]

lemma restrictOf_apply {F : Type*} [FunLike F (CategoryRing C) A]
    [AddMonoidHomClass F (CategoryRing C) A] (φ : F) (X Y : C) (f : X ⟶ Y) :
    restrictOf φ X Y f = φ (CategoryRing.of X Y f) := rfl

/-- The additive map underlying `CategoryRing.lift data`, forgetting that
it respects multiplication. -/
protected def toAddMonoidHom (data : LiftData C A) : CategoryRing C →+ A :=
  DirectSum.toAddMonoid (fun X ↦ DirectSum.toAddMonoid (fun Y ↦ data.toFun X Y))

protected lemma toAddMonoidHom_of (data : LiftData C A) (X Y : C) (f : X ⟶ Y) :
    CategoryRing.toAddMonoidHom data (CategoryRing.of X Y f) = data.toFun X Y f := by
  rw [CategoryRing.toAddMonoidHom, CategoryRing.of, AddMonoidHom.comp_apply]
  rw [DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of]

protected lemma toAddMonoidHom_map_mul (data : LiftData C A) (a b : CategoryRing C) :
    CategoryRing.toAddMonoidHom data (a * b) = CategoryRing.toAddMonoidHom data a
    * CategoryRing.toAddMonoidHom data b := by
  induction a using CategoryRing.induction with
  | h_zero => rw [zero_mul, map_zero, zero_mul]
  | h_add a₁ a₂ h1 h2 => rw [add_mul, map_add, map_add, h1, h2, add_mul]
  | h_of X Y f =>
    induction b using CategoryRing.induction with
    | h_zero => rw [mul_zero, map_zero, mul_zero]
    | h_add b₁ b₂ h1 h2 => rw [mul_add, map_add, map_add, h1, h2, mul_add]
    | h_of Z W g =>
      by_cases h : Y = Z
      · subst h
        rw [of_mul, compSingle_of_eq, CategoryRing.toAddMonoidHom_of]
        rw [CategoryRing.toAddMonoidHom_of, CategoryRing.toAddMonoidHom_of, data.map_comp]
      · rw [of_mul, compSingle_of_ne h, map_zero, CategoryRing.toAddMonoidHom_of]
        rw [CategoryRing.toAddMonoidHom_of, data.map_ortho _ _ h]

/-- The non-unital ring homomorphism out of the category ring induced by an instance
of `LiftData`. -/
protected def lift (data : LiftData C A) : CategoryRing C →ₙ+* A :=
  { CategoryRing.toAddMonoidHom data with map_mul' := CategoryRing.toAddMonoidHom_map_mul data }

protected lemma lift_of (data : LiftData C A) (X Y : C) (f : X ⟶ Y) :
    CategoryRing.lift data (CategoryRing.of X Y f) = data.toFun X Y f :=
  CategoryRing.toAddMonoidHom_of data X Y f

/-- The `LiftData` for `C` valued in `A` given by a non-unital ring homomorphism out of the
category ring. -/
def _root_.NonUnitalRingHom.toLiftData (φ : CategoryRing C →ₙ+* A) : LiftData C A where
  toFun := restrictOf φ
  map_comp f g := by
    rw [restrictOf_apply, restrictOf_apply, restrictOf_apply,
      ← map_mul, of_mul, compSingle_of_eq]
  map_ortho f g h := by
    rw [restrictOf_apply, restrictOf_apply, ← map_mul, of_mul,
      compSingle_of_ne h, map_zero]

lemma toLiftData_lift (data : LiftData C A) : (CategoryRing.lift data).toLiftData = data := by
  ext X Y f
  rw [NonUnitalRingHom.toLiftData, restrictOf_apply, CategoryRing.lift_of]

lemma lift_toLiftData (φ : CategoryRing C →ₙ+* A) : CategoryRing.lift φ.toLiftData = φ := by
  ext a
  induction a using CategoryRing.induction with
  | h_zero => rw [map_zero, map_zero]
  | h_add a b ha hb => rw [map_add, map_add, ha, hb]
  | h_of X Y f => rw [CategoryRing.lift_of, NonUnitalRingHom.toLiftData, restrictOf_apply]

/-- The universal property of the category ring of a preadditive category: non-unital ring
homomorphisms out of `CategoryRing C` correspond to lift data for `C`. -/
protected def liftEquiv : LiftData C A ≃ (CategoryRing C →ₙ+* A) where
  toFun := CategoryRing.lift
  invFun := NonUnitalRingHom.toLiftData
  left_inv := toLiftData_lift
  right_inv := lift_toLiftData

end UniversalPropertyPreadditive

section UniversalPropertyLinear

variable (R : Type w) [CommSemiring R] [Linear R C]
variable {A : Type*} [NonUnitalNonAssocSemiring A] [Module R A]
variable [IsScalarTower R A A] [SMulCommClass R A A]

/-- The data needed to build a non-unital `R`-algebra homomorphism out of `CategoryRing C` via
`CategoryRing.linearLift`: `LiftData` for an `R`-linear category `C`, together with compatibility
with scalar multiplication (`map_smul'`). -/
@[ext]
structure LinearLiftData (R : Type w) [CommSemiring R]
    (C : Type u) [Category.{v} C] [Preadditive C] [DecidableEq C] [Linear R C]
    (A : Type*) [NonUnitalNonAssocSemiring A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] extends LiftData C A where
  /-- The underlying family of additive maps is compatible with scalar multiplication. -/
  map_smul' : ∀ (X Y : C) (r : R) (f : X ⟶ Y), toFun X Y (r • f) = r • toFun X Y f

lemma lift_toLiftData_smul (data : LinearLiftData R C A) (r : R) (a : CategoryRing C) :
    CategoryRing.lift data.toLiftData (r • a) = r • CategoryRing.lift data.toLiftData a := by
  induction a using CategoryRing.induction with
  | h_zero => rw [smul_zero, map_zero, smul_zero]
  | h_add a b ha hb => rw [smul_add, map_add, ha, hb, map_add, smul_add]
  | h_of X Y f => rw [← of_smul R X Y r f, CategoryRing.lift_of, CategoryRing.lift_of]
                  rw [data.map_smul']

/-- The non-unital algebra homomorphism out of the category ring induced by linear lift data. -/
def linearLift (data : LinearLiftData R C A) : CategoryRing C →ₙₐ[R] A :=
  { CategoryRing.lift data.toLiftData with map_smul' := lift_toLiftData_smul R data }

lemma linearLift_of (data : LinearLiftData R C A) (X Y : C) (f : X ⟶ Y) :
    CategoryRing.linearLift R data (CategoryRing.of X Y f) = data.toFun X Y f :=
  CategoryRing.lift_of data.toLiftData X Y f

/-- The linear lift data for `C` valued in `A` induced by a non-unital algebra homomorphism out of
the category ring. -/
def _root_.NonUnitalAlgHom.toLiftData (ψ : CategoryRing C →ₙₐ[R] A) : LinearLiftData R C A where
  toFun := restrictOf ψ
  map_comp f g := by
    rw [restrictOf_apply, restrictOf_apply, restrictOf_apply,
      ← map_mul, of_mul, compSingle_of_eq]
  map_ortho f g h := by
    rw [restrictOf_apply, restrictOf_apply, ← map_mul, of_mul,
      compSingle_of_ne h, map_zero]
  map_smul' X Y r f := by
    rw [restrictOf_apply, restrictOf_apply, of_smul, map_smul]

lemma toLiftData_linearLift (data : LinearLiftData R C A) :
    (CategoryRing.linearLift R data).toLiftData = data := by
  ext X Y f
  rw [NonUnitalAlgHom.toLiftData, restrictOf_apply, linearLift_of]

lemma linearLift_toLiftData (ψ : CategoryRing C →ₙₐ[R] A) :
    CategoryRing.linearLift R ψ.toLiftData = ψ := by
  ext a
  induction a using CategoryRing.induction with
  | h_zero => rw [map_zero, map_zero]
  | h_add a b ha hb => rw [map_add, map_add, ha, hb]
  | h_of X Y f => rw [linearLift_of, NonUnitalAlgHom.toLiftData, restrictOf_apply]

/-- The universal property of the category ring of a linear category: non-unital algebra
homomorphisms out of `CategoryRing C` correspond to linear lift data for `C`. -/
def linearLiftEquiv : LinearLiftData R C A ≃ (CategoryRing C →ₙₐ[R] A) where
  toFun := CategoryRing.linearLift R
  invFun := NonUnitalAlgHom.toLiftData R
  left_inv := toLiftData_linearLift R
  right_inv := linearLift_toLiftData R

end UniversalPropertyLinear

section UniversalPropertyUnital

variable [Fintype C]
variable {A : Type*} [Semiring A]

/-- The data needed to build a (unital) ring homomorphism out of `CategoryRing C` via
`CategoryRing.unitalLift`: `LiftData` for a category `C` with finitely many objects, together with
the condition that the images of the identity morphisms sum to `1` (`map_one'`). -/
@[ext]
structure UnitalLiftData (C : Type u) [Category.{v} C]
    [Preadditive C] [DecidableEq C] [Fintype C]
    (A : Type*) [Semiring A] extends LiftData C A where
  /-- The images of the identity morphisms sum to `1`. -/
  map_one' : ∑ X : C, toFun X X (𝟙 X) = 1

lemma lift_toLiftData_one (data : UnitalLiftData C A) : CategoryRing.lift data.toLiftData 1
    = 1 := by
  have h : (∑ X : C, CategoryRing.lift data.toLiftData (CategoryRing.of X X (𝟙 X)))
      = ∑ X : C, data.toFun X X (𝟙 X) :=
    Finset.sum_congr rfl fun X _ ↦ CategoryRing.lift_of data.toLiftData X X (𝟙 X)
  rw [one_def, map_sum, h, data.map_one']

/-- The (unital) ring homomorphism out of the category ring induced by unital lift data. -/
def unitalLift (data : UnitalLiftData C A) : CategoryRing C →+* A :=
  { CategoryRing.lift data.toLiftData with map_one' := lift_toLiftData_one data }

lemma unitalLift_of (data : UnitalLiftData C A) (X Y : C) (f : X ⟶ Y) :
    unitalLift data (CategoryRing.of X Y f) = data.toFun X Y f :=
  CategoryRing.lift_of data.toLiftData X Y f

/-- The unital lift data for `C` valued in `A` induced by a ring homomorphism out of the category
ring. -/
def _root_.RingHom.toUnitalLiftData (φ : CategoryRing C →+* A) : UnitalLiftData C A where
  toFun := restrictOf φ
  map_comp f g := by
    rw [restrictOf_apply, restrictOf_apply, restrictOf_apply,
      ← map_mul, of_mul, compSingle_of_eq]
  map_ortho f g h := by
    rw [restrictOf_apply, restrictOf_apply, ← map_mul, of_mul,
      compSingle_of_ne h, map_zero]
  map_one' := by
    have h : (∑ X : C, restrictOf φ X X (𝟙 X)) = ∑ X : C, φ (CategoryRing.of X X (𝟙 X)) :=
      Finset.sum_congr rfl fun X _ ↦ restrictOf_apply φ X X (𝟙 X)
    rw [h, ← map_sum, ← one_def, map_one]

lemma toUnitalLiftData_unitalLift (data : UnitalLiftData C A) :
    (unitalLift data).toUnitalLiftData = data := by
  ext X Y f
  rw [RingHom.toUnitalLiftData, restrictOf_apply, unitalLift_of]

lemma unitalLift_toUnitalLiftData (φ : CategoryRing C →+* A) :
    unitalLift φ.toUnitalLiftData = φ := by
  apply RingHom.ext
  intro a
  induction a using CategoryRing.induction with
  | h_zero => rw [map_zero, map_zero]
  | h_add a b ha hb => rw [map_add, map_add, ha, hb]
  | h_of X Y f => rw [unitalLift_of, RingHom.toUnitalLiftData, restrictOf_apply]

/-- The universal property of the category ring of a preadditive category with finitely many
objects: ring homomorphisms out of `CategoryRing C` correspond to unital lift data for
`C`. -/
def unitalLiftEquiv : UnitalLiftData C A ≃ (CategoryRing C →+* A) where
  toFun := unitalLift
  invFun := RingHom.toUnitalLiftData
  left_inv := toUnitalLiftData_unitalLift
  right_inv := unitalLift_toUnitalLiftData

end UniversalPropertyUnital

section UniversalPropertyUnitalLinear

variable (R : Type w) [CommSemiring R] [Linear R C] [Fintype C]
variable {A : Type*} [Semiring A] [Algebra R A]

/-- The data needed to build a (unital) `R`-algebra homomorphism out of `CategoryRing C` via
`CategoryRing.unitalLinearLift`: `LinearLiftData` for a category `C` with finitely many objects,
together with the condition that the images of the identity morphisms sum to `1` (`map_one'`). -/
@[ext]
structure UnitalLinearLiftData (R : Type w) [CommSemiring R] (C : Type u) [Category.{v} C]
    [Preadditive C] [DecidableEq C] [Linear R C] [Fintype C]
    (A : Type*) [Semiring A] [Algebra R A] extends LinearLiftData R C A where
  /-- The images of the identity morphisms sum to `1`. -/
  map_one' : ∑ X : C, toFun X X (𝟙 X) = 1

/-- Forgetting linearity, unital linear lift data is unital lift data. -/
def UnitalLinearLiftData.toUnitalLiftData (data : UnitalLinearLiftData R C A) :
  UnitalLiftData C A := { data.toLiftData with map_one' := data.map_one' }

lemma unitalLinearLift_commutes (data : UnitalLinearLiftData R C A) (r : R) :
    unitalLift data.toUnitalLiftData (algebraMap R (CategoryRing C) r) = algebraMap R A r := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
  have key : unitalLift data.toUnitalLiftData (r • (1 : CategoryRing C))
      = r • unitalLift data.toUnitalLiftData (1 : CategoryRing C) :=
    lift_toLiftData_smul R data.toLinearLiftData r (1 : CategoryRing C)
  rw [key, map_one]

/-- The (unital) algebra homomorphism out of the category ring induced by unital linear
lift data. -/
def unitalLinearLift (data : UnitalLinearLiftData R C A) : CategoryRing C →ₐ[R] A :=
  { unitalLift data.toUnitalLiftData with commutes' := unitalLinearLift_commutes R data }

lemma unitalLinearLift_of (data : UnitalLinearLiftData R C A) (X Y : C) (f : X ⟶ Y) :
    unitalLinearLift R data (CategoryRing.of X Y f) = data.toFun X Y f :=
  unitalLift_of data.toUnitalLiftData X Y f

/-- The unital linear lift data for `C` valued in `A` underlying an algebra homomorphism out of
the category ring. -/
def _root_.AlgHom.toUnitalLinearLiftData (ψ : CategoryRing C →ₐ[R] A) :
    UnitalLinearLiftData R C A where
  toFun := restrictOf ψ
  map_comp f g := by
    rw [restrictOf_apply, restrictOf_apply, restrictOf_apply,
      ← map_mul, of_mul, compSingle_of_eq]
  map_ortho f g h := by
    rw [restrictOf_apply, restrictOf_apply, ← map_mul, of_mul,
      compSingle_of_ne h, map_zero]
  map_smul' X Y r f := by
    rw [restrictOf_apply, restrictOf_apply, of_smul, map_smul]
  map_one' := by
    have h : (∑ X : C, restrictOf ψ X X (𝟙 X)) = ∑ X : C, ψ (CategoryRing.of X X (𝟙 X)) :=
      Finset.sum_congr rfl fun X _ ↦ restrictOf_apply ψ X X (𝟙 X)
    rw [h, ← map_sum, ← one_def, map_one]

lemma toUnitalLinearLiftData_unitalLinearLift (data : UnitalLinearLiftData R C A) :
    (unitalLinearLift R data).toUnitalLinearLiftData = data := by
  ext X Y f
  rw [AlgHom.toUnitalLinearLiftData, restrictOf_apply, unitalLinearLift_of]

lemma unitalLinearLift_toUnitalLinearLiftData (ψ : CategoryRing C →ₐ[R] A) :
    unitalLinearLift R ψ.toUnitalLinearLiftData = ψ := by
  apply AlgHom.ext
  intro a
  induction a using CategoryRing.induction with
  | h_zero => rw [map_zero, map_zero]
  | h_add a b ha hb => rw [map_add, map_add, ha, hb]
  | h_of X Y f =>
    rw [unitalLinearLift_of, AlgHom.toUnitalLinearLiftData, restrictOf_apply]

/-- The universal property of the category ring of a linear category with finitely many objects:
algebra homomorphisms out of `CategoryRing C` correspond to unital linear lift data for
`C`. -/
def unitalLinearLiftEquiv : UnitalLinearLiftData R C A ≃ (CategoryRing C →ₐ[R] A) where
  toFun := unitalLinearLift R
  invFun := AlgHom.toUnitalLinearLiftData R
  left_inv := toUnitalLinearLiftData_unitalLinearLift R
  right_inv := unitalLinearLift_toUnitalLinearLiftData R

end UniversalPropertyUnitalLinear

end CategoryRing
end CategoryTheory.Preadditive
