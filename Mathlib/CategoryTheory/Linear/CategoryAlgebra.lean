/-
Copyright (c) 2025 Bernhard Reinke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bernhard Reinke, Ray Shang
-/

module

public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Ring.Associator
public import Mathlib.CategoryTheory.Linear.Basic

/-!
# Category algebra of a linear category
-/

@[expose] public section

universe w' w v u

namespace CategoryTheory.Linear

open DirectSum
open CategoryTheory.Preadditive

/- Category algebra is constructed from a commutative semiring R and a R-linear category C.
   With abbrev, Catgory algebra inherits all properties of a module.
 -/
abbrev CategoryAlgebra (R : Type w) (C : Type u) [CommSemiring R]  [Category.{v} C] [Preadditive C]
  [Linear R C] := ⨁ (p : C × C), p.1 ⟶ p.2

namespace CategoryAlgebra

variable {R : Type w} [CommSemiring R] {C : Type u} [Category.{v} C] [Preadditive C]
  [Linear R C] [DecidableEq C]

protected def of (a b : C) : (a ⟶ b) →+ CategoryAlgebra R C :=
  DirectSum.of (fun (p : C × C) ↦ p.1 ⟶ p.2) (a,b)

@[ext 10000]
theorem addHom_ext {γ : Type w'} [AddZeroClass γ] ⦃f g : CategoryAlgebra R C →+ γ⦄
    (H : ∀ (X Y : C) (y : X ⟶ Y), f (CategoryAlgebra.of X Y y) = g (CategoryAlgebra.of X Y y)) :
    f = g := DFinsupp.addHom_ext (fun p => H p.1 p.2)

theorem of_eq_single (a b : C) (f : a ⟶ b) :
    (CategoryAlgebra.of a b f : CategoryAlgebra R C) =
    DFinsupp.single (a,b) f := by rfl

/-- Composition is composition if well-defined, otherwise it is 0. -/
def comp₀ (X Y Z W : C) : (X ⟶ Y) →+ (Z ⟶ W) →+ (X ⟶ W) :=
  if h : Y = Z then
    { toFun := fun f ↦ compHom (f ≫ eqToHom h)
      map_add' := by intros; ext; simp
      map_zero' := by ext; simp }
  else
    0

theorem comp₀_assoc (X₁ Y₁ X₂ Y₂ X₃ Y₃ : C) (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) (h : X₃ ⟶ Y₃) :
    ((comp₀ X₁ Y₂ X₃ Y₃) (((comp₀ X₁ Y₁ X₂ Y₂) f) g)) h =
    ((comp₀ X₁ Y₁ X₂ Y₃) f) (((comp₀ X₂ Y₂ X₃ Y₃) g) h)
    := by
  by_cases h₁₂ : Y₁ = X₂ <;> by_cases h₂₃ : Y₂ = X₃ <;>
  simp [comp₀, h₁₂, h₂₃, compHom, Preadditive.leftComp]

/-- The multiplication on the category algebra, defined by linearly extending
the composition of morphisms across the direct sum. -/
def mul' : CategoryAlgebra R C →+ CategoryAlgebra R C →+ CategoryAlgebra R C :=
  DFinsupp.sumAddHom₂ (fun q p ↦ AddMonoidHom.compr₂
  (comp₀ q.1 q.2 p.1 p.2) (CategoryAlgebra.of q.1 p.2))

instance : Mul (CategoryAlgebra R C) := ⟨fun f g => mul' f g⟩

theorem mul_def (f g : CategoryAlgebra R C) :
    f * g = DFinsupp.sumAddHom₂ (fun q p ↦ AddMonoidHom.compr₂
    (comp₀ q.1 q.2 p.1 p.2) (CategoryAlgebra.of q.1 p.2)) f g := rfl

attribute [irreducible] mul'

instance : NonUnitalNonAssocSemiring (CategoryAlgebra R C) where
  left_distrib := fun a b c => by simp only [mul_def ]; erw [map_add]
  right_distrib := fun a b c => by simp only [mul_def]; erw [map_add, AddMonoidHom.add_apply]
  zero_mul := fun a => by simp only [mul_def]; erw [map_zero]; rfl
  mul_zero := fun a => by simp only [mul_def]; erw [map_zero]

theorem mul_of (X₁ Y₁ X₂ Y₂ : C) (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (CategoryAlgebra.of X₁ Y₁ f) * (CategoryAlgebra.of X₂ Y₂ g : (CategoryAlgebra R C)) =
    CategoryAlgebra.of X₁ Y₂ (comp₀ X₁ Y₁ X₂ Y₂ f g) := by
    rw [mul_def]
    simp [CategoryAlgebra.of_eq_single, DFinsupp.sumAddHom₂_single]

theorem mul_assoc' :
    AddMonoidHom.mulLeft₃ (R := (CategoryAlgebra R C)) = AddMonoidHom.mulRight₃ := by
  ext
  simp [mul_of, comp₀_assoc]

instance : NonUnitalSemiring (CategoryAlgebra R C) where
  mul_assoc a b c := by
    have : AddMonoidHom.mulLeft₃ a b c = AddMonoidHom.mulRight₃ a b c := by simp [mul_assoc']
    simpa







section UniversalProperty

variable {A : Type*} [NonUnitalNonAssocSemiring A] [Module R A]

/-- The data of a representation of a linear category `C` in a non-unital algebra `A`.
This consists of a family of linear maps for each hom-set that preserve category composition. -/
structure CatHom (R : Type w) [CommSemiring R] (C : Type u) [Category.{v} C]
  [Preadditive C] [Linear R C] (A : Type*) [NonUnitalNonAssocSemiring A] [Module R A] where
  toFun : ∀ (X Y : C), (X ⟶ Y) →ₗ[R] A
  map_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
    toFun X Z (f ≫ g) = toFun X Y f * toFun Y Z g

variable (F : CatHom R C A)

/-- The universal extension of a composition-preserving family of maps
to a global linear map on the category algebra. -/
def lift : CategoryAlgebra R C →ₗ[R] A :=
  DirectSum.toModule R (C × C) A (fun p => F.toFun p.1 p.2)

/-- The lift evaluates exactly to the underlying map on the canonical inclusions. -/
@[simp]
theorem lift_of (X Y : C) (f : X ⟶ Y) :
    lift F (CategoryAlgebra.of X Y f) = F.toFun X Y f := by
  -- Proof sketch: Unfold `of` and use `DirectSum.toModule_lof`
  -- (or `DFinsupp.sumAddHom_single` depending on your `of` definition).
  sorry

/-- The universal lift preserves the multiplication of the category algebra. -/
theorem lift_mul (a b : CategoryAlgebra R C) :
    lift F (a * b) = lift F a * lift F b := by
  -- Proof sketch: Use `DFinsupp.induction` or `DirectSum.addHom_ext` on `a` and `b`.
  -- Base cases will reduce to `lift_of` and `F.map_comp'`.
  sorry

/-- The uniqueness part of the universal property: Any linear map that preserves
multiplication and agrees on the generators must be exactly `lift F`. -/
theorem lift_unique (Phi : CategoryAlgebra R C →ₗ[R] A)
    (hPhi_mul : ∀ x y, Phi (x * y) = Phi x * Phi y)
    (hPhi_of : ∀ X Y (f : X ⟶ Y), Phi (CategoryAlgebra.of X Y f) = F.toFun X Y f) :
    Phi = lift F := by
  -- Proof sketch: Two linear maps out of a DirectSum are equal if they are equal
  -- on all components. Use `DirectSum.linearMap_ext` and apply `hPhi_of`.
  sorry

end UniversalProperty













section Unital

variable [Fintype C]

def one' : CategoryAlgebra R C :=  ∑ i : C, (CategoryAlgebra.of i i (𝟙 i))

instance : One (CategoryAlgebra R C) := ⟨one'⟩

theorem one_def : (1 : CategoryAlgebra R C) = ∑ i : C, (CategoryAlgebra.of i i (𝟙 i)) := rfl

instance : Semiring (CategoryAlgebra R C) where
  one_mul := by
    have H : (AddMonoidHom.mulLeft (1 : (CategoryAlgebra R C)) = (AddMonoidHom.id _)) := by
      apply CategoryAlgebra.addHom_ext
      rintro X₁ Y₁ f
      simp only [AddMonoidHom.mulLeft, one_def, Finset.sum_mul, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
        mul_of, AddMonoidHom.id_apply]
      rw [Finset.sum_eq_single_of_mem X₁ (Finset.mem_univ _)]
      · simp [comp₀, compHom, Preadditive.leftComp]
      · intro b _ h
        simp [comp₀, h]
    apply DFunLike.congr_fun (h₁ := H)
  mul_one := by
    have H : (AddMonoidHom.mulRight (1 : (CategoryAlgebra R C)) = (AddMonoidHom.id _)) := by
      apply CategoryAlgebra.addHom_ext
      rintro X₁ Y₁ f
      simp only [AddMonoidHom.mulRight, one_def, Finset.mul_sum, AddMonoidHom.coe_mk,
        ZeroHom.coe_mk, mul_of, AddMonoidHom.id_apply]
      rw [Finset.sum_eq_single_of_mem Y₁ (Finset.mem_univ _)]
      · simp [comp₀, compHom, Preadditive.leftComp]
      · intro b _ h
        simp [comp₀, h.symm]
    apply DFunLike.congr_fun (h₁ := H)

end Unital

















end CategoryAlgebra
end CategoryTheory.Linear
