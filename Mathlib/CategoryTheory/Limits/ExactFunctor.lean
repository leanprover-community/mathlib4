/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# Bundled exact functors

We say that a functor `F` is left exact if it preserves finite limits, it is right exact if it
preserves finite colimits, and it is exact if it is both left exact and right exact.

In this file, we define the categories of bundled left exact, right exact and exact functors.

-/


universe v₁ v₂ u₁ u₂

open CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

section

variable (C) (D)

-- porting note (#5171): removed @[nolint has_nonempty_instance]
/-- Bundled left-exact functors. -/
def LeftExactFunctor :=
  FullSubcategory fun F : C ⥤ D => Nonempty (PreservesFiniteLimits F)

instance : Category (LeftExactFunctor C D) :=
  FullSubcategory.category _

/-- `C ⥤ₗ D` denotes left exact functors `C ⥤ D` -/
infixr:26 " ⥤ₗ " => LeftExactFunctor

/-- A left exact functor is in particular a functor. -/
def LeftExactFunctor.forget : (C ⥤ₗ D) ⥤ C ⥤ D :=
  fullSubcategoryInclusion _

instance : (LeftExactFunctor.forget C D).Full :=
  FullSubcategory.full _

instance : (LeftExactFunctor.forget C D).Faithful :=
  FullSubcategory.faithful _

-- porting note (#5171): removed @[nolint has_nonempty_instance]
/-- Bundled right-exact functors. -/
def RightExactFunctor :=
  FullSubcategory fun F : C ⥤ D => Nonempty (PreservesFiniteColimits F)

instance : Category (RightExactFunctor C D) :=
  FullSubcategory.category _

/-- `C ⥤ᵣ D` denotes right exact functors `C ⥤ D` -/
infixr:26 " ⥤ᵣ " => RightExactFunctor

/-- A right exact functor is in particular a functor. -/
def RightExactFunctor.forget : (C ⥤ᵣ D) ⥤ C ⥤ D :=
  fullSubcategoryInclusion _

instance : (RightExactFunctor.forget C D).Full :=
  FullSubcategory.full _

instance : (RightExactFunctor.forget C D).Faithful :=
  FullSubcategory.faithful _

-- porting note (#5171): removed @[nolint has_nonempty_instance]
/-- Bundled exact functors. -/
def ExactFunctor :=
  FullSubcategory fun F : C ⥤ D =>
    Nonempty (PreservesFiniteLimits F) ∧ Nonempty (PreservesFiniteColimits F)

instance : Category (ExactFunctor C D) :=
  FullSubcategory.category _

/-- `C ⥤ₑ D` denotes exact functors `C ⥤ D` -/
infixr:26 " ⥤ₑ " => ExactFunctor

/-- An exact functor is in particular a functor. -/
def ExactFunctor.forget : (C ⥤ₑ D) ⥤ C ⥤ D :=
  fullSubcategoryInclusion _

instance : (ExactFunctor.forget C D).Full :=
  FullSubcategory.full _

instance : (ExactFunctor.forget C D).Faithful :=
  FullSubcategory.faithful _

/-- Turn an exact functor into a left exact functor. -/
def LeftExactFunctor.ofExact : (C ⥤ₑ D) ⥤ C ⥤ₗ D :=
  FullSubcategory.map fun _ => And.left

instance : (LeftExactFunctor.ofExact C D).Full :=
  FullSubcategory.full_map _

instance : (LeftExactFunctor.ofExact C D).Faithful :=
  FullSubcategory.faithful_map _

/-- Turn an exact functor into a left exact functor. -/
def RightExactFunctor.ofExact : (C ⥤ₑ D) ⥤ C ⥤ᵣ D :=
  FullSubcategory.map fun _ => And.right

instance : (RightExactFunctor.ofExact C D).Full :=
  FullSubcategory.full_map _

instance : (RightExactFunctor.ofExact C D).Faithful :=
  FullSubcategory.faithful_map _

variable {C D}

@[simp]
theorem LeftExactFunctor.ofExact_obj (F : C ⥤ₑ D) :
    (LeftExactFunctor.ofExact C D).obj F = ⟨F.1, F.2.1⟩ :=
  rfl

@[simp]
theorem RightExactFunctor.ofExact_obj (F : C ⥤ₑ D) :
    (RightExactFunctor.ofExact C D).obj F = ⟨F.1, F.2.2⟩ :=
  rfl

@[simp]
theorem LeftExactFunctor.ofExact_map {F G : C ⥤ₑ D} (α : F ⟶ G) :
    (LeftExactFunctor.ofExact C D).map α = α :=
  rfl

@[simp]
theorem RightExactFunctor.ofExact_map {F G : C ⥤ₑ D} (α : F ⟶ G) :
    (RightExactFunctor.ofExact C D).map α = α :=
  rfl

@[simp]
theorem LeftExactFunctor.forget_obj (F : C ⥤ₗ D) : (LeftExactFunctor.forget C D).obj F = F.1 :=
  rfl

@[simp]
theorem RightExactFunctor.forget_obj (F : C ⥤ᵣ D) : (RightExactFunctor.forget C D).obj F = F.1 :=
  rfl

@[simp]
theorem ExactFunctor.forget_obj (F : C ⥤ₑ D) : (ExactFunctor.forget C D).obj F = F.1 :=
  rfl

@[simp]
theorem LeftExactFunctor.forget_map {F G : C ⥤ₗ D} (α : F ⟶ G) :
    (LeftExactFunctor.forget C D).map α = α :=
  rfl

@[simp]
theorem RightExactFunctor.forget_map {F G : C ⥤ᵣ D} (α : F ⟶ G) :
    (RightExactFunctor.forget C D).map α = α :=
  rfl

@[simp]
theorem ExactFunctor.forget_map {F G : C ⥤ₑ D} (α : F ⟶ G) : (ExactFunctor.forget C D).map α = α :=
  rfl

/-- Turn a left exact functor into an object of the category `LeftExactFunctor C D`. -/
def LeftExactFunctor.of (F : C ⥤ D) [PreservesFiniteLimits F] : C ⥤ₗ D :=
  ⟨F, ⟨inferInstance⟩⟩

/-- Turn a right exact functor into an object of the category `RightExactFunctor C D`. -/
def RightExactFunctor.of (F : C ⥤ D) [PreservesFiniteColimits F] : C ⥤ᵣ D :=
  ⟨F, ⟨inferInstance⟩⟩

/-- Turn an exact functor into an object of the category `ExactFunctor C D`. -/
def ExactFunctor.of (F : C ⥤ D) [PreservesFiniteLimits F] [PreservesFiniteColimits F] : C ⥤ₑ D :=
  ⟨F, ⟨⟨inferInstance⟩, ⟨inferInstance⟩⟩⟩

@[simp]
theorem LeftExactFunctor.of_fst (F : C ⥤ D) [PreservesFiniteLimits F] :
    (LeftExactFunctor.of F).obj = F :=
  rfl

@[simp]
theorem RightExactFunctor.of_fst (F : C ⥤ D) [PreservesFiniteColimits F] :
    (RightExactFunctor.of F).obj = F :=
  rfl

@[simp]
theorem ExactFunctor.of_fst (F : C ⥤ D) [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (ExactFunctor.of F).obj = F :=
  rfl

theorem LeftExactFunctor.forget_obj_of (F : C ⥤ D) [PreservesFiniteLimits F] :
    (LeftExactFunctor.forget C D).obj (LeftExactFunctor.of F) = F :=
  rfl

theorem RightExactFunctor.forget_obj_of (F : C ⥤ D) [PreservesFiniteColimits F] :
    (RightExactFunctor.forget C D).obj (RightExactFunctor.of F) = F :=
  rfl

theorem ExactFunctor.forget_obj_of (F : C ⥤ D) [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] : (ExactFunctor.forget C D).obj (ExactFunctor.of F) = F :=
  rfl

noncomputable instance (F : C ⥤ₗ D) : PreservesFiniteLimits F.obj :=
  F.property.some

noncomputable instance (F : C ⥤ᵣ D) : PreservesFiniteColimits F.obj :=
  F.property.some

noncomputable instance (F : C ⥤ₑ D) : PreservesFiniteLimits F.obj :=
  F.property.1.some

noncomputable instance (F : C ⥤ₑ D) : PreservesFiniteColimits F.obj :=
  F.property.2.some

end

end CategoryTheory
