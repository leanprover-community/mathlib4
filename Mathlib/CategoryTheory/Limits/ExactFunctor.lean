/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.Preserves.Finite

#align_import category_theory.limits.exact_functor from "leanprover-community/mathlib"@"9fc53308a90fac244ac715308e1f9c969e6843a4"

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
set_option linter.uppercaseLean3 false in
#align category_theory.LeftExactFunctor CategoryTheory.LeftExactFunctor

instance : Category (LeftExactFunctor C D) :=
  FullSubcategory.category _

/-- `C ⥤ₗ D` denotes left exact functors `C ⥤ D` -/
infixr:26 " ⥤ₗ " => LeftExactFunctor

/-- A left exact functor is in particular a functor. -/
def LeftExactFunctor.forget : (C ⥤ₗ D) ⥤ C ⥤ D :=
  fullSubcategoryInclusion _
set_option linter.uppercaseLean3 false in
#align category_theory.LeftExactFunctor.forget CategoryTheory.LeftExactFunctor.forget

instance : (LeftExactFunctor.forget C D).Full :=
  FullSubcategory.full _

instance : (LeftExactFunctor.forget C D).Faithful :=
  FullSubcategory.faithful _

-- porting note (#5171): removed @[nolint has_nonempty_instance]
/-- Bundled right-exact functors. -/
def RightExactFunctor :=
  FullSubcategory fun F : C ⥤ D => Nonempty (PreservesFiniteColimits F)
set_option linter.uppercaseLean3 false in
#align category_theory.RightExactFunctor CategoryTheory.RightExactFunctor

instance : Category (RightExactFunctor C D) :=
  FullSubcategory.category _

/-- `C ⥤ᵣ D` denotes right exact functors `C ⥤ D` -/
infixr:26 " ⥤ᵣ " => RightExactFunctor

/-- A right exact functor is in particular a functor. -/
def RightExactFunctor.forget : (C ⥤ᵣ D) ⥤ C ⥤ D :=
  fullSubcategoryInclusion _
set_option linter.uppercaseLean3 false in
#align category_theory.RightExactFunctor.forget CategoryTheory.RightExactFunctor.forget

instance : (RightExactFunctor.forget C D).Full :=
  FullSubcategory.full _

instance : (RightExactFunctor.forget C D).Faithful :=
  FullSubcategory.faithful _

-- porting note (#5171): removed @[nolint has_nonempty_instance]
/-- Bundled exact functors. -/
def ExactFunctor :=
  FullSubcategory fun F : C ⥤ D =>
    Nonempty (PreservesFiniteLimits F) ∧ Nonempty (PreservesFiniteColimits F)
set_option linter.uppercaseLean3 false in
#align category_theory.ExactFunctor CategoryTheory.ExactFunctor

instance : Category (ExactFunctor C D) :=
  FullSubcategory.category _

/-- `C ⥤ₑ D` denotes exact functors `C ⥤ D` -/
infixr:26 " ⥤ₑ " => ExactFunctor

/-- An exact functor is in particular a functor. -/
def ExactFunctor.forget : (C ⥤ₑ D) ⥤ C ⥤ D :=
  fullSubcategoryInclusion _
set_option linter.uppercaseLean3 false in
#align category_theory.ExactFunctor.forget CategoryTheory.ExactFunctor.forget

instance : (ExactFunctor.forget C D).Full :=
  FullSubcategory.full _

instance : (ExactFunctor.forget C D).Faithful :=
  FullSubcategory.faithful _

/-- Turn an exact functor into a left exact functor. -/
def LeftExactFunctor.ofExact : (C ⥤ₑ D) ⥤ C ⥤ₗ D :=
  FullSubcategory.map fun _ => And.left
set_option linter.uppercaseLean3 false in
#align category_theory.LeftExactFunctor.of_exact CategoryTheory.LeftExactFunctor.ofExact

instance : (LeftExactFunctor.ofExact C D).Full :=
  FullSubcategory.full_map _

instance : (LeftExactFunctor.ofExact C D).Faithful :=
  FullSubcategory.faithful_map _

/-- Turn an exact functor into a left exact functor. -/
def RightExactFunctor.ofExact : (C ⥤ₑ D) ⥤ C ⥤ᵣ D :=
  FullSubcategory.map fun _ => And.right
set_option linter.uppercaseLean3 false in
#align category_theory.RightExactFunctor.of_exact CategoryTheory.RightExactFunctor.ofExact

instance : (RightExactFunctor.ofExact C D).Full :=
  FullSubcategory.full_map _

instance : (RightExactFunctor.ofExact C D).Faithful :=
  FullSubcategory.faithful_map _

variable {C D}

@[simp]
theorem LeftExactFunctor.ofExact_obj (F : C ⥤ₑ D) :
    (LeftExactFunctor.ofExact C D).obj F = ⟨F.1, F.2.1⟩ :=
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.LeftExactFunctor.of_exact_obj CategoryTheory.LeftExactFunctor.ofExact_obj

@[simp]
theorem RightExactFunctor.ofExact_obj (F : C ⥤ₑ D) :
    (RightExactFunctor.ofExact C D).obj F = ⟨F.1, F.2.2⟩ :=
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.RightExactFunctor.of_exact_obj CategoryTheory.RightExactFunctor.ofExact_obj

@[simp]
theorem LeftExactFunctor.ofExact_map {F G : C ⥤ₑ D} (α : F ⟶ G) :
    (LeftExactFunctor.ofExact C D).map α = α :=
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.LeftExactFunctor.of_exact_map CategoryTheory.LeftExactFunctor.ofExact_map

@[simp]
theorem RightExactFunctor.ofExact_map {F G : C ⥤ₑ D} (α : F ⟶ G) :
    (RightExactFunctor.ofExact C D).map α = α :=
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.RightExactFunctor.of_exact_map CategoryTheory.RightExactFunctor.ofExact_map

@[simp]
theorem LeftExactFunctor.forget_obj (F : C ⥤ₗ D) : (LeftExactFunctor.forget C D).obj F = F.1 :=
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.LeftExactFunctor.forget_obj CategoryTheory.LeftExactFunctor.forget_obj

@[simp]
theorem RightExactFunctor.forget_obj (F : C ⥤ᵣ D) : (RightExactFunctor.forget C D).obj F = F.1 :=
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.RightExactFunctor.forget_obj CategoryTheory.RightExactFunctor.forget_obj

@[simp]
theorem ExactFunctor.forget_obj (F : C ⥤ₑ D) : (ExactFunctor.forget C D).obj F = F.1 :=
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.ExactFunctor.forget_obj CategoryTheory.ExactFunctor.forget_obj

@[simp]
theorem LeftExactFunctor.forget_map {F G : C ⥤ₗ D} (α : F ⟶ G) :
    (LeftExactFunctor.forget C D).map α = α :=
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.LeftExactFunctor.forget_map CategoryTheory.LeftExactFunctor.forget_map

@[simp]
theorem RightExactFunctor.forget_map {F G : C ⥤ᵣ D} (α : F ⟶ G) :
    (RightExactFunctor.forget C D).map α = α :=
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.RightExactFunctor.forget_map CategoryTheory.RightExactFunctor.forget_map

@[simp]
theorem ExactFunctor.forget_map {F G : C ⥤ₑ D} (α : F ⟶ G) : (ExactFunctor.forget C D).map α = α :=
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.ExactFunctor.forget_map CategoryTheory.ExactFunctor.forget_map

/-- Turn a left exact functor into an object of the category `LeftExactFunctor C D`. -/
def LeftExactFunctor.of (F : C ⥤ D) [PreservesFiniteLimits F] : C ⥤ₗ D :=
  ⟨F, ⟨inferInstance⟩⟩
set_option linter.uppercaseLean3 false in
#align category_theory.LeftExactFunctor.of CategoryTheory.LeftExactFunctor.of

/-- Turn a right exact functor into an object of the category `RightExactFunctor C D`. -/
def RightExactFunctor.of (F : C ⥤ D) [PreservesFiniteColimits F] : C ⥤ᵣ D :=
  ⟨F, ⟨inferInstance⟩⟩
set_option linter.uppercaseLean3 false in
#align category_theory.RightExactFunctor.of CategoryTheory.RightExactFunctor.of

/-- Turn an exact functor into an object of the category `ExactFunctor C D`. -/
def ExactFunctor.of (F : C ⥤ D) [PreservesFiniteLimits F] [PreservesFiniteColimits F] : C ⥤ₑ D :=
  ⟨F, ⟨⟨inferInstance⟩, ⟨inferInstance⟩⟩⟩
set_option linter.uppercaseLean3 false in
#align category_theory.ExactFunctor.of CategoryTheory.ExactFunctor.of

@[simp]
theorem LeftExactFunctor.of_fst (F : C ⥤ D) [PreservesFiniteLimits F] :
    (LeftExactFunctor.of F).obj = F :=
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.LeftExactFunctor.of_fst CategoryTheory.LeftExactFunctor.of_fst

@[simp]
theorem RightExactFunctor.of_fst (F : C ⥤ D) [PreservesFiniteColimits F] :
    (RightExactFunctor.of F).obj = F :=
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.RightExactFunctor.of_fst CategoryTheory.RightExactFunctor.of_fst

@[simp]
theorem ExactFunctor.of_fst (F : C ⥤ D) [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (ExactFunctor.of F).obj = F :=
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.ExactFunctor.of_fst CategoryTheory.ExactFunctor.of_fst

theorem LeftExactFunctor.forget_obj_of (F : C ⥤ D) [PreservesFiniteLimits F] :
    (LeftExactFunctor.forget C D).obj (LeftExactFunctor.of F) = F :=
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.LeftExactFunctor.forget_obj_of CategoryTheory.LeftExactFunctor.forget_obj_of

theorem RightExactFunctor.forget_obj_of (F : C ⥤ D) [PreservesFiniteColimits F] :
    (RightExactFunctor.forget C D).obj (RightExactFunctor.of F) = F :=
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.RightExactFunctor.forget_obj_of CategoryTheory.RightExactFunctor.forget_obj_of

theorem ExactFunctor.forget_obj_of (F : C ⥤ D) [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] : (ExactFunctor.forget C D).obj (ExactFunctor.of F) = F :=
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.ExactFunctor.forget_obj_of CategoryTheory.ExactFunctor.forget_obj_of

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
