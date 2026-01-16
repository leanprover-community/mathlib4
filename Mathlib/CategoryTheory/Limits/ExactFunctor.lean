/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# Bundled exact functors

We say that a functor `F` is left exact if it preserves finite limits, it is right exact if it
preserves finite colimits, and it is exact if it is both left exact and right exact.

In this file, we define the categories of bundled left exact, right exact and exact functors.

-/

@[expose] public section


universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

section

variable (C) (D)

/-- Left-exactness, as a property of objects in `C ⥤ D`. -/
def leftExactFunctor : ObjectProperty (C ⥤ D) :=
  fun F ↦ PreservesFiniteLimits F

variable {C D} in
@[simp]
lemma leftExactFunctor_iff (F : C ⥤ D) :
    leftExactFunctor C D F ↔ PreservesFiniteLimits F := Iff.rfl

/-- Bundled left-exact functors. -/
abbrev LeftExactFunctor := (leftExactFunctor C D).FullSubcategory

/-- `C ⥤ₗ D` denotes left exact functors `C ⥤ D` -/
infixr:26 " ⥤ₗ " => LeftExactFunctor

/-- A left exact functor is in particular a functor. -/
abbrev LeftExactFunctor.forget : (C ⥤ₗ D) ⥤ C ⥤ D :=
  ObjectProperty.ι _

/-- The inclusion of left exact functors into functors is fully faithful. -/
abbrev LeftExactFunctor.fullyFaithful : (LeftExactFunctor.forget C D).FullyFaithful :=
  ObjectProperty.fullyFaithfulι _

/-- Right-exactness, as a property of objects in `C ⥤ D`. -/
def rightExactFunctor : ObjectProperty (C ⥤ D) :=
  fun F ↦ PreservesFiniteColimits F

variable {C D} in
@[simp]
lemma rightExactFunctor_iff (F : C ⥤ D) :
    rightExactFunctor C D F ↔ PreservesFiniteColimits F := Iff.rfl

/-- Bundled right-exact functors. -/
abbrev RightExactFunctor := (rightExactFunctor C D).FullSubcategory

/-- `C ⥤ᵣ D` denotes right exact functors `C ⥤ D` -/
infixr:26 " ⥤ᵣ " => RightExactFunctor

/-- A right exact functor is in particular a functor. -/
abbrev RightExactFunctor.forget : (C ⥤ᵣ D) ⥤ C ⥤ D :=
  ObjectProperty.ι _

/-- The inclusion of right exact functors into functors is fully faithful. -/
abbrev RightExactFunctor.fullyFaithful : (RightExactFunctor.forget C D).FullyFaithful :=
  ObjectProperty.fullyFaithfulι _

/-- Exactness, as a property of objects in `C ⥤ D`. -/
def exactFunctor : ObjectProperty (C ⥤ D) :=
  leftExactFunctor C D ⊓ rightExactFunctor C D

variable {C D} in
@[simp]
lemma exactFunctor_iff (F : C ⥤ D) :
    exactFunctor C D F ↔ PreservesFiniteLimits F ∧ PreservesFiniteColimits F := Iff.rfl

/-- Bundled exact functors. -/
abbrev ExactFunctor := (exactFunctor C D).FullSubcategory

/-- `C ⥤ₑ D` denotes exact functors `C ⥤ D` -/
infixr:26 " ⥤ₑ " => ExactFunctor

/-- An exact functor is in particular a functor. -/
abbrev ExactFunctor.forget : (C ⥤ₑ D) ⥤ C ⥤ D :=
  ObjectProperty.ι _

lemma exactFunctor_le_leftExactFunctor :
    exactFunctor C D ≤ leftExactFunctor C D :=
  fun _ h ↦ h.1

lemma exactFunctor_le_rightExactFunctor :
    exactFunctor C D ≤ rightExactFunctor C D :=
  fun _ h ↦ h.2

/-- Turn an exact functor into a left exact functor. -/
abbrev LeftExactFunctor.ofExact : (C ⥤ₑ D) ⥤ C ⥤ₗ D :=
  ObjectProperty.ιOfLE (exactFunctor_le_leftExactFunctor C D)

/-- Turn an exact functor into a left exact functor. -/
abbrev RightExactFunctor.ofExact : (C ⥤ₑ D) ⥤ C ⥤ᵣ D :=
  ObjectProperty.ιOfLE (exactFunctor_le_rightExactFunctor C D)

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
theorem LeftExactFunctor.ofExact_map_hom {F G : C ⥤ₑ D} (α : F ⟶ G) :
    ((LeftExactFunctor.ofExact C D).map α).hom = α.hom :=
  rfl

@[simp]
theorem RightExactFunctor.ofExact_map_hom {F G : C ⥤ₑ D} (α : F ⟶ G) :
    ((RightExactFunctor.ofExact C D).map α).hom = α.hom :=
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
    (LeftExactFunctor.forget C D).map α = α.hom :=
  rfl

@[simp]
theorem RightExactFunctor.forget_map {F G : C ⥤ᵣ D} (α : F ⟶ G) :
    (RightExactFunctor.forget C D).map α = α.hom :=
  rfl

@[simp]
theorem ExactFunctor.forget_map {F G : C ⥤ₑ D} (α : F ⟶ G) :
    (ExactFunctor.forget C D).map α = α.hom :=
  rfl

/-- Turn a left exact functor into an object of the category `LeftExactFunctor C D`. -/
def LeftExactFunctor.of (F : C ⥤ D) [PreservesFiniteLimits F] : C ⥤ₗ D :=
  ⟨F, by simpa⟩

/-- Turn a right exact functor into an object of the category `RightExactFunctor C D`. -/
def RightExactFunctor.of (F : C ⥤ D) [PreservesFiniteColimits F] : C ⥤ᵣ D :=
  ⟨F, by simpa⟩

/-- Turn an exact functor into an object of the category `ExactFunctor C D`. -/
def ExactFunctor.of (F : C ⥤ D) [PreservesFiniteLimits F] [PreservesFiniteColimits F] : C ⥤ₑ D :=
  ⟨F, by simp only [exactFunctor_iff]; constructor <;> assumption⟩

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
  F.property

noncomputable instance (F : C ⥤ᵣ D) : PreservesFiniteColimits F.obj :=
  F.property

noncomputable instance (F : C ⥤ₑ D) : PreservesFiniteLimits F.obj :=
  F.property.1

noncomputable instance (F : C ⥤ₑ D) : PreservesFiniteColimits F.obj :=
  F.property.2

variable {E : Type u₃} [Category.{v₃} E]

section

variable (C D E)

/-- Whiskering a left exact functor by a left exact functor yields a left exact functor. -/
@[simps! obj_obj_obj obj_map map_app]
def LeftExactFunctor.whiskeringLeft : (C ⥤ₗ D) ⥤ (D ⥤ₗ E) ⥤ (C ⥤ₗ E) where
  obj F := ObjectProperty.lift _ (forget _ _ ⋙ (Functor.whiskeringLeft C D E).obj F.obj)
    (fun G => by dsimp; exact comp_preservesFiniteLimits _ _)
  map {F G} η :=
    { app H := ObjectProperty.homMk (((Functor.whiskeringLeft C D E).map η.hom).app H.obj) }

/-- Whiskering a left exact functor by a left exact functor yields a left exact functor. -/
@[simps! obj_obj_obj obj_map map_app]
def LeftExactFunctor.whiskeringRight : (D ⥤ₗ E) ⥤ (C ⥤ₗ D) ⥤ (C ⥤ₗ E) where
  obj F := ObjectProperty.lift _ (forget _ _ ⋙ (Functor.whiskeringRight C D E).obj F.obj)
    (fun G => by dsimp; exact comp_preservesFiniteLimits _ _)
  map {F G} η :=
    { app H := ObjectProperty.homMk (((Functor.whiskeringRight C D E).map η.hom).app H.obj) }

/-- Whiskering a right exact functor by a right exact functor yields a right exact functor. -/
@[simps! obj_obj_obj obj_map map_app]
def RightExactFunctor.whiskeringLeft : (C ⥤ᵣ D) ⥤ (D ⥤ᵣ E) ⥤ (C ⥤ᵣ E) where
  obj F := ObjectProperty.lift _ (forget _ _ ⋙ (Functor.whiskeringLeft C D E).obj F.obj)
    (fun G => by dsimp; exact comp_preservesFiniteColimits _ _)
  map {F G} η :=
    { app H := ObjectProperty.homMk (((Functor.whiskeringLeft C D E).map η.hom).app H.obj) }

/-- Whiskering a right exact functor by a right exact functor yields a right exact functor. -/
@[simps! obj_obj_obj obj_map map_app]
def RightExactFunctor.whiskeringRight : (D ⥤ᵣ E) ⥤ (C ⥤ᵣ D) ⥤ (C ⥤ᵣ E) where
  obj F := ObjectProperty.lift _ (forget _ _ ⋙ (Functor.whiskeringRight C D E).obj F.obj)
    (fun G => by dsimp; exact comp_preservesFiniteColimits _ _)
  map {F G} η :=
    { app H := ObjectProperty.homMk (((Functor.whiskeringRight C D E).map η.hom).app H.obj) }

/-- Whiskering an exact functor by an exact functor yields an exact functor. -/
@[simps! obj_obj_obj obj_map map_app]
def ExactFunctor.whiskeringLeft : (C ⥤ₑ D) ⥤ (D ⥤ₑ E) ⥤ (C ⥤ₑ E) where
  obj F := ObjectProperty.lift _ (forget _ _ ⋙ (Functor.whiskeringLeft C D E).obj F.obj)
    (fun G => ⟨by dsimp; exact comp_preservesFiniteLimits _ _,
      by dsimp; exact comp_preservesFiniteColimits _ _⟩)
  map {F G} η :=
    { app H := ObjectProperty.homMk (((Functor.whiskeringLeft C D E).map η.hom).app H.obj) }

/-- Whiskering an exact functor by an exact functor yields an exact functor. -/
@[simps! obj_obj_obj obj_map map_app]
def ExactFunctor.whiskeringRight : (D ⥤ₑ E) ⥤ (C ⥤ₑ D) ⥤ (C ⥤ₑ E) where
  obj F := ObjectProperty.lift _ (forget _ _ ⋙ (Functor.whiskeringRight C D E).obj F.obj)
    (fun G => ⟨by dsimp; exact comp_preservesFiniteLimits _ _,
      by dsimp; exact comp_preservesFiniteColimits _ _⟩)
  map {F G} η :=
    { app H := ObjectProperty.homMk (((Functor.whiskeringRight C D E).map η.hom).app H.obj) }

end

end

@[deprecated (since := "2025-12-18")] alias LeftExactFunctor.ofExact_map :=
  LeftExactFunctor.ofExact_map_hom

@[deprecated (since := "2025-12-18")] alias RightExactFunctor.ofExact_map :=
  RightExactFunctor.ofExact_map_hom

end CategoryTheory
