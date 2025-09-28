/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.CategoryTheory.Sites.Canonical
import Mathlib.CategoryTheory.Sites.Whiskering
/-!

# Subcanonical Grothendieck topologies

This file provides some API for the Yoneda embedding into the category of sheaves for a
subcanonical Grothendieck topology.
-/

universe v' v u

namespace CategoryTheory.GrothendieckTopology

open Opposite

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) [Subcanonical J]

/--
The equivalence between natural transformations from the yoneda embedding (to the sheaf category)
and elements of `F.val.obj X`.
-/
def yonedaEquiv {X : C} {F : Sheaf J (Type v)} : (J.yoneda.obj X ⟶ F) ≃ F.val.obj (op X) :=
  (fullyFaithfulSheafToPresheaf _ _).homEquiv.trans CategoryTheory.yonedaEquiv

theorem yonedaEquiv_apply {X : C} {F : Sheaf J (Type v)} (f : J.yoneda.obj X ⟶ F) :
    yonedaEquiv J f = f.val.app (op X) (𝟙 X) :=
  rfl

@[simp]
theorem yonedaEquiv_symm_app_apply {X : C} {F : Sheaf J (Type v)} (x : F.val.obj (op X)) (Y : Cᵒᵖ)
    (f : Y.unop ⟶ X) : (J.yonedaEquiv.symm x).val.app Y f = F.val.map f.op x :=
  rfl

/-- See also `yonedaEquiv_naturality'` for a more general version. -/
lemma yonedaEquiv_naturality {X Y : C} {F : Sheaf J (Type v)} (f : J.yoneda.obj X ⟶ F)
    (g : Y ⟶ X) : F.val.map g.op (J.yonedaEquiv f) = J.yonedaEquiv (J.yoneda.map g ≫ f) := by
  simp [yonedaEquiv, CategoryTheory.yonedaEquiv_naturality]
  rfl

/--
Variant of `yonedaEquiv_naturality` with general `g`. This is technically strictly more general
than `yonedaEquiv_naturality`, but `yonedaEquiv_naturality` is sometimes preferable because it
can avoid the "motive is not type correct" error.
-/
lemma yonedaEquiv_naturality' {X Y : Cᵒᵖ} {F : Sheaf J (Type v)} (f : J.yoneda.obj (unop X) ⟶ F)
    (g : X ⟶ Y) : F.val.map g (J.yonedaEquiv f) = J.yonedaEquiv (J.yoneda.map g.unop ≫ f) :=
  J.yonedaEquiv_naturality _ _

lemma yonedaEquiv_comp {X : C} {F G : Sheaf J (Type v)} (α : J.yoneda.obj X ⟶ F) (β : F ⟶ G) :
    J.yonedaEquiv (α ≫ β) = β.val.app _ (J.yonedaEquiv α) :=
  rfl

lemma yonedaEquiv_yoneda_map {X Y : C} (f : X ⟶ Y) : J.yonedaEquiv (J.yoneda.map f) = f := by
  rw [yonedaEquiv_apply]
  simp

lemma yonedaEquiv_symm_naturality_left {X X' : C} (f : X' ⟶ X) (F : Sheaf J (Type v))
    (x : F.val.obj ⟨X⟩) : J.yoneda.map f ≫ J.yonedaEquiv.symm x = J.yonedaEquiv.symm
      ((F.val.map f.op) x) := by
  apply J.yonedaEquiv.injective
  simp only [yonedaEquiv_comp, yonedaEquiv_symm_app_apply, Equiv.apply_symm_apply]
  rw [yonedaEquiv_yoneda_map]

lemma yonedaEquiv_symm_naturality_right (X : C) {F F' : Sheaf J (Type v)} (f : F ⟶ F')
    (x : F.val.obj ⟨X⟩) : J.yonedaEquiv.symm x ≫ f = J.yonedaEquiv.symm (f.val.app ⟨X⟩ x) := by
  apply J.yonedaEquiv.injective
  simp [yonedaEquiv_comp]

/-- See also `map_yonedaEquiv'` for a more general version. -/
lemma map_yonedaEquiv {X Y : C} {F : Sheaf J (Type v)} (f : J.yoneda.obj X ⟶ F)
    (g : Y ⟶ X) : F.val.map g.op (J.yonedaEquiv f) = f.val.app (op Y) g := by
  rw [yonedaEquiv_naturality, yonedaEquiv_comp, yonedaEquiv_yoneda_map]

/--
Variant of `map_yonedaEquiv` with general `g`. This is technically strictly more general
than `map_yonedaEquiv`, but `map_yonedaEquiv` is sometimes preferable because it
can avoid the "motive is not type correct" error.
-/
lemma map_yonedaEquiv' {X Y : Cᵒᵖ} {F : Sheaf J (Type v)} (f : J.yoneda.obj (unop X) ⟶ F)
    (g : X ⟶ Y) : F.val.map g (J.yonedaEquiv f) = f.val.app Y g.unop := by
  rw [yonedaEquiv_naturality', yonedaEquiv_comp, yonedaEquiv_yoneda_map]

lemma yonedaEquiv_symm_map {X Y : Cᵒᵖ} (f : X ⟶ Y) {F : Sheaf J (Type v)} (t : F.val.obj X) :
    J.yonedaEquiv.symm (F.val.map f t) = J.yoneda.map f.unop ≫ J.yonedaEquiv.symm t := by
  obtain ⟨u, rfl⟩ := J.yonedaEquiv.surjective t
  rw [yonedaEquiv_naturality', Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/--
Two morphisms of sheaves of types `P ⟶ Q` coincide if the precompositions with morphisms
`yoneda.obj X ⟶ P` agree.
-/
lemma hom_ext_yoneda {P Q : Sheaf J (Type v)} {f g : P ⟶ Q}
    (h : ∀ (X : C) (p : J.yoneda.obj X ⟶ P), p ≫ f = p ≫ g) :
    f = g := by
  ext X x
  simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply]
    using congr_arg (J.yonedaEquiv) (h _ (J.yonedaEquiv.symm x))

/--
The Yoneda embedding into a category of sheaves taking values in sets possibly larger than the
morphisms in the defining site.
-/
@[pp_with_univ]
def yonedaULift : C ⥤ Sheaf J (Type (max v v')) := J.yoneda ⋙ sheafCompose J uliftFunctor.{v'}

/-- A version of `yonedaEquiv` for `yonedaULift`. -/
def yonedaULiftEquiv {X : C} {F : Sheaf J (Type (max v v'))} :
    ((yonedaULift.{v'} J).obj X ⟶ F) ≃ F.val.obj (op X) :=
  (fullyFaithfulSheafToPresheaf _ _).homEquiv.trans uliftYonedaEquiv

theorem yonedaULiftEquiv_apply {X : C} {F : Sheaf J (Type (max v v'))}
    (f : J.yonedaULift.obj X ⟶ F) : yonedaULiftEquiv.{v'} J f = f.val.app (op X) ⟨𝟙 X⟩ :=
  rfl

@[simp]
theorem yonedaULiftEquiv_symm_app_apply {X : C} {F : Sheaf J (Type (max v v'))}
    (x : F.val.obj (op X)) (Y : Cᵒᵖ) (f : Y.unop ⟶ X) :
      (J.yonedaULiftEquiv.symm x).val.app Y ⟨f⟩ = F.val.map f.op x :=
  rfl

/-- See also `yonedaEquiv_naturality'` for a more general version. -/
lemma yonedaULiftEquiv_naturality {X Y : C} {F : Sheaf J (Type (max v v'))}
    (f : J.yonedaULift.obj X ⟶ F) (g : Y ⟶ X) :
      F.val.map g.op (J.yonedaULiftEquiv f) = J.yonedaULiftEquiv (J.yonedaULift.map g ≫ f) := by
  change (f.val.app (op X) ≫ F.val.map g.op) ⟨𝟙 X⟩ = f.val.app (op Y) ⟨𝟙 Y ≫ g⟩
  rw [← f.val.naturality]
  simp [yonedaULift]

/-- Variant of `yonedaEquiv_naturality` with general `g`. This is technically strictly more general
than `yonedaEquiv_naturality`, but `yonedaEquiv_naturality` is sometimes preferable because it
can avoid the "motive is not type correct" error. -/
lemma yonedaULiftEquiv_naturality' {X Y : Cᵒᵖ} {F : Sheaf J (Type (max v v'))}
    (f : J.yonedaULift.obj (unop X) ⟶ F) (g : X ⟶ Y) :
      F.val.map g (J.yonedaULiftEquiv f) = J.yonedaULiftEquiv (J.yonedaULift.map g.unop ≫ f) :=
  J.yonedaULiftEquiv_naturality _ _

lemma yonedaULiftEquiv_comp {X : C} {F G : Sheaf J (Type (max v v'))} (α : J.yonedaULift.obj X ⟶ F)
    (β : F ⟶ G) : J.yonedaULiftEquiv (α ≫ β) = β.val.app _ (J.yonedaULiftEquiv α) :=
  rfl

lemma yonedaULiftEquiv_yonedaULift_map {X Y : C} (f : X ⟶ Y) :
    (yonedaULiftEquiv.{v'} J) (J.yonedaULift.map f) = ⟨f⟩ := by
  rw [yonedaULiftEquiv_apply]
  simp [yonedaULift]

lemma yonedaULiftEquiv_symm_naturality_left {X X' : C} (f : X' ⟶ X) (F : Sheaf J (Type (max v v')))
    (x : F.val.obj ⟨X⟩) : J.yonedaULift.map f ≫ J.yonedaULiftEquiv.symm x = J.yonedaULiftEquiv.symm
      ((F.val.map f.op) x) := by
  apply J.yonedaULiftEquiv.injective
  simp only [yonedaULiftEquiv_comp, Equiv.apply_symm_apply]
  rw [yonedaULiftEquiv_yonedaULift_map]
  rfl

lemma yonedaULiftEquiv_symm_naturality_right (X : C) {F F' : Sheaf J (Type (max v v'))}
    (f : F ⟶ F') (x : F.val.obj ⟨X⟩) :
      J.yonedaULiftEquiv.symm x ≫ f = J.yonedaULiftEquiv.symm (f.val.app ⟨X⟩ x) := by
  apply J.yonedaULiftEquiv.injective
  simp [yonedaULiftEquiv_comp]

/-- See also `map_yonedaEquiv'` for a more general version. -/
lemma map_yonedaULiftEquiv {X Y : C} {F : Sheaf J (Type (max v v'))}
    (f : J.yonedaULift.obj X ⟶ F) (g : Y ⟶ X) :
      F.val.map g.op (J.yonedaULiftEquiv f) = f.val.app (op Y) ⟨g⟩ := by
  rw [yonedaULiftEquiv_naturality, yonedaULiftEquiv_comp, yonedaULiftEquiv_yonedaULift_map]

/-- Variant of `map_yonedaEquiv` with general `g`. This is technically strictly more general
than `map_yonedaEquiv`, but `map_yonedaEquiv` is sometimes preferable because it
can avoid the "motive is not type correct" error. -/
lemma map_yonedaULiftEquiv' {X Y : Cᵒᵖ} {F : Sheaf J (Type (max v v'))}
    (f : J.yonedaULift.obj (unop X) ⟶ F)
    (g : X ⟶ Y) : F.val.map g (J.yonedaULiftEquiv f) = f.val.app Y ⟨g.unop⟩ := by
  rw [yonedaULiftEquiv_naturality', yonedaULiftEquiv_comp, yonedaULiftEquiv_yonedaULift_map]

lemma yonedaULeftEquiv_symm_map {X Y : Cᵒᵖ} (f : X ⟶ Y) {F : Sheaf J (Type (max v v'))}
    (t : F.val.obj X) : J.yonedaULiftEquiv.symm (F.val.map f t) =
      J.yonedaULift.map f.unop ≫ J.yonedaULiftEquiv.symm t := by
  obtain ⟨u, rfl⟩ := J.yonedaULiftEquiv.surjective t
  rw [yonedaULiftEquiv_naturality', Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- Two morphisms of sheaves of types `P ⟶ Q` coincide if the precompositions
with morphisms `yoneda.obj X ⟶ P` agree. -/
lemma hom_ext_yonedaULift {P Q : Sheaf J (Type (max v v'))} {f g : P ⟶ Q}
    (h : ∀ (X : C) (p : J.yonedaULift.obj X ⟶ P), p ≫ f = p ≫ g) :
    f = g := by
  ext X x
  simpa only [yonedaULiftEquiv_comp, Equiv.apply_symm_apply]
    using congr_arg (J.yonedaULiftEquiv) (h _ (J.yonedaULiftEquiv.symm x))

end CategoryTheory.GrothendieckTopology
