/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.Data.Fintype.EquivFin
/-!

# Functors preserving effective epimorphisms

This file concerns functors which preserve and/or reflect effective epimorphisms and effective
epimorphic families.

## TODO
- Find nice sufficient conditions in terms of preserving/reflecting (co)limits, to preserve/reflect
  effective epis, similar to `CategoryTheory.preserves_epi_of_preservesColimit`.
-/

universe u

namespace CategoryTheory

open Limits

variable {C : Type*} [Category C]

noncomputable section Equivalence

variable {D : Type*} [Category D] (e : C ≌ D) {B : C}

variable {α : Type*} (X : α → C) (π : (a : α) → (X a ⟶ B))

theorem effectiveEpiFamilyStructOfEquivalence_aux {W : D} (ε : (a : α) → e.functor.obj (X a) ⟶ W)
    (h : ∀ {Z : D} (a₁ a₂ : α) (g₁ : Z ⟶ e.functor.obj (X a₁)) (g₂ : Z ⟶ e.functor.obj (X a₂)),
      g₁ ≫ e.functor.map (π a₁) = g₂ ≫ e.functor.map (π a₂) → g₁ ≫ ε a₁ = g₂ ≫ ε a₂)
    {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂) (hg : g₁ ≫ π a₁ = g₂ ≫ π a₂) :
    g₁ ≫ (fun a ↦ e.unit.app (X a) ≫ e.inverse.map (ε a)) a₁ =
    g₂ ≫ (fun a ↦ e.unit.app (X a) ≫ e.inverse.map (ε a)) a₂ := by
  have := h a₁ a₂ (e.functor.map g₁) (e.functor.map g₂)
  simp only [← Functor.map_comp, hg] at this
  simpa using congrArg e.inverse.map (this (by trivial))

variable [EffectiveEpiFamily X π]

/-- Equivalences preserve effective epimorphic families -/
def effectiveEpiFamilyStructOfEquivalence : EffectiveEpiFamilyStruct (fun a ↦ e.functor.obj (X a))
    (fun a ↦ e.functor.map (π a)) where
  desc ε h := (e.toAdjunction.homEquiv _ _).symm
      (EffectiveEpiFamily.desc X π (fun a ↦ e.unit.app _ ≫ e.inverse.map (ε a))
      (effectiveEpiFamilyStructOfEquivalence_aux e X π ε h))
  fac ε h a := by
    simp only [Functor.comp_obj, Adjunction.homEquiv_counit, Functor.id_obj,
      Equivalence.toAdjunction_counit]
    have := congrArg ((fun f ↦ f ≫ e.counit.app _) ∘ e.functor.map)
      (EffectiveEpiFamily.fac X π (fun a ↦ e.unit.app _ ≫ e.inverse.map (ε a))
      (effectiveEpiFamilyStructOfEquivalence_aux e X π ε h) a)
    simp only [Functor.id_obj, Functor.comp_obj, Function.comp_apply, Functor.map_comp,
        Category.assoc, Equivalence.fun_inv_map, Iso.inv_hom_id_app, Category.comp_id] at this
    simp [this]
  uniq ε h m hm := by
    simp only [Functor.comp_obj, Adjunction.homEquiv_counit, Functor.id_obj,
      Equivalence.toAdjunction_counit]
    have := EffectiveEpiFamily.uniq X π (fun a ↦ e.unit.app _ ≫ e.inverse.map (ε a))
      (effectiveEpiFamilyStructOfEquivalence_aux e X π ε h)
    specialize this (e.unit.app _ ≫ e.inverse.map m) fun a ↦ ?_
    · rw [← congrArg e.inverse.map (hm a)]
      simp
    · simp [← this]

instance (F : C ⥤ D) [F.IsEquivalence] :
    EffectiveEpiFamily (fun a ↦ F.obj (X a)) (fun a ↦ F.map (π a)) :=
  ⟨⟨effectiveEpiFamilyStructOfEquivalence F.asEquivalence _ _⟩⟩

example {X B : C} (π : X ⟶ B) (F : C ⥤ D) [F.IsEquivalence] [EffectiveEpi π] :
    EffectiveEpi <| F.map π := inferInstance

end Equivalence

namespace Functor

variable {D : Type*} [Category D]

section Preserves

/--
A class describing the property of preserving effective epimorphisms.
-/
class PreservesEffectiveEpis (F : C ⥤ D) : Prop where
  /--
  A functor preserves effective epimorphisms if it maps effective
  epimorphisms to effective epimorphisms.
  -/
  preserves : ∀ {X Y : C} (f : X ⟶ Y) [EffectiveEpi f], EffectiveEpi (F.map f)

instance map_effectiveEpi (F : C ⥤ D) [F.PreservesEffectiveEpis] {X Y : C} (f : X ⟶ Y)
    [EffectiveEpi f] : EffectiveEpi (F.map f) :=
  PreservesEffectiveEpis.preserves f

/--
A class describing the property of preserving effective epimorphic families.
-/
class PreservesEffectiveEpiFamilies (F : C ⥤ D) : Prop where
  /--
  A functor preserves effective epimorphic families if it maps effective epimorphic families to
  effective epimorphic families.
  -/
  preserves : ∀ {α : Type u} {B : C} (X : α → C) (π : (a : α) → (X a ⟶ B)) [EffectiveEpiFamily X π],
    EffectiveEpiFamily (fun a ↦ F.obj (X a)) (fun a  ↦ F.map (π a))

instance map_effectiveEpiFamily (F : C ⥤ D) [PreservesEffectiveEpiFamilies.{u} F]
    {α : Type u} {B : C} (X : α → C) (π : (a : α) → (X a ⟶ B)) [EffectiveEpiFamily X π] :
    EffectiveEpiFamily (fun a ↦ F.obj (X a)) (fun a  ↦ F.map (π a)) :=
  PreservesEffectiveEpiFamilies.preserves X π

/--
A class describing the property of preserving finite effective epimorphic families.
-/
class PreservesFiniteEffectiveEpiFamilies (F : C ⥤ D) : Prop where
  /--
  A functor preserves finite effective epimorphic families if it maps finite effective epimorphic
  families to effective epimorphic families.
  -/
  preserves : ∀ {α : Type} [Finite α] {B : C} (X : α → C) (π : (a : α) → (X a ⟶ B))
    [EffectiveEpiFamily X π],
    EffectiveEpiFamily (fun a ↦ F.obj (X a)) (fun a  ↦ F.map (π a))

instance map_finite_effectiveEpiFamily (F : C ⥤ D) [F.PreservesFiniteEffectiveEpiFamilies]
    {α : Type} [Finite α] {B : C} (X : α → C) (π : (a : α) → (X a ⟶ B)) [EffectiveEpiFamily X π] :
    EffectiveEpiFamily (fun a ↦ F.obj (X a)) (fun a  ↦ F.map (π a)) :=
  PreservesFiniteEffectiveEpiFamilies.preserves X π

instance (F : C ⥤ D) [PreservesEffectiveEpiFamilies.{0} F] :
    PreservesFiniteEffectiveEpiFamilies F where
  preserves _ _ := inferInstance

instance (F : C ⥤ D) [PreservesFiniteEffectiveEpiFamilies F] : PreservesEffectiveEpis F where
  preserves _ := inferInstance

instance (F : C ⥤ D) [IsEquivalence F] : F.PreservesEffectiveEpiFamilies where
  preserves _ _ := inferInstance

end Preserves

section Reflects

/--
A class describing the property of reflecting effective epimorphisms.
-/
class ReflectsEffectiveEpis (F : C ⥤ D) : Prop where
  /--
  A functor reflects effective epimorphisms if morphisms that are mapped to epimorphisms are
  themselves effective epimorphisms.
  -/
  reflects : ∀ {X Y : C} (f : X ⟶ Y), EffectiveEpi (F.map f) → EffectiveEpi f

lemma effectiveEpi_of_map (F : C ⥤ D) [F.ReflectsEffectiveEpis] {X Y : C} (f : X ⟶ Y)
    (h : EffectiveEpi (F.map f)) : EffectiveEpi f :=
  ReflectsEffectiveEpis.reflects f h

/--
A class describing the property of reflecting effective epimorphic families.
-/
class ReflectsEffectiveEpiFamilies (F : C ⥤ D) : Prop where
  /--
  A functor reflects effective epimorphic families if families that are mapped to effective
  epimorphic families are themselves effective epimorphic families.
  -/
  reflects : ∀ {α : Type u} {B : C} (X : α → C) (π : (a : α) → (X a ⟶ B)),
    EffectiveEpiFamily (fun a ↦ F.obj (X a)) (fun a  ↦ F.map (π a)) →
    EffectiveEpiFamily X π

lemma effectiveEpiFamily_of_map (F : C ⥤ D) [ReflectsEffectiveEpiFamilies.{u} F]
    {α : Type u} {B : C} (X : α → C) (π : (a : α) → (X a ⟶ B))
    (h : EffectiveEpiFamily (fun a ↦ F.obj (X a)) (fun a  ↦ F.map (π a))) :
    EffectiveEpiFamily X π :=
  ReflectsEffectiveEpiFamilies.reflects X π h

/--
A class describing the property of reflecting finite effective epimorphic families.
-/
class ReflectsFiniteEffectiveEpiFamilies (F : C ⥤ D) : Prop where
  /--
  A functor reflects finite effective epimorphic families if finite families that are
  mapped to effective epimorphic families are themselves effective epimorphic families.
  -/
  reflects : ∀ {α : Type} [Finite α] {B : C} (X : α → C) (π : (a : α) → (X a ⟶ B)),
    EffectiveEpiFamily (fun a ↦ F.obj (X a)) (fun a  ↦ F.map (π a)) →
    EffectiveEpiFamily X π

lemma finite_effectiveEpiFamily_of_map (F : C ⥤ D) [ReflectsFiniteEffectiveEpiFamilies F]
    {α : Type} [Finite α] {B : C} (X : α → C) (π : (a : α) → (X a ⟶ B))
    (h : EffectiveEpiFamily (fun a ↦ F.obj (X a)) (fun a  ↦ F.map (π a))) :
    EffectiveEpiFamily X π :=
  ReflectsFiniteEffectiveEpiFamilies.reflects X π h

instance (F : C ⥤ D) [ReflectsEffectiveEpiFamilies.{0} F] :
    ReflectsFiniteEffectiveEpiFamilies F where
  reflects _ _ h := by
    have := F.effectiveEpiFamily_of_map _ _ h
    infer_instance

instance (F : C ⥤ D) [ReflectsFiniteEffectiveEpiFamilies F] : ReflectsEffectiveEpis F where
  reflects _ h := by
    rw [effectiveEpi_iff_effectiveEpiFamily] at h
    have := F.finite_effectiveEpiFamily_of_map _ _ h
    infer_instance

instance (F : C ⥤ D) [IsEquivalence F] : F.PreservesEffectiveEpiFamilies where
  preserves _ _ := inferInstance

instance (F : C ⥤ D) [IsEquivalence F] : F.ReflectsEffectiveEpiFamilies where
  reflects {α B} X π _ := by
    let i : (a : α) → X a ⟶ (inv F).obj (F.obj (X a)) := fun a ↦ (asEquivalence F).unit.app _
    have : EffectiveEpiFamily X (fun a ↦ (i a) ≫ (inv F).map (F.map (π a))) := inferInstance
    simp only [inv_fun_map, Iso.hom_inv_id_app_assoc, i] at this
    have : EffectiveEpiFamily X (fun a ↦ (π a ≫ (asEquivalence F).unit.app B) ≫
        (asEquivalence F).unitInv.app _) := inferInstance
    simpa

end Reflects

end Functor

end CategoryTheory
