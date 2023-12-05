/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Limits.Creates
import Mathlib.CategoryTheory.Limits.Types

/-!
# `ULift` creates small (co)limits

This file shows that `uliftFunctor.{v, u}` creates (and hence preserves) limits and colimits indexed
by `J` with `[Category.{u, u} J]`.

It also shows that `uliftFunctor.{v, u}` *preserves* "all" limits (i.e. of size `max u v`,
potentially too big to exist in `Type u`).

-/

universe v u

namespace CategoryTheory.Limits.Types

/--
The equivalence between the ulift of the explicit limit cone of a functor `K` and the explicit limit
cone of `K ⋙ uliftFunctor`.
-/
def sectionsEquiv {J : Type u} [Category.{u, u} J] (K : J ⥤ Type u) :
    uliftFunctor.{v, u}.obj (Functor.sections K) ≃
      (Functor.sections (K ⋙ uliftFunctor.{v, u})) where
  toFun := fun ⟨u, hu⟩ => ⟨fun j => ⟨u j⟩, fun f => by simp [hu f]⟩
  invFun := fun ⟨u, hu⟩ => ⟨fun j => (u j).down, fun f => by simp [← hu f]⟩
  left_inv _ := by apply ULift.ext; ext; rfl
  right_inv _ := by ext; rfl

/--
The functor `uliftFunctor : Type u ⥤ Type (max u v)` creates `u`-small limits.
-/
noncomputable instance : CreatesLimitsOfSize.{u, u} uliftFunctor.{v, u} where
  CreatesLimitsOfShape := {
    CreatesLimit := fun {K} =>
      @createsLimitOfFullyFaithfulOfIso _ _ _ _ _ _ K uliftFunctor _ _ _ (limit K)
        (uliftFunctor.{v, u}.mapIso (equivEquivIso (isLimitEquivSections.{u, u}
        (limit.isLimit K))) ≪≫ (equivEquivIso (sectionsEquiv K)) ≪≫
        (equivEquivIso (isLimitEquivSections.{u, max u v}
        (limit.isLimit (K ⋙ uliftFunctor.{v, u})))).symm) }

/--
The equivalence between `K.sections` and `(K ⋙ uliftFunctor.{v, u}).sections`. This is used to show
that `uliftFunctor` preserves limits that are too possibly too large to exist in the source
category.
-/
def sectionsEquiv' {J : Type*} [Category J] (K : J ⥤ Type u) :
    K.sections ≃ (K ⋙ uliftFunctor.{v, u}).sections where
  toFun := fun ⟨u, hu⟩ => ⟨fun j => ⟨u j⟩, fun f => by simp [hu f]⟩
  invFun := fun ⟨u, hu⟩ => ⟨fun j => (u j).down, @fun j j' f => by simp [← hu f]⟩
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl

/--
The functor `uliftFunctor : Type u ⥤ Type (max u v)` preserves limits.
-/
noncomputable
instance : PreservesLimits uliftFunctor.{v, u} where
  preservesLimitsOfShape {J} := {
    preservesLimit := fun {K} => {
      preserves := fun {c} hc => by
        apply Nonempty.some
        rw [Types.isLimit_iff ((uliftFunctor.{v, u}).mapCone c)]
        intro s hs
        obtain ⟨x, hx₁, hx₂⟩ := (Types.isLimit_iff c).mp ⟨hc⟩ _ ((sectionsEquiv' K).symm ⟨s, hs⟩).2
        exact ⟨⟨x⟩, fun i => ULift.ext _ _ (hx₁ i),
          fun y hy => ULift.ext _ _ (hx₂ y.down fun i ↦ (ULift.ext_iff _ _).mp (hy i))⟩ } }

/--
The equivalence between the ulift of the explicit colimit cocone of a functor `K` and the explicit
colimit cocone of `K ⋙ uliftFunctor`.
-/
def quotEquiv {J : Type u} [Category.{u, u} J] (K : J ⥤ Type u) :
    uliftFunctor.{v, u}.obj (Types.Quot.{u, u} K) ≃
      (Types.Quot.{u, v} (K ⋙ uliftFunctor.{v, u})) where
  toFun := fun ⟨u⟩ => Quot.map (fun ⟨j, x⟩ ↦ ⟨j, ⟨x⟩⟩)
    (fun _ _ ⟨f, h⟩ => ⟨f, ULift.ext _ _ h⟩) u
  invFun := fun u => ⟨Quot.map (fun ⟨j, x⟩ ↦ ⟨j, x.down⟩)
    (fun _ _ ⟨f, h⟩ => ⟨f, (ULift.ext_iff.{v, u} _ _).mp h⟩) u⟩
  left_inv := by
    intro ⟨x⟩
    apply ULift.ext
    simp only [Functor.comp_obj, Quot.map]
    rw [← Quot.out_eq x]
  right_inv := by
    intro x
    simp only [Functor.comp_obj, Quot.map]
    rw [← Quot.out_eq x]
    rfl

/--
The functor `uliftFunctor : Type u ⥤ Type (max u v)` creates `u`-small colimits.
-/
noncomputable instance : CreatesColimitsOfSize.{u, u} uliftFunctor.{v, u} where
  CreatesColimitsOfShape := {
    CreatesColimit := fun {K} =>
      @createsColimitOfFullyFaithfulOfIso _ _ _ _ _ _ K uliftFunctor.{v, u} _ _
        (Types.hasColimit.{u, max u v} (K ⋙ uliftFunctor.{v, u})) (colimit K)
        (uliftFunctor.{v, u}.mapIso (equivEquivIso (colimitEquivQuot.{u, u} K)) ≪≫
        (equivEquivIso (quotEquiv K)) ≪≫
        (equivEquivIso (colimitEquivQuot.{u, v} (K ⋙ uliftFunctor.{v, u}))).symm) }

end CategoryTheory.Limits.Types
