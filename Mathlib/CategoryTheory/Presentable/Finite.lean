/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.CategoryTheory.Presentable.Basic

/-!
# Finitely Presentable Objects

We define finitely presentable objects as a synonym for `ℵ₀`-presentable objects,
and link this definition with the preservation of filtered colimits.

-/


universe w v' v u' u

namespace CategoryTheory

open Limits Opposite Cardinal

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

attribute [local instance] fact_isRegular_aleph0

/-- A functor `F : C ⥤ D` is finitely accessible if it is `ℵ₀`-accessible.
Equivalently, it preserves all filtered colimits.
See `CategoryTheory.Functor.IsFinitelyAccessible_iff_preservesFilteredColimits`. -/
abbrev Functor.IsFinitelyAccessible (F : C ⥤ D) : Prop := IsCardinalAccessible.{w} F ℵ₀

lemma Functor.IsFinitelyAccessible_iff_preservesFilteredColimitsOfSize {F : C ⥤ D} :
    IsFinitelyAccessible.{w} F ↔ PreservesFilteredColimitsOfSize.{w, w} F := by
  refine ⟨fun ⟨H⟩ ↦ ⟨?_⟩, fun ⟨H⟩ ↦ ⟨?_⟩⟩ <;>
    simp only [isCardinalFiltered_aleph0_iff] at * <;>
    exact H

lemma Functor.isFinitelyAccessible_iff_preservesFilteredColimits {F : C ⥤ D} :
    IsFinitelyAccessible.{v'} F ↔ PreservesFilteredColimits F :=
  IsFinitelyAccessible_iff_preservesFilteredColimitsOfSize

/-- An object `X` is finitely presentable if `Hom(X, -)` preserves all filtered colimits. -/
abbrev IsFinitelyPresentable (X : C) : Prop :=
  IsCardinalPresentable.{w} X ℵ₀

variable (C) in
/-- `IsFinitelyPresentable` as an `ObjectProperty` on `C`. This is sometimes called "compact". -/
def ObjectProperty.isFinitelyPresentable : ObjectProperty C := fun X ↦ IsFinitelyPresentable.{w} X

variable (C) in
/-- A morphism `f : X ⟶ Y` is finitely presentable if it is so as an object of `Under X`. -/
def MorphismProperty.isFinitelyPresentable : MorphismProperty C :=
  fun _ _ f ↦ ObjectProperty.isFinitelyPresentable.{w} _ (CategoryTheory.Under.mk f)

lemma isFinitelyPresentable_iff_preservesFilteredColimitsOfSize {X : C} :
    IsFinitelyPresentable.{w} X ↔ PreservesFilteredColimitsOfSize.{w, w} (coyoneda.obj (op X)) :=
  Functor.IsFinitelyAccessible_iff_preservesFilteredColimitsOfSize

lemma isFinitelyPresentable_iff_preservesFilteredColimits {X : C} :
    IsFinitelyPresentable.{v} X ↔ PreservesFilteredColimits (coyoneda.obj (op X)) :=
  Functor.IsFinitelyAccessible_iff_preservesFilteredColimitsOfSize

instance (X : C) [IsFinitelyPresentable.{w} X] :
    PreservesFilteredColimitsOfSize.{w, w} (coyoneda.obj (op X)) := by
  rw [← isFinitelyPresentable_iff_preservesFilteredColimitsOfSize]
  infer_instance

lemma IsFinitelyPresentable.exists_hom_of_isColimit {J : Type w} [SmallCategory J] [IsFiltered J]
    {D : J ⥤ C} {c : Cocone D} (hc : IsColimit c) {X : C} [IsFinitelyPresentable.{w} X]
    (f : X ⟶ c.pt) :
    ∃ (j : J) (p : X ⟶ D.obj j), p ≫ c.ι.app j = f :=
  Types.jointly_surjective_of_isColimit (isColimitOfPreserves (coyoneda.obj (op X)) hc) f

lemma IsFinitelyPresentable.exists_eq_of_isColimit {J : Type w} [SmallCategory J] [IsFiltered J]
    {D : J ⥤ C} {c : Cocone D} (hc : IsColimit c) {X : C} [IsFinitelyPresentable.{w} X]
    {i j : J} (f : X ⟶ D.obj i) (g : X ⟶ D.obj j) (h : f ≫ c.ι.app i = g ≫ c.ι.app j) :
    ∃ (k : J) (u : i ⟶ k) (v : j ⟶ k), f ≫ D.map u = g ≫ D.map v :=
  (Types.FilteredColimit.isColimit_eq_iff _ (isColimitOfPreserves (coyoneda.obj (op X)) hc)).mp h

lemma IsFinitelyPresentable.exists_hom_of_isColimit_under
    {J : Type w} [SmallCategory J] [IsFiltered J] {D : J ⥤ C} {c : Cocone D} (hc : IsColimit c)
    {X A : C} (p : X ⟶ A) (s : (Functor.const J).obj X ⟶ D)
    [IsFinitelyPresentable.{w} (Under.mk p)]
    (f : A ⟶ c.pt) (h : ∀ (j : J), s.app j ≫ c.ι.app j = p ≫ f) :
    ∃ (j : J) (q : A ⟶ D.obj j), p ≫ q = s.app j ∧ q ≫ c.ι.app j = f := by
  have : Nonempty J := IsFiltered.nonempty
  let hc' := Under.isColimitLiftCocone D s c (p ≫ f) h hc
  obtain ⟨j, q, hq⟩ := exists_hom_of_isColimit (X := Under.mk p) hc' (Under.homMk f rfl)
  use j, q.right, Under.w q, congr($(hq).right)

lemma HasCardinalFilteredColimits_iff_hasFilteredColimitsOfSize :
    HasCardinalFilteredColimits.{w} C ℵ₀ ↔ HasFilteredColimitsOfSize.{w, w} C := by
  refine ⟨fun ⟨H⟩ ↦ ⟨?_⟩, fun ⟨H⟩ ↦ ⟨?_⟩⟩ <;>
    simp only [isCardinalFiltered_aleph0_iff] at * <;>
    exact H

lemma HasCardinalFilteredColimits_iff_hasFilteredColimits :
    HasCardinalFilteredColimits.{v} C ℵ₀ ↔ HasFilteredColimits C :=
  HasCardinalFilteredColimits_iff_hasFilteredColimitsOfSize

end CategoryTheory
