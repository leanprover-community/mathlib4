/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour, Wojciech Nawrocki
-/
module

import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Functor.TwoSquare
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

/-!
# Cartesian natural transformations

Defines natural transformations between functors is cartesian if all their naturality squares are
pullback squares.

## Main results

- `NatTrans.isCartesian_of_discrete` shows that any natural transformation between functors from a
  discrete category is cartesian.

- `NatTrans.isCartesian_of_isIso` shows that any natural isomorphism is cartesian.

- `NatTrans.isIso_of_isCartesian_of_isIso_app_terminal` shows that a cartesian natural
  transformation is an isomorphism if its component at a terminal object is an isomorphism.

- `NatTrans.isCartesian_of_isPullback_isTerminal_from` shows that a natural transformation is
  cartesian if all its naturality squares to the terminal object are pullback squares.

- `NatTrans.IsCartesian.comp` shows that the composition of two cartesian natural transformations is

### References

The content here is based on our work on the formalization of polynomial functors project at the
Trimester "Prospect of Formal Mathematics" at the Hausdorff Institute (HIM) in Bonn:

https://github.com/sinhp/Poly

-/


open CategoryTheory Limits IsPullback

namespace CategoryTheory

universe v' u' v u

variable {J : Type v'} [Category.{u'} J] {C : Type u} [Category.{v} C]
variable {K : Type*} [Category K] {D : Type*} [Category D]

namespace NatTrans

open Functor

/-- A natural transformation is cartesian if all its naturality squares are pullbacks. -/
def IsCartesian {F G : J ⥤ C} (α : F ⟶ G) : Prop :=
  ∀ ⦃X Y : J⦄ (f : X ⟶ Y), IsPullback (F.map f) (α.app X) (α.app Y) (G.map f)

theorem isCartesian_of_discrete {ι : Type*} {F G : Discrete ι ⥤ C}
    (α : F ⟶ G) : IsCartesian α := by
  rintro ⟨X⟩ ⟨Y⟩ ⟨⟨rfl : X = Y⟩⟩
  simp only [Discrete.functor_map_id]
  exact IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩

theorem isCartesian_of_isIso {F G : J ⥤ C} (α : F ⟶ G) [IsIso α] : IsCartesian α :=
  fun _ _ f => IsPullback.of_vert_isIso ⟨NatTrans.naturality _ f⟩

theorem isIso_of_isCartesian_of_isIso_app_terminal {F G : J ⥤ C} (α : F ⟶ G) (hα : IsCartesian α)
    (T : J) (hT : IsTerminal T) [IsIso (α.app T)] : IsIso α :=
  @NatIso.isIso_of_isIso_app _ _ _ _ _ _ α
    (fun j ↦ isIso_snd_of_isIso <| hα <| hT.from j)

theorem isCartesian_of_isPullback_isTerminal_from {F G : J ⥤ C} (α : F ⟶ G)
    (T : J) (hT : IsTerminal T)
    (pb : ∀ Y, IsPullback (F.map (hT.from Y)) (α.app Y) (α.app T) (G.map (hT.from Y))) :
    IsCartesian α := by
  intro X Y f
  apply IsPullback.of_right (h₁₂ := F.map (hT.from Y)) (h₂₂ := G.map (hT.from Y))
  · simpa [← F.map_comp, ← G.map_comp] using (pb X)
  · exact α.naturality f
  · exact pb Y

namespace IsCartesian

theorem comp {F G H : J ⥤ C} {α : F ⟶ G} {β : G ⟶ H} (hα : IsCartesian α) (hβ : IsCartesian β) :
    IsCartesian (α ≫ β) :=
  fun _ _ f => (hα f).paste_vert (hβ f)

theorem whiskerRight {F G : J ⥤ C} {α : F ⟶ G} (hα : IsCartesian α) (H : C ⥤ D)
    [∀ (X Y : J) (f : Y ⟶ X), PreservesLimit (cospan (α.app X) (G.map f)) H] :
    IsCartesian (whiskerRight α H) :=
  fun _ _ f => (hα f).map H

theorem whiskerLeft {K : Type*} [Category K] {F G : J ⥤ C}
    {α : F ⟶ G} (hα : IsCartesian α) (H : K ⥤ J) : IsCartesian (whiskerLeft H α) :=
  fun _ _ f => hα (H.map f)

theorem hcomp {K : Type*} [Category K] {F G : J ⥤ C} {M N : C ⥤ K} {α : F ⟶ G} {β : M ⟶ N}
    (hα : IsCartesian α) (hβ : IsCartesian β)
    [∀ (X Y : J) (f : Y ⟶ X), PreservesLimit (cospan (α.app X) (G.map f)) M] :
    IsCartesian (NatTrans.hcomp α β) := by
  have ha := hα.whiskerRight M
  have hb := hβ.whiskerLeft G
  have hc := ha.comp hb
  unfold IsCartesian
  intros X Y f
  specialize hc f
  simp only [Functor.comp_obj, Functor.comp_map, comp_app,
    whiskerRight_app, whiskerLeft_app,
    naturality] at hc
  exact hc

open TwoSquare

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} C₄]
  {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {B : C₃ ⥤ C₄}

variable {C₅ : Type u₅} {C₆ : Type u₆} {C₇ : Type u₇} {C₈ : Type u₈}
  [Category.{v₅} C₅] [Category.{v₆} C₆] [Category.{v₇} C₇] [Category.{v₈} C₈]
  {T' : C₂ ⥤ C₅} {R' : C₅ ⥤ C₆} {B' : C₄ ⥤ C₆} {L' : C₃ ⥤ C₇} {R'' : C₄ ⥤ C₈} {B'' : C₇ ⥤ C₈}

theorem vComp {w : TwoSquare T L R B} {w' : TwoSquare B L' R'' B''}
    [∀ (X Y : C₁) (f : Y ⟶ X), PreservesLimit (cospan (w.app X) ((L ⋙ B).map f)) R''] :
    IsCartesian w → IsCartesian w' → IsCartesian (w ≫ᵥ w') :=
  fun cw cw' =>
    (isCartesian_of_isIso _).comp <|
    (cw.whiskerRight _).comp <|
    (isCartesian_of_isIso _).comp <|
    (cw'.whiskerLeft _).comp <|
    (isCartesian_of_isIso _)

theorem hComp {w : TwoSquare T L R B} {w' : TwoSquare T' R R' B'}
    [∀ (X Y : C₁) (f : Y ⟶ X), PreservesLimit (cospan (w.app X) ((L ⋙ B).map f)) B'] :
    IsCartesian w → IsCartesian w' → IsCartesian (w ≫ₕ w') :=
  fun cw cw' =>
    (isCartesian_of_isIso _).comp <|
    (cw'.whiskerLeft _).comp <|
    (isCartesian_of_isIso _).comp <|
    (cw.whiskerRight _).comp <|
    (isCartesian_of_isIso _)

end IsCartesian

end NatTrans

end CategoryTheory
