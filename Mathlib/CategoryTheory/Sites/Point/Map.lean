/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Sites.Point.OfCofiltered
public import Mathlib.CategoryTheory.Sites.CoverLifting

/-!
# ...


-/

@[expose] public section

universe w v' v u' u

namespace CategoryTheory.GrothendieckTopology.Point
open Limits Opposite

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  [LocallySmall.{w} D]
  {J : GrothendieckTopology C} (Φ : Point.{w} J) (F : C ⥤ D)
  (K : GrothendieckTopology D)

noncomputable def map' [IsCofiltered Φ.fiber.Elements] [EssentiallySmall.{w} Φ.fiber.Elements]
    [F.IsCocontinuous J K] :
    Point.{w} K :=
  Point.ofCofiltered.{w} (CategoryOfElements.π Φ.fiber ⋙ F) (by
    intro Y R hR ⟨U, u⟩ f
    dsimp at f ⊢
    obtain ⟨V, g, hg, v, rfl⟩ :=
      Φ.jointly_surjective _ (F.cover_lift J K (K.pullback_stable f hR)) u
    exact ⟨_, F.map g ≫ f, hg, Φ.fiber.elementsMk _ v, ⟨g, rfl⟩, 𝟙 _, by simp⟩)

noncomputable def mapAux {N : Type w} [SmallCategory N] [IsCofiltered N]
    [F.IsCocontinuous J K]
    (p : N ⥤ Φ.fiber.Elements) [p.Initial] :
    Point.{w} K :=
  Point.ofCofiltered.{w} (p ⋙ CategoryOfElements.π Φ.fiber ⋙ F) (by
    intro Y R hR U f
    dsimp at f
    obtain ⟨V, g, hg, v, hv⟩ :=
      Φ.jointly_surjective _ (F.cover_lift J K (K.pullback_stable f hR)) (p.obj U).snd
    let γ : Φ.fiber.elementsMk V v ⟶ p.obj U := ⟨g, hv⟩
    obtain ⟨l⟩ : Nonempty (CostructuredArrow p (Φ.fiber.elementsMk V v)) := inferInstance
    obtain ⟨W, a, rfl⟩ := CostructuredArrow.mk_surjective l
    obtain ⟨W, a, b, hb⟩ : ∃ (W : N) (a : W ⟶ U) (b : F.obj (p.obj W).fst ⟶ F.obj V),
        b ≫ F.map g = F.map (p.map a).1 := by
      refine ⟨W, ?_, sorry⟩
      sorry
    exact ⟨_, F.map g ≫ f, hg, W, a, b, by simp [reassoc_of% hb]⟩)


noncomputable def map [F.IsCocontinuous J K] : Point.{w} K :=
  Φ.mapAux F K (fromCofilteredInitialModel _)

end CategoryTheory.GrothendieckTopology.Point
