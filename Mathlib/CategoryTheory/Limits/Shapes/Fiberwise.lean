/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!

# Computing Colimits Fiberwise

In this file, we consider category `J` equipped with a functor `F : J ⥤ D` to a discrete category
`D`. Then the colimit of any diagram `diagram : J ⥤ C` can be computed fiberwise, i.e., for each
`d : D`, we consider the fiber `F.Fiber d` of `F` over `d`, and the colimit of the diagram
`diagram` restricted to `F.Fiber d`, then we take the coproduct of these restricted colimits.

## Main Results

- `colimitOfFiber`: As above, given colimits on each restriction, and coproduct of the values, this
  gives the colimit of the original diagram `diagram`.

-/

universe v v₁ v₂ u u₁ u₂

open CategoryTheory Functor Category

variable {J : Type u} {D : Type u₁}
  [Category.{v} J] [Category.{v₁} D] [IsDiscrete D]
  (F : J ⥤ D)
  {C : Type u₂} [Category.{v₂} C] (diagram : J ⥤ C)

namespace CategoryTheory

namespace Functor

/-- The object property that defines the fibers. -/
abbrev fiberProp (d : D) : ObjectProperty J :=
  fun j ↦ F.obj j = d

/-- The fiber of `F : J ⥤ D` over an object `d : D`. This is a full subcategory of `J`. -/
abbrev Fiber (d : D) : Type u :=
  (F.fiberProp d).FullSubcategory

/-- The forgetful functor from the fiber to the base category. -/
@[simps!] abbrev fiberIncl (d : D) : (F.Fiber d) ⥤ J :=
  (F.fiberProp d).ι

/-- The inclusion of an object into its fiber. -/
abbrev toFiber (d : D) (j : J) (h : F.obj j = d) : F.Fiber d where
  obj := j
  property := h

/-- Special case of `toFiber` when the relevant objects are definitionally equal. -/
abbrev toFiber' (j : J) : F.Fiber (F.obj j) :=
  F.toFiber _ j rfl

theorem fiberCongr {j₁ j₂ : J} (f : j₁ ⟶ j₂) : F.obj j₁ = F.obj j₂ :=
  IsDiscrete.eq_of_hom (F.map f)

/-- Constructing a morphism in a fiber. -/
abbrev fiberMap {j₁ j₂ : J} (f : j₁ ⟶ j₂) :
    F.toFiber' j₁ ⟶ F.toFiber _ j₂ (F.fiberCongr f).symm :=
  f

/-- Constructing a morphism in a fiber. -/
abbrev fiberMap' {j₁ j₂ : J} (f : j₁ ⟶ j₂) :
    F.toFiber _ j₁ (F.fiberCongr f) ⟶ F.toFiber' j₂ :=
  f

@[elab_as_elim] lemma fiber_inductionOn {motive : ∀ {j₁ j₂ : J}, (j₁ ⟶ j₂) → Prop}
    {j₁ j₂ : J} (f : j₁ ⟶ j₂)
    (ih : ∀ d : D, ∀ {j₁ j₂ : F.Fiber d} (f : j₁ ⟶ j₂), motive f) :
    motive f :=
  ih _ (F.fiberMap f)

end Functor

namespace Limits

open Functor

variable (fiberwiseCocone : ∀ d : D, Cocone (F.fiberIncl d ⋙ diagram))
  (cofan : Cofan fun d : D ↦ (fiberwiseCocone d).pt)

/-- Given a functor `F : J ⥤ D` to a discrete category `D`, and a diagram `diagram : J ⥤ C`,
we can construct a cocone over `diagram` using the following algorithm:

1. For each `d : D`, construct a cocone over the restricted diagram `F.fiberIncl d ⋙ diagram`.
2. Take a cofan of the values of these cocones over all `d : D`.
-/
@[simps] def coconeOfFiber : Cocone diagram where
  pt := cofan.pt
  ι :=
  { app j := (fiberwiseCocone (F.obj j)).ι.app (F.toFiber' j) ≫ cofan.inj (F.obj j)
    naturality j₁ j₂ f := by
      simp only [const_obj_obj, const_obj_map, comp_id]
      have := (fiberwiseCocone (F.obj j₁)).w (F.fiberMap f)
      rw [← this, Functor.comp_map, assoc]
      unfold toFiber'
      congr 2 <;> try { rw [F.fiberCongr f] }
      congr 1 <;> try { rw [F.fiberCongr f] }
      congr 1 <;> try { rw [F.fiberCongr f] }
      exact heq_of_eqRec_eq (by rw [F.fiberCongr f]) rfl }

variable (fiberwiseColimit : ∀ d : D, IsColimit (fiberwiseCocone d))
  (colimitCofan : IsColimit cofan)

/-- Given a functor `F : J ⥤ D` to a discrete category, the colimit of any diagram `J ⥤ C` can
be computed using this algorithm:

1. For each `d : D`, compute the colimit of the restricted diagram `F.fiberIncl d ⋙ diagram`.
2. Take the coproduct of these colimits over all `d : D`.
-/
@[simps] def colimitOfFiber : IsColimit (coconeOfFiber F diagram fiberwiseCocone cofan) where
  desc c := Cofan.IsColimit.desc colimitCofan fun d ↦ (fiberwiseColimit d).desc
    (c.whisker (F.fiberIncl d))
  uniq c s w := by
    refine Cofan.IsColimit.hom_ext colimitCofan _ _ fun d ↦
      (fiberwiseColimit d).hom_ext fun j ↦ ?_
    rw [Cofan.IsColimit.fac, IsColimit.fac, Cocone.whisker_ι, whiskerLeft_app, ← w,
      coconeOfFiber_ι_app, assoc]
    obtain ⟨j, rfl⟩ := j
    rfl

-- Not an instance because `D` cannot be inferred.
theorem hasColimit_of_fiber [∀ d, HasColimit (F.fiberIncl d ⋙ diagram)]
    [h : HasColimit (Discrete.functor fun d ↦ colimit (F.fiberIncl d ⋙ diagram))] :
    HasColimit diagram :=
  ⟨⟨⟨_, colimitOfFiber F diagram _ _
    (fun d ↦ colimit.isColimit (F.fiberIncl d ⋙ diagram))
    (coproductIsCoproduct fun d ↦ colimit (F.fiberIncl d ⋙ diagram))⟩⟩⟩

-- Not an instance because `D` cannot be inferred.
theorem hasColimitOfShapes_of_fiber
    [∀ d, HasColimitsOfShape (F.Fiber d) C] [HasCoproductsOfShape D C] :
    HasColimitsOfShape J C :=
  ⟨fun diagram ↦ hasColimit_of_fiber F diagram⟩

end Limits

end CategoryTheory
