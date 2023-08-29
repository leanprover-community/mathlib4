/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.Limits.Preserves.Basic

#align_import category_theory.category.Cat.limit from "leanprover-community/mathlib"@"1995c7bbdbb0adb1b6d5acdc654f6cf46ed96cfa"

/-!
# The category of small categories has all small limits.

An object in the limit consists of a family of objects,
which are carried to one another by the functors in the diagram.
A morphism between two such objects is a family of morphisms between the corresponding objects,
which are carried to one another by the action on morphisms of the functors in the diagram.

## Future work
Can the indexing category live in a lower universe?
-/


noncomputable section

universe v u

open CategoryTheory.Limits

namespace CategoryTheory

variable {J : Type v} [SmallCategory J]

namespace Cat

namespace HasLimits

instance categoryObjects {F : J ⥤ Cat.{u, u}} {j} :
    SmallCategory ((F ⋙ Cat.objects.{u, u}).obj j) :=
  (F.obj j).str
set_option linter.uppercaseLean3 false in
#align category_theory.Cat.has_limits.category_objects CategoryTheory.Cat.HasLimits.categoryObjects

/-- Auxiliary definition:
the diagram whose limit gives the morphism space between two objects of the limit category. -/
@[simps]
def homDiagram {F : J ⥤ Cat.{v, v}} (X Y : limit (F ⋙ Cat.objects.{v, v})) : J ⥤ Type v where
  obj j := limit.π (F ⋙ Cat.objects) j X ⟶ limit.π (F ⋙ Cat.objects) j Y
  map f g := by
    refine' eqToHom _ ≫ (F.map f).map g ≫ eqToHom _
    -- ⊢ limit.π (F ⋙ objects) Y✝ X = (F.map f).obj (limit.π (F ⋙ objects) X✝ X)
    exact (congr_fun (limit.w (F ⋙ Cat.objects) f) X).symm
    -- ⊢ (F.map f).obj (limit.π (F ⋙ objects) X✝ Y) = limit.π (F ⋙ objects) Y✝ Y
    exact congr_fun (limit.w (F ⋙ Cat.objects) f) Y
    -- 🎉 no goals
  map_id X := by
    funext f
    -- ⊢ { obj := fun j => limit.π (F ⋙ objects) j X✝ ⟶ limit.π (F ⋙ objects) j Y, ma …
    letI : Category (objects.obj (F.obj X)) := (inferInstance : Category (F.obj X))
    -- ⊢ { obj := fun j => limit.π (F ⋙ objects) j X✝ ⟶ limit.π (F ⋙ objects) j Y, ma …
    simp [Functor.congr_hom (F.map_id X) f]
    -- 🎉 no goals
  map_comp {_ _ Z} f g := by
    funext h
    -- ⊢ { obj := fun j => limit.π (F ⋙ objects) j X ⟶ limit.π (F ⋙ objects) j Y, map …
    letI : Category (objects.obj (F.obj Z)) := (inferInstance : Category (F.obj Z))
    -- ⊢ { obj := fun j => limit.π (F ⋙ objects) j X ⟶ limit.π (F ⋙ objects) j Y, map …
    simp [Functor.congr_hom (F.map_comp f g) h, eqToHom_map]
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align category_theory.Cat.has_limits.hom_diagram CategoryTheory.Cat.HasLimits.homDiagram

@[simps]
instance (F : J ⥤ Cat.{v, v}) : Category (limit (F ⋙ Cat.objects)) where
  Hom X Y := limit (homDiagram X Y)
  id X := Types.Limit.mk.{v, v} (homDiagram X X) (fun j => 𝟙 _) fun j j' f => by simp
                                                                                 -- 🎉 no goals
  comp {X Y Z} f g :=
    Types.Limit.mk.{v, v} (homDiagram X Z)
      (fun j => limit.π (homDiagram X Y) j f ≫ limit.π (homDiagram Y Z) j g) fun j j' h => by
      simp [← congr_fun (limit.w (homDiagram X Y) h) f,
        ← congr_fun (limit.w (homDiagram Y Z) h) g]
  id_comp _ := by
    apply Types.limit_ext.{v, v}
    -- ⊢ ∀ (j : J), limit.π (homDiagram X✝ Y✝) j (𝟙 X✝ ≫ x✝) = limit.π (homDiagram X✝ …
    aesop_cat
    -- 🎉 no goals
  comp_id _ := by
    apply Types.limit_ext.{v, v}
    -- ⊢ ∀ (j : J), limit.π (homDiagram X✝ Y✝) j (x✝ ≫ 𝟙 Y✝) = limit.π (homDiagram X✝ …
    aesop_cat
    -- 🎉 no goals

/-- Auxiliary definition: the limit category. -/
@[simps]
def limitConeX (F : J ⥤ Cat.{v, v}) : Cat.{v, v} where α := limit (F ⋙ Cat.objects)
set_option linter.uppercaseLean3 false in
#align category_theory.Cat.has_limits.limit_cone_X CategoryTheory.Cat.HasLimits.limitConeX

/-- Auxiliary definition: the cone over the limit category. -/
@[simps]
def limitCone (F : J ⥤ Cat.{v, v}) : Cone F where
  pt := limitConeX F
  π :=
    { app := fun j =>
        { obj := limit.π (F ⋙ Cat.objects) j
          map := fun f => limit.π (homDiagram _ _) j f }
      naturality := fun j j' f =>
        CategoryTheory.Functor.ext (fun X => (congr_fun (limit.w (F ⋙ Cat.objects) f) X).symm)
          fun X Y h => (congr_fun (limit.w (homDiagram X Y) f) h).symm }
set_option linter.uppercaseLean3 false in
#align category_theory.Cat.has_limits.limit_cone CategoryTheory.Cat.HasLimits.limitCone

/-- Auxiliary definition: the universal morphism to the proposed limit cone. -/
@[simps]
def limitConeLift (F : J ⥤ Cat.{v, v}) (s : Cone F) : s.pt ⟶ limitConeX F where
  obj :=
    limit.lift (F ⋙ Cat.objects)
      { pt := s.pt
        π :=
          { app := fun j => (s.π.app j).obj
            naturality := fun _ _ f => Functor.congr_map objects (s.π.naturality f) } }
  map f := by
    fapply Types.Limit.mk.{v, v}
    -- ⊢ (j : J) → (homDiagram (limit.lift (F ⋙ objects) { pt := ↑s.pt, π := NatTrans …
    · intro j
      -- ⊢ (homDiagram (limit.lift (F ⋙ objects) { pt := ↑s.pt, π := NatTrans.mk fun j  …
      refine' eqToHom _ ≫ (s.π.app j).map f ≫ eqToHom _ <;> simp
      -- ⊢ limit.π (F ⋙ objects) j (limit.lift (F ⋙ objects) { pt := ↑s.pt, π := NatTra …
                                                            -- 🎉 no goals
                                                            -- 🎉 no goals
    · intro j j' h
      -- ⊢ (homDiagram (limit.lift (F ⋙ objects) { pt := ↑s.pt, π := NatTrans.mk fun j  …
      dsimp
      -- ⊢ eqToHom (_ : limit.π (F ⋙ objects) j' (limit.lift (F ⋙ objects) { pt := ↑s.p …
      simp only [Category.assoc, Functor.map_comp, eqToHom_map, eqToHom_trans,
        eqToHom_trans_assoc, ← Functor.comp_map]
      have := (s.π.naturality h).symm
      -- ⊢ eqToHom (_ : limit.π (F ⋙ objects) j' (limit.lift (F ⋙ objects) { pt := ↑s.p …
      dsimp at this
      -- ⊢ eqToHom (_ : limit.π (F ⋙ objects) j' (limit.lift (F ⋙ objects) { pt := ↑s.p …
      rw [Category.id_comp] at this
      -- ⊢ eqToHom (_ : limit.π (F ⋙ objects) j' (limit.lift (F ⋙ objects) { pt := ↑s.p …
      erw [Functor.congr_hom this f]
      -- ⊢ eqToHom (_ : limit.π (F ⋙ objects) j' (limit.lift (F ⋙ objects) { pt := ↑s.p …
      simp
      -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align category_theory.Cat.has_limits.limit_cone_lift CategoryTheory.Cat.HasLimits.limitConeLift

@[simp]
theorem limit_π_homDiagram_eqToHom {F : J ⥤ Cat.{v, v}} (X Y : limit (F ⋙ Cat.objects.{v, v}))
    (j : J) (h : X = Y) :
    limit.π (homDiagram X Y) j (eqToHom h) =
      eqToHom (congr_arg (limit.π (F ⋙ Cat.objects.{v, v}) j) h) := by
  subst h
  -- ⊢ limit.π (homDiagram X X) j (eqToHom (_ : X = X)) = eqToHom (_ : limit.π (F ⋙ …
  simp
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align category_theory.Cat.has_limits.limit_π_hom_diagram_eq_to_hom CategoryTheory.Cat.HasLimits.limit_π_homDiagram_eqToHom

/-- Auxiliary definition: the proposed cone is a limit cone. -/
def limitConeIsLimit (F : J ⥤ Cat.{v, v}) : IsLimit (limitCone F) where
  lift := limitConeLift F
  fac s j := CategoryTheory.Functor.ext (by simp) fun X Y f => by
                                            -- 🎉 no goals
    dsimp [limitConeLift]
    -- ⊢ limit.π (homDiagram (limit.lift (F ⋙ objects) { pt := ↑s.pt, π := NatTrans.m …
    exact Types.Limit.π_mk.{v, v} _ _ _ _
    -- 🎉 no goals
  uniq s m w := by
    symm
    -- ⊢ limitConeLift F s = m
    refine' CategoryTheory.Functor.ext _ _
    -- ⊢ ∀ (X : ↑s.pt), (limitConeLift F s).obj X = m.obj X
    · intro X
      -- ⊢ (limitConeLift F s).obj X = m.obj X
      apply Types.limit_ext.{v, v}
      -- ⊢ ∀ (j : J), limit.π (F ⋙ objects) j ((limitConeLift F s).obj X) = limit.π (F  …
      intro j
      -- ⊢ limit.π (F ⋙ objects) j ((limitConeLift F s).obj X) = limit.π (F ⋙ objects)  …
      simp [Types.Limit.lift_π_apply', ← w j]
      -- 🎉 no goals
    · intro X Y f
      -- ⊢ (limitConeLift F s).map f = eqToHom (_ : (limitConeLift F s).obj X = m.obj X …
      dsimp
      -- ⊢ Types.Limit.mk (homDiagram (limit.lift (F ⋙ objects) { pt := ↑s.pt, π := Nat …
      simp [fun j => Functor.congr_hom (w j).symm f]
      -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align category_theory.Cat.has_limits.limit_cone_is_limit CategoryTheory.Cat.HasLimits.limitConeIsLimit

end HasLimits

/-- The category of small categories has all small limits. -/
instance : HasLimits Cat.{v, v} where
  has_limits_of_shape _ :=
    { has_limit := fun F => ⟨⟨⟨HasLimits.limitCone F, HasLimits.limitConeIsLimit F⟩⟩⟩ }

instance : PreservesLimits Cat.objects.{v, v} where
  preservesLimitsOfShape :=
    { preservesLimit := fun {F} =>
        preservesLimitOfPreservesLimitCone (HasLimits.limitConeIsLimit F)
          (Limits.IsLimit.ofIsoLimit (limit.isLimit (F ⋙ Cat.objects))
            (Cones.ext (by rfl) (by aesop_cat))) }
                           -- 🎉 no goals
                                    -- 🎉 no goals

end Cat

end CategoryTheory
