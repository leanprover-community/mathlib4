/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Adam Topaz
-/
import Mathlib.CategoryTheory.Comma.StructuredArrow
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.PUnit

#align_import category_theory.limits.kan_extension from "leanprover-community/mathlib"@"c9c9fa15fec7ca18e9ec97306fb8764bfe988a7e"

/-!

# Right Kan extensions

This file defines the right Kan extensions of a functor.
They exist under the assumption that the target category has enough limits.

The main definitions is `Ran ι`, where `ι : S ⥤ L` is a functor.
Namely, `Ran ι : (S ⥤ D) ⥤ (L ⥤ D)` is the right Kan extension.

To access the adjunction associated to this, use `Ran.adjunction`.

## TODO

- refactor `Ran` so that it relies on the general API for Kan
extensions of functors, similarly as the left Kan extension
adjunction is defined in `CategoryTheory.Functor.KanExtension.Adjunction`.


## Projects

A lot of boilerplate could be generalized by defining and working with pseudofunctors.


-/


noncomputable section

namespace CategoryTheory

open Limits

universe v v₁ v₂ v₃ u₁ u₂ u₃

variable {S : Type u₁} {L : Type u₂} {D : Type u₃}
variable [Category.{v₁} S] [Category.{v₂} L] [Category.{v₃} D]
variable (ι : S ⥤ L)

namespace Ran

attribute [local simp] StructuredArrow.proj

/-- The diagram indexed by `Ran.index ι x` used to define `Ran`. -/
abbrev diagram (F : S ⥤ D) (x : L) : StructuredArrow x ι ⥤ D :=
  StructuredArrow.proj x ι ⋙ F
set_option linter.uppercaseLean3 false in
#align category_theory.Ran.diagram CategoryTheory.Ran.diagram

variable {ι}

/-- A cone over `Ran.diagram ι F x` used to define `Ran`. -/
@[simp]
def cone {F : S ⥤ D} {G : L ⥤ D} (x : L) (f : ι ⋙ G ⟶ F) : Cone (diagram ι F x) where
  pt := G.obj x
  π :=
    { app := fun i => G.map i.hom ≫ f.app i.right
      naturality := by
        rintro ⟨⟨il⟩, ir, i⟩ ⟨⟨jl⟩, jr, j⟩ ⟨⟨⟨fl⟩⟩, fr, ff⟩
        dsimp at *
        dsimp at ff
        simp only [Category.id_comp, Category.assoc] at *
        rw [ff]
        have := f.naturality
        aesop_cat }
set_option linter.uppercaseLean3 false in
#align category_theory.Ran.cone CategoryTheory.Ran.cone

variable (ι)

/-- An auxiliary definition used to define `Ran`. -/
@[simps]
def loc (F : S ⥤ D) [h : ∀ x, HasLimit (diagram ι F x)] : L ⥤ D where
  obj x := limit (diagram ι F x)
  map {X Y} f :=
    haveI : HasLimit <| StructuredArrow.map f ⋙ diagram ι F X := h Y
    limit.pre (diagram ι F X) (StructuredArrow.map f)
  map_id := by
    intro l
    haveI : HasLimit (StructuredArrow.map (𝟙 _) ⋙ diagram ι F l) := h _
    dsimp
    ext j
    simp only [Category.id_comp, limit.pre_π]
    congr 1
    simp
  map_comp := by
    intro x y z f g
    apply limit.hom_ext
    intro j
    erw [limit.pre_pre, limit.pre_π, limit.pre_π]
    congr 1
    aesop_cat
set_option linter.uppercaseLean3 false in
#align category_theory.Ran.loc CategoryTheory.Ran.loc

/-- An auxiliary definition used to define `Ran` and `Ran.adjunction`. -/
@[simps]
def equiv (F : S ⥤ D) [h : ∀ x, HasLimit (diagram ι F x)] (G : L ⥤ D) :
    (G ⟶ loc ι F) ≃ (((whiskeringLeft _ _ _).obj ι).obj G ⟶ F) where
  toFun f :=
    { app := fun x => f.app _ ≫ limit.π (diagram ι F (ι.obj x)) (StructuredArrow.mk (𝟙 _))
      naturality := by
        intro x y ff
        dsimp only [whiskeringLeft]
        simp only [Functor.comp_map, NatTrans.naturality_assoc, loc_map, Category.assoc]
        congr 1
        haveI : HasLimit (StructuredArrow.map (ι.map ff) ⋙ diagram ι F (ι.obj x)) := h _
        erw [limit.pre_π]
        let t : StructuredArrow.mk (𝟙 (ι.obj x)) ⟶
          (StructuredArrow.map (ι.map ff)).obj (StructuredArrow.mk (𝟙 (ι.obj y))) :=
          StructuredArrow.homMk ff ?_
        · convert (limit.w (diagram ι F (ι.obj x)) t).symm using 1
        · simp }
  invFun f :=
    { app := fun x => limit.lift (diagram ι F x) (cone _ f)
      naturality := by
        intro x y ff
        apply limit.hom_ext
        intros j
        haveI : HasLimit (StructuredArrow.map ff ⋙ diagram ι F x) := h _
        erw [limit.lift_pre, limit.lift_π, Category.assoc, limit.lift_π (cone _ f) j]
        simp }
  left_inv := by
    intro x
    ext k
    apply limit.hom_ext
    intros j
    dsimp only [cone]
    rw [limit.lift_π]
    simp only [NatTrans.naturality_assoc, loc_map]
    haveI : HasLimit (StructuredArrow.map j.hom ⋙ diagram ι F k) := h _
    erw [limit.pre_π]
    congr
    rcases j with ⟨⟨⟩, _, _⟩
    aesop_cat
  right_inv := by aesop_cat
set_option linter.uppercaseLean3 false in
#align category_theory.Ran.equiv CategoryTheory.Ran.equiv

end Ran

/-- The right Kan extension of a functor. -/
@[simps!]
def ran [∀ X, HasLimitsOfShape (StructuredArrow X ι) D] : (S ⥤ D) ⥤ L ⥤ D :=
  Adjunction.rightAdjointOfEquiv (fun F G => (Ran.equiv ι G F).symm) (by {
    -- Porting note (#10936): was `tidy`
    intros X' X Y f g
    ext t
    apply limit.hom_ext
    intros j
    dsimp [Ran.equiv]
    simp })
set_option linter.uppercaseLean3 false in
#align category_theory.Ran CategoryTheory.ran

namespace Ran

variable (D)

/-- The adjunction associated to `Ran`. -/
def adjunction [∀ X, HasLimitsOfShape (StructuredArrow X ι) D] :
    (whiskeringLeft _ _ D).obj ι ⊣ ran ι :=
  Adjunction.adjunctionOfEquivRight _ _
set_option linter.uppercaseLean3 false in
#align category_theory.Ran.adjunction CategoryTheory.Ran.adjunction

theorem reflective [ι.Full] [ι.Faithful] [∀ X, HasLimitsOfShape (StructuredArrow X ι) D] :
    IsIso (adjunction D ι).counit := by
  simp only [NatTrans.isIso_iff_isIso_app]
  intro F X
  dsimp [adjunction, equiv]
  simp only [Category.id_comp]
  exact ((limit.isLimit _).conePointUniqueUpToIso
    (limitOfDiagramInitial StructuredArrow.mkIdInitial _)).isIso_hom
set_option linter.uppercaseLean3 false in
#align category_theory.Ran.reflective CategoryTheory.Ran.reflective

end Ran

end CategoryTheory

-- These lemmas have always been bad (#7657), but leanprover/lean4#2644 made `simp` start noticing
attribute [nolint simpNF] CategoryTheory.Ran.equiv_symm_apply_app
  CategoryTheory.Ran.equiv_apply_app
