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

# Left Kan extensions

This file defines the left Kan extensions of a functor.
They exist under the assumption that the target category has enough colimits.

The main definitions is `Lan ι`, where `ι : S ⥤ L` is a functor:
`Lan ι : (S ⥤ D) ⥤ (L ⥤ D)` is the left Kan extension.

To access the adjunction associated to this, use `Lan.adjunction`.

# Projects

A lot of boilerplate could be generalized by defining and working with pseudofunctors.

## TODO

* remove this file when #10425 is merged, so that `Lan` and `Ran` are defined
in terms of the API in `CategoryTheory.Functor.KanExtension`.

-/


noncomputable section

namespace CategoryTheory

open Limits

universe v v₁ v₂ v₃ u₁ u₂ u₃

variable {S : Type u₁} {L : Type u₂} {D : Type u₃}
variable [Category.{v₁} S] [Category.{v₂} L] [Category.{v₃} D]
variable (ι : S ⥤ L)

namespace Lan

attribute [local simp] CostructuredArrow.proj

/-- The diagram indexed by `Lan.index ι x` used to define `Lan`. -/
abbrev diagram (F : S ⥤ D) (x : L) : CostructuredArrow ι x ⥤ D :=
  CostructuredArrow.proj ι x ⋙ F
set_option linter.uppercaseLean3 false in
#align category_theory.Lan.diagram CategoryTheory.Lan.diagram

variable {ι}

/-- A cocone over `Lan.diagram ι F x` used to define `Lan`. -/
@[simp]
def cocone {F : S ⥤ D} {G : L ⥤ D} (x : L) (f : F ⟶ ι ⋙ G) : Cocone (diagram ι F x) where
  pt := G.obj x
  ι :=
    { app := fun i => f.app i.left ≫ G.map i.hom
      naturality := by
        rintro ⟨ir, ⟨il⟩, i⟩ ⟨jl, ⟨jr⟩, j⟩ ⟨fl, ⟨⟨fl⟩⟩, ff⟩
        dsimp at *
        simp only [Functor.comp_map, Category.comp_id, NatTrans.naturality_assoc]
        rw [← G.map_comp, ff]
        aesop_cat }
set_option linter.uppercaseLean3 false in
#align category_theory.Lan.cocone CategoryTheory.Lan.cocone

variable (ι)

/-- An auxiliary definition used to define `Lan`. -/
@[simps]
def loc (F : S ⥤ D) [I : ∀ x, HasColimit (diagram ι F x)] : L ⥤ D where
  obj x := colimit (diagram ι F x)
  map {x y} f :=
    haveI : HasColimit (CostructuredArrow.map f ⋙ diagram ι F y) := I _
    colimit.pre (diagram ι F y) (CostructuredArrow.map f)
  map_id := by
    intro l
    dsimp
    haveI : HasColimit (CostructuredArrow.map (𝟙 l) ⋙ diagram ι F l) := I _
    ext j
    erw [colimit.ι_pre, Category.comp_id]
    congr 1
    simp
  map_comp := by
    intro x y z f g
    dsimp
    haveI : HasColimit (CostructuredArrow.map (f ≫ g) ⋙ diagram ι F z) := I _
    ext j
    let ff : CostructuredArrow ι _ ⥤ _ := CostructuredArrow.map f
    let gg : CostructuredArrow ι _ ⥤ _ := CostructuredArrow.map g
    let dd := diagram ι F z
    -- Porting note: It seems that even Lean3 had some trouble with instances in this case.
    -- I don't know why lean can't deduce the following three instances...
    -- The corresponding `haveI` statements could be removed from `Ran.loc` and it just worked,
    -- here it doesn't...
    haveI : HasColimit (ff ⋙ gg ⋙ dd) := I _
    haveI : HasColimit ((ff ⋙ gg) ⋙ dd) := I _
    haveI : HasColimit (gg ⋙ dd) := I _
    change _ = colimit.ι ((ff ⋙ gg) ⋙ dd) j ≫ _ ≫ _
    erw [colimit.pre_pre dd gg ff, colimit.ι_pre, colimit.ι_pre]
    congr 1
    simp
set_option linter.uppercaseLean3 false in
#align category_theory.Lan.loc CategoryTheory.Lan.loc

/-- An auxiliary definition used to define `Lan` and `Lan.adjunction`. -/
@[simps]
def equiv (F : S ⥤ D) [I : ∀ x, HasColimit (diagram ι F x)] (G : L ⥤ D) :
    (loc ι F ⟶ G) ≃ (F ⟶ ((whiskeringLeft _ _ _).obj ι).obj G) where
  toFun f :=
    { app := fun x => colimit.ι (diagram ι F (ι.obj x)) (CostructuredArrow.mk (𝟙 _)) ≫ f.app _
      naturality := by
        intro x y ff
        dsimp only [whiskeringLeft]
        simp only [Functor.comp_map, Category.assoc]
        rw [← f.naturality (ι.map ff), ← Category.assoc, ← Category.assoc]
        let fff : CostructuredArrow ι _ ⥤ _ := CostructuredArrow.map (ι.map ff)
        -- same issue :-(
        haveI : HasColimit (fff ⋙ diagram ι F (ι.obj y)) := I _
        erw [colimit.ι_pre (diagram ι F (ι.obj y)) fff (CostructuredArrow.mk (𝟙 _))]
        let xx : CostructuredArrow ι (ι.obj y) := CostructuredArrow.mk (ι.map ff)
        let yy : CostructuredArrow ι (ι.obj y) := CostructuredArrow.mk (𝟙 _)
        let fff' : xx ⟶ yy :=
          CostructuredArrow.homMk ff
            (by
              simp only [xx, CostructuredArrow.mk_hom_eq_self]
              erw [Category.comp_id])
        erw [colimit.w (diagram ι F (ι.obj y)) fff']
        congr
        simp [fff] }
  invFun f :=
    { app := fun x => colimit.desc (diagram ι F x) (cocone _ f)
      naturality := by
        intro x y ff
        apply colimit.hom_ext
        intros j
        haveI : HasColimit (CostructuredArrow.map ff ⋙ diagram ι F y) := I _
        erw [colimit.pre_desc, ← Category.assoc, colimit.ι_desc, colimit.ι_desc]
        simp }
  left_inv := by
    intros x
    dsimp
    ext k
    dsimp
    apply colimit.hom_ext
    intros j
    rw [colimit.ι_desc]
    dsimp only [cocone]
    rw [Category.assoc, ← x.naturality j.hom, ← Category.assoc]
    congr 1
    dsimp [loc]
    haveI : HasColimit (CostructuredArrow.map j.hom ⋙ diagram ι F k) := I _
    erw [colimit.ι_pre (diagram ι F k) (CostructuredArrow.map j.hom)]
    congr
    rcases j with ⟨_, ⟨⟩, _⟩
    simp only [CostructuredArrow.map_mk, Category.id_comp]
    rfl
  right_inv := by aesop_cat
set_option linter.uppercaseLean3 false in
#align category_theory.Lan.equiv CategoryTheory.Lan.equiv

-- These lemmas have always been bad (#7657), but leanprover/lean4#2644 made `simp` start noticing
attribute [nolint simpNF]
  CategoryTheory.Lan.equiv_symm_apply_app
  CategoryTheory.Lan.equiv_apply_app

end Lan

/-- The left Kan extension of a functor. -/
@[simps!]
def lan [∀ F : S ⥤ D, ∀ x, HasColimit (Lan.diagram ι F x)] : (S ⥤ D) ⥤ L ⥤ D :=
  Adjunction.leftAdjointOfEquiv (fun F G => Lan.equiv ι F G) (by {
    intros X' X Y f g
    ext
    simp [Lan.equiv] })
set_option linter.uppercaseLean3 false in
#align category_theory.Lan CategoryTheory.lan

namespace Lan

variable (D)

/-- The adjunction associated to `Lan`. -/
def adjunction [∀ F : S ⥤ D, ∀ x, HasColimit (Lan.diagram ι F x)] :
    lan ι ⊣ (whiskeringLeft _ _ D).obj ι :=
  Adjunction.adjunctionOfEquivLeft _ _
set_option linter.uppercaseLean3 false in
#align category_theory.Lan.adjunction CategoryTheory.Lan.adjunction

theorem coreflective [ι.Full] [ι.Faithful] [∀ F : S ⥤ D, ∀ x, HasColimit (Lan.diagram ι F x)] :
    IsIso (adjunction D ι).unit := by
  suffices ∀ (X : S ⥤ D), IsIso (NatTrans.app (adjunction D ι).unit X) by
    apply NatIso.isIso_of_isIso_app
  intro F
  suffices ∀ (X : S), IsIso (NatTrans.app (NatTrans.app (adjunction D ι).unit F) X) by
    apply NatIso.isIso_of_isIso_app
  intro X
  dsimp [adjunction, equiv]
  simp only [Category.comp_id]
  exact
    Iso.isIso_hom
      ((colimit.isColimit _).coconePointUniqueUpToIso
          (colimitOfDiagramTerminal CostructuredArrow.mkIdTerminal _)).symm
set_option linter.uppercaseLean3 false in
#align category_theory.Lan.coreflective CategoryTheory.Lan.coreflective

end Lan

end CategoryTheory
