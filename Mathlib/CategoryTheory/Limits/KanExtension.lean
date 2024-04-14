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

# Kan extensions

This file defines the right and left Kan extensions of a functor.
They exist under the assumption that the target category has enough limits
resp. colimits.

The main definitions are `Ran ι` and `Lan ι`, where `ι : S ⥤ L` is a functor.
Namely, `Ran ι` is the right Kan extension, while `Lan ι` is the left Kan extension,
both as functors `(S ⥤ D) ⥤ (L ⥤ D)`.

To access the right resp. left adjunction associated to these, use `Ran.adjunction`
resp. `Lan.adjunction`.

# Projects

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
def cone {F : S ⥤ D} {G : L ⥤ D} (x : L) (f : ι ⋙ G ⟶ F) : Cone (diagram ι F x)
    where
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
def loc (F : S ⥤ D) [h : ∀ x, HasLimit (diagram ι F x)] : L ⥤ D
    where
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
    -- Porting note: The fact that we need to add these instances all over the place
    -- is certainly not ideal.
    haveI : HasLimit (StructuredArrow.map f ⋙ diagram ι F _) := h _
    haveI : HasLimit (StructuredArrow.map g ⋙ diagram ι F _) := h _
    haveI : HasLimit (StructuredArrow.map (f ≫ g) ⋙ diagram ι F _) := h _
    haveI : HasLimit (StructuredArrow.map g ⋙ StructuredArrow.map f ⋙ diagram ι F _) := h _
    haveI : HasLimit ((StructuredArrow.map g ⋙ StructuredArrow.map f) ⋙ diagram ι F _) := h _
    erw [limit.pre_pre, limit.pre_π, limit.pre_π]
    congr 1
    aesop_cat
set_option linter.uppercaseLean3 false in
#align category_theory.Ran.loc CategoryTheory.Ran.loc

/-- An auxiliary definition used to define `Ran` and `Ran.adjunction`. -/
@[simps]
def equiv (F : S ⥤ D) [h : ∀ x, HasLimit (diagram ι F x)] (G : L ⥤ D) :
    (G ⟶ loc ι F) ≃ (((whiskeringLeft _ _ _).obj ι).obj G ⟶ F)
    where
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
        convert (limit.w (diagram ι F (ι.obj x)) t).symm using 1
        simp }
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

theorem reflective [Full ι] [Faithful ι] [∀ X, HasLimitsOfShape (StructuredArrow X ι) D] :
    IsIso (adjunction D ι).counit := by
  suffices ∀ (X : S ⥤ D), IsIso (NatTrans.app (adjunction D ι).counit X) by
    apply NatIso.isIso_of_isIso_app
  intro F
  suffices ∀ (X : S), IsIso (NatTrans.app (NatTrans.app (adjunction D ι).counit F) X) by
    apply NatIso.isIso_of_isIso_app
  intro X
  dsimp [adjunction, equiv]
  simp only [Category.id_comp]
  exact
    IsIso.of_iso
      ((limit.isLimit _).conePointUniqueUpToIso
        (limitOfDiagramInitial StructuredArrow.mkIdInitial _))
set_option linter.uppercaseLean3 false in
#align category_theory.Ran.reflective CategoryTheory.Ran.reflective

variable {D}

abbrev self (F : L ⥤ D) [∀ x, HasLimit (Ran.diagram ι (ι ⋙ F) x)] : L ⥤ D :=
  Ran.loc ι (ι ⋙ F)

end Ran

class IsRightKanExtendedAlong (F : L ⥤ D) [∀ x, HasLimit (Ran.diagram ι (ι ⋙ F) x)] : Prop where
  isoSelf : Nonempty (F ≅ Ran.self ι F)

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
def cocone {F : S ⥤ D} {G : L ⥤ D} (x : L) (f : F ⟶ ι ⋙ G) : Cocone (diagram ι F x)
    where
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
def loc (F : S ⥤ D) [I : ∀ x, HasColimit (diagram ι F x)] : L ⥤ D
    where
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
    (loc ι F ⟶ G) ≃ (F ⟶ ((whiskeringLeft _ _ _).obj ι).obj G)
    where
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
attribute [nolint simpNF] CategoryTheory.Ran.equiv_symm_apply_app
  CategoryTheory.Ran.equiv_apply_app
  CategoryTheory.Lan.equiv_symm_apply_app
  CategoryTheory.Lan.equiv_apply_app

end Lan

/-- The left Kan extension of a functor. -/
@[simps!]
def lan [∀ F : S ⥤ D, ∀ x, HasColimit (Lan.diagram ι F x)] : (S ⥤ D) ⥤ L ⥤ D :=
  Adjunction.leftAdjointOfEquiv (fun F G => Lan.equiv ι F G) (by {
    intros X' X Y f g
    ext
    simp [Lan.equiv]
    -- This used to be the end of the proof before leanprover/lean4#2644
    erw [Equiv.coe_fn_mk, Equiv.coe_fn_mk]
    simp })
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

theorem coreflective [Full ι] [Faithful ι] [∀ F : S ⥤ D, ∀ x, HasColimit (Lan.diagram ι F x)] :
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
    IsIso.of_iso
      ((colimit.isColimit _).coconePointUniqueUpToIso
          (colimitOfDiagramTerminal CostructuredArrow.mkIdTerminal _)).symm
set_option linter.uppercaseLean3 false in
#align category_theory.Lan.coreflective CategoryTheory.Lan.coreflective

variable {D}

abbrev self (F : L ⥤ D) [∀ x, HasColimit (Lan.diagram ι (ι ⋙ F) x)] : L ⥤ D :=
  Lan.loc ι (ι ⋙ F)

end Lan

class IsLeftKanExtendedAlong (F : L ⥤ D) [∀ x, HasColimit (Lan.diagram ι (ι ⋙ F) x)] : Prop where
  isoSelf : Nonempty (F ≅ Lan.self ι F)


end CategoryTheory
