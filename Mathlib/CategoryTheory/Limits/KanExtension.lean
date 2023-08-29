/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Adam Topaz
-/
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.PUnit
import Mathlib.CategoryTheory.StructuredArrow

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
        -- ⊢ ((Functor.const (StructuredArrow x ι)).obj (G.obj x)).map (CommaMorphism.mk  …
        dsimp at *
        -- ⊢ 𝟙 (G.obj x) ≫ G.map j ≫ NatTrans.app f jr = (G.map i ≫ NatTrans.app f ir) ≫  …
        dsimp at ff
        -- ⊢ 𝟙 (G.obj x) ≫ G.map j ≫ NatTrans.app f jr = (G.map i ≫ NatTrans.app f ir) ≫  …
        simp only [Category.id_comp, Category.assoc] at *
        -- ⊢ G.map j ≫ NatTrans.app f jr = G.map i ≫ NatTrans.app f ir ≫ F.map fr
        rw [ff]
        -- ⊢ G.map (i ≫ ι.map fr) ≫ NatTrans.app f jr = G.map i ≫ NatTrans.app f ir ≫ F.m …
        have := f.naturality
        -- ⊢ G.map (i ≫ ι.map fr) ≫ NatTrans.app f jr = G.map i ≫ NatTrans.app f ir ≫ F.m …
        aesop_cat }
        -- 🎉 no goals
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
    -- ⊢ { obj := fun x => limit (diagram ι F x), map := fun {X Y} f => limit.pre (di …
    haveI : HasLimit (StructuredArrow.map (𝟙 _) ⋙ diagram ι F l) := h _
    -- ⊢ { obj := fun x => limit (diagram ι F x), map := fun {X Y} f => limit.pre (di …
    dsimp
    -- ⊢ limit.pre (diagram ι F l) (StructuredArrow.map (𝟙 l)) = 𝟙 (limit (diagram ι  …
    ext j
    -- ⊢ limit.pre (diagram ι F l) (StructuredArrow.map (𝟙 l)) ≫ limit.π (StructuredA …
    simp only [Category.id_comp, limit.pre_π]
    -- ⊢ limit.π (diagram ι F l) ((StructuredArrow.map (𝟙 l)).obj j) = limit.π (Struc …
    congr 1
    -- ⊢ (StructuredArrow.map (𝟙 l)).obj j = j
    simp
    -- 🎉 no goals
  map_comp := by
    intro x y z f g
    -- ⊢ { obj := fun x => limit (diagram ι F x), map := fun {X Y} f => limit.pre (di …
    apply limit.hom_ext
    -- ⊢ ∀ (j : StructuredArrow z ι), { obj := fun x => limit (diagram ι F x), map := …
    intro j
    -- ⊢ { obj := fun x => limit (diagram ι F x), map := fun {X Y} f => limit.pre (di …
    -- Porting note: The fact that we need to add these instances all over the place
    -- is certainly not ideal.
    haveI : HasLimit (StructuredArrow.map f ⋙ diagram ι F _) := h _
    -- ⊢ { obj := fun x => limit (diagram ι F x), map := fun {X Y} f => limit.pre (di …
    haveI : HasLimit (StructuredArrow.map g ⋙ diagram ι F _) := h _
    -- ⊢ { obj := fun x => limit (diagram ι F x), map := fun {X Y} f => limit.pre (di …
    haveI : HasLimit (StructuredArrow.map (f ≫ g) ⋙ diagram ι F _) := h _
    -- ⊢ { obj := fun x => limit (diagram ι F x), map := fun {X Y} f => limit.pre (di …
    haveI : HasLimit (StructuredArrow.map g ⋙ StructuredArrow.map f ⋙ diagram ι F _) := h _
    -- ⊢ { obj := fun x => limit (diagram ι F x), map := fun {X Y} f => limit.pre (di …
    haveI : HasLimit ((StructuredArrow.map g ⋙ StructuredArrow.map f) ⋙ diagram ι F _) := h _
    -- ⊢ { obj := fun x => limit (diagram ι F x), map := fun {X Y} f => limit.pre (di …
    erw [limit.pre_pre, limit.pre_π, limit.pre_π]
    -- ⊢ limit.π (diagram ι F x) ((StructuredArrow.map (f ≫ g)).obj j) = limit.π (dia …
    congr 1
    -- ⊢ (StructuredArrow.map (f ≫ g)).obj j = (StructuredArrow.map g ⋙ StructuredArr …
    aesop_cat
    -- 🎉 no goals
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
        -- ⊢ (((whiskeringLeft S L D).obj ι).obj G).map ff ≫ (fun x => NatTrans.app f (ι. …
        dsimp only [whiskeringLeft]
        -- ⊢ (ι ⋙ G).map ff ≫ NatTrans.app f (ι.obj y) ≫ limit.π (diagram ι F (ι.obj y))  …
        simp only [Functor.comp_map, NatTrans.naturality_assoc, loc_map, Category.assoc]
        -- ⊢ NatTrans.app f (ι.obj x) ≫ limit.pre (diagram ι F (ι.obj x)) (StructuredArro …
        congr 1
        -- ⊢ limit.pre (diagram ι F (ι.obj x)) (StructuredArrow.map (ι.map ff)) ≫ limit.π …
        haveI : HasLimit (StructuredArrow.map (ι.map ff) ⋙ diagram ι F (ι.obj x)) := h _
        -- ⊢ limit.pre (diagram ι F (ι.obj x)) (StructuredArrow.map (ι.map ff)) ≫ limit.π …
        erw [limit.pre_π]
        -- ⊢ limit.π (diagram ι F (ι.obj x)) ((StructuredArrow.map (ι.map ff)).obj (Struc …
        let t : StructuredArrow.mk (𝟙 (ι.obj x)) ⟶
          (StructuredArrow.map (ι.map ff)).obj (StructuredArrow.mk (𝟙 (ι.obj y))) :=
          StructuredArrow.homMk ff ?_
        convert (limit.w (diagram ι F (ι.obj x)) t).symm using 1
        -- ⊢ (StructuredArrow.mk (𝟙 (ι.obj x))).hom ≫ ι.map ff = ((StructuredArrow.map (ι …
        simp }
        -- 🎉 no goals
  invFun f :=
    { app := fun x => limit.lift (diagram ι F x) (cone _ f)
      naturality := by
        intro x y ff
        -- ⊢ G.map ff ≫ (fun x => limit.lift (diagram ι F x) (cone x f)) y = (fun x => li …
        apply limit.hom_ext
        -- ⊢ ∀ (j : StructuredArrow y ι), (G.map ff ≫ (fun x => limit.lift (diagram ι F x …
        intros j
        -- ⊢ (G.map ff ≫ (fun x => limit.lift (diagram ι F x) (cone x f)) y) ≫ limit.π (d …
        haveI : HasLimit (StructuredArrow.map ff ⋙ diagram ι F x) := h _
        -- ⊢ (G.map ff ≫ (fun x => limit.lift (diagram ι F x) (cone x f)) y) ≫ limit.π (d …
        erw [limit.lift_pre, limit.lift_π, Category.assoc, limit.lift_π (cone _ f) j]
        -- ⊢ G.map ff ≫ NatTrans.app (cone y f).π j = NatTrans.app (Cone.whisker (Structu …
        simp }
        -- 🎉 no goals
  left_inv := by
    intro x
    -- ⊢ (fun f => NatTrans.mk fun x => limit.lift (diagram ι F x) (cone x f)) ((fun  …
    ext k
    -- ⊢ NatTrans.app ((fun f => NatTrans.mk fun x => limit.lift (diagram ι F x) (con …
    apply limit.hom_ext
    -- ⊢ ∀ (j : StructuredArrow k ι), NatTrans.app ((fun f => NatTrans.mk fun x => li …
    intros j
    -- ⊢ NatTrans.app ((fun f => NatTrans.mk fun x => limit.lift (diagram ι F x) (con …
    dsimp only [cone]
    -- ⊢ limit.lift (diagram ι F k) { pt := G.obj k, π := NatTrans.mk fun i => G.map  …
    rw [limit.lift_π]
    -- ⊢ NatTrans.app { pt := G.obj k, π := NatTrans.mk fun i => G.map i.hom ≫ NatTra …
    simp only [NatTrans.naturality_assoc, loc_map]
    -- ⊢ NatTrans.app x k ≫ limit.pre (diagram ι F k) (StructuredArrow.map j.hom) ≫ l …
    haveI : HasLimit (StructuredArrow.map j.hom ⋙ diagram ι F k) := h _
    -- ⊢ NatTrans.app x k ≫ limit.pre (diagram ι F k) (StructuredArrow.map j.hom) ≫ l …
    erw [limit.pre_π]
    -- ⊢ NatTrans.app x k ≫ limit.π (diagram ι F k) ((StructuredArrow.map j.hom).obj  …
    congr
    -- ⊢ (StructuredArrow.map j.hom).obj (StructuredArrow.mk (𝟙 (ι.obj j.right))) = j
    rcases j with ⟨⟨⟩, _, _⟩
    -- ⊢ (StructuredArrow.map { left := { as := as✝ }, right := right✝, hom := hom✝ } …
    aesop_cat
    -- 🎉 no goals
  right_inv := by aesop_cat
                  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align category_theory.Ran.equiv CategoryTheory.Ran.equiv

end Ran

/-- The right Kan extension of a functor. -/
@[simps!]
def ran [∀ X, HasLimitsOfShape (StructuredArrow X ι) D] : (S ⥤ D) ⥤ L ⥤ D :=
  Adjunction.rightAdjointOfEquiv (fun F G => (Ran.equiv ι G F).symm) (by {
    -- Porting note: was `tidy`
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
  suffices : ∀ (X : S ⥤ D), IsIso (NatTrans.app (adjunction D ι).counit X)
  -- ⊢ IsIso (adjunction D ι).counit
  · apply NatIso.isIso_of_isIso_app
    -- 🎉 no goals
  intro F
  -- ⊢ IsIso (NatTrans.app (adjunction D ι).counit F)
  suffices : ∀ (X : S), IsIso (NatTrans.app (NatTrans.app (adjunction D ι).counit F) X)
  -- ⊢ IsIso (NatTrans.app (adjunction D ι).counit F)
  · apply NatIso.isIso_of_isIso_app
    -- 🎉 no goals
  intro X
  -- ⊢ IsIso (NatTrans.app (NatTrans.app (adjunction D ι).counit F) X)
  dsimp [adjunction, equiv]
  -- ⊢ IsIso (𝟙 (limit (diagram ι F (ι.obj X))) ≫ limit.π (diagram ι F (ι.obj X)) ( …
  simp only [Category.id_comp]
  -- ⊢ IsIso (limit.π (diagram ι F (ι.obj X)) (StructuredArrow.mk (𝟙 (ι.obj X))))
  exact
    IsIso.of_iso
      ((limit.isLimit _).conePointUniqueUpToIso
        (limitOfDiagramInitial StructuredArrow.mkIdInitial _))
set_option linter.uppercaseLean3 false in
#align category_theory.Ran.reflective CategoryTheory.Ran.reflective

end Ran

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
        -- ⊢ (diagram ι F x).map (CommaMorphism.mk fl✝ { down := { down := fl } }) ≫ (fun …
        dsimp at *
        -- ⊢ F.map fl✝ ≫ NatTrans.app f jl ≫ G.map j = (NatTrans.app f ir ≫ G.map i) ≫ 𝟙  …
        simp only [Functor.comp_map, Category.comp_id, NatTrans.naturality_assoc]
        -- ⊢ NatTrans.app f ir ≫ G.map (ι.map fl✝) ≫ G.map j = NatTrans.app f ir ≫ G.map i
        rw [← G.map_comp, ff]
        -- ⊢ NatTrans.app f ir ≫ G.map ({ left := ir, right := { as := il }, hom := i }.h …
        aesop_cat }
        -- 🎉 no goals
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
    -- ⊢ { obj := fun x => colimit (diagram ι F x), map := fun {x y} f => colimit.pre …
    dsimp
    -- ⊢ colimit.pre (diagram ι F l) (CostructuredArrow.map (𝟙 l)) = 𝟙 (colimit (diag …
    haveI : HasColimit (CostructuredArrow.map (𝟙 l) ⋙ diagram ι F l) := I _
    -- ⊢ colimit.pre (diagram ι F l) (CostructuredArrow.map (𝟙 l)) = 𝟙 (colimit (diag …
    ext j
    -- ⊢ colimit.ι (CostructuredArrow.map (𝟙 l) ⋙ diagram ι F l) j ≫ colimit.pre (dia …
    erw [colimit.ι_pre, Category.comp_id]
    -- ⊢ colimit.ι (diagram ι F l) ((CostructuredArrow.map (𝟙 l)).obj j) = colimit.ι  …
    congr 1
    -- ⊢ (CostructuredArrow.map (𝟙 l)).obj j = j
    simp
    -- 🎉 no goals
  map_comp := by
    intro x y z f g
    -- ⊢ { obj := fun x => colimit (diagram ι F x), map := fun {x y} f => colimit.pre …
    dsimp
    -- ⊢ colimit.pre (diagram ι F z) (CostructuredArrow.map (f ≫ g)) = colimit.pre (d …
    haveI : HasColimit (CostructuredArrow.map (f ≫ g) ⋙ diagram ι F z) := I _
    -- ⊢ colimit.pre (diagram ι F z) (CostructuredArrow.map (f ≫ g)) = colimit.pre (d …
    ext j
    -- ⊢ colimit.ι (CostructuredArrow.map (f ≫ g) ⋙ diagram ι F z) j ≫ colimit.pre (d …
    let ff : CostructuredArrow ι _ ⥤ _ := CostructuredArrow.map f
    -- ⊢ colimit.ι (CostructuredArrow.map (f ≫ g) ⋙ diagram ι F z) j ≫ colimit.pre (d …
    let gg : CostructuredArrow ι _ ⥤ _ := CostructuredArrow.map g
    -- ⊢ colimit.ι (CostructuredArrow.map (f ≫ g) ⋙ diagram ι F z) j ≫ colimit.pre (d …
    let dd := diagram ι F z
    -- ⊢ colimit.ι (CostructuredArrow.map (f ≫ g) ⋙ diagram ι F z) j ≫ colimit.pre (d …
    -- Porting note: It seems that even Lean3 had some trouble with instances in this case.
    -- I don't know why lean can't deduce the following three instances...
    haveI : HasColimit (ff ⋙ gg ⋙ dd) := I _
    -- ⊢ colimit.ι (CostructuredArrow.map (f ≫ g) ⋙ diagram ι F z) j ≫ colimit.pre (d …
    haveI : HasColimit ((ff ⋙ gg) ⋙ dd) := I _
    -- ⊢ colimit.ι (CostructuredArrow.map (f ≫ g) ⋙ diagram ι F z) j ≫ colimit.pre (d …
    haveI : HasColimit (gg ⋙ dd) := I _
    -- ⊢ colimit.ι (CostructuredArrow.map (f ≫ g) ⋙ diagram ι F z) j ≫ colimit.pre (d …
    change _ = colimit.ι ((ff ⋙ gg) ⋙ dd) j ≫ _ ≫ _
    -- ⊢ colimit.ι (CostructuredArrow.map (f ≫ g) ⋙ diagram ι F z) j ≫ colimit.pre (d …
    erw [colimit.pre_pre dd gg ff, colimit.ι_pre, colimit.ι_pre]
    -- ⊢ colimit.ι (diagram ι F z) ((CostructuredArrow.map (f ≫ g)).obj j) = colimit. …
    congr 1
    -- ⊢ (CostructuredArrow.map (f ≫ g)).obj j = (ff ⋙ gg).obj j
    simp
    -- 🎉 no goals
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
        -- ⊢ F.map ff ≫ (fun x => colimit.ι (diagram ι F (ι.obj x)) (CostructuredArrow.mk …
        dsimp only [whiskeringLeft]
        -- ⊢ F.map ff ≫ colimit.ι (diagram ι F (ι.obj y)) (CostructuredArrow.mk (𝟙 (ι.obj …
        simp only [Functor.comp_map, Category.assoc]
        -- ⊢ F.map ff ≫ colimit.ι (diagram ι F (ι.obj y)) (CostructuredArrow.mk (𝟙 (ι.obj …
        rw [← f.naturality (ι.map ff), ← Category.assoc, ← Category.assoc]
        -- ⊢ (F.map ff ≫ colimit.ι (diagram ι F (ι.obj y)) (CostructuredArrow.mk (𝟙 (ι.ob …
        let fff : CostructuredArrow ι _ ⥤ _ := CostructuredArrow.map (ι.map ff)
        -- ⊢ (F.map ff ≫ colimit.ι (diagram ι F (ι.obj y)) (CostructuredArrow.mk (𝟙 (ι.ob …
        -- same issue :-(
        haveI : HasColimit (fff ⋙ diagram ι F (ι.obj y)) := I _
        -- ⊢ (F.map ff ≫ colimit.ι (diagram ι F (ι.obj y)) (CostructuredArrow.mk (𝟙 (ι.ob …
        erw [colimit.ι_pre (diagram ι F (ι.obj y)) fff (CostructuredArrow.mk (𝟙 _))]
        -- ⊢ (F.map ff ≫ colimit.ι (diagram ι F (ι.obj y)) (CostructuredArrow.mk (𝟙 (ι.ob …
        let xx : CostructuredArrow ι (ι.obj y) := CostructuredArrow.mk (ι.map ff)
        -- ⊢ (F.map ff ≫ colimit.ι (diagram ι F (ι.obj y)) (CostructuredArrow.mk (𝟙 (ι.ob …
        let yy : CostructuredArrow ι (ι.obj y) := CostructuredArrow.mk (𝟙 _)
        -- ⊢ (F.map ff ≫ colimit.ι (diagram ι F (ι.obj y)) (CostructuredArrow.mk (𝟙 (ι.ob …
        let fff : xx ⟶ yy :=
          CostructuredArrow.homMk ff
            (by
              simp only [CostructuredArrow.mk_hom_eq_self]
              erw [Category.comp_id])
        erw [colimit.w (diagram ι F (ι.obj y)) fff]
        -- ⊢ colimit.ι (diagram ι F (ι.obj y)) xx ≫ NatTrans.app f (ι.obj y) = colimit.ι  …
        congr
        -- ⊢ xx = fff✝.obj (CostructuredArrow.mk (𝟙 (ι.obj x)))
        simp }
        -- 🎉 no goals
  invFun f :=
    { app := fun x => colimit.desc (diagram ι F x) (cocone _ f)
      naturality := by
        intro x y ff
        -- ⊢ (loc ι F).map ff ≫ (fun x => colimit.desc (diagram ι F x) (cocone x f)) y =  …
        apply colimit.hom_ext
        -- ⊢ ∀ (j : CostructuredArrow ι x), colimit.ι (diagram ι F x) j ≫ (loc ι F).map f …
        intros j
        -- ⊢ colimit.ι (diagram ι F x) j ≫ (loc ι F).map ff ≫ (fun x => colimit.desc (dia …
        haveI : HasColimit (CostructuredArrow.map ff ⋙ diagram ι F y) := I _
        -- ⊢ colimit.ι (diagram ι F x) j ≫ (loc ι F).map ff ≫ (fun x => colimit.desc (dia …
        erw [colimit.pre_desc, ← Category.assoc, colimit.ι_desc, colimit.ι_desc]
        -- ⊢ NatTrans.app (Cocone.whisker (CostructuredArrow.map ff) (cocone y f)).ι j =  …
        simp }
        -- 🎉 no goals
  left_inv := by
    intros x
    -- ⊢ (fun f => NatTrans.mk fun x => colimit.desc (diagram ι F x) (cocone x f)) (( …
    dsimp
    -- ⊢ (NatTrans.mk fun x_1 => colimit.desc (diagram ι F x_1) { pt := G.obj x_1, ι  …
    ext k
    -- ⊢ NatTrans.app (NatTrans.mk fun x_1 => colimit.desc (diagram ι F x_1) { pt :=  …
    dsimp
    -- ⊢ colimit.desc (diagram ι F k) { pt := G.obj k, ι := NatTrans.mk fun i => (col …
    apply colimit.hom_ext
    -- ⊢ ∀ (j : CostructuredArrow ι k), colimit.ι (diagram ι F k) j ≫ colimit.desc (d …
    intros j
    -- ⊢ colimit.ι (diagram ι F k) j ≫ colimit.desc (diagram ι F k) { pt := G.obj k,  …
    rw [colimit.ι_desc]
    -- ⊢ NatTrans.app { pt := G.obj k, ι := NatTrans.mk fun i => (colimit.ι (diagram  …
    dsimp only [cocone]
    -- ⊢ (colimit.ι (diagram ι F (ι.obj j.left)) (CostructuredArrow.mk (𝟙 (ι.obj j.le …
    rw [Category.assoc, ← x.naturality j.hom, ← Category.assoc]
    -- ⊢ (colimit.ι (diagram ι F (ι.obj j.left)) (CostructuredArrow.mk (𝟙 (ι.obj j.le …
    congr 1
    -- ⊢ colimit.ι (diagram ι F (ι.obj j.left)) (CostructuredArrow.mk (𝟙 (ι.obj j.lef …
    dsimp [loc]
    -- ⊢ colimit.ι (diagram ι F (ι.obj j.left)) (CostructuredArrow.mk (𝟙 (ι.obj j.lef …
    haveI : HasColimit (CostructuredArrow.map j.hom ⋙ diagram ι F k) := I _
    -- ⊢ colimit.ι (diagram ι F (ι.obj j.left)) (CostructuredArrow.mk (𝟙 (ι.obj j.lef …
    erw [colimit.ι_pre (diagram ι F k) (CostructuredArrow.map j.hom)]
    -- ⊢ colimit.ι (diagram ι F k) ((CostructuredArrow.map j.hom).obj (CostructuredAr …
    congr
    -- ⊢ (CostructuredArrow.map j.hom).obj (CostructuredArrow.mk (𝟙 (ι.obj j.left)))  …
    rcases j with ⟨_, ⟨⟩, _⟩
    -- ⊢ (CostructuredArrow.map { left := left✝, right := { as := as✝ }, hom := hom✝  …
    simp only [CostructuredArrow.map_mk, Category.id_comp]
    -- ⊢ CostructuredArrow.mk hom✝ = { left := left✝, right := { as := as✝ }, hom :=  …
    rfl
    -- 🎉 no goals
  right_inv := by aesop_cat
                  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align category_theory.Lan.equiv CategoryTheory.Lan.equiv

end Lan

/-- The left Kan extension of a functor. -/
@[simps!]
def lan [∀ X, HasColimitsOfShape (CostructuredArrow ι X) D] : (S ⥤ D) ⥤ L ⥤ D :=
  Adjunction.leftAdjointOfEquiv (fun F G => Lan.equiv ι F G) (by {
    intros X' X Y f g
    ext
    simp [Lan.equiv] })
set_option linter.uppercaseLean3 false in
#align category_theory.Lan CategoryTheory.lan

namespace Lan

variable (D)

/-- The adjunction associated to `Lan`. -/
def adjunction [∀ X, HasColimitsOfShape (CostructuredArrow ι X) D] :
    lan ι ⊣ (whiskeringLeft _ _ D).obj ι :=
  Adjunction.adjunctionOfEquivLeft _ _
set_option linter.uppercaseLean3 false in
#align category_theory.Lan.adjunction CategoryTheory.Lan.adjunction

theorem coreflective [Full ι] [Faithful ι] [∀ X, HasColimitsOfShape (CostructuredArrow ι X) D] :
    IsIso (adjunction D ι).unit := by
  suffices : ∀ (X : S ⥤ D), IsIso (NatTrans.app (adjunction D ι).unit X)
  -- ⊢ IsIso (adjunction D ι).unit
  · apply NatIso.isIso_of_isIso_app
    -- 🎉 no goals
  intro F
  -- ⊢ IsIso (NatTrans.app (adjunction D ι).unit F)
  suffices : ∀ (X : S), IsIso (NatTrans.app (NatTrans.app (adjunction D ι).unit F) X)
  -- ⊢ IsIso (NatTrans.app (adjunction D ι).unit F)
  · apply NatIso.isIso_of_isIso_app
    -- 🎉 no goals
  intro X
  -- ⊢ IsIso (NatTrans.app (NatTrans.app (adjunction D ι).unit F) X)
  dsimp [adjunction, equiv]
  -- ⊢ IsIso (colimit.ι (diagram ι F (ι.obj X)) (CostructuredArrow.mk (𝟙 (ι.obj X)) …
  simp only [Category.comp_id]
  -- ⊢ IsIso (colimit.ι (diagram ι F (ι.obj X)) (CostructuredArrow.mk (𝟙 (ι.obj X))))
  exact
    IsIso.of_iso
      ((colimit.isColimit _).coconePointUniqueUpToIso
          (colimitOfDiagramTerminal CostructuredArrow.mkIdTerminal _)).symm
set_option linter.uppercaseLean3 false in
#align category_theory.Lan.coreflective CategoryTheory.Lan.coreflective

end Lan

end CategoryTheory
