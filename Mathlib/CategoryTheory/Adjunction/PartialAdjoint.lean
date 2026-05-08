/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Yoneda

/-!
# Domain of definition of the partial left adjoint

Given a functor `F : D ⥤ C`, we define a functor
`F.partialLeftAdjoint : F.PartialLeftAdjointSource ⥤ D` which is
defined on the full subcategory of `C` consisting of those objects `X : C`
such that `F ⋙ coyoneda.obj (op X) : D ⥤ Type _` is corepresentable.
For `X : F.PartialLeftAdjointSource` and `Y : D`, we have a natural bijection
`(F.partialLeftAdjoint.obj X ⟶ Y) ≃ (X.obj ⟶ F.obj Y)`
that is similar to what we would expect for the image of the object `X`
by the left adjoint of `F`, if such an adjoint existed.

Indeed, if the predicate `F.leftAdjointObjIsDefined` which defines
the `F.PartialLeftAdjointSource` holds for all
objects `X : C`, then `F` has a left adjoint.

When colimits indexed by a category `J` exist in `D`, we show that
the predicate `F.leftAdjointObjIsDefined` is stable under colimits indexed by `J`.

## TODO
* consider dualizing the results to right adjoints

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Functor

open Category Opposite Limits

section partialLeftAdjoint

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : D ⥤ C)

/-- Given a functor `F : D ⥤ C`, this is a predicate on objects `X : C` corresponding
to the domain of definition of the (partial) left adjoint of `F`. -/
def leftAdjointObjIsDefined : ObjectProperty C :=
  fun X ↦ IsCorepresentable (F ⋙ coyoneda.obj (op X))

lemma leftAdjointObjIsDefined_iff (X : C) :
    F.leftAdjointObjIsDefined X ↔ IsCorepresentable (F ⋙ coyoneda.obj (op X)) := by rfl

variable {F} in
lemma leftAdjointObjIsDefined_of_adjunction {G : C ⥤ D} (adj : G ⊣ F) (X : C) :
    F.leftAdjointObjIsDefined X :=
  (adj.corepresentableBy X).isCorepresentable

/-- The full subcategory where `F.partialLeftAdjoint` shall be defined. -/
abbrev PartialLeftAdjointSource := F.leftAdjointObjIsDefined.FullSubcategory

instance (X : F.PartialLeftAdjointSource) :
    IsCorepresentable (F ⋙ coyoneda.obj (op X.obj)) := X.property

/-- Given `F : D ⥤ C`, this is `F.partialLeftAdjoint` on objects: it sends
`X : C` such that `F.leftAdjointObjIsDefined X` holds to an object of `D`
which represents the functor `F ⋙ coyoneda.obj (op X.obj)`. -/
noncomputable def partialLeftAdjointObj (X : F.PartialLeftAdjointSource) : D :=
  (F ⋙ coyoneda.obj (op X.obj)).coreprX

/-- Given `F : D ⥤ C`, this is the canonical bijection
`(F.partialLeftAdjointObj X ⟶ Y) ≃ (X.obj ⟶ F.obj Y)`
for all `X : F.PartialLeftAdjointSource` and `Y : D`. -/
noncomputable def partialLeftAdjointHomEquiv {X : F.PartialLeftAdjointSource} {Y : D} :
    (F.partialLeftAdjointObj X ⟶ Y) ≃ (X.obj ⟶ F.obj Y) :=
  (F ⋙ coyoneda.obj (op X.obj)).corepresentableBy.homEquiv

lemma partialLeftAdjointHomEquiv_comp {X : F.PartialLeftAdjointSource} {Y Y' : D}
    (f : F.partialLeftAdjointObj X ⟶ Y) (g : Y ⟶ Y') :
    F.partialLeftAdjointHomEquiv (f ≫ g) =
      F.partialLeftAdjointHomEquiv f ≫ F.map g := by
  apply CorepresentableBy.homEquiv_comp

/-- Given `F : D ⥤ C`, this is `F.partialLeftAdjoint` on morphisms. -/
noncomputable def partialLeftAdjointMap {X Y : F.PartialLeftAdjointSource}
    (f : X ⟶ Y) : F.partialLeftAdjointObj X ⟶ F.partialLeftAdjointObj Y :=
    F.partialLeftAdjointHomEquiv.symm (f.hom ≫ F.partialLeftAdjointHomEquiv (𝟙 _))

@[simp]
lemma partialLeftAdjointHomEquiv_map {X Y : F.PartialLeftAdjointSource}
    (f : X ⟶ Y) :
    F.partialLeftAdjointHomEquiv (F.partialLeftAdjointMap f) =
      f.hom ≫ F.partialLeftAdjointHomEquiv (𝟙 _) := by
  simp [partialLeftAdjointMap]

lemma partialLeftAdjointHomEquiv_map_comp {X X' : F.PartialLeftAdjointSource} {Y : D}
    (f : X ⟶ X') (g : F.partialLeftAdjointObj X' ⟶ Y) :
    F.partialLeftAdjointHomEquiv (F.partialLeftAdjointMap f ≫ g) =
      f.hom ≫ F.partialLeftAdjointHomEquiv g := by
  rw [partialLeftAdjointHomEquiv_comp, partialLeftAdjointHomEquiv_map, assoc,
    ← partialLeftAdjointHomEquiv_comp, id_comp]

@[reassoc]
lemma partialLeftAdjointHomEquiv_symm_comp {X : F.PartialLeftAdjointSource} {Y Y' : D}
    (f : X.obj ⟶ F.obj Y) (g : Y ⟶ Y') :
    F.partialLeftAdjointHomEquiv.symm f ≫ g = F.partialLeftAdjointHomEquiv.symm (f ≫ F.map g) :=
  CorepresentableBy.homEquiv_symm_comp ..

@[reassoc]
lemma partialLeftAdjointHomEquiv_comp_symm {X X' : F.PartialLeftAdjointSource} {Y : D}
    (f : X'.obj ⟶ F.obj Y) (g : X ⟶ X') :
    F.partialLeftAdjointMap g ≫ F.partialLeftAdjointHomEquiv.symm f =
    F.partialLeftAdjointHomEquiv.symm (g.hom ≫ f) := by
  rw [Equiv.eq_symm_apply, partialLeftAdjointHomEquiv_comp, partialLeftAdjointHomEquiv_map,
    assoc, ← partialLeftAdjointHomEquiv_comp, id_comp, Equiv.apply_symm_apply]

/-- Given `F : D ⥤ C`, this is the partial adjoint functor `F.PartialLeftAdjointSource ⥤ D`. -/
@[simps]
noncomputable def partialLeftAdjoint : F.PartialLeftAdjointSource ⥤ D where
  obj := F.partialLeftAdjointObj
  map := F.partialLeftAdjointMap
  map_id X := by
    apply F.partialLeftAdjointHomEquiv.injective
    simp [partialLeftAdjointHomEquiv_map]
  map_comp {X Y Z} f g := by
    apply F.partialLeftAdjointHomEquiv.injective
    simp [partialLeftAdjointHomEquiv_comp, ← F.partialLeftAdjointHomEquiv_comp]

variable {F}

lemma isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
    (h : F.leftAdjointObjIsDefined = ⊤) : F.IsRightAdjoint := by
  replace h : ∀ X, IsCorepresentable (F ⋙ coyoneda.obj (op X)) := fun X ↦ by
    simp only [← leftAdjointObjIsDefined_iff, h, Pi.top_apply, Prop.top_eq_true]
  exact (Adjunction.adjunctionOfEquivLeft
    (fun X Y ↦ (F ⋙ coyoneda.obj (op X)).corepresentableBy.homEquiv)
    (fun X Y Y' g f ↦ by apply CorepresentableBy.homEquiv_comp)).isRightAdjoint

variable (F) in
lemma isRightAdjoint_iff_leftAdjointObjIsDefined_eq_top :
    F.IsRightAdjoint ↔ F.leftAdjointObjIsDefined = ⊤ := by
  refine ⟨fun h ↦ ?_, isRightAdjoint_of_leftAdjointObjIsDefined_eq_top⟩
  ext X
  simpa only [Pi.top_apply, Prop.top_eq_true, iff_true]
    using leftAdjointObjIsDefined_of_adjunction (Adjunction.ofIsRightAdjoint F) X

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `leftAdjointObjIsDefined_of_isColimit`. -/
noncomputable def corepresentableByCompCoyonedaObjOfIsColimit {J : Type*} [Category* J]
    {R : J ⥤ F.PartialLeftAdjointSource}
    {c : Cocone (R ⋙ ObjectProperty.ι _)} (hc : IsColimit c)
    {c' : Cocone (R ⋙ F.partialLeftAdjoint)} (hc' : IsColimit c') :
    (F ⋙ coyoneda.obj (op c.pt)).CorepresentableBy c'.pt where
  homEquiv {Y} :=
    { toFun := fun f ↦ hc.desc (Cocone.mk _
        { app := fun j ↦ F.partialLeftAdjointHomEquiv (c'.ι.app j ≫ f)
          naturality := fun j j' φ ↦ by
            dsimp
            rw [comp_id, ← c'.w φ, ← partialLeftAdjointHomEquiv_map_comp, assoc]
            dsimp })
      invFun := fun g ↦ hc'.desc (Cocone.mk _
        { app := fun j ↦ F.partialLeftAdjointHomEquiv.symm (c.ι.app j ≫ g)
          naturality := fun j j' φ ↦ by
            apply F.partialLeftAdjointHomEquiv.injective
            have := c.w φ
            dsimp at this ⊢
            rw [comp_id, Equiv.apply_symm_apply, partialLeftAdjointHomEquiv_map_comp,
              Equiv.apply_symm_apply, reassoc_of% this] })
      left_inv := fun f ↦ hc'.hom_ext (fun j ↦ by simp)
      right_inv := fun g ↦ hc.hom_ext (fun j ↦ by simp) }
  homEquiv_comp {Y Y'} g f := hc.hom_ext (fun j ↦ by
    dsimp
    simp only [IsColimit.fac, IsColimit.fac_assoc, partialLeftAdjointHomEquiv_comp,
      F.map_comp, assoc])

lemma leftAdjointObjIsDefined_of_isColimit {J : Type*} [Category* J] {R : J ⥤ C} {c : Cocone R}
    (hc : IsColimit c) [HasColimitsOfShape J D]
    (h : ∀ (j : J), F.leftAdjointObjIsDefined (R.obj j)) :
    F.leftAdjointObjIsDefined c.pt :=
  (corepresentableByCompCoyonedaObjOfIsColimit
    (R := ObjectProperty.lift _ R h) hc (colimit.isColimit _)).isCorepresentable

lemma leftAdjointObjIsDefined_colimit {J : Type*} [Category* J] (R : J ⥤ C)
    [HasColimit R] [HasColimitsOfShape J D]
    (h : ∀ (j : J), F.leftAdjointObjIsDefined (R.obj j)) :
    F.leftAdjointObjIsDefined (colimit R) :=
  leftAdjointObjIsDefined_of_isColimit (colimit.isColimit R) h

end partialLeftAdjoint

section partialRightAdjoint

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)

/-- Given a functor `F : C ⥤ D`, this is a predicate on objects `X : D` corresponding
to the domain of definition of the (partial) right adjoint of `F`. -/
def rightAdjointObjIsDefined : ObjectProperty D :=
  fun Y ↦ IsRepresentable (F.op ⋙ yoneda.obj Y)

lemma rightAdjointObjIsDefined_iff (Y : D) :
    F.rightAdjointObjIsDefined Y ↔ IsRepresentable (F.op ⋙ yoneda.obj Y) := by rfl

variable {F} in
lemma rightAdjointObjIsDefined_of_adjunction {G : D ⥤ C} (adj : F ⊣ G) (Y : D) :
    F.rightAdjointObjIsDefined Y :=
  (adj.representableBy Y).isRepresentable

/-- The full subcategory where `F.partialRightAdjoint` shall be defined. -/
abbrev PartialRightAdjointSource := F.rightAdjointObjIsDefined.FullSubcategory

instance (Y : F.PartialRightAdjointSource) :
    IsRepresentable (F.op ⋙ yoneda.obj Y.obj) := Y.property

/-- Given `F : C ⥤ D`, this is `F.partialRightAdjoint` on objects: it sends
`X : D` such that `F.rightAdjointObjIsDefined X` holds to an object of `C`
which represents the functor `F.op ⋙ yoneda.obj X.obj`. -/
noncomputable def partialRightAdjointObj (Y : F.PartialRightAdjointSource) : C :=
  (F.op ⋙ yoneda.obj Y.obj).reprX

/-- Given `F : C ⥤ D`, this is the canonical bijection
`(X ⟶ F.partialRightAdjointObj Y) ≃ (F.obj X ⟶ Y.obj)`
for all `X : C` and `Y : F.PartialRightAdjointSource`. -/
noncomputable def partialRightAdjointHomEquiv {X : C} {Y : F.PartialRightAdjointSource} :
    (X ⟶ F.partialRightAdjointObj Y) ≃ (F.obj X ⟶ Y.obj) :=
  (F.op ⋙ yoneda.obj Y.obj).representableBy.homEquiv

lemma partialRightAdjointHomEquiv_comp {X X' : C} {Y : F.PartialRightAdjointSource}
    (f : X' ⟶ F.partialRightAdjointObj Y) (g : X ⟶ X') :
    F.partialRightAdjointHomEquiv (g ≫ f) =
      F.map g ≫ F.partialRightAdjointHomEquiv f :=
  RepresentableBy.homEquiv_comp ..

/-- Given `F : C ⥤ D`, this is `F.partialRightAdjoint` on morphisms. -/
noncomputable def partialRightAdjointMap {X Y : F.PartialRightAdjointSource}
    (f : X ⟶ Y) : F.partialRightAdjointObj X ⟶ F.partialRightAdjointObj Y :=
    F.partialRightAdjointHomEquiv.symm (F.partialRightAdjointHomEquiv (𝟙 _) ≫ f.hom)

@[simp]
lemma partialRightAdjointHomEquiv_map {X Y : F.PartialRightAdjointSource}
    (f : X ⟶ Y) :
    F.partialRightAdjointHomEquiv (F.partialRightAdjointMap f) =
      F.partialRightAdjointHomEquiv (𝟙 _) ≫ f.hom := by
  simp [partialRightAdjointMap]

lemma partialRightAdjointHomEquiv_map_comp {X : C} {Y Y' : F.PartialRightAdjointSource}
    (f : X ⟶ F.partialRightAdjointObj Y) (g : Y ⟶ Y') :
    F.partialRightAdjointHomEquiv (f ≫ F.partialRightAdjointMap g) =
      F.partialRightAdjointHomEquiv f ≫ g.hom := by
  rw [partialRightAdjointHomEquiv_comp, partialRightAdjointHomEquiv_map,
    ← assoc, ← partialRightAdjointHomEquiv_comp, comp_id]

@[reassoc]
lemma partialRightAdjointHomEquiv_comp_symm {X X' : C} {Y : F.PartialRightAdjointSource}
    (f : F.obj X' ⟶ Y.obj) (g : X ⟶ X') :
    g ≫ F.partialRightAdjointHomEquiv.symm f =
      F.partialRightAdjointHomEquiv.symm (F.map g ≫ f) :=
  RepresentableBy.comp_homEquiv_symm ..

@[reassoc]
lemma partialRightAdjointHomEquiv_symm_comp {X : C} {Y Y' : F.PartialRightAdjointSource}
    (f : F.obj X ⟶ Y.obj) (g : Y ⟶ Y') :
    F.partialRightAdjointHomEquiv.symm f ≫ F.partialRightAdjointMap g =
      F.partialRightAdjointHomEquiv.symm (f ≫ g.hom) := by
  simp [Equiv.eq_symm_apply, partialRightAdjointHomEquiv_map_comp]

/-- Given `F : C ⥤ D`, this is the partial adjoint functor `F.PartialRightAdjointSource ⥤ C`. -/
@[simps]
noncomputable def partialRightAdjoint : F.PartialRightAdjointSource ⥤ C where
  obj := F.partialRightAdjointObj
  map := F.partialRightAdjointMap
  map_id X := by
    apply F.partialRightAdjointHomEquiv.injective
    simp [partialRightAdjointHomEquiv_map]
  map_comp {X Y Z} f g := by
    apply F.partialRightAdjointHomEquiv.injective
    simp [partialRightAdjointHomEquiv_comp, ← assoc, ← F.partialRightAdjointHomEquiv_comp]

variable {F}

lemma isLeftAdjoint_of_rightAdjointObjIsDefined_eq_top
    (h : F.rightAdjointObjIsDefined = ⊤) : F.IsLeftAdjoint := by
  replace h : ∀ X, IsRepresentable (F.op ⋙ yoneda.obj X) := fun X ↦ by
    simp only [← rightAdjointObjIsDefined_iff, h, Pi.top_apply, Prop.top_eq_true]
  exact (Adjunction.adjunctionOfEquivRight
    (fun X Y ↦ (F.op ⋙ yoneda.obj Y).representableBy.homEquiv.symm)
    (fun X Y Y' g f ↦ (RepresentableBy.comp_homEquiv_symm ..).symm)).isLeftAdjoint

variable (F) in
lemma isLeftAdjoint_iff_rightAdjointObjIsDefined_eq_top :
    F.IsLeftAdjoint ↔ F.rightAdjointObjIsDefined = ⊤ := by
  refine ⟨fun h ↦ ?_, isLeftAdjoint_of_rightAdjointObjIsDefined_eq_top⟩
  ext X
  simpa only [Pi.top_apply, Prop.top_eq_true, iff_true]
    using rightAdjointObjIsDefined_of_adjunction (Adjunction.ofIsLeftAdjoint F) X

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `rightAdjointObjIsDefined_of_isLimit`. -/
noncomputable def representableByCompYonedaObjOfIsLimit {J : Type*} [Category* J]
    {R : J ⥤ F.PartialRightAdjointSource}
    {c : Cone (R ⋙ ObjectProperty.ι _)} (hc : IsLimit c)
    {c' : Cone (R ⋙ F.partialRightAdjoint)} (hc' : IsLimit c') :
    (F.op ⋙ yoneda.obj c.pt).RepresentableBy c'.pt where
  homEquiv {Y} :=
    { toFun := fun f ↦ hc.lift (Cone.mk _
        { app := fun j ↦ F.partialRightAdjointHomEquiv (f ≫ c'.π.app j)
          naturality := fun j j' φ ↦ by
            dsimp
            rw [id_comp, ← c'.w φ, ← partialRightAdjointHomEquiv_map_comp,
              ← assoc]
            dsimp })
      invFun := fun g ↦ hc'.lift (Cone.mk _
        { app := fun j ↦ F.partialRightAdjointHomEquiv.symm (g ≫ c.π.app j)
          naturality := fun j j' φ ↦ by
            apply F.partialRightAdjointHomEquiv.injective
            have := c.w φ
            dsimp at this ⊢
            rw [id_comp, Equiv.apply_symm_apply, partialRightAdjointHomEquiv_map_comp,
              Equiv.apply_symm_apply, assoc, this] })
      left_inv := fun f ↦ hc'.hom_ext (fun j ↦ by simp)
      right_inv := fun g ↦ hc.hom_ext (fun j ↦ by simp) }
  homEquiv_comp {Y Y'} g f := hc.hom_ext (fun j ↦ by
    dsimp
    simp only [IsLimit.fac, partialRightAdjointHomEquiv_comp, assoc])

lemma rightAdjointObjIsDefined_of_isLimit {J : Type*} [Category* J] {R : J ⥤ D} {c : Cone R}
    (hc : IsLimit c) [HasLimitsOfShape J C]
    (h : ∀ (j : J), F.rightAdjointObjIsDefined (R.obj j)) :
    F.rightAdjointObjIsDefined c.pt :=
  (representableByCompYonedaObjOfIsLimit
    (R := ObjectProperty.lift _ R h) hc (limit.isLimit _)).isRepresentable

lemma rightAdjointObjIsDefined_limit {J : Type*} [Category* J] (R : J ⥤ D)
    [HasLimit R] [HasLimitsOfShape J C]
    (h : ∀ (j : J), F.rightAdjointObjIsDefined (R.obj j)) :
    F.rightAdjointObjIsDefined (limit R) :=
  rightAdjointObjIsDefined_of_isLimit (limit.isLimit R) h

end partialRightAdjoint

end Functor

end CategoryTheory
