/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Yun Liu, Christian Merten, Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Weighted limits

In this file, we define weighted limits (in the non enriched case).
Given a weight `W : J ⥤ Type w` and a functor `F : J ⥤ C`,
the `W`-weighted limit of `J` is the limit of the functor
`CategoryOfElements.π W ⋙ F : W.Elements ⥤ C`.

## References
* https://ncatlab.org/nlab/show/weighted+limit

-/

@[expose] public section

universe w v u v' u'

namespace CategoryTheory

open Limits Opposite

namespace Limits

variable {J : Type u} [Category.{v} J] {C : Type u'} [Category.{v'} C]

/-- Given `W : J ⥤ Type w` and `F : J ⥤ C`, this is the type of cones for
the functor `CategoryOfElements.π W ⋙ F : W.Elements ⥤ C`. -/
abbrev WeightedCone (W : J ⥤ Type w) (F : J ⥤ C) :=
  Cone (CategoryOfElements.π W ⋙ F)

/-- Given a weight `W : J ⥤ Type w` and `F : J ⥤ C`, we say that
the `W`-weighted limit of `F` exists if the functor
`CategoryOfElements.π W ⋙ F : W.Elements ⥤ C` has a limit. -/
abbrev HasWeightedLimit (W : J ⥤ Type w) (F : J ⥤ C) : Prop :=
  HasLimit (CategoryOfElements.π W ⋙ F)

namespace WeightedCone

variable {W : J ⥤ Type w} {F : J ⥤ C}

/-- The projection `c.pt ⟶ F.obj j` for `c : WeightedCone W F`
and `x : W.obj j`. -/
protected abbrev π (c : WeightedCone W F) {j : J} (x : W.obj j) :
    c.pt ⟶ F.obj j :=
  (Cone.π c).app (Functor.elementsMk _ _ x)

@[reassoc (attr := simp)]
protected lemma w (c : WeightedCone W F) {i j : J} (x : W.obj i) (f : i ⟶ j) :
    c.π x ≫ F.map f = c.π (W.map f x) :=
  Cone.w c (CategoryOfElements.homMk (Functor.elementsMk _ _ x)
    (Functor.elementsMk _ _ (W.map f x)) f rfl)

variable (pt : C) (π : ∀ ⦃j : J⦄ (_ : W.obj j), pt ⟶ F.obj j)
  (hπ : ∀ ⦃j₁ j₂ : J⦄ (x : W.obj j₁) (f : j₁ ⟶ j₂),
    π x ≫ F.map f = π (W.map f x))

set_option backward.defeqAttrib.useBackward true in
/-- Constructor for weighted cones. -/
@[simps pt]
def mk : WeightedCone W F where
  pt := pt
  π.app x := π x.snd
  π.naturality x₁ x₂ f := by simpa using (hπ x₁.snd f.val).symm

@[simp]
lemma mk_π {j : J} (x : W.obj j) :
    (mk pt π hπ).π x = π x := rfl

/-- A weighted cone `c : WeightedCone W F` is a limit if it is so
as a cone of `CategoryOfElements.π W ⋙ F : W.Elements ⥤ C`. -/
protected abbrev IsLimit (c : WeightedCone W F) := Limits.IsLimit c

namespace IsLimit

variable {c : WeightedCone W F} (hc : c.IsLimit) {Z : C}

include hc in
lemma hasWeightedLimit : HasWeightedLimit W F := ⟨_, hc⟩

section

variable
  (π : ∀ ⦃j : J⦄ (_ : W.obj j), Z ⟶ F.obj j)
  (hπ : ∀ ⦃j₁ j₂ : J⦄ (x : W.obj j₁) (f : j₁ ⟶ j₂),
    π x ≫ F.map f = π (W.map f x))

/-- Constructor for morphisms from the point of a limit weighted cone. -/
def lift : Z ⟶ c.pt :=
  Limits.IsLimit.lift hc (WeightedCone.mk Z π hπ)

@[reassoc (attr := simp)]
lemma fac {j : J} (x : W.obj j) :
    hc.lift π hπ ≫ c.π x = π x :=
  Limits.IsLimit.fac hc (WeightedCone.mk Z π hπ) (Functor.elementsMk _ _ x)

end

include hc in
lemma hom_ext {f g : Z ⟶ c.pt} (h : ∀ {j : J} (x : W.obj j), f ≫ c.π x = g ≫ c.π x) :
    f = g :=
  Limits.IsLimit.hom_ext hc (fun _ ↦ h _)

end IsLimit

open Opposite in
set_option backward.defeqAttrib.useBackward true in
/-- If the weight is `coyoneda.obj (op j) : J ⥤ Type _`, this is the limit
weighted cone for `F : J ⥤ C` with point `F.obj j`. -/
@[simps]
protected abbrev coyoneda (F : J ⥤ C) (j : J) :
    WeightedCone (coyoneda.obj (op j)) F where
  pt := F.obj j
  π.app u := F.map u.snd
  π.naturality _ _ f := by simp [← Functor.map_comp, Category.id_comp, f.prop.symm]

set_option backward.defeqAttrib.useBackward true in
/-- The weighted limit of `F` for the weight `coyoneda.obj (op j)` is `F.obj j`. -/
def isLimitCoyoneda (F : J ⥤ C) (j : J) : (WeightedCone.coyoneda F j).IsLimit where
  lift s := WeightedCone.π s (𝟙 j)
  fac s x := by
    simpa using s.w (CategoryOfElements.homMk (Functor.elementsMk _ j (𝟙 j)) x x.snd (by simp))
  uniq s m hm := by
    simpa using hm (Functor.elementsMk _ j (𝟙 j))

end WeightedCone

end Limits

namespace Functor

section

variable {J : Type u} [Category.{v} J] {C : Type u'} [Category.{v'} C]
  (W W' W'' : J ⥤ Type w) (g : W ⟶ W') (g' : W' ⟶ W'') (F : J ⥤ C)
  [HasWeightedLimit W F] [HasWeightedLimit W' F] [HasWeightedLimit W'' F]

/-- Given a weight `W : J ⥤ Type w` and `F : J ⥤ C`, this is the `W`-weighted
limit of `F`. -/
noncomputable def weightedLimObjObj : C :=
  limit (CategoryOfElements.π W ⋙ F)

/-- The projections from the weighted limit. -/
@[no_expose]
noncomputable def weightedLimObjObjπ ⦃j : J⦄ (x : W.obj j) :
    W.weightedLimObjObj F ⟶ F.obj j :=
  limit.π (CategoryOfElements.π W ⋙ F) (Functor.elementsMk _ _ x)

@[reassoc (attr := simp)]
lemma weightedLimObjObj_w ⦃j₁ j₂ : J⦄ (x : W.obj j₁)
    (f : j₁ ⟶ j₂) :
    W.weightedLimObjObjπ F x ≫ F.map f =
      W.weightedLimObjObjπ F (W.map f x) :=
  limit.w (CategoryOfElements.π W ⋙ F)
    (CategoryOfElements.homMk (Functor.elementsMk _ _ x) (Functor.elementsMk _ _
      (W.map f x)) f rfl)

/-- A choice of limit weighted cone. -/
noncomputable abbrev weightedLimCone :
    WeightedCone W F :=
  WeightedCone.mk (W.weightedLimObjObj F)
    (fun j x ↦ W.weightedLimObjObjπ F x)
    (fun j₁ j₂ x f ↦ by simp)

/-- The weighted cone `W.weightedLimCone F` is a limit. -/
@[no_expose]
noncomputable def isLimitWeightedLimCone :
    (W.weightedLimCone F).IsLimit :=
  limit.isLimit _

@[reassoc (attr := simp)]
lemma isLimitWeightedLimCone_fac {Z} (π) (hπ) ⦃j : J⦄ (x : W.obj j) :
    (W.isLimitWeightedLimCone F).lift (Z := Z) π hπ ≫ W.weightedLimObjObjπ F x = π x :=
  (W.isLimitWeightedLimCone F).fac ..

variable {W F} in
@[ext]
lemma weightedLimObjObj.hom_ext {Z : C} {f g : Z ⟶ W.weightedLimObjObj F}
    (h : ∀ {j : J} (x : W.obj j),
      f ≫ W.weightedLimObjObjπ F x = g ≫ W.weightedLimObjObjπ F x) :
    f = g :=
  (W.isLimitWeightedLimCone F).hom_ext h

/-- Functoriality of the weighted limits with fixed weight `W : J ⥤ Type w`
with respect to the functor in `J ⥤ C`. -/
@[no_expose]
noncomputable def weightedLimObjMap {F₁ F₂ : J ⥤ C}
    [HasWeightedLimit W F₁] [HasWeightedLimit W F₂] (f : F₁ ⟶ F₂) :
    W.weightedLimObjObj F₁ ⟶ W.weightedLimObjObj F₂ :=
  limMap (whiskerLeft _ f)

@[reassoc (attr := simp)]
lemma weightedLimObjMap_π {F₁ F₂ : J ⥤ C}
    [HasWeightedLimit W F₁] [HasWeightedLimit W F₂] (f : F₁ ⟶ F₂)
    ⦃j : J⦄ (x : W.obj j) :
    W.weightedLimObjMap f ≫ W.weightedLimObjObjπ F₂ x =
      W.weightedLimObjObjπ F₁ x ≫ f.app j :=
  limit.lift_π ..

@[simp]
lemma weightedLimObjMap_id (F : J ⥤ C) [HasWeightedLimit W F] :
    W.weightedLimObjMap (𝟙 F) = 𝟙 _ := by
  cat_disch

@[reassoc]
lemma weightedLimObjMap_comp {F₁ F₂ F₃ : J ⥤ C}
    [HasWeightedLimit W F₁] [HasWeightedLimit W F₂] [HasWeightedLimit W F₃]
    (f : F₁ ⟶ F₂) (g : F₂ ⟶ F₃) :
    W.weightedLimObjMap (f ≫ g) = W.weightedLimObjMap f ≫ W.weightedLimObjMap g := by
  cat_disch

section

variable {W W' W''}

/-- The (contravariant) functoriality of weighted limits with respect to the weight. -/
noncomputable def weightedLimFlipObjMap :
    W'.weightedLimObjObj F ⟶ W.weightedLimObjObj F :=
  (W.isLimitWeightedLimCone F).lift
    (fun j x ↦ W'.weightedLimObjObjπ F (g.app j x)) (by simp)

@[reassoc (attr := simp)]
lemma weightedLimObjObjMap_π ⦃j : J⦄ (x : W.obj j) :
    weightedLimFlipObjMap g F ≫ W.weightedLimObjObjπ F x =
      W'.weightedLimObjObjπ F (g.app j x) :=
  (W.isLimitWeightedLimCone F).fac ..

@[simp]
lemma weightedLimFlipObjMap_id :
    weightedLimFlipObjMap (𝟙 W) F = 𝟙 _ := by
  cat_disch

@[reassoc]
lemma weightedLimFlipObjMap_comp :
    weightedLimFlipObjMap g' F ≫ weightedLimFlipObjMap g F =
    weightedLimFlipObjMap (g ≫ g') F := by
  cat_disch

end

end

section

variable {J : Type u} [Category.{v} J] (W : J ⥤ Type w) {C : Type u'} [Category.{v'} C]

variable (C) in
/-- Given a weight `W : J ⥤ Type w`, this is the property that all `W`-weighted limits
exist for functors `F : J ⥤ C`. -/
abbrev HasWeightedLimObj : Prop :=
  ∀ (F : J ⥤ C), HasWeightedLimit W F

variable [W.HasWeightedLimObj C]

/-- Weighted limits for a fixed weight `W : J ⥤p Type w`, as a functor `(J ⥤ C) ⥤ C`. -/
@[implicit_reducible, simps]
noncomputable def weightedLimObj : (J ⥤ C) ⥤ C where
  obj F := W.weightedLimObjObj F
  map f := W.weightedLimObjMap f

instance (j : Jᵒᵖ) : HasWeightedLimObj (coyoneda.obj j) C :=
  fun F ↦ (WeightedCone.isLimitCoyoneda F j.unop).hasWeightedLimit

end

section

variable {J : Type u} [Category.{v} J] {C : Type u'} [Category.{v'} C]
  (F : J ⥤ C)

/-- Given a functor `F : J ⥤ C`, this is the property satisfied by weights `W : J ⥤ Type w`
such that the `W`-weighted limit of `F` exists. -/
abbrev hasWeightedLimit : ObjectProperty (J ⥤ Type w) :=
  fun W ↦ HasWeightedLimit W F

instance (W : (hasWeightedLimit.{w} F).FullSubcategory) :
    HasWeightedLimit W.obj F := W.property

/-- Given a functor `F : J ⥤ C`, this is the functor which sends a weight `W : J ⥤ Type w`
to the `W`-weighted limit of `F`. This is defined on the full subcategory of `J ⥤ Type w`
where this weighted limit exists. -/
@[implicit_reducible, simps]
noncomputable def weightedLimFlipObj' : (hasWeightedLimit.{w} F).FullSubcategoryᵒᵖ ⥤ C where
  obj W := W.unop.1.weightedLimObjObj F
  map g := weightedLimFlipObjMap g.unop.hom F

/-- Given `F : J ⥤ C`, this is the property that weighted limits of `F` exist for all
weights `W : J ⥤ Type w`. -/
abbrev HasWeightedLimFlipObj : Prop :=
  ∀ (W : J ⥤ Type w), HasWeightedLimit W F

variable [HasWeightedLimFlipObj.{w} F]

lemma hasWeightedLimit_eq_top :
    hasWeightedLimit.{w} F = ⊤ := by
  rw [← top_le_iff]
  infer_instance

/-- Given a functor `F : J ⥤ C`, this is the functor `(J ⥤ Type w)ᵒᵖ ⥤ C` which sends
a weight `W : J ⥤ Type w` to the `W`-weighted limit of `F`. Here, we assume that
all such weighted limits exist. -/
@[implicit_reducible, simps]
noncomputable def weightedLimFlipObj : (J ⥤ Type w)ᵒᵖ ⥤ C where
  obj W := W.unop.weightedLimObjObj F
  map g := weightedLimFlipObjMap g.unop F

/-- When `HasWeightedLimFlipObj.{w} F` holds, the composition
of the equivalence `F.hasWeightedLimit.ι.op` with `weightedLimFlipObj.{w} F`
identifies to `weightedLimFlipObj'.{w} F`. -/
noncomputable def weightedLimFlipObjIso' :
    F.hasWeightedLimit.ι.op ⋙ weightedLimFlipObj.{w} F ≅
      F.weightedLimFlipObj' :=
  Iso.refl _

instance : (hasWeightedLimit.{w} F).ι.IsEquivalence :=
  ObjectProperty.isEquivalence_ι (hasWeightedLimit_eq_top _)

/-- When `HasWeightedLimFlipObj.{w} F` holds, the composition
of the inverse of the equivalence `F.hasWeightedLimit.ι.op` with
`weightedLimFlipObj'.{w} F` identifies to `weightedLimFlipObj.{w} F`. -/
noncomputable def weightedLimFlipObjIso :
    F.hasWeightedLimit.ι.inv.op ⋙ F.weightedLimFlipObj' ≅
      weightedLimFlipObj.{w} F :=
  Functor.isoWhiskerLeft _ F.weightedLimFlipObjIso'.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight F.hasWeightedLimit.ι.asEquivalence.op.counitIso _ ≪≫
    Functor.leftUnitor _

end

end Functor

namespace Limits

variable {J : Type u} [Category.{v} J] {C : Type u'} [Category.{v'} C]

/-- When all weighted limits exists, this is the weighted limit
bifunctor `(J ⥤ Type w)ᵒᵖ ⥤ (J ⥤ C) ⥤ C`. -/
@[implicit_reducible, simps]
noncomputable def weightedLim [∀ (W : J ⥤ Type w), W.HasWeightedLimObj C] :
    (J ⥤ Type w)ᵒᵖ ⥤ (J ⥤ C) ⥤ C where
  obj W := W.unop.weightedLimObj
  map g := { app F := Functor.weightedLimFlipObjMap g.unop F }

section

variable {W : J ⥤ Type w} {F : J ⥤ C} {c : WeightedCone W F} (hc : c.IsLimit)
  [HasWeightedLimit W F]

/-- The isomorphism `weightedLimObjObj W F ≅ c.pt` when `c : WeightedCone W F`
is a limit. -/
@[no_expose]
noncomputable def WeightedCone.IsLimit.iso :
    W.weightedLimObjObj F ≅ c.pt :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit _) hc

@[reassoc (attr := simp)]
lemma WeightedCone.IsLimit.iso_hom_π {j : J} (x : W.obj j) :
    hc.iso.hom ≫ c.π x = W.weightedLimObjObjπ F x :=
  IsLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit _) hc (Functor.elementsMk _ _ x)

@[reassoc (attr := simp)]
lemma WeightedCone.IsLimit.iso_inv_π {j : J} (x : W.obj j) :
    hc.iso.inv ≫ W.weightedLimObjObjπ F x = c.π x :=
  IsLimit.conePointUniqueUpToIso_inv_comp (limit.isLimit _) hc (Functor.elementsMk _ _ x)

end

set_option backward.defeqAttrib.useBackward true in
/-- Let `j : J`, the weighted limit functor with weight `coyoneda.obj (op j) : J ⥤ Type _`
identifies to the evaluation functor `(J ⥤ C) ⥤ C` at `j`. -/
@[simps!]
noncomputable def weightedLimObjCoyonedaObjIso (j : J) :
    Functor.weightedLimObj (coyoneda.obj (op j)) ≅
      (evaluation J C).obj j :=
  (NatIso.ofComponents (fun F ↦ (WeightedCone.isLimitCoyoneda F j).iso.symm)).symm

end Limits

end CategoryTheory
