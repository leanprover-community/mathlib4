/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Comma.Presheaf.Basic
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.CategoryTheory.ShrinkYoneda

/-!
# Colimit of representables

In this file, We show that every presheaf of types on a category `C` (with `Category.{v₁} C`)
is a colimit of representables. This result is also known as the density theorem,
the co-Yoneda lemma and the Ninja Yoneda lemma. Three formulations are given:
* `colimitOfRepresentable` uses the category of elements of a functor to types;
* `isColimitTautologicalCocone` uses the category of costructured arrows
  for `yoneda : C ⥤ Cᵒᵖ ⥤ Type v₁`;
* `isColimitTautologicalCocone'` uses the category of costructured arrows
  for `uliftYoneda : C ⥤ Cᵒᵖ ⥤ Type max w v₁`, when the presheaf has values
  in `Type max w v₁`;

In this file, we also study the left Kan extensions of functors `A : C ⥤ ℰ`
along the Yoneda embedding `uliftYoneda : C ⥤ Cᵒᵖ ⥤ Type max w v₁ v₂`
(when `Category.{v₂} ℰ` and `w` is an auxiliary universe). In particular,
the definition `uliftYonedaAdjunction` shows that such a pointwise left Kan
extension (which exists when `ℰ` has colimits) is a left adjoint to the
functor `restrictedULiftYoneda : ℰ ⥤ Cᵒᵖ ⥤ Type max w v₁ v₂`.

In the lemma `isLeftKanExtension_along_uliftYoneda_iff`, we show that
if `L : (Cᵒᵖ ⥤ Type max w v₁ v₂) ⥤ ℰ` and `α : A ⟶ uliftYoneda ⋙ L`, then
`α` makes `L` the left Kan extension of `L` along yoneda if and only if
`α` is an isomorphism (i.e. `L` extends `A`) and `L` preserves colimits.
`uniqueExtensionAlongULiftYoneda` shows `uliftYoneda.leftKanExtension A` is
unique amongst functors preserving colimits with this property, establishing the
presheaf category as the free cocompletion of a category.

Given a functor `F : C ⥤ D`, we also show construct an isomorphism
`compULiftYonedaIsoULiftYonedaCompLan : F ⋙ uliftYoneda ≅ uliftYoneda ⋙ F.op.lan`, and
show that it makes `F.op.lan` a left Kan extension of `F ⋙ uliftYoneda`.

## Tags
colimit, representable, presheaf, free cocompletion

## References
* [S. MacLane, I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]
* https://ncatlab.org/nlab/show/Yoneda+extension
-/

@[expose] public section

namespace CategoryTheory

open Category Limits Opposite ConcreteCategory

universe w v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]

namespace Presheaf

variable {ℰ : Type u₂} [Category.{v₂} ℰ] (A : C ⥤ ℰ)

/--
Given a functor `A : C ⥤ ℰ` (with `Category.{v₂} ℰ`) and an auxiliary universe `w`,
this is the functor `ℰ ⥤ Cᵒᵖ ⥤ Type max w v₂` which sends `(E : ℰ) (c : Cᵒᵖ)`
to the homset `A.obj C ⟶ E` (considered in the higher universe `max w v₂`).
Under the existence of a suitable pointwise left Kan extension, it is shown in
`uliftYonedaAdjunction` that this functor has a left adjoint.

Defined as in [MM92], Chapter I, Section 5, Theorem 2.
-/
@[simps! obj_map map_app]
def restrictedULiftYoneda : ℰ ⥤ Cᵒᵖ ⥤ Type max w v₂ :=
    uliftYoneda.{w} ⋙ (Functor.whiskeringLeft _ _ _).obj A.op

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma map_comp_uliftYonedaEquiv_down (E : ℰ) {X Y : C} (f : X ⟶ Y)
    (g : uliftYoneda.{max w v₂}.obj Y ⟶ (restrictedULiftYoneda.{max w v₁} A).obj E) :
    A.map f ≫ (uliftYonedaEquiv g).down =
      (uliftYonedaEquiv (uliftYoneda.map f ≫ g)).down := by
  have this := (g.naturality_apply f.op) (ULift.up (𝟙 Y))
  dsimp [uliftYonedaEquiv, uliftYoneda] at this ⊢
  cat_disch

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `restrictedULiftYonedaHomEquiv`. -/
def restrictedULiftYonedaHomEquiv' (P : Cᵒᵖ ⥤ Type max w v₁ v₂) (E : ℰ) :
    (CostructuredArrow.proj uliftYoneda.{max w v₂} P ⋙ A ⟶
      (Functor.const (CostructuredArrow uliftYoneda.{max w v₂} P)).obj E) ≃
      (P ⟶ (restrictedULiftYoneda.{max w v₁} A).obj E) where
  toFun f :=
    { app _ := ↾fun x ↦ ULift.up
        (f.app (CostructuredArrow.mk (uliftYonedaEquiv.symm x)))
      naturality _ _ g := by
        ext x
        let φ : CostructuredArrow.mk (uliftYonedaEquiv.{max w v₂}.symm (P.map g x)) ⟶
          CostructuredArrow.mk (uliftYonedaEquiv.symm x) :=
            CostructuredArrow.homMk g.unop (by
              dsimp
              rw [uliftYonedaEquiv_symm_map])
        dsimp
        congr 1
        simpa using (f.naturality φ).symm }
  invFun g :=
    { app y := (uliftYonedaEquiv.{max w v₂} (y.hom ≫ g)).down
      naturality y y' f := by
        dsimp
        rw [comp_id, ← CostructuredArrow.w f, assoc, map_comp_uliftYonedaEquiv_down] }
  left_inv f := by
    ext X
    let e : CostructuredArrow.mk
      (uliftYonedaEquiv.{max w v₂}.symm (X.hom.app (op X.left) ⟨𝟙 X.left⟩)) ≅ X :=
        CostructuredArrow.isoMk (Iso.refl _) (by
          ext Y x
          dsimp
          simp [← NatTrans.naturality_apply])
    simpa [e] using f.naturality e.inv
  right_inv g := by
    ext X x
    apply ULift.down_injective
    simp [uliftYonedaEquiv]

@[reassoc]
lemma restrictedULiftYonedaHomEquiv'_symm_naturality_right (P : Cᵒᵖ ⥤ Type max w v₁ v₂)
    {E E' : ℰ} (g : E ⟶ E') (f : P ⟶ (restrictedULiftYoneda.{max w v₁} A).obj E) :
    (restrictedULiftYonedaHomEquiv' A P E').symm (f ≫ (restrictedULiftYoneda A).map g) =
      (restrictedULiftYonedaHomEquiv' A P E).symm f ≫ (Functor.const _).map g := by
  rfl

@[reassoc]
lemma restrictedULiftYonedaHomEquiv'_symm_app_naturality_left
    {P Q : Cᵒᵖ ⥤ Type max w v₁ v₂} (f : P ⟶ Q) (E : ℰ)
    (g : Q ⟶ (restrictedULiftYoneda.{max w v₁} A).obj E)
    (p : CostructuredArrow uliftYoneda.{max w v₂} P) :
    ((restrictedULiftYonedaHomEquiv' A P E).symm (f ≫ g)).app p =
      ((restrictedULiftYonedaHomEquiv' A Q E).symm g).app
        ((CostructuredArrow.map f).obj p) :=
  rfl

section

variable (P : ℰᵒᵖ ⥤ Type max w v₁ v₂)

example [HasColimitsOfSize.{v₁, max u₁ v₁ v₂ w} ℰ] :
    (uliftYoneda.{max w v₂}).HasPointwiseLeftKanExtension A := by
  infer_instance

variable [(uliftYoneda.{max w v₂}).HasPointwiseLeftKanExtension A]

variable {A}
variable (L : (Cᵒᵖ ⥤ Type max w v₁ v₂) ⥤ ℰ)
  (α : A ⟶ uliftYoneda.{max w v₂} ⋙ L) [L.IsLeftKanExtension α]

/-- Auxiliary definition for `uliftYonedaAdjunction`. -/
noncomputable def restrictedULiftYonedaHomEquiv (P : Cᵒᵖ ⥤ Type max w v₁ v₂) (E : ℰ) :
    (L.obj P ⟶ E) ≃ (P ⟶ (restrictedULiftYoneda.{max w v₁} A).obj E) :=
  (Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension _ α P).homEquiv.trans
    (restrictedULiftYonedaHomEquiv' A P E)

set_option backward.isDefEq.respectTransparency false in
/-- If `L : (Cᵒᵖ ⥤ Type max w v₁ v₂) ⥤ ℰ` is a pointwise left Kan extension
of a functor `A : C ⥤ ℰ` along the Yoneda embedding,
then `L` is a left adjoint of `restrictedULiftYoneda A : ℰ ⥤ Cᵒᵖ ⥤ Type max w v₁ v₂` -/
noncomputable def uliftYonedaAdjunction : L ⊣ restrictedULiftYoneda.{max w v₁} A :=
  Adjunction.mkOfHomEquiv
    { homEquiv := restrictedULiftYonedaHomEquiv L α
      homEquiv_naturality_left_symm {P Q X} f g := by
        apply (Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension L α P).hom_ext
        intro p
        have hfg := (Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension
          L α P).comp_homEquiv_symm ((restrictedULiftYonedaHomEquiv' A P X).symm (f ≫ g)) p
        have hg := (Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension
          L α Q).comp_homEquiv_symm ((restrictedULiftYonedaHomEquiv' A Q X).symm g)
            ((CostructuredArrow.map f).obj p)
        dsimp at hfg hg
        dsimp [restrictedULiftYonedaHomEquiv]
        simp only [assoc, hfg, ← L.map_comp_assoc, hg,
          restrictedULiftYonedaHomEquiv'_symm_app_naturality_left]
      homEquiv_naturality_right {P X Y} f g := by
        have := @IsColimit.homEquiv_symm_naturality (h :=
          Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension L α P)
        dsimp at this
        apply (restrictedULiftYonedaHomEquiv L α P Y).symm.injective
        apply (Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension L α P).hom_ext
        intro
        simp [restrictedULiftYonedaHomEquiv,
          restrictedULiftYonedaHomEquiv'_symm_naturality_right, this] }

@[simp]
lemma uliftYonedaAdjunction_homEquiv_app {P : Cᵒᵖ ⥤ Type max w v₁ v₂}
    {Y : ℰ} (f : L.obj P ⟶ Y) {Z : Cᵒᵖ} (z : P.obj Z) :
    ((uliftYonedaAdjunction.{w} L α).homEquiv P Y f).app Z z =
      ULift.up (α.app Z.unop ≫ L.map (uliftYonedaEquiv.symm z) ≫ f) := by
  simp [uliftYonedaAdjunction, restrictedULiftYonedaHomEquiv,
    restrictedULiftYonedaHomEquiv', IsColimit.homEquiv]

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma uliftYonedaAdjunction_unit_app_app (P : Cᵒᵖ ⥤ Type max w v₁ v₂)
    {Z : Cᵒᵖ} (z : P.obj Z) :
    dsimp% ((uliftYonedaAdjunction.{w} L α).unit.app P).app Z z =
      ULift.up (α.app Z.unop ≫ L.map (uliftYonedaEquiv.symm z)) := by
  have h₁ := (uliftYonedaAdjunction.{w} L α).homEquiv_unit P _ (𝟙 _)
  simp only [Functor.comp_obj, Functor.map_id, comp_id] at h₁
  simp [← h₁]

include α in
/-- Any left Kan extension along the Yoneda embedding preserves colimits. -/
lemma preservesColimitsOfSize_of_isLeftKanExtension :
    PreservesColimitsOfSize.{v₃, u₃} L :=
  (uliftYonedaAdjunction L α).leftAdjoint_preservesColimits

lemma isIso_of_isLeftKanExtension : IsIso α :=
  (Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension _ α).isIso_hom

variable (A)

/-- See Property 2 of https://ncatlab.org/nlab/show/Yoneda+extension#properties. -/
instance preservesColimitsOfSize_leftKanExtension :
    PreservesColimitsOfSize.{v₃, u₃} (uliftYoneda.{max w v₂}.leftKanExtension A) :=
  (uliftYonedaAdjunction _ (uliftYoneda.leftKanExtensionUnit A)).leftAdjoint_preservesColimits

instance : IsIso (uliftYoneda.{max w v₂}.leftKanExtensionUnit A) :=
  isIso_of_isLeftKanExtension _ (uliftYoneda.leftKanExtensionUnit A)

/-- A pointwise left Kan extension along the Yoneda embedding is an extension. -/
noncomputable def isExtensionAlongULiftYoneda :
    uliftYoneda.{max w v₂} ⋙ uliftYoneda.leftKanExtension A ≅ A :=
  (asIso (uliftYoneda.leftKanExtensionUnit A)).symm

end

/-- Given `P : Cᵒᵖ ⥤ Type max w v₁`, this is the functor from the opposite category
of the category of elements of `X` which sends an element in `P.obj (op X)` to the
presheaf represented by `X`. The definition `coconeOfRepresentable`
gives a cocone for this functor which is a colimit and has point `P`.
-/
@[simps! obj map]
def functorToRepresentables (P : Cᵒᵖ ⥤ Type max w v₁) :
    P.Elementsᵒᵖ ⥤ Cᵒᵖ ⥤ Type max w v₁ :=
  (CategoryOfElements.π P).leftOp ⋙ uliftYoneda.{w}

set_option backward.isDefEq.respectTransparency false in
/-- This is a cocone with point `P` for the functor `functorToRepresentables P`. It is shown in
`colimitOfRepresentable P` that this cocone is a colimit: that is, we have exhibited an arbitrary
presheaf `P` as a colimit of representables.

The construction of [MM92], Chapter I, Section 5, Corollary 3.
-/
@[simps]
def coconeOfRepresentable (P : Cᵒᵖ ⥤ Type max w v₁) :
    Cocone (functorToRepresentables P) where
  pt := P
  ι :=
    { app x := uliftYonedaEquiv.symm x.unop.2
      naturality {x₁ x₂} f := by
        dsimp
        rw [comp_id, ← uliftYonedaEquiv_symm_map, f.unop.2] }

set_option backward.isDefEq.respectTransparency false in
/-- The legs of the cocone `coconeOfRepresentable` are natural in the choice of presheaf. -/
theorem coconeOfRepresentable_naturality
    {P₁ P₂ : Cᵒᵖ ⥤ Type max w v₁} (α : P₁ ⟶ P₂) (j : P₁.Elementsᵒᵖ) :
    (coconeOfRepresentable P₁).ι.app j ≫ α =
      (coconeOfRepresentable P₂).ι.app ((CategoryOfElements.map α).op.obj j) := by
  ext T f
  simp [uliftYonedaEquiv]

set_option backward.isDefEq.respectTransparency false in
/-- The cocone with point `P` given by `coconeOfRepresentable` is a colimit:
that is, we have exhibited an arbitrary presheaf `P` as a colimit of representables.

The result of [MM92], Chapter I, Section 5, Corollary 3.
-/
def colimitOfRepresentable (P : Cᵒᵖ ⥤ Type max w v₁) :
    IsColimit (coconeOfRepresentable P) where
  desc s :=
    { app X := ↾fun x ↦ uliftYonedaEquiv
        (s.ι.app (Opposite.op (Functor.elementsMk P X x)))
      naturality X Y f := by
        ext x
        have := s.w (Quiver.Hom.op (CategoryOfElements.homMk (P.elementsMk X x)
          (P.elementsMk Y (P.map f x)) f rfl))
        dsimp at this x ⊢
        rw [← this, uliftYonedaEquiv_comp]
        dsimp
        rw [uliftYonedaEquiv_apply, uliftYonedaEquiv_apply,
          ← NatTrans.naturality_apply]
        simp [uliftYoneda] }
  fac s j := by
    ext X x
    let φ : j.unop ⟶ (Functor.elementsMk P _
      ((uliftYonedaEquiv.symm (unop j).snd).app X x)) := ⟨x.down.op, rfl⟩
    have := s.w φ.op
    dsimp [φ] at this x ⊢
    rw [← this, uliftYonedaEquiv_apply]
    simp [uliftYoneda]
  uniq s m hm := by
    ext X x
    simp only [functorToRepresentables_obj, coconeOfRepresentable_pt, Functor.const_obj_obj,
      coconeOfRepresentable_ι_app, Functor.leftOp_obj, CategoryOfElements.π_obj, op_unop,
      TypeCat.Fun.toFun_apply, hom_ofHom, TypeCat.Fun.coe_mk] at hm ⊢
    rw [← hm, uliftYonedaEquiv_comp, Equiv.apply_symm_apply]

variable {A : C ⥤ ℰ}

example [HasColimitsOfSize.{v₁, max w u₁ v₁ v₂} ℰ] :
    uliftYoneda.{max w v₂}.HasPointwiseLeftKanExtension A := by
  infer_instance

variable [uliftYoneda.{max w v₂}.HasPointwiseLeftKanExtension A]

section

variable (L : (Cᵒᵖ ⥤ Type max w v₁ v₂) ⥤ ℰ) (α : A ⟶ uliftYoneda.{max w v₂} ⋙ L)

instance [L.IsLeftKanExtension α] : IsIso α :=
  (Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension L α).isIso_hom

lemma isLeftKanExtension_along_uliftYoneda_iff :
    L.IsLeftKanExtension α ↔
      (IsIso α ∧ PreservesColimitsOfSize.{v₁, max w u₁ v₁ v₂} L) := by
  constructor
  · intro
    exact ⟨inferInstance, preservesColimits_of_natIso (Functor.leftKanExtensionUnique _
      (uliftYoneda.{max w v₂}.leftKanExtensionUnit A) _ α)⟩
  · rintro ⟨_, _⟩
    apply Functor.LeftExtension.IsPointwiseLeftKanExtension.isLeftKanExtension
      (E := Functor.LeftExtension.mk _ α)
    intro P
    dsimp [Functor.LeftExtension.IsPointwiseLeftKanExtensionAt]
    apply IsColimit.ofWhiskerEquivalence
      (CategoryOfElements.costructuredArrowULiftYonedaEquivalence _)
    let e : (CategoryOfElements.costructuredArrowULiftYonedaEquivalence P).functor ⋙
      CostructuredArrow.proj uliftYoneda.{max w v₂} P ⋙ A ≅
        functorToRepresentables.{max w v₂} P ⋙ L :=
      Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _ (asIso α)) ≪≫
        Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫
        (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (Iso.refl _) L
    refine (IsColimit.precomposeHomEquiv e.symm _).1 ?_
    exact IsColimit.ofIsoColimit (isColimitOfPreserves L (colimitOfRepresentable.{max w v₂} P))
      (Cocone.ext (Iso.refl _))

lemma isLeftKanExtension_of_preservesColimits
    (L : (Cᵒᵖ ⥤ Type max w v₁ v₂) ⥤ ℰ) (e : A ≅ uliftYoneda.{max w v₂} ⋙ L)
    [PreservesColimitsOfSize.{v₁, max w u₁ v₁ v₂} L] :
    L.IsLeftKanExtension e.hom := by
  rw [isLeftKanExtension_along_uliftYoneda_iff]
  exact ⟨inferInstance, ⟨inferInstance⟩⟩

end

/-- Show that `uliftYoneda.leftKanExtension A` is the unique colimit-preserving
functor which extends `A` to the presheaf category.

The second part of [MM92], Chapter I, Section 5, Corollary 4.
See Property 3 of https://ncatlab.org/nlab/show/Yoneda+extension#properties.
-/
noncomputable def uniqueExtensionAlongULiftYoneda (L : (Cᵒᵖ ⥤ Type max w v₁ v₂) ⥤ ℰ)
    (e : A ≅ uliftYoneda.{max w v₂} ⋙ L)
    [PreservesColimitsOfSize.{v₁, max w u₁ v₁ v₂} L] :
    L ≅ uliftYoneda.{max w v₂}.leftKanExtension A :=
  have := isLeftKanExtension_of_preservesColimits L e
  Functor.leftKanExtensionUnique _ e.hom _ (uliftYoneda.leftKanExtensionUnit A)

instance (L : (Cᵒᵖ ⥤ Type max w v₁ v₂) ⥤ ℰ) [PreservesColimitsOfSize.{v₁, max w u₁ v₁ v₂} L]
    [uliftYoneda.{max w v₂}.HasPointwiseLeftKanExtension (uliftYoneda.{max w v₂} ⋙ L)] :
    L.IsLeftKanExtension (𝟙 _ : uliftYoneda.{max w v₂} ⋙ L ⟶ _) :=
  isLeftKanExtension_of_preservesColimits _ (Iso.refl _)

/-- If `L` preserves colimits and `ℰ` has them, then it is a left adjoint. Note this is a (partial)
converse to `leftAdjointPreservesColimits`.
-/
lemma isLeftAdjoint_of_preservesColimits (L : (C ⥤ Type max w v₁ v₂) ⥤ ℰ)
    [PreservesColimitsOfSize.{v₁, max w u₁ v₁ v₂} L]
    [uliftYoneda.{max w v₂}.HasPointwiseLeftKanExtension
      (uliftYoneda.{max w v₂} ⋙ (opOpEquivalence C).congrLeft.functor.comp L)] :
    L.IsLeftAdjoint :=
  ⟨_, ⟨((opOpEquivalence C).congrLeft.symm.toAdjunction.comp
    (uliftYonedaAdjunction _ (𝟙 _))).ofNatIsoLeft
      ((opOpEquivalence C).congrLeft.invFunIdAssoc L)⟩⟩

section

variable {D : Type u₂} [Category.{v₁} D] (F : C ⥤ D)

set_option backward.isDefEq.respectTransparency false in
instance (X : C) (Y : F.op.LeftExtension (yoneda.obj X)) :
    Unique (Functor.LeftExtension.mk _ (yonedaMap F X) ⟶ Y) where
  default := StructuredArrow.homMk
      (yonedaEquiv.symm (yonedaEquiv (F := F.op.comp Y.right) Y.hom)) (by
        ext Z f
        convert (Y.hom.naturality_apply f.op _).symm
        simp)
  uniq φ := by
    ext1
    apply yonedaEquiv.injective
    simp [← StructuredArrow.w φ, yonedaEquiv, yonedaMap]

/-- Given `F : C ⥤ D` and `X : C`, `yoneda.obj (F.obj X) : Dᵒᵖ ⥤ Type _` is the
left Kan extension of `yoneda.obj X : Cᵒᵖ ⥤ Type _` along `F.op`. -/
instance (X : C) : (yoneda.obj (F.obj X)).IsLeftKanExtension (yonedaMap F X) :=
  ⟨⟨Limits.IsInitial.ofUnique _⟩⟩

end

section

variable {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)

set_option backward.isDefEq.respectTransparency false in
instance (X : C) (Y : F.op.LeftExtension (uliftYoneda.{max w v₂}.obj X)) :
    Unique (Functor.LeftExtension.mk _ (uliftYonedaMap.{w} F X) ⟶ Y) where
  default := StructuredArrow.homMk
    (uliftYonedaEquiv.symm (uliftYonedaEquiv (F := F.op ⋙ Y.right) Y.hom)) (by
      ext Z ⟨f⟩
      simpa [uliftYonedaEquiv, uliftYoneda] using
        ConcreteCategory.congr_hom (CC := fun X ↦ X) (Y.hom.naturality f.op).symm (ULift.up (𝟙 _)))
  uniq φ := by
    ext : 1
    apply uliftYonedaEquiv.injective
    simp [← StructuredArrow.w φ, uliftYonedaEquiv, uliftYonedaMap]

/-- Given `F : C ⥤ D` and `X : C`, `uliftYoneda.obj (F.obj X) : Dᵒᵖ ⥤ Type max w v₁ v₂` is the
left Kan extension of `uliftYoneda.obj X : Cᵒᵖ ⥤ Type max w v₁ v₂` along `F.op`. -/
instance (X : C) : (uliftYoneda.{max w v₁}.obj (F.obj X)).IsLeftKanExtension
    (uliftYonedaMap.{w} F X) :=
  ⟨⟨Limits.IsInitial.ofUnique _⟩⟩

section
variable [∀ (P : Cᵒᵖ ⥤ Type max w v₁ v₂), F.op.HasLeftKanExtension P]

set_option backward.isDefEq.respectTransparency false in
/-- `F ⋙ uliftYoneda` is naturally isomorphic to `uliftYoneda ⋙ F.op.lan`. -/
noncomputable def compULiftYonedaIsoULiftYonedaCompLan :
    F ⋙ uliftYoneda.{max w v₁} ≅ uliftYoneda.{max w v₂} ⋙ F.op.lan :=
  NatIso.ofComponents (fun X => Functor.leftKanExtensionUnique _
    (uliftYonedaMap.{w} F X) (F.op.lan.obj _) (F.op.lanUnit.app (uliftYoneda.obj X)))
    (fun {X Y} f => by
      apply uliftYonedaEquiv.injective
      have eq₁ := ConcreteCategory.congr_hom
        ((uliftYoneda.{max w v₁}.obj (F.obj Y)).descOfIsLeftKanExtension_fac_app
        (uliftYonedaMap F Y) (F.op.lan.obj (uliftYoneda.obj Y))
          (F.op.lanUnit.app (uliftYoneda.obj Y)) _) ⟨f⟩
      have eq₂ := ConcreteCategory.congr_hom
        (((uliftYoneda.{max w v₁}.obj (F.obj X)).descOfIsLeftKanExtension_fac_app
        (uliftYonedaMap F X) (F.op.lan.obj (uliftYoneda.obj X))
          (F.op.lanUnit.app (uliftYoneda.obj X))) _) ⟨𝟙 _⟩
      have eq₃ := ConcreteCategory.congr_hom (congr_app (F.op.lanUnit.naturality
        (uliftYoneda.{max w v₂}.map f)) _) ⟨𝟙 _⟩
      dsimp [uliftYoneda, uliftYonedaMap, uliftYonedaEquiv,
        Functor.leftKanExtensionUnique] at eq₁ eq₂ eq₃ ⊢
      simp only [Functor.map_id] at eq₂
      simp only [id_comp] at eq₃
      simp [eq₁, eq₂, eq₃])

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma compULiftYonedaIsoULiftYonedaCompLan_inv_app_app_apply_eq_id (X : C) :
    dsimp% ((compULiftYonedaIsoULiftYonedaCompLan.{w} F).inv.app X).app (op (F.obj X))
          ((F.op.lanUnit.app ((uliftYoneda.{max w v₂}).obj X)).app (op X)
        (ULift.up (𝟙 X))) = ULift.up (𝟙 (F.obj X)) :=
        (ConcreteCategory.congr_hom (CC := fun X ↦ X) (Functor.descOfIsLeftKanExtension_fac_app _
    (F.op.lanUnit.app ((uliftYoneda.{max w v₂}).obj X)) _
    (uliftYonedaMap.{w} F X) (op X)) (ULift.up (𝟙 X))).trans (by simp [uliftYonedaMap])

end

namespace compULiftYonedaIsoULiftYonedaCompLan

variable {F}

section

variable {X : C} {G : (Cᵒᵖ ⥤ Type max w v₁ v₂) ⥤ Dᵒᵖ ⥤ Type max w v₁ v₂}
  (φ : F ⋙ uliftYoneda.{max w v₁} ⟶ uliftYoneda.{max w v₂} ⋙ G)

/-- Auxiliary definition for `presheafHom`. -/
def coconeApp {P : Cᵒᵖ ⥤ Type max w v₁ v₂} (x : P.Elements) :
    uliftYoneda.{max w v₂}.obj x.1.unop ⟶ F.op ⋙ G.obj P :=
  uliftYonedaEquiv.symm
    ((G.map (uliftYonedaEquiv.{max w v₂}.symm x.2)).app _
      ((φ.app x.1.unop).app _ (ULift.up (𝟙 _))))

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma coconeApp_naturality {P : Cᵒᵖ ⥤ Type max w v₁ v₂} {x y : P.Elements} (f : x ⟶ y) :
    uliftYoneda.map f.1.unop ≫ coconeApp.{w} φ x = coconeApp φ y := by
  have eq₁ : uliftYoneda.map f.1.unop ≫ uliftYonedaEquiv.symm x.2 =
      uliftYonedaEquiv.{max w v₂}.symm y.2 :=
    uliftYonedaEquiv.injective
      (by simpa only [Equiv.apply_symm_apply, ← uliftYonedaEquiv_naturality] using f.2)
  have eq₂ := ConcreteCategory.congr_hom ((G.map (uliftYonedaEquiv.{max w v₂}.symm x.2)).naturality
    (F.map f.1.unop).op) ((φ.app x.1.unop).app _ (ULift.up (𝟙 _)))
  have eq₃ := ConcreteCategory.congr_hom (CC := fun X ↦ X)
    (congr_app (φ.naturality f.1.unop) _) (ULift.up (𝟙 _))
  have eq₄ := ConcreteCategory.congr_hom ((φ.app x.1.unop).naturality (F.map f.1.unop).op)
  dsimp at eq₂ eq₃ eq₄
  apply uliftYonedaEquiv.{max w v₂}.injective
  dsimp only [coconeApp]
  rw [Equiv.apply_symm_apply, ← uliftYonedaEquiv_naturality, Equiv.apply_symm_apply]
  simp only [op_unop, Functor.comp_obj, Functor.op_obj, Functor.comp_map, Functor.op_map,
    uliftYoneda_obj_obj, yoneda_obj_obj, ← eq₃, ← eq₄, ← eq₂, ← eq₁, Functor.map_comp,
    NatTrans.comp_app, comp_apply]
  simp [uliftYoneda]

set_option backward.isDefEq.respectTransparency false in
/-- Given functors `F : C ⥤ D` and
`G : (Cᵒᵖ ⥤ Type max w v₁ v₂) ⥤ (Dᵒᵖ ⥤ Type max w v₁ v₂)`,
and a natural transformation `φ : F ⋙ uliftYoneda ⟶ uliftYoneda ⋙ G`, this is the
(natural) morphism `P ⟶ F.op ⋙ G.obj P` for all `P : Cᵒᵖ ⥤ Type max w v₁ v₂` that is
determined by `φ`. -/
def presheafHom (P : Cᵒᵖ ⥤ Type max w v₁ v₂) : P ⟶ F.op ⋙ G.obj P :=
  (colimitOfRepresentable P).desc
    (Cocone.mk _ { app x := coconeApp.{w} φ x.unop })

lemma uliftYonedaEquiv_ι_presheafHom (P : Cᵒᵖ ⥤ Type max w v₁ v₂) {X : C}
    (f : uliftYoneda.{max w v₂}.obj X ⟶ P) :
    uliftYonedaEquiv (f ≫ presheafHom.{w} φ P) =
      (G.map f).app (Opposite.op (F.obj X)) ((φ.app X).app _ (ULift.up (𝟙 _))) := by
  obtain ⟨x, rfl⟩ := uliftYonedaEquiv.symm.surjective f
  erw [(colimitOfRepresentable P).fac _ (Opposite.op (P.elementsMk _ x))]
  dsimp only [coconeApp]
  apply Equiv.apply_symm_apply

lemma uliftYonedaEquiv_presheafHom_uliftYoneda_obj (X : C) :
    uliftYonedaEquiv.{max w v₂} (presheafHom.{w} φ (uliftYoneda.{max w v₂}.obj X)) =
      ((φ.app X).app (F.op.obj (Opposite.op X)) (ULift.up (𝟙 _))) := by
  simpa using uliftYonedaEquiv_ι_presheafHom.{w} φ (uliftYoneda.obj X) (𝟙 _)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma presheafHom_naturality {P Q : Cᵒᵖ ⥤ Type max w v₁ v₂} (f : P ⟶ Q) :
    presheafHom.{w} φ P ≫ Functor.whiskerLeft F.op (G.map f) = f ≫ presheafHom φ Q :=
  hom_ext_uliftYoneda.{max w v₂} (fun X p ↦ uliftYonedaEquiv.injective (by
    rw [← assoc p f, uliftYonedaEquiv_ι_presheafHom, ← assoc,
      uliftYonedaEquiv_comp, uliftYonedaEquiv_ι_presheafHom,
      Functor.map_comp]
    dsimp))

variable [∀ (P : Cᵒᵖ ⥤ Type max w v₁ v₂), F.op.HasLeftKanExtension P]

/-- Given functors `F : C ⥤ D` and `G : (Cᵒᵖ ⥤ Type max w v₁ v₂) ⥤ (Dᵒᵖ ⥤ Type max w v₁ v₂)`,
and a natural transformation `φ : F ⋙ uliftYoneda ⟶ uliftYoneda ⋙ G`, this is
the canonical natural transformation `F.op.lan ⟶ G`, which is part of the
fact that `F.op.lan : (Cᵒᵖ ⥤ Type max w v₁ v₂) ⥤ Dᵒᵖ ⥤ Type max w v₁ v₂`
is the left Kan extension of `F ⋙ uliftYoneda : C ⥤ Dᵒᵖ ⥤ Type max w v₁ v₂`
along `uliftYoneda : C ⥤ Cᵒᵖ ⥤ Type max w v₁ v₂`. -/
noncomputable def natTrans : F.op.lan ⟶ G where
  app P := (F.op.lan.obj P).descOfIsLeftKanExtension (F.op.lanUnit.app P) _ (presheafHom φ P)
  naturality {P Q} f := by
    apply (F.op.lan.obj P).hom_ext_of_isLeftKanExtension (F.op.lanUnit.app P)
    have eq := F.op.lanUnit.naturality f
    dsimp at eq ⊢
    rw [Functor.descOfIsLeftKanExtension_fac_assoc, ← reassoc_of% eq,
      Functor.descOfIsLeftKanExtension_fac, presheafHom_naturality]

set_option backward.isDefEq.respectTransparency false in
lemma natTrans_app_uliftYoneda_obj (X : C) :
    (natTrans.{w} φ).app (uliftYoneda.{max w v₂}.obj X) =
      (compULiftYonedaIsoULiftYonedaCompLan.{w} F).inv.app X ≫ φ.app X := by
  dsimp [natTrans]
  apply (F.op.lan.obj (uliftYoneda.obj X)).hom_ext_of_isLeftKanExtension (F.op.lanUnit.app _)
  rw [Functor.descOfIsLeftKanExtension_fac]
  apply uliftYonedaEquiv.injective
  rw [uliftYonedaEquiv_presheafHom_uliftYoneda_obj]
  exact _root_.congr_arg _ (compULiftYonedaIsoULiftYonedaCompLan_inv_app_app_apply_eq_id F X).symm

end

variable [∀ (P : Cᵒᵖ ⥤ Type max w v₁ v₂), F.op.HasLeftKanExtension P]

set_option backward.isDefEq.respectTransparency false in
/-- Given a functor `F : C ⥤ D`, this definition is part of the verification that
`Functor.LeftExtension.mk F.op.lan (compULiftYonedaIsoULiftYonedaCompLan F).hom`
is universal, i.e. that  `F.op.lan : (Cᵒᵖ ⥤ Type max w v₁ v₂) ⥤ Dᵒᵖ ⥤ Type max w v₁ v₂`
is the left Kan extension of `F ⋙ uliftYoneda : C ⥤ Dᵒᵖ ⥤ Type max w v₁ v₂`
along `uliftYoneda : C ⥤ Cᵒᵖ ⥤ Type max w v₁ v₂`. -/
noncomputable def extensionHom
    (Φ : uliftYoneda.{max w v₂}.LeftExtension (F ⋙ uliftYoneda.{max w v₁})) :
    Functor.LeftExtension.mk F.op.lan (compULiftYonedaIsoULiftYonedaCompLan.{w} F).hom ⟶ Φ :=
  StructuredArrow.homMk (natTrans Φ.hom) (by
    ext X : 2
    dsimp
    rw [natTrans_app_uliftYoneda_obj, Iso.hom_inv_id_app_assoc])

set_option backward.isDefEq.respectTransparency false in
@[ext]
lemma hom_ext {Φ : uliftYoneda.{max w v₂}.LeftExtension (F ⋙ uliftYoneda.{max w v₁})}
    (f g : Functor.LeftExtension.mk F.op.lan (compULiftYonedaIsoULiftYonedaCompLan F).hom ⟶ Φ) :
    f = g := by
  ext P : 3
  apply (F.op.lan.obj P).hom_ext_of_isLeftKanExtension (F.op.lanUnit.app P)
  apply (colimitOfRepresentable.{max w v₂} P).hom_ext
  intro x
  have eq := F.op.lanUnit.naturality (uliftYonedaEquiv.{max w v₂}.symm x.unop.2)
  have eq₁ := congr_hom (CC := fun X ↦ X) (congr_app (congr_app (StructuredArrow.w f) x.unop.1.unop)
    (F.op.obj x.unop.1)) (ULift.up (𝟙 _))
  have eq₂ := congr_hom (CC := fun X ↦ X) (congr_app (congr_app (StructuredArrow.w g) x.unop.1.unop)
    (F.op.obj x.unop.1)) (ULift.up (𝟙 _))
  dsimp at eq₁ eq₂ eq ⊢
  simp only [reassoc_of% eq, ← Functor.whiskerLeft_comp]
  congr 2
  simp only [← cancel_epi ((compULiftYonedaIsoULiftYonedaCompLan F).hom.app x.unop.1.unop),
    NatTrans.naturality]
  apply uliftYonedaEquiv.injective
  simp [eq₁, eq₂, uliftYonedaEquiv_apply]

end compULiftYonedaIsoULiftYonedaCompLan

variable [∀ (P : Cᵒᵖ ⥤ Type max w v₁ v₂), F.op.HasLeftKanExtension P]

noncomputable instance (Φ : StructuredArrow (F ⋙ uliftYoneda.{max w v₁})
    ((Functor.whiskeringLeft C (Cᵒᵖ ⥤ Type max w v₁ v₂)
      (Dᵒᵖ ⥤ Type max w v₁ v₂)).obj uliftYoneda.{max w v₂})) :
    Unique (Functor.LeftExtension.mk F.op.lan
      (compULiftYonedaIsoULiftYonedaCompLan.{w} F).hom ⟶ Φ) where
  default := compULiftYonedaIsoULiftYonedaCompLan.extensionHom Φ
  uniq _ := compULiftYonedaIsoULiftYonedaCompLan.hom_ext _ _

/-- Given a functor `F : C ⥤ D`, `F.op.lan : (Cᵒᵖ ⥤ Type v₁) ⥤ Dᵒᵖ ⥤ Type v₁` is the
left Kan extension of `F ⋙ yoneda : C ⥤ Dᵒᵖ ⥤ Type v₁` along `yoneda : C ⥤ Cᵒᵖ ⥤ Type v₁`. -/
instance : F.op.lan.IsLeftKanExtension (compULiftYonedaIsoULiftYonedaCompLan.{w} F).hom :=
  ⟨⟨Limits.IsInitial.ofUnique _⟩⟩

end

/-- For a presheaf `P`, consider the forgetful functor from the category of representable
    presheaves over `P` to the category of presheaves. There is a tautological cocone over this
    functor whose leg for a natural transformation `V ⟶ P` with `V` representable is just that
    natural transformation. (In this version, we allow the presheaf `P` to have values in
    a larger universe.) -/
@[simps]
def tautologicalCocone' (P : Cᵒᵖ ⥤ Type max w v₁) :
    Cocone (CostructuredArrow.proj uliftYoneda.{w} P ⋙ uliftYoneda.{w}) where
  pt := P
  ι := { app X := X.hom }

/-- The tautological cocone with point `P` is a colimit cocone, exhibiting `P` as a colimit of
    representables. (In this version, we allow the presheaf `P` to have values in
    a larger universe.)

    Proposition 2.6.3(i) in [Kashiwara2006] -/
def isColimitTautologicalCocone' (P : Cᵒᵖ ⥤ Type max w v₁) :
    IsColimit (tautologicalCocone'.{w} P) :=
  (IsColimit.whiskerEquivalenceEquiv
    (CategoryOfElements.costructuredArrowULiftYonedaEquivalence.{w} P)).2
      (colimitOfRepresentable.{w} P)


/-- For a presheaf `P`, consider the forgetful functor from the category of representable
    presheaves over `P` to the category of presheaves. There is a tautological cocone over this
    functor whose leg for a natural transformation `V ⟶ P` with `V` representable is just that
    natural transformation. -/
@[simps]
def tautologicalCocone (P : Cᵒᵖ ⥤ Type v₁) :
    Cocone (CostructuredArrow.proj yoneda P ⋙ yoneda) where
  pt := P
  ι := { app X := X.hom }

/-- The tautological cocone with point `P` is a colimit cocone, exhibiting `P` as a colimit of
    representables.

    Proposition 2.6.3(i) in [Kashiwara2006] -/
def isColimitTautologicalCocone (P : Cᵒᵖ ⥤ Type v₁) :
    IsColimit (tautologicalCocone P) :=
  let e : functorToRepresentables.{v₁} P ≅
    ((CategoryOfElements.costructuredArrowYonedaEquivalence P).functor ⋙
      CostructuredArrow.proj yoneda P ⋙ yoneda) :=
    NatIso.ofComponents (fun e ↦ NatIso.ofComponents (fun X ↦ Equiv.ulift.toIso))
  (IsColimit.whiskerEquivalenceEquiv
    (CategoryOfElements.costructuredArrowYonedaEquivalence P)).2
      ((IsColimit.precomposeHomEquiv e _).1 (colimitOfRepresentable.{v₁} P))

variable {I : Type v₁} [SmallCategory I] (F : I ⥤ C)

set_option backward.isDefEq.respectTransparency false in
/-- Given a functor `F : I ⥤ C`, a cocone `c` on `F ⋙ yoneda : I ⥤ Cᵒᵖ ⥤ Type v₁` induces a
    functor `I ⥤ CostructuredArrow yoneda c.pt` which maps `i : I` to the leg
    `yoneda.obj (F.obj i) ⟶ c.pt`. If `c` is a colimit cocone, then that functor is
    final.

    Proposition 2.6.3(ii) in [Kashiwara2006] -/
theorem final_toCostructuredArrow_comp_pre {c : Cocone (F ⋙ yoneda)} (hc : IsColimit c) :
    Functor.Final (c.toCostructuredArrow ⋙ CostructuredArrow.pre F yoneda c.pt) := by
  apply Functor.final_of_isTerminal_colimit_comp_yoneda
  suffices IsTerminal (colimit ((c.toCostructuredArrow ⋙ CostructuredArrow.pre F yoneda c.pt) ⋙
      CostructuredArrow.toOver yoneda c.pt)) by
    apply IsTerminal.isTerminalOfObj (overEquivPresheafCostructuredArrow c.pt).inverse
    apply IsTerminal.ofIso this
    refine ?_ ≪≫ (preservesColimitIso (overEquivPresheafCostructuredArrow c.pt).inverse _).symm
    apply HasColimit.isoOfNatIso
    exact Functor.isoWhiskerLeft _
      (CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow c.pt).isoCompInverse
  apply IsTerminal.ofIso Over.mkIdTerminal
  let isc : IsColimit ((Over.forget _).mapCocone _) := isColimitOfPreserves _
    (colimit.isColimit ((c.toCostructuredArrow ⋙ CostructuredArrow.pre F yoneda c.pt) ⋙
      CostructuredArrow.toOver yoneda c.pt))
  exact Over.isoMk (hc.coconePointUniqueUpToIso isc) (hc.hom_ext fun i => by simp)

end Presheaf

namespace Functor.Elements

variable [LocallySmall.{w} C] (F : C ⥤ Type w)

set_option backward.isDefEq.respectTransparency false in
/-- If `F : C ⥤ Type w` and `C` is locally `w`-small, then for any `X : C`,
this is the colimit cocone which identifies `F.obj X` to the colimit of
`(CategoryOfElements.π F).op ⋙ shrinkYoneda.obj X`. -/
@[simps]
noncomputable def coconeπOpCompShrinkYonedaObj (X : C) :
    Cocone ((CategoryOfElements.π F).op ⋙ shrinkYoneda.{w}.obj X) where
  pt := F.obj X
  ι.app u := ↾fun t ↦ F.map (shrinkYonedaObjObjEquiv t) u.unop.snd
  ι.naturality u₁ u₂ g := by
    ext f
    obtain ⟨f, rfl⟩ := shrinkYonedaObjObjEquiv.symm.surjective f
    simp [shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm.{w}]

set_option backward.isDefEq.respectTransparency false in
/-- If `F : C ⥤ Type w` and `C` is locally `w`-small, then for any `X : C`,
`F.obj X` identifies to the colimit of
`(CategoryOfElements.π F).op ⋙ shrinkYoneda.obj X`. -/
noncomputable def isColimitCoconeπOpCompShrinkYonedaObj (X : C) :
    IsColimit (coconeπOpCompShrinkYonedaObj F X) := by
  refine Nonempty.some ((Types.isColimit_iff_coconeTypesIsColimit _).2
    ⟨?_, fun x ↦ ?_⟩)
  · let G := (CategoryOfElements.π F).op ⋙ shrinkYoneda.{w}.obj X
    let c := G.coconeTypesEquiv.symm (coconeπOpCompShrinkYonedaObj F X)
    have (u : G.ColimitType) (x : F.obj X) (h : G.descColimitType c u = x) :
        G.ιColimitType (op (elementsMk _ _ x))
          (shrinkYonedaObjObjEquiv.symm (𝟙 X)) = u := by
      obtain ⟨⟨u⟩, v, rfl⟩ := Functor.ιColimitType_jointly_surjective _ u
      obtain ⟨v, rfl⟩ := shrinkYonedaObjObjEquiv.symm.surjective v
      dsimp [c] at v h
      simp only [Equiv.apply_symm_apply] at h
      rw [← G.ιColimitType_map (show u ⟶ F.elementsMk _ x from ⟨v, h⟩).op]
      simp [G, shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm.{w}]
    intro u₁ u₂ hu
    generalize hx₁ : G.descColimitType c u₁ = x
    have hx₂ : G.descColimitType c u₂ = x := by rw [← hx₁]; exact hu.symm
    rw [← this _ _ hx₁, ← this _ _ hx₂]
  · exact ⟨Functor.ιColimitType _ (op (elementsMk _ _ x))
      (shrinkYonedaObjObjEquiv.symm (𝟙 X)), by simp⟩

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma shrinkYoneda_map_app_coconeπOpCompShrinkYonedaObj_ι_app
    {X₁ X₂ : C} (f : X₁ ⟶ X₂) (u : F.Elements) :
    dsimp% (shrinkYoneda.{w}.map f).app (op u.fst) ≫
      (coconeπOpCompShrinkYonedaObj F X₂).ι.app (op u) =
    (coconeπOpCompShrinkYonedaObj F X₁).ι.app (op u) ≫ F.map f := by
  ext g
  obtain ⟨g, rfl⟩ := shrinkYonedaObjObjEquiv.symm.surjective g
  simp [shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm.{w}]

set_option backward.isDefEq.respectTransparency false in
/-- If `C` is a locally `w`-small category, this is a (colimit) cocone
expressing `F : C ⥤ Type w` as a colimit of corepresentable functors. -/
noncomputable def coconeπOpCompShrinkYonedaFlip :
    Cocone ((CategoryOfElements.π F).op ⋙ shrinkYoneda.{w}.flip) where
  pt := F
  ι.app u :=
    { app X := (coconeπOpCompShrinkYonedaObj F X).ι.app u
      naturality {X Y} f := by
        ext x
        obtain ⟨x, rfl⟩ := shrinkYonedaObjObjEquiv.symm.surjective x
        simp }
  ι.naturality u v g := by
    ext X x
    obtain ⟨x, rfl⟩ := shrinkYonedaObjObjEquiv.symm.surjective x
    simp [← shrinkYonedaObjObjEquiv_symm_comp.{w}]

/-- If `F : C ⥤ Type w` and `C` is locally `w`-small, then `F` identifies to the colimit
of `(CategoryOfElements.π F).op ⋙ shrinkYoneda.{w}.flip`. -/
noncomputable def isColimitCoconeπOpCompShrinkYonedaFlip :
    IsColimit (coconeπOpCompShrinkYonedaFlip F) :=
  evaluationJointlyReflectsColimits _ (isColimitCoconeπOpCompShrinkYonedaObj F)

set_option backward.isDefEq.respectTransparency false in
/-- If `F : C ⥤ Type w` and `C` is locally `w`-small, then `F` identifies to the composition
`shrinkYoneda ⋙ (Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π F).op ⋙ colim`. -/
noncomputable def shrinkYonedaCompWhiskeringLeftObjπCompColimIso
    [HasColimitsOfShape F.Elementsᵒᵖ (Type w)] :
    shrinkYoneda.{w} ⋙
      (Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π F).op ⋙ colim ≅ F :=
  NatIso.ofComponents (fun X ↦
    IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
      (isColimitCoconeπOpCompShrinkYonedaObj F X)) (fun {X₁ X₂} f ↦ colimit.hom_ext (by
        cat_disch))

set_option backward.isDefEq.respectTransparency false in
lemma shrinkYonedaCompWhiskeringLeftObjπCompColimIso_inv_app_apply
    [HasColimitsOfShape F.Elementsᵒᵖ (Type w)] (u : F.Elements) :
      (shrinkYonedaCompWhiskeringLeftObjπCompColimIso F).inv.app _ u.snd =
      (colimit.ι ((CategoryOfElements.π F).op ⋙ shrinkYoneda.{w}.obj u.fst) (op u)
        (shrinkYonedaObjObjEquiv.symm (𝟙 _))) := by
  have :
      (coconeπOpCompShrinkYonedaObj F u.fst).ι.app (op u) ≫
        (shrinkYonedaCompWhiskeringLeftObjπCompColimIso F).inv.app u.fst =
      colimit.ι ((CategoryOfElements.π F).op ⋙ shrinkYoneda.{w}.obj u.fst) (op u) :=
    IsColimit.comp_coconePointUniqueUpToIso_inv (colimit.isColimit _) _ (op u)
  simpa using ConcreteCategory.congr_hom this (shrinkYonedaObjObjEquiv.symm (𝟙 _))

set_option backward.isDefEq.respectTransparency false in
/-- The object of the category of elements `shrinkYoneda.{w}.flip.obj (op X)`
corresponding to the identity of `X` is initial. -/
noncomputable def isInitialElementsMkShrinkYonedaObjObjEquivId (X : C) :
    IsInitial (Functor.elementsMk (shrinkYoneda.{w}.flip.obj (op X)) X
      (shrinkYonedaObjObjEquiv.symm (𝟙 X))) :=
  IsInitial.ofUniqueHom (fun u ↦ ⟨shrinkYonedaObjObjEquiv.{w} u.2, by
    simp [shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm.{w}]⟩) (by
    rintro u ⟨m, hm⟩
    ext
    simp [← hm, shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm.{w}])

instance (X : C) : HasInitial (shrinkYoneda.{w}.flip.obj (op X)).Elements :=
  (isInitialElementsMkShrinkYonedaObjObjEquivId X).hasInitial

end Functor.Elements

end CategoryTheory
