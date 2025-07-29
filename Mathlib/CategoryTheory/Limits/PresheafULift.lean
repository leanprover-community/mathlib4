/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Joël Riou
-/
import Mathlib.CategoryTheory.Comma.Presheaf.Basic
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Limits.Over

/-!
# Colimit of representables

This file constructs an adjunction `Presheaf.yonedaAdjunction` between `(Cᵒᵖ ⥤ Type u)` and
`ℰ` given a functor `A : C ⥤ ℰ`, where the right adjoint `restrictedYoneda`
sends `(E : ℰ)` to `c ↦ (A.obj c ⟶ E)`, and the left adjoint `(Cᵒᵖ ⥤ Type v₁) ⥤ ℰ`
is a pointwise left Kan extension of `A` along the Yoneda embedding, which
exists provided `ℰ` has colimits)

We also show that every presheaf is a colimit of representables. This result
is also known as the density theorem, the co-Yoneda lemma and
the Ninja Yoneda lemma. Two formulations are given:
* `colimitOfRepresentable` uses the category of elements of a functor to types;
* `isColimitTautologicalCocone` uses the category of costructured arrows.

In the lemma `isLeftKanExtension_along_yoneda_iff`, we show that
if `L : (Cᵒᵖ ⥤ Type v₁) ⥤ ℰ)` and `α : A ⟶ yoneda ⋙ L`, then
`α` makes `L` the left Kan extension of `L` along yoneda if and only if
`α` is an isomorphism (i.e. `L` extends `A`) and `L` preserves colimits.
`uniqueExtensionAlongYoneda` shows `yoneda.leftKanExtension A` is unique amongst
functors preserving colimits with this property, establishing the
presheaf category as the free cocompletion of a category.

Given a functor `F : C ⥤ D`, we also show construct an
isomorphism `compYonedaIsoYonedaCompLan : F ⋙ yoneda ≅ yoneda ⋙ F.op.lan`, and
show that it makes `F.op.lan` a left Kan extension of `F ⋙ yoneda`.

## Tags
colimit, representable, presheaf, free cocompletion

## References
* [S. MacLane, I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]
* https://ncatlab.org/nlab/show/Yoneda+extension
-/

namespace CategoryTheory

open Category Limits Opposite

universe w v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]

namespace Presheaf

variable {ℰ : Type u₂} [Category.{v₂} ℰ] (A : C ⥤ ℰ)

/--
The functor taking `(E : ℰ) (c : Cᵒᵖ)` to the homset `(A.obj C ⟶ E)`. It is shown in `L_adjunction`
that this functor has a left adjoint (provided `E` has colimits) given by taking colimits over
categories of elements.
In the case where `ℰ = Cᵒᵖ ⥤ Type u` and `A = yoneda`, this functor is isomorphic to the identity.

Defined as in [MM92], Chapter I, Section 5, Theorem 2.
-/
@[simps! obj_map map_app]
def restrictedULiftYoneda : ℰ ⥤ Cᵒᵖ ⥤ Type (max w v₂) :=
    uliftYoneda.{w} ⋙ (Functor.whiskeringLeft _ _ _).obj A.op

/-- Auxiliary definition for `restrictedULiftYonedaHomEquiv`. -/
def restrictedULiftYonedaHomEquiv' (P : Cᵒᵖ ⥤ Type (max w v₁ v₂)) (E : ℰ) :
    (CostructuredArrow.proj uliftYoneda.{max w v₂} P ⋙ A ⟶
      (Functor.const (CostructuredArrow uliftYoneda.{max w v₂} P)).obj E) ≃
      (P ⟶ (restrictedULiftYoneda.{max w v₁} A).obj E) where
  toFun f :=
    { app _ x := ULift.up (f.app (CostructuredArrow.mk (uliftYonedaEquiv.symm x)))
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
      naturality := by
        sorry }
  left_inv f := by
    ext X
    let e : CostructuredArrow.mk
      (uliftYonedaEquiv.{max w v₂}.symm (X.hom.app (op X.left) ⟨𝟙 X.left⟩)) ≅ X :=
        CostructuredArrow.isoMk (Iso.refl _) (by
          ext Y x
          dsimp
          rw [← FunctorToTypes.naturality]
          simp [uliftYoneda]
          rfl )
    simpa [e] using f.naturality e.inv
  right_inv g := by
    ext X x
    apply ULift.down_injective
    dsimp
    rw [uliftYonedaEquiv_comp, Equiv.apply_symm_apply]

@[reassoc]
lemma restrictedULiftYonedaHomEquiv'_symm_naturality_right (P : Cᵒᵖ ⥤ Type (max w v₁ v₂)) {E E' : ℰ}
    (g : E ⟶ E') (f : (P ⟶ (restrictedULiftYoneda.{max w v₁} A).obj E)) :
    (restrictedULiftYonedaHomEquiv' A P E').symm (f ≫ (restrictedULiftYoneda A).map g) =
      (restrictedULiftYonedaHomEquiv' A P E).symm f ≫ (Functor.const _ ).map g := by
  rfl

@[reassoc]
lemma restrictedULiftYonedaHomEquiv'_symm_app_naturality_left
    {P Q : Cᵒᵖ ⥤ Type (max w v₁ v₂)} (f : P ⟶ Q) (E : ℰ)
    (g : (Q ⟶ (restrictedULiftYoneda.{max w v₁} A).obj E))
    (p : CostructuredArrow uliftYoneda.{max w v₂} P) :
    ((restrictedULiftYonedaHomEquiv' A P E).symm (f ≫ g)).app p =
      ((restrictedULiftYonedaHomEquiv' A Q E).symm g).app
        ((CostructuredArrow.map f).obj p) :=
  rfl

section

variable (P : ℰᵒᵖ ⥤ Type (max w v₁ v₂))

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

/-- If `L : (Cᵒᵖ ⥤ Type v₁) ⥤ ℰ` is a pointwise left Kan extension
of a functor `A : C ⥤ ℰ` along the Yoneda embedding,
then `L` is a left adjoint of `restrictedYoneda A : ℰ ⥤ Cᵒᵖ ⥤ Type v₁` -/
noncomputable def uliftYonedaAdjunction : L ⊣ restrictedULiftYoneda.{max w v₁} A :=
  Adjunction.mkOfHomEquiv
    { homEquiv := restrictedULiftYonedaHomEquiv L α
      homEquiv_naturality_left_symm := fun {P Q X} f g => by
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
      homEquiv_naturality_right := fun {P X Y} f g => by
        have := @IsColimit.homEquiv_symm_naturality (h :=
          Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension L α P)
        dsimp at this
        apply (restrictedULiftYonedaHomEquiv L α P Y).symm.injective
        apply (Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension L α P).hom_ext
        intro
        simp [restrictedULiftYonedaHomEquiv,
          restrictedULiftYonedaHomEquiv'_symm_naturality_right, this] }

include α in
/-- Any left Kan extension along the Yoneda embedding preserves colimits. -/
lemma preservesColimitsOfSize_of_isLeftKanExtension :
    PreservesColimitsOfSize.{v₃, u₃} L :=
  (uliftYonedaAdjunction L α).leftAdjoint_preservesColimits

lemma isIso_of_isLeftKanExtension : IsIso α :=
  (Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension _ α).isIso_hom

variable (A)

/-- See Property 2 of https://ncatlab.org/nlab/show/Yoneda+extension#properties. -/
noncomputable instance preservesColimitsOfSize_leftKanExtension :
    PreservesColimitsOfSize.{v₃, u₃} (uliftYoneda.{max w v₂}.leftKanExtension A) :=
  (uliftYonedaAdjunction _ (uliftYoneda.leftKanExtensionUnit A)).leftAdjoint_preservesColimits

instance : IsIso (uliftYoneda.{max w v₂}.leftKanExtensionUnit A) :=
  isIso_of_isLeftKanExtension _ (uliftYoneda.leftKanExtensionUnit A)

/-- A pointwise left Kan extension along the Yoneda embedding is an extension. -/
noncomputable def isExtensionAlongULiftYoneda :
    uliftYoneda.{max w v₂} ⋙ uliftYoneda.leftKanExtension A ≅ A :=
  (asIso (uliftYoneda.leftKanExtensionUnit A)).symm

end

/-- A functor to the presheaf category in which everything in the image is representable (witnessed
by the fact that it factors through the yoneda embedding).
`coconeOfRepresentable` gives a cocone for this functor which is a colimit and has point `P`.
-/
@[simps! obj map]
def functorToRepresentables (P : Cᵒᵖ ⥤ Type max w v₁) :
    P.Elementsᵒᵖ ⥤ Cᵒᵖ ⥤ Type (max w v₁) :=
  (CategoryOfElements.π P).leftOp ⋙ uliftYoneda.{w}

/-- This is a cocone with point `P` for the functor `functorToRepresentables P`. It is shown in
`colimitOfRepresentable P` that this cocone is a colimit: that is, we have exhibited an arbitrary
presheaf `P` as a colimit of representables.

The construction of [MM92], Chapter I, Section 5, Corollary 3.
-/
@[simps]
noncomputable def coconeOfRepresentable (P : Cᵒᵖ ⥤ Type max w v₁) :
    Cocone (functorToRepresentables P) where
  pt := P
  ι :=
    { app x := uliftYonedaEquiv.symm x.unop.2
      naturality := fun {x₁ x₂} f => by
        dsimp
        rw [comp_id, ← uliftYonedaEquiv_symm_map, f.unop.2] }

/-- The legs of the cocone `coconeOfRepresentable` are natural in the choice of presheaf. -/
theorem coconeOfRepresentable_naturality
    {P₁ P₂ : Cᵒᵖ ⥤ Type max w v₁} (α : P₁ ⟶ P₂) (j : P₁.Elementsᵒᵖ) :
    (coconeOfRepresentable P₁).ι.app j ≫ α =
      (coconeOfRepresentable P₂).ι.app ((CategoryOfElements.map α).op.obj j) := by
  ext T f
  simp [uliftYonedaEquiv, FunctorToTypes.naturality]

/-- The cocone with point `P` given by `coconeOfRepresentable` is a colimit:
that is, we have exhibited an arbitrary presheaf `P` as a colimit of representables.

The result of [MM92], Chapter I, Section 5, Corollary 3.
-/
noncomputable def colimitOfRepresentable (P : Cᵒᵖ ⥤ Type max w v₁) :
    IsColimit (coconeOfRepresentable P) where
  desc s :=
    { app X x := uliftYonedaEquiv (s.ι.app (Opposite.op (Functor.elementsMk P X x)))
      naturality X Y f := by
        ext x
        have := s.w (Quiver.Hom.op (CategoryOfElements.homMk (P.elementsMk X x)
          (P.elementsMk Y (P.map f x)) f rfl))
        dsimp at this x ⊢
        rw [← this, uliftYonedaEquiv_comp]
        dsimp
        rw [uliftYonedaEquiv_apply, ← FunctorToTypes.naturality,
          uliftYonedaEquiv_uliftYoneda_map]
        simp [uliftYoneda] }
  fac s j := by
    ext X x
    let φ : j.unop ⟶ (Functor.elementsMk P _
      ((uliftYonedaEquiv.symm (unop j).snd).app X x)) := ⟨x.down.op, rfl⟩
    have := s.w φ.op
    dsimp [φ] at this x ⊢
    rw [← this, uliftYonedaEquiv_apply]
    dsimp [uliftYoneda]
    rw [id_comp]
  uniq s m hm := by
    ext X x
    dsimp at hm ⊢
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
      (Cocones.ext (Iso.refl _))

lemma isLeftKanExtension_of_preservesColimits
    (L : (Cᵒᵖ ⥤ Type max w v₁ v₂) ⥤ ℰ) (e : A ≅ uliftYoneda.{max w v₂} ⋙ L)
    [PreservesColimitsOfSize.{v₁, max w u₁ v₁ v₂} L] :
    L.IsLeftKanExtension e.hom := by
  rw [isLeftKanExtension_along_uliftYoneda_iff]
  exact ⟨inferInstance, ⟨inferInstance⟩⟩

end

/-- Show that `yoneda.leftKanExtension A` is the unique colimit-preserving
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

instance (X : C) (Y : F.op.LeftExtension (yoneda.obj X)) :
    Unique (Functor.LeftExtension.mk _ (yonedaMap F X) ⟶ Y) where
  default := StructuredArrow.homMk
      (yonedaEquiv.symm (yonedaEquiv (F := F.op.comp Y.right) Y.hom)) (by
        ext Z f
        simpa using congr_fun (Y.hom.naturality f.op).symm (𝟙 _))
  uniq φ := by
    ext1
    apply yonedaEquiv.injective
    simp [← StructuredArrow.w φ, yonedaEquiv]

/-- Given `F : C ⥤ D` and `X : C`, `yoneda.obj (F.obj X) : Dᵒᵖ ⥤ Type _` is the
left Kan extension of `yoneda.obj X : Cᵒᵖ ⥤ Type _` along `F.op`. -/
instance (X : C) : (yoneda.obj (F.obj X)).IsLeftKanExtension (yonedaMap F X) :=
  ⟨⟨Limits.IsInitial.ofUnique _⟩⟩

end

section

variable {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)

instance (X : C) (Y : F.op.LeftExtension (uliftYoneda.{max w v₂}.obj X)) :
    Unique (Functor.LeftExtension.mk _ (uliftYonedaMap.{w} F X) ⟶ Y) where
  default := StructuredArrow.homMk
    (uliftYonedaEquiv.symm (uliftYonedaEquiv (F := F.op ⋙ Y.right) Y.hom)) (by
      ext Z ⟨f⟩
      dsimp
      rw [uliftYonedaMap_app_apply]
      simpa [uliftYonedaEquiv, uliftYoneda] using
        congr_fun (Y.hom.naturality f.op).symm (ULift.up (𝟙 _)) )
  uniq φ := by
    ext : 1
    apply uliftYonedaEquiv.injective
    simp [← StructuredArrow.w φ, uliftYonedaEquiv, uliftYonedaMap]

/-- Given `F : C ⥤ D` and `X : C`, `uliftYoneda.obj (F.obj X) : Dᵒᵖ ⥤ Type (max w v₁ v₂)` is the
left Kan extension of `uliftYoneda.obj X : Cᵒᵖ ⥤ Type (max w v₁ v₂)` along `F.op`. -/
instance (X : C) : (uliftYoneda.{max w v₁}.obj (F.obj X)).IsLeftKanExtension
    (uliftYonedaMap.{w} F X) :=
  ⟨⟨Limits.IsInitial.ofUnique _⟩⟩

section
variable [∀ (P : Cᵒᵖ ⥤ Type max w v₁ v₂), F.op.HasLeftKanExtension P]

/-- `F ⋙ uliftYoneda` is naturally isomorphic to `uliftYoneda ⋙ F.op.lan`. -/
noncomputable def compULiftYonedaIsoULiftYonedaCompLan :
    F ⋙ uliftYoneda.{max w v₁} ≅ uliftYoneda.{max w v₂} ⋙ F.op.lan :=
  NatIso.ofComponents (fun X => Functor.leftKanExtensionUnique _
    (uliftYonedaMap.{w} F X) (F.op.lan.obj _) (F.op.lanUnit.app (uliftYoneda.obj X)))
    (fun {X Y} f => by
      apply uliftYonedaEquiv.injective
      have eq₁ := congr_fun
        ((uliftYoneda.{max w v₁}.obj (F.obj Y)).descOfIsLeftKanExtension_fac_app
        (uliftYonedaMap F Y) (F.op.lan.obj (uliftYoneda.obj Y))
          (F.op.lanUnit.app (uliftYoneda.obj Y)) _) ⟨f⟩
      have eq₂ := congr_fun
        (((uliftYoneda.{max w v₁}.obj (F.obj X)).descOfIsLeftKanExtension_fac_app
        (uliftYonedaMap F X) (F.op.lan.obj (uliftYoneda.obj X))
          (F.op.lanUnit.app (uliftYoneda.obj X))) _) ⟨𝟙 _⟩
      have eq₃ := congr_fun (congr_app (F.op.lanUnit.naturality
        (uliftYoneda.{max w v₂}.map f)) _) ⟨𝟙 _⟩
      dsimp [uliftYoneda, uliftYonedaMap, uliftYonedaEquiv,
        Functor.leftKanExtensionUnique] at eq₁ eq₂ eq₃ ⊢
      simp only [Functor.map_id] at eq₂
      simp only [id_comp] at eq₃
      simp [eq₁, eq₂, eq₃])

@[simp]
lemma compULiftYonedaIsoULiftYonedaCompLan_inv_app_app_apply_eq_id (X : C) :
    ((compULiftYonedaIsoULiftYonedaCompLan.{w} F).inv.app X).app (op (F.obj X))
          ((F.op.lanUnit.app ((uliftYoneda.{max w v₂}).obj X)).app (op X)
        (ULift.up (𝟙 X))) = ULift.up (𝟙 (F.obj X)) :=
  (congr_fun (Functor.descOfIsLeftKanExtension_fac_app _
    (F.op.lanUnit.app ((uliftYoneda.{max w v₂}).obj X)) _
    (uliftYonedaMap.{w} F X) (op X)) (ULift.up (𝟙 X))).trans (by simp [uliftYonedaMap])

end
#exit

namespace compYonedaIsoYonedaCompLan

variable {F}

section

variable {X : C} {G : (Cᵒᵖ ⥤ Type v₁) ⥤ Dᵒᵖ ⥤ Type v₁} (φ : F ⋙ yoneda ⟶ yoneda ⋙ G)

/-- Auxiliary definition for `presheafHom`. -/
def coconeApp {P : Cᵒᵖ ⥤ Type v₁} (x : P.Elements) :
    yoneda.obj x.1.unop ⟶ F.op ⋙ G.obj P := yonedaEquiv.symm
      ((G.map (yonedaEquiv.symm x.2)).app _ ((φ.app x.1.unop).app _ (𝟙 _)))

@[reassoc (attr := simp)]
lemma coconeApp_naturality {P : Cᵒᵖ ⥤ Type v₁} {x y : P.Elements} (f : x ⟶ y) :
    yoneda.map f.1.unop ≫ coconeApp φ x = coconeApp φ y := by
  have eq₁ : yoneda.map f.1.unop ≫ yonedaEquiv.symm x.2 = yonedaEquiv.symm y.2 :=
    yonedaEquiv.injective
      (by simpa only [Equiv.apply_symm_apply, ← yonedaEquiv_naturality] using f.2)
  have eq₂ := congr_fun ((G.map (yonedaEquiv.symm x.2)).naturality (F.map f.1.unop).op)
    ((φ.app x.1.unop).app _ (𝟙 _))
  have eq₃ := congr_fun (congr_app (φ.naturality f.1.unop) _) (𝟙 _)
  have eq₄ := congr_fun ((φ.app x.1.unop).naturality (F.map f.1.unop).op)
  dsimp at eq₂ eq₃ eq₄
  apply yonedaEquiv.injective
  dsimp only [coconeApp]
  rw [Equiv.apply_symm_apply, ← yonedaEquiv_naturality, Equiv.apply_symm_apply]
  simp [← eq₁, ← eq₂, ← eq₃, ← eq₄, Functor.map_comp, FunctorToTypes.comp, id_comp, comp_id]

/-- Given functors `F : C ⥤ D` and `G : (Cᵒᵖ ⥤ Type v₁) ⥤ (Dᵒᵖ ⥤ Type v₁)`, and
a natural transformation `φ : F ⋙ yoneda ⟶ yoneda ⋙ G`, this is the
(natural) morphism `P ⟶ F.op ⋙ G.obj P` for all `P : Cᵒᵖ ⥤ Type v₁` that is
determined by `φ`. -/
noncomputable def presheafHom (P : Cᵒᵖ ⥤ Type v₁) : P ⟶ F.op ⋙ G.obj P :=
  (colimitOfRepresentable P).desc
    (Cocone.mk _ { app := fun x => coconeApp φ x.unop })

lemma yonedaEquiv_ι_presheafHom (P : Cᵒᵖ ⥤ Type v₁) {X : C} (f : yoneda.obj X ⟶ P) :
    yonedaEquiv (f ≫ presheafHom φ P) =
      (G.map f).app (Opposite.op (F.obj X)) ((φ.app X).app _ (𝟙 _)) := by
  obtain ⟨x, rfl⟩ := yonedaEquiv.symm.surjective f
  erw [(colimitOfRepresentable P).fac _ (Opposite.op (P.elementsMk _ x))]
  dsimp only [coconeApp]
  apply Equiv.apply_symm_apply

lemma yonedaEquiv_presheafHom_yoneda_obj (X : C) :
    yonedaEquiv (presheafHom φ (yoneda.obj X)) =
      ((φ.app X).app (F.op.obj (Opposite.op X)) (𝟙 _)) := by
  simpa using yonedaEquiv_ι_presheafHom φ (yoneda.obj X) (𝟙 _)

@[reassoc (attr := simp)]
lemma presheafHom_naturality {P Q : Cᵒᵖ ⥤ Type v₁} (f : P ⟶ Q) :
    presheafHom φ P ≫ whiskerLeft F.op (G.map f) = f ≫ presheafHom φ Q :=
  hom_ext_yoneda (fun X p => yonedaEquiv.injective (by
    rw [← assoc p f, yonedaEquiv_ι_presheafHom, ← assoc,
      yonedaEquiv_comp, yonedaEquiv_ι_presheafHom,
      whiskerLeft_app, Functor.map_comp, FunctorToTypes.comp]
    dsimp))

variable [∀ (P : Cᵒᵖ ⥤ Type v₁), F.op.HasLeftKanExtension P]

/-- Given functors `F : C ⥤ D` and `G : (Cᵒᵖ ⥤ Type v₁) ⥤ (Dᵒᵖ ⥤ Type v₁)`,
and a natural transformation `φ : F ⋙ yoneda ⟶ yoneda ⋙ G`, this is
the canonical natural transformation `F.op.lan ⟶ G`, which is part of the
that `F.op.lan : (Cᵒᵖ ⥤ Type v₁) ⥤ Dᵒᵖ ⥤ Type v₁` is the left Kan extension
of `F ⋙ yoneda : C ⥤ Dᵒᵖ ⥤ Type v₁` along `yoneda : C ⥤ Cᵒᵖ ⥤ Type v₁`. -/
noncomputable def natTrans : F.op.lan ⟶ G where
  app P := (F.op.lan.obj P).descOfIsLeftKanExtension (F.op.lanUnit.app P) _ (presheafHom φ P)
  naturality {P Q} f := by
    apply (F.op.lan.obj P).hom_ext_of_isLeftKanExtension (F.op.lanUnit.app P)
    have eq := F.op.lanUnit.naturality f
    dsimp at eq ⊢
    rw [Functor.descOfIsLeftKanExtension_fac_assoc, ← reassoc_of% eq,
      Functor.descOfIsLeftKanExtension_fac, presheafHom_naturality]

lemma natTrans_app_yoneda_obj (X : C) : (natTrans φ).app (yoneda.obj X) =
    (compYonedaIsoYonedaCompLan F).inv.app X ≫ φ.app X := by
  dsimp [natTrans]
  apply (F.op.lan.obj (yoneda.obj X)).hom_ext_of_isLeftKanExtension (F.op.lanUnit.app _)
  rw [Functor.descOfIsLeftKanExtension_fac]
  apply yonedaEquiv.injective
  rw [yonedaEquiv_presheafHom_yoneda_obj]
  exact congr_arg _ (compYonedaIsoYonedaCompLan_inv_app_app_apply_eq_id F X).symm

end

variable [∀ (P : Cᵒᵖ ⥤ Type v₁), F.op.HasLeftKanExtension P]

/-- Given a functor `F : C ⥤ D`, this definition is part of the verification that
`Functor.LeftExtension.mk F.op.lan (compYonedaIsoYonedaCompLan F).hom`
is universal, i.e. that  `F.op.lan : (Cᵒᵖ ⥤ Type v₁) ⥤ Dᵒᵖ ⥤ Type v₁` is the
left Kan extension of `F ⋙ yoneda : C ⥤ Dᵒᵖ ⥤ Type v₁`
along `yoneda : C ⥤ Cᵒᵖ ⥤ Type v₁`. -/
noncomputable def extensionHom (Φ : yoneda.LeftExtension (F ⋙ yoneda)) :
    Functor.LeftExtension.mk F.op.lan (compYonedaIsoYonedaCompLan F).hom ⟶ Φ :=
  StructuredArrow.homMk (natTrans Φ.hom) (by
    ext X : 2
    dsimp
    rw [natTrans_app_yoneda_obj, Iso.hom_inv_id_app_assoc])

@[ext]
lemma hom_ext {Φ : yoneda.LeftExtension (F ⋙ yoneda)}
    (f g : Functor.LeftExtension.mk F.op.lan (compYonedaIsoYonedaCompLan F).hom ⟶ Φ) :
    f = g := by
  ext P : 3
  apply (F.op.lan.obj P).hom_ext_of_isLeftKanExtension (F.op.lanUnit.app P)
  apply (colimitOfRepresentable P).hom_ext
  intro x
  have eq := F.op.lanUnit.naturality (yonedaEquiv.symm x.unop.2)
  have eq₁ := congr_fun (congr_app (congr_app (StructuredArrow.w f) x.unop.1.unop)
    (F.op.obj x.unop.1)) (𝟙 _)
  have eq₂ := congr_fun (congr_app (congr_app (StructuredArrow.w g) x.unop.1.unop)
    (F.op.obj x.unop.1)) (𝟙 _)
  dsimp at eq₁ eq₂ eq ⊢
  simp only [reassoc_of% eq, ← whiskerLeft_comp]
  congr 2
  simp only [← cancel_epi ((compYonedaIsoYonedaCompLan F).hom.app x.unop.1.unop),
    NatTrans.naturality]
  apply yonedaEquiv.injective
  dsimp [yonedaEquiv_apply]
  rw [eq₁, eq₂]

end compYonedaIsoYonedaCompLan

variable [∀ (P : Cᵒᵖ ⥤ Type v₁), F.op.HasLeftKanExtension P]

noncomputable instance (Φ : StructuredArrow (F ⋙ yoneda)
    ((whiskeringLeft C (Cᵒᵖ ⥤ Type v₁) (Dᵒᵖ ⥤ Type v₁)).obj yoneda)) :
    Unique (Functor.LeftExtension.mk F.op.lan (compYonedaIsoYonedaCompLan F).hom ⟶ Φ) where
  default := compYonedaIsoYonedaCompLan.extensionHom Φ
  uniq _ := compYonedaIsoYonedaCompLan.hom_ext _ _

/-- Given a functor `F : C ⥤ D`, `F.op.lan : (Cᵒᵖ ⥤ Type v₁) ⥤ Dᵒᵖ ⥤ Type v₁` is the
left Kan extension of `F ⋙ yoneda : C ⥤ Dᵒᵖ ⥤ Type v₁` along `yoneda : C ⥤ Cᵒᵖ ⥤ Type v₁`. -/
instance : F.op.lan.IsLeftKanExtension (compYonedaIsoYonedaCompLan F).hom :=
  ⟨⟨Limits.IsInitial.ofUnique _⟩⟩

end

section

variable {C : Type u₁} [Category.{v₁} C] (P : Cᵒᵖ ⥤ Type v₁)

/-- For a presheaf `P`, consider the forgetful functor from the category of representable
    presheaves over `P` to the category of presheaves. There is a tautological cocone over this
    functor whose leg for a natural transformation `V ⟶ P` with `V` representable is just that
    natural transformation. -/
@[simps]
def tautologicalCocone : Cocone (CostructuredArrow.proj yoneda P ⋙ yoneda) where
  pt := P
  ι := { app := fun X => X.hom }

/-- The tautological cocone with point `P` is a colimit cocone, exhibiting `P` as a colimit of
    representables.

    Proposition 2.6.3(i) in [Kashiwara2006] -/
def isColimitTautologicalCocone : IsColimit (tautologicalCocone P) where
  desc := fun s => by
    refine ⟨fun X t => yonedaEquiv (s.ι.app (CostructuredArrow.mk (yonedaEquiv.symm t))), ?_⟩
    intros X Y f
    ext t
    dsimp
    rw [yonedaEquiv_naturality', yonedaEquiv_symm_map]
    simpa using (s.ι.naturality
      (CostructuredArrow.homMk' (CostructuredArrow.mk (yonedaEquiv.symm t)) f.unop)).symm
  fac := by
    intro s t
    dsimp
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp]
    dsimp only
    rw [Equiv.symm_apply_apply]
    rfl
  uniq := by
    intro s j h
    ext V x
    obtain ⟨t, rfl⟩ := yonedaEquiv.surjective x
    dsimp
    rw [Equiv.symm_apply_apply, ← yonedaEquiv_comp]
    exact congr_arg _ (h (CostructuredArrow.mk t))

variable {I : Type v₁} [SmallCategory I] (F : I ⥤ C)

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
    exact isoWhiskerLeft _
      (CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow c.pt).isoCompInverse

  apply IsTerminal.ofIso Over.mkIdTerminal
  let isc : IsColimit ((Over.forget _).mapCocone _) := isColimitOfPreserves _
    (colimit.isColimit ((c.toCostructuredArrow ⋙ CostructuredArrow.pre F yoneda c.pt) ⋙
      CostructuredArrow.toOver yoneda c.pt))
  exact Over.isoMk (hc.coconePointUniqueUpToIso isc) (hc.hom_ext fun i => by simp)

end-/

end Presheaf

end CategoryTheory
