/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta

! This file was ported from Lean 3 source module category_theory.limits.presheaf
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Adjunction.Limits
import Mathbin.CategoryTheory.Adjunction.Opposites
import Mathbin.CategoryTheory.Elements
import Mathbin.CategoryTheory.Limits.FunctorCategory
import Mathbin.CategoryTheory.Limits.KanExtension
import Mathbin.CategoryTheory.Limits.Shapes.Terminal
import Mathbin.CategoryTheory.Limits.Types

/-!
# Colimit of representables

This file constructs an adjunction `yoneda_adjunction` between `(Cᵒᵖ ⥤ Type u)` and `ℰ` given a
functor `A : C ⥤ ℰ`, where the right adjoint sends `(E : ℰ)` to `c ↦ (A.obj c ⟶ E)` (provided `ℰ`
has colimits).

This adjunction is used to show that every presheaf is a colimit of representables.

Further, the left adjoint `colimit_adj.extend_along_yoneda : (Cᵒᵖ ⥤ Type u) ⥤ ℰ` satisfies
`yoneda ⋙ L ≅ A`, that is, an extension of `A : C ⥤ ℰ` to `(Cᵒᵖ ⥤ Type u) ⥤ ℰ` through
`yoneda : C ⥤ Cᵒᵖ ⥤ Type u`. It is the left Kan extension of `A` along the yoneda embedding,
sometimes known as the Yoneda extension, as proved in `extend_along_yoneda_iso_Kan`.

`unique_extension_along_yoneda` shows `extend_along_yoneda` is unique amongst cocontinuous functors
with this property, establishing the presheaf category as the free cocompletion of a small category.

## Tags
colimit, representable, presheaf, free cocompletion

## References
* [S. MacLane, I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]
* https://ncatlab.org/nlab/show/Yoneda+extension
-/


namespace CategoryTheory

noncomputable section

open Category Limits

universe u₁ u₂

variable {C : Type u₁} [SmallCategory C]

variable {ℰ : Type u₂} [Category.{u₁} ℰ]

variable (A : C ⥤ ℰ)

namespace ColimitAdj

/--
The functor taking `(E : ℰ) (c : Cᵒᵖ)` to the homset `(A.obj C ⟶ E)`. It is shown in `L_adjunction`
that this functor has a left adjoint (provided `E` has colimits) given by taking colimits over
categories of elements.
In the case where `ℰ = Cᵒᵖ ⥤ Type u` and `A = yoneda`, this functor is isomorphic to the identity.

Defined as in [MM92], Chapter I, Section 5, Theorem 2.
-/
@[simps]
def restrictedYoneda : ℰ ⥤ Cᵒᵖ ⥤ Type u₁ :=
  yoneda ⋙ (whiskeringLeft _ _ (Type u₁)).obj (Functor.op A)
#align category_theory.colimit_adj.restricted_yoneda CategoryTheory.ColimitAdj.restrictedYoneda

/--
The functor `restricted_yoneda` is isomorphic to the identity functor when evaluated at the yoneda
embedding.
-/
def restrictedYonedaYoneda : restrictedYoneda (yoneda : C ⥤ Cᵒᵖ ⥤ Type u₁) ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun P =>
      NatIso.ofComponents (fun X => yonedaSectionsSmall X.unop _) fun X Y f =>
        funext fun x => by
          dsimp
          rw [← functor_to_types.naturality _ _ x f (𝟙 _)]
          dsimp
          simp)
    fun _ _ _ => rfl
#align category_theory.colimit_adj.restricted_yoneda_yoneda CategoryTheory.ColimitAdj.restrictedYonedaYoneda

/-- (Implementation). The equivalence of homsets which helps construct the left adjoint to
`colimit_adj.restricted_yoneda`.
It is shown in `restrict_yoneda_hom_equiv_natural` that this is a natural bijection.
-/
def restrictYonedaHomEquiv (P : Cᵒᵖ ⥤ Type u₁) (E : ℰ)
    {c : Cocone ((CategoryOfElements.π P).leftOp ⋙ A)} (t : IsColimit c) :
    (c.pt ⟶ E) ≃ (P ⟶ (restrictedYoneda A).obj E) :=
  ((uliftTrivial _).symm ≪≫ t.homIso' E).toEquiv.trans
    { toFun := fun k =>
        { app := fun c p => k.1 (Opposite.op ⟨_, p⟩)
          naturality' := fun c c' f =>
            funext fun p =>
              (k.2
                  (Quiver.Hom.op ⟨f, rfl⟩ :
                    (Opposite.op ⟨c', P.map f p⟩ : P.Elementsᵒᵖ) ⟶ Opposite.op ⟨c, p⟩)).symm }
      invFun := fun τ =>
        { val := fun p => τ.app p.unop.1 p.unop.2
          property := fun p p' f => by
            simp_rw [← f.unop.2]
            apply (congr_fun (τ.naturality f.unop.1) p'.unop.2).symm }
      left_inv := by
        rintro ⟨k₁, k₂⟩
        ext
        dsimp
        congr 1
        simp
      right_inv := by
        rintro ⟨_, _⟩
        rfl }
#align category_theory.colimit_adj.restrict_yoneda_hom_equiv CategoryTheory.ColimitAdj.restrictYonedaHomEquiv

/--
(Implementation). Show that the bijection in `restrict_yoneda_hom_equiv` is natural (on the right).
-/
theorem restrictYonedaHomEquiv_natural (P : Cᵒᵖ ⥤ Type u₁) (E₁ E₂ : ℰ) (g : E₁ ⟶ E₂) {c : Cocone _}
    (t : IsColimit c) (k : c.pt ⟶ E₁) :
    restrictYonedaHomEquiv A P E₂ t (k ≫ g) =
      restrictYonedaHomEquiv A P E₁ t k ≫ (restrictedYoneda A).map g :=
  by
  ext (_ X p)
  apply (assoc _ _ _).symm
#align category_theory.colimit_adj.restrict_yoneda_hom_equiv_natural CategoryTheory.ColimitAdj.restrictYonedaHomEquiv_natural

variable [HasColimits ℰ]

/--
The left adjoint to the functor `restricted_yoneda` (shown in `yoneda_adjunction`). It is also an
extension of `A` along the yoneda embedding (shown in `is_extension_along_yoneda`), in particular
it is the left Kan extension of `A` through the yoneda embedding.
-/
def extendAlongYoneda : (Cᵒᵖ ⥤ Type u₁) ⥤ ℰ :=
  Adjunction.leftAdjointOfEquiv (fun P E => restrictYonedaHomEquiv A P E (colimit.isColimit _))
    fun P E E' g => restrictYonedaHomEquiv_natural A P E E' g _
#align category_theory.colimit_adj.extend_along_yoneda CategoryTheory.ColimitAdj.extendAlongYoneda

@[simp]
theorem extendAlongYoneda_obj (P : Cᵒᵖ ⥤ Type u₁) :
    (extendAlongYoneda A).obj P = colimit ((CategoryOfElements.π P).leftOp ⋙ A) :=
  rfl
#align category_theory.colimit_adj.extend_along_yoneda_obj CategoryTheory.ColimitAdj.extendAlongYoneda_obj

theorem extendAlongYoneda_map {X Y : Cᵒᵖ ⥤ Type u₁} (f : X ⟶ Y) :
    (extendAlongYoneda A).map f =
      colimit.pre ((CategoryOfElements.π Y).leftOp ⋙ A) (CategoryOfElements.map f).op :=
  by
  ext J
  erw [colimit.ι_pre ((category_of_elements.π Y).leftOp ⋙ A) (category_of_elements.map f).op]
  dsimp only [extend_along_yoneda, restrict_yoneda_hom_equiv, is_colimit.hom_iso',
    is_colimit.hom_iso, ulift_trivial]
  simpa
#align category_theory.colimit_adj.extend_along_yoneda_map CategoryTheory.ColimitAdj.extendAlongYoneda_map

/-- Show `extend_along_yoneda` is left adjoint to `restricted_yoneda`.

The construction of [MM92], Chapter I, Section 5, Theorem 2.
-/
def yonedaAdjunction : extendAlongYoneda A ⊣ restrictedYoneda A :=
  Adjunction.adjunctionOfEquivLeft _ _
#align category_theory.colimit_adj.yoneda_adjunction CategoryTheory.ColimitAdj.yonedaAdjunction

/--
The initial object in the category of elements for a representable functor. In `is_initial` it is
shown that this is initial.
-/
def Elements.initial (A : C) : (yoneda.obj A).Elements :=
  ⟨Opposite.op A, 𝟙 _⟩
#align category_theory.colimit_adj.elements.initial CategoryTheory.ColimitAdj.Elements.initial

/-- Show that `elements.initial A` is initial in the category of elements for the `yoneda` functor.
-/
def isInitial (A : C) : IsInitial (Elements.initial A)
    where
  desc s := ⟨s.pt.2.op, comp_id _⟩
  uniq s m w := by
    simp_rw [← m.2]
    dsimp [elements.initial]
    simp
  fac := by rintro s ⟨⟨⟩⟩
#align category_theory.colimit_adj.is_initial CategoryTheory.ColimitAdj.isInitial

/--
`extend_along_yoneda A` is an extension of `A` to the presheaf category along the yoneda embedding.
`unique_extension_along_yoneda` shows it is unique among functors preserving colimits with this
property (up to isomorphism).

The first part of [MM92], Chapter I, Section 5, Corollary 4.
See Property 1 of <https://ncatlab.org/nlab/show/Yoneda+extension#properties>.
-/
def isExtensionAlongYoneda : (yoneda : C ⥤ Cᵒᵖ ⥤ Type u₁) ⋙ extendAlongYoneda A ≅ A :=
  NatIso.ofComponents
    (fun X =>
      (colimit.isColimit _).coconePointUniqueUpToIso
        (colimitOfDiagramTerminal (terminalOpOfInitial (isInitial _)) _))
    (by
      intro X Y f
      change colimit.desc _ ⟨_, _⟩ ≫ colimit.desc _ _ = colimit.desc _ _ ≫ _
      apply colimit.hom_ext
      intro j
      rw [colimit.ι_desc_assoc, colimit.ι_desc_assoc]
      change (colimit.ι _ _ ≫ 𝟙 _) ≫ colimit.desc _ _ = _
      rw [comp_id, colimit.ι_desc]
      dsimp
      rw [← A.map_comp]
      congr 1)
#align category_theory.colimit_adj.is_extension_along_yoneda CategoryTheory.ColimitAdj.isExtensionAlongYoneda

/-- See Property 2 of https://ncatlab.org/nlab/show/Yoneda+extension#properties. -/
instance : PreservesColimits (extendAlongYoneda A) :=
  (yonedaAdjunction A).leftAdjointPreservesColimits

/-- Show that the images of `X` after `extend_along_yoneda` and `Lan yoneda` are indeed isomorphic.
This follows from `category_theory.category_of_elements.costructured_arrow_yoneda_equivalence`.
-/
@[simps]
def extendAlongYonedaIsoKanApp (X) :
    (extendAlongYoneda A).obj X ≅ ((lan yoneda : (_ ⥤ ℰ) ⥤ _).obj A).obj X :=
  let eq := CategoryOfElements.costructuredArrowYonedaEquivalence X
  { Hom := colimit.pre (Lan.diagram (yoneda : C ⥤ _ ⥤ Type u₁) A X) Eq.Functor
    inv := colimit.pre ((CategoryOfElements.π X).leftOp ⋙ A) Eq.inverse
    hom_inv_id' :=
      by
      erw [colimit.pre_pre ((category_of_elements.π X).leftOp ⋙ A) eq.inverse]
      trans colimit.pre ((category_of_elements.π X).leftOp ⋙ A) (𝟭 _)
      congr
      · exact congr_arg functor.op (category_of_elements.from_to_costructured_arrow_eq X)
      · ext
        simp only [colimit.ι_pre]
        erw [category.comp_id]
        congr
    inv_hom_id' :=
      by
      erw [colimit.pre_pre (Lan.diagram (yoneda : C ⥤ _ ⥤ Type u₁) A X) eq.functor]
      trans colimit.pre (Lan.diagram (yoneda : C ⥤ _ ⥤ Type u₁) A X) (𝟭 _)
      congr
      · exact category_of_elements.to_from_costructured_arrow_eq X
      · ext
        simp only [colimit.ι_pre]
        erw [category.comp_id]
        congr }
#align category_theory.colimit_adj.extend_along_yoneda_iso_Kan_app CategoryTheory.ColimitAdj.extendAlongYonedaIsoKanApp

/-- Verify that `extend_along_yoneda` is indeed the left Kan extension along the yoneda embedding.
-/
@[simps]
def extendAlongYonedaIsoKan : extendAlongYoneda A ≅ (lan yoneda : (_ ⥤ ℰ) ⥤ _).obj A :=
  NatIso.ofComponents (extendAlongYonedaIsoKanApp A)
    (by
      intro X Y f; simp
      rw [extend_along_yoneda_map]
      erw [colimit.pre_pre (Lan.diagram (yoneda : C ⥤ _ ⥤ Type u₁) A Y) (costructured_arrow.map f)]
      erw [colimit.pre_pre (Lan.diagram (yoneda : C ⥤ _ ⥤ Type u₁) A Y)
          (category_of_elements.costructured_arrow_yoneda_equivalence Y).Functor]
      congr 1
      apply category_of_elements.costructured_arrow_yoneda_equivalence_naturality)
#align category_theory.colimit_adj.extend_along_yoneda_iso_Kan CategoryTheory.ColimitAdj.extendAlongYonedaIsoKan

/-- extending `F ⋙ yoneda` along the yoneda embedding is isomorphic to `Lan F.op`. -/
@[simps]
def extendOfCompYonedaIsoLan {D : Type u₁} [SmallCategory D] (F : C ⥤ D) :
    extendAlongYoneda (F ⋙ yoneda) ≅ lan F.op :=
  Adjunction.natIsoOfRightAdjointNatIso (yonedaAdjunction (F ⋙ yoneda))
    (Lan.adjunction (Type u₁) F.op)
    (isoWhiskerRight curriedYonedaLemma' ((whiskeringLeft Cᵒᵖ Dᵒᵖ (Type u₁)).obj F.op : _))
#align category_theory.colimit_adj.extend_of_comp_yoneda_iso_Lan CategoryTheory.ColimitAdj.extendOfCompYonedaIsoLan

end ColimitAdj

open ColimitAdj

/-- `F ⋙ yoneda` is naturally isomorphic to `yoneda ⋙ Lan F.op`. -/
@[simps]
def compYonedaIsoYonedaCompLan {D : Type u₁} [SmallCategory D] (F : C ⥤ D) :
    F ⋙ yoneda ≅ yoneda ⋙ lan F.op :=
  (isExtensionAlongYoneda (F ⋙ yoneda)).symm ≪≫ isoWhiskerLeft yoneda (extendOfCompYonedaIsoLan F)
#align category_theory.comp_yoneda_iso_yoneda_comp_Lan CategoryTheory.compYonedaIsoYonedaCompLan

/-- Since `extend_along_yoneda A` is adjoint to `restricted_yoneda A`, if we use `A = yoneda`
then `restricted_yoneda A` is isomorphic to the identity, and so `extend_along_yoneda A` is as well.
-/
def extendAlongYonedaYoneda : extendAlongYoneda (yoneda : C ⥤ _) ≅ 𝟭 _ :=
  Adjunction.natIsoOfRightAdjointNatIso (yonedaAdjunction _) Adjunction.id restrictedYonedaYoneda
#align category_theory.extend_along_yoneda_yoneda CategoryTheory.extendAlongYonedaYoneda

-- Maybe this should be reducible or an abbreviation?
/-- A functor to the presheaf category in which everything in the image is representable (witnessed
by the fact that it factors through the yoneda embedding).
`cocone_of_representable` gives a cocone for this functor which is a colimit and has point `P`.
-/
def functorToRepresentables (P : Cᵒᵖ ⥤ Type u₁) : P.Elementsᵒᵖ ⥤ Cᵒᵖ ⥤ Type u₁ :=
  (CategoryOfElements.π P).leftOp ⋙ yoneda
#align category_theory.functor_to_representables CategoryTheory.functorToRepresentables

/-- This is a cocone with point `P` for the functor `functor_to_representables P`. It is shown in
`colimit_of_representable P` that this cocone is a colimit: that is, we have exhibited an arbitrary
presheaf `P` as a colimit of representables.

The construction of [MM92], Chapter I, Section 5, Corollary 3.
-/
def coconeOfRepresentable (P : Cᵒᵖ ⥤ Type u₁) : Cocone (functorToRepresentables P) :=
  Cocone.extend (colimit.cocone _) (extendAlongYonedaYoneda.Hom.app P)
#align category_theory.cocone_of_representable CategoryTheory.coconeOfRepresentable

@[simp]
theorem coconeOfRepresentable_pt (P : Cᵒᵖ ⥤ Type u₁) : (coconeOfRepresentable P).pt = P :=
  rfl
#align category_theory.cocone_of_representable_X CategoryTheory.coconeOfRepresentable_pt

-- Marking this as a simp lemma seems to make things more awkward.
/-- An explicit formula for the legs of the cocone `cocone_of_representable`. -/
theorem coconeOfRepresentable_ι_app (P : Cᵒᵖ ⥤ Type u₁) (j : P.Elementsᵒᵖ) :
    (coconeOfRepresentable P).ι.app j = (yonedaSectionsSmall _ _).inv j.unop.2 :=
  colimit.ι_desc _ _
#align category_theory.cocone_of_representable_ι_app CategoryTheory.coconeOfRepresentable_ι_app

/-- The legs of the cocone `cocone_of_representable` are natural in the choice of presheaf. -/
theorem coconeOfRepresentable_naturality {P₁ P₂ : Cᵒᵖ ⥤ Type u₁} (α : P₁ ⟶ P₂) (j : P₁.Elementsᵒᵖ) :
    (coconeOfRepresentable P₁).ι.app j ≫ α =
      (coconeOfRepresentable P₂).ι.app ((CategoryOfElements.map α).op.obj j) :=
  by
  ext (T f)
  simpa [cocone_of_representable_ι_app] using functor_to_types.naturality _ _ α f.op _
#align category_theory.cocone_of_representable_naturality CategoryTheory.coconeOfRepresentable_naturality

/-- The cocone with point `P` given by `the_cocone` is a colimit: that is, we have exhibited an
arbitrary presheaf `P` as a colimit of representables.

The result of [MM92], Chapter I, Section 5, Corollary 3.
-/
def colimitOfRepresentable (P : Cᵒᵖ ⥤ Type u₁) : IsColimit (coconeOfRepresentable P) :=
  by
  apply is_colimit.of_point_iso (colimit.is_colimit (functor_to_representables P))
  change is_iso (colimit.desc _ (cocone.extend _ _))
  rw [colimit.desc_extend, colimit.desc_cocone]
  infer_instance
#align category_theory.colimit_of_representable CategoryTheory.colimitOfRepresentable

/-- Given two functors L₁ and L₂ which preserve colimits, if they agree when restricted to the
representable presheaves then they agree everywhere.
-/
def natIsoOfNatIsoOnRepresentables (L₁ L₂ : (Cᵒᵖ ⥤ Type u₁) ⥤ ℰ) [PreservesColimits L₁]
    [PreservesColimits L₂] (h : yoneda ⋙ L₁ ≅ yoneda ⋙ L₂) : L₁ ≅ L₂ :=
  by
  apply nat_iso.of_components _ _
  · intro P
    refine'
      (is_colimit_of_preserves L₁ (colimit_of_representable P)).coconePointsIsoOfNatIso
        (is_colimit_of_preserves L₂ (colimit_of_representable P)) _
    apply functor.associator _ _ _ ≪≫ _
    exact iso_whisker_left (category_of_elements.π P).leftOp h
  · intro P₁ P₂ f
    apply (is_colimit_of_preserves L₁ (colimit_of_representable P₁)).hom_ext
    intro j
    dsimp only [id.def, is_colimit.cocone_points_iso_of_nat_iso_hom, iso_whisker_left_hom]
    have :
      (L₁.map_cocone (cocone_of_representable P₁)).ι.app j ≫ L₁.map f =
        (L₁.map_cocone (cocone_of_representable P₂)).ι.app
          ((category_of_elements.map f).op.obj j) :=
      by
      dsimp
      rw [← L₁.map_comp, cocone_of_representable_naturality]
      rfl
    rw [reassoc_of this, is_colimit.ι_map_assoc, is_colimit.ι_map]
    dsimp
    rw [← L₂.map_comp, cocone_of_representable_naturality]
    rfl
#align category_theory.nat_iso_of_nat_iso_on_representables CategoryTheory.natIsoOfNatIsoOnRepresentables

variable [HasColimits ℰ]

/-- Show that `extend_along_yoneda` is the unique colimit-preserving functor which extends `A` to
the presheaf category.

The second part of [MM92], Chapter I, Section 5, Corollary 4.
See Property 3 of https://ncatlab.org/nlab/show/Yoneda+extension#properties.
-/
def uniqueExtensionAlongYoneda (L : (Cᵒᵖ ⥤ Type u₁) ⥤ ℰ) (hL : yoneda ⋙ L ≅ A)
    [PreservesColimits L] : L ≅ extendAlongYoneda A :=
  natIsoOfNatIsoOnRepresentables _ _ (hL ≪≫ (isExtensionAlongYoneda _).symm)
#align category_theory.unique_extension_along_yoneda CategoryTheory.uniqueExtensionAlongYoneda

/-- If `L` preserves colimits and `ℰ` has them, then it is a left adjoint. This is a special case of
`is_left_adjoint_of_preserves_colimits` used to prove that.
-/
def isLeftAdjointOfPreservesColimitsAux (L : (Cᵒᵖ ⥤ Type u₁) ⥤ ℰ) [PreservesColimits L] :
    IsLeftAdjoint L where
  right := restrictedYoneda (yoneda ⋙ L)
  adj := (yonedaAdjunction _).ofNatIsoLeft (uniqueExtensionAlongYoneda _ L (Iso.refl _)).symm
#align category_theory.is_left_adjoint_of_preserves_colimits_aux CategoryTheory.isLeftAdjointOfPreservesColimitsAux

/-- If `L` preserves colimits and `ℰ` has them, then it is a left adjoint. Note this is a (partial)
converse to `left_adjoint_preserves_colimits`.
-/
def isLeftAdjointOfPreservesColimits (L : (C ⥤ Type u₁) ⥤ ℰ) [PreservesColimits L] :
    IsLeftAdjoint L :=
  let e : _ ⥤ Type u₁ ≌ _ ⥤ Type u₁ := (opOpEquivalence C).congr_left
  let t := isLeftAdjointOfPreservesColimitsAux (e.Functor ⋙ L : _)
  adjunction.left_adjoint_of_nat_iso (e.inv_fun_id_assoc _)
#align category_theory.is_left_adjoint_of_preserves_colimits CategoryTheory.isLeftAdjointOfPreservesColimits

end CategoryTheory

