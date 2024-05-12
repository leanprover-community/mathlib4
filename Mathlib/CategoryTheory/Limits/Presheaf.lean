/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.CategoryTheory.Adjunction.Opposites
import Mathlib.CategoryTheory.Comma.Presheaf
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Limits.ConeCategory
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Limits.FunctorCategory
import Mathlib.CategoryTheory.Limits.Over
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Types

#align_import category_theory.limits.presheaf from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Colimit of representables

This file constructs an adjunction `yonedaAdjunction` between `(Cᵒᵖ ⥤ Type u)` and `ℰ` given a
functor `A : C ⥤ ℰ`, where the right adjoint sends `(E : ℰ)` to `c ↦ (A.obj c ⟶ E)` (provided `ℰ`
has colimits).

This adjunction is used to show that every presheaf is a colimit of representables. This result is
also known as the density theorem, the co-Yoneda lemma and the Ninja Yoneda lemma.

Further, the left adjoint `colimitAdj.extendAlongYoneda : (Cᵒᵖ ⥤ Type u) ⥤ ℰ` satisfies
`yoneda ⋙ L ≅ A`, that is, an extension of `A : C ⥤ ℰ` to `(Cᵒᵖ ⥤ Type u) ⥤ ℰ` through
`yoneda : C ⥤ Cᵒᵖ ⥤ Type u`. It is the left Kan extension of `A` along the yoneda embedding,
sometimes known as the Yoneda extension, as proved in `extendAlongYonedaIsoKan`.

`uniqueExtensionAlongYoneda` shows `extendAlongYoneda` is unique amongst cocontinuous functors
with this property, establishing the presheaf category as the free cocompletion of a small category.

We also give a direct pedestrian proof that every presheaf is a colimit of representables. This
version of the proof is valid for any category `C`, even if it is not small.

## Tags
colimit, representable, presheaf, free cocompletion

## References
* [S. MacLane, I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]
* https://ncatlab.org/nlab/show/Yoneda+extension
-/

namespace CategoryTheory

open Category Limits

universe v₁ v₂ u₁ u₂

section SmallCategory

variable {C : Type u₁} [SmallCategory C]

namespace ColimitAdj

variable {ℰ : Type u₂} [Category.{u₁} ℰ] (A : C ⥤ ℰ)

/--
The functor taking `(E : ℰ) (c : Cᵒᵖ)` to the homset `(A.obj C ⟶ E)`. It is shown in `L_adjunction`
that this functor has a left adjoint (provided `E` has colimits) given by taking colimits over
categories of elements.
In the case where `ℰ = Cᵒᵖ ⥤ Type u` and `A = yoneda`, this functor is isomorphic to the identity.

Defined as in [MM92], Chapter I, Section 5, Theorem 2.
-/
@[simps!]
def restrictedYoneda : ℰ ⥤ Cᵒᵖ ⥤ Type u₁ :=
  yoneda ⋙ (whiskeringLeft _ _ (Type u₁)).obj (Functor.op A)
#align category_theory.colimit_adj.restricted_yoneda CategoryTheory.ColimitAdj.restrictedYoneda

/--
The functor `restrictedYoneda` is isomorphic to the identity functor when evaluated at the yoneda
embedding.
-/
def restrictedYonedaYoneda : restrictedYoneda (yoneda : C ⥤ Cᵒᵖ ⥤ Type u₁) ≅ 𝟭 _ :=
  NatIso.ofComponents fun P =>
    NatIso.ofComponents (fun X => Equiv.toIso yonedaEquiv) @ fun X Y f =>
      funext fun x => by
        dsimp [yonedaEquiv]
        have : x.app X (CategoryStruct.id (Opposite.unop X)) =
            (x.app X (𝟙 (Opposite.unop X))) := rfl
        rw [this]
        rw [← FunctorToTypes.naturality _ _ x f (𝟙 _)]
        simp only [id_comp, Functor.op_obj, Opposite.unop_op, yoneda_obj_map, comp_id]
#align category_theory.colimit_adj.restricted_yoneda_yoneda CategoryTheory.ColimitAdj.restrictedYonedaYoneda

/-def restrictYonedaHomEquiv' (P : Cᵒᵖ ⥤ Type v₂) (E : ℰ) :
    ((CategoryOfElements.π P).leftOp ⋙ A ⟶
        (Functor.const (Functor.Elements P)ᵒᵖ).toPrefunctor.obj E) ≃
      (P ⟶ (restrictedYoneda A).obj E) where
  toFun k :=
    { app := fun X p => k.app (Opposite.op ⟨_, p⟩)
      naturality := fun X₁ X₂ f => by
        ext p
        let φ : P.elementsMk X₁ p ⟶ P.elementsMk X₂ (P.map f p) := ⟨f, rfl⟩
        simpa using (k.naturality φ.op).symm }
  invFun τ :=
    { app := fun e => τ.app e.unop.1 e.unop.2
      naturality := fun p₁ p₂ f => by
        simpa [← f.unop.2] using (congr_fun (τ.naturality f.unop.1) p₂.unop.2).symm }
  left_inv := by aesop_cat
  right_inv := by aesop_cat

/-- (Implementation). The equivalence of homsets which helps construct the left adjoint to
`colimitAdj.restrictedYoneda`.
It is shown in `restrictYonedaHomEquivNatural` that this is a natural bijection.
-/
def restrictYonedaHomEquiv (P : Cᵒᵖ ⥤ Type v₂) (E : ℰ)
    {c : Cocone ((CategoryOfElements.π P).leftOp ⋙ A)} (t : IsColimit c) :
    (c.pt ⟶ E) ≃ (P ⟶ (restrictedYoneda A).obj E) :=
  (t.homEquiv E).trans (restrictYonedaHomEquiv' A P E)
#align category_theory.colimit_adj.restrict_yoneda_hom_equiv CategoryTheory.ColimitAdj.restrictYonedaHomEquiv

/--
(Implementation). Show that the bijection in `restrictYonedaHomEquiv` is natural (on the right).
-/
theorem restrictYonedaHomEquiv_natural (P : Cᵒᵖ ⥤ Type v₂) (E₁ E₂ : ℰ) (g : E₁ ⟶ E₂) {c : Cocone _}
    (t : IsColimit c) (k : c.pt ⟶ E₁) :
    restrictYonedaHomEquiv A P E₂ t (k ≫ g) =
      restrictYonedaHomEquiv A P E₁ t k ≫ (restrictedYoneda A).map g := by
  ext x X
  apply (assoc _ _ _).symm
#align category_theory.colimit_adj.restrict_yoneda_hom_equiv_natural CategoryTheory.ColimitAdj.restrictYonedaHomEquiv_natural-/

def homEquiv' (P : Cᵒᵖ ⥤ Type u₁) (E : ℰ) :
    (CostructuredArrow.proj yoneda P ⋙ A ⟶
      (Functor.const (CostructuredArrow yoneda P)).obj E) ≃
      (P ⟶ (restrictedYoneda A).obj E) where
  toFun f :=
    { app := fun X x => f.app (CostructuredArrow.mk (yonedaEquiv.symm x))
      naturality := fun {X₁ X₂} φ => by
        ext x
        dsimp
        let ψ : CostructuredArrow.mk (yonedaEquiv.symm (P.toPrefunctor.map φ x)) ⟶
          CostructuredArrow.mk (yonedaEquiv.symm x) := CostructuredArrow.homMk φ.unop (by
            dsimp [yonedaEquiv]
            aesop_cat )
        simpa using (f.naturality ψ).symm }
  invFun g :=
    { app := fun y => yonedaEquiv (y.hom ≫ g)
      naturality := fun {X₁ X₂} φ => by
        dsimp
        rw [← CostructuredArrow.w φ]
        dsimp [yonedaEquiv]
        simp only [comp_id, id_comp]
        refine' (congr_fun (g.naturality φ.left.op) (X₂.hom.app (Opposite.op X₂.left)
          (𝟙 _))).symm.trans _
        dsimp
        apply congr_arg
        simpa using congr_fun (X₂.hom.naturality φ.left.op).symm (𝟙 _) }
  left_inv f := by
    ext x
    dsimp
    erw [yonedaEquiv_apply]
    simp
    congr 1
    obtain ⟨X, ⟨⟨⟩⟩, f⟩ := x
    dsimp [CostructuredArrow.mk]
    suffices yonedaEquiv.symm (f.app (Opposite.op X) (𝟙 X)) = f by
      erw [this]
    ext Y y
    simpa using congr_fun (f.naturality y.op).symm (𝟙 _)
  right_inv g := by
    ext X x
    dsimp
    erw [yonedaEquiv_apply]
    rw [FunctorToTypes.comp]
    erw [yonedaEquiv_symm_app_apply]
    simp

variable [yoneda.HasPointwiseLeftKanExtension A] -- follows from  `[HasColimits ℰ]`

noncomputable def homEquiv (P : Cᵒᵖ ⥤ Type u₁) (E : ℰ) :
    ((yoneda.leftKanExtension A).obj P ⟶ E) ≃ (P ⟶ (restrictedYoneda A).obj E) :=
  ((Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension _
    (yoneda.leftKanExtensionUnit A) P).homEquiv E).trans (homEquiv' A P E)

-- TODO: redefine this for any (pointwise) left Kan extension, not just the chosen one

noncomputable def yonedaAdjunction : yoneda.leftKanExtension A ⊣ restrictedYoneda A :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv A
      homEquiv_naturality_left_symm := sorry
      homEquiv_naturality_right := sorry }

/-- See Property 2 of https://ncatlab.org/nlab/show/Yoneda+extension#properties. -/
noncomputable instance : PreservesColimits (yoneda.leftKanExtension A) :=
  (yonedaAdjunction A).leftAdjointPreservesColimits

instance : IsIso (yoneda.leftKanExtensionUnit A) :=
  (Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension _
    (yoneda.leftKanExtensionUnit A)).isIso_hom

noncomputable def isExtensionAlongYoneda :
    yoneda ⋙ yoneda.leftKanExtension A ≅ A :=
  (asIso (yoneda.leftKanExtensionUnit A)).symm


/-
/--
The left adjoint to the functor `restrictedYoneda` (shown in `yonedaAdjunction`). It is also an
extension of `A` along the yoneda embedding (shown in `isExtensionAlongYoneda`), in particular
it is the left Kan extension of `A` through the yoneda embedding.
-/
noncomputable def extendAlongYoneda : (Cᵒᵖ ⥤ Type v₂) ⥤ ℰ :=
  Adjunction.leftAdjointOfEquiv (fun P E => restrictYonedaHomEquiv A P E (colimit.isColimit _))
    fun P E E' g => restrictYonedaHomEquiv_natural A P E E' g _
#align category_theory.colimit_adj.extend_along_yoneda CategoryTheory.ColimitAdj.extendAlongYoneda

@[simp]
theorem extendAlongYoneda_obj (P : Cᵒᵖ ⥤ Type v₂) :
    (extendAlongYoneda A).obj P = colimit ((CategoryOfElements.π P).leftOp ⋙ A) :=
  rfl
#align category_theory.colimit_adj.extend_along_yoneda_obj CategoryTheory.ColimitAdj.extendAlongYoneda_obj

-- Porting note: adding this lemma because lean 4 ext no longer applies all ext lemmas when
-- stuck (and hence can see through definitional equalities). The previous lemma shows that
-- `(extendAlongYoneda A).obj P` is definitionally a colimit, and the ext lemma is just
-- a special case of `CategoryTheory.Limits.colimit.hom_ext`.
-- See https://github.com/leanprover-community/mathlib4/issues/5229
@[ext] lemma extendAlongYoneda_obj.hom_ext {P : Cᵒᵖ ⥤ Type v₂}
    {f f' : (extendAlongYoneda A).obj P ⟶ X}
    (w : ∀ j, colimit.ι ((CategoryOfElements.π P).leftOp ⋙ A) j ≫ f =
      colimit.ι ((CategoryOfElements.π P).leftOp ⋙ A) j ≫ f') : f = f' :=
CategoryTheory.Limits.colimit.hom_ext w

theorem extendAlongYoneda_map {X Y : Cᵒᵖ ⥤ Type v₂} (f : X ⟶ Y) :
    (extendAlongYoneda A).map f =
      colimit.pre ((CategoryOfElements.π Y).leftOp ⋙ A) (CategoryOfElements.map f).op := by
  ext J
  erw [colimit.ι_pre ((CategoryOfElements.π Y).leftOp ⋙ A) (CategoryOfElements.map f).op]
  dsimp only [extendAlongYoneda, restrictYonedaHomEquiv, IsColimit.homIso', IsColimit.homIso,
    uliftTrivial]
  -- Porting note: in mathlib3 the rest of the proof was `simp, refl`; this is squeezed
  -- and appropriately reordered, presumably because of a non-confluence issue.
  simp only [Adjunction.leftAdjointOfEquiv_map, Iso.symm_mk, Iso.toEquiv_comp, Equiv.coe_trans,
    Equiv.coe_fn_mk, Iso.toEquiv_fun, Equiv.symm_trans_apply, Equiv.coe_fn_symm_mk,
    Iso.toEquiv_symm_fun, id, colimit.isColimit_desc, colimit.ι_desc, FunctorToTypes.comp,
    Cocone.extend_ι, Cocone.extensions_app, Functor.map_id, Category.comp_id, colimit.cocone_ι]
  simp only [Functor.comp_obj, Functor.leftOp_obj, CategoryOfElements.π_obj, colimit.cocone_x,
    Functor.comp_map, Functor.leftOp_map, CategoryOfElements.π_map, Opposite.unop_op,
    Adjunction.leftAdjointOfEquiv_obj, Function.comp_apply, Functor.map_id, comp_id,
    colimit.cocone_ι, Functor.op_obj]
  rfl
#align category_theory.colimit_adj.extend_along_yoneda_map CategoryTheory.ColimitAdj.extendAlongYoneda_map

/-- Show `extendAlongYoneda` is left adjoint to `restrictedYoneda`.

The construction of [MM92], Chapter I, Section 5, Theorem 2.
-/
noncomputable def yonedaAdjunction : extendAlongYoneda A ⊣ restrictedYoneda A :=
  Adjunction.adjunctionOfEquivLeft _ _
#align category_theory.colimit_adj.yoneda_adjunction CategoryTheory.ColimitAdj.yonedaAdjunction

/--
The initial object in the category of elements for a representable functor. In `isInitial` it is
shown that this is initial.
-/
def Elements.initial (A : C) : (yoneda.obj A).Elements :=
  ⟨Opposite.op A, 𝟙 _⟩
#align category_theory.colimit_adj.elements.initial CategoryTheory.ColimitAdj.Elements.initial

/-- Show that `Elements.initial A` is initial in the category of elements for the `yoneda` functor.
-/
def isInitial (A : C) : IsInitial (Elements.initial A) where
  desc s := ⟨s.pt.2.op, comp_id _⟩
  uniq s m _ := by
    simp_rw [← m.2]
    dsimp [Elements.initial]
    simp
  fac := by rintro s ⟨⟨⟩⟩
#align category_theory.colimit_adj.is_initial CategoryTheory.ColimitAdj.isInitial


/--
`extendAlongYoneda A` is an extension of `A` to the presheaf category along the yoneda embedding.
`uniqueExtensionAlongYoneda` shows it is unique among functors preserving colimits with this
property (up to isomorphism).

The first part of [MM92], Chapter I, Section 5, Corollary 4.
See Property 1 of <https://ncatlab.org/nlab/show/Yoneda+extension#properties>.
-/
noncomputable def isExtensionAlongYoneda :
    (yoneda : C ⥤ Cᵒᵖ ⥤ Type _) ⋙ extendAlongYoneda A ≅ A :=
  NatIso.ofComponents
    (fun X =>
      (colimit.isColimit _).coconePointUniqueUpToIso
        (colimitOfDiagramTerminal (terminalOpOfInitial (isInitial _)) _))
    (by
      intro X Y f
      -- Porting note: this is slightly different to the `change` in mathlib3 which
      -- didn't work
      change (colimit.desc _ _ ≫ _) = colimit.desc _ _ ≫ _
      ext
      rw [colimit.ι_desc_assoc, colimit.ι_desc_assoc]
      change (colimit.ι _ _ ≫ 𝟙 _) ≫ colimit.desc _ _ = _
      rw [comp_id, colimit.ι_desc]
      dsimp
      rw [← A.map_comp]
      congr 1)
#align category_theory.colimit_adj.is_extension_along_yoneda CategoryTheory.ColimitAdj.isExtensionAlongYoneda

@[reassoc]
lemma isExtensionAlongYoneda_inv_app_extendAlongYoneda_map_yonedaSections (X : Cᵒᵖ ⥤ Type u₁) (j : X.Elements) :
      (isExtensionAlongYoneda A).inv.app j.1.unop ≫ (extendAlongYoneda A).map ((yonedaSections j.1.unop X).inv ⟨j.2⟩) =
      colimit.ι ((CategoryOfElements.costructuredArrowYonedaEquivalence X).functor ⋙
        CostructuredArrow.proj yoneda X ⋙ A) (Opposite.op j) := by
  have eq := IsColimit.comp_coconePointUniqueUpToIso_inv (colimit.isColimit  ((CategoryOfElements.π (yoneda.obj j.1.unop)).leftOp ⋙ A))
    (colimitOfDiagramTerminal (terminalOpOfInitial (isInitial _)) _) (Opposite.op (Elements.initial j.1.unop))
  dsimp at eq
  simp only [IsTerminal.from_self, unop_id, Opposite.unop_op, CategoryOfElements.id_val,
    yoneda_obj_obj, Functor.map_id, id_comp] at eq
  dsimp [isExtensionAlongYoneda]
  rw [eq, extendAlongYoneda_map]
  erw [colimit.ι_desc]
  dsimp [Cocone.whisker, CategoryOfElements.map, Elements.initial]
  congr 1
  simp

/-- See Property 2 of https://ncatlab.org/nlab/show/Yoneda+extension#properties. -/
noncomputable instance : PreservesColimits (extendAlongYoneda A) :=
  (yonedaAdjunction A).leftAdjointPreservesColimits

/-- Show that the images of `X` after `extendAlongYoneda` and `Lan yoneda` are indeed isomorphic.
This follows from `CategoryTheory.CategoryOfElements.costructuredArrowYonedaEquivalence`.
-/
@[simps]
noncomputable def extendAlongYonedaIsoKanApp (X) :
    (extendAlongYoneda A).obj X ≅ ((lan yoneda : (_ ⥤ ℰ) ⥤ _).obj A).obj X :=
  let eq := CategoryOfElements.costructuredArrowYonedaEquivalence X
  { hom := colimit.pre (Lan.diagram (yoneda : C ⥤ _ ⥤ Type u₁) A X) eq.functor
    inv := colimit.pre ((CategoryOfElements.π X).leftOp ⋙ A) eq.inverse
    hom_inv_id := by
      erw [colimit.pre_pre ((CategoryOfElements.π X).leftOp ⋙ A) eq.inverse]
      trans colimit.pre ((CategoryOfElements.π X).leftOp ⋙ A) (𝟭 _)
      · congr
        exact congr_arg Functor.op (CategoryOfElements.from_toCostructuredArrow_eq X)
      · ext
        simp only [colimit.ι_pre]
        erw [Category.comp_id]
        congr
    inv_hom_id := by
      erw [colimit.pre_pre (Lan.diagram (yoneda : C ⥤ _ ⥤ Type u₁) A X) eq.functor]
      trans colimit.pre (Lan.diagram (yoneda : C ⥤ _ ⥤ Type u₁) A X) (𝟭 _)
      · congr
        exact CategoryOfElements.to_fromCostructuredArrow_eq X
      · ext
        simp only [colimit.ι_pre]
        erw [Category.comp_id]
        congr }
set_option linter.uppercaseLean3 false in
#align category_theory.colimit_adj.extend_along_yoneda_iso_Kan_app CategoryTheory.ColimitAdj.extendAlongYonedaIsoKanApp

/-- Verify that `extendAlongYoneda` is indeed the left Kan extension along the yoneda embedding.
-/
@[simps!]
noncomputable def extendAlongYonedaIsoKan :
    extendAlongYoneda A ≅ yoneda.lan.obj A :=
  Functor.leftKanExtensionUnique _ _ (isExtensionAlongYoneda A).inv (yoneda.lanUnit.app A)
set_option linter.uppercaseLean3 false in
#align category_theory.colimit_adj.extend_along_yoneda_iso_Kan CategoryTheory.ColimitAdj.extendAlongYonedaIsoKan-/

/-- extending `F ⋙ yoneda` along the yoneda embedding is isomorphic to `F.op.lan`. -/
@[simps!]
noncomputable def yonedaLeftKanExtensionCompYonedaIsoLan {D : Type u₁} [SmallCategory D] (F : C ⥤ D) :
    yoneda.leftKanExtension (F ⋙ yoneda) ≅ F.op.lan :=
  Adjunction.natIsoOfRightAdjointNatIso (yonedaAdjunction (F ⋙ yoneda))
    (F.op.lanAdjunction (Type u₁))
    (isoWhiskerRight curriedYonedaLemma' ((whiskeringLeft Cᵒᵖ Dᵒᵖ (Type u₁)).obj F.op : _))
set_option linter.uppercaseLean3 false in
#align category_theory.colimit_adj.extend_of_comp_yoneda_iso_Lan CategoryTheory.ColimitAdj.yonedaLeftKanExtensionCompYonedaIsoLan

end ColimitAdj

open ColimitAdj

/-- `F ⋙ yoneda` is naturally isomorphic to `yoneda ⋙ F.op.lan`. -/
@[simps!]
noncomputable def compYonedaIsoYonedaCompLan {D : Type u₁} [SmallCategory D] (F : C ⥤ D) :
    F ⋙ yoneda ≅ yoneda ⋙ F.op.lan :=
  (isExtensionAlongYoneda (F ⋙ yoneda)).symm ≪≫ isoWhiskerLeft yoneda (yonedaLeftKanExtensionCompYonedaIsoLan F)
set_option linter.uppercaseLean3 false in
#align category_theory.comp_yoneda_iso_yoneda_comp_Lan CategoryTheory.compYonedaIsoYonedaCompLan

/-- Since `extendAlongYoneda A` is adjoint to `restrictedYoneda A`, if we use `A = yoneda`
then `restrictedYoneda A` is isomorphic to the identity, and so `extendAlongYoneda A` is as well.
-/
noncomputable def extendAlongYonedaYoneda : yoneda.leftKanExtension (yoneda : C ⥤ _) ≅ 𝟭 _ :=
  Adjunction.natIsoOfRightAdjointNatIso (yonedaAdjunction _) Adjunction.id restrictedYonedaYoneda
#align category_theory.extend_along_yoneda_yoneda CategoryTheory.extendAlongYonedaYoneda

-- Maybe this should be reducible or an abbreviation?
/-- A functor to the presheaf category in which everything in the image is representable (witnessed
by the fact that it factors through the yoneda embedding).
`coconeOfRepresentable` gives a cocone for this functor which is a colimit and has point `P`.
-/
@[reducible]
def functorToRepresentables (P : Cᵒᵖ ⥤ Type u₁) : P.Elementsᵒᵖ ⥤ Cᵒᵖ ⥤ Type u₁ :=
  (CategoryOfElements.π P).leftOp ⋙ yoneda
#align category_theory.functor_to_representables CategoryTheory.functorToRepresentables

/-- This is a cocone with point `P` for the functor `functorToRepresentables P`. It is shown in
`colimitOfRepresentable P` that this cocone is a colimit: that is, we have exhibited an arbitrary
presheaf `P` as a colimit of representables.

The construction of [MM92], Chapter I, Section 5, Corollary 3.
-/
@[simps]
noncomputable def coconeOfRepresentable (P : Cᵒᵖ ⥤ Type u₁) : Cocone (functorToRepresentables P) where
  pt := P
  ι :=
    { app := fun x => yonedaEquiv.symm x.unop.2
      naturality := fun {x₁ x₂} f => by
        dsimp
        rw [comp_id]
        erw [← yonedaEquiv_symm_map]
        congr 1
        rw [f.unop.2] }
#align category_theory.cocone_of_representable CategoryTheory.coconeOfRepresentable
set_option linter.uppercaseLean3 false in
#align category_theory.cocone_of_representable_X CategoryTheory.coconeOfRepresentable_pt
#align category_theory.cocone_of_representable_ι_app CategoryTheory.coconeOfRepresentable_ι_app

-- Marking this as a simp lemma seems to make things more awkward.
--attribute [-simp] coconeOfRepresentable_ι_app


/-- The legs of the cocone `coconeOfRepresentable` are natural in the choice of presheaf. -/
theorem coconeOfRepresentable_naturality {P₁ P₂ : Cᵒᵖ ⥤ Type u₁} (α : P₁ ⟶ P₂) (j : P₁.Elementsᵒᵖ) :
    (coconeOfRepresentable P₁).ι.app j ≫ α =
      (coconeOfRepresentable P₂).ι.app ((CategoryOfElements.map α).op.obj j) := by
  ext T f
  simpa [coconeOfRepresentable_ι_app] using FunctorToTypes.naturality _ _ α f.op _
#align category_theory.cocone_of_representable_naturality CategoryTheory.coconeOfRepresentable_naturality

/-- The cocone with point `P` given by `coconeOfRepresentable` is a colimit:
that is, we have exhibited an arbitrary presheaf `P` as a colimit of representables.

The result of [MM92], Chapter I, Section 5, Corollary 3.
-/
noncomputable def colimitOfRepresentable (P : Cᵒᵖ ⥤ Type u₁) :
    IsColimit (coconeOfRepresentable P) where
  desc s :=
    { app := fun X x => (s.ι.app (Opposite.op (Functor.elementsMk P X x))).app X (𝟙 _)
      naturality := sorry }
  fac s j := by
    ext X x
    dsimp
    let φ : j.unop ⟶ Functor.elementsMk P X ((yonedaEquiv.symm j.unop.2).app X x) := ⟨x.op, rfl⟩
    simpa using congr_fun (congr_app (s.ι.naturality φ.op).symm X) (𝟙 _)
  uniq s m hm := by
    ext X x
    dsimp
    rw [← hm]
    dsimp
    apply congr_arg
    simp [coconeOfRepresentable_ι_app, yonedaEquiv]
#align category_theory.colimit_of_representable CategoryTheory.colimitOfRepresentable

variable {ℰ : Type u₂} [Category.{u₁} ℰ] {A : C ⥤ ℰ}
variable [yoneda.HasPointwiseLeftKanExtension A] -- follows from  `[HasColimits ℰ]`

section

variable (L : (Cᵒᵖ ⥤ Type u₁) ⥤ ℰ) (α : A ⟶ yoneda ⋙ L)

instance [L.IsLeftKanExtension α] : IsIso α :=
  (Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension L α).isIso_hom

lemma isLeftKanExtension_along_yoneda_iff :
    L.IsLeftKanExtension α ↔ (IsIso α ∧ Nonempty (PreservesColimits L)) := by
  constructor
  · intro
    exact ⟨inferInstance, ⟨preservesColimitsOfNatIso
      (Functor.leftKanExtensionUnique _ (yoneda.leftKanExtensionUnit A) _ α)⟩⟩
  · rintro ⟨_, ⟨_⟩⟩
    let E := Functor.LeftExtension.mk _ α
    apply Functor.LeftExtension.IsPointwiseLeftKanExtension.isLeftKanExtension (E := E)
    intro P
    dsimp [Functor.LeftExtension.IsPointwiseLeftKanExtensionAt]
    apply IsColimit.ofWhiskerEquivalence (CategoryOfElements.costructuredArrowYonedaEquivalence _)
    let e : CategoryOfElements.toCostructuredArrow P ⋙ CostructuredArrow.proj yoneda P ⋙ A ≅
        functorToRepresentables P ⋙ L :=
      isoWhiskerLeft _ (isoWhiskerLeft _ (asIso α)) ≪≫
        isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫
        (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (Iso.refl _) L
    apply (IsColimit.precomposeHomEquiv e.symm _).1
    exact IsColimit.ofIsoColimit (isColimitOfPreserves L (colimitOfRepresentable P))
      (Cocones.ext (Iso.refl _))

noncomputable def isLeftKanExtension_of_preservesColimits
    (L : (Cᵒᵖ ⥤ Type u₁) ⥤ ℰ) (e : A ≅ yoneda ⋙ L) [PreservesColimits L] :
    L.IsLeftKanExtension e.hom := by
  rw [isLeftKanExtension_along_yoneda_iff]
  exact ⟨inferInstance, ⟨inferInstance⟩⟩

end

variable (A)

/-
/-- Given two functors L₁ and L₂ which preserve colimits, if they agree when restricted to the
representable presheaves then they agree everywhere.
-/
noncomputable def natIsoOfNatIsoOnRepresentables (L₁ L₂ : (Cᵒᵖ ⥤ Type u₁) ⥤ ℰ)
    [PreservesColimits L₁] [PreservesColimits L₂] (h : yoneda ⋙ L₁ ≅ yoneda ⋙ L₂) : L₁ ≅ L₂ := by
  sorry
  #exit
  apply NatIso.ofComponents _ _
  · intro P
    refine'
      (isColimitOfPreserves L₁ (colimitOfRepresentable P)).coconePointsIsoOfNatIso
        (isColimitOfPreserves L₂ (colimitOfRepresentable P)) _
    apply Functor.associator _ _ _ ≪≫ _
    exact isoWhiskerLeft (CategoryOfElements.π P).leftOp h
  · intro P₁ P₂ f
    apply (isColimitOfPreserves L₁ (colimitOfRepresentable P₁)).hom_ext
    intro j
    dsimp only [id, isoWhiskerLeft_hom]
    have :
      (L₁.mapCocone (coconeOfRepresentable P₁)).ι.app j ≫ L₁.map f =
        (L₁.mapCocone (coconeOfRepresentable P₂)).ι.app
          ((CategoryOfElements.map f).op.obj j) := by
      dsimp
      rw [← L₁.map_comp]
      erw [coconeOfRepresentable_naturality]
      rfl
    erw [reassoc_of% this, IsColimit.ι_map_assoc, IsColimit.ι_map]
    dsimp
    rw [← L₂.map_comp]
    erw [coconeOfRepresentable_naturality]
    rfl
#align category_theory.nat_iso_of_nat_iso_on_representables CategoryTheory.natIsoOfNatIsoOnRepresentables-/

variable [HasColimits ℰ]

/-- Show that `extendAlongYoneda` is the unique colimit-preserving functor which extends `A` to
the presheaf category.

The second part of [MM92], Chapter I, Section 5, Corollary 4.
See Property 3 of https://ncatlab.org/nlab/show/Yoneda+extension#properties.
-/
noncomputable def uniqueExtensionAlongYoneda (L : (Cᵒᵖ ⥤ Type u₁) ⥤ ℰ) (e : A ≅ yoneda ⋙ L)
    [PreservesColimits L] : L ≅ yoneda.leftKanExtension A :=
  have := isLeftKanExtension_of_preservesColimits L e
  Functor.leftKanExtensionUnique _ e.hom _ (yoneda.leftKanExtensionUnit A)
#align category_theory.unique_extension_along_yoneda CategoryTheory.uniqueExtensionAlongYoneda

/-- Auxiliary definition for `isLeftAdjointOfPreservesColimits`. -/
noncomputable def adjunctionOfPreservesColimitsAux (L : (Cᵒᵖ ⥤ Type u₁) ⥤ ℰ)
    [PreservesColimits L] : L ⊣ restrictedYoneda (yoneda ⋙ L) :=
  (yonedaAdjunction _).ofNatIsoLeft (uniqueExtensionAlongYoneda _ L (Iso.refl _)).symm
#align category_theory.is_left_adjoint_of_preserves_colimits_aux CategoryTheory.adjunctionOfPreservesColimitsAux

/-- If `L` preserves colimits and `ℰ` has them, then it is a left adjoint. Note this is a (partial)
converse to `leftAdjointPreservesColimits`.
-/
lemma isLeftAdjointOfPreservesColimits (L : (C ⥤ Type u₁) ⥤ ℰ) [PreservesColimits L] :
    L.IsLeftAdjoint :=
  ⟨_, ⟨((opOpEquivalence C).congrLeft.symm.toAdjunction.comp
    (adjunctionOfPreservesColimitsAux ((opOpEquivalence C).congrLeft.functor ⋙ L))).ofNatIsoLeft
        ((opOpEquivalence C).congrLeft.invFunIdAssoc L)⟩⟩
#align category_theory.is_left_adjoint_of_preserves_colimits CategoryTheory.isLeftAdjointOfPreservesColimits

end SmallCategory

section ArbitraryUniverses

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
    refine' ⟨fun X t => yonedaEquiv (s.ι.app (CostructuredArrow.mk (yonedaEquiv.symm t))), _⟩
    intros X Y f
    ext t
    dsimp
    -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
    erw [yonedaEquiv_naturality', yonedaEquiv_symm_map]
    simpa using (s.ι.naturality
      (CostructuredArrow.homMk' (CostructuredArrow.mk (yonedaEquiv.symm t)) f.unop)).symm
  fac := by
    intro s t
    dsimp
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp]
    dsimp only
    -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
    erw [Equiv.symm_apply_apply]
    rfl
  uniq := by
    intro s j h
    ext V x
    obtain ⟨t, rfl⟩ := yonedaEquiv.surjective x
    dsimp
    -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
    erw [Equiv.symm_apply_apply, ← yonedaEquiv_comp]
    exact congr_arg _ (h (CostructuredArrow.mk t))

variable {I : Type v₁} [SmallCategory I] (F : I ⥤ C)

/-- Given a functor `F : I ⥤ C`, a cocone `c` on `F ⋙ yoneda : I ⥤ Cᵒᵖ ⥤ Type v₁` induces a
    functor `I ⥤ CostructuredArrow yoneda c.pt` which maps `i : I` to the leg
    `yoneda.obj (F.obj i) ⟶ c.pt`. If `c` is a colimit cocone, then that functor is
    final.

    Proposition 2.6.3(ii) in [Kashiwara2006] -/
theorem final_toCostructuredArrow_comp_pre {c : Cocone (F ⋙ yoneda)} (hc : IsColimit c) :
    Functor.Final (c.toCostructuredArrow ⋙ CostructuredArrow.pre F yoneda c.pt) := by
  apply Functor.cofinal_of_isTerminal_colimit_comp_yoneda

  suffices IsTerminal (colimit ((c.toCostructuredArrow ⋙ CostructuredArrow.pre F yoneda c.pt) ⋙
      CostructuredArrow.toOver yoneda c.pt)) by
    apply IsTerminal.isTerminalOfObj (overEquivPresheafCostructuredArrow c.pt).inverse
    apply IsTerminal.ofIso this
    refine ?_ ≪≫ (preservesColimitIso (overEquivPresheafCostructuredArrow c.pt).inverse _).symm
    apply HasColimit.isoOfNatIso
    exact isoWhiskerLeft _
      (CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow c.pt).isoCompInverse

  apply IsTerminal.ofIso Over.mkIdTerminal
  let isc : IsColimit ((Over.forget _).mapCocone _) := PreservesColimit.preserves
    (colimit.isColimit ((c.toCostructuredArrow ⋙ CostructuredArrow.pre F yoneda c.pt) ⋙
      CostructuredArrow.toOver yoneda c.pt))
  exact Over.isoMk (hc.coconePointUniqueUpToIso isc) (hc.hom_ext fun i => by simp)

end ArbitraryUniverses

end CategoryTheory
