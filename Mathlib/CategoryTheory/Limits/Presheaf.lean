/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Adjunction.Opposites
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Limits.FunctorCategory
import Mathlib.CategoryTheory.Limits.KanExtension
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

set_option autoImplicit true


namespace CategoryTheory

open Category Limits

universe v₁ v₂ u₁ u₂

section SmallCategory

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
    NatIso.ofComponents (fun X => yonedaSectionsSmall X.unop _) @ fun X Y f =>
      funext fun x => by
        dsimp
        -- ⊢ NatTrans.app x { unop := Y.unop } (𝟙 Y.unop ≫ f.unop) = P.map f (NatTrans.ap …
        have : x.app X (CategoryStruct.id (Opposite.unop X)) =
            (x.app X (𝟙 (Opposite.unop X)))
              := by rfl
        rw [this]
        -- ⊢ NatTrans.app x { unop := Y.unop } (𝟙 Y.unop ≫ f.unop) = P.map f (NatTrans.ap …
        rw [← FunctorToTypes.naturality _ _ x f (𝟙 _)]
        -- ⊢ NatTrans.app x { unop := Y.unop } (𝟙 Y.unop ≫ f.unop) = NatTrans.app x Y ((y …
        simp only [id_comp, Functor.op_obj, Opposite.unop_op, yoneda_obj_map, comp_id]
        -- 🎉 no goals
#align category_theory.colimit_adj.restricted_yoneda_yoneda CategoryTheory.ColimitAdj.restrictedYonedaYoneda

/-- (Implementation). The equivalence of homsets which helps construct the left adjoint to
`colimitAdj.restrictedYoneda`.
It is shown in `restrictYonedaHomEquivNatural` that this is a natural bijection.
-/
def restrictYonedaHomEquiv (P : Cᵒᵖ ⥤ Type u₁) (E : ℰ)
    {c : Cocone ((CategoryOfElements.π P).leftOp ⋙ A)} (t : IsColimit c) :
    (c.pt ⟶ E) ≃ (P ⟶ (restrictedYoneda A).obj E) :=
  ((uliftTrivial _).symm ≪≫ t.homIso' E).toEquiv.trans
    { toFun := fun k =>
        { app := fun c p => k.1 (Opposite.op ⟨_, p⟩)
          naturality := fun c c' f =>
            funext fun p =>
              (k.2
                  (Quiver.Hom.op ⟨f, rfl⟩ :
                    (Opposite.op ⟨c', P.map f p⟩ : P.Elementsᵒᵖ) ⟶ Opposite.op ⟨c, p⟩)).symm }
      invFun := fun τ =>
        { val := fun p => τ.app p.unop.1 p.unop.2
          property := @fun p p' f => by
            simp_rw [← f.unop.2]
            -- ⊢ ((CategoryOfElements.π P).leftOp ⋙ A).map f ≫ NatTrans.app τ p'.unop.fst p'. …
            apply (congr_fun (τ.naturality f.unop.1) p'.unop.2).symm }
            -- 🎉 no goals
      left_inv := by
        rintro ⟨k₁, k₂⟩
        -- ⊢ (fun τ => { val := fun p => NatTrans.app τ p.unop.fst p.unop.snd, property : …
        ext
        -- ⊢ ↑((fun τ => { val := fun p => NatTrans.app τ p.unop.fst p.unop.snd, property …
        dsimp
        -- ⊢ k₁ (Opposite.op { fst := x✝.unop.fst, snd := x✝.unop.snd }) = k₁ x✝
        congr 1
        -- 🎉 no goals
      right_inv := by
        rintro ⟨_, _⟩
        -- ⊢ (fun k => NatTrans.mk fun c p => ↑k (Opposite.op { fst := c, snd := p })) (( …
        rfl }
        -- 🎉 no goals
#align category_theory.colimit_adj.restrict_yoneda_hom_equiv CategoryTheory.ColimitAdj.restrictYonedaHomEquiv

/--
(Implementation). Show that the bijection in `restrictYonedaHomEquiv` is natural (on the right).
-/
theorem restrictYonedaHomEquiv_natural (P : Cᵒᵖ ⥤ Type u₁) (E₁ E₂ : ℰ) (g : E₁ ⟶ E₂) {c : Cocone _}
    (t : IsColimit c) (k : c.pt ⟶ E₁) :
    restrictYonedaHomEquiv A P E₂ t (k ≫ g) =
      restrictYonedaHomEquiv A P E₁ t k ≫ (restrictedYoneda A).map g := by
  ext x X
  -- ⊢ NatTrans.app (↑(restrictYonedaHomEquiv A P E₂ t) (k ≫ g)) x X = NatTrans.app …
  apply (assoc _ _ _).symm
  -- 🎉 no goals
#align category_theory.colimit_adj.restrict_yoneda_hom_equiv_natural CategoryTheory.ColimitAdj.restrictYonedaHomEquiv_natural

variable [HasColimits ℰ]

/--
The left adjoint to the functor `restrictedYoneda` (shown in `yonedaAdjunction`). It is also an
extension of `A` along the yoneda embedding (shown in `isExtensionAlongYoneda`), in particular
it is the left Kan extension of `A` through the yoneda embedding.
-/
noncomputable def extendAlongYoneda : (Cᵒᵖ ⥤ Type u₁) ⥤ ℰ :=
  Adjunction.leftAdjointOfEquiv (fun P E => restrictYonedaHomEquiv A P E (colimit.isColimit _))
    fun P E E' g => restrictYonedaHomEquiv_natural A P E E' g _
#align category_theory.colimit_adj.extend_along_yoneda CategoryTheory.ColimitAdj.extendAlongYoneda

@[simp]
theorem extendAlongYoneda_obj (P : Cᵒᵖ ⥤ Type u₁) :
    (extendAlongYoneda A).obj P = colimit ((CategoryOfElements.π P).leftOp ⋙ A) :=
  rfl
#align category_theory.colimit_adj.extend_along_yoneda_obj CategoryTheory.ColimitAdj.extendAlongYoneda_obj

-- porting note: adding this lemma because lean 4 ext no longer applies all ext lemmas when
-- stuck (and hence can see through definitional equalities). The previous lemma shows that
-- `(extendAlongYoneda A).obj P` is definitionally a colimit, and the ext lemma is just
-- a special case of `CategoryTheory.Limits.colimit.hom_ext`.
-- See https://github.com/leanprover-community/mathlib4/issues/5229
@[ext] lemma extendAlongYoneda_obj.hom_ext {P : Cᵒᵖ ⥤ Type u₁}
    {f f' : (extendAlongYoneda A).obj P ⟶ X}
    (w : ∀ j, colimit.ι ((CategoryOfElements.π P).leftOp ⋙ A) j ≫ f =
      colimit.ι ((CategoryOfElements.π P).leftOp ⋙ A) j ≫ f') : f = f' :=
CategoryTheory.Limits.colimit.hom_ext w

theorem extendAlongYoneda_map {X Y : Cᵒᵖ ⥤ Type u₁} (f : X ⟶ Y) :
    (extendAlongYoneda A).map f =
      colimit.pre ((CategoryOfElements.π Y).leftOp ⋙ A) (CategoryOfElements.map f).op := by
  ext J
  -- ⊢ colimit.ι ((CategoryOfElements.π X).leftOp ⋙ A) J ≫ (extendAlongYoneda A).ma …
  erw [colimit.ι_pre ((CategoryOfElements.π Y).leftOp ⋙ A) (CategoryOfElements.map f).op]
  -- ⊢ colimit.ι ((CategoryOfElements.π X).leftOp ⋙ A) J ≫ (extendAlongYoneda A).ma …
  dsimp only [extendAlongYoneda, restrictYonedaHomEquiv, IsColimit.homIso', IsColimit.homIso,
    uliftTrivial]
  -- porting note: in mathlib3 the rest of the proof was `simp, refl`; this is squeezed
  -- and appropriately reordered, presumably because of a non-confluence issue.
  simp only [Adjunction.leftAdjointOfEquiv_map, Iso.symm_mk, Iso.toEquiv_comp, Equiv.coe_trans,
    Equiv.coe_fn_mk, Iso.toEquiv_fun, Equiv.symm_trans_apply, Equiv.coe_fn_symm_mk,
    Iso.toEquiv_symm_fun, id.def, colimit.isColimit_desc, colimit.ι_desc, FunctorToTypes.comp,
    Cocone.extend_ι, Cocone.extensions_app, Functor.map_id, Category.comp_id, colimit.cocone_ι]
  simp only [Functor.comp_obj, Functor.leftOp_obj, CategoryOfElements.π_obj, colimit.cocone_x,
    Functor.comp_map, Functor.leftOp_map, CategoryOfElements.π_map, Opposite.unop_op,
    Adjunction.leftAdjointOfEquiv_obj, Function.comp_apply, Functor.map_id, comp_id,
    colimit.cocone_ι, Functor.op_obj]
  rfl
  -- 🎉 no goals
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
    -- ⊢ m = { val := ((yoneda.obj A).map (↑m) (asEmptyCocone (Elements.initial A)).p …
    dsimp [Elements.initial]
    -- ⊢ m = { val := 𝟙 (Opposite.op A) ≫ ↑m, property := (_ : (𝟙 (Opposite.op A) ≫ ↑ …
            -- 🎉 no goals
    simp
    -- 🎉 no goals
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
    (yoneda : C ⥤ Cᵒᵖ ⥤ Type u₁) ⋙ extendAlongYoneda A ≅ A :=
  NatIso.ofComponents
    (fun X =>
      (colimit.isColimit _).coconePointUniqueUpToIso
        (colimitOfDiagramTerminal (terminalOpOfInitial (isInitial _)) _))
    (by
      intro X Y f
      -- ⊢ (yoneda ⋙ extendAlongYoneda A).map f ≫ ((fun X => IsColimit.coconePointUniqu …
      -- porting note: this is slightly different to the `change` in mathlib3 which
      -- didn't work
      change (colimit.desc _ _ ≫ _) = colimit.desc _ _ ≫ _
      -- ⊢ colimit.desc ((CategoryOfElements.π (yoneda.obj X)).leftOp ⋙ A) { pt := (fun …
      ext
      -- ⊢ colimit.ι ((CategoryOfElements.π (yoneda.obj X)).leftOp ⋙ A) j✝ ≫ colimit.de …
      rw [colimit.ι_desc_assoc, colimit.ι_desc_assoc]
      -- ⊢ NatTrans.app { pt := (fun P => (colimit.cocone ((CategoryOfElements.π P).lef …
      change (colimit.ι _ _ ≫ 𝟙 _) ≫ colimit.desc _ _ = _
      -- ⊢ (colimit.ι (Opposite.op ((CategoryOfElements.π (yoneda.obj Y)).leftOp ⋙ A)). …
      rw [comp_id, colimit.ι_desc]
      -- ⊢ NatTrans.app (coconeOfDiagramTerminal (terminalOpOfInitial (isInitial Y)) (( …
      dsimp
      -- ⊢ A.map (↑(IsTerminal.from (terminalOpOfInitial (isInitial Y)) (Opposite.op {  …
      rw [← A.map_comp]
      -- ⊢ A.map (↑(IsTerminal.from (terminalOpOfInitial (isInitial Y)) (Opposite.op {  …
      congr 1)
      -- 🎉 no goals
#align category_theory.colimit_adj.is_extension_along_yoneda CategoryTheory.ColimitAdj.isExtensionAlongYoneda

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
      -- ⊢ colimit.pre ((CategoryOfElements.π X).leftOp ⋙ A) (eq.functor ⋙ eq.inverse)  …
      trans colimit.pre ((CategoryOfElements.π X).leftOp ⋙ A) (𝟭 _)
      -- ⊢ colimit.pre ((CategoryOfElements.π X).leftOp ⋙ A) (eq.functor ⋙ eq.inverse)  …
      congr
      -- ⊢ eq.functor ⋙ eq.inverse = 𝟭 (Functor.Elements X)ᵒᵖ
      · exact congr_arg Functor.op (CategoryOfElements.from_toCostructuredArrow_eq X)
        -- 🎉 no goals
      · ext
        -- ⊢ colimit.ι (𝟭 (Functor.Elements X)ᵒᵖ ⋙ (CategoryOfElements.π X).leftOp ⋙ A) j …
        simp only [colimit.ι_pre]
        -- ⊢ colimit.ι ((CategoryOfElements.π X).leftOp ⋙ A) ((𝟭 (Functor.Elements X)ᵒᵖ). …
        erw [Category.comp_id]
        -- ⊢ colimit.ι ((CategoryOfElements.π X).leftOp ⋙ A) ((𝟭 (Functor.Elements X)ᵒᵖ). …
        congr
        -- 🎉 no goals
    inv_hom_id := by
      erw [colimit.pre_pre (Lan.diagram (yoneda : C ⥤ _ ⥤ Type u₁) A X) eq.functor]
      -- ⊢ colimit.pre (Lan.diagram yoneda A X) (eq.inverse ⋙ eq.functor) = 𝟙 (((lan yo …
      trans colimit.pre (Lan.diagram (yoneda : C ⥤ _ ⥤ Type u₁) A X) (𝟭 _)
      -- ⊢ colimit.pre (Lan.diagram yoneda A X) (eq.inverse ⋙ eq.functor) = colimit.pre …
      congr
      -- ⊢ eq.inverse ⋙ eq.functor = 𝟭 (CostructuredArrow yoneda X)
      · exact CategoryOfElements.to_fromCostructuredArrow_eq X
        -- 🎉 no goals
      · ext
        -- ⊢ colimit.ι (𝟭 (CostructuredArrow yoneda X) ⋙ Lan.diagram yoneda A X) j✝ ≫ col …
        simp only [colimit.ι_pre]
        -- ⊢ colimit.ι (Lan.diagram yoneda A X) ((𝟭 (CostructuredArrow yoneda X)).obj j✝) …
        erw [Category.comp_id]
        -- ⊢ colimit.ι (Lan.diagram yoneda A X) ((𝟭 (CostructuredArrow yoneda X)).obj j✝) …
        congr }
        -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align category_theory.colimit_adj.extend_along_yoneda_iso_Kan_app CategoryTheory.ColimitAdj.extendAlongYonedaIsoKanApp

/-- Verify that `extendAlongYoneda` is indeed the left Kan extension along the yoneda embedding.
-/
@[simps!]
noncomputable def extendAlongYonedaIsoKan :
    extendAlongYoneda A ≅ (lan yoneda : (_ ⥤ ℰ) ⥤ _).obj A :=
  NatIso.ofComponents (extendAlongYonedaIsoKanApp A) (by
    intro X Y f; simp
    -- ⊢ (extendAlongYoneda A).map f ≫ (extendAlongYonedaIsoKanApp A Y).hom = (extend …
                 -- ⊢ (extendAlongYoneda A).map f ≫ colimit.pre (Lan.diagram yoneda A Y) (Category …
    rw [extendAlongYoneda_map]
    -- ⊢ colimit.pre ((CategoryOfElements.π Y).leftOp ⋙ A) (CategoryOfElements.map f) …
    erw [colimit.pre_pre (Lan.diagram (yoneda : C ⥤ _ ⥤ Type u₁) A Y) (CostructuredArrow.map f)]
    -- ⊢ colimit.pre ((CategoryOfElements.π Y).leftOp ⋙ A) (CategoryOfElements.map f) …
    erw [colimit.pre_pre (Lan.diagram (yoneda : C ⥤ _ ⥤ Type u₁) A Y)
        (CategoryOfElements.costructuredArrowYonedaEquivalence Y).functor]
    congr 1
    -- ⊢ (CategoryOfElements.map f).op ⋙ (CategoryOfElements.costructuredArrowYonedaE …
    apply CategoryOfElements.costructuredArrow_yoneda_equivalence_naturality)
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align category_theory.colimit_adj.extend_along_yoneda_iso_Kan CategoryTheory.ColimitAdj.extendAlongYonedaIsoKan

/-- extending `F ⋙ yoneda` along the yoneda embedding is isomorphic to `Lan F.op`. -/
noncomputable def extendOfCompYonedaIsoLan {D : Type u₁} [SmallCategory D] (F : C ⥤ D) :
    extendAlongYoneda (F ⋙ yoneda) ≅ lan F.op :=
  Adjunction.natIsoOfRightAdjointNatIso (yonedaAdjunction (F ⋙ yoneda))
    (Lan.adjunction (Type u₁) F.op)
    (isoWhiskerRight curriedYonedaLemma' ((whiskeringLeft Cᵒᵖ Dᵒᵖ (Type u₁)).obj F.op : _))
set_option linter.uppercaseLean3 false in
#align category_theory.colimit_adj.extend_of_comp_yoneda_iso_Lan CategoryTheory.ColimitAdj.extendOfCompYonedaIsoLan

-- porting note: attaching `[simps!]` directly to the declaration causes a timeout.
attribute [simps!] extendOfCompYonedaIsoLan

end ColimitAdj

open ColimitAdj

/-- `F ⋙ yoneda` is naturally isomorphic to `yoneda ⋙ Lan F.op`. -/
@[simps!]
noncomputable def compYonedaIsoYonedaCompLan {D : Type u₁} [SmallCategory D] (F : C ⥤ D) :
    F ⋙ yoneda ≅ yoneda ⋙ lan F.op :=
  (isExtensionAlongYoneda (F ⋙ yoneda)).symm ≪≫ isoWhiskerLeft yoneda (extendOfCompYonedaIsoLan F)
set_option linter.uppercaseLean3 false in
#align category_theory.comp_yoneda_iso_yoneda_comp_Lan CategoryTheory.compYonedaIsoYonedaCompLan

/-- Since `extendAlongYoneda A` is adjoint to `restrictedYoneda A`, if we use `A = yoneda`
then `restrictedYoneda A` is isomorphic to the identity, and so `extendAlongYoneda A` is as well.
-/
noncomputable def extendAlongYonedaYoneda : extendAlongYoneda (yoneda : C ⥤ _) ≅ 𝟭 _ :=
  Adjunction.natIsoOfRightAdjointNatIso (yonedaAdjunction _) Adjunction.id restrictedYonedaYoneda
#align category_theory.extend_along_yoneda_yoneda CategoryTheory.extendAlongYonedaYoneda

-- Maybe this should be reducible or an abbreviation?
/-- A functor to the presheaf category in which everything in the image is representable (witnessed
by the fact that it factors through the yoneda embedding).
`coconeOfRepresentable` gives a cocone for this functor which is a colimit and has point `P`.
-/
def functorToRepresentables (P : Cᵒᵖ ⥤ Type u₁) : P.Elementsᵒᵖ ⥤ Cᵒᵖ ⥤ Type u₁ :=
  (CategoryOfElements.π P).leftOp ⋙ yoneda
#align category_theory.functor_to_representables CategoryTheory.functorToRepresentables

/-- This is a cocone with point `P` for the functor `functorToRepresentables P`. It is shown in
`colimitOfRepresentable P` that this cocone is a colimit: that is, we have exhibited an arbitrary
presheaf `P` as a colimit of representables.

The construction of [MM92], Chapter I, Section 5, Corollary 3.
-/
noncomputable def coconeOfRepresentable (P : Cᵒᵖ ⥤ Type u₁) : Cocone (functorToRepresentables P) :=
  Cocone.extend (colimit.cocone _) (extendAlongYonedaYoneda.hom.app P)
#align category_theory.cocone_of_representable CategoryTheory.coconeOfRepresentable

@[simp]
theorem coconeOfRepresentable_pt (P : Cᵒᵖ ⥤ Type u₁) : (coconeOfRepresentable P).pt = P :=
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.cocone_of_representable_X CategoryTheory.coconeOfRepresentable_pt

-- Marking this as a simp lemma seems to make things more awkward.
/-- An explicit formula for the legs of the cocone `coconeOfRepresentable`. -/
theorem coconeOfRepresentable_ι_app (P : Cᵒᵖ ⥤ Type u₁) (j : P.Elementsᵒᵖ) :
    (coconeOfRepresentable P).ι.app j = (yonedaSectionsSmall _ _).inv j.unop.2 :=
  colimit.ι_desc _ _
#align category_theory.cocone_of_representable_ι_app CategoryTheory.coconeOfRepresentable_ι_app

/-- The legs of the cocone `coconeOfRepresentable` are natural in the choice of presheaf. -/
theorem coconeOfRepresentable_naturality {P₁ P₂ : Cᵒᵖ ⥤ Type u₁} (α : P₁ ⟶ P₂) (j : P₁.Elementsᵒᵖ) :
    (coconeOfRepresentable P₁).ι.app j ≫ α =
      (coconeOfRepresentable P₂).ι.app ((CategoryOfElements.map α).op.obj j) := by
  ext T f
  -- ⊢ NatTrans.app (NatTrans.app (coconeOfRepresentable P₁).ι j ≫ α) T f = NatTran …
  simpa [coconeOfRepresentable_ι_app] using FunctorToTypes.naturality _ _ α f.op _
  -- 🎉 no goals
#align category_theory.cocone_of_representable_naturality CategoryTheory.coconeOfRepresentable_naturality

/-- The cocone with point `P` given by `coconeOfRepresentable` is a colimit:
that is, we have exhibited an arbitrary presheaf `P` as a colimit of representables.

The result of [MM92], Chapter I, Section 5, Corollary 3.
-/
noncomputable def colimitOfRepresentable (P : Cᵒᵖ ⥤ Type u₁) :
    IsColimit (coconeOfRepresentable P) := by
  -- porting note:
  -- the `suffices` was not necessary in mathlib3; the function being `apply`ed has an
  -- `IsIso` input in square brackets; lean 3 was happy to give the user the input as a goal but
  -- lean 4 complains that typeclass inference can't find it.
  suffices IsIso (IsColimit.desc (colimit.isColimit (functorToRepresentables P))
    (coconeOfRepresentable P)) by
    apply IsColimit.ofPointIso (colimit.isColimit (functorToRepresentables P))
  change IsIso (colimit.desc _ (Cocone.extend _ _))
  -- ⊢ IsIso (colimit.desc (functorToRepresentables P) (Cocone.extend (colimit.coco …
  rw [colimit.desc_extend, colimit.desc_cocone]
  -- ⊢ IsIso (𝟙 (colimit (functorToRepresentables P)) ≫ NatTrans.app extendAlongYon …
  infer_instance
  -- 🎉 no goals
#align category_theory.colimit_of_representable CategoryTheory.colimitOfRepresentable

/-- Given two functors L₁ and L₂ which preserve colimits, if they agree when restricted to the
representable presheaves then they agree everywhere.
-/
noncomputable def natIsoOfNatIsoOnRepresentables (L₁ L₂ : (Cᵒᵖ ⥤ Type u₁) ⥤ ℰ)
    [PreservesColimits L₁] [PreservesColimits L₂] (h : yoneda ⋙ L₁ ≅ yoneda ⋙ L₂) : L₁ ≅ L₂ := by
  apply NatIso.ofComponents _ _
  -- ⊢ (X : Cᵒᵖ ⥤ Type u₁) → L₁.obj X ≅ L₂.obj X
  · intro P
    -- ⊢ L₁.obj P ≅ L₂.obj P
    refine'
      (isColimitOfPreserves L₁ (colimitOfRepresentable P)).coconePointsIsoOfNatIso
        (isColimitOfPreserves L₂ (colimitOfRepresentable P)) _
    apply Functor.associator _ _ _ ≪≫ _
    -- ⊢ (CategoryOfElements.π P).leftOp ⋙ yoneda ⋙ L₁ ≅ functorToRepresentables P ⋙ L₂
    exact isoWhiskerLeft (CategoryOfElements.π P).leftOp h
    -- 🎉 no goals
  · intro P₁ P₂ f
    -- ⊢ L₁.map f ≫ (IsColimit.coconePointsIsoOfNatIso (isColimitOfPreserves L₁ (coli …
    apply (isColimitOfPreserves L₁ (colimitOfRepresentable P₁)).hom_ext
    -- ⊢ ∀ (j : (Functor.Elements P₁)ᵒᵖ), NatTrans.app (L₁.mapCocone (coconeOfReprese …
    intro j
    -- ⊢ NatTrans.app (L₁.mapCocone (coconeOfRepresentable P₁)).ι j ≫ L₁.map f ≫ (IsC …
    dsimp only [id.def, IsColimit.comp_coconePointsIsoOfNatIso_hom, isoWhiskerLeft_hom]
    -- ⊢ NatTrans.app (L₁.mapCocone (coconeOfRepresentable P₁)).ι j ≫ L₁.map f ≫ (IsC …
    have :
      (L₁.mapCocone (coconeOfRepresentable P₁)).ι.app j ≫ L₁.map f =
        (L₁.mapCocone (coconeOfRepresentable P₂)).ι.app
          ((CategoryOfElements.map f).op.obj j) := by
      dsimp
      rw [← L₁.map_comp, coconeOfRepresentable_naturality]
      rfl
    erw [reassoc_of% this, IsColimit.ι_map_assoc, IsColimit.ι_map]
    -- ⊢ NatTrans.app (Functor.associator (CategoryOfElements.π P₂).leftOp yoneda L₁  …
    dsimp
    -- ⊢ (𝟙 (L₁.obj (yoneda.obj j.unop.fst.unop)) ≫ NatTrans.app h.hom j.unop.fst.uno …
    rw [← L₂.map_comp, coconeOfRepresentable_naturality]
    -- ⊢ (𝟙 (L₁.obj (yoneda.obj j.unop.fst.unop)) ≫ NatTrans.app h.hom j.unop.fst.uno …
    rfl
    -- 🎉 no goals
#align category_theory.nat_iso_of_nat_iso_on_representables CategoryTheory.natIsoOfNatIsoOnRepresentables

variable [HasColimits ℰ]

/-- Show that `extendAlongYoneda` is the unique colimit-preserving functor which extends `A` to
the presheaf category.

The second part of [MM92], Chapter I, Section 5, Corollary 4.
See Property 3 of https://ncatlab.org/nlab/show/Yoneda+extension#properties.
-/
noncomputable def uniqueExtensionAlongYoneda (L : (Cᵒᵖ ⥤ Type u₁) ⥤ ℰ) (hL : yoneda ⋙ L ≅ A)
    [PreservesColimits L] : L ≅ extendAlongYoneda A :=
  natIsoOfNatIsoOnRepresentables _ _ (hL ≪≫ (isExtensionAlongYoneda _).symm)
#align category_theory.unique_extension_along_yoneda CategoryTheory.uniqueExtensionAlongYoneda

/-- If `L` preserves colimits and `ℰ` has them, then it is a left adjoint. This is a special case of
`isLeftAdjointOfPreservesColimits` used to prove that.
-/
noncomputable def isLeftAdjointOfPreservesColimitsAux (L : (Cᵒᵖ ⥤ Type u₁) ⥤ ℰ)
    [PreservesColimits L] : IsLeftAdjoint L where
  right := restrictedYoneda (yoneda ⋙ L)
  adj := (yonedaAdjunction _).ofNatIsoLeft (uniqueExtensionAlongYoneda _ L (Iso.refl _)).symm
#align category_theory.is_left_adjoint_of_preserves_colimits_aux CategoryTheory.isLeftAdjointOfPreservesColimitsAux

/-- If `L` preserves colimits and `ℰ` has them, then it is a left adjoint. Note this is a (partial)
converse to `leftAdjointPreservesColimits`.
-/
noncomputable def isLeftAdjointOfPreservesColimits (L : (C ⥤ Type u₁) ⥤ ℰ) [PreservesColimits L] :
    IsLeftAdjoint L :=
  let e : _ ⥤ Type u₁ ≌ _ ⥤ Type u₁ := (opOpEquivalence C).congrLeft
  let _ := isLeftAdjointOfPreservesColimitsAux (e.functor ⋙ L : _)
  Adjunction.leftAdjointOfNatIso (e.invFunIdAssoc _)
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
    representables. -/
def isColimitTautologicalCocone : IsColimit (tautologicalCocone P) where
  desc := fun s => by
    refine' ⟨fun X t => yonedaEquiv (s.ι.app (CostructuredArrow.mk (yonedaEquiv.symm t))), _⟩
    -- ⊢ ∀ ⦃X Y : Cᵒᵖ⦄ (f : X ⟶ Y), (tautologicalCocone P).pt.map f ≫ (fun X t => ↑yo …
    intros X Y f
    -- ⊢ (tautologicalCocone P).pt.map f ≫ (fun X t => ↑yonedaEquiv (NatTrans.app s.ι …
    ext t
    -- ⊢ ((tautologicalCocone P).pt.map f ≫ (fun X t => ↑yonedaEquiv (NatTrans.app s. …
    dsimp
    -- ⊢ ↑yonedaEquiv (NatTrans.app s.ι (CostructuredArrow.mk (↑yonedaEquiv.symm (P.m …
    rw [yonedaEquiv_naturality', yonedaEquiv_symm_map]
    -- ⊢ ↑yonedaEquiv (NatTrans.app s.ι (CostructuredArrow.mk (yoneda.map f.unop ≫ ↑y …
    simpa using (s.ι.naturality
      (CostructuredArrow.homMk' (CostructuredArrow.mk (yonedaEquiv.symm t)) f.unop)).symm
  fac := by
    intro s t
    -- ⊢ NatTrans.app (tautologicalCocone P).ι t ≫ (fun s => NatTrans.mk fun X t => ↑ …
    dsimp
    -- ⊢ (t.hom ≫ NatTrans.mk fun X t => ↑yonedaEquiv (NatTrans.app s.ι (Costructured …
    apply yonedaEquiv.injective
    -- ⊢ ↑yonedaEquiv (t.hom ≫ NatTrans.mk fun X t => ↑yonedaEquiv (NatTrans.app s.ι  …
    rw [yonedaEquiv_comp]
    -- ⊢ NatTrans.app (NatTrans.mk fun X t => ↑yonedaEquiv (NatTrans.app s.ι (Costruc …
    dsimp only
    -- ⊢ ↑yonedaEquiv (NatTrans.app s.ι (CostructuredArrow.mk (↑yonedaEquiv.symm (↑yo …
    rw [Equiv.symm_apply_apply]
    -- ⊢ ↑yonedaEquiv (NatTrans.app s.ι (CostructuredArrow.mk t.hom)) = ↑yonedaEquiv  …
    rfl
    -- 🎉 no goals
  uniq := by
    intro s j h
    -- ⊢ j = (fun s => NatTrans.mk fun X t => ↑yonedaEquiv (NatTrans.app s.ι (Costruc …
    ext V x
    -- ⊢ NatTrans.app j V x = NatTrans.app ((fun s => NatTrans.mk fun X t => ↑yonedaE …
    obtain ⟨t, rfl⟩ := yonedaEquiv.surjective x
    -- ⊢ NatTrans.app j V (↑yonedaEquiv t) = NatTrans.app ((fun s => NatTrans.mk fun  …
    dsimp
    -- ⊢ NatTrans.app j V (↑yonedaEquiv t) = ↑yonedaEquiv (NatTrans.app s.ι (Costruct …
    rw [Equiv.symm_apply_apply, ← yonedaEquiv_comp']
    -- ⊢ ↑yonedaEquiv (t ≫ j) = ↑yonedaEquiv (NatTrans.app s.ι (CostructuredArrow.mk  …
    exact congr_arg _ (h (CostructuredArrow.mk t))
    -- 🎉 no goals

end ArbitraryUniverses

end CategoryTheory
