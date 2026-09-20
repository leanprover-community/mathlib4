/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.DenseAtCoyoneda
public import Mathlib.CategoryTheory.Functor.KanExtension.Yoneda

/-!
# Colimit of representables

All the definitions in this file are deprecated. The results in this file
are now in the folder `Mathlib/CategoryTheory/Functor/KanExtension/`.
In particular, the fact that any presheaf of types is a colimit of
representable presheaves is now proven in the fil
`Mathlib/CategoryTheory/Functor/KanExtension/DenseAtYoneda.lean`.

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

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `restrictedULiftYonedaHomEquiv`. -/
@[deprecated "use `restrictedShrinkYonedaHomEquivAux` instead." (since := "2026-08-17")]
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
        simpa using! (f.naturality φ).symm }
  invFun g :=
    { app y := (uliftYonedaEquiv.{max w v₂} (y.hom ≫ g)).down
      naturality y y' f := by
        dsimp
        rw [comp_id, ← CostructuredArrow.w f, assoc,
          map_comp_uliftYonedaEquiv_down] }
  left_inv f := by
    ext X
    let e : CostructuredArrow.mk
      (uliftYonedaEquiv.{max w v₂}.symm (X.hom.app (op X.left) ⟨𝟙 X.left⟩)) ≅ X :=
        CostructuredArrow.isoMk (Iso.refl _) (by
          ext Y x
          dsimp
          simp [← NatTrans.naturality_apply])
    simpa [e] using! f.naturality e.inv
  right_inv g := by
    ext X x
    apply ULift.down_injective
    simp [uliftYonedaEquiv]

@[reassoc, deprecated "Use `restrictedShrinkYonedaHomEquiv_symm_naturality_right` instead."
  (since := "2026-08-17")]
lemma restrictedULiftYonedaHomEquiv'_symm_naturality_right (P : Cᵒᵖ ⥤ Type max w v₁ v₂)
    {E E' : ℰ} (g : E ⟶ E') (f : P ⟶ (restrictedULiftYoneda.{max w v₁} A).obj E) :
    (restrictedULiftYonedaHomEquiv' A P E').symm (f ≫ (restrictedULiftYoneda A).map g) =
      (restrictedULiftYonedaHomEquiv' A P E).symm f ≫ (Functor.const _).map g := by
  rfl

@[reassoc, deprecated "Use `restrictedShrinkYonedaHomEquiv_symm_naturality_left`"
  (since := "2026-08-17")]
lemma restrictedULiftYonedaHomEquiv'_symm_app_naturality_left
    {P Q : Cᵒᵖ ⥤ Type max w v₁ v₂} (f : P ⟶ Q) (E : ℰ)
    (g : Q ⟶ (restrictedULiftYoneda.{max w v₁} A).obj E)
    (p : CostructuredArrow uliftYoneda.{max w v₂} P) :
    ((restrictedULiftYonedaHomEquiv' A P E).symm (f ≫ g)).app p =
      ((restrictedULiftYonedaHomEquiv' A Q E).symm g).app
        ((CostructuredArrow.map f).obj p) :=
  rfl

section

variable {A} (P : ℰᵒᵖ ⥤ Type max w v₁ v₂)
  [(uliftYoneda.{max w v₂}).HasPointwiseLeftKanExtension A]
  (L : (Cᵒᵖ ⥤ Type max w v₁ v₂) ⥤ ℰ)
  (α : A ⟶ uliftYoneda.{max w v₂} ⋙ L) [L.IsLeftKanExtension α]

/-- Auxiliary definition for `uliftYonedaAdjunction`. -/
@[deprecated "Use `restrictedULiftYonedaAdjunction`" (since := "2026-08-27")]
noncomputable def restrictedULiftYonedaHomEquiv (P : Cᵒᵖ ⥤ Type max w v₁ v₂) (E : ℰ) :
    (L.obj P ⟶ E) ≃ (P ⟶ (restrictedULiftYoneda.{max w v₁} A).obj E) :=
  (Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension _ α P).homEquiv.trans
    (restrictedULiftYonedaHomEquiv' A P E)

/-- If `L : (Cᵒᵖ ⥤ Type max w v₁ v₂) ⥤ ℰ` is a pointwise left Kan extension
of a functor `A : C ⥤ ℰ` along the Yoneda embedding,
then `L` is a left adjoint of `restrictedULiftYoneda A : ℰ ⥤ Cᵒᵖ ⥤ Type max w v₁ v₂` -/
@[deprecated (since := "2026-08-17")] alias uliftYonedaAdjunction :=
  restrictedULiftYonedaAdjunction

@[deprecated (since := "2026-08-17")] alias uliftYonedaAdjunction_unit_app_app :=
  restrictedULiftYonedaAdjunction_unit_app_app

@[deprecated (since := "2026-08-17")] alias uliftYonedaAdjunction_homEquiv_app :=
  restrictedULiftYonedaAdjunction_homEquiv_app

variable (A)

/-- A pointwise left Kan extension along the Yoneda embedding is an extension. -/
@[deprecated "No replacement" (since := "2026-08-17")]
noncomputable def isExtensionAlongULiftYoneda :
    uliftYoneda.{max w v₂} ⋙ uliftYoneda.leftKanExtension A ≅ A :=
  (asIso (uliftYoneda.leftKanExtensionUnit A)).symm

end

/-- Given `P : Cᵒᵖ ⥤ Type max w v₁`, this is the functor from the opposite category
of the category of elements of `X` which sends an element in `P.obj (op X)` to the
presheaf represented by `X`. The definition `coconeOfRepresentable`
gives a cocone for this functor which is a colimit and has point `P`.
-/
@[simps! obj map, deprecated "See `denseAtUliftYoneda`" (since := "2026-08-17")]
def functorToRepresentables (P : Cᵒᵖ ⥤ Type max w v₁) :
    P.Elementsᵒᵖ ⥤ Cᵒᵖ ⥤ Type max w v₁ :=
  (Functor.Elements.π P).leftOp ⋙ uliftYoneda.{w}

set_option backward.defeqAttrib.useBackward true in
/-- This is a cocone with point `P` for the functor `functorToRepresentables P`. It is shown in
`colimitOfRepresentable P` that this cocone is a colimit: that is, we have exhibited an arbitrary
presheaf `P` as a colimit of representables.

The construction of [MM92], Chapter I, Section 5, Corollary 3.
-/
@[simps, deprecated "See `denseAtUliftYoneda`" (since := "2026-08-17")]
def coconeOfRepresentable (P : Cᵒᵖ ⥤ Type max w v₁) :
    Cocone (functorToRepresentables P) where
  pt := P
  ι :=
    { app x := uliftYonedaEquiv.symm x.unop.2
      naturality {x₁ x₂} f := by
        dsimp
        rw [comp_id, ← uliftYonedaEquiv_symm_map, f.unop.2] }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The legs of the cocone `coconeOfRepresentable` are natural in the choice of presheaf. -/
@[deprecated "No replacement" (since := "2026-08-17")]
theorem coconeOfRepresentable_naturality
    {P₁ P₂ : Cᵒᵖ ⥤ Type max w v₁} (α : P₁ ⟶ P₂) (j : P₁.Elementsᵒᵖ) :
    (coconeOfRepresentable P₁).ι.app j ≫ α =
      (coconeOfRepresentable P₂).ι.app (α.mapElements.op.obj j) := by
  ext T f
  simp [uliftYonedaEquiv]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The cocone with point `P` given by `coconeOfRepresentable` is a colimit:
that is, we have exhibited an arbitrary presheaf `P` as a colimit of representables.

The result of [MM92], Chapter I, Section 5, Corollary 3.
-/
@[deprecated denseAtUliftYoneda +typeChanged (since := "2026-08-17")]
def colimitOfRepresentable (P : Cᵒᵖ ⥤ Type max w v₁) :
    IsColimit (coconeOfRepresentable P) where
  desc s :=
    { app X := ↾fun x ↦ uliftYonedaEquiv
        (s.ι.app (Opposite.op (Functor.elementsMk P X x)))
      naturality X Y f := by
        ext x
        have := s.w (Quiver.Hom.op (Functor.Elements.homMk (x := P.elementsMk X x)
          (y := P.elementsMk Y (P.map f x)) f rfl))
        dsimp at this x ⊢
        rw [← this, uliftYonedaEquiv_comp]
        dsimp
        rw [uliftYonedaEquiv_apply, uliftYonedaEquiv_apply,
          ← NatTrans.naturality_apply]
        simp [uliftYoneda] }
  fac s j := by
    ext X x
    let φ : j.unop ⟶ (Functor.elementsMk P _
      ((uliftYonedaEquiv.symm (unop j).val).app X x)) := ⟨x.down.op, rfl⟩
    have := s.w φ.op
    dsimp [φ] at this x ⊢
    rw [← this, uliftYonedaEquiv_apply]
    simp [uliftYoneda]
  uniq s m hm := by
    ext X x
    simp only [functorToRepresentables_obj, coconeOfRepresentable_pt, Functor.const_obj_obj,
      coconeOfRepresentable_ι_app, Functor.leftOp_obj, Functor.Elements.π_obj, op_unop,
      TypeCat.Fun.toFun_apply, hom_ofHom, TypeCat.Fun.coe_mk] at hm ⊢
    rw [← hm, uliftYonedaEquiv_comp, Equiv.apply_symm_apply]

variable {A : C ⥤ ℰ}

example [HasColimitsOfSize.{v₁, max w u₁ v₁ v₂} ℰ] :
    uliftYoneda.{max w v₂}.HasPointwiseLeftKanExtension A := by
  infer_instance

variable [uliftYoneda.{max w v₂}.HasPointwiseLeftKanExtension A]

@[deprecated (since := "2026-08-18")] alias isLeftKanExtension_of_preservesColimits :=
 isLeftKanExtension_along_uliftYoneda_of_preservesColimits

/-- Show that `uliftYoneda.leftKanExtension A` is the unique colimit-preserving
functor which extends `A` to the presheaf category.

The second part of [MM92], Chapter I, Section 5, Corollary 4.
See Property 3 of https://ncatlab.org/nlab/show/Yoneda+extension#properties.
-/
@[deprecated "No replacement" (since := "2026-08-17")]
noncomputable def uniqueExtensionAlongULiftYoneda (L : (Cᵒᵖ ⥤ Type max w v₁ v₂) ⥤ ℰ)
    (e : uliftYoneda.{max w v₂} ⋙ L ≅ A)
    [PreservesColimitsOfSize.{v₁, max w u₁ v₁ v₂} L] :
    L ≅ uliftYoneda.{max w v₂}.leftKanExtension A :=
  have := isLeftKanExtension_along_uliftYoneda_of_preservesColimits e
  Functor.leftKanExtensionUnique _ e.inv _ (uliftYoneda.leftKanExtensionUnit A)

section

variable {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)

namespace compULiftYonedaIsoULiftYonedaCompLan

variable {F}

section

variable {X : C} {G : (Cᵒᵖ ⥤ Type max w v₁ v₂) ⥤ Dᵒᵖ ⥤ Type max w v₁ v₂}
  (φ : F ⋙ uliftYoneda.{max w v₁} ⟶ uliftYoneda.{max w v₂} ⋙ G)

/-- Auxiliary definition for `presheafHom`. -/
@[deprecated "No replacement." (since := "2026-08-23")]
def coconeApp {P : Cᵒᵖ ⥤ Type max w v₁ v₂} (x : P.Elements) :
    uliftYoneda.{max w v₂}.obj x.1.unop ⟶ F.op ⋙ G.obj P :=
  uliftYonedaEquiv.symm
    ((G.map (uliftYonedaEquiv.{max w v₂}.symm x.2)).app _
      ((φ.app x.1.unop).app _ (ULift.up (𝟙 _))))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[deprecated "No replacement." (since := "2026-08-23"), reassoc (attr := simp)]
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
@[deprecated "No replacement" (since := "2026-09-20")]
def presheafHom (P : Cᵒᵖ ⥤ Type max w v₁ v₂) : P ⟶ F.op ⋙ G.obj P :=
  (colimitOfRepresentable P).desc
    (Cocone.mk _ { app x := coconeApp.{w} φ x.unop })

@[deprecated "No replacement" (since := "2026-09-20")]
lemma uliftYonedaEquiv_ι_presheafHom (P : Cᵒᵖ ⥤ Type max w v₁ v₂) {X : C}
    (f : uliftYoneda.{max w v₂}.obj X ⟶ P) :
    uliftYonedaEquiv (f ≫ presheafHom.{w} φ P) =
      (G.map f).app (Opposite.op (F.obj X)) ((φ.app X).app _ (ULift.up (𝟙 _))) := by
  obtain ⟨x, rfl⟩ := uliftYonedaEquiv.symm.surjective f
  erw [(colimitOfRepresentable P).fac _ (Opposite.op (P.elementsMk _ x))]
  dsimp only [coconeApp]
  apply Equiv.apply_symm_apply

@[deprecated "No replacement" (since := "2026-09-20")]
lemma uliftYonedaEquiv_presheafHom_uliftYoneda_obj (X : C) :
    uliftYonedaEquiv.{max w v₂} (presheafHom.{w} φ (uliftYoneda.{max w v₂}.obj X)) =
      ((φ.app X).app (F.op.obj (Opposite.op X)) (ULift.up (𝟙 _))) := by
  simpa using! uliftYonedaEquiv_ι_presheafHom.{w} φ (uliftYoneda.obj X) (𝟙 _)

set_option backward.defeqAttrib.useBackward true in
@[reassoc, deprecated "No replacement" (since := "2026-09-20")]
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
@[deprecated "No replacement" (since := "2026-08-23")]
noncomputable def natTrans : F.op.lan ⟶ G :=
  Functor.descOfIsLeftKanExtension _ (compULiftYonedaIsoULiftYonedaCompLan.{w} F).hom _ φ

@[deprecated "No replacemenet" (since := "2026-08-23")]
lemma natTrans_app_uliftYoneda_obj (X : C) :
    (natTrans.{w} φ).app (uliftYoneda.{max w v₂}.obj X) =
      (compULiftYonedaIsoULiftYonedaCompLan.{w} F).inv.app X ≫ φ.app X := by
  rw [← cancel_epi ((compULiftYonedaIsoULiftYonedaCompLan.{w} F).hom.app X),
    Iso.hom_inv_id_app_assoc]
  apply Functor.descOfIsLeftKanExtension_fac_app

/-- Given functors `F : C ⥤ D` and
`G : (Cᵒᵖ ⥤ Type max w v₁ v₂) ⥤ (Dᵒᵖ ⥤ Type max w v₁ v₂)`,
and a natural transformation `φ : F ⋙ uliftYoneda ⟶ uliftYoneda ⋙ G`, this is the
(natural) morphism `P ⟶ F.op ⋙ G.obj P` for all `P : Cᵒᵖ ⥤ Type max w v₁ v₂` that is
determined by `φ`. -/
@[deprecated "No replacement" (since := "2026-08-23")]
noncomputable def presheafHom' (P : Cᵒᵖ ⥤ Type max w v₁ v₂) : P ⟶ F.op ⋙ G.obj P :=
  (F.op.lanAdjunction _).homEquiv _ _ ((natTrans.{w} φ).app P)

end

variable [∀ (P : Cᵒᵖ ⥤ Type max w v₁ v₂), F.op.HasLeftKanExtension P]

/-- Given a functor `F : C ⥤ D`, this definition is part of the verification that
`Functor.LeftExtension.mk F.op.lan (compULiftYonedaIsoULiftYonedaCompLan F).hom`
is universal, i.e. that  `F.op.lan : (Cᵒᵖ ⥤ Type max w v₁ v₂) ⥤ Dᵒᵖ ⥤ Type max w v₁ v₂`
is the left Kan extension of `F ⋙ uliftYoneda : C ⥤ Dᵒᵖ ⥤ Type max w v₁ v₂`
along `uliftYoneda : C ⥤ Cᵒᵖ ⥤ Type max w v₁ v₂`. -/
@[deprecated "No replacement" (since := "2026-08-23")]
noncomputable def extensionHom
    (Φ : uliftYoneda.{max w v₂}.LeftExtension (F ⋙ uliftYoneda.{max w v₁})) :
    Functor.LeftExtension.mk F.op.lan (compULiftYonedaIsoULiftYonedaCompLan.{w} F).hom ⟶ Φ :=
  IsInitial.to (Functor.isUniversalOfIsLeftKanExtension _
    (compULiftYonedaIsoULiftYonedaCompLan.{w} F).hom) _

@[ext, deprecated "No replacement" (since := "2026-08-23")]
lemma hom_ext {Φ : uliftYoneda.{max w v₂}.LeftExtension (F ⋙ uliftYoneda.{max w v₁})}
    (f g : Functor.LeftExtension.mk F.op.lan (compULiftYonedaIsoULiftYonedaCompLan F).hom ⟶ Φ) :
    f = g :=
  IsInitial.hom_ext (Functor.isUniversalOfIsLeftKanExtension _
    (compULiftYonedaIsoULiftYonedaCompLan.{w} F).hom) _ _

end compULiftYonedaIsoULiftYonedaCompLan

end

set_option backward.defeqAttrib.useBackward true in
/-- For a presheaf `P`, consider the forgetful functor from the category of representable
    presheaves over `P` to the category of presheaves. There is a tautological cocone over this
    functor whose leg for a natural transformation `V ⟶ P` with `V` representable is just that
    natural transformation. (In this version, we allow the presheaf `P` to have values in
    a larger universe.) -/
@[simps, deprecated "See `denseAtUliftYoneda`" (since := "2026-09-20")]
def tautologicalCocone' (P : Cᵒᵖ ⥤ Type max w v₁) :
    Cocone (CostructuredArrow.proj uliftYoneda.{w} P ⋙ uliftYoneda.{w}) where
  pt := P
  ι := { app X := X.hom }

/-- The tautological cocone with point `P` is a colimit cocone, exhibiting `P` as a colimit of
    representables. (In this version, we allow the presheaf `P` to have values in
    a larger universe.)

    Proposition 2.6.3(i) in [Kashiwara2006] -/
@[deprecated "denseAtUliftYoneda" (since := "2026-09-20")]
noncomputable def isColimitTautologicalCocone' (P : Cᵒᵖ ⥤ Type max w v₁) :
    IsColimit (tautologicalCocone'.{w} P) :=
  denseAtUliftYoneda P

set_option backward.defeqAttrib.useBackward true in
/-- For a presheaf `P`, consider the forgetful functor from the category of representable
    presheaves over `P` to the category of presheaves. There is a tautological cocone over this
    functor whose leg for a natural transformation `V ⟶ P` with `V` representable is just that
    natural transformation. -/
@[simps, deprecated "See `denseAtYoneda`" (since := "2026-09-20")]
def tautologicalCocone (P : Cᵒᵖ ⥤ Type v₁) :
    Cocone (CostructuredArrow.proj yoneda P ⋙ yoneda) where
  pt := P
  ι := { app X := X.hom }

/-- The tautological cocone with point `P` is a colimit cocone, exhibiting `P` as a colimit of
    representables.

    Proposition 2.6.3(i) in [Kashiwara2006] -/
@[deprecated "See `denseAtYoneda`" (since := "2026-09-20")]
noncomputable def isColimitTautologicalCocone (P : Cᵒᵖ ⥤ Type v₁) :
    IsColimit (tautologicalCocone P) :=
  denseAtYoneda P

end Presheaf

namespace Functor.Elements

variable [LocallySmall.{w} C] (F : C ⥤ Type w)

set_option backward.defeqAttrib.useBackward true in
/-- If `F : C ⥤ Type w` and `C` is locally `w`-small, then for any `X : C`,
this is the colimit cocone which identifies `F.obj X` to the colimit of
`(CategoryOfElements.π F).op ⋙ shrinkYoneda.obj X`. -/
@[simps, deprecated "Use shrinkCoyonedaCocone" (since := "2026-09-20")]
noncomputable def coconeπOpCompShrinkYonedaObj (X : C) :
    Cocone ((Functor.Elements.π F).op ⋙ shrinkYoneda.{w}.obj X) where
  pt := F.obj X
  ι.app u := ↾fun t ↦ F.map (shrinkYonedaObjObjEquiv t) u.unop.val
  ι.naturality u₁ u₂ g := by
    ext f
    obtain ⟨f, rfl⟩ := shrinkYonedaObjObjEquiv.symm.surjective f
    simp [shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm.{w}]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `F : C ⥤ Type w` and `C` is locally `w`-small, then for any `X : C`,
`F.obj X` identifies to the colimit of
`(CategoryOfElements.π F).op ⋙ shrinkYoneda.obj X`. -/
@[deprecated isColimitShrinkCoyonedaCoconeObj +typeChanged (since := "2026-09-20")]
noncomputable def isColimitCoconeπOpCompShrinkYonedaObj (X : C) :
    IsColimit (coconeπOpCompShrinkYonedaObj F X) :=
  isColimitShrinkCoyonedaCoconeObj F X

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp),
deprecated shrinkYoneda_map_app_shrinkCoyonedaCocone_ι_app_app +typeChanged (since := "2026-09-20")]
lemma shrinkYoneda_map_app_coconeπOpCompShrinkYonedaObj_ι_app
    {X₁ X₂ : C} (f : X₁ ⟶ X₂) (u : F.Elements) :
    dsimp% (shrinkYoneda.{w}.map f).app (op u.obj) ≫
      (coconeπOpCompShrinkYonedaObj F X₂).ι.app (op u) =
    (coconeπOpCompShrinkYonedaObj F X₁).ι.app (op u) ≫ F.map f := by
  ext g
  obtain ⟨g, rfl⟩ := shrinkYonedaObjObjEquiv.symm.surjective g
  simp [shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm.{w}]

set_option backward.defeqAttrib.useBackward true in
/-- If `C` is a locally `w`-small category, this is a (colimit) cocone
expressing `F : C ⥤ Type w` as a colimit of corepresentable functors. -/
@[deprecated (since := "2026-09-20")] alias coconeπOpCompShrinkYonedaFlip := shrinkCoyonedaCocone

/-- If `F : C ⥤ Type w` and `C` is locally `w`-small, then `F` identifies to the colimit
of `(CategoryOfElements.π F).op ⋙ shrinkYoneda.{w}.flip`. -/
@[deprecated (since := "2026-09-20")] alias isColimitCoconeπOpCompShrinkYonedaFlip :=
  isColimitShrinkCoyonedaCocone

@[deprecated (since := "2026-09-20")] alias isInitialElementsMkShrinkYonedaObjObjEquivId :=
  isInitialShrinkCoyonedaObj

end Functor.Elements

end CategoryTheory
