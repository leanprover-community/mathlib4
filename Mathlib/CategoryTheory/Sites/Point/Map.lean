/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ShrinkYoneda
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Point.OfIsCofiltered

/-!
# The image of a point by a cocontinuous functor

Let `F : C ⥤ D` be a cocontinuous functor between sites `(C, J)` and `(D, K)`.
Let `Φ` be a point of `(C, J)`. In this file, we define a point `Φ.map F K`
of `(D, K)` and show that there are natural isomorphisms
`(Φ.map F K).presheafFiber ≅ (Functor.whiskeringLeft _ _ A).obj F.op ⋙ Φ.presheafFiber`
and `(Φ.map F K).sheafFiber ≅ F.sheafPushforwardContinuous A J K ⋙ Φ.sheafFiber`
(the latter is defined only that `F` is also continuous).

-/

@[expose] public section

universe w v'' v' v u'' u' u

namespace CategoryTheory

open Limits Opposite

namespace GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} (Φ : Point.{w} J) (F : C ⥤ D)
  (K : GrothendieckTopology D) [F.IsCocontinuous J K]

lemma map_aux ⦃X : D⦄ (R : Sieve X) (hR : R ∈ K X)
    ⦃u : Φ.fiber.Elements⦄ (f : (CategoryOfElements.π Φ.fiber ⋙ F).obj u ⟶ X) :
    ∃ (Y : D) (g : Y ⟶ X) (_ : R.arrows g) (v : Φ.fiber.Elements)
      (q : v ⟶ u) (a : F.obj v.fst ⟶ Y), a ≫ g = F.map q.1 ≫ f := by
  obtain ⟨U, u⟩ := u
  dsimp at f ⊢
  obtain ⟨V, g, hg, v, rfl⟩ :=
    Φ.jointly_surjective _ (F.cover_lift J K (K.pullback_stable f hR)) u
  exact ⟨_, F.map g ≫ f, hg, Φ.fiber.elementsMk _ v, ⟨g, rfl⟩, 𝟙 _, by simp⟩

variable [LocallySmall.{w} D]

/-- The image of a point of a site by a cocontinuous functor. -/
noncomputable def map : Point.{w} K :=
  Point.ofIsCofiltered.{w} (CategoryOfElements.π Φ.fiber ⋙ F) (Φ.map_aux F K)

variable {A : Type u''} [Category.{v''} A] [HasColimitsOfSize.{w, w} A]

/-- Given a cocontinuous functor `F : C ⥤ D` between sites `(C, J)` and `(D, K)`,
`P` a presheaf on `D`, `X : C`, `x : Φ.fiber.obj X`, this is the canonical morphism
`P.obj (op (F.obj X)) ⟶ (Φ.map F K).presheafFiber.obj P`, which is part
of the colimit cocone `presheafFiberMapCocone`. -/
noncomputable def toPresheafFiberMap (P : Dᵒᵖ ⥤ A) (X : C) (x : Φ.fiber.obj X) :
    P.obj (op (F.obj X)) ⟶ (Φ.map F K).presheafFiber.obj P :=
  toPresheafFiberOfIsCofiltered _ (Φ.map_aux F K) (Φ.fiber.elementsMk X x) P

@[reassoc (attr := simp)]
lemma toPresheafFiberMap_w {X Y : C} (f : X ⟶ Y)
    (x : Φ.fiber.obj X) (P : Dᵒᵖ ⥤ A) :
    P.map (F.map f).op ≫ Φ.toPresheafFiberMap F K P X x =
      Φ.toPresheafFiberMap F K P Y (Φ.fiber.map f x) :=
  toPresheafFiberOfIsCofiltered_w _ (Φ.map_aux F K)
    (V := ⟨X, x⟩) (U := ⟨Y, Φ.fiber.map f x⟩) ⟨f, rfl⟩ P

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma toPresheafFiberMap_naturality {P Q : Dᵒᵖ ⥤ A} (g : P ⟶ Q) (X : C) (x : Φ.fiber.obj X) :
    Φ.toPresheafFiberMap F K P X x ≫ (Φ.map F K).presheafFiber.map g =
      g.app _ ≫ Φ.toPresheafFiberMap F K Q X x :=
  toPresheafFiberOfIsCofiltered_naturality _ _ _ _

/-- Given a cocontinuous functor `F : C ⥤ D` between sites `(C, J)` and `(D, K)`,
`P` a presheaf on `D`, this is the (colimit) cocone which expresses
`(Φ.map F K).presheafFiber.obj P` as a colimit of `P.obj (op (F.obj X))`
for `X : C`, `x : Φ.fiber.obj X`. -/
noncomputable def presheafFiberMapCocone (P : Dᵒᵖ ⥤ A) :
    Cocone ((CategoryOfElements.π Φ.fiber).op ⋙ F.op ⋙ P) where
  pt := (Φ.map F K).presheafFiber.obj P
  ι.app x := Φ.toPresheafFiberMap F K P x.unop.1 x.unop.2

/-- Given a cocontinuous functor `F : C ⥤ D` between sites `(C, J)` and `(D, K)`,
`P` a presheaf on `D`, then `(Φ.map F K).presheafFiber.obj P` is a colimit
of `P.obj (op (F.obj X))` for `X : C`, `x : Φ.fiber.obj X`. -/
noncomputable def isColimitPresheafFiberMapCocone (P : Dᵒᵖ ⥤ A) :
    IsColimit (Φ.presheafFiberMapCocone F K P) :=
  (isColimitPresheafFiberOfIsCofilteredCocone.{w} _ (Φ.map_aux F K) P)

@[ext]
lemma presheafFiberMap_hom_ext {P : Dᵒᵖ ⥤ A} {T : A}
    {f g : (Φ.map F K).presheafFiber.obj P ⟶ T}
    (h : ∀ (X : C) (x : Φ.fiber.obj X),
      Φ.toPresheafFiberMap F K P X x ≫ f = Φ.toPresheafFiberMap F K P X x ≫ g) :
    f = g :=
  (Φ.isColimitPresheafFiberMapCocone F K P).hom_ext (fun _ ↦ h _ _)

/-- Relation between the fiber functors on presheaves for the points `Φ.map F K`
and `Φ`. -/
noncomputable def presheafFiberMapObjIso (P : Dᵒᵖ ⥤ A) :
    (Φ.map F K).presheafFiber.obj P ≅ Φ.presheafFiber.obj (F.op ⋙ P) :=
  IsColimit.coconePointUniqueUpToIso (Φ.isColimitPresheafFiberMapCocone F K P)
    (Φ.isColimitPresheafFiberCocone (F.op ⋙ P))

@[reassoc (attr := simp)]
lemma toPresheafFiberMap_presheafFiberMapObjIso_hom (P : Dᵒᵖ ⥤ A) (X : C) (x : Φ.fiber.obj X) :
    Φ.toPresheafFiberMap F K P X x ≫ (Φ.presheafFiberMapObjIso F K P).hom =
      Φ.toPresheafFiber X x (F.op ⋙ P) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (Φ.isColimitPresheafFiberMapCocone F K P) _ ⟨X, x⟩

variable (A) in
/-- Relation between the fiber functors on presheaves for the points `Φ.map F K`
and `Φ` when `F : C ⥤ D` is a cocontinuous functor between sites `(C, J)` and `(D, K)`. -/
noncomputable def presheafFiberMapIso :
    (Φ.map F K).presheafFiber ≅
      (Functor.whiskeringLeft _ _ A).obj F.op ⋙ Φ.presheafFiber :=
  NatIso.ofComponents (Φ.presheafFiberMapObjIso F K)

variable (A) in
/-- Relation between the fiber functors on presheaves for the points `Φ.map F K`
and `Φ` when `F : C ⥤ D` is a cocontinuous and continuous functor between
sites `(C, J)` and `(D, K)`. -/
noncomputable def sheafFiberMapIso [Functor.IsContinuous.{v''} F J K] :
    (Φ.map F K).sheafFiber ≅
      F.sheafPushforwardContinuous A J K ⋙ Φ.sheafFiber :=
  Functor.isoWhiskerLeft (sheafToPresheaf K A) (Φ.presheafFiberMapIso F K A)

end GrothendieckTopology.Point

end CategoryTheory
