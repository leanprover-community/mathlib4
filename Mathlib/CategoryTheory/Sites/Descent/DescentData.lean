/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Descent.IsPrestack

/-!
# Descent data

In this file, given a pseudofunctor `F` from `LocallyDiscrete Cᵒᵖ` to `Cat`,
and a family of maps `f i : X i ⟶ S` in the category `C`,
we define the category `F.DescentData f` of objects over the `X i`
equipped with descent data relative to the morphisms `f i : X i ⟶ S`.

We show that up to an equivalence, the category `F.DescentData f` is unchanged
when we replace `S` by an isomorphic object, or the family `f i : X i ⟶ S`
by another family which generates the same sieve
(see `Pseudofunctor.DescentData.pullFunctorEquivalence`).

Given a presieve `R`, we introduce predicates `F.IsPrestackFor R` and `F.IsStackFor R`
saying the functor `F.DescentData (fun (f : R.category) ↦ f.obj.hom)` attached
to `R` is respectively fully faithful or an equivalence. We show that
`F` satisfies `F.IsPrestack J` for a Grothendieck topology `J` iff it
satisfies `F.IsPrestackFor R.arrows` for all covering sieves `R`.

## TODO (@joelriou, @chrisflav)
* Introduce multiple variants of `DescentData` (when `C` has pullbacks,
  when `F` also has a covariant functoriality, etc.).

-/

@[expose] public section

universe t t' t'' v' v u' u

namespace CategoryTheory

open Opposite

namespace Pseudofunctor

open LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C] (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
  {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)

/-- Given a pseudofunctor `F` from `LocallyDiscrete Cᵒᵖ` to `Cat`, and a family of
morphisms `f i : X i ⟶ S`, the objects of the category of descent data for
the `X i` relative to the morphisms `f i` consist of families of
objects `obj i` in `F.obj (.mk (op (X i)))` together with morphisms `hom`
between the pullbacks of `obj i₁` and `obj i₂` over any object `Y` which maps
to both `X i₁` and `X i₂` (in a way that is compatible with the morphisms to `S`).
The compatibilities these morphisms satisfy imply that the morphisms `hom` are isomorphisms. -/
structure DescentData where
  /-- The objects over `X i` for all `i` -/
  obj (i : ι) : F.obj (.mk (op (X i)))
  /-- The compatibility morphisms after pullbacks. It follows from the conditions
  `hom_self` and `hom_comp` that these are isomorphisms, see
  `CategoryTheory.Pseudofunctor.DescentData.iso` below. -/
  hom ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (_hf₁ : f₁ ≫ f i₁ = q := by cat_disch) (_hf₂ : f₂ ≫ f i₂ = q := by cat_disch) :
      (F.map f₁.op.toLoc).toFunctor.obj (obj i₁) ⟶ (F.map f₂.op.toLoc).toFunctor.obj (obj i₂)
  pullHom_hom ⦃Y' Y : C⦄ (g : Y' ⟶ Y) (q : Y ⟶ S) (q' : Y' ⟶ S) (hq : g ≫ q = q')
    ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q)
    (gf₁ : Y' ⟶ X i₁) (gf₂ : Y' ⟶ X i₂) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
      pullHom (hom q f₁ f₂) g gf₁ gf₂ = hom q' gf₁ gf₂ := by cat_disch
  hom_self ⦃Y : C⦄ (q : Y ⟶ S) ⦃i : ι⦄ (g : Y ⟶ X i) (_ : g ≫ f i = q) :
      hom q g g = 𝟙 _ := by cat_disch
  hom_comp ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ i₃ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (f₃ : Y ⟶ X i₃)
      (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) (hf₃ : f₃ ≫ f i₃ = q) :
      hom q f₁ f₂ hf₁ hf₂ ≫ hom q f₂ f₃ hf₂ hf₃ = hom q f₁ f₃ hf₁ hf₃ := by cat_disch

namespace DescentData

variable {F f} (D : F.DescentData f)

attribute [local simp] hom_self pullHom_hom
attribute [reassoc (attr := simp)] hom_comp

/-- The morphisms `DescentData.hom`, as isomorphisms. -/
@[simps]
def iso ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (_hf₁ : f₁ ≫ f i₁ = q := by cat_disch) (_hf₂ : f₂ ≫ f i₂ = q := by cat_disch) :
    (F.map f₁.op.toLoc).toFunctor.obj (D.obj i₁) ≅
      (F.map f₂.op.toLoc).toFunctor.obj (D.obj i₂) where
  hom := D.hom q f₁ f₂
  inv := D.hom q f₂ f₁

instance {Y : C} (q : Y ⟶ S) {i₁ i₂ : ι} (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    IsIso (D.hom q f₁ f₂ hf₁ hf₂) :=
  (D.iso q f₁ f₂).isIso_hom

/-- The type of morphisms in the category `Pseudofunctor.DescentData`. -/
@[ext]
structure Hom (D₁ D₂ : F.DescentData f) where
  /-- The morphisms between the `obj` fields of descent data. -/
  hom (i : ι) : D₁.obj i ⟶ D₂.obj i
  comm ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁)
    (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    (F.map f₁.op.toLoc).toFunctor.map (hom i₁) ≫ D₂.hom q f₁ f₂ =
        D₁.hom q f₁ f₂ ≫ (F.map f₂.op.toLoc).toFunctor.map (hom i₂) := by cat_disch

attribute [reassoc (attr := local simp)] Hom.comm

instance : Category (F.DescentData f) where
  Hom := Hom
  id D := { hom _ := 𝟙 _ }
  comp φ φ' := { hom i := φ.hom i ≫ φ'.hom i }

@[ext]
lemma hom_ext {D₁ D₂ : F.DescentData f} {φ φ' : D₁ ⟶ D₂}
    (h : ∀ i, φ.hom i = φ'.hom i) : φ = φ' :=
  Hom.ext (funext h)

@[simp]
lemma id_hom (D : F.DescentData f) (i : ι) : Hom.hom (𝟙 D) i = 𝟙 _ := rfl

@[simp, reassoc]
lemma comp_hom {D₁ D₂ D₃ : F.DescentData f} (φ : D₁ ⟶ D₂) (φ' : D₂ ⟶ D₃) (i : ι) :
    (φ ≫ φ').hom i = φ.hom i ≫ φ'.hom i := rfl

/-- Given a family of morphisms `f : X i ⟶ S`, and `M : F.obj (.mk (op S))`,
this is the object in `F.DescentData f` that is obtained by pulling back `M`
over the `X i`. -/
@[simps]
def ofObj (M : F.obj (.mk (op S))) : F.DescentData f where
  obj i := (F.map (f i).op.toLoc).toFunctor.obj M
  hom Y q i₁ i₂ f₁ f₂ hf₁ hf₂ :=
    (F.mapComp' (f i₁).op.toLoc f₁.op.toLoc q.op.toLoc (by grind)).inv.toNatTrans.app _ ≫
      (F.mapComp' (f i₂).op.toLoc f₂.op.toLoc q.op.toLoc (by grind)).hom.toNatTrans.app _
  pullHom_hom Y' Y g q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
    simp only [pullHom, Functor.map_comp, Category.assoc,
      F.mapComp'₀₁₃_inv_app (f i₁).op.toLoc f₁.op.toLoc g.op.toLoc q.op.toLoc
        gf₁.op.toLoc q'.op.toLoc (by grind) (by grind) (by grind),
      F.mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom_app (f i₂).op.toLoc f₂.op.toLoc g.op.toLoc
      q.op.toLoc gf₂.op.toLoc q'.op.toLoc (by grind) (by grind) (by grind)]

/-- Constructor for isomorphisms in `Pseudofunctor.DescentData`. -/
@[simps]
def isoMk {D₁ D₂ : F.DescentData f} (e : ∀ (i : ι), D₁.obj i ≅ D₂.obj i)
    (comm : ∀ ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁)
    (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q),
    (F.map f₁.op.toLoc).toFunctor.map (e i₁).hom ≫ D₂.hom q f₁ f₂ =
      D₁.hom q f₁ f₂ ≫ (F.map f₂.op.toLoc).toFunctor.map (e i₂).hom := by cat_disch) : D₁ ≅ D₂ where
  hom :=
    { hom i := (e i).hom }
  inv :=
    { hom i := (e i).inv
      comm Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := by
        rw [← cancel_mono ((F.map f₂.op.toLoc).toFunctor.map (e i₂).hom), Category.assoc,
          Category.assoc, Iso.map_inv_hom_id, Category.comp_id,
          ← cancel_epi ((F.map f₁.op.toLoc).toFunctor.map (e i₁).hom),
          Iso.map_hom_inv_id_assoc, comm q f₁ f₂ hf₁ hf₂] }

end DescentData

/-- The functor `F.obj (.mk (op S)) ⥤ F.DescentData f`. -/
@[simps]
def toDescentData : F.obj (.mk (op S)) ⥤ F.DescentData f where
  obj M := .ofObj M
  map {M M'} φ := { hom i := (F.map (f i).op.toLoc).toFunctor.map φ }

namespace DescentData

section

variable {F f} {S' : C} {p : S' ⟶ S} {ι' : Type t'} {X' : ι' → C} {f' : ∀ j, X' j ⟶ S'}
  {α : ι' → ι} {p' : ∀ j, X' j ⟶ X (α j)} (w : ∀ j, p' j ≫ f (α j) = f' j ≫ p)

/-- Auxiliary definition for `pullFunctor`. -/
def pullFunctorObjHom (D : F.DescentData f)
    ⦃Y : C⦄ (q : Y ⟶ S') ⦃j₁ j₂ : ι'⦄ (f₁ : Y ⟶ X' j₁) (f₂ : Y ⟶ X' j₂)
    (hf₁ : f₁ ≫ f' j₁ = q := by cat_disch) (hf₂ : f₂ ≫ f' j₂ = q := by cat_disch) :
    (F.map f₁.op.toLoc).toFunctor.obj ((F.map (p' j₁).op.toLoc).toFunctor.obj (D.obj (α j₁))) ⟶
      (F.map f₂.op.toLoc).toFunctor.obj ((F.map (p' j₂).op.toLoc).toFunctor.obj (D.obj (α j₂))) :=
  (F.mapComp (p' j₁).op.toLoc f₁.op.toLoc).inv.toNatTrans.app _ ≫
    D.hom (q ≫ p) (f₁ ≫ p' _) (f₂ ≫ p' _) (by simp [w, reassoc_of% hf₁])
      (by simp [w, reassoc_of% hf₂]) ≫
    (F.mapComp (p' j₂).op.toLoc f₂.op.toLoc).hom.toNatTrans.app _

@[reassoc]
lemma pullFunctorObjHom_eq (D : F.DescentData f)
    ⦃Y : C⦄ (q : Y ⟶ S') ⦃j₁ j₂ : ι'⦄ (f₁ : Y ⟶ X' j₁) (f₂ : Y ⟶ X' j₂)
    (q' : Y ⟶ S) (f₁' : Y ⟶ X (α j₁)) (f₂' : Y ⟶ X (α j₂))
    (hf₁ : f₁ ≫ f' j₁ = q := by cat_disch) (hf₂ : f₂ ≫ f' j₂ = q := by cat_disch)
    (hq' : q ≫ p = q' := by cat_disch)
    (hf₁' : f₁ ≫ p' j₁ = f₁' := by cat_disch)
    (hf₂' : f₂ ≫ p' j₂ = f₂' := by cat_disch) :
  pullFunctorObjHom w D q f₁ f₂ =
    (F.mapComp' _ _ _).inv.toNatTrans.app _ ≫ D.hom q' f₁' f₂'
      (by rw [← hq', ← hf₁', Category.assoc, w, reassoc_of% hf₁])
      (by rw [← hq', ← hf₂', Category.assoc, w, reassoc_of% hf₂]) ≫
      (F.mapComp' _ _ _).hom.toNatTrans.app _ := by
  subst hq' hf₁' hf₂'
  simp [mapComp'_eq_mapComp, pullFunctorObjHom]

/-- Auxiliary definition for `pullFunctor`. -/
@[simps]
def pullFunctorObj (D : F.DescentData f) :
    F.DescentData f' where
  obj j := (F.map (p' _).op.toLoc).toFunctor.obj (D.obj (α j))
  hom Y q j₁ j₂ f₁ f₂ hf₁ hf₂ := pullFunctorObjHom w _ _ _ _
  pullHom_hom Y' Y g q q' hq j₁ j₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
    rw [pullFunctorObjHom_eq _ _ _ _ _ (q' ≫ p) (gf₁ ≫ p' j₁) (gf₂ ≫ p' j₂),
      pullFunctorObjHom_eq _ _ _ _ _ (q ≫ p) (f₁ ≫ p' j₁) (f₂ ≫ p' j₂)]
    rw [← D.pullHom_hom g (q ≫ p) (q' ≫ p) (by rw [reassoc_of% hq])
      (f₁ ≫ p' j₁) (f₂ ≫ p' j₂) (by rw [Category.assoc, w, reassoc_of% hf₁])
      (by rw [Category.assoc, w, reassoc_of% hf₂]) (gf₁ ≫ p' j₁) (gf₂ ≫ p' j₂)
      (by cat_disch) (by cat_disch)]
    dsimp [pullHom]
    simp only [Functor.map_comp, Category.assoc]
    rw [F.mapComp'₀₁₃_inv_comp_mapComp'₀₂₃_hom_app_assoc _ _ _ _ _ _ _ _ (by cat_disch),
      mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom_app _ _ _ _ _ _ _ _ _ (by cat_disch)]
  hom_self Y q j g hg := by
    rw [pullFunctorObjHom_eq _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl,
      D.hom_self _ _ (by cat_disch)]
    simp
  hom_comp Y q j₁ j₂ j₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ := by
    rw [pullFunctorObjHom_eq _ _ _ _ _ (q ≫ p) (f₁ ≫ p' j₁) (f₂ ≫ p' j₂),
      pullFunctorObjHom_eq _ _ _ _ _ (q ≫ p) (f₂ ≫ p' j₂) (f₃ ≫ p' j₃),
      pullFunctorObjHom_eq _ _ _ _ _ (q ≫ p) (f₁ ≫ p' j₁) (f₃ ≫ p' j₃)]
    simp

variable (F)

/-- Given a family of morphisms `f : X i ⟶ S` and `f' : X' j ⟶ S'`, and suitable
commutative diagrams `p' j ≫ f (α j) = f' j ≫ p`, this is the
induced functor `F.DescentData f ⥤ F.DescentData f'`. (Up to a (unique) isomorphism,
this functor only depends on `f` and `f'`, see `pullFunctorIso`.) -/
@[simps]
def pullFunctor : F.DescentData f ⥤ F.DescentData f' where
  obj D := pullFunctorObj w D
  map {D₁ D₂} φ :=
    { hom j := (F.map (p' j).op.toLoc).toFunctor.map (φ.hom (α j))
      comm Y q j₁ j₂ f₁ f₂ hf₁ hf₂ := by
        have := φ.comm (q ≫ p) (f₁ ≫ p' j₁) (f₂ ≫ p' j₂)
          (by rw [Category.assoc, w, reassoc_of% hf₁])
          (by rw [Category.assoc, w, reassoc_of% hf₂])
        dsimp at this ⊢
        rw [pullFunctorObjHom_eq_assoc _ _ _ _ _ (q ≫ p) (f₁ ≫ p' j₁) (f₂ ≫ p' j₂),
          pullFunctorObjHom_eq _ _ _ _ _ (q ≫ p) (f₁ ≫ p' j₁) (f₂ ≫ p' j₂)]
        dsimp
        rw [mapComp'_inv_naturality_assoc, ← mapComp'_hom_naturality,
          reassoc_of% this] }

/-- Given families of morphisms `f : X i ⟶ S` and `f' : X' j ⟶ S'`, suitable
commutative diagrams `w j : p' j ≫ f (α j) = f' j ≫ p`, this is the natural
isomorphism between the descent data relative to `f'` that are obtained either:
* by considering the obvious descent data relative to `f` given by an object `M : F.obj (op S)`,
  followed by the application of `pullFunctor F w : F.DescentData f ⥤ F.DescentData f'`;
* by considering the obvious descent data relative to `f'` given by pulling
  back the object `M` to `S'`. -/
def toDescentDataCompPullFunctorIso :
    F.toDescentData f ⋙ pullFunctor F w ≅ (F.map p.op.toLoc).toFunctor ⋙ F.toDescentData f' :=
  NatIso.ofComponents
    (fun M ↦ isoMk (fun i ↦ (Cat.Hom.toNatIso
        (F.isoMapOfCommSq (CommSq.mk (w i)).op.toLoc)).symm.app M)
      (fun Y q i₁ i₂ f₁ f₂ hf₁ hf₂ ↦ by
        dsimp
        rw [F.isoMapOfCommSq_eq _ _ rfl, F.isoMapOfCommSq_eq _ _ rfl]
        dsimp
        simp only [Functor.map_comp, Category.assoc]
        rw [← F.mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom_app_assoc p.op.toLoc
            (f' i₁).op.toLoc f₁.op.toLoc _ q.op.toLoc (p.op.toLoc ≫ q.op.toLoc) rfl
            (by grind) (by grind) M,
          pullFunctorObjHom_eq _ _ _ _ _ (q ≫ p) (f₁ ≫ p' i₁) (f₂ ≫ p' i₂),
          ← cancel_mono ((F.mapComp' (f' i₂).op.toLoc f₂.op.toLoc q.op.toLoc
            (by grind)).inv.toNatTrans.app _)]
        dsimp
        simp only [Category.assoc,
          ← F.mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom_app p.op.toLoc
            (f' i₂).op.toLoc f₂.op.toLoc _ q.op.toLoc (p.op.toLoc ≫ q.op.toLoc) rfl
            (by grind) (by grind) M,
          ← F.mapComp'_inv_whiskerRight_mapComp'₀₂₃_inv_app_assoc (f (α i₁)).op.toLoc
            (p' i₁).op.toLoc f₁.op.toLoc (p.op.toLoc ≫ (f' i₁).op.toLoc) _
            (p.op.toLoc ≫ q.op.toLoc) (by grind) rfl (by grind) M,
          F.mapComp'_inv_whiskerRight_mapComp'₀₂₃_inv_app_assoc (f (α i₂)).op.toLoc
            (p' i₂).op.toLoc f₂.op.toLoc (p.op.toLoc ≫ (f' i₂).op.toLoc) _
            (p.op.toLoc ≫ q.op.toLoc) (by grind) rfl (by grind) M]
        simp))
    (fun f ↦ by
      ext i
      exact (F.isoMapOfCommSq (CommSq.mk (w i)).op.toLoc).inv.toNatTrans.naturality f)

/-- Up to a (unique) isomorphism, the functor
`pullFunctor : F.DescentData f ⥤ F.DescentData f'` does not depend
on the auxiliary data. -/
@[simps!]
def pullFunctorIso {β : ι' → ι} {p'' : ∀ j, X' j ⟶ X (β j)}
    (w' : ∀ j, p'' j ≫ f (β j) = f' j ≫ p) :
    pullFunctor F w ≅ pullFunctor F w' :=
  NatIso.ofComponents (fun D ↦ isoMk (fun j ↦ D.iso _ _ _) (by
    intro Y q j₁ j₂ f₁ f₂ hf₁ hf₂
    dsimp
    rw [pullFunctorObjHom_eq _ _ _ _ _ (q ≫ p) _ _ rfl (by cat_disch) (by cat_disch),
      pullFunctorObjHom_eq _ _ _ _ _ (q ≫ p) _ _ rfl (by cat_disch) (by cat_disch),
      map_eq_pullHom_assoc _ _ (f₁ ≫ p' j₁) (f₁ ≫ p'' j₁) (by cat_disch) (by cat_disch),
      map_eq_pullHom _ _ (f₂ ≫ p' j₂) (f₂ ≫ p'' j₂) (by cat_disch) (by cat_disch)]
    simp only [Cat.Hom.hom_inv_id_toNatTrans_app_assoc, Category.assoc]
    rw [pullHom_hom _ _ _ (q ≫ p) (by rw [w, reassoc_of% hf₁]) _ _
        rfl (by cat_disch) _ _ rfl rfl, hom_comp_assoc,
      pullHom_hom _ _ _ (q ≫ p) (by rw [w, reassoc_of% hf₂]) _ _
        rfl (by cat_disch) _ _ rfl rfl, hom_comp_assoc]))
    (fun φ ↦ by
      ext j
      exact φ.comm _ _ _ rfl (by cat_disch))

variable (S) in
/-- The functor `F.DescentData f ⥤ F.DescentData f` corresponding to `pullFunctor`
applied to identity morphisms is isomorphic to the identity functor. -/
@[simps!]
def pullFunctorIdIso :
    pullFunctor F (p := 𝟙 S) (p' := fun _ ↦ 𝟙 _) (w := by simp) ≅ 𝟭 (F.DescentData f) :=
  NatIso.ofComponents (fun D ↦ isoMk (fun i ↦ (Cat.Hom.toNatIso (F.mapId _)).app _) (by
    intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
    dsimp
    rw [pullFunctorObjHom_eq_assoc _ _ _ _ _ q f₁ f₂ rfl]
    simp [mapComp'_id_comp_inv_app_assoc, mapComp'_id_comp_hom_app, ← Functor.map_comp]))

/-- The composition of two functors `pullFunctor` is isomorphic to `pullFunctor` applied
to the compositions. -/
@[simps!]
def pullFunctorCompIso
    {S'' : C} {q : S'' ⟶ S'} {ι'' : Type t''} {X'' : ι'' → C} {f'' : ∀ k, X'' k ⟶ S''}
    {β : ι'' → ι'} {q' : ∀ k, X'' k ⟶ X' (β k)} (w' : ∀ k, q' k ≫ f' (β k) = f'' k ≫ q)
    (r : S'' ⟶ S) {r' : ∀ k, X'' k ⟶ X (α (β k))}
    (hr : q ≫ p = r := by cat_disch) (hr' : ∀ k, q' k ≫ p' (β k) = r' k := by cat_disch) :
    pullFunctor F w ⋙ pullFunctor F w' ≅
      pullFunctor F (p := r) (α := α ∘ β) (p' := r') (fun k ↦ by
        dsimp
        rw [← hr', Category.assoc, w, reassoc_of% w', hr]) :=
  NatIso.ofComponents
    (fun D ↦ isoMk (fun _ ↦ (Cat.Hom.toNatIso (F.mapComp' _ _ _ (by grind))).symm.app _) (by
      intro Y s k₁ k₂ f₁ f₂ hf₁ hf₂
      dsimp
      rw [pullFunctorObjHom_eq _ _ _ _ _ (s ≫ r) _ _ rfl,
        pullFunctorObjHom_eq _ _ _ _ _ (s ≫ q) (f₁ ≫ q' k₁) (f₂ ≫ q' k₂)]
      dsimp
      rw [pullFunctorObjHom_eq _ _ _ _ _ (s ≫ r) (f₁ ≫ r' k₁) (f₂ ≫ r' k₂)
        rfl (by simp [w', reassoc_of% hf₁, reassoc_of% hf₂]) (by
          simp [reassoc_of% w', reassoc_of% hf₁, hr])]
      dsimp
      simp only [Category.assoc]
      rw [mapComp'_inv_whiskerRight_mapComp'₀₂₃_inv_app_assoc _ _ _ _ _ _ _
        (by grind) rfl rfl, mapComp'₀₂₃_hom_app _ _ _ _ _ _ _ _ rfl rfl]))

end

variable {f} in
/-- Up to an equivalence, the category `DescentData` for a pseudofunctor `F` and
a family of morphisms `f : X i ⟶ S` is unchanged when we replace `S` by an isomorphic object,
or when we replace `f` by another family which generate the same sieve. -/
@[simps]
def pullFunctorEquivalence {S' : C} {ι' : Type t'} {X' : ι' → C} {f' : ∀ j, X' j ⟶ S'}
    (e : S' ≅ S) {α : ι' → ι} {p' : ∀ j, X' j ⟶ X (α j)}
    (w : ∀ j, p' j ≫ f (α j) = f' j ≫ e.hom)
    {β : ι → ι'} {q' : ∀ i, X i ⟶ X' (β i)} (w' : ∀ i, q' i ≫ f' (β i) = f i ≫ e.inv) :
    F.DescentData f ≌ F.DescentData f' where
  functor := pullFunctor F w
  inverse := pullFunctor F w'
  unitIso :=
    (pullFunctorIdIso F S).symm ≪≫ pullFunctorIso _ _ _ ≪≫
      (pullFunctorCompIso _ _ _ _ e.inv_hom_id (fun _ ↦ rfl)).symm
  counitIso :=
    pullFunctorCompIso _ _ _ _ e.hom_inv_id (fun _ ↦ rfl) ≪≫
      pullFunctorIso _ _ _ ≪≫ pullFunctorIdIso F S'
  functor_unitIso_comp D := by
    ext j
    dsimp
    simp only [Category.id_comp, Functor.map_comp, Category.assoc]
    rw [pullFunctorObjHom_eq_assoc _ _ _ _ _ (p' _ ≫ f _) (p' _ ≫ q' _ ≫ p' _) (p' _) (by simp)
        (by simp [w', reassoc_of% w]),
      map_eq_pullHom_assoc _ (p' j) (p' j) (p' _ ≫ q' _ ≫ p' _) (by simp) (by simp),
      D.pullHom_hom _ _ (p' j ≫ f _) (by simp) _ _ (by simp)
        (by simp [w, reassoc_of% w']) _ _ (by simp) rfl]
    dsimp
    rw [← F.mapComp'₀₁₃_hom_comp_whiskerLeft_mapComp'_hom_app_assoc _ _ _ _ _ _ rfl rfl (by simp),
      mapComp'_comp_id_hom_app, mapComp'_id_comp_inv_app_assoc, ← Functor.map_comp_assoc,
      Cat.Hom.inv_hom_id_toNatTrans_app]
    simp [D.hom_self _ _ rfl]

lemma exists_equivalence_of_sieve_eq
    {ι' : Type t'} {X' : ι' → C} (f' : ∀ i', X' i' ⟶ S)
    (h : Sieve.ofArrows _ f = Sieve.ofArrows _ f') :
    ∃ (e : F.DescentData f ≌ F.DescentData f'),
      Nonempty (F.toDescentData f ⋙ e.functor ≅ F.toDescentData f') := by
  have h₁ (i' : ι') : ∃ (i : ι) (g' : X' i' ⟶ X i), g' ≫ f i = f' i' := by
    obtain ⟨_, _, _, ⟨i⟩, fac⟩ : Sieve.ofArrows X f (f' i') := by
      rw [h]; apply Sieve.ofArrows_mk
    exact ⟨i, _, fac⟩
  have h₂ (i : ι) : ∃ (i' : ι') (g : X i ⟶ X' i'), g ≫ f' i' = f i := by
    obtain ⟨_, _, _, ⟨i'⟩, fac⟩ : Sieve.ofArrows X' f' (f i) := by
      rw [← h]; apply Sieve.ofArrows_mk
    exact ⟨i', _, fac⟩
  choose α p' w using h₁
  choose β q' w' using h₂
  exact ⟨pullFunctorEquivalence (p' := p') (q' := q') F (Iso.refl _)
    (by cat_disch) (by cat_disch), ⟨toDescentDataCompPullFunctorIso _ _ ≪≫
    Functor.isoWhiskerRight (Cat.Hom.toNatIso (F.mapId _)) _ ≪≫ Functor.leftUnitor _⟩⟩

lemma nonempty_fullyFaithful_toDescentData_iff_of_sieve_eq
    {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)
    {ι' : Type t'} {X' : ι' → C} (f' : ∀ i', X' i' ⟶ S)
    (h : Sieve.ofArrows _ f = Sieve.ofArrows _ f') :
    Nonempty (F.toDescentData f).FullyFaithful ↔
      Nonempty (F.toDescentData f').FullyFaithful := by
  obtain ⟨e, ⟨iso⟩⟩ := DescentData.exists_equivalence_of_sieve_eq F f f' h
  exact ⟨fun ⟨h⟩ ↦ ⟨(h.comp e.fullyFaithfulFunctor).ofIso iso⟩,
    fun ⟨h⟩ ↦ ⟨(h.comp e.fullyFaithfulInverse).ofIso iso.symm.compInverseIso⟩⟩

lemma isEquivalence_toDescentData_iff_of_sieve_eq
    {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)
    {ι' : Type t'} {X' : ι' → C} (f' : ∀ i', X' i' ⟶ S)
    (h : Sieve.ofArrows _ f = Sieve.ofArrows _ f') :
    (F.toDescentData f).IsEquivalence ↔ (F.toDescentData f').IsEquivalence := by
  obtain ⟨e, ⟨iso⟩⟩ := DescentData.exists_equivalence_of_sieve_eq F f f' h
  rw [← Functor.isEquivalence_iff_of_iso iso]
  exact ⟨fun _ ↦ inferInstance,
    fun _ ↦ Functor.isEquivalence_of_comp_right _ e.functor⟩

/-- Morphisms between objects in the image of the functor `F.toDescentData f`
identify to compatible families of sections of the presheaf `F.presheafHom M N` on
the object `Over.mk (𝟙 S)`, relatively to the family of morphisms in `Over S`
corresponding to the family `f`. -/
def subtypeCompatibleHomEquiv {M N : F.obj (.mk (op S))} :
    Subtype (Presieve.Arrows.Compatible (F.presheafHom M N)
      (X := fun i ↦ Over.mk (f i)) (B := Over.mk (𝟙 S)) (fun i ↦ Over.homMk (f i))) ≃
    ((F.toDescentData f).obj M ⟶ (F.toDescentData f).obj N) where
  toFun φ :=
    { hom := φ.val
      comm Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := by
        have := φ.property i₁ i₂ (Over.mk q) (Over.homMk f₁) (Over.homMk f₂) (by cat_disch)
        simp_all [map_eq_pullHom] }
  invFun g :=
    { val := g.hom
      property i₁ i₂ Z f₁ f₂ h := by
        simpa [map_eq_pullHom (g.hom i₁) f₁.left Z.hom Z.hom (Over.w f₁) (Over.w f₁),
          map_eq_pullHom (g.hom i₂) f₂.left Z.hom Z.hom (Over.w f₂) (Over.w f₂),
          cancel_epi, cancel_mono] using g.comm Z.hom f₁.left f₂.left (Over.w f₁) (Over.w f₂) }

lemma subtypeCompatibleHomEquiv_toCompatible_presheafHomObjHomEquiv
    {M N : F.obj (.mk (op S))} (φ : M ⟶ N) :
    subtypeCompatibleHomEquiv F f (Presieve.Arrows.toCompatible _ _
      (F.presheafHomObjHomEquiv φ)) = (F.toDescentData f).map φ := by
  ext i
  simp [subtypeCompatibleHomEquiv, presheafHomObjHomEquiv, pullHom,
    ← Functor.map_comp, Pseudofunctor.mapComp'_id_comp_hom_app_assoc,
    Pseudofunctor.mapComp'_id_comp_inv_app]

end DescentData

/-- The condition that a pseudofunctor satisfies the descent of morphisms
relative to a presieve. -/
@[mk_iff]
structure IsPrestackFor (R : Presieve S) : Prop where
  nonempty_fullyFaithful :
    Nonempty (F.toDescentData (fun (f : R.category) ↦ f.obj.hom)).FullyFaithful

variable {F} in
/-- If `R` is a presieve such that `F.IsPrestackFor R`, then the functor
`F.toDescentData (fun (f : R.category) ↦ f.obj.hom)` is fully faithful. -/
noncomputable def IsPrestackFor.fullyFaithful {R : Presieve S} (hF : F.IsPrestackFor R) :
    (F.toDescentData (fun (f : R.category) ↦ f.obj.hom)).FullyFaithful :=
  hF.nonempty_fullyFaithful.some

lemma isPrestackFor_iff_of_sieve_eq
    {R R' : Presieve S} (h : Sieve.generate R = Sieve.generate R') :
    F.IsPrestackFor R ↔ F.IsPrestackFor R' := by
  simp only [isPrestackFor_iff]
  obtain ⟨_, _, f, rfl⟩ := Presieve.exists_eq_ofArrows R
  obtain ⟨_, _, f', rfl⟩ := Presieve.exists_eq_ofArrows R'
  apply DescentData.nonempty_fullyFaithful_toDescentData_iff_of_sieve_eq
  simpa only [Sieve.ofArrows_category']

@[simp]
lemma IsPrestackFor_generate_iff (R : Presieve S) :
    F.IsPrestackFor (Sieve.generate R).arrows ↔ F.IsPrestackFor R :=
  F.isPrestackFor_iff_of_sieve_eq (by simp)

lemma isPrestackFor_ofArrows_iff :
    F.IsPrestackFor (Presieve.ofArrows _ f) ↔
      Nonempty (F.toDescentData f).FullyFaithful := by
  simp only [isPrestackFor_iff]
  apply DescentData.nonempty_fullyFaithful_toDescentData_iff_of_sieve_eq
  rw [Sieve.ofArrows_category']

/-- The condition that a pseudofunctor has effective descent
relative to a presieve. -/
@[mk_iff]
structure IsStackFor (R : Presieve S) : Prop where
  isEquivalence :
    (F.toDescentData (fun (f : R.category) ↦ f.obj.hom)).IsEquivalence

variable {F} in
lemma IsStackFor.isPrestackFor {R : Presieve S} (h : F.IsStackFor R) :
    F.IsPrestackFor R where
  nonempty_fullyFaithful := ⟨by
    rw [isStackFor_iff] at h
    exact .ofFullyFaithful _⟩

variable {F} in
lemma IsStackFor.essSurj {R : Presieve S} (h : F.IsStackFor R) :
    (F.toDescentData (fun (f : R.category) ↦ f.obj.hom)).EssSurj := by
  have := h.isEquivalence
  infer_instance

lemma isStackFor_iff_of_sieve_eq
    {R R' : Presieve S} (h : Sieve.generate R = Sieve.generate R') :
    F.IsStackFor R ↔ F.IsStackFor R' := by
  simp only [isStackFor_iff]
  obtain ⟨_, _, f, rfl⟩ := Presieve.exists_eq_ofArrows R
  obtain ⟨_, _, f', rfl⟩ := Presieve.exists_eq_ofArrows R'
  apply DescentData.isEquivalence_toDescentData_iff_of_sieve_eq
  simpa only [Sieve.ofArrows_category']

@[simp]
lemma IsStackFor_generate_iff (R : Presieve S) :
    F.IsStackFor (Sieve.generate R).arrows ↔ F.IsStackFor R :=
  F.isStackFor_iff_of_sieve_eq (by simp)

lemma isStackFor_ofArrows_iff :
    F.IsStackFor (Presieve.ofArrows _ f) ↔
      (F.toDescentData f).IsEquivalence := by
  simp only [isStackFor_iff]
  apply DescentData.isEquivalence_toDescentData_iff_of_sieve_eq
  rw [Sieve.ofArrows_category']

variable {F} in
lemma bijective_toDescentData_map_iff (M N : F.obj (.mk (op S))) :
    Function.Bijective ((F.toDescentData f).map : (M ⟶ N) → _) ↔
  Presieve.IsSheafFor (F.presheafHom M N) (X := Over.mk (𝟙 S))
    (Presieve.ofArrows (Y := fun i ↦ Over.mk (f i)) (fun i ↦ Over.homMk (f i))) := by
  rw [Presieve.isSheafFor_ofArrows_iff_bijective_toCompabible,
    ← (DescentData.subtypeCompatibleHomEquiv F f).bijective.of_comp_iff',
    ← Function.Bijective.of_comp_iff _ (presheafHomObjHomEquiv F).bijective]
  convert Iff.rfl
  ext φ : 1
  apply DescentData.subtypeCompatibleHomEquiv_toCompatible_presheafHomObjHomEquiv

lemma isPrestackFor_iff_isSheafFor {S : C} (R : Sieve S) :
    F.IsPrestackFor R.arrows ↔ ∀ (M N : F.obj (.mk (op S))),
      Presieve.IsSheafFor (P := F.presheafHom M N)
        ((Sieve.overEquiv (Over.mk (𝟙 S))).symm R).arrows := by
  rw [isPrestackFor_iff, Functor.FullyFaithful.nonempty_iff_map_bijective]
  refine forall_congr' (fun M ↦ forall_congr' (fun N ↦ ?_))
  rw [bijective_toDescentData_map_iff]
  convert Iff.rfl
  refine le_antisymm ?_ ?_
  · rintro X f (hf : R.arrows f.left)
    obtain ⟨X, g, rfl⟩ := Over.mk_surjective X
    obtain rfl : f = Over.homMk g := by ext; simpa using Over.w f
    exact Presieve.ofArrows.mk (ι := R.arrows.category) ⟨Over.mk g, hf⟩
  · rintro _ _ ⟨_, h⟩
    exact h

lemma isPrestackFor_iff_isSheafFor' {S : C} (R : Sieve S) :
    F.IsPrestackFor R.arrows ↔ ∀ ⦃S₀ : C⦄ (M N : F.obj (.mk (op S₀))) (a : S ⟶ S₀),
      Presieve.IsSheafFor (F.presheafHom M N) ((Sieve.overEquiv (Over.mk a)).symm R).arrows := by
  rw [isPrestackFor_iff_isSheafFor]
  refine ⟨fun h S₀ M N a ↦ ?_, by tauto⟩
  replace h := h ((F.map a.op.toLoc).toFunctor.obj M) ((F.map a.op.toLoc).toFunctor.obj N)
  rw [← Presieve.isSheafFor_iff_of_iso (F.overMapCompPresheafHomIso M N a),
    Presieve.isSheafFor_over_map_op_comp_iff (X' := Over.mk a)
      (e := Over.isoMk (Iso.refl _))] at h
  convert h
  refine le_antisymm ?_ ?_
  · intro Y f hf
    exact ⟨Over.mk f.left, Over.homMk f.left, Over.homMk (𝟙 _) (by simpa using Over.w f),
      hf, by cat_disch⟩
  · rintro X b ⟨Y, c, d, h, fac⟩
    replace fac := (Over.forget _).congr_map fac
    dsimp at fac
    rw [Category.comp_id] at fac
    change R.arrows b.left
    simpa [fac] using R.downward_closed h d.left

variable {F} in
lemma IsPrestackFor.isSheafFor'
    {S₀ : C} (S : Over S₀) {R : Sieve S} (hF : F.IsPrestackFor (Sieve.overEquiv _ R).arrows)
    (M N : F.obj (.mk (op S₀))) :
    Presieve.IsSheafFor (F.presheafHom M N) R.arrows := by
  rw [isPrestackFor_iff_isSheafFor'] at hF
  obtain ⟨S, a, rfl⟩ := S.mk_surjective
  simpa using hF M N a

variable {J : GrothendieckTopology C}

/-- If `F` is a prestack for a Grothendieck topology `J`, and `f` is a covering
family of morphisms, then the functor `F.toDescentData f` is fully faithful. -/
noncomputable def fullyFaithfulToDescentData [F.IsPrestack J] (hf : Sieve.ofArrows _ f ∈ J S) :
    (F.toDescentData f).FullyFaithful :=
  Nonempty.some (by
    rw [← isPrestackFor_ofArrows_iff, ← IsPrestackFor_generate_iff,
      isPrestackFor_iff_isSheafFor]
    intro M N
    refine ((isSheaf_iff_isSheaf_of_type _ _).1
      (IsPrestack.isSheaf J M N)).isSheafFor _ _ ?_
    rwa [GrothendieckTopology.mem_over_iff, Sieve.generate_sieve, Equiv.apply_symm_apply])

lemma isPrestackFor [F.IsPrestack J] {S : C} (R : Presieve S) (hR : Sieve.generate R ∈ J S) :
    F.IsPrestackFor R := by
  rw [isPrestackFor_iff]
  exact ⟨F.fullyFaithfulToDescentData _ (by rwa [Sieve.ofArrows_category'])⟩

lemma isPrestackFor' [F.IsPrestack J] {S : C} (R : Sieve S) (hR : R ∈ J S) :
    F.IsPrestackFor R.arrows :=
  F.isPrestackFor _ (by simpa)

variable {F} in
lemma IsPrestack.of_isPrestackFor
    (hF : ∀ (S : C) (R : Sieve S) (_ : R ∈ J S), F.IsPrestackFor R.arrows) :
    F.IsPrestack J where
  isSheaf M N := by
    rw [isSheaf_iff_isSheaf_of_type]
    intro U S hS
    obtain ⟨U, u, rfl⟩ := Over.mk_surjective U
    apply (hF _ _ hS).isSheafFor'

end Pseudofunctor

end CategoryTheory
