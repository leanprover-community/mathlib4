/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Christian Merten
-/
import Mathlib.CategoryTheory.Sites.Descent.IsPrestack

/-!
# Descent data

In this file, given a pseudofunctor `F` from `LocallyDiscrete Cᵒᵖ` to `Cat`,
and a family of maps `f i : X i ⟶ S` in the category `C`,
we define the category `F.DescentData f` of objects over the `X i`
equipped with a descent data relative to the morphisms `f i : X i ⟶ S`.

## TODO (@joelriou, @chrisflav)
* Relate the prestack condition to the fully faithfullness of `Pseudofunctor.toDescentData`.
* Define stacks.
* Introduce multiple variants of `DescentData` (when `C` has pullbacks,
when `F` also has a covariant functoriality, etc.).

-/

universe t t' v' v u' u

namespace CategoryTheory

open Opposite

namespace Pseudofunctor

-- TODO: can we make grind to this?
/-- Tactic which does `simp [← Quiver.Hom.comp_toLoc, ← op_comp]` before applying `aesop`. -/
macro "aesoptoloc" : tactic =>
  `(tactic|(simp [← Quiver.Hom.comp_toLoc, ← op_comp] <;> aesop))

open LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C] (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
  {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)

/-- Given a pseudofunctor `F` from `LocallyDiscrete Cᵒᵖ` to `Cat`, and a family of
morphisms `f i : X i ⟶ S`, the objects of the category of descent data for
the `X i` relative to the morphisms `f i` consists in families of
objects `obj i` in `F.obj (.mk (op (X i)))` together with morphisms `hom`
between the pullbacks of `obj i₁` and `obj i₂` over any object `Y` which maps
to both `X i₁` and `X i₂` (in a way that is compatible with the morphisms to `S`).
The compatibles these morphisms satisfy imply that the morphisms `hom` are isomorphisms. -/
structure DescentData where
  /-- The objects over `X i` for all `i` -/
  obj (i : ι) : F.obj (.mk (op (X i)))
  /-- The compatibility (iso)morphisms after pullbacks. -/
  hom ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (_hf₁ : f₁ ≫ f i₁ = q := by cat_disch) (_hf₂ : f₂ ≫ f i₂ = q := by cat_disch) :
      (F.map f₁.op.toLoc).obj (obj i₁) ⟶ (F.map f₂.op.toLoc).obj (obj i₂)
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
    (F.map f₁.op.toLoc).obj (D.obj i₁) ≅ (F.map f₂.op.toLoc).obj (D.obj i₂) where
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
    (F.map f₁.op.toLoc).map (hom i₁) ≫ D₂.hom q f₁ f₂ =
        D₁.hom q f₁ f₂ ≫ (F.map f₂.op.toLoc).map (hom i₂) := by cat_disch

attribute [reassoc (attr := local simp)] Hom.comm

instance : Category (F.DescentData f) where
  Hom := Hom
  id D := { hom _ := 𝟙 _}
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
  obj i := (F.map (f i).op.toLoc).obj M
  hom Y q i₁ i₂ f₁ f₂ hf₁ hf₂ :=
    (F.mapComp' (f i₁).op.toLoc f₁.op.toLoc q.op.toLoc (by aesoptoloc)).inv.app _ ≫
      (F.mapComp' (f i₂).op.toLoc f₂.op.toLoc q.op.toLoc (by aesoptoloc)).hom.app _
  pullHom_hom Y' Y g q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
    simp only [pullHom, Functor.map_comp, Category.assoc,
      F.mapComp'₀₁₃_inv_app (f i₁).op.toLoc f₁.op.toLoc g.op.toLoc q.op.toLoc
        gf₁.op.toLoc q'.op.toLoc (by aesoptoloc) (by aesoptoloc) (by aesoptoloc),
      F.mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom_app (f i₂).op.toLoc f₂.op.toLoc g.op.toLoc
      q.op.toLoc gf₂.op.toLoc q'.op.toLoc (by aesoptoloc) (by aesoptoloc) (by aesoptoloc)]

/-- Constructor for isomorphisms in `Pseudofunctor.DescentData`. -/
@[simps]
def isoMk {D₁ D₂ : F.DescentData f} (e : ∀ (i : ι), D₁.obj i ≅ D₂.obj i)
    (comm : ∀ ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁)
    (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q),
    (F.map f₁.op.toLoc).map (e i₁).hom ≫ D₂.hom q f₁ f₂ =
        D₁.hom q f₁ f₂ ≫ (F.map f₂.op.toLoc).map (e i₂).hom := by cat_disch) : D₁ ≅ D₂ where
  hom :=
    { hom i := (e i).hom
      comm := comm }
  inv :=
    { hom i := (e i).inv
      comm Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := by
        rw [← cancel_mono ((F.map f₂.op.toLoc).map (e i₂).hom), Category.assoc,
          Category.assoc, Iso.map_inv_hom_id, Category.comp_id,
          ← cancel_epi ((F.map f₁.op.toLoc).map (e i₁).hom),
          Iso.map_hom_inv_id_assoc, comm q f₁ f₂ hf₁ hf₂] }

end DescentData

/-- The functor `F.obj (.mk (op S)) ⥤ F.DescentData f`. -/
def toDescentData : F.obj (.mk (op S)) ⥤ F.DescentData f where
  obj M := .ofObj M
  map {M M'} φ := { hom i := (F.map (f i).op.toLoc).map φ }

namespace DescentData

variable {F f} {S' : C} {p : S' ⟶ S} {ι' : Type t'} {X' : ι' → C} {f' : ∀ j, X' j ⟶ S'}

variable {α : ι' → ι} {p' : ∀ j, X' j ⟶ X (α j)} (w : ∀ j, p' j ≫ f (α j) = f' j ≫ p)

/-- Auxiliary definition for `pullFunctor`. -/
def pullFunctorObjHom (D : F.DescentData f)
    ⦃Y : C⦄ (q : Y ⟶ S') ⦃j₁ j₂ : ι'⦄ (f₁ : Y ⟶ X' j₁) (f₂ : Y ⟶ X' j₂)
    (hf₁ : f₁ ≫ f' j₁ = q := by cat_disch) (hf₂ : f₂ ≫ f' j₂ = q := by cat_disch) :
    (F.map f₁.op.toLoc).obj ((F.map (p' j₁).op.toLoc).obj (D.obj (α j₁))) ⟶
      (F.map f₂.op.toLoc).obj ((F.map (p' j₂).op.toLoc).obj (D.obj (α j₂))) :=
  (F.mapComp (p' j₁).op.toLoc f₁.op.toLoc).inv.app _ ≫
    D.hom (q ≫ p) (f₁ ≫ p' _) (f₂ ≫ p' _) (by simp [w, reassoc_of% hf₁])
      (by simp [w, reassoc_of% hf₂]) ≫
    (F.mapComp (p' j₂).op.toLoc f₂.op.toLoc).hom.app _

@[reassoc]
lemma pullFunctorObjHom_eq (D : F.DescentData f)
    ⦃Y : C⦄ (q : Y ⟶ S') ⦃j₁ j₂ : ι'⦄ (f₁ : Y ⟶ X' j₁) (f₂ : Y ⟶ X' j₂)
    (q' : Y ⟶ S) (f₁' : Y ⟶ X (α j₁)) (f₂' : Y ⟶ X (α j₂))
    (hf₁ : f₁ ≫ f' j₁ = q := by cat_disch) (hf₂ : f₂ ≫ f' j₂ = q := by cat_disch)
    (hq' : q ≫ p = q' := by cat_disch)
    (hf₁' : f₁ ≫ p' j₁ = f₁' := by cat_disch)
    (hf₂' : f₂ ≫ p' j₂ = f₂' := by cat_disch) :
  pullFunctorObjHom w D q f₁ f₂ =
    (F.mapComp' _ _ _).inv.app _ ≫ D.hom q' f₁' f₂'
      (by rw [← hq', ← hf₁', Category.assoc, w, reassoc_of% hf₁])
      (by rw [← hq', ← hf₂', Category.assoc, w, reassoc_of% hf₂]) ≫
      (F.mapComp' _ _ _).hom.app _ := by
  subst hq' hf₁' hf₂'
  simp [mapComp'_eq_mapComp, pullFunctorObjHom]

/-- Auxiliary definition for `pullFunctor`. -/
@[simps]
def pullFunctorObj (D : F.DescentData f) :
    F.DescentData f' where
  obj j := (F.map (p' _).op.toLoc).obj (D.obj (α j))
  hom Y q j₁ j₂ f₁ f₂ hf₁ hf₂ := pullFunctorObjHom w _ _ _ _
  pullHom_hom Y' Y g q q' hq j₁ j₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
    rw [pullFunctorObjHom_eq _ _ _ _ _ (q' ≫ p) (gf₁ ≫ p' j₁) (gf₂ ≫ p' j₂),
      pullFunctorObjHom_eq _ _ _ _ _ (q ≫ p) (f₁ ≫ p' j₁) (f₂ ≫ p' j₂)]
    dsimp
    rw [← D.pullHom_hom g (q ≫ p) (q' ≫ p) (by rw [reassoc_of% hq])
      (f₁ ≫ p' j₁) (f₂ ≫ p' j₂) (by rw [Category.assoc, w, reassoc_of% hf₁])
      (by rw [Category.assoc, w, reassoc_of% hf₂]) (gf₁ ≫ p' j₁) (gf₂ ≫ p' j₂)
      (by aesop) (by aesop)]
    dsimp [pullHom]
    simp only [Functor.map_comp, Category.assoc]
    rw [F.mapComp'₀₁₃_inv_comp_mapComp'₀₂₃_hom_app_assoc _ _ _ _ _ _ _ _ (by aesop),
      mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom_app _ _ _ _ _ _ _ _ _ (by aesop)]
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

/-- Given family of morphisms `f : X i ⟶ S` and `f' : X' j ⟶ S'`, and suitable
commutative diagrams `p' j ≫ f (α j) = f' j ≫ p`, this is the
induced functor `F.DescentData f ⥤ F.DescentData f'`. (Up to a (unique) isomorphism,
this functor only depends on `f` and `f'`, see `pullFunctorIso`.) -/
@[simps]
def pullFunctor : F.DescentData f ⥤ F.DescentData f' where
  obj D := pullFunctorObj w D
  map {D₁ D₂} φ :=
    { hom j := (F.map (p' j).op.toLoc).map (φ.hom (α j))
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

/-- Up to a (unique) isomorphism, the functor
`pullFunctor : F.DescentData f ⥤ F.DescentData f'` does not depend
on the auxiliary data. -/
def pullFunctorIso {β : ι' → ι} {p'' : ∀ j, X' j ⟶ X (β j)}
    (w' : ∀ j, p'' j ≫ f (β j) = f' j ≫ p) :
    pullFunctor F w ≅ pullFunctor F w' :=
  NatIso.ofComponents (fun D ↦ isoMk (fun j ↦ D.iso _ _ _) (by
    intro Y q j₁ j₂ f₁ f₂ hf₁ hf₂
    dsimp
    rw [pullFunctorObjHom_eq _ _ _ _ _ (q ≫ p) _ _ rfl (by aesop) (by aesop),
      pullFunctorObjHom_eq _ _ _ _ _ (q ≫ p) _ _ rfl (by aesop) (by aesop),
      map_eq_pullHom_assoc _ _ (f₁ ≫ p' j₁) (f₁ ≫ p'' j₁) (by aesop) (by aesop),
      map_eq_pullHom _ _ (f₂ ≫ p' j₂) (f₂ ≫ p'' j₂) (by aesop) (by aesop)]
    dsimp
    simp only [Iso.hom_inv_id_app_assoc, Category.assoc, NatIso.cancel_natIso_inv_left,
      NatIso.cancel_natIso_hom_right_assoc, op_comp, Quiver.Hom.comp_toLoc]
    rw [pullHom_hom _ _ _ (q ≫ p) (by rw [w, reassoc_of% hf₁]) _ _
        rfl (by aesop) _ _ rfl rfl, hom_comp,
      pullHom_hom _ _ _ (q ≫ p) (by rw [w, reassoc_of% hf₂]) _ _
        rfl (by aesop) _ _ rfl rfl, hom_comp]))
    (fun {D₁ D₂} φ ↦ by
      ext j
      exact φ.comm _ _ _ rfl (by aesop))

end DescentData

end Pseudofunctor

end CategoryTheory
