/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Christian Merten
-/
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Bicategory.Functor.Cat
import Mathlib.CategoryTheory.Sites.Descent.PullbackStruct
import Mathlib.CategoryTheory.Sites.Descent.IsPrestack

/-!
# Descent data

-/

universe t v' v u' u

namespace CategoryTheory

open Opposite Limits

namespace Pseudofunctor

macro "aesoptoloc" : tactic =>
  `(tactic|(simp [← Quiver.Hom.comp_toLoc, ← op_comp] <;> aesop))

open LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C] (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
  {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)

structure DescentData where
  obj (i : ι) : F.obj (.mk (op (X i)))
  hom ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (_hf₁ : f₁ ≫ f i₁ = q := by aesop_cat) (_hf₂ : f₂ ≫ f i₂ = q := by aesop_cat) :
      (F.map f₁.op.toLoc).obj (obj i₁) ⟶ (F.map f₂.op.toLoc).obj (obj i₂)
  pullHom_hom ⦃Y' Y : C⦄ (g : Y' ⟶ Y) (q : Y ⟶ S) (q' : Y' ⟶ S) (hq : g ≫ q = q')
    ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q)
    (gf₁ : Y' ⟶ X i₁) (gf₂ : Y' ⟶ X i₂) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
      pullHom (hom q f₁ f₂) g gf₁ gf₂ = hom q' gf₁ gf₂ := by aesop_cat
  hom_self ⦃Y : C⦄ (q : Y ⟶ S) ⦃i : ι⦄ (g : Y ⟶ X i) (_ : g ≫ f i = q) :
      hom q g g = 𝟙 _ := by aesop_cat
  hom_comp ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ i₃ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (f₃ : Y ⟶ X i₃)
      (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) (hf₃ : f₃ ≫ f i₃ = q) :
      hom q f₁ f₂ hf₁ hf₂ ≫ hom q f₂ f₃ hf₂ hf₃ = hom q f₁ f₃ hf₁ hf₃ := by aesop_cat

namespace DescentData

variable {F f} (D : F.DescentData f)

attribute [local simp] hom_self pullHom_hom
attribute [reassoc (attr := simp)] hom_comp

@[simps]
def iso ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (_hf₁ : f₁ ≫ f i₁ = q := by aesop_cat) (_hf₂ : f₂ ≫ f i₂ = q := by aesop_cat) :
    (F.map f₁.op.toLoc).obj (D.obj i₁) ≅ (F.map f₂.op.toLoc).obj (D.obj i₂) where
  hom := D.hom q f₁ f₂
  inv := D.hom q f₂ f₁

instance {Y : C} (q : Y ⟶ S) {i₁ i₂ : ι} (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    IsIso (D.hom q f₁ f₂ hf₁ hf₂) :=
  (D.iso q f₁ f₂).isIso_hom

@[ext]
structure Hom (D₁ D₂ : F.DescentData f) where
  hom (i : ι) : D₁.obj i ⟶ D₂.obj i
  comm ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁)
    (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    (F.map f₁.op.toLoc).map (hom i₁) ≫ D₂.hom q f₁ f₂ =
        D₁.hom q f₁ f₂ ≫ (F.map f₂.op.toLoc).map (hom i₂) := by aesop_cat

attribute [reassoc (attr := local simp)] Hom.comm

@[simps]
def Hom.id (D : F.DescentData f) : Hom D D where
  hom i := 𝟙 _

@[simps]
def Hom.comp {D₁ D₂ D₃ : F.DescentData f} (φ : Hom D₁ D₂) (φ' : Hom D₂ D₃) : Hom D₁ D₃ where
  hom i := φ.hom i ≫ φ'.hom i

instance : Category (F.DescentData f) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

@[ext]
lemma hom_ext {D₁ D₂ : F.DescentData f} {φ φ' : D₁ ⟶ D₂}
    (h : ∀ i, φ.hom i = φ'.hom i) : φ = φ' :=
  Hom.ext (funext h)

@[simp]
lemma id_hom (D : F.DescentData f) (i : ι) : Hom.hom (𝟙 D) i = 𝟙 _ := rfl

@[simp, reassoc]
lemma comp_hom {D₁ D₂ D₃ : F.DescentData f} (φ : D₁ ⟶ D₂) (φ' : D₂ ⟶ D₃) (i : ι) :
    (φ ≫ φ').hom i = φ.hom i ≫ φ'.hom i := rfl

@[simps]
def ofObj (M : F.obj (.mk (op S))) : F.DescentData f where
  obj i := (F.map (f i).op.toLoc).obj M
  hom Y q i₁ i₂ f₁ f₂ hf₁ hf₂ :=
    (F.mapComp' (f i₁).op.toLoc f₁.op.toLoc q.op.toLoc (by aesoptoloc)).inv.app _ ≫
      (F.mapComp' (f i₂).op.toLoc f₂.op.toLoc q.op.toLoc (by aesoptoloc)).hom.app _
  pullHom_hom Y' Y g q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
    dsimp
    simp only [pullHom, Functor.map_comp, Category.assoc,
      F.mapComp'₀₁₃_inv_app (f i₁).op.toLoc f₁.op.toLoc g.op.toLoc q.op.toLoc
        gf₁.op.toLoc q'.op.toLoc (by aesoptoloc) (by aesoptoloc) (by aesoptoloc),
      F.mapComp'_hom_app_comp_mapComp'_inv_app
        (f i₂).op.toLoc f₂.op.toLoc g.op.toLoc q.op.toLoc gf₂.op.toLoc q'.op.toLoc
        (by aesoptoloc) (by aesoptoloc) (by aesoptoloc) M]

@[simps]
def isoMk {D₁ D₂ : F.DescentData f} (e : ∀ (i : ι), D₁.obj i ≅ D₂.obj i)
    (comm : ∀ ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁)
    (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q),
    (F.map f₁.op.toLoc).map (e i₁).hom ≫ D₂.hom q f₁ f₂ =
        D₁.hom q f₁ f₂ ≫ (F.map f₂.op.toLoc).map (e i₂).hom := by aesop_cat) : D₁ ≅ D₂ where
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

end Pseudofunctor

end CategoryTheory
