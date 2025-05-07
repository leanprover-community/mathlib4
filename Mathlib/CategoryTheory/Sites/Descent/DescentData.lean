/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Christian Merten
-/
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Sites.Descent.Morphisms
import Mathlib.CategoryTheory.Sites.Descent.CodescentData
import Mathlib.CategoryTheory.Sites.Descent.PullbackStruct

/-!
# Descent data

-/

universe t v' v u' u

namespace CategoryTheory

open Opposite Limits

namespace Pseudofunctor

section

@[simp]
lemma mapComp'_mapLocallyDiscrete_comp
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    (G : Pseudofunctor (LocallyDiscrete D) Cat)
    {X Y Z : LocallyDiscrete C} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : f ≫ g = fg) :
      ((mapLocallyDiscrete F).comp G).mapComp' f g fg hfg =
      G.mapComp' ((mapLocallyDiscrete F).map f) ((mapLocallyDiscrete F).map g)
        ((mapLocallyDiscrete F).map fg) (by aesop) := by
  ext
  subst hfg
  rw [mapComp'_eq_mapComp]
  rfl

end

variable {C : Type u} [Category.{v} C] (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
  {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)

/-- If `F` is a pseudofunctor from `(LocallyDiscrete Cᵒᵖ)` to `Cat` and `f i : X i ⟶ S`
is a family of morphisms in `C`, this is the type of family of objects in `F.obj (X i)`
equipped with a descent datum relative to the morphisms `f i`. -/
abbrev DescentData :=
  ((mapLocallyDiscrete (Over.forget S).op).comp F).CodescentData
    (fun (i : ι) ↦ .mk (op (Over.mk (f i))))

/-- The functor `F.obj (.mk (op S)) ⥤ F.DescentData f`. -/
def toDescentData : F.obj (.mk (op S)) ⥤ F.DescentData f :=
  ((mapLocallyDiscrete (Over.forget S).op).comp F).toCodescentDataOfIsInitial
    (fun (i : ι) ↦ .mk (op (Over.mk (f i)))) (.mk (op (Over.mk (𝟙 _))))
      (IsInitial.ofUniqueHom
        (fun Z ↦ .toLoc (Quiver.Hom.op (Over.homMk Z.as.unop.hom)))
        (fun ⟨⟨Z⟩⟩ ⟨⟨m⟩⟩ ↦ by
          congr
          ext
          simpa using Over.w m))

namespace DescentData

variable {F f}

nonrec def iso (D : F.DescentData f) ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁)
    (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q := by aesop) (hf₂ : f₂ ≫ f i₂ = q := by aesop) :
    (F.map f₁.op.toLoc).obj (D.obj i₁) ≅ (F.map f₂.op.toLoc).obj (D.obj i₂) := by
  exact D.iso (Y := .mk (op (Over.mk q)))
    ((Over.homMk f₁).op.toLoc) ((Over.homMk f₂).op.toLoc)

nonrec lemma iso_comp' (D : F.DescentData f)
    ⦃Y' Y : C⦄ (g : Y' ⟶ Y) (q : Y ⟶ S) (q' : Y' ⟶ S) (hq : g ≫ q = q')
    ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q)
    (gf₁ : Y' ⟶ X i₁) (gf₂ : Y' ⟶ X i₂) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    D.iso q' gf₁ gf₂ (by aesop) (by aesop) =
    (F.mapComp' f₁.op.toLoc g.op.toLoc gf₁.op.toLoc (by
      simp only [← Quiver.Hom.comp_toLoc, ← op_comp, hgf₁])).app _ ≪≫
        (F.map g.op.toLoc).mapIso (D.iso q f₁ f₂) ≪≫
      (F.mapComp' f₂.op.toLoc g.op.toLoc gf₂.op.toLoc (by
        simp only [← Quiver.Hom.comp_toLoc, ← op_comp, hgf₂])).symm.app _ := by
  ext : 1
  simpa using congr_arg Iso.hom (D.iso_comp' (Y' := .mk (op (Over.mk q')))
    (Y := .mk (op (Over.mk q))) (Over.homMk g).op.toLoc (Over.homMk f₁).op.toLoc
    (Over.homMk f₂).op.toLoc (Over.homMk gf₁).op.toLoc (Over.homMk gf₂).op.toLoc (by
      simp only [← Quiver.Hom.comp_toLoc, ← op_comp]
      congr 2
      aesop) (by
      simp only [← Quiver.Hom.comp_toLoc, ← op_comp]
      congr 2
      aesop))

nonrec lemma iso_trans (D : F.DescentData f) ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ i₃ : ι⦄ (f₁ : Y ⟶ X i₁)
    (f₂ : Y ⟶ X i₂) (f₃ : Y ⟶ X i₃) (hf₁ : f₁ ≫ f i₁ = q)
    (hf₂ : f₂ ≫ f i₂ = q) (hf₃ : f₃ ≫ f i₃ = q) :
    D.iso q f₁ f₂ hf₁ hf₂ ≪≫ D.iso q f₂ f₃ hf₂ hf₃ = D.iso q f₁ f₃ hf₁ hf₃ := by
  apply D.iso_trans

@[reassoc (attr := simp)]
nonrec lemma iso_hom_iso_hom
    (D : F.DescentData f) ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ i₃ : ι⦄ (f₁ : Y ⟶ X i₁)
    (f₂ : Y ⟶ X i₂) (f₃ : Y ⟶ X i₃) (hf₁ : f₁ ≫ f i₁ = q)
    (hf₂ : f₂ ≫ f i₂ = q) (hf₃ : f₃ ≫ f i₃ = q) :
    (D.iso q f₁ f₂ hf₁ hf₂).hom ≫ (D.iso q f₂ f₃ hf₂ hf₃).hom =
      (D.iso q f₁ f₃ hf₁ hf₃).hom := by
  apply D.iso_hom_iso_hom

@[ext]
lemma hom_ext {D₁ D₂ : F.DescentData f} {φ φ' : D₁ ⟶ D₂}
    (h : ∀ i, φ.hom i = φ'.hom i): φ = φ' :=
  CodescentData.hom_ext h

section

variable (obj : ∀ i, F.obj (.mk (op (X i))))
    (hom : ∀ ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
      (_hf₁ : f₁ ≫ f i₁ = q) (_hf₂ : f₂ ≫ f i₂ = q),
        (F.map f₁.op.toLoc).obj (obj i₁) ⟶ (F.map f₂.op.toLoc).obj (obj i₂))
    (hom_comp' : ∀ ⦃Y Y' : C⦄ (g : Y' ⟶ Y) (q : Y ⟶ S) (q' : Y' ⟶ S) (hq : g ≫ q = q')
      ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q)
      (gf₁ : Y' ⟶ X i₁) (gf₂ : Y' ⟶ X i₂) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂),
      hom q' gf₁ gf₂ (by aesop_cat) (by aesop_cat) =
        (F.mapComp' f₁.op.toLoc g.op.toLoc gf₁.op.toLoc
          (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hgf₁])).hom.app _ ≫
          (F.map (.toLoc g.op)).map (hom q f₁ f₂ hf₁ hf₂) ≫
          (F.mapComp' f₂.op.toLoc g.op.toLoc gf₂.op.toLoc
          (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hgf₂])).inv.app _)
    (hom_self : ∀ ⦃Y : C⦄ (q : Y ⟶ S) ⦃i : ι⦄ (g : Y ⟶ X i) (hg : g ≫ f i = q),
      hom q g g hg hg = 𝟙 _)
    (comp_hom : ∀ ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ i₃ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
      (f₃ : Y ⟶ X i₃) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) (hf₃ : f₃ ≫ f i₃ = q),
        hom q f₁ f₂ hf₁ hf₂ ≫ hom q f₂ f₃ hf₂ hf₃ = hom q f₁ f₃ hf₁ hf₃)

@[simps! obj]
def mk' : F.DescentData f :=
  CodescentData.mk' obj
    (fun Y i₁ i₂ f₁ f₂ ↦ hom Y.as.unop.hom f₁.as.unop.left f₂.as.unop.left
      (Over.w f₁.as.unop) (Over.w f₂.as.unop))
    (fun Y' Y g i₁ i₂ f₁ f₂ f₁g f₂g hf₁g hf₂g ↦ by
      simpa using hom_comp' g.as.unop.left Y.as.unop.hom Y'.as.unop.hom
        (Over.w g.as.unop) f₁.as.unop.left f₂.as.unop.left
        (Over.w f₁.as.unop) (Over.w f₂.as.unop) f₁g.as.unop.left f₂g.as.unop.left
        (by simp [← hf₁g]) (by simp [← hf₂g]))
    (fun _ _ _ ↦ hom_self _ _ _)
    (fun Y i₁ i₂ i₃ f₁ f₂ f₃ ↦ comp_hom _ _ _ _ _ _ _)

@[simp]
lemma mk'_iso_hom ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁)
    (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    ((mk' obj hom hom_comp' hom_self comp_hom).iso q f₁ f₂ hf₁ hf₂).hom =
      hom q f₁ f₂ hf₁ hf₂ := rfl

end


@[simps]
def homMk {D₁ D₂ : F.DescentData f} (φ : ∀ i, D₁.obj i ⟶ D₂.obj i)
    (hφ : ∀ ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁)
    (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q),
      (F.map f₁.op.toLoc).map (φ i₁) ≫ (D₂.iso q f₁ f₂ hf₁ hf₂).hom =
        (D₁.iso q f₁ f₂ hf₁ hf₂).hom ≫ (F.map f₂.op.toLoc).map (φ i₂) := by aesop_cat) :
    D₁ ⟶ D₂ where
  hom i := φ i
  comm Y _ _ f₁ f₂ :=
    hφ Y.as.unop.hom f₁.as.unop.left f₂.as.unop.left
      (Over.w f₁.as.unop) (Over.w f₂.as.unop)

@[reassoc]
lemma comm {D₁ D₂ : F.DescentData f} (φ : D₁ ⟶ D₂)
    ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁)
    (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    (F.map f₁.op.toLoc).map (φ.hom i₁) ≫ (D₂.iso q f₁ f₂ hf₁ hf₂).hom =
        (D₁.iso q f₁ f₂ hf₁ hf₂).hom ≫ (F.map f₂.op.toLoc).map (φ.hom i₂) := by
  exact φ.comm (Y := .mk (op (Over.mk q)))
    (Over.homMk f₁).op.toLoc (Over.homMk f₂).op.toLoc

end DescentData

end Pseudofunctor

end CategoryTheory
