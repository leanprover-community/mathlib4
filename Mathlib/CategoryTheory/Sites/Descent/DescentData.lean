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

@[simps!]
def mk' (obj : ∀ i, F.obj (.mk (op (X i))))
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
        hom q f₁ f₂ hf₁ hf₂ ≫ hom q f₂ f₃ hf₂ hf₃ = hom q f₁ f₃ hf₁ hf₃) :
    F.DescentData f :=
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

section mk''

variable (obj : ∀ i, (F.obj (.mk (op (X i)))))
  (sq : ∀ i j, ChosenPullback (f i) (f j))
  (hom : ∀ (i j : ι), (F.map (sq i j).p₁.op.toLoc).obj (obj i) ⟶
    (F.map (sq i j).p₂.op.toLoc).obj (obj j))
  (diag : ∀ i, (sq i i).Diagonal)
  (hom_self : ∀ i, (F.map (diag i).f.op.toLoc).map (hom i i) =
    (F.mapComp' (sq i i).p₁.op.toLoc (diag i).f.op.toLoc (𝟙 _)
        (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.app _ ≫
      (F.mapComp' (sq i i).p₂.op.toLoc (diag i).f.op.toLoc (𝟙 _)
        (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.app _)

noncomputable def mk''Hom ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    (F.map f₁.op.toLoc).obj (obj i₁) ⟶ (F.map f₂.op.toLoc).obj (obj i₂) :=
  let p : Y ⟶ (sq i₁ i₂).pullback := (sq i₁ i₂).isPullback.lift f₁ f₂ (by aesop)
  (F.mapComp' (sq i₁ i₂).p₁.op.toLoc p.op.toLoc f₁.op.toLoc
        (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, IsPullback.lift_fst])).hom.app _ ≫
      (F.map (.toLoc p.op)).map (hom i₁ i₂) ≫
      (F.mapComp' (sq i₁ i₂).p₂.op.toLoc p.op.toLoc f₂.op.toLoc
        (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, IsPullback.lift_snd])).inv.app _

lemma mk''Hom_eq ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) (p : Y ⟶ (sq i₁ i₂).pullback)
    (hp₁ : p ≫ (sq i₁ i₂).p₁ = f₁) (hp₂ : p ≫ (sq i₁ i₂).p₂ = f₂) :
  mk''Hom obj sq hom q f₁ f₂ hf₁ hf₂ =
    (F.mapComp' (sq i₁ i₂).p₁.op.toLoc p.op.toLoc f₁.op.toLoc (by aesop)).hom.app _ ≫
      (F.map (.toLoc p.op)).map (hom i₁ i₂) ≫
      (F.mapComp' (sq i₁ i₂).p₂.op.toLoc p.op.toLoc f₂.op.toLoc (by aesop)).inv.app _ := by
  obtain rfl : p = (sq i₁ i₂).isPullback.lift f₁ f₂ (by rw [hf₁, hf₂]) := by
    apply (sq i₁ i₂).isPullback.hom_ext <;> aesop
  rfl

lemma mk''Hom_comp' ⦃Y Y' : C⦄ (g : Y' ⟶ Y) (q : Y ⟶ S) (q' : Y' ⟶ S) (hq : g ≫ q = q')
    ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q)
    (gf₁ : Y' ⟶ X i₁) (gf₂ : Y' ⟶ X i₂) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    mk''Hom obj sq hom q' gf₁ gf₂ (by aesop) (by aesop) =
      (F.mapComp' f₁.op.toLoc g.op.toLoc gf₁.op.toLoc (by aesop)).hom.app (obj i₁) ≫
        (F.map g.op.toLoc).map (mk''Hom obj sq hom q f₁ f₂ hf₁ hf₂) ≫
          (F.mapComp' f₂.op.toLoc g.op.toLoc gf₂.op.toLoc (by aesop)).inv.app (obj i₂) := by
  let p := (sq i₁ i₂).isPullback.lift f₁ f₂ (by aesop)
  dsimp
  rw [mk''Hom_eq _ _ _ _ _ _ _ _ p (by aesop) (by aesop),
    mk''Hom_eq _ _ _ _ _ _ _ _ (g ≫ p) (by aesop) (by aesop)]
  dsimp
  simp only [Functor.map_comp, Category.assoc]
  rw [← F.mapComp'_hom_app_comp_mapComp'_hom_app_map_obj_assoc
    _ _ _ _ _ _ (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, IsPullback.lift_fst]) rfl
    (by rw [← Quiver.Hom.comp_toLoc, ← Quiver.Hom.comp_toLoc, ← op_comp, ← op_comp,
        Category.assoc, IsPullback.lift_fst, hgf₁])]
  rw [F.map_map_mapComp'_inv_app_comp_mapComp'_inv_app
    _ _ _ _ _ _ (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, IsPullback.lift_snd]) rfl
    (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hgf₂]),
    mapComp'_inv_naturality_assoc, Iso.hom_inv_id_app_assoc]

@[simp]
lemma mk''Hom_p₁_p₂ (i : ι) :
    mk''Hom obj sq hom (sq i i).p (sq i i).p₁ (sq i i).p₂ (by simp) (by simp) = hom i i := by
  rw [mk''Hom_eq obj sq hom (sq i i).p (sq i i).p₁ (sq i i).p₂ (by simp) (by simp)
    (𝟙 _) (by simp)  (by simp)]
  simp [mapComp'_comp_id_hom_app, mapComp'_comp_id_inv_app]

include hom_self in
lemma mk''Hom_self ⦃Y : C⦄ (q : Y ⟶ S) ⦃i : ι⦄ (g : Y ⟶ X i) (hg : g ≫ f i = q) :
    mk''Hom obj sq hom q g g hg hg = 𝟙 _ := by
  rw [mk''Hom_comp' obj sq hom (g ≫ (diag i).f) (sq i i).p _ (by aesop) (sq i i).p₁ (sq i i).p₂
    (by simp) (by simp) _ _ (by simp) (by simp), mk''Hom_p₁_p₂,
    ← F.mapComp'_naturality_2_assoc (diag i).f.op.toLoc g.op.toLoc _ (by simp), hom_self,
    Functor.map_comp_assoc]
  dsimp
  rw [F.mapComp'_inv_app_map_obj_comp_mapComp'_inv_app _ _ _ (𝟙 _) _ _
    (by simp only [← Quiver.Hom.comp_toLoc, ← op_comp, ChosenPullback.LiftStruct.f_p₂,
      Quiver.Hom.id_toLoc, op_id]) rfl
    (by simp only [← Quiver.Hom.comp_toLoc, ← op_comp, Category.assoc,
      ChosenPullback.LiftStruct.f_p₂, Category.comp_id])]
  simp only [← Functor.map_comp_assoc, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  rw [F.mapComp'_hom_app_comp_mapComp'_hom_app_map_obj_assoc _ _ _ (𝟙 _) _ _
    (by simp only [← Quiver.Hom.comp_toLoc, ← op_comp, ChosenPullback.LiftStruct.f_p₁,
      Quiver.Hom.id_toLoc, op_id]) rfl
    (by simp only [← Quiver.Hom.comp_toLoc, ← op_comp, Category.assoc,
      ChosenPullback.LiftStruct.f_p₁, Category.comp_id]),
    ← Functor.map_comp_assoc]
  simp

variable (sq₃ : ∀ (i₁ i₂ i₃ : ι), ChosenPullback₃ (sq i₁ i₂) (sq i₂ i₃) (sq i₁ i₃))
  (hom_comp : ∀ (i₁ i₂ i₃ : ι),
    mk''Hom obj sq hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₂ (by simp) (by simp) ≫
    mk''Hom obj sq hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₂ (sq₃ i₁ i₂ i₃).p₃ (by simp) (by simp) =
    mk''Hom obj sq hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₃ (by simp) (by simp))

-- TODO @jriou: moving to DescentDataPrime.lean
noncomputable def mk'' : F.DescentData f :=
  DescentData.mk' obj (fun _ _ _ _ _ _ ↦ mk''Hom _ _ _ _ _ _)
    (fun _ _ _ _ _ hq _ _ _ _ _ _ _ _ ↦ mk''Hom_comp' _ _ _ _ _ _ hq _ _ _ _ _ _)
    (fun _ _ _ _ hg ↦ mk''Hom_self obj sq hom diag hom_self _ _ hg)
    (fun Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ ↦ by
      obtain ⟨φ, _, _, _⟩ := (sq₃ i₁ i₂ i₃).exists_lift f₁ f₂ f₃ q hf₁ hf₂ hf₃
      dsimp
      rw [mk''Hom_comp' obj sq hom φ (sq₃ i₁ i₂ i₃).p _ _
            (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₂ _ _ _ _ _ _,
        mk''Hom_comp' obj sq hom φ (sq₃ i₁ i₂ i₃).p _ _ (sq₃ i₁ i₂ i₃).p₂
          (sq₃ i₁ i₂ i₃).p₃ _ _ _ _ _ _,
        mk''Hom_comp' obj sq hom φ (sq₃ i₁ i₂ i₃).p _ (by aesop) (sq₃ i₁ i₂ i₃).p₁
          (sq₃ i₁ i₂ i₃).p₃ _ _ _ _ _ _]
      · simp only [Category.assoc, Iso.inv_hom_id_app_assoc,
        ← Functor.map_comp_assoc, hom_comp]
      all_goals aesop)

end mk''

end DescentData

end Pseudofunctor

end CategoryTheory
