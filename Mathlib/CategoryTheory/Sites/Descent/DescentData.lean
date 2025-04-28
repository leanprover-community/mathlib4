/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Christian Merten
-/
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Sites.Descent.Morphisms
import Mathlib.CategoryTheory.Sites.Descent.CodescentData

/-!
# Descent data

-/

universe t w v' v u' u

namespace CategoryTheory

open Opposite

namespace Presieve

variable {C : Type u} [Category.{v} C] (P : Cᵒᵖ ⥤ Type w) {X : C} (R : Presieve X)

@[simps]
def toCompatible (s : P.obj (op X)) :
    Subtype (FamilyOfElements.Compatible (P := P) (R := R)) where
  val Y f hf := P.map f.op s
  property Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ fac := by
    simp only [← FunctorToTypes.map_comp_apply, ← op_comp, fac]

lemma isSheafFor_iff_bijective_toCompatible (P : Cᵒᵖ ⥤ Type w) (R : Presieve X) :
    IsSheafFor P R ↔ Function.Bijective (toCompatible P R) := by
  constructor
  · intro h
    constructor
    · intro s₁ s₂ hs
      simp only [Subtype.ext_iff] at hs
      apply h.isSeparatedFor.ext
      intro Y f hf
      exact congr_fun (congr_fun (congr_fun hs Y) f) hf
    · rintro ⟨x, hx⟩
      exact ⟨h.amalgamate x hx, by ext; funext; apply h.valid_glue⟩
  · intro h x hx
    apply existsUnique_of_exists_of_unique
    · obtain ⟨s, hs⟩ := h.surjective ⟨x, hx⟩
      simp only [Subtype.ext_iff] at hs
      exact ⟨s, fun Y f hf ↦ congr_fun (congr_fun (congr_fun hs Y) f) hf⟩
    · intro s₁ s₂ hs₁ hs₂
      apply h.injective
      ext
      funext Y f hf
      simp only [toCompatible_coe, hs₁ f hf, hs₂ f hf]

end Presieve

open Limits Bicategory

namespace Pseudofunctor

variable {C : Type u} [Category.{v} C] (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
  {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)

-- to be moved
instance {X Y : C} (f : X ⟶ Y) [IsIso f] (F : Pseudofunctor (LocallyDiscrete C) Cat.{v', u'}) :
    (F.map (.toLoc f)).IsEquivalence := by
  let e : F.obj (.mk X) ≌ F.obj (.mk Y) :=
    Equivalence.mk (F.map (.toLoc f)) (F.map (.toLoc (inv f)))
    ((F.mapId _).symm ≪≫ F.mapComp' f.toLoc (inv f).toLoc (𝟙 _) (by
        rw [← Quiver.Hom.comp_toLoc, IsIso.hom_inv_id, Quiver.Hom.id_toLoc]))
    ((F.mapComp' (inv f).toLoc f.toLoc (𝟙 _) (by
        rw [← Quiver.Hom.comp_toLoc, IsIso.inv_hom_id, Quiver.Hom.id_toLoc])).symm ≪≫ F.mapId _)
  exact e.isEquivalence_functor

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

end Pseudofunctor

end CategoryTheory
