import Mathlib.Algebra.Category.ModuleCat.Presheaf

universe v₂ v₁ v u₂ u₁ u

namespace PresheafOfModules

open CategoryTheory Limits

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
  {J : Type u₂} [Category.{v₂} J] (F : J ⥤ PresheafOfModules.{v} R)

def evaluationJointlyReflectsLimits (c : Cone F)
    (hc : ∀ (X : Cᵒᵖ), IsLimit ((evaluation.{v} R X).mapCone c)) : IsLimit c where
  lift s := Hom.mk' (fun X => (hc X).lift ((evaluation.{v} R X).mapCone s)) (by
    intros X Y f x
    suffices (restriction R f).app s.pt ≫ (ModuleCat.restrictScalars (R.map f)).map ((hc Y).lift ((evaluation.{v} R Y).mapCone s)) =
      (hc X).lift ((evaluation.{v} R X).mapCone s) ≫ (restriction R f).app c.pt from congr_hom this x
    have H : IsLimit ((evaluation.{v} R Y ⋙ ModuleCat.restrictScalars (R.map f)).mapCone c) := by
      -- needs that `restrictScalars` preserves limits
      -- easy because it is a right adjoint (but universe restrictions?)
      sorry
    apply H.hom_ext
    intro j
    simp only [evaluation_obj, Functor.comp_obj, Functor.mapCone_pt, Functor.mapCone_π_app, Functor.comp_map,
      evaluation_map, Category.assoc]
    simp only [← Functor.map_comp]
    erw [IsLimit.fac]
    simp only [Functor.mapCone_pt, evaluation_obj, Functor.mapCone_π_app, evaluation_map]
    erw [← NatTrans.naturality, ← NatTrans.naturality]
    erw [IsLimit.fac_assoc]
    rfl)
  fac s j := by
    ext1 X
    exact (hc X).fac ((evaluation.{v} R X).mapCone s) j
  uniq s m hm := by
    ext1 X
    exact (hc X).uniq ((evaluation.{v} R X).mapCone s) ((evaluation.{v} R X).map m) (fun j => by
      dsimp
      rw [← hm]
      rfl)

def evaluationJointlyReflectsColimits (c : Cocone F)
    (hc : ∀ (X : Cᵒᵖ), IsColimit ((evaluation.{v} R X).mapCocone c)) : IsColimit c := by
  sorry

end PresheafOfModules
