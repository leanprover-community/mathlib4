module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
public import Mathlib.CategoryTheory.Sites.Sheafification

@[expose] public section

namespace CategoryTheory

open Category Functor Limits EffectiveEpiFamily

variable {C D : Type*} [Category C] [Category D]

instance [HasPullbacks D] [HasPushouts D] [IsRegularEpiCategory D] :
    IsRegularEpiCategory (C ⥤ D) where
  regularEpiOfEpi {F G} f hf := ⟨{
    W := combinePullbackCones f f _ (fun k ↦ pullback.isLimit (f.app k) (f.app k)) |>.pt
    left := combinePullbackCones f f _ (fun k ↦ pullback.isLimit (f.app k) (f.app k)) |>.fst
    right := combinePullbackCones f f _ (fun k ↦ pullback.isLimit (f.app k) (f.app k)) |>.snd
    w := combinePullbackCones f f _ (fun k ↦ pullback.isLimit (f.app k) (f.app k)) |>.condition
    isColimit := by
      apply evaluationJointlyReflectsColimits
      intro k
      have : RegularEpi (f.app k) := regularEpiOfEpi (f.app k)
      refine .equivOfNatIsoOfIso ?_ _ _ ?_ (isColimitCoforkOfEffectiveEpi (f.app k)
        (pullback.cone (f.app k) (f.app k))
        (pullback.isLimit (f.app k) (f.app k)))
      · refine NatIso.ofComponents ?_ ?_
        · rintro (_ | _)
          exacts [Iso.refl _, Iso.refl _]
        · rintro (_ | _ | _) (_ | _ | _) (_ | _)
          all_goals cat_disch
      · refine Cocones.ext (Iso.refl _) ?_
        rintro (_ | _ | _)
        · simp only [comp_obj, parallelPair_obj_zero, evaluation_obj_obj, mapCocone_pt,
            Cofork.ofπ_pt, limit.cone_x, PullbackCone.fst_limit_cone, PullbackCone.snd_limit_cone,
            parallelPair_obj_one, Cocones.precompose_obj_pt, const_obj_obj,
            Cocones.precompose_obj_ι, NatTrans.comp_app, NatIso.ofComponents_inv_app, Iso.refl_inv,
            Cofork.ofπ_ι_app, Iso.refl_hom, comp_id, mapCocone_ι_app, evaluation_obj_map]
          erw [id_comp] -- when `D` is `Type*`, `cat_disch` just works and this `erw` is not needed
          cat_disch
        · cat_disch }⟩

universe u

instance (J : GrothendieckTopology C) [HasPullbacks D] [HasPushouts D] [IsRegularEpiCategory D]
    [HasWeakSheafify J D] : IsRegularEpiCategory (Sheaf J D) where
  regularEpiOfEpi := sorry

end CategoryTheory
