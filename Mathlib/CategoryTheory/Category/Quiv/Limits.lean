/-
Copyright (c) 2025 Robert Maxton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Maxton
-/

import Mathlib.CategoryTheory.Category.Quiv.AsFunctor.Defs
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
import Mathlib.CategoryTheory.Limits.Types.Shapes

/-!
  # Limits in `Quiv.{v, u}`

  In `AsFunctor.Defs`, we showed that `Quiv.{v, u}` is equivalent to the full subcategory of
  `WalkingQuiver ⥤ Type max v u` which are `u`-small and locally `v`-small.

  We now show that that subcategory is closed under `min u v`-small limits, and therefore that
  `Quiv.{v, u}` has all limits of small diagrams.
-/

namespace CategoryTheory.Quiv
open CategoryTheory Limits PresheafWalkingQuiver ObjectProperty
universe v u w' w

variable [UnivLE.{w, v}] [UnivLE.{w, u}] {J : Type w}
         (F : Discrete J ⥤ Quiv.{v, u})

/-- `SmallAsQuiv.{v, u, w}` is closed under `min u v`-small limits. -/
lemma smallAsQuivClosedUnderLimits (J : Type w) [Category.{w} J] :
    ClosedUnderLimitsOfShape J SmallAsQuiv.{v, u, max w v u} :=
  closedUnderLimitsOfShape_of_limit fun {F} [_] hF ↦
    prop_of_iso _ (limitIsoFlipCompLim F).symm {
      small_vertex := by
        have {j} := hF j |>.small_vertex
        simp_rw [Vertex, Functor.comp_obj, lim_obj, small_congr (Types.limitEquivSections _),
        Functor.flip_obj_obj]
        infer_instance
      small_edge s t := by
        let ι : _ ⟶ ∏ᶜ F.obj := (limitIsoFlipCompLim F).inv ≫ limitSubobjectProduct F
        have hι j : (ι ≫ Pi.π F.obj j).app 0 = limit.π (F.flip.obj 0) j := by
          ext k
          simp at k
          unfold ι
          simp_rw [Category.assoc, limitSubobjectProduct_eq_lift, Pi.lift_π,
          NatTrans.comp_app, limitIsoFlipCompLim_inv_app,
          limitObjIsoLimitCompEvaluation_inv_π_app, comp_evaluation]
        let ι₁ := ι.app 1 ≫ (piObjIso F.obj 1).hom ≫ (Types.productIso _).hom
        unfold Edge
        have h j := hF j |>.small_edge
          (limit.π (F.flip.obj 0) j s) (limit.π (F.flip.obj 0) j t)
        replace h := @small_Pi _ _ _ h
        rw [small_congr Equiv.subtypePiEquivPi.symm,
        small_congr (Equiv.subtypeEquivRight (fun _ ↦ forall_and))] at h
        replace h := @small_subtype _ h (fun e ↦ e.1 ∈ Set.range ι₁)
        refine small_congr ?_ |>.mp h
        calc
        _ ≃ _ := Equiv.subtypeSubtypeEquivSubtypeInter _ _
        _ ≃ _ := Equiv.subtypeEquivRight (fun _ ↦ and_comm)
        _ ≃ _ := Equiv.subtypeSubtypeEquivSubtypeInter _ _ |>.symm
        _ ≃ _ := Equiv.subtypeEquiv
          (Equiv.ofInjective ι₁ (mono_iff_injective _ |>.mp inferInstance)).symm
          (by
            rintro ⟨e', ⟨e, rfl⟩⟩
            congrm ?lhs ∧ ?rhs
            all_goals
                simp_rw [Equiv.ofInjective_symm_apply, ι₁, ← Category.assoc]
                conv_lhs =>
                  ext j
                  rw [types_comp_apply, Types.productIso_hom_comp_eval_apply,
                  ← types_comp_apply _ (Pi.π (F.obj · |>.obj 1) j), Category.assoc,
                  piObjIso_hom_comp_π, ← NatTrans.comp_app]
                  (try rw [naturality_src]); (try rw [naturality_tgt])
                  unfold ι
                  rw [Category.assoc, limitSubobjectProduct_eq_lift, Pi.lift_π,
                  NatTrans.comp_app, limitIsoFlipCompLim_inv_app,
                  limitObjIsoLimitCompEvaluation_inv_π_app]
                simp [comp_evaluation, ← Types.limit_ext_iff]) }

omit [UnivLE.{w, v}] [UnivLE.{w, u}] in
/-- The full subcategory of `u`-small and locally `v`-small functors
`WalkingQuiver ⥤ Type max w v u` has all limits of size `w`. -/
instance : HasLimitsOfSize.{w, w} SmallAsQuivSubcategory.{v, u, max w v u} where
  has_limits_of_shape J _ :=
     hasLimitsOfShape_of_closedUnderLimits <| smallAsQuivClosedUnderLimits.{v, u} J

/-- The category `Quiv.{v, u}` has all limits of size `min v u`. -/
instance : HasLimitsOfSize.{w, w} Quiv.{v, u} :=
    Adjunction.has_limits_of_equivalence quivEquiv.functor.{w}

/-- The category of quivers has all limits of size `min v u`.

This version avoids requring `UnivLE` directly. -/
instance : HasLimitsOfSize.{w', w'} Quiv.{max w' v, max w' u} :=
    Adjunction.has_limits_of_equivalence quivEquiv.functor.{max w' v u, max w' v, max w' u}

end CategoryTheory.Quiv

#min_imports
