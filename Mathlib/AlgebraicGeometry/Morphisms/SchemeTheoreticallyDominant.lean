/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Scheme-theoretically dominant morphisms

In this file, we define scheme-theoretically dominant morphisms as morphisms with trivial kernel.
## Main results
- `AlgebraicGeometry.IsSchemeTheoreticallyDominant`:
  The class of scheme-theoretically dominant morphisms.
- `AlgebraicGeometry.isSchemeTheoreticallyDominant_iff_isDominant`:
  If the target is reduced and the map is quasi-compact, then scheme-theoretically dominant
  is equivalent to dominant.
- `AlgebraicGeometry.IsSchemeTheoreticallyDominant.of_isPullback`:
  quasicompact + scheme-theoretically dominant is stable under flat base change.

-/

public section

open CategoryTheory MorphismProperty Limits

namespace AlgebraicGeometry

variable {X Y Z S : Scheme} (f : X ⟶ S) (g : Y ⟶ S)

/-- A morphism is scheme-theoretically dominant if its kernel is trivial. -/
@[mk_iff]
class IsSchemeTheoreticallyDominant (f : X ⟶ Y) : Prop where
  ker_eq_bot (f) : f.ker = ⊥

alias Scheme.Hom.ker_eq_bot := IsSchemeTheoreticallyDominant.ker_eq_bot

instance (priority := low) [IsIso f] : IsSchemeTheoreticallyDominant f :=
  ⟨by simp⟩

instance (priority := low) [IsSchemeTheoreticallyDominant f] [QuasiCompact f] :
    IsDominant f := by
  rw [isDominant_iff, DenseRange, dense_iff_closure_eq, ← Scheme.Hom.support_ker,
    f.ker_eq_bot, Scheme.IdealSheafData.support_bot, TopologicalSpace.Closeds.coe_top]

instance (f : X ⟶ Y) (g : Y ⟶ Z) [IsSchemeTheoreticallyDominant f]
    [IsSchemeTheoreticallyDominant g] :
    IsSchemeTheoreticallyDominant (f ≫ g) := by
  rw [isSchemeTheoreticallyDominant_iff, Scheme.Hom.ker_comp, f.ker_eq_bot,
    Scheme.IdealSheafData.map_bot, g.ker_eq_bot]

instance : IsMultiplicative @IsSchemeTheoreticallyDominant where
  id_mem _ := inferInstance
  comp_mem _ _ _ _ := inferInstance

lemma IsSchemeTheoreticallyDominant.of_isDominant (f : X ⟶ Y) [IsDominant f] [IsReduced Y] :
    IsSchemeTheoreticallyDominant f := by
  rw [isSchemeTheoreticallyDominant_iff, ← Scheme.IdealSheafData.support_eq_top_iff,
    ← SetLike.coe_injective.eq_iff, TopologicalSpace.Closeds.coe_top, ← Set.univ_subset_iff,
    ← f.denseRange.closure_eq, f.ker.support.isClosed.closure_subset_iff]
  exact f.range_subset_ker_support

/-- If the target is reduced and the map is quasi-compact, then scheme-theoretically dominant
is equivalent to dominant. -/
lemma isSchemeTheoreticallyDominant_iff_isDominant (f : X ⟶ Y) [QuasiCompact f] [IsReduced Y] :
    IsSchemeTheoreticallyDominant f ↔ IsDominant f :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ .of_isDominant _⟩

lemma Scheme.Hom.app_injective (f : X ⟶ Y) [IsSchemeTheoreticallyDominant f] [QuasiCompact f]
    (U : Y.Opens) :
    Function.Injective (f.app U) := by
  wlog hU : IsAffineOpen U generalizing U; swap
  · rw [RingHom.injective_iff_ker_eq_bot, ← f.ker_apply ⟨U, hU⟩, f.ker_eq_bot]
    simp
  rw [injective_iff_map_eq_zero]
  intro s hs
  refine Y.IsSheaf.section_ext fun x hx ↦ ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU : V ≤ U⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
  refine ⟨V, hVU, hxV, this V hV ?_⟩
  rw [← ConcreteCategory.comp_apply, f.naturality]
  simp [hs]

lemma IsSchemeTheoreticallyDominant.isReduced (f : X ⟶ Y) [IsSchemeTheoreticallyDominant f]
    [QuasiCompact f] [IsReduced X] : IsReduced Y :=
  ⟨fun _ ↦ isReduced_of_injective _ (f.app_injective _)⟩

set_option backward.isDefEq.respectTransparency false in
instance IsSchemeTheoreticallyDominant.pullbackSnd (f : X ⟶ S) (g : Y ⟶ S)
    [IsSchemeTheoreticallyDominant f] [QuasiCompact f] [Flat g] :
    IsSchemeTheoreticallyDominant (pullback.snd f g) := by
  rw [isSchemeTheoreticallyDominant_iff]
  let h𝒰 := Y.isBasis_affineOpens.isOpenCover_mem_and_le
    (S.isBasis_affineOpens.isOpenCover.comap g.base.hom)
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top (fun U ↦ ⟨_, by exact U.2.1⟩) h𝒰 ?_
  rintro ⟨⟨V, ⟨U, hU⟩⟩, hV, hVU : V ≤ g ⁻¹ᵁ U⟩
  simp only [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply, ← le_bot_iff]
  intro x hx
  have := mono_pushoutSection_of_isCompact_of_flat_right
    (.of_hasPullback f g) (UY := pullback.snd f g ⁻¹ᵁ V) hVU le_rfl (by
      grw [← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage, right_eq_inf,
        hVU]) hU hV (f.isCompact_preimage hU.isCompact)
  rw [@ConcreteCategory.mono_iff_injective_of_preservesPullback] at this
  refine CommRingCat.inr_injective_of_flat (f.appLE U (f ⁻¹ᵁ U) le_rfl) (g.appLE U V hVU)
    (by simpa [Scheme.Hom.appLE] using f.app_injective U) (g.flat_appLE hU hV hVU) ?_
  apply this
  simpa [← CommRingCat.comp_apply, ← Scheme.Hom.app_eq_appLE] using hx

lemma IsSchemeTheoreticallyDominant.of_isPullback {f : X ⟶ S} {g : Y ⟶ S}
    {pX : Z ⟶ X} {pY : Z ⟶ Y} (H : IsPullback pX pY f g)
    [IsSchemeTheoreticallyDominant f] [QuasiCompact f] [Flat g] :
    IsSchemeTheoreticallyDominant pY := by
  rw [← H.isoPullback_hom_snd]
  infer_instance

instance IsSchemeTheoreticallyDominant.pullbackFst (f : X ⟶ S) (g : Y ⟶ S)
    [IsSchemeTheoreticallyDominant g] [QuasiCompact g] [Flat f] :
    IsSchemeTheoreticallyDominant (pullback.fst f g) :=
  .of_isPullback (.flip <| .of_hasPullback _ _)

end AlgebraicGeometry
