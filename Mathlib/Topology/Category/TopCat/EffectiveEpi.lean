/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Sites.EffectiveEpimorphic
import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
/-!

# Effective epimorphisms in `TopCat`

This file proves the result `TopCat.effectiveEpi_iff_quotientMap`:
The effective epimorphisms in `TopCat` are precisely the quotient maps.

-/

universe u

open CategoryTheory Limits

namespace TopCat

/--
Implementation: If `π` is a morphism in `TopCat` which is a quotient map, then it is an effective
epimorphism. The theorem `TopCat.effectiveEpi_iff_quotientMap` should be used instead of
the definition.
-/
noncomputable
def QuotientEpiStruct {B X : TopCat.{u}} (π : X ⟶ B) (hπ : QuotientMap π) : EffectiveEpiStruct π where
  desc e h := hπ.lift e fun a b hab ↦
    DFunLike.congr_fun (h ⟨fun _ ↦ a, continuous_const⟩ ⟨fun _ ↦ b, continuous_const⟩
    (by ext; exact hab)) a
  fac e h := (hπ.lift_comp e
    fun a b hab ↦ DFunLike.congr_fun (h ⟨fun _ ↦ a, continuous_const⟩ ⟨fun _ ↦ b, continuous_const⟩
    (by ext; exact hab)) a)
  uniq e h g hm := by
    suffices g = hπ.liftEquiv ⟨e,
      fun a b hab ↦ DFunLike.congr_fun
        (h ⟨fun _ ↦ a, continuous_const⟩ ⟨fun _ ↦ b, continuous_const⟩ (by ext; exact hab))
        a⟩ by assumption
    rw [← Equiv.symm_apply_eq hπ.liftEquiv]
    ext
    simp only [QuotientMap.liftEquiv_symm_apply_coe, ContinuousMap.comp_apply, ← hm]
    rfl

/-- The effective epimorphisms in `TopCat` are precisely the quotient maps. -/
theorem effectiveEpi_iff_quotientMap {B X : TopCat.{u}} (π : X ⟶ B) :
    EffectiveEpi π ↔ QuotientMap π := by
  refine ⟨fun _ ↦ ?_, fun hπ ↦ ⟨⟨QuotientEpiStruct π hπ⟩⟩⟩
  have hπ : RegularEpi π := inferInstance
  let F := parallelPair hπ.left hπ.right
  let i : B ≅ colimit F := hπ.isColimit.coconePointUniqueUpToIso (colimit.isColimit _)
  have : QuotientMap (homeoOfIso i ∘ π) := by
    constructor
    · change Function.Surjective (π ≫ i.hom)
      rw [← epi_iff_surjective]
      infer_instance
    · ext U
      have : π ≫ i.hom = colimit.ι F WalkingParallelPair.one := by simp [← Iso.eq_comp_inv]
      rw [isOpen_coinduced (f := (homeoOfIso i ∘ π)), coequalizer_isOpen_iff _ U, ← this]
      rfl
  simpa [← Function.comp.assoc] using (homeoOfIso i).symm.quotientMap.comp this

end TopCat
