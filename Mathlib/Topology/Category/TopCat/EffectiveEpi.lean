/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.EffectiveEpi.RegularEpi
import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
/-!

# Effective epimorphisms in `TopCat`

This file proves the result `TopCat.effectiveEpi_iff_quotientMap`:
The effective epimorphisms in `TopCat` are precisely the quotient maps.

-/

universe u

open CategoryTheory Limits Topology

namespace TopCat

/--
Implementation: If `π` is a morphism in `TopCat` which is a quotient map, then it is an effective
epimorphism. The theorem `TopCat.effectiveEpi_iff_quotientMap` should be used instead of
this definition.
-/
noncomputable
def effectiveEpiStructOfQuotientMap {B X : TopCat.{u}} (π : X ⟶ B) (hπ : IsQuotientMap π) :
    EffectiveEpiStruct π where
  /- `IsQuotientMap.lift` gives the required morphism -/
  desc e h := hπ.lift e fun a b hab ↦
    DFunLike.congr_fun (h ⟨fun _ ↦ a, continuous_const⟩ ⟨fun _ ↦ b, continuous_const⟩
    (by ext; exact hab)) a
  /- `IsQuotientMap.lift_comp` gives the factorisation -/
  fac e h := (hπ.lift_comp e
    fun a b hab ↦ DFunLike.congr_fun (h ⟨fun _ ↦ a, continuous_const⟩ ⟨fun _ ↦ b, continuous_const⟩
    (by ext; exact hab)) a)
  /- Uniqueness follows from the fact that `IsQuotientMap.lift` is an equivalence (given by
  `IsQuotientMap.liftEquiv`). -/
  uniq e h g hm := by
    suffices g = hπ.liftEquiv ⟨e,
      fun a b hab ↦ DFunLike.congr_fun
        (h ⟨fun _ ↦ a, continuous_const⟩ ⟨fun _ ↦ b, continuous_const⟩ (by ext; exact hab))
        a⟩ by assumption
    rw [← Equiv.symm_apply_eq hπ.liftEquiv]
    ext
    simp only [IsQuotientMap.liftEquiv_symm_apply_coe, ContinuousMap.comp_apply, ← hm]
    rfl

/-- The effective epimorphisms in `TopCat` are precisely the quotient maps. -/
theorem effectiveEpi_iff_quotientMap {B X : TopCat.{u}} (π : X ⟶ B) :
    EffectiveEpi π ↔ IsQuotientMap π := by
  /- The backward direction is given by `effectiveEpiStructOfQuotientMap` above. -/
  refine ⟨fun _ ↦ ?_, fun hπ ↦ ⟨⟨effectiveEpiStructOfQuotientMap π hπ⟩⟩⟩
  /- Since `TopCat` has pullbacks, `π` is in fact a `RegularEpi`. This means that it exhibits `B` as
    a coequalizer of two maps into `X`. It suffices to prove that `π` followed by the isomorphism to
    an arbitrary coequalizer is a quotient map. -/
  have hπ : RegularEpi π := inferInstance
  let F := parallelPair hπ.left hπ.right
  let i : B ≅ colimit F := hπ.isColimit.coconePointUniqueUpToIso (colimit.isColimit _)
  suffices IsQuotientMap (homeoOfIso i ∘ π) by
    simpa [← Function.comp_assoc] using (homeoOfIso i).symm.isQuotientMap.comp this
  constructor
  /- Effective epimorphisms are epimorphisms and epimorphisms in `TopCat` are surjective. -/
  · change Function.Surjective (π ≫ i.hom)
    rw [← epi_iff_surjective]
    infer_instance
  /- The key to proving that the coequalizer has the quotient topology is
    `TopCat.coequalizer_isOpen_iff` which characterises the open sets in a coequalizer. -/
  · ext U
    have : π ≫ i.hom = colimit.ι F WalkingParallelPair.one := by simp [i, ← Iso.eq_comp_inv]
    rw [isOpen_coinduced (f := (homeoOfIso i ∘ π)), coequalizer_isOpen_iff _ U, ← this]
    rfl

end TopCat
