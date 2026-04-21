/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
public import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
/-!

# Effective epimorphisms in `TopCat`

This file proves the result `TopCat.effectiveEpi_iff_isQuotientMap`:
The effective epimorphisms in `TopCat` are precisely the quotient maps.

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe u

open CategoryTheory Limits Topology

namespace TopCat

/--
Implementation: If `π` is a morphism in `TopCat` which is a quotient map, then it is an effective
epimorphism. The theorem `TopCat.effectiveEpi_iff_isQuotientMap` should be used instead of
this definition.
-/
noncomputable
def effectiveEpiStructOfQuotientMap {B X : TopCat.{u}} (π : X ⟶ B) (hπ : IsQuotientMap π) :
    EffectiveEpiStruct π where
  /- `IsQuotientMap.lift` gives the required morphism -/
  desc e h := ofHom <| hπ.lift e.hom fun a b hab ↦
    CategoryTheory.congr_fun (h
      (ofHom ⟨fun _ ↦ a, continuous_const⟩)
      (ofHom ⟨fun _ ↦ b, continuous_const⟩)
    (by ext; exact hab)) a
  /- `IsQuotientMap.lift_comp` gives the factorisation -/
  fac e h := hom_ext (hπ.lift_comp e.hom
    fun a b hab ↦ CategoryTheory.congr_fun (h
      (ofHom ⟨fun _ ↦ a, continuous_const⟩)
      (ofHom ⟨fun _ ↦ b, continuous_const⟩)
    (by ext; exact hab)) a)
  /- Uniqueness follows from the fact that `IsQuotientMap.lift` is an equivalence (given by
  `IsQuotientMap.liftEquiv`). -/
  uniq e h g hm := by
    suffices g = ofHom (hπ.liftEquiv ⟨e.hom,
      fun a b hab ↦ CategoryTheory.congr_fun (h
          (ofHom ⟨fun _ ↦ a, continuous_const⟩)
          (ofHom ⟨fun _ ↦ b, continuous_const⟩)
          (by ext; exact hab))
        a⟩) by assumption
    apply hom_ext
    rw [hom_ofHom, ← Equiv.symm_apply_eq hπ.liftEquiv]
    ext
    simp only [IsQuotientMap.liftEquiv_symm_apply_coe, ContinuousMap.comp_apply, ← hm]
    rfl

/-- The effective epimorphisms in `TopCat` are precisely the quotient maps. -/
theorem effectiveEpi_iff_isQuotientMap {B X : TopCat.{u}} (π : X ⟶ B) :
    EffectiveEpi π ↔ IsQuotientMap π := by
  /- The backward direction is given by `effectiveEpiStructOfQuotientMap` above. -/
  refine ⟨fun _ ↦ ?_, fun hπ ↦ ⟨⟨effectiveEpiStructOfQuotientMap π hπ⟩⟩⟩
  /- Since `TopCat` has pullbacks, `π` is in fact a `RegularEpi`. This means that it exhibits `B` as
    a coequalizer of two maps into `X`. It suffices to prove that `π` followed by the isomorphism to
    an arbitrary coequalizer is a quotient map. -/
  exact isQuotientMap_of_isColimit_cofork _ (IsRegularEpi.isColimit π)

end TopCat
