/-
Copyright (c) 2023 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Boris Bolvig Kjær, Jon Eugster, Sina Hazratpour
-/
import Mathlib.CategoryTheory.Sites.Coherent.ReflectsPreregular
import Mathlib.Topology.Category.CompHaus.EffectiveEpi
import Mathlib.Topology.Category.Profinite.Limits
import Mathlib.Topology.Category.Stonean.Basic

/-!
# Effective epimorphisms and finite effective epimorphic families in `Profinite`

This file proves that `Profinite` is `Preregular`. Together with the fact that it is
`FinitaryPreExtensive`, this implies that `Profinite` is `Precoherent`.

To do this, we need to characterise effective epimorphisms in `Profinite`. As a consequence, we also
get a characterisation of finite effective epimorphic families.

## Main results

* `Profinite.effectiveEpi_tfae`: For a morphism in `Profinite`, the conditions surjective,
  epimorphic, and effective epimorphic are all equivalent.

* `Profinite.effectiveEpiFamily_tfae`: For a finite family of morphisms in `Profinite` with fixed
  target in `Profinite`, the conditions jointly surjective, jointly epimorphic and effective
  epimorphic are all equivalent.

As a consequence, we obtain instances that `Profinite` is precoherent and preregular.

-/

universe u

/-
Previously, this had accidentally been made a global instance,
and we now turn it on locally when convenient.
-/
attribute [local instance] CategoryTheory.ConcreteCategory.instFunLike

open CategoryTheory Limits

namespace Profinite

/--
Implementation: If `π` is a surjective morphism in `Profinite`, then it is an effective epi.
The theorem `Profinite.effectiveEpi_tfae` should be used instead.
-/
noncomputable
def struct {B X : Profinite.{u}} (π : X ⟶ B) (hπ : Function.Surjective π) :
    EffectiveEpiStruct π where
  desc e h := (QuotientMap.of_surjective_continuous hπ π.continuous).lift e fun a b hab ↦
    DFunLike.congr_fun (h ⟨fun _ ↦ a, continuous_const⟩ ⟨fun _ ↦ b, continuous_const⟩
    (by ext; exact hab)) a
  fac e h := ((QuotientMap.of_surjective_continuous hπ π.continuous).lift_comp e
    fun a b hab ↦ DFunLike.congr_fun (h ⟨fun _ ↦ a, continuous_const⟩ ⟨fun _ ↦ b, continuous_const⟩
    (by ext; exact hab)) a)
  uniq e h g hm := by
    suffices g = (QuotientMap.of_surjective_continuous hπ π.continuous).liftEquiv ⟨e,
      fun a b hab ↦ DFunLike.congr_fun
        (h ⟨fun _ ↦ a, continuous_const⟩ ⟨fun _ ↦ b, continuous_const⟩ (by ext; exact hab))
        a⟩ by assumption
    rw [← Equiv.symm_apply_eq (QuotientMap.of_surjective_continuous hπ π.continuous).liftEquiv]
    ext
    simp only [QuotientMap.liftEquiv_symm_apply_coe, ContinuousMap.comp_apply, ← hm]
    rfl

open List in
theorem effectiveEpi_tfae
    {B X : Profinite.{u}} (π : X ⟶ B) :
    TFAE
    [ EffectiveEpi π
    , Epi π
    , Function.Surjective π
    ] := by
  tfae_have 1 → 2
  · intro; infer_instance
  tfae_have 2 ↔ 3
  · exact epi_iff_surjective π
  tfae_have 3 → 1
  · exact fun hπ ↦ ⟨⟨struct π hπ⟩⟩
  tfae_finish

instance : profiniteToCompHaus.PreservesEffectiveEpis where
  preserves f h :=
    ((CompHaus.effectiveEpi_tfae _).out 0 2).mpr (((Profinite.effectiveEpi_tfae _).out 0 2).mp h)

instance : profiniteToCompHaus.ReflectsEffectiveEpis where
  reflects f h :=
    ((Profinite.effectiveEpi_tfae f).out 0 2).mpr (((CompHaus.effectiveEpi_tfae _).out 0 2).mp h)

/--
An effective presentation of an `X : Profinite` with respect to the inclusion functor from `Stonean`
-/
noncomputable def profiniteToCompHausEffectivePresentation (X : CompHaus) :
    profiniteToCompHaus.EffectivePresentation X where
  p := Stonean.toProfinite.obj X.presentation
  f := CompHaus.presentation.π X
  effectiveEpi := ((CompHaus.effectiveEpi_tfae _).out 0 1).mpr (inferInstance : Epi _)

instance : profiniteToCompHaus.EffectivelyEnough where
  presentation X := ⟨profiniteToCompHausEffectivePresentation X⟩

instance : Preregular Profinite.{u} := profiniteToCompHaus.reflects_preregular

example : Precoherent Profinite.{u} := inferInstance

-- TODO: prove this for `Type*`
open List in
theorem effectiveEpiFamily_tfae
    {α : Type} [Finite α] {B : Profinite.{u}}
    (X : α → Profinite.{u}) (π : (a : α) → (X a ⟶ B)) :
    TFAE
    [ EffectiveEpiFamily X π
    , Epi (Sigma.desc π)
    , ∀ b : B, ∃ (a : α) (x : X a), π a x = b
    ] := by
  tfae_have 2 → 1
  · intro
    simpa [← effectiveEpi_desc_iff_effectiveEpiFamily, (effectiveEpi_tfae (Sigma.desc π)).out 0 1]
  tfae_have 1 → 2
  · intro; infer_instance
  tfae_have 3 ↔ 1
  · erw [((CompHaus.effectiveEpiFamily_tfae
      (fun a ↦ profiniteToCompHaus.obj (X a)) (fun a ↦ profiniteToCompHaus.map (π a))).out 2 0 : )]
    exact ⟨fun h ↦ profiniteToCompHaus.finite_effectiveEpiFamily_of_map _ _ h,
      fun _ ↦ inferInstance⟩
  tfae_finish

theorem effectiveEpiFamily_of_jointly_surjective
    {α : Type} [Finite α] {B : Profinite.{u}}
    (X : α → Profinite.{u}) (π : (a : α) → (X a ⟶ B))
    (surj : ∀ b : B, ∃ (a : α) (x : X a), π a x = b) :
    EffectiveEpiFamily X π :=
  ((effectiveEpiFamily_tfae X π).out 2 0).mp surj

end Profinite
