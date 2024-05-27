/-
Copyright (c) 2023 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Boris Bolvig Kjær, Jon Eugster, Sina Hazratpour, Nima Rasekh
-/
import Mathlib.Topology.Category.Stonean.Limits
import Mathlib.Topology.Category.CompHaus.EffectiveEpi

/-!
# Effective epimorphic families in `Stonean`

This file proves that `Stonean` is `Preregular`. Together with the fact that it is
`FinitaryPreExtensive`, this implies that `Stonean` is `Precoherent`.

To do this, we need to characterise effective epimorphisms in `Stonean`. As a consequence, we also
get a characterisation of finite effective epimorphic families.

## Main results

* `Stonean.effectiveEpi_tfae`: For a morphism in `Stonean`, the conditions surjective,
  epimorphic, and effective epimorphic are all equivalent.

* `Stonean.effectiveEpiFamily_tfae`: For a finite family of morphisms in `Stonean` with fixed
  target in `Stonean`, the conditions jointly surjective, jointly epimorphic and effective
  epimorphic are all equivalent.

As a consequence, we obtain instances that `Stonean` is precoherent and preregular.

- TODO: Write API for reflecting effective epimorphisms and deduce the contents of this file by
  abstract nonsense from the corresponding results for `CompHaus`.

-/

universe u

open CategoryTheory Limits

namespace Stonean

/--
Implementation: If `π` is a surjective morphism in `Stonean`, then it is an effective epi.
The theorem `Stonean.effectiveEpi_tfae` should be used instead.
-/
noncomputable
def struct {B X : Stonean.{u}} (π : X ⟶ B) (hπ : Function.Surjective π) : EffectiveEpiStruct π where
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
    {B X : Stonean.{u}} (π : X ⟶ B) :
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

instance : Preregular Stonean where
  exists_fac := by
    intro X Y Z f π hπ
    have := epiOfEffectiveEpi π
    exact ⟨X, 𝟙 X, inferInstance, Projective.factors f π⟩

example : Precoherent Stonean.{u} := inferInstance

-- TODO: prove this for `Type*`
open List in
theorem effectiveEpiFamily_tfae
    {α : Type} [Finite α] {B : Stonean.{u}}
    (X : α → Stonean.{u}) (π : (a : α) → (X a ⟶ B)) :
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
  tfae_have 3 → 2
  · intro e
    rw [epi_iff_surjective]
    intro b
    obtain ⟨t, x, h⟩ := e b
    refine ⟨Sigma.ι X t x, ?_⟩
    change (Sigma.ι X t ≫ Sigma.desc π) x = _
    simpa using h
  tfae_have 2 → 3
  · intro e; rw [epi_iff_surjective] at e
    let i : ∐ X ≅ finiteCoproduct X :=
      (colimit.isColimit _).coconePointUniqueUpToIso (finiteCoproduct.isColimit _)
    intro b
    obtain ⟨t, rfl⟩ := e b
    let q := i.hom t
    refine ⟨q.1,q.2,?_⟩
    have : t = i.inv (i.hom t) := show t = (i.hom ≫ i.inv) t by simp only [i.hom_inv_id]; rfl
    rw [this]
    show _ = (i.inv ≫ Sigma.desc π) (i.hom t)
    suffices i.inv ≫ Sigma.desc π = finiteCoproduct.desc X π by
      rw [this]; rfl
    rw [Iso.inv_comp_eq]
    apply colimit.hom_ext
    rintro ⟨a⟩
    simp only [i, Discrete.functor_obj, colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app,
      colimit.comp_coconePointUniqueUpToIso_hom_assoc]
    ext; rfl
  tfae_finish

theorem effectiveEpiFamily_of_jointly_surjective
    {α : Type} [Finite α] {B : Stonean.{u}}
    (X : α → Stonean.{u}) (π : (a : α) → (X a ⟶ B))
    (surj : ∀ b : B, ∃ (a : α) (x : X a), π a x = b) :
    EffectiveEpiFamily X π :=
  ((effectiveEpiFamily_tfae X π).out 2 0).mp surj

open CompHaus Functor

theorem _root_.CategoryTheory.EffectiveEpiFamily.toCompHaus
    {α : Type} [Finite α] {B : Stonean.{u}}
    {X : α → Stonean.{u}} {π : (a : α) → (X a ⟶ B)} (H : EffectiveEpiFamily X π) :
    EffectiveEpiFamily (toCompHaus.obj <| X ·) (toCompHaus.map <| π ·) := by
  refine ((CompHaus.effectiveEpiFamily_tfae _ _).out 0 2).2 (fun b => ?_)
  exact (((effectiveEpiFamily_tfae _ _).out 0 2).1 H : ∀ _, ∃ _, _) _

end Stonean
