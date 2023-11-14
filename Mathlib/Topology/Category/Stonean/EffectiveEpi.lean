/-
Copyright (c) 2023 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Boris Bolvig Kjær, Jon Eugster, Sina Hazratpour, Nima Rasekh
-/
import Mathlib.Topology.Category.Stonean.Limits
import Mathlib.Topology.Category.CompHaus.EffectiveEpi

/-!
# Effective epimorphic families in `Stonean`

Let `π a : X a ⟶ B` be a family of morphisms in `Stonean` indexed by a finite type `α`.
In this file, we show that the following are all equivalent:
- The family `π` is effective epimorphic.
- The induced map `∐ X ⟶ B` is epimorphic.
- The family `π` is jointly surjective.

As a consequence, we show (see `effectiveEpi_iff_surjective`) that all epimorphisms in `Stonean` 
are effective, and that `Stonean` is preregular.

## Main results
- `Stonean.effectiveEpiFamily_tfae`: characterise being an effective epimorphic family.
- `Stonean.instPrecoherent`: `Stonean` is precoherent.

## Implementation notes
The entire section `EffectiveEpiFamily` comprises exclusively a technical construction for
the main proof and does not contain any statements that would be useful in other contexts.

-/

universe u

open CategoryTheory Limits

namespace Stonean

noncomputable
def struct {B X : Stonean.{u}} (π : X ⟶ B) (hπ : Function.Surjective π) : EffectiveEpiStruct π where
  desc e h := by
    refine QuotientMap.lift (QuotientMap.of_surjective_continuous hπ π.continuous) e fun a b hab ↦
      FunLike.congr_fun (h ⟨fun _ ↦ a, continuous_const⟩ ⟨fun _ ↦ b, continuous_const⟩
      (by ext; exact hab)) a
  fac e h := by
    ext
    have := QuotientMap.lift_comp (QuotientMap.of_surjective_continuous hπ π.continuous) e
      fun a b hab ↦ FunLike.congr_fun (h ⟨fun _ ↦ a, continuous_const⟩ ⟨fun _ ↦ b, continuous_const⟩
      (by ext; exact hab)) a
    exact FunLike.congr_fun this _
  uniq {W} e h g hm := by
    have hg : g = (QuotientMap.liftEquiv (QuotientMap.of_surjective_continuous hπ π.continuous)) ⟨e,
      fun a b hab ↦ FunLike.congr_fun (h ⟨fun _ ↦ a, continuous_const⟩ ⟨fun _ ↦ b, continuous_const⟩
      (by ext; exact hab)) a⟩
    · rw [← Equiv.symm_apply_eq
        (QuotientMap.liftEquiv (QuotientMap.of_surjective_continuous hπ π.continuous))]
      ext
      simp only [QuotientMap.liftEquiv_symm_apply_coe, ContinuousMap.comp_apply]
      rw [← hm]
      rfl
    · exact hg

open List in
theorem effectiveEpi_tfae
    {B X : Stonean.{u}} (π : X ⟶ B) :
    TFAE
    [ EffectiveEpi π
    , Epi π
    , Function.Surjective π
    ] := by
  tfae_have 1 → 2
  · intro; exact epiOfEffectiveEpi _
  tfae_have 2 ↔ 3
  · exact epi_iff_surjective π
  tfae_have 3 → 1
  · exact fun hπ ↦ ⟨⟨struct π hπ⟩⟩
  tfae_finish

lemma effectiveEpi_iff_surjective {X Y : Stonean} (f : X ⟶ Y) :
    EffectiveEpi f ↔ Function.Surjective f := (effectiveEpi_tfae f).out 0 2

instance : Preregular Stonean where
  exists_fac := by
    intro X Y Z f π hπ
    have := epiOfEffectiveEpi π
    exact ⟨X, 𝟙 X, inferInstance, Projective.factors f π⟩

instance : Precoherent Stonean.{u} := inferInstance

-- TODO: prove this for `Type*`
open List in
theorem effectiveEpiFamily_tfae
    {α : Type} [Fintype α] {B : Stonean.{u}}
    (X : α → Stonean.{u}) (π : (a : α) → (X a ⟶ B)) :
    TFAE
    [ EffectiveEpiFamily X π
    , Epi (Sigma.desc π)
    , ∀ b : B, ∃ (a : α) (x : X a), π a x = b
    ] := by
  tfae_have 2 → 1
  · intro
    rwa [← effectiveEpi_desc_iff_effectiveEpiFamily,
      effectiveEpi_iff_surjective, ← epi_iff_surjective]
  tfae_have 1 → 2
  · intro; exact epiCoproductDescOfEffectiveEpiFamily _ _
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
    simp only [Discrete.functor_obj, colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app,
      colimit.comp_coconePointUniqueUpToIso_hom_assoc]
    ext; rfl
  tfae_finish

theorem effectiveEpiFamily_of_jointly_surjective
    {α : Type} [Fintype α] {B : Stonean.{u}}
    (X : α → Stonean.{u}) (π : (a : α) → (X a ⟶ B))
    (surj : ∀ b : B, ∃ (a : α) (x : X a), π a x = b) :
    EffectiveEpiFamily X π :=
  ((effectiveEpiFamily_tfae X π).out 2 0).mp surj

open CompHaus Functor

theorem _root_.CategoryTheory.EffectiveEpiFamily.toCompHaus
    {α : Type} [Fintype α] {B : Stonean.{u}}
    {X : α → Stonean.{u}} {π : (a : α) → (X a ⟶ B)} (H : EffectiveEpiFamily X π) :
    EffectiveEpiFamily (toCompHaus.obj <| X ·) (toCompHaus.map <| π ·) := by
  refine' ((CompHaus.effectiveEpiFamily_tfae _ _).out 0 2).2 (fun b => _)
  exact (((effectiveEpiFamily_tfae _ _).out 0 2).1 H : ∀ _, ∃ _, _) _

end Stonean
