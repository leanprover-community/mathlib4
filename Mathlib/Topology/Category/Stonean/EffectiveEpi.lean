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

/- Assume we have a family `X a → B` which is jointly surjective. -/
variable {α : Type} [Fintype α] {B : Stonean}
  {X : α → Stonean} (π : (a : α) → (X a ⟶ B))
  (surj : ∀ b : B, ∃ (a : α) (x : X a), π a x = b)

/-!
This section contains exclusively technical definitions and results that are used
in the proof of `Stonean.effectiveEpiFamily_of_jointly_surjective`.
-/
namespace EffectiveEpiFamily

/-- Implementation: Abbreviation for the fully faithful functor `Stonean ⥤ CompHaus`. -/
abbrev F := Stonean.toCompHaus

open CompHaus in
/-- Implementation: A helper lemma lifting the condition

```
∀ {Z : Stonean} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),
  g₁ ≫ π a₁ = g₂ ≫ π a₂ → g₁ ≫ e a₁ = g₂ ≫ e a₂)
```

from `Z : Stonean` to `Z : CompHaus`.

The descent `EffectiveEpiFamily.dec` along an effective epi family in a category `C`
takes this condition (for all `Z` in `C`) as an assumption.

In the construction in this file we start with this descent condition for all `Z : Stonean` but
to apply the analogue result on `CompHaus` we need extend this condition to all
`Z : CompHaus`. We do this by considering the Stone-Cech compactification `βZ → Z`
which is an epi in `CompHaus` covering `Z` where `βZ` lies in the image of `Stonean`.
-/
lemma lift_desc_condition {W : Stonean} {e : (a : α) → X a ⟶ W}
    (h : ∀ {Z : Stonean} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),
      g₁ ≫ π a₁ = g₂ ≫ π a₂ → g₁ ≫ e a₁ = g₂ ≫ e a₂) :
    ∀ {Z : CompHaus} (a₁ a₂ : α) (g₁ : Z ⟶ F.obj (X a₁)) (g₂ : Z ⟶ F.obj (X a₂)),
        g₁ ≫ (π a₁) = g₂ ≫ (π a₂) → g₁ ≫ e a₁ = g₂ ≫ e a₂ := by
  intro Z a₁ a₂ g₁ g₂ hg
  -- The Stone-Cech-compactification `βZ` of `Z : CompHaus` is in `Stonean`
  let βZ := Z.presentation
  let g₁' := F.preimage (presentation.π Z ≫ g₁ : F.obj βZ ⟶ F.obj (X a₁))
  let g₂' := F.preimage (presentation.π Z ≫ g₂ : F.obj βZ ⟶ F.obj (X a₂))
  -- Use that `βZ → Z` is an epi
  apply Epi.left_cancellation (f := presentation.π Z)
  -- By definition `g₁' = presentationπ ≫ g₁` and `g₂' = presentationπ ≫ g₂`
  change g₁' ≫ e a₁ = g₂' ≫ e a₂
  -- use the condition in `Stonean`
  apply h
  change presentation.π Z ≫ g₁ ≫ π a₁ = presentation.π Z ≫ g₂ ≫ π a₂
  simp [hg]

/-- Implementation: The structure for the `EffectiveEpiFamily X π`. -/
noncomputable
def struct : EffectiveEpiFamilyStruct X π where
  desc := fun {W} e h => Stonean.toCompHaus.preimage <|
    -- Use the `EffectiveEpiFamily F(X) F(π)` on `CompHaus`
    (CompHaus.effectiveEpiFamily_of_jointly_surjective (F.obj <| X ·) π surj).desc
    (fun (a : α) => F.map (e a)) (lift_desc_condition π h)
  fac := by
    -- The `EffectiveEpiFamily F(X) F(π)` on `CompHaus`
    let fam : EffectiveEpiFamily (F.obj <| X ·) π :=
      CompHaus.effectiveEpiFamily_of_jointly_surjective (F.obj <| X ·) π surj
    intro W e he a
    -- The `fac` on `CompHaus`
    have fac₁ :  F.map (π a ≫ _) = F.map (e a) :=
      EffectiveEpiFamily.fac (F.obj <| X ·) π e (lift_desc_condition π he) a
    exact Faithful.map_injective fac₁
  uniq := by
    -- The `EffectiveEpiFamily F(X) F(π)` on `CompHaus`
    let fam : EffectiveEpiFamily (F.obj <| X ·) π :=
      CompHaus.effectiveEpiFamily_of_jointly_surjective (F.obj <| X ·) π surj
    intro W e he m hm
    have Fhm : ∀ (a : α), π a ≫ F.map m = e a
    · intro a
      simp_all only [toCompHaus_map]
    have uniq₁ : F.map m = F.map _ :=
      EffectiveEpiFamily.uniq (F.obj <| X ·) π e (lift_desc_condition π he) (F.map m) Fhm
    exact Faithful.map_injective uniq₁

end EffectiveEpiFamily

section JointlySurjective

/-- One direction of `effectiveEpiFamily_tfae`. -/
theorem effectiveEpiFamily_of_jointly_surjective
    {α : Type} [Fintype α] {B : Stonean}
    (X : α → Stonean) (π : (a : α) → (X a ⟶ B))
    (surj : ∀ b : B, ∃ (a : α) (x : X a), π a x = b) :
    EffectiveEpiFamily X π :=
  ⟨⟨Stonean.EffectiveEpiFamily.struct π surj⟩⟩

open List in
/--
For a finite family of extremally spaces `π a : X a → B` the following are equivalent:
* `π` is an effective epimorphic family
* the map `∐ π a ⟶ B` is an epimorphism
* `π` is jointly surjective
-/
theorem effectiveEpiFamily_tfae {α : Type} [Fintype α] {B : Stonean}
    (X : α → Stonean) (π : (a : α) → (X a ⟶ B)) :
    TFAE [
      EffectiveEpiFamily X π,
      Epi (Limits.Sigma.desc π),
      ∀ (b : B), ∃ (a : α) (x : X a), π a x = b ] := by
  tfae_have 1 → 2
  · intro
    infer_instance
  tfae_have 1 → 2
  · intro
    infer_instance
  tfae_have 2 → 3
  · intro e
    rw [epi_iff_surjective] at e
    intro b
    obtain ⟨t, rfl⟩ := e b
    let q := (coproductIsoCoproduct X).inv t
    refine ⟨q.1, q.2, ?_⟩
    rw [← (coproductIsoCoproduct X).inv_hom_id_apply t]
    show _ = ((coproductIsoCoproduct X).hom ≫ Sigma.desc π) ((coproductIsoCoproduct X).inv t)
    suffices : (coproductIsoCoproduct X).hom ≫ Sigma.desc π = finiteCoproduct.desc X π
    · rw [this]
      rfl
    apply Eq.symm
    rw [← Iso.inv_comp_eq]
    apply colimit.hom_ext
    rintro ⟨a⟩
    simp only [Discrete.functor_obj, colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app,
      coproductIsoCoproduct, colimit.comp_coconePointUniqueUpToIso_inv_assoc]
    ext
    rfl
  tfae_have 3 → 1
  · apply effectiveEpiFamily_of_jointly_surjective
  tfae_finish

lemma effectiveEpi_iff_surjective {X Y : Stonean} (f : X ⟶ Y) :
    EffectiveEpi f ↔ Function.Surjective f := by
  rw [← epi_iff_surjective]
  exact effectiveEpi_iff_epi (fun _ _ ↦ (effectiveEpiFamily_tfae _ _).out 0 1) f

instance : Preregular Stonean where
  exists_fac := by
    intro X Y Z f π hπ
    exact ⟨X, 𝟙 X, inferInstance, Projective.factors f π⟩

end JointlySurjective

section Coherent

open CompHaus Functor

theorem _root_.CategoryTheory.EffectiveEpiFamily.toCompHaus
    {α : Type} [Fintype α] {B : Stonean.{u}}
    {X : α → Stonean.{u}} {π : (a : α) → (X a ⟶ B)} (H : EffectiveEpiFamily X π) :
    EffectiveEpiFamily (toCompHaus.obj <| X ·) (toCompHaus.map <| π ·) := by
  refine' ((CompHaus.effectiveEpiFamily_tfae _ _).out 0 2).2 (fun b => _)
  exact (((effectiveEpiFamily_tfae _ _).out 0 2).1 H : ∀ _, ∃ _, _) _

instance instPrecoherent : Precoherent Stonean.{u} := by
  constructor
  intro B₁ B₂ f α _ X₁ π₁ h₁
  refine ⟨α, inferInstance, fun a => (CompHaus.pullback f (π₁ a)).presentation, fun a =>
    toCompHaus.preimage (presentation.π _ ≫ (CompHaus.pullback.fst _ _)), ?_, id, fun a =>
    toCompHaus.preimage (presentation.π _ ≫ (CompHaus.pullback.snd _ _ )), fun a => ?_⟩
  · refine ((effectiveEpiFamily_tfae _ _).out 0 2).2 (fun b => ?_)
    have h₁' := ((CompHaus.effectiveEpiFamily_tfae _ _).out 0 2).1 h₁.toCompHaus
    obtain ⟨a, x, h⟩ := h₁' (f b)
    obtain ⟨c, hc⟩ := (CompHaus.epi_iff_surjective _).1
      (presentation.epi_π (CompHaus.pullback f (π₁ a))) ⟨⟨b, x⟩, h.symm⟩
    refine ⟨a, c, ?_⟩
    change toCompHaus.map (toCompHaus.preimage _) _ = _
    simp only [image_preimage, toCompHaus_obj, comp_apply, hc]
    rfl
  · apply map_injective toCompHaus
    simp only [map_comp, image_preimage, Category.assoc]
    congr 1
    ext ⟨⟨_, _⟩, h⟩
    exact h.symm

end Coherent

end Stonean
