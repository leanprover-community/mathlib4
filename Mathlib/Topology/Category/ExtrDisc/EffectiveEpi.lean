/-
Copyright (c) 2023 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Boris Bolvig Kjær, Jon Eugster, Sina Hazratpour, Nima Rasekh
-/
import Mathlib.Topology.Category.ExtrDisc.ExplicitLimits
import Mathlib.Topology.Category.CompHaus.EffectiveEpi

open CategoryTheory Limits

namespace ExtrDisc

-- Assume we have `X a → B` which are jointly surjective.
variable {α : Type} [Fintype α] {B : ExtrDisc}
  {X : α → ExtrDisc} (π : (a : α) → (X a ⟶ B))
  (surj : ∀ b : B, ∃ (a : α) (x : X a), π a x = b)

/--
`Fin 2` as an extremally disconnected space.
Implementation: This is only used in the proof below.
-/
protected
def two : ExtrDisc where
  compHaus := CompHaus.of <| ULift <| Fin 2
  extrDisc := by
    dsimp
    constructor
    intro U _
    apply isOpen_discrete (closure U)

lemma epi_iff_surjective {X Y : ExtrDisc} (f : X ⟶ Y) :
    Epi f ↔ Function.Surjective f := by
  constructor
  · dsimp [Function.Surjective]
    contrapose!
    rintro ⟨y,hy⟩ h
    let C := Set.range f
    have hC : IsClosed C := (isCompact_range f.continuous).isClosed
    let U := Cᶜ
    have hyU : y ∈ U := by
      refine' Set.mem_compl _
      rintro ⟨y', hy'⟩
      exact hy y' hy'
    have hUy : U ∈ nhds y := hC.compl_mem_nhds hyU
    haveI : TotallyDisconnectedSpace ((forget CompHaus).obj (toCompHaus.obj Y)) :=
      show TotallyDisconnectedSpace Y from inferInstance
    obtain ⟨V, hV, hyV, hVU⟩ := isTopologicalBasis_clopen.mem_nhds_iff.mp hUy
    classical
    let g : Y ⟶ ExtrDisc.two :=
      ⟨(LocallyConstant.ofClopen hV).map ULift.up, LocallyConstant.continuous _⟩
    let h : Y ⟶ ExtrDisc.two := ⟨fun _ => ⟨1⟩, continuous_const⟩
    have H : h = g := by
      rw [← cancel_epi f]
      apply ContinuousMap.ext; intro x
      apply ULift.ext
      change 1 =  _
      dsimp [LocallyConstant.ofClopen]
      -- BUG: Should not have to provide instance `(ExtrDisc.instTopologicalSpace Y)` explicitely
      rw [comp_apply, @ContinuousMap.coe_mk _ _ (ExtrDisc.instTopologicalSpace Y),
      Function.comp_apply, if_neg]
      refine' mt (fun α => hVU α) _
      simp only [Set.mem_compl_iff, Set.mem_range, not_exists, not_forall, not_not]
      exact ⟨x, rfl⟩
    apply_fun fun e => (e y).down at H
    dsimp [LocallyConstant.ofClopen] at H
    change 1 = ite _ _ _ at H
    rw [if_pos hyV] at H
    exact top_ne_bot H
  · intro (h : Function.Surjective (toCompHaus.map f))
    rw [← CompHaus.epi_iff_surjective] at h
    constructor
    intro W a b h
    apply Functor.map_injective toCompHaus
    apply_fun toCompHaus.map at h
    simp only [Functor.map_comp] at h
    rwa [← cancel_epi (toCompHaus.map f)]

/-!
Everything in this section is only used for the proof of
`effectiveEpiFamily_of_jointly_surjective`
-/
namespace EffectiveEpiFamily

/--
Abbreviation for the fully faithful functor `ExtrDisc ⥤ CompHaus` called `ExtrDisc.toCompHaus`
-/
abbrev F := ExtrDisc.toCompHaus

/-- A helper lemma lifting the condition
```
∀ {Z : ExtrDisc} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),
  g₁ ≫ π a₁ = g₂ ≫ π a₂ → g₁ ≫ e a₁ = g₂ ≫ e a₂)
```
from `Z : ExtrDisc` to `Z : CompHaus`. This condition is used in
the definition of `EffectiveEpiFamily.dec`, etc.
-/
lemma helper {W : ExtrDisc} {e : (a : α) → X a ⟶ W}
    (h : ∀ {Z : ExtrDisc} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),
      g₁ ≫ π a₁ = g₂ ≫ π a₂ → g₁ ≫ e a₁ = g₂ ≫ e a₂)
    : ∀ {Z : CompHaus} (a₁ a₂ : α) (g₁ : Z ⟶ F.obj (X a₁)) (g₂ : Z ⟶ F.obj (X a₂)),
        g₁ ≫ (π a₁) = g₂ ≫ (π a₂) → g₁ ≫ e a₁ = g₂ ≫ e a₂ := by
  intro Z a₁ a₂ g₁ g₂ hg
  -- The Stone-Cech-compactification `βZ` of `Z : CompHaus` is in `ExtrDisc`
  let βZ := Z.presentation
  let g₁' := F.preimage (Z.presentationπ ≫ g₁ : F.obj βZ ⟶ F.obj (X a₁))
  let g₂' := F.preimage (Z.presentationπ ≫ g₂ : F.obj βZ ⟶ F.obj (X a₂))
  -- Use that `βZ → Z` is an epi
  apply Epi.left_cancellation (f := Z.presentationπ)
  -- By definition `g₁' = presentationπ ≫ g₁` and `g₂' = presentationπ ≫ g₂`
  change g₁' ≫ e a₁ = g₂' ≫ e a₂
  -- use assumption in `ExtrDisc`
  apply h
  change CompHaus.presentationπ Z ≫ g₁ ≫ π a₁ = CompHaus.presentationπ Z ≫ g₂ ≫ π a₂
  simp [hg]

/-- Implementation: The structure for the `EffectiveEpiFamily X π` -/
noncomputable
def struct : EffectiveEpiFamilyStruct X π where
  desc := fun {W} e h => ExtrDisc.toCompHaus.preimage <|
    -- Use the `EffectiveEpiFamily F(X) F(π)` on `CompHaus`
    (CompHaus.effectiveEpiFamily_of_jointly_surjective (fun (a : α) => F.obj (X a)) π surj).desc
    (fun (a : α) => F.map (e a)) (helper π h)
  fac := by
    intro W e he a
    -- The `EffectiveEpiFamily F(X) F(π)` on `CompHaus`
    have : EffectiveEpiFamily (fun a => F.obj (X a)) π :=
      CompHaus.effectiveEpiFamily_of_jointly_surjective (fun a => F.obj (X a)) π surj
    -- The `fac` on `CompHaus`
    have fac₁ := EffectiveEpiFamily.fac (fun (a : α) => F.obj (X a)) π e (helper π he) a
    change F.map (π a ≫ _) = F.map (e a) at fac₁
    replace fac₁ := Faithful.map_injective fac₁
    exact fac₁
  uniq := by
    intro W e he m hm
    have Fhm : ∀ (a : α), π a ≫ F.map m = e a
    · aesop_cat
    have : EffectiveEpiFamily (fun a => F.obj (X a)) π :=
      CompHaus.effectiveEpiFamily_of_jointly_surjective (fun a => F.obj (X a)) π surj
    have uniq₁ :=
      EffectiveEpiFamily.uniq (fun (a : α) => F.obj (X a)) π e (helper π he) (F.map m) Fhm
    change F.map m = F.map _ at uniq₁
    replace uniq₁ := Faithful.map_injective uniq₁
    exact uniq₁

end EffectiveEpiFamily

/-- On direction of `effectiveEpiFamily_tfae` -/
theorem effectiveEpiFamily_of_jointly_surjective
    {α : Type} [Fintype α] {B : ExtrDisc}
    (X : α → ExtrDisc) (π : (a : α) → (X a ⟶ B))
    (surj : ∀ b : B, ∃ (a : α) (x : X a), π a x = b) :
    EffectiveEpiFamily X π :=
  ⟨⟨ExtrDisc.EffectiveEpiFamily.struct π surj⟩⟩

open List in
/--
For a finite family of extremally disconnected spaces `πₐ : Xₐ → B` the following are equivalent:
* they are an effective epi family
* the map `∐ πₐ ⟶ B` is an epimorphism
* they are jointly surjective
-/
theorem effectiveEpiFamily_tfae {α : Type} [Fintype α] {B : ExtrDisc}
    (X : α → ExtrDisc)
    (π : (a : α) → (X a ⟶ B)) :
    TFAE [
      EffectiveEpiFamily X π,
      Epi (Limits.Sigma.desc π),
      ∀ (b : B), ∃ (a : α) (x : X a), π a x = b
    ] := by
  tfae_have 1 → 2
  · intro; infer_instance
  tfae_have 1 → 2
  · intro; infer_instance
  tfae_have 2 → 3
  · intro e
    rw [epi_iff_surjective] at e
    intro b
    obtain ⟨t,rfl⟩ := e b
    let q := (FromFiniteCoproductIso X).inv t
    refine ⟨q.1,q.2,?_⟩
    rw [← (FromFiniteCoproductIso X).inv_hom_id_apply t]
    show _ = ((FromFiniteCoproductIso X).hom ≫ Sigma.desc π) ((FromFiniteCoproductIso X).inv t)
    suffices (FromFiniteCoproductIso X).hom ≫ Sigma.desc π = finiteCoproduct.desc X π by
      rw [this]; rfl
    apply Eq.symm
    rw [← Iso.inv_comp_eq]
    apply colimit.hom_ext
    rintro ⟨a⟩
    simp only [Discrete.functor_obj, colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app,
      FromFiniteCoproductIso, colimit.comp_coconePointUniqueUpToIso_inv_assoc]
    ext; rfl
  tfae_have 3 → 1
  · apply effectiveEpiFamily_of_jointly_surjective
  tfae_finish

end ExtrDisc
