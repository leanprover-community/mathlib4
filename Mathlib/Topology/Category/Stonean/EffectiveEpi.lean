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

/--
`Fin 2` as an extremally disconnected space.
Implementation: This is only used in the proof below.
-/
protected
def two : Stonean where
  compHaus := CompHaus.of <| ULift <| Fin 2
  extrDisc := by
    dsimp
    -- ⊢ ExtremallyDisconnected (ULift (Fin 2))
    constructor
    -- ⊢ ∀ (U : Set (ULift (Fin 2))), IsOpen U → IsOpen (closure U)
    intro U _
    -- ⊢ IsOpen (closure U)
    apply isOpen_discrete (closure U)
    -- 🎉 no goals

lemma epi_iff_surjective {X Y : Stonean} (f : X ⟶ Y) :
    Epi f ↔ Function.Surjective f := by
  constructor
  -- ⊢ Epi f → Function.Surjective ↑f
  · dsimp [Function.Surjective]
    -- ⊢ Epi f → ∀ (b : CoeSort.coe Y), ∃ a, ↑f a = b
    contrapose!
    -- ⊢ (∃ b, ∀ (a : CoeSort.coe X), ↑f a ≠ b) → ¬Epi f
    rintro ⟨y, hy⟩ h
    -- ⊢ False
    let C := Set.range f
    -- ⊢ False
    have hC : IsClosed C := (isCompact_range f.continuous).isClosed
    -- ⊢ False
    let U := Cᶜ
    -- ⊢ False
    have hyU : y ∈ U := by
      refine' Set.mem_compl _
      rintro ⟨y', hy'⟩
      exact hy y' hy'
    have hUy : U ∈ nhds y := hC.compl_mem_nhds hyU
    -- ⊢ False
    haveI : TotallyDisconnectedSpace ((forget CompHaus).obj (toCompHaus.obj Y)) :=
      show TotallyDisconnectedSpace Y from inferInstance
    obtain ⟨V, hV, hyV, hVU⟩ := isTopologicalBasis_clopen.mem_nhds_iff.mp hUy
    -- ⊢ False
    classical
    let g : Y ⟶ Stonean.two :=
      ⟨(LocallyConstant.ofClopen hV).map ULift.up, LocallyConstant.continuous _⟩
    let h : Y ⟶ Stonean.two := ⟨fun _ => ⟨1⟩, continuous_const⟩
    have H : h = g := by
      rw [← cancel_epi f]
      apply ContinuousMap.ext
      intro x
      apply ULift.ext
      change 1 =  _
      dsimp [LocallyConstant.ofClopen]
      -- BUG: Should not have to provide instance `(Stonean.instTopologicalSpace Y)` explicitely
      rw [comp_apply, @ContinuousMap.coe_mk _ _ (Stonean.instTopologicalSpace Y),
      Function.comp_apply, if_neg]
      refine mt (hVU ·) ?_
      simp only [Set.mem_compl_iff, Set.mem_range, not_exists, not_forall, not_not]
      exact ⟨x, rfl⟩
    apply_fun fun e => (e y).down at H
    dsimp only [LocallyConstant.ofClopen] at H
    change 1 = ite _ _ _ at H
    rw [if_pos hyV] at H
    exact top_ne_bot H
  · intro (h : Function.Surjective (toCompHaus.map f))
    -- ⊢ Epi f
    rw [← CompHaus.epi_iff_surjective] at h
    -- ⊢ Epi f
    constructor
    -- ⊢ ∀ {Z : Stonean} (g h : Y ⟶ Z), f ≫ g = f ≫ h → g = h
    intro W a b h
    -- ⊢ a = b
    apply Functor.map_injective toCompHaus
    -- ⊢ toCompHaus.map a = toCompHaus.map b
    apply_fun toCompHaus.map at h
    -- ⊢ toCompHaus.map a = toCompHaus.map b
    simp only [Functor.map_comp] at h
    -- ⊢ toCompHaus.map a = toCompHaus.map b
    rwa [← cancel_epi (toCompHaus.map f)]
    -- 🎉 no goals

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
`Z : CompHaus`. We do this by considering the Stone-Czech compactification `βZ → Z`
which is an epi in `CompHaus` covering `Z` where `βZ` lies in the image of `Stonean`.
-/
lemma lift_desc_condition {W : Stonean} {e : (a : α) → X a ⟶ W}
    (h : ∀ {Z : Stonean} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),
      g₁ ≫ π a₁ = g₂ ≫ π a₂ → g₁ ≫ e a₁ = g₂ ≫ e a₂)
    : ∀ {Z : CompHaus} (a₁ a₂ : α) (g₁ : Z ⟶ F.obj (X a₁)) (g₂ : Z ⟶ F.obj (X a₂)),
        g₁ ≫ (π a₁) = g₂ ≫ (π a₂) → g₁ ≫ e a₁ = g₂ ≫ e a₂ := by
  intro Z a₁ a₂ g₁ g₂ hg
  -- ⊢ g₁ ≫ e a₁ = g₂ ≫ e a₂
  -- The Stone-Cech-compactification `βZ` of `Z : CompHaus` is in `Stonean`
  let βZ := Z.presentation
  -- ⊢ g₁ ≫ e a₁ = g₂ ≫ e a₂
  let g₁' := F.preimage (presentation.π Z ≫ g₁ : F.obj βZ ⟶ F.obj (X a₁))
  -- ⊢ g₁ ≫ e a₁ = g₂ ≫ e a₂
  let g₂' := F.preimage (presentation.π Z ≫ g₂ : F.obj βZ ⟶ F.obj (X a₂))
  -- ⊢ g₁ ≫ e a₁ = g₂ ≫ e a₂
  -- Use that `βZ → Z` is an epi
  apply Epi.left_cancellation (f := presentation.π Z)
  -- ⊢ presentation.π Z ≫ g₁ ≫ e a₁ = presentation.π Z ≫ g₂ ≫ e a₂
  -- By definition `g₁' = presentationπ ≫ g₁` and `g₂' = presentationπ ≫ g₂`
  change g₁' ≫ e a₁ = g₂' ≫ e a₂
  -- ⊢ g₁' ≫ e a₁ = g₂' ≫ e a₂
  -- use the condition in `Stonean`
  apply h
  -- ⊢ g₁' ≫ π a₁ = g₂' ≫ π a₂
  change presentation.π Z ≫ g₁ ≫ π a₁ = presentation.π Z ≫ g₂ ≫ π a₂
  -- ⊢ presentation.π Z ≫ g₁ ≫ π a₁ = presentation.π Z ≫ g₂ ≫ π a₂
  simp [hg]
  -- 🎉 no goals

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
    -- ⊢ π a ≫ (fun {W} e h => toCompHaus.preimage (EffectiveEpiFamily.desc (fun x => …
    -- The `fac` on `CompHaus`
    have fac₁ :  F.map (π a ≫ _) = F.map (e a) :=
      EffectiveEpiFamily.fac (F.obj <| X ·) π e (lift_desc_condition π he) a
    replace fac₁ := Faithful.map_injective fac₁
    -- ⊢ π a ≫ (fun {W} e h => toCompHaus.preimage (EffectiveEpiFamily.desc (fun x => …
    exact fac₁
    -- 🎉 no goals
  uniq := by
    -- The `EffectiveEpiFamily F(X) F(π)` on `CompHaus`
    let fam : EffectiveEpiFamily (F.obj <| X ·) π :=
      CompHaus.effectiveEpiFamily_of_jointly_surjective (F.obj <| X ·) π surj
    intro W e he m hm
    -- ⊢ m = (fun {W} e h => toCompHaus.preimage (EffectiveEpiFamily.desc (fun x => F …
    have Fhm : ∀ (a : α), π a ≫ F.map m = e a
    -- ⊢ ∀ (a : α), π a ≫ F.map m = e a
    · intro a
      -- ⊢ π a ≫ F.map m = e a
      simp_all only [toCompHaus_map]
      -- 🎉 no goals
    have uniq₁ : F.map m = F.map _ :=
      EffectiveEpiFamily.uniq (F.obj <| X ·) π e (lift_desc_condition π he) (F.map m) Fhm
    replace uniq₁ := Faithful.map_injective uniq₁
    -- ⊢ m = (fun {W} e h => toCompHaus.preimage (EffectiveEpiFamily.desc (fun x => F …
    exact uniq₁
    -- 🎉 no goals

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
  -- ⊢ EffectiveEpiFamily X π → Epi (Sigma.desc π)
  · intro
    -- ⊢ Epi (Sigma.desc π)
    infer_instance
    -- 🎉 no goals
  tfae_have 1 → 2
  -- ⊢ EffectiveEpiFamily X π → Epi (Sigma.desc π)
  · intro
    -- ⊢ Epi (Sigma.desc π)
    infer_instance
    -- 🎉 no goals
  tfae_have 2 → 3
  -- ⊢ Epi (Sigma.desc π) → ∀ (b : CoeSort.coe B), ∃ a x, ↑(π a) x = b
  · intro e
    -- ⊢ ∀ (b : CoeSort.coe B), ∃ a x, ↑(π a) x = b
    rw [epi_iff_surjective] at e
    -- ⊢ ∀ (b : CoeSort.coe B), ∃ a x, ↑(π a) x = b
    intro b
    -- ⊢ ∃ a x, ↑(π a) x = b
    obtain ⟨t, rfl⟩ := e b
    -- ⊢ ∃ a x, ↑(π a) x = ↑(Sigma.desc π) t
    let q := (coproductIsoCoproduct X).inv t
    -- ⊢ ∃ a x, ↑(π a) x = ↑(Sigma.desc π) t
    refine ⟨q.1, q.2, ?_⟩
    -- ⊢ ↑(π q.fst) q.snd = ↑(Sigma.desc π) t
    rw [← (coproductIsoCoproduct X).inv_hom_id_apply t]
    -- ⊢ ↑(π q.fst) q.snd = ↑(Sigma.desc π) (↑(coproductIsoCoproduct X).1 (↑(coproduc …
    show _ = ((coproductIsoCoproduct X).hom ≫ Sigma.desc π) ((coproductIsoCoproduct X).inv t)
    -- ⊢ ↑(π q.fst) q.snd = ↑((coproductIsoCoproduct X).hom ≫ Sigma.desc π) (↑(coprod …
    suffices : (coproductIsoCoproduct X).hom ≫ Sigma.desc π = finiteCoproduct.desc X π
    -- ⊢ ↑(π q.fst) q.snd = ↑((coproductIsoCoproduct X).hom ≫ Sigma.desc π) (↑(coprod …
    · rw [this]
      -- ⊢ ↑(π q.fst) q.snd = ↑(finiteCoproduct.desc X π) (↑(coproductIsoCoproduct X).i …
      rfl
      -- 🎉 no goals
    apply Eq.symm
    -- ⊢ finiteCoproduct.desc X π = (coproductIsoCoproduct X).hom ≫ Sigma.desc π
    rw [← Iso.inv_comp_eq]
    -- ⊢ (coproductIsoCoproduct X).inv ≫ finiteCoproduct.desc X π = Sigma.desc π
    apply colimit.hom_ext
    -- ⊢ ∀ (j : Discrete α), colimit.ι (Discrete.functor X) j ≫ (coproductIsoCoproduc …
    rintro ⟨a⟩
    -- ⊢ colimit.ι (Discrete.functor X) { as := a } ≫ (coproductIsoCoproduct X).inv ≫ …
    simp only [Discrete.functor_obj, colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app,
      coproductIsoCoproduct, colimit.comp_coconePointUniqueUpToIso_inv_assoc]
    ext
    -- ⊢ ↑(NatTrans.app (finiteCoproduct.explicitCocone X).ι { as := a } ≫ finiteCopr …
    rfl
    -- 🎉 no goals
  tfae_have 3 → 1
  -- ⊢ (∀ (b : CoeSort.coe B), ∃ a x, ↑(π a) x = b) → EffectiveEpiFamily X π
  · apply effectiveEpiFamily_of_jointly_surjective
    -- 🎉 no goals
  tfae_finish
  -- 🎉 no goals

end JointlySurjective

section Coherent

open CompHaus Functor

theorem _root_.CategoryTheory.EffectiveEpiFamily.toCompHaus
    {α : Type} [Fintype α] {B : Stonean.{u}}
    {X : α → Stonean.{u}} {π : (a : α) → (X a ⟶ B)} (H : EffectiveEpiFamily X π) :
    EffectiveEpiFamily (toCompHaus.obj <| X ·) (toCompHaus.map <| π ·) := by
  refine' ((CompHaus.effectiveEpiFamily_tfae _ _).out 0 2).2 (fun b => _)
  -- ⊢ ∃ a x, ↑(Stonean.toCompHaus.map (π a)) x = b
  exact (((effectiveEpiFamily_tfae _ _).out 0 2).1 H : ∀ _, ∃ _, _) _
  -- 🎉 no goals

instance instPrecoherent: Precoherent Stonean.{u} := by
  constructor
  -- ⊢ ∀ {B₁ B₂ : Stonean} (f : B₂ ⟶ B₁) (α : Type) [inst : Fintype α] (X₁ : α → St …
  intro B₁ B₂ f α _ X₁ π₁ h₁
  -- ⊢ ∃ β x X₂ π₂, EffectiveEpiFamily X₂ π₂ ∧ ∃ i ι, ∀ (b : β), ι b ≫ π₁ (i b) = π …
  refine ⟨α, inferInstance, fun a => (pullback f (π₁ a)).presentation, fun a =>
    toCompHaus.preimage (presentation.π _ ≫ (pullback.fst _ _)), ?_, id, fun a =>
    toCompHaus.preimage (presentation.π _ ≫ (pullback.snd _ _ )), fun a => ?_⟩
  · refine ((effectiveEpiFamily_tfae _ _).out 0 2).2 (fun b => ?_)
    -- ⊢ ∃ a x, ↑(toCompHaus.preimage (presentation.π (CompHaus.pullback f (π₁ a)) ≫  …
    have h₁' := ((CompHaus.effectiveEpiFamily_tfae _ _).out 0 2).1 h₁.toCompHaus
    -- ⊢ ∃ a x, ↑(toCompHaus.preimage (presentation.π (CompHaus.pullback f (π₁ a)) ≫  …
    obtain ⟨a, x, h⟩ := h₁' (f b)
    -- ⊢ ∃ a x, ↑(toCompHaus.preimage (presentation.π (CompHaus.pullback f (π₁ a)) ≫  …
    obtain ⟨c, hc⟩ := (CompHaus.epi_iff_surjective _).1
      (presentation.epi_π (CompHaus.pullback f (π₁ a))) ⟨⟨b, x⟩, h.symm⟩
    refine ⟨a, c, ?_⟩
    -- ⊢ ↑(toCompHaus.preimage (presentation.π (CompHaus.pullback f (π₁ a)) ≫ CompHau …
    change toCompHaus.map (toCompHaus.preimage _) _ = _
    -- ⊢ ↑(toCompHaus.map (toCompHaus.preimage (presentation.π (CompHaus.pullback f ( …
    simp only [image_preimage, toCompHaus_obj, comp_apply, hc]
    -- ⊢ ↑(CompHaus.pullback.fst f (π₁ a)) { val := (b, x), property := (_ : ↑f b = ↑ …
    rfl
    -- 🎉 no goals
  · apply map_injective toCompHaus
    -- ⊢ toCompHaus.map ((fun a => toCompHaus.preimage (presentation.π (CompHaus.pull …
    simp only [map_comp, image_preimage, Category.assoc]
    -- ⊢ presentation.π (CompHaus.pullback f (π₁ a)) ≫ CompHaus.pullback.snd f (π₁ a) …
    congr 1
    -- ⊢ CompHaus.pullback.snd f (π₁ a) ≫ toCompHaus.map (π₁ (id a)) = CompHaus.pullb …
    ext ⟨⟨_, _⟩, h⟩
    -- ⊢ ↑(CompHaus.pullback.snd f (π₁ a) ≫ toCompHaus.map (π₁ (id a))) { val := (fst …
    exact h.symm
    -- 🎉 no goals

end Coherent

end Stonean
