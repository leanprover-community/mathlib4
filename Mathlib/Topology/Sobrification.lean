/-
Copyright (c) 2026 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/
module

public import Mathlib.Topology.Order.Category.FrameAdjunction

/-! # Sobrification of a topological space

We construct the so-called "sobrification" or "sober reflection" of a topological space, which is
the universal continuous map from `X` into a sober (`T0Space` and `QuasiSober`) space.

## Main results

We construct the sobrification as the unit of the adjunction `Locale.adjunctionTopToLocalePT`, so
that the sober space extending `X` is `Locale.PT (Opens X)`. The main results are:
- The counit `localePointOfSpacePoint X: X → PT (Opens X)` is inducing (always), injective iff
`T0Space X`, and surjective iff `QuasiSober X`. As such, if `X` is sober then we have
`homeomorphPtOpens : X ≃ₜ PT (Opens X)`.
- `Locale.PT.equivIrreducibleCloseds` : the points of `Opens X` are equivalent to the irreducible
closed subsets of `X`.
- `continuousMapEquivFrameHom` : if `Y` is sober then every frame homomorphism `Opens Y → Opens X`
comes from a unique continuous map `X → Y`.
- `sobrificationEquiv` : for `Y` sober, precomposition with `localePointOfSpacePoint` defines an
equivalence `C(PT (Opens X), Y) ≃ C(X, Y)`.

## References

- https://ncatlab.org/nlab/show/sober+topological+space
-/

@[expose] public section

universe u

open Topology TopologicalSpace CategoryTheory

namespace Locale.PT

lemma localePointOfSpacePoint_injective_iff_t0Space (X : Type*) [TopologicalSpace X] :
    (localePointOfSpacePoint X).Injective ↔ T0Space X :=
  ⟨(t0Space_of_injective_of_continuous · (isInducing_localePointOfSpacePoint X).continuous),
    fun _ ↦ (isInducing_localePointOfSpacePoint X).injective⟩

lemma isEmbedding_localePointOfSpacePoint (X : Type*) [TopologicalSpace X] [T0Space X] :
    IsEmbedding (localePointOfSpacePoint X) where
  eq_induced := (isInducing_localePointOfSpacePoint X).eq_induced
  injective := (isInducing_localePointOfSpacePoint X).injective

private lemma map_sSup_not_eq {X : Type*} [TopologicalSpace X] (f : PT (Opens X)) :
    f (sSup {v | ¬ f v}) = ⊥ := by simp; grind

private lemma subset_sSup_not_iff {X : Type*} [TopologicalSpace X] {f : PT (Opens X)}
    {u : Set X} (hu : IsOpen u) : u ⊆ ↑(sSup {v : Opens X | ¬ f v}) ↔ ¬ f ⟨u, hu⟩ := by
  constructor
  · intro (h : ⟨u, hu⟩ ≤ sSup {v | ¬ f v})
    convert OrderHomClass.monotone f h
    rw [map_sSup_not_eq]
    rfl
  · exact le_sSup (s := {v | ¬ f v})

/-- Every point of the frame of opens of `X` induces an irreducible closed subset of `X`... -/
@[simps]
def toIrreducibleCloseds {X : Type*} [TopologicalSpace X] (f : PT (Opens X)) :
    IrreducibleCloseds X where
  carrier := (sSup {v : Opens X | ¬ f v}).compl
  isClosed' := (sSup {v : Opens X | ¬ f v}).compl.isClosed
  isIrreducible' := by
    constructor
    · rw [Opens.coe_compl, Set.nonempty_compl, Ne, Opens.coe_eq_univ]
      refine fun h ↦ bot_ne_top (α := Prop) ?_
      rw [← map_top f, ← map_sSup_not_eq f, h]
    · rw [Opens.coe_compl, isPreirreducible_compl_iff]
      intro u v hu hv
      suffices f ⟨u ∩ v, hu.inter hv⟩ ↔ f ⟨u, hu⟩ ∧ f ⟨v, hv⟩ by
        grind [subset_sSup_not_iff]
      convert! ← map_inf (α := Opens X) (β := Prop) f (⟨u, hu⟩ : Opens X) ⟨v, hv⟩
      ext; exact eq_iff_iff


/-- ... and conversely an irreducible subset defines a point of `Opens X`. -/
@[simps]
def _root_.IsIrreducible.toPTOpens {X : Type*} [TopologicalSpace X] {s : Set X}
    (h : IsIrreducible s) : PT (Opens X) where
  toFun u := (s ∩ u).Nonempty
  map_inf' u v := by
    simp_rw [Opens.coe_inf, inf_Prop_eq, eq_iff_iff]
    exact ⟨fun ⟨x, hx, hu, hv⟩ ↦ ⟨⟨x, hx, hu⟩, ⟨x, hx, hv⟩⟩,
      fun ⟨hu, hv⟩ ↦ h.2 u v u.isOpen v.isOpen hu hv⟩
  map_top' := by simpa using h.nonempty
  map_sSup' T := by simp [sSup_image, Set.inter_iUnion]

lemma toPTOpens_toCloseds {X : Type*} [TopologicalSpace X] (f : PT (Opens X)) :
    f.toIrreducibleCloseds.isIrreducible.toPTOpens = f := by
  ext u
  contrapose!
  simp only [coe_toIrreducibleCloseds, Opens.coe_compl, Set.compl_inter_nonempty_iff,
    IsIrreducible.toPTOpens_toFun, subset_sSup_not_iff u.isOpen]
  exact not_not

lemma toCloseds_injective (X : Type*) [TopologicalSpace X] :
    (PT.toIrreducibleCloseds (X := X)).Injective := by
  intro f g h
  rw [←toPTOpens_toCloseds f, ←toPTOpens_toCloseds g]
  congr

@[simp] lemma toIrreducibleCloseds_toPTOpens {X : Type*} [TopologicalSpace X] {s : Set X}
    (h : IsIrreducible s) :
    h.toPTOpens.toIrreducibleCloseds = ⟨closure s, h.closure, isClosed_closure⟩ := by
  ext x
  simp only [coe_toIrreducibleCloseds, IsIrreducible.toPTOpens_toFun, Opens.coe_compl,
    Opens.coe_sSup, Set.mem_ofPred_eq, Set.compl_iUnion, Set.mem_iInter, Set.mem_compl_iff,
    SetLike.mem_coe, not_imp_not, IrreducibleCloseds.coe_mk, mem_closure_iff]
  refine ⟨fun h u hu hx => ?_, fun h ⟨u, hu⟩ hx => ?_⟩
  · grind [Opens.coe_mk, h ⟨u, hu⟩ hx]
  · grind [Opens.coe_mk,h u hu hx]

/-- Points of `Opens X` are equivalent to irreducible closed subsets of `X`. -/
@[simps] def equivIrreducibleCloseds (X : Type*) [TopologicalSpace X] :
    PT (Opens X) ≃ IrreducibleCloseds X where
  toFun := toIrreducibleCloseds
  invFun | ⟨s, hirred, _⟩ => hirred.toPTOpens
  left_inv := toPTOpens_toCloseds
  right_inv := by
    intro ⟨s, hi, hc⟩
    simp

lemma toPT_singleton {X : Type*} [TopologicalSpace X] (x : X) :
    (isIrreducible_singleton (x := x)).toPTOpens = localePointOfSpacePoint X x := by
  ext u; simp

theorem localePointOfSpacePoint_surjective (X : Type*) [TopologicalSpace X] [QuasiSober X] :
    (localePointOfSpacePoint X).Surjective := by
  intro y
  refine ⟨y.toIrreducibleCloseds.isIrreducible.genericPoint,
    toCloseds_injective X <| SetLike.coe_injective ?_⟩
  simp [-coe_toIrreducibleCloseds, ← toPT_singleton, y.toIrreducibleCloseds.isClosed.closure_eq]

theorem localePointOfSpacePoint_surjective_iff_quasiSober (X : Type*) [TopologicalSpace X] :
    (localePointOfSpacePoint X).Surjective ↔ QuasiSober X := by
  refine ⟨fun h ↦ ⟨?_⟩, fun _ ↦ localePointOfSpacePoint_surjective X⟩
  intro s hs hs'
  obtain ⟨x, hx⟩ := h <| (equivIrreducibleCloseds X).symm ⟨s, hs, hs'⟩
  use x
  rwa [← toPT_singleton, Equiv.eq_symm_apply, equivIrreducibleCloseds_apply,
    toIrreducibleCloseds_toPTOpens, IrreducibleCloseds.ext_iff] at hx

lemma isHomeomorph_localePointOfSpacePoint (X : Type*) [TopologicalSpace X] [T0Space X]
    [QuasiSober X] : IsHomeomorph (localePointOfSpacePoint X) :=
  isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨isEmbedding_localePointOfSpacePoint X, localePointOfSpacePoint_surjective X⟩

/-- A sober space is homeomorphic to the space of points of its frame of opens. -/
noncomputable def homeomorphPtOpens (X : Type*) [TopologicalSpace X] [T0Space X] [QuasiSober X] :
    X ≃ₜ PT (Opens X) := (isHomeomorph_localePointOfSpacePoint X).homeomorph

end PT

end Locale

open Locale

/-- If `Y` is sober, every frame homomorphism `Opens Y → Opens X` comes from a unique continuous map
`X → Y`. -/
noncomputable def continuousMapEquivFrameHom (X Y : Type u) [TopologicalSpace X]
    [TopologicalSpace Y] [T0Space Y] [QuasiSober Y] : C(X, Y) ≃ FrameHom (Opens Y) (Opens X) :=
  (Homeomorph.refl X).continuousMapCongr (PT.homeomorphPtOpens Y) |>.trans <|
    continuousMapPTEquivFrameHomOpens X (Opens Y)

@[simp]
lemma continuousMapEquivFrameHom_apply {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [T0Space Y] [QuasiSober Y] (f : C(X, Y)) : continuousMapEquivFrameHom X Y f = Opens.comap f :=
  rfl

/-- For `Y` sober, continuous maps from the sober space `PT (Opens X)` to `Y` are equivalent to
continuous maps `X → Y`. -/
noncomputable def sobrificationEquiv (X Y : Type u) [TopologicalSpace X]
    [TopologicalSpace Y] [T0Space Y] [QuasiSober Y] : C(PT (Opens X), Y) ≃ C(X, Y) :=
  (continuousMapEquivFrameHom (PT (Opens X)) Y).trans <|
    ((OrderIso.refl (Opens Y)).frameHomCongr (orderIsoOpensPtOpens X).symm).trans <|
    (continuousMapEquivFrameHom X Y).symm

lemma sobrificationEquiv_apply {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] [T0Space Y] [QuasiSober Y] (f : C(PT (Opens X), Y)) :
    sobrificationEquiv X Y f =
      f.comp ⟨localePointOfSpacePoint X, (isInducing_localePointOfSpacePoint X).continuous⟩ := by
  simp_rw [sobrificationEquiv, Equiv.trans_apply, continuousMapEquivFrameHom_apply,
    OrderIso.frameHomCongr_apply, OrderIso.symm_refl, OrderIso.coe_refl, Equiv.symm_apply_eq]
  ext u x
  rfl

theorem sobrificationEquiv_apply_coe {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] [T0Space Y] [QuasiSober Y] (f : C(PT (Opens X), Y)) :
    ↑(sobrificationEquiv X Y f) = f ∘ localePointOfSpacePoint X := by
  rw [sobrificationEquiv_apply]
  rfl
