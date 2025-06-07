/-
Copyright (c) 2023 Matias Heikkilä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matias Heikkilä
-/
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.StoneCech

/-!
# Completely regular topological spaces.

This file defines `CompletelyRegularSpace` and `T35Space`.

## Main definitions

* `CompletelyRegularSpace`: A completely regular space `X` is such that each closed set `K ⊆ X`
  and a point `x ∈ Kᶜ`, there is a continuous function `f` from `X` to the unit interval, so that
  `f x = 0` and `f k = 1` for all `k ∈ K`. A completely regular space is a regular space, and a
  normal space is a completely regular space.
* `T35Space`: A T₃.₅ space is a completely regular space that is also T₁. A T₃.₅ space is a T₃
  space and a T₄ space is a T₃.₅ space.

## Main results

### Completely regular spaces

* `CompletelyRegularSpace.regularSpace`: A completely regular space is a regular space.
* `NormalSpace.completelyRegularSpace`: A normal R0 space is a completely regular space.

### T₃.₅ spaces

* `T35Space.instT3Space`: A T₃.₅ space is a T₃ space.
* `T4Space.instT35Space`: A T₄ space is a T₃.₅ space.

## Implementation notes

The present definition `CompletelyRegularSpace` is a slight modification of the one given in
[russell1974]. There it's assumed that any point `x ∈ Kᶜ` is separated from the closed set `K` by a
continuous *real* valued function `f` (as opposed to `f` being unit-interval-valued). This can be
converted to the present definition by replacing a real-valued `f` by `h ∘ g ∘ f`, with
`g : x ↦ max(x, 0)` and `h : x ↦ min(x, 1)`. Some sources (e.g. [russell1974]) also assume that a
completely regular space is T₁. Here a completely regular space that is also T₁ is called a T₃.₅
space.

## References

* [Russell C. Walker, *The Stone-Čech Compactification*][russell1974]
-/

universe u v

noncomputable section

open Set Topology Filter unitInterval

variable {X : Type u} [TopologicalSpace X]

/-- A space is completely regular if points can be separated from closed sets via
  continuous functions to the unit interval. -/
@[mk_iff]
class CompletelyRegularSpace (X : Type u) [TopologicalSpace X] : Prop where
  completely_regular : ∀ (x : X), ∀ K : Set X, IsClosed K → x ∉ K →
    ∃ f : X → I, Continuous f ∧ f x = 0 ∧ EqOn f 1 K

instance CompletelyRegularSpace.instRegularSpace [CompletelyRegularSpace X] :
    RegularSpace X := by
  rw [regularSpace_iff]
  intro s a hs ha
  obtain ⟨f, cf, hf, hhf⟩ := CompletelyRegularSpace.completely_regular a s hs ha
  apply disjoint_of_map (f := f)
  apply Disjoint.mono (cf.tendsto_nhdsSet_nhds hhf) cf.continuousAt
  exact disjoint_nhds_nhds.mpr (hf.symm ▸ zero_ne_one).symm

instance NormalSpace.instCompletelyRegularSpace [NormalSpace X] [R0Space X] :
    CompletelyRegularSpace X := by
  rw [completelyRegularSpace_iff]
  intro x K hK hx
  have cx : IsClosed (closure {x}) := isClosed_closure
  have d : Disjoint (closure {x}) K := by
    rw [Set.disjoint_iff]
    intro a ⟨hax, haK⟩
    exact hx ((specializes_iff_mem_closure.mpr hax).symm.mem_closed hK haK)
  let ⟨⟨f, cf⟩, hfx, hfK, hficc⟩ := exists_continuous_zero_one_of_isClosed cx hK d
  let g : X → I := fun x => ⟨f x, hficc x⟩
  have cg : Continuous g := cf.subtype_mk hficc
  have hgx : g x = 0 := Subtype.ext (hfx (subset_closure (mem_singleton x)))
  have hgK : EqOn g 1 K := fun k hk => Subtype.ext (hfK hk)
  exact ⟨g, cg, hgx, hgK⟩

lemma Topology.IsInducing.completelyRegularSpace
    {Y : Type v} [TopologicalSpace Y] [CompletelyRegularSpace Y]
    {f : X → Y} (hf : IsInducing f) : CompletelyRegularSpace X where
  completely_regular x K hK hxK := by
    rw [hf.isClosed_iff] at hK
    obtain ⟨K, hK, rfl⟩ := hK
    rw [mem_preimage] at hxK
    obtain ⟨g, hcf, egfx, hgK⟩ := CompletelyRegularSpace.completely_regular _ _ hK hxK
    refine ⟨g ∘ f, hcf.comp hf.continuous, egfx, ?_⟩
    conv => arg 2; equals (1 : Y → ↥I) ∘ f => rfl
    exact hgK.comp_right <| mapsTo_preimage _ _

instance {p : X → Prop} [CompletelyRegularSpace X] : CompletelyRegularSpace (Subtype p) :=
  Topology.IsInducing.subtypeVal.completelyRegularSpace

/-- A T₃.₅ space is a completely regular space that is also T1. -/
@[mk_iff]
class T35Space (X : Type u) [TopologicalSpace X] : Prop extends T1Space X, CompletelyRegularSpace X

instance T35Space.instT3space [T35Space X] : T3Space X where

instance T4Space.instT35Space [T4Space X] : T35Space X where

lemma Topology.IsEmbedding.t35Space
    {Y : Type v} [TopologicalSpace Y] [T35Space Y]
    {f : X → Y} (hf : IsEmbedding f) : T35Space X :=
  @T35Space.mk _ _ hf.t1Space hf.isInducing.completelyRegularSpace

instance {p : X → Prop} [T35Space X] : T35Space (Subtype p) where

lemma separatesPoints_continuous_of_t35Space [T35Space X] :
    SeparatesPoints (Continuous : Set (X → ℝ)) := by
  intro x y x_ne_y
  obtain ⟨f, f_cont, f_zero, f_one⟩ :=
    CompletelyRegularSpace.completely_regular x {y} isClosed_singleton x_ne_y
  exact ⟨fun x ↦ f x, continuous_subtype_val.comp f_cont, by aesop⟩

@[deprecated (since := "2025-04-13")]
alias separatesPoints_continuous_of_completelyRegularSpace := separatesPoints_continuous_of_t35Space

lemma separatesPoints_continuous_of_t35Space_Icc [T35Space X] :
    SeparatesPoints (Continuous : Set (X → I)) := by
  intro x y x_ne_y
  obtain ⟨f, f_cont, f_zero, f_one⟩ :=
    CompletelyRegularSpace.completely_regular x {y} isClosed_singleton x_ne_y
  exact ⟨f, f_cont, by aesop⟩

@[deprecated (since := "2025-04-13")]
alias separatesPoints_continuous_of_completelyRegularSpace_Icc :=
  separatesPoints_continuous_of_t35Space_Icc

lemma injective_stoneCechUnit_of_t35Space [T35Space X] :
    Function.Injective (stoneCechUnit : X → StoneCech X) := by
  intros a b hab
  contrapose hab
  obtain ⟨f, fc, fab⟩ := separatesPoints_continuous_of_t35Space_Icc hab
  exact fun q ↦ fab (eq_if_stoneCechUnit_eq fc q)

@[deprecated (since := "2025-04-13")]
alias injective_stoneCechUnit_of_completelyRegularSpace := injective_stoneCechUnit_of_t35Space
