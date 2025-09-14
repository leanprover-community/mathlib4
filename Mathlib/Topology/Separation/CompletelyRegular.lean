/-
Copyright (c) 2023 Matias Heikkilä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matias Heikkilä
-/
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Compactification.StoneCech
import Mathlib.Topology.Order.Lattice
import Mathlib.Analysis.Real.Cardinality

/-!
# Completely regular topological spaces.

This file defines `CompletelyRegularSpace` and `T35Space`.

## Main definitions

* `CompletelyRegularSpace`: A completely regular space `X` is such that each closed set `K ⊆ X`
  and a point `x ∈ Kᶜ`, there is a continuous function `f` from `X` to the unit interval, so that
  `f x = 0` and `f k = 1` for all `k ∈ K`. A completely regular space is a regular space, and a
  normal space is a completely regular space.
* `T35Space`: A T₃.₅ space is a completely regular space that is also T₀. A T₃.₅ space is a T₃
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
continuous *real*-valued function `f` (as opposed to `f` being unit-interval-valued). This can be
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

lemma completelyRegularSpace_iff_isOpen : CompletelyRegularSpace X ↔
    ∀ (x : X), ∀ K : Set X, IsOpen K → x ∈ K →
      ∃ f : X → I, Continuous f ∧ f x = 0 ∧ EqOn f 1 Kᶜ := by
  conv_lhs => tactic =>
    simp_rw +singlePass [completelyRegularSpace_iff, compl_surjective.forall, isClosed_compl_iff,
      mem_compl_iff, not_not]

lemma CompletelyRegularSpace.completely_regular_isOpen [CompletelyRegularSpace X] :
    ∀ (x : X), ∀ K : Set X, IsOpen K → x ∈ K →
      ∃ f : X → I, Continuous f ∧ f x = 0 ∧ EqOn f 1 Kᶜ :=
  completelyRegularSpace_iff_isOpen.mp inferInstance

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

lemma completelyRegularSpace_induced
    {X Y : Type*} {t : TopologicalSpace Y} (ht : @CompletelyRegularSpace Y t)
    (f : X → Y) : @CompletelyRegularSpace X (t.induced f) :=
  @IsInducing.completelyRegularSpace _ (t.induced f) _ t _ _ (IsInducing.induced f)

lemma completelyRegularSpace_iInf {ι X : Type*} {t : ι → TopologicalSpace X}
    (ht : ∀ i, @CompletelyRegularSpace X (t i)) : @CompletelyRegularSpace X (⨅ i, t i) := by
  letI := (⨅ i, t i) -- register this as default topological space to reduce `@`s
  rw [completelyRegularSpace_iff_isOpen]
  intro x K hK hxK
  simp_rw [← hK.mem_nhds_iff, nhds_iInf, mem_iInf, exists_finite_iff_finset,
    Finset.coe_sort_coe] at hxK; clear hK
  obtain ⟨I', V, hV, rfl⟩ := hxK
  simp only [mem_nhds_iff] at hV
  choose U hUV hU hxU using hV
  replace hU := fun (i : ↥I') =>
    @CompletelyRegularSpace.completely_regular_isOpen _ (t i) (ht i) x (U i) (hU i) (hxU i)
  clear hxU
  choose fs hfs hxfs hfsU using hU
  use I'.attach.sup fs
  constructorm* _ ∧ _
  · solve_by_elim [Continuous.finset_sup, continuous_iInf_dom]
  · simpa [show (0 : ↥I) = ⊥ from rfl] using hxfs
  · simp only [EqOn, Pi.one_apply, show (1 : ↥I) = ⊤ from rfl] at hfsU ⊢
    conv => equals ∀ x i, x ∈ (V i)ᶜ → ∃ b, fs b x = ⊤ => simp [Finset.sup_eq_top_iff]
    intro x i hxi
    specialize hfsU i (by tauto_set)
    exists i

lemma completelyRegularSpace_inf {X : Type*} {t₁ t₂ : TopologicalSpace X}
    (ht₁ : @CompletelyRegularSpace X t₁) (ht₂ : @CompletelyRegularSpace X t₂) :
    @CompletelyRegularSpace X (t₁ ⊓ t₂) := by
  rw [inf_eq_iInf]; apply completelyRegularSpace_iInf; simp [*]

instance {ι : Type*} {X : ι → Type*} [t : Π (i : ι), TopologicalSpace (X i)]
    [ht : Π (i : ι), CompletelyRegularSpace (X i)] : CompletelyRegularSpace (Π i, X i) :=
  completelyRegularSpace_iInf (fun i => completelyRegularSpace_induced (ht i) _)

instance {X Y : Type*} [tX : TopologicalSpace X] [tY : TopologicalSpace Y]
    [htX : CompletelyRegularSpace X] [htY : CompletelyRegularSpace Y] :
    CompletelyRegularSpace (X × Y) :=
  completelyRegularSpace_inf
    (completelyRegularSpace_induced htX _) ((completelyRegularSpace_induced htY _))

lemma isInducing_stoneCechUnit [CompletelyRegularSpace X] :
    IsInducing (stoneCechUnit : X → StoneCech X) := by
  rw [isInducing_iff_nhds]
  intro x
  apply le_antisymm
  · rw [← map_le_iff_le_comap]; exact continuous_stoneCechUnit.continuousAt
  · simp_rw [le_nhds_iff, ((nhds_basis_opens _).comap _).mem_iff, and_assoc]
    intro U hxU hU
    obtain ⟨f, hf, efx, hfU⟩ :=
      CompletelyRegularSpace.completely_regular_isOpen x U hU hxU
    conv at hfU => equals Uᶜ ⊆ f ⁻¹' {1} => simp [EqOn, subset_def]
    rw [← compl_subset_comm, ← preimage_compl, ← stoneCechExtend_extends hf, preimage_comp] at hfU
    refine ⟨stoneCechExtend hf ⁻¹' {1}ᶜ, ?_,
      isOpen_compl_singleton.preimage (continuous_stoneCechExtend hf), hfU⟩
    rw [mem_preimage, stoneCechExtend_stoneCechUnit, efx, mem_compl_iff, mem_singleton_iff]
    norm_num

lemma isDenseInducing_stoneCechUnit [CompletelyRegularSpace X] :
    IsDenseInducing (stoneCechUnit : X → StoneCech X) where
  toIsInducing := isInducing_stoneCechUnit
  dense := denseRange_stoneCechUnit

lemma completelyRegularSpace_iff_isInducing_stoneCechUnit :
    CompletelyRegularSpace X ↔ IsInducing (stoneCechUnit : X → StoneCech X) where
  mp _ := isInducing_stoneCechUnit
  mpr hs := hs.completelyRegularSpace

open TopologicalSpace Cardinal in
theorem CompletelyRegularSpace.isTopologicalBasis_clopens_of_cardinalMk_lt_continuum
    [CompletelyRegularSpace X] (hX : Cardinal.mk X < continuum) :
    IsTopologicalBasis {s : Set X | IsClopen s} := by
  refine isTopologicalBasis_of_isOpen_of_nhds (fun x s ↦ IsClopen.isOpen s) (fun x s hxs hs ↦ ?_)
  choose f hf using completely_regular_isOpen x s hs hxs
  obtain ⟨hfc, hf₀, hf₁⟩ := hf
  let R := Set.range f
  have hR : lift.{u, 0} (Cardinal.mk R) < lift.{0, u} continuum := by
    simpa [R] using mk_range_le_lift.trans_lt (lift_strictMono hX)
  rw [lift_continuum, ← lift_continuum.{u, 0}, lift_lt, ← mk_Icc_real zero_lt_one, ← unitInterval]
    at hR
  obtain ⟨r, hr⟩ : ∃ r : I, r ∈ Rᶜ := compl_nonempty_of_mk_lt_mk hR
  have hr' : ∀ (x : X), f x ≠ r := by simpa [R] using hr
  have hrclopen : f ⁻¹' Iio r = f ⁻¹' Iic r := by
    ext; simp [le_iff_lt_or_eq, hr']
  refine ⟨f ⁻¹' Iio r, ⟨hrclopen ▸ isClosed_Iic.preimage hfc, isOpen_Iio.preimage hfc⟩, ?_, ?_⟩
  · simp [hf₀, hrclopen]
  · refine preimage_subset_iff.mpr (fun x ↦ ?_)
    contrapose!; intro hxs
    simpa [hf₁ hxs] using le_one'

/-- A T₃.₅ space is a completely regular space that is also T₀. -/
@[mk_iff]
class T35Space (X : Type u) [TopologicalSpace X] : Prop extends T0Space X, CompletelyRegularSpace X

instance T35Space.instT3space [T35Space X] : T3Space X where

instance T4Space.instT35Space [T4Space X] : T35Space X where

lemma Topology.IsEmbedding.t35Space
    {Y : Type v} [TopologicalSpace Y] [T35Space Y]
    {f : X → Y} (hf : IsEmbedding f) : T35Space X :=
  @T35Space.mk _ _ hf.t0Space hf.isInducing.completelyRegularSpace

instance {p : X → Prop} [T35Space X] : T35Space (Subtype p) where

instance {ι : Type*} {X : ι → Type*} [t : Π (i : ι), TopologicalSpace (X i)]
    [ht : Π (i : ι), T35Space (X i)] : T35Space (Π i, X i) where

instance {X Y : Type*} [tX : TopologicalSpace X] [tY : TopologicalSpace Y]
    [htX : T35Space X] [htY : T35Space Y] : T35Space (X × Y) where

lemma separatesPoints_continuous_of_t35Space [T35Space X] :
    SeparatesPoints {f : X → ℝ | Continuous f} := by
  intro x y x_ne_y
  obtain ⟨f, f_cont, f_zero, f_one⟩ :=
    CompletelyRegularSpace.completely_regular x {y} isClosed_singleton x_ne_y
  exact ⟨fun x ↦ f x, continuous_subtype_val.comp f_cont, by simp_all⟩

@[deprecated (since := "2025-04-13")]
alias separatesPoints_continuous_of_completelyRegularSpace := separatesPoints_continuous_of_t35Space

lemma separatesPoints_continuous_of_t35Space_Icc [T35Space X] :
    SeparatesPoints {f : X → I | Continuous f} := by
  intro x y x_ne_y
  obtain ⟨f, f_cont, f_zero, f_one⟩ :=
    CompletelyRegularSpace.completely_regular x {y} isClosed_singleton x_ne_y
  exact ⟨f, f_cont, by simp_all⟩

@[deprecated (since := "2025-04-13")]
alias separatesPoints_continuous_of_completelyRegularSpace_Icc :=
  separatesPoints_continuous_of_t35Space_Icc

lemma injective_stoneCechUnit_of_t35Space [T35Space X] :
    Function.Injective (stoneCechUnit : X → StoneCech X) := by
  intro a b hab
  contrapose hab
  obtain ⟨f, fc, fab⟩ := separatesPoints_continuous_of_t35Space_Icc hab
  exact fun q ↦ fab (eq_if_stoneCechUnit_eq fc q)

@[deprecated (since := "2025-04-13")]
alias injective_stoneCechUnit_of_completelyRegularSpace := injective_stoneCechUnit_of_t35Space

lemma isEmbedding_stoneCechUnit [T35Space X] :
    IsEmbedding (stoneCechUnit : X → StoneCech X) where
  toIsInducing := isInducing_stoneCechUnit
  injective := injective_stoneCechUnit_of_t35Space

lemma isDenseEmbedding_stoneCechUnit [T35Space X] :
    IsDenseEmbedding (stoneCechUnit : X → StoneCech X) where
  toIsDenseInducing := isDenseInducing_stoneCechUnit
  injective := injective_stoneCechUnit_of_t35Space

lemma t35Space_iff_isEmbedding_stoneCechUnit :
    T35Space X ↔ IsEmbedding (stoneCechUnit : X → StoneCech X) where
  mp _ := isEmbedding_stoneCechUnit
  mpr hs := hs.t35Space
