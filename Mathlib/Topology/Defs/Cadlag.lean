/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.LeftRightLim

/-! # cadlag functions

-/

@[expose] public section

open Filter TopologicalSpace Bornology
open scoped Topology ENNReal

variable {ι E : Type*} [TopologicalSpace ι]

/-- The predicate that a function is right continuous. -/
abbrev IsRightContinuous [TopologicalSpace E] [Preorder ι] (f : ι → E) :=
  ∀ a, ContinuousWithinAt f (Set.Ioi a) a

lemma Continuous.isRightContinuous [TopologicalSpace E] [Preorder ι]
    {f : ι → E} (hf : Continuous f) :
    IsRightContinuous f :=
  fun _ ↦ hf.continuousWithinAt

lemma IsRightContinuous.continuous_comp {F : Type*} [TopologicalSpace E]
    [TopologicalSpace F] [Preorder ι] {g : E → F}
    {f : ι → E} (hg : Continuous g) (hf : IsRightContinuous f) : IsRightContinuous (g ∘ f) :=
  fun x ↦ (hg.tendsto (f x)).comp (hf x)

lemma Function.IsRightContinuous.comp_continuous {F : Type*} [TopologicalSpace E]
    [TopologicalSpace F] [Preorder ι] {g : F → ι} [Preorder F]
    {f : ι → E} (hg : Continuous g) (hf : IsRightContinuous f)
    (hg' : StrictMono g) : IsRightContinuous (f ∘ g) := by
  intro x
  apply (hf (g x)).comp hg.continuousWithinAt
  intro y hy
  grind [StrictMono]

@[simp]
lemma isRightContinuous_const [TopologicalSpace E] [Preorder ι] (c : E) :
    IsRightContinuous (fun _ ↦ c : ι → E) :=
  continuous_const.isRightContinuous

@[to_additive (attr := to_fun)]
lemma IsRightContinuous.mul [TopologicalSpace E] [Preorder ι] [Mul E] [ContinuousMul E]
    {f g : ι → E} (hf : IsRightContinuous f) (hg : IsRightContinuous g) :
    IsRightContinuous (f * g) :=
  fun x ↦ (hf x).mul (hg x)

@[to_additive (attr := to_fun) sub]
lemma IsRightContinuous.div' [TopologicalSpace E] [Preorder ι] [Div E] [ContinuousDiv E]
    {f g : ι → E} (hf : IsRightContinuous f) (hg : IsRightContinuous g) :
    IsRightContinuous (f / g) :=
  fun x ↦ (hf x).div' (hg x)

@[to_fun]
lemma IsRightContinuous.div [Preorder ι] [GroupWithZero E] [TopologicalSpace E]
    [ContinuousInv₀ E] [ContinuousMul E] {f g : ι → E}
    (hf : IsRightContinuous f) (hg : IsRightContinuous g) (h : ∀ x, g x ≠ 0) :
    IsRightContinuous (f / g) :=
  fun x ↦ (hf x).div (hg x) (h x)

/-- A function is cadlag if it is right-continuous and has left limits. -/
structure IsCadlag [TopologicalSpace E] [Preorder ι] (f : ι → E) : Prop where
  right_continuous : IsRightContinuous f
  left_limit : ∀ x, ∃ l, Tendsto f (𝓝[<] x) (𝓝 l)

lemma Continuous.isCadlag [TopologicalSpace E] [Preorder ι] {f : ι → E} (hf : Continuous f) :
    IsCadlag f where
  right_continuous := hf.isRightContinuous
  left_limit x := ⟨f x, hf.continuousAt.continuousWithinAt⟩

@[simp]
lemma isCadlag_const [TopologicalSpace E] [Preorder ι] (c : E) : IsCadlag (fun _ ↦ c : ι → E) :=
  continuous_const.isCadlag

@[to_additive (attr := to_fun)]
lemma IsCadlag.mul {E : Type*} [Mul E] [TopologicalSpace E] [ContinuousMul E] [Preorder ι]
    {f g : ι → E} (hf : IsCadlag f) (hg : IsCadlag g) :
    IsCadlag (f * g) := by
  refine ⟨fun i ↦ ContinuousWithinAt.mul (hf.1 i) (hg.1 i), fun i ↦ ?_⟩
  obtain ⟨l, hl⟩ := hf.2 i
  obtain ⟨m, hm⟩ := hg.2 i
  exact ⟨l * m, hl.mul hm⟩

@[to_fun]
lemma IsCadlag.const_smul {E : Type*} [SMul ℝ E] [TopologicalSpace E] [ContinuousSMul ℝ E]
    [Preorder ι] {f : ι → E} (hf : IsCadlag f) (r : ℝ) :
    IsCadlag (r • f) := by
  refine ⟨fun i ↦ ContinuousWithinAt.const_smul (hf.1 i) r, fun i ↦ ?_⟩
  obtain ⟨l, hl⟩ := hf.2 i
  exact ⟨r • l, hl.const_smul r⟩

@[to_additive (attr := to_fun)]
lemma IsCadlag.inv {E : Type*} [Group E] [TopologicalSpace E] [ContinuousInv E] [Preorder ι]
    {f : ι → E} (hf : IsCadlag f) :
    IsCadlag (f⁻¹) := by
  refine ⟨fun i ↦ ContinuousWithinAt.inv (hf.1 i), fun i ↦ ?_⟩
  obtain ⟨l, hl⟩ := hf.2 i
  exact ⟨l⁻¹, hl.inv⟩

@[to_fun]
lemma IsCadlag.sub {E : Type*} [Sub E] [TopologicalSpace E] [ContinuousSub E]
    [Preorder ι] {f g : ι → E} (hf : IsCadlag f) (hg : IsCadlag g) :
    IsCadlag (f - g) := by
  refine ⟨fun i ↦ ContinuousWithinAt.sub (hf.1 i) (hg.1 i), fun i ↦ ?_⟩
  obtain ⟨l, hl⟩ := hf.2 i
  obtain ⟨m, hm⟩ := hg.2 i
  exact ⟨l - m, hl.sub hm⟩

lemma IsCadlag.continuous_comp {κ E F : Type*} [TopologicalSpace κ] [TopologicalSpace E]
    [TopologicalSpace F] [Preorder κ] {g : E → F} {f : κ → E}
    (hg : Continuous g) (hf : IsCadlag f) : IsCadlag (g ∘ f) where
  right_continuous := IsRightContinuous.continuous_comp hg hf.right_continuous
  left_limit i := by
    obtain ⟨l, hl⟩ := hf.left_limit i
    exact ⟨g l, (hg.tendsto l).comp hl⟩

lemma IsCadlag.norm {κ F : Type*} [TopologicalSpace κ] [NormedAddCommGroup F] [Preorder κ]
    {f : κ → F} (hf : IsCadlag f) : IsCadlag (fun i ↦ ‖f i‖) :=
  hf.continuous_comp continuous_norm

lemma IsCadlag.norm_sq {κ F : Type*} [TopologicalSpace κ] [NormedAddCommGroup F] [Preorder κ]
    {f : κ → F} (hf : IsCadlag f) : IsCadlag (fun i ↦ ‖f i‖ ^ 2) :=
  hf.norm.continuous_comp (continuous_pow 2)

/-- A càdlàg function is locally bounded. -/
lemma isLocallyBounded_of_isCadlag {E : Type*} [LinearOrder ι] [PseudoMetricSpace E]
    {f : ι → E} (hf : IsCadlag f) (x : ι) : ∃ t ∈ 𝓝 x, IsBounded (f '' t) := by
  obtain ⟨l, hl⟩ := hf.2 x
  obtain ⟨U, ⟨⟨A, ⟨hp, ⟨W, hW⟩⟩⟩, hU⟩⟩ := Metric.exists_isBounded_image_of_tendsto hl
  obtain ⟨V, ⟨⟨B, ⟨hq, ⟨R, hR⟩⟩⟩, hV⟩⟩ := Metric.exists_isBounded_image_of_tendsto (hf.1 x).tendsto
  refine ⟨A ∩ B, inter_mem hp hq, ?_⟩
  apply IsBounded.subset ((hU.union hV).union (isBounded_singleton : Bornology.IsBounded ({f x})))
  rintro _ ⟨y, ⟨hyL, hyR⟩ , rfl⟩
  rcases lt_trichotomy y x with (hlt | heq | hgt)
  · have : y ∈ U := hW.2 ▸ ⟨hyL, hW.1 hlt⟩
    grind
  · grind
  · have : y ∈ V := hR.2 ▸ ⟨hyR, hR.1 hgt⟩
    grind

/-- A càdlàg function maps compact sets to bounded sets. -/
lemma isBounded_image_of_isCadlag_of_isCompact {E : Type*} [LinearOrder ι] [PseudoMetricSpace E]
    {f : ι → E} (hf : IsCadlag f) {s : Set ι} (hs : IsCompact s) :
    IsBounded (f '' s) :=
  isBounded_image_of_isLocallyBounded_of_isCompact hs (isLocallyBounded_of_isCadlag hf)
