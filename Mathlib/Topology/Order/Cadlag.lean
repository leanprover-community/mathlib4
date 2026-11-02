/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Nick Kuhn, Yongxi Lin, Rohit Manokaran, Etienne Marion, Kexing Ying
-/
module

public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Topology.Order.LeftRightLim

/-! # Càdlàg functions

This file defines *càdlàg functions*, i.e. right-continuous functions with left limits. These
are for instance a common hypothesis made on stochastic processes.

Using the `to_dual` machinery we also define *càglàd functions* (left-continuous with right limits).

-/

@[expose] public section

open Filter TopologicalSpace Bornology
open scoped Topology ENNReal

variable {X Y : Type*} [TopologicalSpace X] {f g : X → Y}

section Basic

variable [Preorder X] [TopologicalSpace Y]

/- TODO: Cannot tag this with `fun_prop` because it fails when tagging a lemma
because of `to_dual`. -/
/-- A function `f` is *right-continuous* if for any `a`, `f x → f a` when `x → a` and `x > a`. -/
@[to_dual /-- A function `f` is *left-continuous* if for any `a`, `f x → f a` when `x → a`
and `x < a`. -/]
def IsRightContinuous (f : X → Y) :=
  ∀ a, ContinuousWithinAt f (Set.Ioi a) a

@[to_dual]
lemma Continuous.isRightContinuous (hf : Continuous f) :
    IsRightContinuous f :=
  fun _ ↦ hf.continuousWithinAt

@[to_dual (attr := to_fun)]
lemma IsRightContinuous.continuous_comp {Z : Type*} [TopologicalSpace Z] {g : Y → Z}
    (hf : IsRightContinuous f) (hg : Continuous g) :
    IsRightContinuous (g ∘ f) :=
  fun x ↦ (hg.tendsto (f x)).comp (hf x)

@[to_dual]
lemma IsRightContinuous.continuous_comp₂ {Z T : Type*} [TopologicalSpace Z] [TopologicalSpace T]
    {g : X → Z} {φ : Y → Z → T} (hf : IsRightContinuous f) (hg : IsRightContinuous g)
    (hφ : Continuous φ.uncurry) :
    IsRightContinuous (fun x ↦ φ (f x) (g x)) :=
  fun x ↦ (hφ.tendsto (f x, g x)).comp ((hf x).prodMk_nhds (hg x))

@[to_dual (attr := simp)]
lemma IsRightContinuous.const {c : Y} :
    IsRightContinuous (fun _ ↦ c : X → Y) :=
  continuous_const.isRightContinuous

@[to_additive (attr := to_fun (attr := to_dual))]
lemma IsRightContinuous.mul [Mul Y] [ContinuousMul Y]
    (hf : IsRightContinuous f) (hg : IsRightContinuous g) :
    IsRightContinuous (f * g) :=
  hf.continuous_comp₂ hg continuous_mul

@[to_additive (attr := to_fun (attr := to_dual)) sub]
lemma IsRightContinuous.div' [Div Y] [ContinuousDiv Y]
    (hf : IsRightContinuous f) (hg : IsRightContinuous g) :
    IsRightContinuous (f / g) :=
  hf.continuous_comp₂ hg continuous_div'

@[to_fun (attr := to_dual)]
lemma IsRightContinuous.div [GroupWithZero Y] [ContinuousInv₀ Y] [ContinuousMul Y]
    (hf : IsRightContinuous f) (hg : IsRightContinuous g) (h : ∀ x, g x ≠ 0) :
    IsRightContinuous (f / g) :=
  fun x ↦ (hf x).div (hg x) (h x)

@[to_additive (attr := to_fun (attr := to_dual))]
lemma IsRightContinuous.inv [Inv Y] [ContinuousInv Y] (hf : IsRightContinuous f) :
    IsRightContinuous (f⁻¹) :=
  hf.continuous_comp continuous_inv

@[to_fun (attr := to_dual)]
lemma IsRightContinuous.inv₀ [Zero Y] [Inv Y] [ContinuousInv₀ Y]
    (hf : IsRightContinuous f) (h : ∀ x, f x ≠ 0) :
    IsRightContinuous (f⁻¹) :=
  fun x ↦ (hf x).inv₀ (h x)

@[to_fun (attr := to_dual (attr := to_additive))]
lemma IsRightContinuous.const_smul {R : Type*} [SMul R Y] [ContinuousConstSMul R Y] (c : R)
    (hf : IsRightContinuous f) :
    IsRightContinuous (c • f) :=
  hf.continuous_comp (continuous_const_smul c)

/-- A function is *càglàd* if it is left-continuous and has right limits. -/
structure IsCaglad (f : X → Y) : Prop where
  isLeftContinuous : IsLeftContinuous f
  tendsto_nhdsGT : ∀ x, ∃ l, Tendsto f (𝓝[>] x) (𝓝 l)

/-- A function is *càdlàg* if it is right-continuous and has left limits. -/
@[to_dual existing]
structure IsCadlag (f : X → Y) : Prop where
  isRightContinuous : IsRightContinuous f
  tendsto_nhdsLT : ∀ x, ∃ l, Tendsto f (𝓝[<] x) (𝓝 l)

@[to_dual]
lemma Continuous.isCadlag (hf : Continuous f) :
    IsCadlag f where
  isRightContinuous := hf.isRightContinuous
  tendsto_nhdsLT x := ⟨f x, hf.continuousAt.continuousWithinAt⟩

@[to_dual (attr := simp)]
lemma IsCadlag.const {c : Y} : IsCadlag (fun _ ↦ c : X → Y) :=
  continuous_const.isCadlag

@[to_dual (attr := to_fun)]
lemma IsCadlag.continuous_comp {Z : Type*} [TopologicalSpace Z] {g : Y → Z}
    (hf : IsCadlag f) (hg : Continuous g) :
    IsCadlag (g ∘ f) where
  isRightContinuous := hf.isRightContinuous.continuous_comp hg
  tendsto_nhdsLT x := by
    obtain ⟨l, hl⟩ := hf.tendsto_nhdsLT x
    exact ⟨g l, (hg.tendsto l).comp hl⟩

@[to_dual]
lemma IsCadlag.continuous_comp₂ {Z T : Type*} [TopologicalSpace Z] [TopologicalSpace T]
    {g : X → Z} {φ : Y → Z → T} (hf : IsCadlag f) (hg : IsCadlag g)
    (hφ : Continuous φ.uncurry) :
    IsCadlag (fun x ↦ φ (f x) (g x)) where
  isRightContinuous := hf.isRightContinuous.continuous_comp₂ hg.isRightContinuous hφ
  tendsto_nhdsLT x := by
    obtain ⟨l1, hl1⟩ := hf.tendsto_nhdsLT x
    obtain ⟨l2, hl2⟩ := hg.tendsto_nhdsLT x
    exact ⟨φ l1 l2, (hφ.tendsto (l1, l2)).comp (hl1.prodMk_nhds hl2)⟩

@[to_additive (attr := to_fun (attr := to_dual))]
lemma IsCadlag.mul [Mul Y] [ContinuousMul Y] (hf : IsCadlag f) (hg : IsCadlag g) :
    IsCadlag (f * g) :=
  hf.continuous_comp₂ hg continuous_mul

@[to_additive (attr := to_fun (attr := to_dual)) sub]
lemma IsCadlag.div' [Div Y] [ContinuousDiv Y] (hf : IsCadlag f) (hg : IsCadlag g) :
    IsCadlag (f / g) :=
  hf.continuous_comp₂ hg continuous_div'

@[to_fun (attr := to_dual (attr := to_additive))]
lemma IsCadlag.const_smul {R : Type*} [SMul R Y] [ContinuousConstSMul R Y] (c : R)
    (hf : IsCadlag f) :
    IsCadlag (c • f) :=
  hf.continuous_comp (continuous_const_smul c)

end Basic

section LinearOrder

variable [LinearOrder X] [TopologicalSpace Y]

lemma IsCaglad.tendsto_nhdsGT_rightLim [OrderTopology X] (hf : IsCaglad f) (x : X) :
    Tendsto f (𝓝[>] x) (𝓝 (f.rightLim x)) :=
  tendsto_rightLim_of_tendsto (hf.tendsto_nhdsGT x)

-- TODO: tag `leftLim` with `to_dual` to use `to_dual` here.
lemma IsCadlag.tendsto_nhdsLT_leftLim [OrderTopology X] (hf : IsCadlag f) (x : X) :
    Tendsto f (𝓝[<] x) (𝓝 (f.leftLim x)) :=
  tendsto_leftLim_of_tendsto (hf.tendsto_nhdsLT x)

end LinearOrder

section PseudoMetricSpace

variable [LinearOrder X] [PseudoMetricSpace Y]

/-- A càdlàg function is locally bounded. -/
@[to_dual /-- A càglàd function is locally bounded. -/]
lemma IsCadlag.isLocallyBounded (hf : IsCadlag f) (x : X) : ∃ t ∈ 𝓝 x, IsBounded (f '' t) := by
  obtain ⟨l, hl⟩ := hf.2 x
  obtain ⟨-, ⟨⟨A, ⟨hA, ⟨W, hW, rfl⟩⟩⟩, hAW⟩⟩ := Metric.exists_isBounded_image_of_tendsto hl
  obtain ⟨-, ⟨⟨B, ⟨hB, ⟨R, hR, rfl⟩⟩⟩, hBR⟩⟩ :=
    Metric.exists_isBounded_image_of_tendsto (hf.1 x).tendsto
  refine ⟨A ∩ B, inter_mem hA hB, ?_⟩
  apply ((hAW.union hBR).union (isBounded_singleton (x := f x))).subset
  rintro _ ⟨y, ⟨hyL, hyR⟩ , rfl⟩
  rcases lt_trichotomy y x with (hlt | heq | hgt)
  · grind [hW hlt]
  · grind
  · grind [hR hgt]

/-- A càdlàg function maps compact sets to bounded sets. -/
@[to_dual /-- A càglàd function maps compact sets to bounded sets. -/]
lemma isBounded_image_of_isCadlag_of_isCompact (hf : IsCadlag f) {s : Set X} (hs : IsCompact s) :
    IsBounded (f '' s) :=
  isBounded_image_of_isLocallyBounded_of_isCompact hs hf.isLocallyBounded

end PseudoMetricSpace
