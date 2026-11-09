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

open Filter TopologicalSpace Bornology Set
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

section IsRightContinuousOn

variable {s t : Set X}

/-- A function `f` is *right-continuous on* a set `s` if for any `a ∈ s`, `f x → f a` when
`x → a` with `x ∈ s` and `x > a`. -/
@[to_dual /-- A function `f` is *left-continuous on* a set `s` if for any `a ∈ s`, `f x → f a`
when `x → a` with `x ∈ s` and `x < a`. -/]
def IsRightContinuousOn (f : X → Y) (s : Set X) : Prop :=
  ∀ a ∈ s, ContinuousWithinAt f (s ∩ Ioi a) a

@[to_dual]
lemma IsRightContinuousOn.continuousWithinAt {a : X} (hf : IsRightContinuousOn f s) (ha : a ∈ s) :
    ContinuousWithinAt f (s ∩ Ioi a) a :=
  hf a ha

@[to_dual (attr := simp)]
lemma isRightContinuousOn_univ : IsRightContinuousOn f univ ↔ IsRightContinuous f := by
  simp [IsRightContinuousOn, IsRightContinuous]

@[to_dual]
lemma IsRightContinuousOn.mono (hf : IsRightContinuousOn f s) (h : t ⊆ s) :
    IsRightContinuousOn f t :=
  fun a ha ↦ (hf a (h ha)).mono (inter_subset_inter_left _ h)

@[to_dual]
lemma IsRightContinuous.isRightContinuousOn (hf : IsRightContinuous f) :
    IsRightContinuousOn f s :=
  fun a _ ↦ (hf a).mono inter_subset_right

@[to_dual]
lemma ContinuousOn.isRightContinuousOn (hf : ContinuousOn f s) : IsRightContinuousOn f s :=
  fun a ha ↦ (hf a ha).mono inter_subset_left

@[to_dual (attr := simp)]
lemma isRightContinuousOn_empty (f : X → Y) : IsRightContinuousOn f ∅ :=
  fun _ ↦ False.elim

@[to_dual (attr := simp)]
lemma isRightContinuousOn_singleton (f : X → Y) (a : X) : IsRightContinuousOn f {a} :=
  (continuousOn_singleton f a).isRightContinuousOn

@[to_dual]
lemma IsOpen.isRightContinuousOn_iff (hs : IsOpen s) :
    IsRightContinuousOn f s ↔ ∀ a ∈ s, ContinuousWithinAt f (Ioi a) a :=
  forall₂_congr fun _ ha ↦ by rw [inter_comm, continuousWithinAt_inter (hs.mem_nhds ha)]

@[to_dual]
lemma isRightContinuousOn_iff_isRightContinuous_domRestrict :
    IsRightContinuousOn f s ↔ IsRightContinuous (s.domRestrict f) := by
  rw [IsRightContinuousOn, IsRightContinuous, Subtype.forall]
  exact forall₂_congr fun _ ha ↦ continuousWithinAt_inter_iff_continuousWithinAt_domRestrict f ha

@[to_dual]
alias ⟨IsRightContinuousOn.domRestrict, _⟩ := isRightContinuousOn_iff_isRightContinuous_domRestrict

@[to_dual]
lemma IsRightContinuousOn.congr (hf : IsRightContinuousOn f s) (h : EqOn g f s) :
    IsRightContinuousOn g s :=
  fun a ha ↦ (hf a ha).congr (fun _ hy ↦ h hy.1) (h ha)

@[to_dual]
lemma isRightContinuousOn_congr (h : EqOn g f s) :
    IsRightContinuousOn g s ↔ IsRightContinuousOn f s :=
  ⟨fun hg ↦ hg.congr h.symm, fun hf ↦ hf.congr h⟩

@[to_dual (attr := to_fun continuous_fun_comp)]
lemma IsRightContinuousOn.continuous_comp {Z : Type*} [TopologicalSpace Z] {g : Y → Z}
    (hf : IsRightContinuousOn f s) (hg : Continuous g) :
    IsRightContinuousOn (g ∘ f) s :=
  fun a ha ↦ hg.continuousAt.comp_continuousWithinAt (hf a ha)

@[to_dual]
lemma IsRightContinuousOn.continuous_comp₂ {Z T : Type*} [TopologicalSpace Z] [TopologicalSpace T]
    {g : X → Z} {φ : Y → Z → T} (hf : IsRightContinuousOn f s) (hg : IsRightContinuousOn g s)
    (hφ : Continuous φ.uncurry) :
    IsRightContinuousOn (fun x ↦ φ (f x) (g x)) s :=
  fun a ha ↦ (hφ.tendsto (f a, g a)).comp ((hf a ha).prodMk_nhds (hg a ha))

@[to_dual (attr := simp)]
lemma IsRightContinuousOn.const {c : Y} : IsRightContinuousOn (fun _ ↦ c : X → Y) s :=
  continuous_const.continuousOn.isRightContinuousOn

@[to_dual]
lemma IsRightContinuousOn.id : IsRightContinuousOn (id : X → X) s :=
  continuous_id.continuousOn.isRightContinuousOn

@[to_additive (attr := to_fun (attr := to_dual))]
lemma IsRightContinuousOn.mul [Mul Y] [ContinuousMul Y]
    (hf : IsRightContinuousOn f s) (hg : IsRightContinuousOn g s) :
    IsRightContinuousOn (f * g) s :=
  hf.continuous_comp₂ hg continuous_mul

@[to_additive (attr := to_fun (attr := to_dual)) sub]
lemma IsRightContinuousOn.div' [Div Y] [ContinuousDiv Y]
    (hf : IsRightContinuousOn f s) (hg : IsRightContinuousOn g s) :
    IsRightContinuousOn (f / g) s :=
  hf.continuous_comp₂ hg continuous_div'

@[to_fun (attr := to_dual)]
lemma IsRightContinuousOn.div [GroupWithZero Y] [ContinuousInv₀ Y] [ContinuousMul Y]
    (hf : IsRightContinuousOn f s) (hg : IsRightContinuousOn g s) (h : ∀ x ∈ s, g x ≠ 0) :
    IsRightContinuousOn (f / g) s :=
  fun x hx ↦ (hf x hx).div (hg x hx) (h x hx)

@[to_additive (attr := to_fun (attr := to_dual))]
lemma IsRightContinuousOn.inv [Inv Y] [ContinuousInv Y] (hf : IsRightContinuousOn f s) :
    IsRightContinuousOn (f⁻¹) s :=
  hf.continuous_comp continuous_inv

@[to_fun (attr := to_dual)]
lemma IsRightContinuousOn.inv₀ [Zero Y] [Inv Y] [ContinuousInv₀ Y]
    (hf : IsRightContinuousOn f s) (h : ∀ x ∈ s, f x ≠ 0) :
    IsRightContinuousOn (f⁻¹) s :=
  fun x hx ↦ (hf x hx).inv₀ (h x hx)

@[to_fun (attr := to_dual (attr := to_additive))]
lemma IsRightContinuousOn.const_smul {R : Type*} [SMul R Y] [ContinuousConstSMul R Y] (c : R)
    (hf : IsRightContinuousOn f s) :
    IsRightContinuousOn (c • f) s :=
  hf.continuous_comp (continuous_const_smul c)

end IsRightContinuousOn

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

section PartialOrder

variable [PartialOrder X] [TopologicalSpace Y] {s : Set X}

@[to_dual]
lemma isRightContinuous_iff_continuousWithinAt_Ici :
    IsRightContinuous f ↔ ∀ a, ContinuousWithinAt f (Ici a) a :=
  forall_congr' fun _ ↦ continuousWithinAt_Ioi_iff_Ici

@[to_dual]
lemma isRightContinuousOn_iff_continuousWithinAt_inter_Ici :
    IsRightContinuousOn f s ↔ ∀ a ∈ s, ContinuousWithinAt f (s ∩ Set.Ici a) a :=
  forall₂_congr fun _ _ ↦ continuousWithinAt_inter_Ioi_iff_Ici

end PartialOrder

section LinearOrder

variable [LinearOrder X] [TopologicalSpace Y]

@[to_dual]
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
