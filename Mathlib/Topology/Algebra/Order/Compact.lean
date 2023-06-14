/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Yury Kudryashov

! This file was ported from Lean 3 source module topology.algebra.order.compact
! leanprover-community/mathlib commit 4c19a16e4b705bf135cf9a80ac18fcc99c438514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Topology.Algebra.Order.IntermediateValue
import Mathlib.Topology.LocalExtr

/-!
# Compactness of a closed interval

In this file we prove that a closed interval in a conditionally complete linear ordered type with
order topology (or a product of such types) is compact.

We prove the extreme value theorem (`IsCompact.exists_isMinOn`, `IsCompact.exists_isMaxOn`):
a continuous function on a compact set takes its minimum and maximum values. We provide many
variations of this theorem.

We also prove that the image of a closed interval under a continuous map is a closed interval, see
`ContinuousOn.image_Icc`.

## Tags

compact, extreme value theorem
-/


open Filter OrderDual TopologicalSpace Function Set

open Filter Topology

/-!
### Compactness of a closed interval

In this section we define a typeclass `CompactIccSpace α` saying that all closed intervals in `α`
are compact. Then we provide an instance for a `ConditionallyCompleteLinearOrder` and prove that
the product (both `α × β` and an indexed product) of spaces with this property inherits the
property.

We also prove some simple lemmas about spaces with this property.
-/


/-- This typeclass says that all closed intervals in `α` are compact. This is true for all
conditionally complete linear orders with order topology and products (finite or infinite)
of such spaces. -/
class CompactIccSpace (α : Type _) [TopologicalSpace α] [Preorder α] : Prop where
  /-- A closed interval `Set.Icc a b` is a compact set for all `a` and `b`. -/
  isCompact_Icc : ∀ {a b : α}, IsCompact (Icc a b)
#align compact_Icc_space CompactIccSpace

export CompactIccSpace (isCompact_Icc)

-- porting note: new lemma; TODO: make it the definition
lemma CompactIccSpace.mk' [TopologicalSpace α] [Preorder α]
    (h : ∀ {a b : α}, a ≤ b → IsCompact (Icc a b)) : CompactIccSpace α where
  isCompact_Icc {a b} := by_cases h $ fun hab => by rw [Icc_eq_empty hab]; exact isCompact_empty

-- porting note: new lemma; TODO: drop one `'`
lemma CompactIccSpace.mk'' [TopologicalSpace α] [PartialOrder α]
    (h : ∀ {a b : α}, a < b → IsCompact (Icc a b)) : CompactIccSpace α :=
  .mk' fun hab => hab.eq_or_lt.elim (by rintro rfl; simp) h

/-- A closed interval in a conditionally complete linear order is compact. -/
instance (priority := 100) ConditionallyCompleteLinearOrder.toCompactIccSpace (α : Type _)
    [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α] :
    CompactIccSpace α := by
  refine' .mk'' fun {a b} hlt => ?_
  refine' isCompact_iff_ultrafilter_le_nhds.2 fun f hf => _
  by_contra H
  simp only [not_exists, not_and] at H -- porting note: `contrapose!` fails
  rw [le_principal_iff] at hf
  have hpt : ∀ x ∈ Icc a b, {x} ∉ f := fun x hx hxf =>
    H x hx ((le_pure_iff.2 hxf).trans (pure_le_nhds x))
  set s := { x ∈ Icc a b | Icc a x ∉ f }
  have hsb : b ∈ upperBounds s := fun x hx => hx.1.2
  have ha : a ∈ s := by simp [hpt, hlt.le]
  obtain ⟨c, hsc⟩ : ∃ c, IsLUB s c := ⟨sSup s, isLUB_csSup ⟨a, ha⟩ ⟨b, hsb⟩⟩
  have hc : c ∈ Icc a b := ⟨hsc.1 ha, hsc.2 hsb⟩
  specialize H c hc
  have hcs : c ∈ s := by
    rcases hc.1.eq_or_lt with (rfl | hlt)
    · assumption
    refine' ⟨hc, fun hcf => H fun U hU => _⟩
    rcases exists_Ioc_subset_of_mem_nhds' hU hlt with ⟨x, hxc, hxU⟩
    rcases ((hsc.frequently_mem ⟨a, ha⟩).and_eventually (Ioc_mem_nhdsWithin_Iic' hxc.2)).exists with
      ⟨y, ⟨-, hyf⟩, hy⟩
    refine' mem_of_superset (f.diff_mem_iff.2 ⟨hcf, hyf⟩) (Subset.trans _ hxU)
    rw [diff_subset_iff]
    exact Icc_subset_Icc_union_Ioc.trans (union_subset_union_right _ (Ioc_subset_Ioc_left hy.1.le))
  cases' hc.2.eq_or_lt with heq hlt
  · exact hcs.2 (heq.symm ▸ hf)
  obtain ⟨y, ⟨hcy, hyb⟩, hyf⟩ : ∃ y ∈ Ioc c b, Ico c y ∉ f
  · contrapose! H
    intro U hU
    rcases exists_Ico_subset_of_mem_nhds' hU hlt with ⟨y, hy, hyU⟩
    exact mem_of_superset (H _ hy) hyU
  suffices : y ∈ s
  · exact hcy.not_le (hsc.1 this)
  have hy : y ∈ Icc a b := ⟨hc.1.trans hcy.le, hyb⟩
  refine ⟨hy, fun hay => ?_⟩
  simp only [← Icc_union_Icc_eq_Icc hc.1 hcy.le, ← Ico_union_right hcy.le,
    Ultrafilter.union_mem_iff, hyf, hcs.2, hpt _ hy, false_or] at hay
#align conditionally_complete_linear_order.to_compact_Icc_space ConditionallyCompleteLinearOrder.toCompactIccSpace

instance {ι : Type _} {α : ι → Type _} [∀ i, Preorder (α i)] [∀ i, TopologicalSpace (α i)]
    [∀ i, CompactIccSpace (α i)] : CompactIccSpace (∀ i, α i) :=
  ⟨fun {a b} => (pi_univ_Icc a b ▸ isCompact_univ_pi) fun _ => isCompact_Icc⟩

instance Pi.compact_Icc_space' {α β : Type _} [Preorder β] [TopologicalSpace β]
    [CompactIccSpace β] : CompactIccSpace (α → β) :=
  inferInstance
#align pi.compact_Icc_space' Pi.compact_Icc_space'

instance {α β : Type _} [Preorder α] [TopologicalSpace α] [CompactIccSpace α] [Preorder β]
    [TopologicalSpace β] [CompactIccSpace β] : CompactIccSpace (α × β) :=
  ⟨fun {a b} => (Icc_prod_eq a b).symm ▸ isCompact_Icc.prod isCompact_Icc⟩

/-- An unordered closed interval is compact. -/
theorem isCompact_uIcc {α : Type _} [LinearOrder α] [TopologicalSpace α] [CompactIccSpace α]
    {a b : α} : IsCompact (uIcc a b) :=
  isCompact_Icc
#align is_compact_uIcc isCompact_uIcc

-- See note [lower instance priority]
/-- A complete linear order is a compact space.

We do not register an instance for a `[CompactIccSpace α]` because this would only add instances
for products (indexed or not) of complete linear orders, and we have instances with higher priority
that cover these cases. -/
instance (priority := 100) compactSpace_of_completeLinearOrder {α : Type _} [CompleteLinearOrder α]
    [TopologicalSpace α] [OrderTopology α] : CompactSpace α :=
  ⟨by simp only [← Icc_bot_top, isCompact_Icc]⟩
#align compact_space_of_complete_linear_order compactSpace_of_completeLinearOrder

section

variable {α : Type _} [Preorder α] [TopologicalSpace α] [CompactIccSpace α]

instance compactSpace_Icc (a b : α) : CompactSpace (Icc a b) :=
  isCompact_iff_compactSpace.mp isCompact_Icc
#align compact_space_Icc compactSpace_Icc

end

/-!
### Min and max elements of a compact set
-/


variable {α β γ : Type _} [ConditionallyCompleteLinearOrder α] [TopologicalSpace α]
  [OrderTopology α] [TopologicalSpace β] [TopologicalSpace γ]

theorem IsCompact.sInf_mem {s : Set α} (hs : IsCompact s) (ne_s : s.Nonempty) : sInf s ∈ s :=
  hs.isClosed.csInf_mem ne_s hs.bddBelow
#align is_compact.Inf_mem IsCompact.sInf_mem

theorem IsCompact.sSup_mem {s : Set α} (hs : IsCompact s) (ne_s : s.Nonempty) : sSup s ∈ s :=
  @IsCompact.sInf_mem αᵒᵈ _ _ _ _ hs ne_s
#align is_compact.Sup_mem IsCompact.sSup_mem

theorem IsCompact.isGLB_sInf {s : Set α} (hs : IsCompact s) (ne_s : s.Nonempty) :
    IsGLB s (sInf s) :=
  isGLB_csInf ne_s hs.bddBelow
#align is_compact.is_glb_Inf IsCompact.isGLB_sInf

theorem IsCompact.isLUB_sSup {s : Set α} (hs : IsCompact s) (ne_s : s.Nonempty) :
    IsLUB s (sSup s) :=
  @IsCompact.isGLB_sInf αᵒᵈ _ _ _ _ hs ne_s
#align is_compact.is_lub_Sup IsCompact.isLUB_sSup

theorem IsCompact.isLeast_sInf {s : Set α} (hs : IsCompact s) (ne_s : s.Nonempty) :
    IsLeast s (sInf s) :=
  ⟨hs.sInf_mem ne_s, (hs.isGLB_sInf ne_s).1⟩
#align is_compact.is_least_Inf IsCompact.isLeast_sInf

theorem IsCompact.isGreatest_sSup {s : Set α} (hs : IsCompact s) (ne_s : s.Nonempty) :
    IsGreatest s (sSup s) :=
  @IsCompact.isLeast_sInf αᵒᵈ _ _ _ _ hs ne_s
#align is_compact.is_greatest_Sup IsCompact.isGreatest_sSup

theorem IsCompact.exists_isLeast {s : Set α} (hs : IsCompact s) (ne_s : s.Nonempty) :
    ∃ x, IsLeast s x :=
  ⟨_, hs.isLeast_sInf ne_s⟩
#align is_compact.exists_is_least IsCompact.exists_isLeast

theorem IsCompact.exists_isGreatest {s : Set α} (hs : IsCompact s) (ne_s : s.Nonempty) :
    ∃ x, IsGreatest s x :=
  ⟨_, hs.isGreatest_sSup ne_s⟩
#align is_compact.exists_is_greatest IsCompact.exists_isGreatest

theorem IsCompact.exists_isGLB {s : Set α} (hs : IsCompact s) (ne_s : s.Nonempty) :
    ∃ x ∈ s, IsGLB s x :=
  ⟨_, hs.sInf_mem ne_s, hs.isGLB_sInf ne_s⟩
#align is_compact.exists_is_glb IsCompact.exists_isGLB

theorem IsCompact.exists_isLUB {s : Set α} (hs : IsCompact s) (ne_s : s.Nonempty) :
    ∃ x ∈ s, IsLUB s x :=
  ⟨_, hs.sSup_mem ne_s, hs.isLUB_sSup ne_s⟩
#align is_compact.exists_is_lub IsCompact.exists_isLUB

theorem IsCompact.exists_sInf_image_eq_and_le {s : Set β} (hs : IsCompact s) (ne_s : s.Nonempty)
    {f : β → α} (hf : ContinuousOn f s) : ∃ x ∈ s, sInf (f '' s) = f x ∧ ∀ y ∈ s, f x ≤ f y :=
  let ⟨x, hxs, hx⟩ := (hs.image_of_continuousOn hf).sInf_mem (ne_s.image f)
  ⟨x, hxs, hx.symm, fun _y hy =>
    hx.trans_le <| csInf_le (hs.image_of_continuousOn hf).bddBelow <| mem_image_of_mem f hy⟩
#align is_compact.exists_Inf_image_eq_and_le IsCompact.exists_sInf_image_eq_and_le

theorem IsCompact.exists_sSup_image_eq_and_ge {s : Set β} (hs : IsCompact s) (ne_s : s.Nonempty)
    {f : β → α} (hf : ContinuousOn f s) : ∃ x ∈ s, sSup (f '' s) = f x ∧ ∀ y ∈ s, f y ≤ f x :=
  @IsCompact.exists_sInf_image_eq_and_le αᵒᵈ _ _ _ _ _ _ hs ne_s _ hf
#align is_compact.exists_Sup_image_eq_and_ge IsCompact.exists_sSup_image_eq_and_ge

theorem IsCompact.exists_sInf_image_eq {s : Set β} (hs : IsCompact s) (ne_s : s.Nonempty)
    {f : β → α} (hf : ContinuousOn f s) : ∃ x ∈ s, sInf (f '' s) = f x :=
  let ⟨x, hxs, hx, _⟩ := hs.exists_sInf_image_eq_and_le ne_s hf
  ⟨x, hxs, hx⟩
#align is_compact.exists_Inf_image_eq IsCompact.exists_sInf_image_eq

theorem IsCompact.exists_sSup_image_eq :
    ∀ {s : Set β},
      IsCompact s → s.Nonempty → ∀ {f : β → α}, ContinuousOn f s → ∃ x ∈ s, sSup (f '' s) = f x :=
  @IsCompact.exists_sInf_image_eq αᵒᵈ _ _ _ _ _
#align is_compact.exists_Sup_image_eq IsCompact.exists_sSup_image_eq

theorem eq_Icc_of_connected_compact {s : Set α} (h₁ : IsConnected s) (h₂ : IsCompact s) :
    s = Icc (sInf s) (sSup s) :=
  eq_Icc_csInf_csSup_of_connected_bdd_closed h₁ h₂.bddBelow h₂.bddAbove h₂.isClosed
#align eq_Icc_of_connected_compact eq_Icc_of_connected_compact

/-!
### Extreme value theorem
-/

-- porting note: new lemma; defeq to the old one but allows us to use dot notation
/-- The **extreme value theorem**: a continuous function realizes its minimum on a compact set. -/
theorem IsCompact.exists_isMinOn {s : Set β} (hs : IsCompact s) (ne_s : s.Nonempty) {f : β → α}
    (hf : ContinuousOn f s) : ∃ x ∈ s, IsMinOn f s x := by
  rcases hs.exists_sInf_image_eq_and_le ne_s hf with ⟨x, hxs, -, hx⟩
  exact ⟨x, hxs, hx⟩

/-- The **extreme value theorem**: a continuous function realizes its minimum on a compact set. -/
@[deprecated IsCompact.exists_isMinOn]
theorem IsCompact.exists_forall_le {s : Set β} (hs : IsCompact s) (ne_s : s.Nonempty) {f : β → α}
    (hf : ContinuousOn f s) : ∃ x ∈ s, ∀ y ∈ s, f x ≤ f y :=
  hs.exists_isMinOn ne_s hf
#align is_compact.exists_forall_le IsCompact.exists_forall_le

-- porting note: new lemma; defeq to the old one but allows us to use dot notation
/-- The **extreme value theorem**: a continuous function realizes its maximum on a compact set. -/
theorem IsCompact.exists_isMaxOn : ∀ {s : Set β}, IsCompact s → s.Nonempty → ∀ {f : β → α},
    ContinuousOn f s → ∃ x ∈ s, IsMaxOn f s x :=
  @IsCompact.exists_isMinOn αᵒᵈ _ _ _ _ _

/-- The **extreme value theorem**: a continuous function realizes its maximum on a compact set. -/
@[deprecated IsCompact.exists_isMaxOn]
theorem IsCompact.exists_forall_ge : ∀ {s : Set β}, IsCompact s → s.Nonempty → ∀ {f : β → α},
    ContinuousOn f s → ∃ x ∈ s, ∀ y ∈ s, f y ≤ f x :=
  IsCompact.exists_isMaxOn
#align is_compact.exists_forall_ge IsCompact.exists_forall_ge

/-- The **extreme value theorem**: if a function `f` is continuous on a closed set `s` and it is
larger than a value in its image away from compact sets, then it has a minimum on this set. -/
theorem ContinuousOn.exists_isMinOn' {s : Set β} {f : β → α} (hf : ContinuousOn f s)
    (hsc : IsClosed s) {x₀ : β} (h₀ : x₀ ∈ s) (hc : ∀ᶠ x in cocompact β ⊓ 𝓟 s, f x₀ ≤ f x) :
    ∃ x ∈ s, IsMinOn f s x := by
  rcases (hasBasis_cocompact.inf_principal _).eventually_iff.1 hc with ⟨K, hK, hKf⟩
  have hsub : insert x₀ (K ∩ s) ⊆ s := insert_subset.2 ⟨h₀, inter_subset_right _ _⟩
  obtain ⟨x, hx, hxf⟩ : ∃ x ∈ insert x₀ (K ∩ s), ∀ y ∈ insert x₀ (K ∩ s), f x ≤ f y :=
    ((hK.inter_right hsc).insert x₀).exists_forall_le (insert_nonempty _ _) (hf.mono hsub)
  refine' ⟨x, hsub hx, fun y hy => _⟩
  by_cases hyK : y ∈ K
  exacts [hxf _ (Or.inr ⟨hyK, hy⟩), (hxf _ (Or.inl rfl)).trans (hKf ⟨hyK, hy⟩)]

/-- The **extreme value theorem**: if a function `f` is continuous on a closed set `s` and it is
larger than a value in its image away from compact sets, then it has a minimum on this set. -/
@[deprecated ContinuousOn.exists_isMinOn']
theorem ContinuousOn.exists_forall_le' {s : Set β} {f : β → α} (hf : ContinuousOn f s)
    (hsc : IsClosed s) {x₀ : β} (h₀ : x₀ ∈ s) (hc : ∀ᶠ x in cocompact β ⊓ 𝓟 s, f x₀ ≤ f x) :
    ∃ x ∈ s, ∀ y ∈ s, f x ≤ f y :=
  hf.exists_isMinOn' hsc h₀ hc
#align continuous_on.exists_forall_le' ContinuousOn.exists_forall_le'

/-- The **extreme value theorem**: if a function `f` is continuous on a closed set `s` and it is
smaller than a value in its image away from compact sets, then it has a maximum on this set. -/
theorem ContinuousOn.exists_isMaxOn' {s : Set β} {f : β → α} (hf : ContinuousOn f s)
    (hsc : IsClosed s) {x₀ : β} (h₀ : x₀ ∈ s) (hc : ∀ᶠ x in cocompact β ⊓ 𝓟 s, f x ≤ f x₀) :
    ∃ x ∈ s, IsMaxOn f s x :=
  @ContinuousOn.exists_isMinOn' αᵒᵈ _ _ _ _ _ _ _ hf hsc _ h₀ hc

/-- The **extreme value theorem**: if a function `f` is continuous on a closed set `s` and it is
smaller than a value in its image away from compact sets, then it has a maximum on this set. -/
@[deprecated ContinuousOn.exists_isMaxOn']
theorem ContinuousOn.exists_forall_ge' {s : Set β} {f : β → α} (hf : ContinuousOn f s)
    (hsc : IsClosed s) {x₀ : β} (h₀ : x₀ ∈ s) (hc : ∀ᶠ x in cocompact β ⊓ 𝓟 s, f x ≤ f x₀) :
    ∃ x ∈ s, ∀ y ∈ s, f y ≤ f x :=
  hf.exists_isMaxOn' hsc h₀ hc
#align continuous_on.exists_forall_ge' ContinuousOn.exists_forall_ge'

/-- The **extreme value theorem**: if a continuous function `f` is larger than a value in its range
away from compact sets, then it has a global minimum. -/
theorem Continuous.exists_forall_le' {f : β → α} (hf : Continuous f) (x₀ : β)
    (h : ∀ᶠ x in cocompact β, f x₀ ≤ f x) : ∃ x : β, ∀ y : β, f x ≤ f y :=
  let ⟨x, _, hx⟩ := hf.continuousOn.exists_forall_le' isClosed_univ (mem_univ x₀)
    (by rwa [principal_univ, inf_top_eq])
  ⟨x, fun y => hx y (mem_univ y)⟩
#align continuous.exists_forall_le' Continuous.exists_forall_le'

/-- The **extreme value theorem**: if a continuous function `f` is smaller than a value in its range
away from compact sets, then it has a global maximum. -/
theorem Continuous.exists_forall_ge' {f : β → α} (hf : Continuous f) (x₀ : β)
    (h : ∀ᶠ x in cocompact β, f x ≤ f x₀) : ∃ x : β, ∀ y : β, f y ≤ f x :=
  @Continuous.exists_forall_le' αᵒᵈ _ _ _ _ _ _ hf x₀ h
#align continuous.exists_forall_ge' Continuous.exists_forall_ge'

/-- The **extreme value theorem**: if a continuous function `f` tends to infinity away from compact
sets, then it has a global minimum. -/
theorem Continuous.exists_forall_le [Nonempty β] {f : β → α} (hf : Continuous f)
    (hlim : Tendsto f (cocompact β) atTop) : ∃ x, ∀ y, f x ≤ f y := by
  inhabit β
  exact hf.exists_forall_le' default (hlim.eventually <| eventually_ge_atTop _)
#align continuous.exists_forall_le Continuous.exists_forall_le

/-- The **extreme value theorem**: if a continuous function `f` tends to negative infinity away from
compact sets, then it has a global maximum. -/
theorem Continuous.exists_forall_ge [Nonempty β] {f : β → α} (hf : Continuous f)
    (hlim : Tendsto f (cocompact β) atBot) : ∃ x, ∀ y, f y ≤ f x :=
  @Continuous.exists_forall_le αᵒᵈ _ _ _ _ _ _ _ hf hlim
#align continuous.exists_forall_ge Continuous.exists_forall_ge

theorem IsCompact.sSup_lt_iff_of_continuous {f : β → α} {K : Set β} (hK : IsCompact K)
    (h0K : K.Nonempty) (hf : ContinuousOn f K) (y : α) : sSup (f '' K) < y ↔ ∀ x ∈ K, f x < y :=
  ((hK.image_of_continuousOn hf).isGreatest_sSup (h0K.image _)).lt_iff.trans ball_image_iff
#align is_compact.Sup_lt_iff_of_continuous IsCompact.sSup_lt_iff_of_continuous

theorem IsCompact.lt_sInf_iff_of_continuous {α β : Type _} [ConditionallyCompleteLinearOrder α]
    [TopologicalSpace α] [OrderTopology α] [TopologicalSpace β] {f : β → α} {K : Set β}
    (hK : IsCompact K) (h0K : K.Nonempty) (hf : ContinuousOn f K) (y : α) :
    y < sInf (f '' K) ↔ ∀ x ∈ K, y < f x :=
  @IsCompact.sSup_lt_iff_of_continuous αᵒᵈ β _ _ _ _ _ _ hK h0K hf y
#align is_compact.lt_Inf_iff_of_continuous IsCompact.lt_sInf_iff_of_continuous

/-- A continuous function with compact support has a global minimum. -/
@[to_additive "A continuous function with compact support has a global minimum."]
theorem Continuous.exists_forall_le_of_hasCompactMulSupport [Nonempty β] [One α] {f : β → α}
    (hf : Continuous f) (h : HasCompactMulSupport f) : ∃ x : β, ∀ y : β, f x ≤ f y := by
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := (h.isCompact_range hf).exists_isLeast (range_nonempty _)
  rw [mem_lowerBounds, forall_range_iff] at hx
  exact ⟨x, hx⟩
#align continuous.exists_forall_le_of_has_compact_mul_support Continuous.exists_forall_le_of_hasCompactMulSupport
#align continuous.exists_forall_le_of_has_compact_support Continuous.exists_forall_le_of_hasCompactSupport

/-- A continuous function with compact support has a global maximum. -/
@[to_additive "A continuous function with compact support has a global maximum."]
theorem Continuous.exists_forall_ge_of_hasCompactMulSupport [Nonempty β] [One α] {f : β → α}
    (hf : Continuous f) (h : HasCompactMulSupport f) : ∃ x : β, ∀ y : β, f y ≤ f x :=
  @Continuous.exists_forall_le_of_hasCompactMulSupport αᵒᵈ _ _ _ _ _ _ _ _ hf h
#align continuous.exists_forall_ge_of_has_compact_mul_support Continuous.exists_forall_ge_of_hasCompactMulSupport
#align continuous.exists_forall_ge_of_has_compact_support Continuous.exists_forall_ge_of_hasCompactSupport

/- If `f : γ → β → α` is a function that is continuous as a function on `γ × β`, `α` is a
conditionally complete linear order, and `K : Set β` is a compact set, then
`fun x ↦ sSup (f x '' K)` is a continuous function.

Porting note: todo: generalize. The following version seems to be true:
```
theorem IsCompact.tendsto_sSup {f : γ → β → α} {g : β → α} {K : Set β} {l : Filter γ}
    (hK : IsCompact K) (hf : ∀ y ∈ K, Tendsto ↿f (l ×ˢ 𝓝[K] y) (𝓝 (g y)))
    (hgc : ContinuousOn g K) :
    Tendsto (fun x => sSup (f x '' K)) l (𝓝 (sSup (g '' K))) := _
```
Moreover, it seems that `hgc` follows from `hf` (Yury Kudryashov).
-/
theorem IsCompact.continuous_sSup {f : γ → β → α} {K : Set β} (hK : IsCompact K)
    (hf : Continuous ↿f) : Continuous fun x => sSup (f x '' K) := by
  rcases eq_empty_or_nonempty K with (rfl | h0K)
  · simp_rw [image_empty]
    exact continuous_const
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨y, hyK, h2y, hy⟩ :=
    hK.exists_sSup_image_eq_and_ge h0K
      (show Continuous fun y => f x y from hf.comp <| Continuous.Prod.mk x).continuousOn
  rw [ContinuousAt, h2y, tendsto_order]
  have := tendsto_order.mp ((show Continuous fun x => f x y
    from hf.comp <| continuous_id.prod_mk continuous_const).tendsto x)
  refine' ⟨fun z hz => _, fun z hz => _⟩
  · refine' (this.1 z hz).mono fun x' hx' =>
      hx'.trans_le <| le_csSup _ <| mem_image_of_mem (f x') hyK
    exact hK.bddAbove_image (hf.comp <| Continuous.Prod.mk x').continuousOn
  · have h : ({x} : Set γ) ×ˢ K ⊆ ↿f ⁻¹' Iio z := by
      rintro ⟨x', y'⟩ ⟨(rfl : x' = x), hy'⟩
      exact (hy y' hy').trans_lt hz
    obtain ⟨u, v, hu, _, hxu, hKv, huv⟩ :=
      generalized_tube_lemma isCompact_singleton hK (isOpen_Iio.preimage hf) h
    refine' eventually_of_mem (hu.mem_nhds (singleton_subset_iff.mp hxu)) fun x' hx' => _
    rw [hK.sSup_lt_iff_of_continuous h0K
        (show Continuous (f x') from hf.comp <| Continuous.Prod.mk x').continuousOn]
    exact fun y' hy' => huv (mk_mem_prod hx' (hKv hy'))
#align is_compact.continuous_Sup IsCompact.continuous_sSup

theorem IsCompact.continuous_sInf {f : γ → β → α} {K : Set β} (hK : IsCompact K)
    (hf : Continuous ↿f) : Continuous fun x => sInf (f x '' K) :=
  @IsCompact.continuous_sSup αᵒᵈ β γ _ _ _ _ _ _ _ hK hf
#align is_compact.continuous_Inf IsCompact.continuous_sInf

namespace ContinuousOn

/-!
### Image of a closed interval
-/

variable [DenselyOrdered α] [ConditionallyCompleteLinearOrder β] [OrderTopology β] {f : α → β}
  {a b c : α}

open Interval

theorem image_Icc (hab : a ≤ b) (h : ContinuousOn f <| Icc a b) :
    f '' Icc a b = Icc (sInf <| f '' Icc a b) (sSup <| f '' Icc a b) :=
  eq_Icc_of_connected_compact ⟨(nonempty_Icc.2 hab).image f, isPreconnected_Icc.image f h⟩
    (isCompact_Icc.image_of_continuousOn h)
#align continuous_on.image_Icc ContinuousOn.image_Icc

theorem image_uIcc_eq_Icc (h : ContinuousOn f [[a, b]]) :
    f '' [[a, b]] = Icc (sInf (f '' [[a, b]])) (sSup (f '' [[a, b]])) :=
  image_Icc min_le_max h
#align continuous_on.image_uIcc_eq_Icc ContinuousOn.image_uIcc_eq_Icc

theorem image_uIcc (h : ContinuousOn f <| [[a, b]]) :
    f '' [[a, b]] = [[sInf (f '' [[a, b]]), sSup (f '' [[a, b]])]] := by
  refine' h.image_uIcc_eq_Icc.trans (uIcc_of_le _).symm
  refine' csInf_le_csSup _ _ (nonempty_uIcc.image _) <;> rw [h.image_uIcc_eq_Icc]
  exacts [bddBelow_Icc, bddAbove_Icc]
#align continuous_on.image_uIcc ContinuousOn.image_uIcc

theorem sInf_image_Icc_le (h : ContinuousOn f <| Icc a b) (hc : c ∈ Icc a b) :
    sInf (f '' Icc a b) ≤ f c := by
  have := mem_image_of_mem f hc
  rw [h.image_Icc (hc.1.trans hc.2)] at this
  exact this.1
#align continuous_on.Inf_image_Icc_le ContinuousOn.sInf_image_Icc_le

theorem le_sSup_image_Icc (h : ContinuousOn f <| Icc a b) (hc : c ∈ Icc a b) :
    f c ≤ sSup (f '' Icc a b) := by
  have := mem_image_of_mem f hc
  rw [h.image_Icc (hc.1.trans hc.2)] at this
  exact this.2
#align continuous_on.le_Sup_image_Icc ContinuousOn.le_sSup_image_Icc

end ContinuousOn

-- porting note: todo: add dual versions

theorem IsCompact.exists_isMinOn_mem_subset {f : β → α} {s t : Set β} {z : β}
    (ht : IsCompact t) (hf : ContinuousOn f t) (hz : z ∈ t) (hfz : ∀ z' ∈ t \ s, f z < f z') :
    ∃ x ∈ s, IsMinOn f t x :=
  let ⟨x, hxt, hfx⟩ := ht.exists_isMinOn ⟨z, hz⟩ hf
  ⟨x, by_contra <| fun hxs => (hfz x ⟨hxt, hxs⟩).not_le (hfx hz), hfx⟩

@[deprecated IsCompact.exists_isMinOn_mem_subset]
theorem IsCompact.exists_isLocalMinOn_mem_subset {f : β → α} {s t : Set β} {z : β}
    (ht : IsCompact t) (hf : ContinuousOn f t) (hz : z ∈ t) (hfz : ∀ z' ∈ t \ s, f z < f z') :
    ∃ x ∈ s, IsLocalMinOn f t x :=
  let ⟨x, hxs, h⟩ := ht.exists_isMinOn_mem_subset hf hz hfz
  ⟨x, hxs, h.localize⟩
#align is_compact.exists_local_min_on_mem_subset IsCompact.exists_isLocalMinOn_mem_subset

-- porting note: rfc: assume `t ∈ 𝓝ˢ s` (a.k.a. `s ⊆ interior t`) instead of `s ⊆ t` and
-- `IsOpen s`?
theorem IsCompact.exists_local_min_mem_open {f : β → α} {s t : Set β} {z : β} (ht : IsCompact t)
    (hst : s ⊆ t) (hf : ContinuousOn f t) (hz : z ∈ t) (hfz : ∀ z' ∈ t \ s, f z < f z')
    (hs : IsOpen s) : ∃ x ∈ s, IsLocalMin f x :=
  let ⟨x, hxs, h⟩ := ht.exists_isMinOn_mem_subset hf hz hfz
  ⟨x, hxs, h.isLocalMin <| mem_nhds_iff.2 ⟨s, hst, hs, hxs⟩⟩
#align is_compact.exists_local_min_mem_open IsCompact.exists_local_min_mem_open
