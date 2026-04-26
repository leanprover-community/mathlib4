/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Yury Kudryashov
-/
module

public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Order.IsLUB
public import Mathlib.Topology.Order.LocalExtr

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

public section

open Filter OrderDual TopologicalSpace Function Set

open scoped Filter Topology

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
class CompactIccSpace (α : Type*) [TopologicalSpace α] [Preorder α] : Prop where
  /-- A closed interval `Set.Icc a b` is a compact set for all `a` and `b`. -/
  isCompact_Icc : ∀ {a b : α}, IsCompact (Icc a b)

export CompactIccSpace (isCompact_Icc)

variable {α : Type*}

-- TODO: make it the definition
lemma CompactIccSpace.mk' [TopologicalSpace α] [Preorder α]
    (h : ∀ {a b : α}, a ≤ b → IsCompact (Icc a b)) : CompactIccSpace α where
  isCompact_Icc {a b} := by_cases h fun hab => by rw [Icc_eq_empty hab]; exact isCompact_empty

-- TODO: drop one `'`
lemma CompactIccSpace.mk'' [TopologicalSpace α] [PartialOrder α]
    (h : ∀ {a b : α}, a < b → IsCompact (Icc a b)) : CompactIccSpace α :=
  .mk' fun hab => hab.eq_or_lt.elim (by rintro rfl; simp) h

instance [TopologicalSpace α] [Preorder α] [CompactIccSpace α] : CompactIccSpace (αᵒᵈ) where
  isCompact_Icc := by
    intro a b
    convert isCompact_Icc (α := α) (a := b) (b := a) using 1
    exact Icc_toDual (α := α)

/-- A closed interval in a conditionally complete linear order is compact. -/
instance (priority := 100) ConditionallyCompleteLinearOrder.toCompactIccSpace (α : Type*)
    [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α] :
    CompactIccSpace α := ⟨fun {_ _} ↦ ConditionallyCompleteLinearOrder.isCompact_Icc _ _⟩

instance {ι : Type*} {α : ι → Type*} [∀ i, Preorder (α i)] [∀ i, TopologicalSpace (α i)]
    [∀ i, CompactIccSpace (α i)] : CompactIccSpace (∀ i, α i) :=
  ⟨fun {a b} => (pi_univ_Icc a b ▸ isCompact_univ_pi) fun _ => isCompact_Icc⟩

instance Pi.compact_Icc_space' {α β : Type*} [Preorder β] [TopologicalSpace β]
    [CompactIccSpace β] : CompactIccSpace (α → β) :=
  inferInstance

instance {α β : Type*} [Preorder α] [TopologicalSpace α] [CompactIccSpace α] [Preorder β]
    [TopologicalSpace β] [CompactIccSpace β] : CompactIccSpace (α × β) :=
  ⟨fun {a b} => (Icc_prod_eq a b).symm ▸ isCompact_Icc.prod isCompact_Icc⟩

/-- An unordered closed interval is compact. -/
theorem isCompact_uIcc {α : Type*} [LinearOrder α] [TopologicalSpace α] [CompactIccSpace α]
    {a b : α} : IsCompact (uIcc a b) :=
  isCompact_Icc

-- See note [lower instance priority]
/-- A complete linear order is a compact space.

We do not register an instance for a `[CompactIccSpace α]` because this would only add instances
for products (indexed or not) of complete linear orders, and we have instances with higher priority
that cover these cases. -/
instance (priority := 100) compactSpace_of_completeLinearOrder {α : Type*} [CompleteLinearOrder α]
    [TopologicalSpace α] [OrderTopology α] : CompactSpace α :=
  ⟨by simp only [← Icc_bot_top, isCompact_Icc]⟩

section

variable {α : Type*} [Preorder α] [TopologicalSpace α] [CompactIccSpace α]

instance compactSpace_Icc (a b : α) : CompactSpace (Icc a b) :=
  isCompact_iff_compactSpace.mp isCompact_Icc

end

section openIntervals
variable {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α]

/-- `Set.Ico a b` is only compact if it is empty. -/
@[simp]
theorem isCompact_Ico_iff {a b : α} : IsCompact (Set.Ico a b) ↔ b ≤ a :=
  ⟨fun h => isClosed_Ico_iff.mp h.isClosed, by simp_all⟩

/-- `Set.Ioc a b` is only compact if it is empty. -/
@[simp]
theorem isCompact_Ioc_iff {a b : α} : IsCompact (Set.Ioc a b) ↔ b ≤ a :=
  ⟨fun h => isClosed_Ioc_iff.mp h.isClosed, by simp_all⟩

/-- `Set.Ioo a b` is only compact if it is empty. -/
@[simp]
theorem isCompact_Ioo_iff {a b : α} : IsCompact (Set.Ioo a b) ↔ b ≤ a :=
  ⟨fun h => isClosed_Ioo_iff.mp h.isClosed, by simp_all⟩

end openIntervals

/-!
### Extreme value theorem
-/

section LinearOrder

variable {α β γ : Type*} [LinearOrder α] [TopologicalSpace α]
  [TopologicalSpace β] [TopologicalSpace γ]

theorem IsCompact.exists_isLeast [ClosedIicTopology α] {s : Set α} (hs : IsCompact s)
    (ne_s : s.Nonempty) : ∃ x, IsLeast s x := by
  haveI : Nonempty s := ne_s.to_subtype
  suffices (s ∩ ⋂ x ∈ s, Iic x).Nonempty from
    ⟨this.choose, this.choose_spec.1, mem_iInter₂.mp this.choose_spec.2⟩
  rw [biInter_eq_iInter]
  by_contra H
  rw [not_nonempty_iff_eq_empty] at H
  rcases hs.elim_directed_family_closed (fun x : s => Iic ↑x) (fun x => isClosed_Iic) H
      (Monotone.directed_ge fun _ _ h => Iic_subset_Iic.mpr h) with ⟨x, hx⟩
  exact not_nonempty_iff_eq_empty.mpr hx ⟨x, x.2, le_rfl⟩

theorem IsCompact.exists_isGreatest [ClosedIciTopology α] {s : Set α} (hs : IsCompact s)
    (ne_s : s.Nonempty) : ∃ x, IsGreatest s x :=
  IsCompact.exists_isLeast (α := αᵒᵈ) hs ne_s

theorem IsCompact.exists_isGLB [ClosedIicTopology α] {s : Set α} (hs : IsCompact s)
    (ne_s : s.Nonempty) : ∃ x ∈ s, IsGLB s x :=
  (hs.exists_isLeast ne_s).imp (fun x (hx : IsLeast s x) => ⟨hx.1, hx.isGLB⟩)

theorem IsCompact.exists_isLUB [ClosedIciTopology α] {s : Set α} (hs : IsCompact s)
    (ne_s : s.Nonempty) : ∃ x ∈ s, IsLUB s x :=
  IsCompact.exists_isGLB (α := αᵒᵈ) hs ne_s

theorem cocompact_le_atBot_atTop [CompactIccSpace α] :
    cocompact α ≤ atBot ⊔ atTop := by
  refine fun s hs ↦ mem_cocompact.mpr <| (isEmpty_or_nonempty α).casesOn ?_ ?_ <;> intro
  · exact ⟨∅, isCompact_empty, fun x _ ↦ (IsEmpty.false x).elim⟩
  · obtain ⟨t, ht⟩ := mem_atBot_sets.mp hs.1
    obtain ⟨u, hu⟩ := mem_atTop_sets.mp hs.2
    refine ⟨Icc t u, isCompact_Icc, fun x hx ↦ ?_⟩
    exact (not_and_or.mp hx).casesOn (fun h ↦ ht x (le_of_not_ge h)) fun h ↦ hu x (le_of_not_ge h)

theorem cocompact_le_atBot [OrderTop α] [CompactIccSpace α] :
    cocompact α ≤ atBot := by
  refine fun _ hs ↦ mem_cocompact.mpr <| (isEmpty_or_nonempty α).casesOn ?_ ?_ <;> intro
  · exact ⟨∅, isCompact_empty, fun x _ ↦ (IsEmpty.false x).elim⟩
  · obtain ⟨t, ht⟩ := mem_atBot_sets.mp hs
    refine ⟨Icc t ⊤, isCompact_Icc, fun _ hx ↦ ?_⟩
    exact (not_and_or.mp hx).casesOn (fun h ↦ ht _ (le_of_not_ge h)) (fun h ↦ (h le_top).elim)

theorem cocompact_le_atTop [OrderBot α] [CompactIccSpace α] :
    cocompact α ≤ atTop :=
  cocompact_le_atBot (α := αᵒᵈ)

theorem atBot_le_cocompact [NoMinOrder α] [ClosedIicTopology α] :
    atBot ≤ cocompact α := by
  refine fun s hs ↦ ?_
  obtain ⟨t, ht, hts⟩ := mem_cocompact.mp hs
  refine (Set.eq_empty_or_nonempty t).casesOn (fun h_empty ↦ ?_) (fun h_nonempty ↦ ?_)
  · rewrite [compl_univ_iff.mpr h_empty, univ_subset_iff] at hts
    convert univ_mem
  · haveI := h_nonempty.nonempty
    obtain ⟨a, ha⟩ := ht.exists_isLeast h_nonempty
    obtain ⟨b, hb⟩ := exists_lt a
    exact Filter.mem_atBot_sets.mpr ⟨b, fun b' hb' ↦ hts <| Classical.byContradiction
      fun hc ↦ LT.lt.false <| hb'.trans_lt <| hb.trans_le <| ha.2 (not_notMem.mp hc)⟩

theorem atTop_le_cocompact [NoMaxOrder α] [ClosedIciTopology α] :
    atTop ≤ cocompact α :=
  atBot_le_cocompact (α := αᵒᵈ)

theorem atBot_atTop_le_cocompact [NoMinOrder α] [NoMaxOrder α]
    [OrderClosedTopology α] : atBot ⊔ atTop ≤ cocompact α :=
  sup_le atBot_le_cocompact atTop_le_cocompact

@[simp 900]
theorem cocompact_eq_atBot_atTop [NoMaxOrder α] [NoMinOrder α]
    [OrderClosedTopology α] [CompactIccSpace α] : cocompact α = atBot ⊔ atTop :=
  cocompact_le_atBot_atTop.antisymm atBot_atTop_le_cocompact

@[simp]
theorem cocompact_eq_atBot [NoMinOrder α] [OrderTop α]
    [ClosedIicTopology α] [CompactIccSpace α] : cocompact α = atBot :=
  cocompact_le_atBot.antisymm atBot_le_cocompact

@[simp]
theorem cocompact_eq_atTop [NoMaxOrder α] [OrderBot α]
    [ClosedIciTopology α] [CompactIccSpace α] : cocompact α = atTop :=
  cocompact_le_atTop.antisymm atTop_le_cocompact

/-- The **extreme value theorem**: a continuous function realizes its minimum on a compact set. -/
theorem IsCompact.exists_isMinOn [ClosedIicTopology α] {s : Set β} (hs : IsCompact s)
    (ne_s : s.Nonempty) {f : β → α} (hf : ContinuousOn f s) : ∃ x ∈ s, IsMinOn f s x := by
  rcases (hs.image_of_continuousOn hf).exists_isLeast (ne_s.image f) with ⟨_, ⟨x, hxs, rfl⟩, hx⟩
  refine ⟨x, hxs, forall_mem_image.1 (fun _ hb => hx <| mem_image_of_mem f ?_)⟩
  rwa [(image_id' s).symm]

/-- If a continuous function lies strictly above `a` on a compact set,
  it has a lower bound strictly above `a`. -/
theorem IsCompact.exists_forall_le' [ClosedIicTopology α] [NoMaxOrder α] {f : β → α}
    {s : Set β} (hs : IsCompact s) (hf : ContinuousOn f s) {a : α} (hf' : ∀ b ∈ s, a < f b) :
    ∃ a', a < a' ∧ ∀ b ∈ s, a' ≤ f b := by
  rcases s.eq_empty_or_nonempty with (rfl | hs')
  · obtain ⟨a', ha'⟩ := exists_gt a
    exact ⟨a', ha', fun _ a ↦ a.elim⟩
  · obtain ⟨x, hx, hx'⟩ := hs.exists_isMinOn hs' hf
    exact ⟨f x, hf' x hx, hx'⟩

/-- The **extreme value theorem**: a continuous function realizes its maximum on a compact set. -/
theorem IsCompact.exists_isMaxOn [ClosedIciTopology α] {s : Set β} (hs : IsCompact s)
    (ne_s : s.Nonempty) {f : β → α} (hf : ContinuousOn f s) : ∃ x ∈ s, IsMaxOn f s x :=
  IsCompact.exists_isMinOn (α := αᵒᵈ) hs ne_s hf

/-- The **extreme value theorem**: if a function `f` is continuous on a closed set `s` and it is
larger than a value in its image away from compact sets, then it has a minimum on this set. -/
theorem ContinuousOn.exists_isMinOn' [ClosedIicTopology α] {s : Set β} {f : β → α}
    (hf : ContinuousOn f s) (hsc : IsClosed s) {x₀ : β} (h₀ : x₀ ∈ s)
    (hc : ∀ᶠ x in cocompact β ⊓ 𝓟 s, f x₀ ≤ f x) : ∃ x ∈ s, IsMinOn f s x := by
  rcases (hasBasis_cocompact.inf_principal _).eventually_iff.1 hc with ⟨K, hK, hKf⟩
  have hsub : insert x₀ (K ∩ s) ⊆ s := insert_subset_iff.2 ⟨h₀, inter_subset_right⟩
  obtain ⟨x, hx, hxf⟩ : ∃ x ∈ insert x₀ (K ∩ s), ∀ y ∈ insert x₀ (K ∩ s), f x ≤ f y :=
    ((hK.inter_right hsc).insert x₀).exists_isMinOn (insert_nonempty _ _) (hf.mono hsub)
  refine ⟨x, hsub hx, fun y hy => ?_⟩
  by_cases hyK : y ∈ K
  exacts [hxf _ (Or.inr ⟨hyK, hy⟩), (hxf _ (Or.inl rfl)).trans (hKf ⟨hyK, hy⟩)]

/-- The **extreme value theorem**: if a function `f` is continuous on a closed set `s` and it is
smaller than a value in its image away from compact sets, then it has a maximum on this set. -/
theorem ContinuousOn.exists_isMaxOn' [ClosedIciTopology α] {s : Set β} {f : β → α}
    (hf : ContinuousOn f s) (hsc : IsClosed s) {x₀ : β} (h₀ : x₀ ∈ s)
    (hc : ∀ᶠ x in cocompact β ⊓ 𝓟 s, f x ≤ f x₀) : ∃ x ∈ s, IsMaxOn f s x :=
  ContinuousOn.exists_isMinOn' (α := αᵒᵈ) hf hsc h₀ hc

/-- The **extreme value theorem**: if a continuous function `f` is larger than a value in its range
away from compact sets, then it has a global minimum. -/
theorem Continuous.exists_forall_le' [ClosedIicTopology α] {f : β → α} (hf : Continuous f)
    (x₀ : β) (h : ∀ᶠ x in cocompact β, f x₀ ≤ f x) : ∃ x : β, ∀ y : β, f x ≤ f y :=
  let ⟨x, _, hx⟩ := hf.continuousOn.exists_isMinOn' isClosed_univ (mem_univ x₀)
    (by rwa [principal_univ, inf_top_eq])
  ⟨x, fun y => hx (mem_univ y)⟩

/-- The **extreme value theorem**: if a continuous function `f` is smaller than a value in its range
away from compact sets, then it has a global maximum. -/
theorem Continuous.exists_forall_ge' [ClosedIciTopology α] {f : β → α} (hf : Continuous f)
    (x₀ : β) (h : ∀ᶠ x in cocompact β, f x ≤ f x₀) : ∃ x : β, ∀ y : β, f y ≤ f x :=
  Continuous.exists_forall_le' (α := αᵒᵈ) hf x₀ h

/-- The **extreme value theorem**: if a continuous function `f` tends to infinity away from compact
sets, then it has a global minimum. -/
theorem Continuous.exists_forall_le [ClosedIicTopology α] [Nonempty β] {f : β → α}
    (hf : Continuous f) (hlim : Tendsto f (cocompact β) atTop) : ∃ x, ∀ y, f x ≤ f y := by
  inhabit β
  exact hf.exists_forall_le' default (hlim.eventually <| eventually_ge_atTop _)

/-- The **extreme value theorem**: if a continuous function `f` tends to negative infinity away from
compact sets, then it has a global maximum. -/
theorem Continuous.exists_forall_ge [ClosedIciTopology α] [Nonempty β] {f : β → α}
    (hf : Continuous f) (hlim : Tendsto f (cocompact β) atBot) : ∃ x, ∀ y, f y ≤ f x :=
  Continuous.exists_forall_le (α := αᵒᵈ) hf hlim

/-- A continuous function with compact support has a global minimum. -/
@[to_additive /-- A continuous function with compact support has a global minimum. -/]
theorem Continuous.exists_forall_le_of_hasCompactMulSupport [ClosedIicTopology α] [Nonempty β]
    [One α] {f : β → α} (hf : Continuous f) (h : HasCompactMulSupport f) :
    ∃ x : β, ∀ y : β, f x ≤ f y := by
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := (h.isCompact_range hf).exists_isLeast (range_nonempty _)
  rw [mem_lowerBounds, forall_mem_range] at hx
  exact ⟨x, hx⟩

/-- A continuous function with compact support has a global maximum. -/
@[to_additive /-- A continuous function with compact support has a global maximum. -/]
theorem Continuous.exists_forall_ge_of_hasCompactMulSupport [ClosedIciTopology α] [Nonempty β]
    [One α] {f : β → α} (hf : Continuous f) (h : HasCompactMulSupport f) :
    ∃ x : β, ∀ y : β, f y ≤ f x :=
  Continuous.exists_forall_le_of_hasCompactMulSupport (α := αᵒᵈ) hf h

/-- A compact set is bounded below -/
theorem IsCompact.bddBelow [ClosedIicTopology α] [Nonempty α] {s : Set α} (hs : IsCompact s) :
    BddBelow s := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · exact bddBelow_empty
  · obtain ⟨a, -, has⟩ := hs.exists_isLeast hne
    exact ⟨a, has⟩

/-- A compact set is bounded above -/
theorem IsCompact.bddAbove [ClosedIciTopology α] [Nonempty α] {s : Set α} (hs : IsCompact s) :
    BddAbove s :=
  IsCompact.bddBelow (α := αᵒᵈ) hs

/-- A continuous function is bounded below on a compact set. -/
theorem IsCompact.bddBelow_image [ClosedIicTopology α] [Nonempty α] {f : β → α} {K : Set β}
    (hK : IsCompact K) (hf : ContinuousOn f K) : BddBelow (f '' K) :=
  (hK.image_of_continuousOn hf).bddBelow

/-- A continuous function is bounded above on a compact set. -/
theorem IsCompact.bddAbove_image [ClosedIciTopology α] [Nonempty α] {f : β → α} {K : Set β}
    (hK : IsCompact K) (hf : ContinuousOn f K) : BddAbove (f '' K) :=
  IsCompact.bddBelow_image (α := αᵒᵈ) hK hf

/-- A continuous function with compact support is bounded below. -/
@[to_additive /-- A continuous function with compact support is bounded below. -/]
theorem Continuous.bddBelow_range_of_hasCompactMulSupport [ClosedIicTopology α] [One α]
    {f : β → α} (hf : Continuous f) (h : HasCompactMulSupport f) : BddBelow (range f) :=
  (h.isCompact_range hf).bddBelow

/-- A continuous function with compact support is bounded above. -/
@[to_additive /-- A continuous function with compact support is bounded above. -/]
theorem Continuous.bddAbove_range_of_hasCompactMulSupport [ClosedIciTopology α] [One α]
    {f : β → α} (hf : Continuous f) (h : HasCompactMulSupport f) : BddAbove (range f) :=
  Continuous.bddBelow_range_of_hasCompactMulSupport (α := αᵒᵈ) hf h

end LinearOrder

section ConditionallyCompleteLinearOrder

variable {α β γ : Type*} [ConditionallyCompleteLinearOrder α] [TopologicalSpace α]
  [TopologicalSpace β] [TopologicalSpace γ]

theorem IsCompact.sSup_lt_iff_of_continuous [ClosedIciTopology α] {f : β → α} {K : Set β}
    (hK : IsCompact K) (h0K : K.Nonempty) (hf : ContinuousOn f K) (y : α) :
    sSup (f '' K) < y ↔ ∀ x ∈ K, f x < y := by
  refine ⟨fun h x hx => (le_csSup (hK.bddAbove_image hf) <| mem_image_of_mem f hx).trans_lt h,
    fun h => ?_⟩
  obtain ⟨x, hx, h2x⟩ := hK.exists_isMaxOn h0K hf
  refine (csSup_le (h0K.image f) ?_).trans_lt (h x hx)
  rintro _ ⟨x', hx', rfl⟩; exact h2x hx'

theorem IsCompact.lt_sInf_iff_of_continuous [ClosedIicTopology α] {f : β → α} {K : Set β}
    (hK : IsCompact K) (h0K : K.Nonempty) (hf : ContinuousOn f K) (y : α) :
    y < sInf (f '' K) ↔ ∀ x ∈ K, y < f x :=
  IsCompact.sSup_lt_iff_of_continuous (α := αᵒᵈ) hK h0K hf y

end ConditionallyCompleteLinearOrder

/-!
### Min and max elements of a compact set
-/

section InfSup

variable {α β : Type*} [ConditionallyCompleteLinearOrder α] [TopologicalSpace α]
  [TopologicalSpace β]

theorem IsCompact.sInf_mem [ClosedIicTopology α] {s : Set α} (hs : IsCompact s)
    (ne_s : s.Nonempty) : sInf s ∈ s :=
  let ⟨_a, ha⟩ := hs.exists_isLeast ne_s
  ha.csInf_mem

theorem IsCompact.sSup_mem [ClosedIciTopology α] {s : Set α} (hs : IsCompact s)
    (ne_s : s.Nonempty) : sSup s ∈ s :=
  IsCompact.sInf_mem (α := αᵒᵈ) hs ne_s

theorem IsCompact.isGLB_sInf [ClosedIicTopology α] {s : Set α} (hs : IsCompact s)
    (ne_s : s.Nonempty) : IsGLB s (sInf s) :=
  isGLB_csInf ne_s hs.bddBelow

theorem IsCompact.isLUB_sSup [ClosedIciTopology α] {s : Set α} (hs : IsCompact s)
    (ne_s : s.Nonempty) : IsLUB s (sSup s) :=
  IsCompact.isGLB_sInf (α := αᵒᵈ) hs ne_s

theorem IsCompact.isLeast_sInf [ClosedIicTopology α] {s : Set α} (hs : IsCompact s)
    (ne_s : s.Nonempty) : IsLeast s (sInf s) :=
  ⟨hs.sInf_mem ne_s, (hs.isGLB_sInf ne_s).1⟩

theorem IsCompact.isGreatest_sSup [ClosedIciTopology α] {s : Set α} (hs : IsCompact s)
    (ne_s : s.Nonempty) : IsGreatest s (sSup s) :=
  IsCompact.isLeast_sInf (α := αᵒᵈ) hs ne_s

theorem IsCompact.exists_sInf_image_eq_and_le [ClosedIicTopology α] {s : Set β}
    (hs : IsCompact s) (ne_s : s.Nonempty) {f : β → α} (hf : ContinuousOn f s) :
    ∃ x ∈ s, sInf (f '' s) = f x ∧ ∀ y ∈ s, f x ≤ f y :=
  let ⟨x, hxs, hx⟩ := (hs.image_of_continuousOn hf).sInf_mem (ne_s.image f)
  ⟨x, hxs, hx.symm, fun _y hy =>
    hx.trans_le <| csInf_le (hs.image_of_continuousOn hf).bddBelow <| mem_image_of_mem f hy⟩

theorem IsCompact.exists_sSup_image_eq_and_ge [ClosedIciTopology α] {s : Set β}
    (hs : IsCompact s) (ne_s : s.Nonempty) {f : β → α} (hf : ContinuousOn f s) :
    ∃ x ∈ s, sSup (f '' s) = f x ∧ ∀ y ∈ s, f y ≤ f x :=
  IsCompact.exists_sInf_image_eq_and_le (α := αᵒᵈ) hs ne_s hf

theorem IsCompact.exists_sInf_image_eq [ClosedIicTopology α] {s : Set β} (hs : IsCompact s)
    (ne_s : s.Nonempty) {f : β → α} (hf : ContinuousOn f s) : ∃ x ∈ s, sInf (f '' s) = f x :=
  let ⟨x, hxs, hx, _⟩ := hs.exists_sInf_image_eq_and_le ne_s hf
  ⟨x, hxs, hx⟩

theorem IsCompact.exists_sSup_image_eq [ClosedIciTopology α] {s : Set β} (hs : IsCompact s)
    (ne_s : s.Nonempty) : ∀ {f : β → α}, ContinuousOn f s → ∃ x ∈ s, sSup (f '' s) = f x :=
  IsCompact.exists_sInf_image_eq (α := αᵒᵈ) hs ne_s

end InfSup

section ExistsExtr

variable {α β : Type*} [LinearOrder α] [TopologicalSpace α] [TopologicalSpace β]

theorem IsCompact.exists_isMinOn_mem_subset [ClosedIicTopology α] {f : β → α} {s t : Set β}
    {z : β} (ht : IsCompact t) (hf : ContinuousOn f t) (hz : z ∈ t)
    (hfz : ∀ z' ∈ t \ s, f z < f z') : ∃ x ∈ s, IsMinOn f t x :=
  let ⟨x, hxt, hfx⟩ := ht.exists_isMinOn ⟨z, hz⟩ hf
  ⟨x, by_contra fun hxs => (hfz x ⟨hxt, hxs⟩).not_ge (hfx hz), hfx⟩

theorem IsCompact.exists_isMaxOn_mem_subset [ClosedIciTopology α] {f : β → α} {s t : Set β}
    {z : β} (ht : IsCompact t) (hf : ContinuousOn f t) (hz : z ∈ t)
    (hfz : ∀ z' ∈ t \ s, f z' < f z) : ∃ x ∈ s, IsMaxOn f t x :=
  let ⟨x, hxt, hfx⟩ := ht.exists_isMaxOn ⟨z, hz⟩ hf
  ⟨x, by_contra fun hxs => (hfz x ⟨hxt, hxs⟩).not_ge (hfx hz), hfx⟩

-- TODO: we could assume `t ∈ 𝓝ˢ s` (a.k.a. `s ⊆ interior t`) instead of `s ⊆ t` and `IsOpen s`.
theorem IsCompact.exists_isLocalMin_mem_open [ClosedIicTopology α] {f : β → α} {s t : Set β}
    {z : β} (ht : IsCompact t) (hst : s ⊆ t) (hf : ContinuousOn f t) (hz : z ∈ t)
    (hfz : ∀ z' ∈ t \ s, f z < f z') (hs : IsOpen s) : ∃ x ∈ s, IsLocalMin f x :=
  let ⟨x, hxs, h⟩ := ht.exists_isMinOn_mem_subset hf hz hfz
  ⟨x, hxs, h.isLocalMin <| mem_nhds_iff.2 ⟨s, hst, hs, hxs⟩⟩

theorem IsCompact.exists_isLocalMax_mem_open [ClosedIciTopology α] {f : β → α} {s t : Set β}
    {z : β} (ht : IsCompact t) (hst : s ⊆ t) (hf : ContinuousOn f t) (hz : z ∈ t)
    (hfz : ∀ z' ∈ t \ s, f z' < f z) (hs : IsOpen s) : ∃ x ∈ s, IsLocalMax f x :=
  let ⟨x, hxs, h⟩ := ht.exists_isMaxOn_mem_subset hf hz hfz
  ⟨x, hxs, h.isLocalMax <| mem_nhds_iff.2 ⟨s, hst, hs, hxs⟩⟩

end ExistsExtr

variable {α β γ : Type*} [ConditionallyCompleteLinearOrder α] [TopologicalSpace α]
  [OrderTopology α] [TopologicalSpace β] [TopologicalSpace γ]

theorem eq_Icc_of_connected_compact {s : Set α} (h₁ : IsConnected s) (h₂ : IsCompact s) :
    s = Icc (sInf s) (sSup s) :=
  eq_Icc_csInf_csSup_of_connected_bdd_closed h₁ h₂.bddBelow h₂.bddAbove h₂.isClosed

/-- If `f : γ → β → α` is a function that is continuous as a function on `γ × β`, `α` is a
conditionally complete linear order, and `K : Set β` is a compact set, then
`fun x ↦ sSup (f x '' K)` is a continuous function. -/
/- TODO: generalize. The following version seems to be true:
```
theorem IsCompact.tendsto_sSup {f : γ → β → α} {g : β → α} {K : Set β} {l : Filter γ}
    (hK : IsCompact K) (hf : ∀ y ∈ K, Tendsto ↿f (l ×ˢ 𝓝[K] y) (𝓝 (g y)))
    (hgc : ContinuousOn g K) :
    Tendsto (fun x => sSup (f x '' K)) l (𝓝 (sSup (g '' K))) := _
```
Moreover, it seems that `hgc` follows from `hf` (Yury Kudryashov). -/
theorem IsCompact.continuous_sSup {f : γ → β → α} {K : Set β} (hK : IsCompact K)
    (hf : Continuous ↿f) : Continuous fun x => sSup (f x '' K) := by
  rcases eq_empty_or_nonempty K with (rfl | h0K)
  · simp_rw [image_empty]
    exact Continuous.const
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨y, hyK, h2y, hy⟩ :=
    hK.exists_sSup_image_eq_and_ge h0K
      (show Continuous (f x) from hf.comp <| .prodMk_right x).continuousOn
  rw [ContinuousAt, h2y, tendsto_order]
  have := tendsto_order.mp ((show Continuous fun x => f x y
    from hf.comp <| .prodMk_left _).tendsto x)
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · refine (this.1 z hz).mono fun x' hx' =>
      hx'.trans_le <| le_csSup ?_ <| mem_image_of_mem (f x') hyK
    exact hK.bddAbove_image (hf.comp <| .prodMk_right x').continuousOn
  · have h : ({x} : Set γ) ×ˢ K ⊆ ↿f ⁻¹' Iio z := by
      rintro ⟨x', y'⟩ ⟨(rfl : x' = x), hy'⟩
      exact (hy y' hy').trans_lt hz
    obtain ⟨u, v, hu, _, hxu, hKv, huv⟩ :=
      generalized_tube_lemma isCompact_singleton hK (isOpen_Iio.preimage hf) h
    refine eventually_of_mem (hu.mem_nhds (singleton_subset_iff.mp hxu)) fun x' hx' => ?_
    rw [hK.sSup_lt_iff_of_continuous h0K
        (show Continuous (f x') from hf.comp <| .prodMk_right x').continuousOn]
    exact fun y' hy' => huv (mk_mem_prod hx' (hKv hy'))

theorem IsCompact.continuous_sInf {f : γ → β → α} {K : Set β} (hK : IsCompact K)
    (hf : Continuous ↿f) : Continuous fun x => sInf (f x '' K) :=
  IsCompact.continuous_sSup (α := αᵒᵈ) hK hf

namespace ContinuousOn

/-!
### Image of a closed interval
-/

variable [DenselyOrdered α] [ConditionallyCompleteLinearOrder β] [OrderTopology β] {f : α → β}
  {a b c : α}

open scoped Interval

theorem image_Icc (hab : a ≤ b) (h : ContinuousOn f <| Icc a b) :
    f '' Icc a b = Icc (sInf <| f '' Icc a b) (sSup <| f '' Icc a b) :=
  eq_Icc_of_connected_compact ⟨(nonempty_Icc.2 hab).image f, isPreconnected_Icc.image f h⟩
    (isCompact_Icc.image_of_continuousOn h)

theorem image_uIcc_eq_Icc (h : ContinuousOn f [[a, b]]) :
    f '' [[a, b]] = Icc (sInf (f '' [[a, b]])) (sSup (f '' [[a, b]])) :=
  image_Icc min_le_max h

theorem image_uIcc (h : ContinuousOn f <| [[a, b]]) :
    f '' [[a, b]] = [[sInf (f '' [[a, b]]), sSup (f '' [[a, b]])]] := by
  refine h.image_uIcc_eq_Icc.trans (uIcc_of_le ?_).symm
  refine csInf_le_csSup (nonempty_uIcc.image _) ?_ ?_ <;> rw [h.image_uIcc_eq_Icc]
  exacts [bddBelow_Icc, bddAbove_Icc]

theorem sInf_image_Icc_le (h : ContinuousOn f <| Icc a b) (hc : c ∈ Icc a b) :
    sInf (f '' Icc a b) ≤ f c := by
  have := mem_image_of_mem f hc
  rw [h.image_Icc (hc.1.trans hc.2)] at this
  exact this.1

theorem le_sSup_image_Icc (h : ContinuousOn f <| Icc a b) (hc : c ∈ Icc a b) :
    f c ≤ sSup (f '' Icc a b) := by
  have := mem_image_of_mem f hc
  rw [h.image_Icc (hc.1.trans hc.2)] at this
  exact this.2

theorem image_Icc_of_monotoneOn (hab : a ≤ b) (h : ContinuousOn f <| Icc a b)
    (h' : MonotoneOn f <| Icc a b) : f '' Icc a b = Icc (f a) (f b) := by
  rw [h.image_Icc hab]
  congr!
  · exact h'.sInf_image_Icc hab
  · exact h'.sSup_image_Icc hab

theorem image_Icc_of_antitoneOn (hab : a ≤ b) (h : ContinuousOn f <| Icc a b)
    (h' : AntitoneOn f <| Icc a b) : f '' Icc a b = Icc (f b) (f a) := by
  have : Icc (f b) (f a) = Icc (toDual (f a)) (toDual (f b)) := by rw [Icc_toDual]; rfl
  rw [this]
  exact image_Icc_of_monotoneOn (β := βᵒᵈ) hab h h'.dual_right

end ContinuousOn
