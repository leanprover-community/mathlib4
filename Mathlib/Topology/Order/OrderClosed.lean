/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
module

public import Mathlib.Topology.Order.LeftRight
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Order-closed topologies

In this file we introduce 3 typeclass mixins that relate topology and order structures:

- `ClosedIicTopology` says that all the intervals $(-∞, a]$ (formally, `Set.Iic a`)
  are closed sets;
- `ClosedIciTopology` says that all the intervals $[a, +∞)$ (formally, `Set.Ici a`)
  are closed sets;
- `OrderClosedTopology` says that the set of points `(x, y)` such that `x ≤ y`
  is closed in the product topology.

The last predicate implies the first two.

We prove many basic properties of such topologies.

## Main statements

This file contains the proofs of the following facts.
For exact requirements
(`OrderClosedTopology` vs `ClosedIciTopology` vs `ClosedIicTopology`,
`Preorder` vs `PartialOrder` vs `LinearOrder`, etc.)
see their statements.

### Open / closed sets

* `isOpen_lt` : if `f` and `g` are continuous functions, then `{x | f x < g x}` is open;
* `isOpen_Iio`, `isOpen_Ioi`, `isOpen_Ioo` : open intervals are open;
* `isClosed_le` : if `f` and `g` are continuous functions, then `{x | f x ≤ g x}` is closed;
* `isClosed_Iic`, `isClosed_Ici`, `isClosed_Icc` : closed intervals are closed;
* `frontier_le_subset_eq`, `frontier_lt_subset_eq` : frontiers of both `{x | f x ≤ g x}`
  and `{x | f x < g x}` are included by `{x | f x = g x}`;

### Convergence and inequalities

* `le_of_tendsto_of_tendsto` : if `f` converges to `a`, `g` converges to `b`, and eventually
  `f x ≤ g x`, then `a ≤ b`
* `le_of_tendsto`, `ge_of_tendsto` : if `f` converges to `a` and eventually `f x ≤ b`
  (resp., `b ≤ f x`), then `a ≤ b` (resp., `b ≤ a`); we also provide primed versions
  that assume the inequalities to hold for all `x`.

### Min, max, `sSup` and `sInf`

* `Continuous.min`, `Continuous.max`: pointwise `min`/`max` of two continuous functions is
  continuous.
* `Tendsto.min`, `Tendsto.max` : if `f` tends to `a` and `g` tends to `b`, then their pointwise
  `min`/`max` tend to `min a b` and `max a b`, respectively.
-/

@[expose] public section

open Set Filter TopologicalSpace
open OrderDual (toDual ofDual)
open scoped Topology

universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}

/-- If `α` is a topological space and a preorder, `ClosedIicTopology α` means that `Iic a` is
closed for all `a : α`. -/
class ClosedIicTopology (α : Type*) [TopologicalSpace α] [Preorder α] : Prop where
  /-- For any `a`, the set `(-∞, a]` is closed. -/
  isClosed_Iic (a : α) : IsClosed (Iic a)

/-- If `α` is a topological space and a preorder, `ClosedIciTopology α` means that `Ici a` is
closed for all `a : α`. -/
class ClosedIciTopology (α : Type*) [TopologicalSpace α] [Preorder α] : Prop where
  /-- For any `a`, the set `[a, +∞)` is closed. -/
  isClosed_Ici (a : α) : IsClosed (Ici a)

/-- A topology on a set which is both a topological space and a preorder is _order-closed_ if the
set of points `(x, y)` with `x ≤ y` is closed in the product space. We introduce this as a mixin.
This property is satisfied for the order topology on a linear order, but it can be satisfied more
generally, and suffices to derive many interesting properties relating order and topology. -/
class OrderClosedTopology (α : Type*) [TopologicalSpace α] [Preorder α] : Prop where
  /-- The set `{ (x, y) | x ≤ y }` is a closed set. -/
  isClosed_le' : IsClosed { p : α × α | p.1 ≤ p.2 }

private theorem isInducing_ofDual' [TopologicalSpace α] :
    Topology.IsInducing (ofDual : αᵒᵈ → α) := ⟨rfl⟩
instance [TopologicalSpace α] [FirstCountableTopology α] : FirstCountableTopology αᵒᵈ :=
  isInducing_ofDual'.firstCountableTopology
instance [TopologicalSpace α] [SecondCountableTopology α] : SecondCountableTopology αᵒᵈ :=
  isInducing_ofDual'.secondCountableTopology
instance [TopologicalSpace α] [SeparableSpace α] : SeparableSpace αᵒᵈ :=
  isOpenMap_ofDual.separableSpace_of_isInducing isInducing_ofDual'

theorem Dense.orderDual [TopologicalSpace α] {s : Set α} (hs : Dense s) :
    Dense (OrderDual.ofDual ⁻¹' s) :=
  hs.preimage isOpenMap_ofDual

section General
variable [TopologicalSpace α] [Preorder α] {s : Set α}

protected lemma BddAbove.of_closure : BddAbove (closure s) → BddAbove s :=
  BddAbove.mono subset_closure

protected lemma BddBelow.of_closure : BddBelow (closure s) → BddBelow s :=
  BddBelow.mono subset_closure

end General

section ClosedIicTopology

section Preorder

variable [TopologicalSpace α] [Preorder α] [ClosedIicTopology α] {f : β → α} {a b : α} {s : Set α}

theorem isClosed_Iic : IsClosed (Iic a) :=
  ClosedIicTopology.isClosed_Iic a

instance : ClosedIciTopology αᵒᵈ where
  isClosed_Ici a := by
    have : Ici a = ofDual ⁻¹' Iic (ofDual a) := by
      ext x; simp [Ici, Iic, OrderDual.ofDual_le_ofDual]
    rw [this]
    exact (isClosed_Iic (α := α)).preimage continuous_ofDual

@[simp]
theorem closure_Iic (a : α) : closure (Iic a) = Iic a :=
  isClosed_Iic.closure_eq

theorem le_of_tendsto_of_frequently {x : Filter β} (lim : Tendsto f x (𝓝 a))
    (h : ∃ᶠ c in x, f c ≤ b) : a ≤ b :=
  isClosed_Iic.mem_of_frequently_of_tendsto h lim

theorem le_of_tendsto {x : Filter β} [NeBot x] (lim : Tendsto f x (𝓝 a))
    (h : ∀ᶠ c in x, f c ≤ b) : a ≤ b :=
  isClosed_Iic.mem_of_tendsto lim h

theorem le_of_tendsto' {x : Filter β} [NeBot x] (lim : Tendsto f x (𝓝 a))
    (h : ∀ c, f c ≤ b) : a ≤ b :=
  le_of_tendsto lim (Eventually.of_forall h)

@[simp] lemma upperBounds_closure (s : Set α) : upperBounds (closure s : Set α) = upperBounds s :=
  ext fun a ↦ by simp_rw [mem_upperBounds_iff_subset_Iic, isClosed_Iic.closure_subset_iff]

@[simp] lemma bddAbove_closure : BddAbove (closure s) ↔ BddAbove s := by
  simp_rw [BddAbove, upperBounds_closure]

protected alias ⟨_, BddAbove.closure⟩ := bddAbove_closure

@[simp]
theorem disjoint_nhds_atBot_iff : Disjoint (𝓝 a) atBot ↔ ¬IsBot a := by
  constructor
  · intro hd hbot
    rw [hbot.atBot_eq, disjoint_principal_right] at hd
    exact mem_of_mem_nhds hd le_rfl
  · simp only [IsBot, not_forall]
    rintro ⟨b, hb⟩
    refine disjoint_of_disjoint_of_mem disjoint_compl_left ?_ (Iic_mem_atBot b)
    exact isClosed_Iic.isOpen_compl.mem_nhds hb

theorem IsLUB.range_of_tendsto {F : Filter β} [F.NeBot] (hle : ∀ i, f i ≤ a)
    (hlim : Tendsto f F (𝓝 a)) : IsLUB (range f) a :=
  ⟨forall_mem_range.mpr hle, fun _c hc ↦ le_of_tendsto' hlim fun i ↦ hc <| mem_range_self i⟩

end Preorder

section NoBotOrder

variable [Preorder α] [NoBotOrder α] [TopologicalSpace α] [ClosedIicTopology α] {a : α}
  {l : Filter β} [NeBot l] {f : β → α}

theorem disjoint_nhds_atBot (a : α) : Disjoint (𝓝 a) atBot := by simp

@[simp]
theorem inf_nhds_atBot (a : α) : 𝓝 a ⊓ atBot = ⊥ := (disjoint_nhds_atBot a).eq_bot

theorem not_tendsto_nhds_of_tendsto_atBot (hf : Tendsto f l atBot) (a : α) : ¬Tendsto f l (𝓝 a) :=
  hf.not_tendsto (disjoint_nhds_atBot a).symm

theorem not_tendsto_atBot_of_tendsto_nhds (hf : Tendsto f l (𝓝 a)) : ¬Tendsto f l atBot :=
  hf.not_tendsto (disjoint_nhds_atBot a)

end NoBotOrder

theorem iSup_eq_of_forall_le_of_tendsto {ι : Type*} {F : Filter ι} [Filter.NeBot F]
    [ConditionallyCompleteLattice α] [TopologicalSpace α] [ClosedIicTopology α]
    {a : α} {f : ι → α} (hle : ∀ i, f i ≤ a) (hlim : Filter.Tendsto f F (𝓝 a)) :
    ⨆ i, f i = a :=
  have := F.nonempty_of_neBot
  (IsLUB.range_of_tendsto hle hlim).ciSup_eq

theorem iUnion_Iic_eq_Iio_of_lt_of_tendsto {ι : Type*} {F : Filter ι} [F.NeBot]
    [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [ClosedIicTopology α]
    {a : α} {f : ι → α} (hlt : ∀ i, f i < a) (hlim : Tendsto f F (𝓝 a)) :
    ⋃ i : ι, Iic (f i) = Iio a := by
  have obs : a ∉ range f := by
    rw [mem_range]
    rintro ⟨i, rfl⟩
    exact (hlt i).false
  rw [← biUnion_range, (IsLUB.range_of_tendsto (le_of_lt <| hlt ·) hlim).biUnion_Iic_eq_Iio obs]

section LinearOrder

variable [TopologicalSpace α] [LinearOrder α] [ClosedIicTopology α] [TopologicalSpace β]
  {a b c : α} {f : α → β}

theorem isOpen_Ioi : IsOpen (Ioi a) := by
  rw [← compl_Iic]
  exact isClosed_Iic.isOpen_compl

@[simp]
theorem interior_Ioi : interior (Ioi a) = Ioi a :=
  isOpen_Ioi.interior_eq

theorem Ioi_mem_nhds (h : a < b) : Ioi a ∈ 𝓝 b := IsOpen.mem_nhds isOpen_Ioi h

theorem eventually_gt_nhds (hab : b < a) : ∀ᶠ x in 𝓝 a, b < x := Ioi_mem_nhds hab

theorem Ici_mem_nhds (h : a < b) : Ici a ∈ 𝓝 b :=
  mem_of_superset (Ioi_mem_nhds h) Ioi_subset_Ici_self

theorem eventually_ge_nhds (hab : b < a) : ∀ᶠ x in 𝓝 a, b ≤ x := Ici_mem_nhds hab

theorem Filter.Tendsto.eventually_const_lt {l : Filter γ} {f : γ → α} {u v : α} (hv : u < v)
    (h : Filter.Tendsto f l (𝓝 v)) : ∀ᶠ a in l, u < f a :=
  h.eventually <| eventually_gt_nhds hv

theorem Filter.Tendsto.eventually_const_le {l : Filter γ} {f : γ → α} {u v : α} (hv : u < v)
    (h : Tendsto f l (𝓝 v)) : ∀ᶠ a in l, u ≤ f a :=
  h.eventually <| eventually_ge_nhds hv

protected theorem Dense.exists_gt [NoMaxOrder α] {s : Set α} (hs : Dense s) (x : α) :
    ∃ y ∈ s, x < y :=
  hs.exists_mem_open isOpen_Ioi (exists_gt x)

protected theorem Dense.exists_ge [NoMaxOrder α] {s : Set α} (hs : Dense s) (x : α) :
    ∃ y ∈ s, x ≤ y :=
  (hs.exists_gt x).imp fun _ h ↦ ⟨h.1, h.2.le⟩

theorem Dense.exists_ge' {s : Set α} (hs : Dense s) (htop : ∀ x, IsTop x → x ∈ s) (x : α) :
    ∃ y ∈ s, x ≤ y := by
  by_cases hx : IsTop x
  · exact ⟨x, htop x hx, le_rfl⟩
  · simp only [IsTop, not_forall, not_le] at hx
    rcases hs.exists_mem_open isOpen_Ioi hx with ⟨y, hys, hy : x < y⟩
    exact ⟨y, hys, hy.le⟩

/-!
### Left neighborhoods on a `ClosedIicTopology`

Limits to the left of real functions are defined in terms of neighborhoods to the left,
either open or closed, i.e., members of `𝓝[<] a` and `𝓝[≤] a`.
Here we prove that all left-neighborhoods of a point are equal,
and we prove other useful characterizations which require the stronger hypothesis `OrderTopology α`
in another file.
-/

/-!
#### Point excluded
-/

theorem Ioo_mem_nhdsLT (H : a < b) : Ioo a b ∈ 𝓝[<] b := by
  simpa only [← Iio_inter_Ioi] using inter_mem_nhdsWithin _ (Ioi_mem_nhds H)

theorem Ioo_mem_nhdsLT_of_mem (H : b ∈ Ioc a c) : Ioo a c ∈ 𝓝[<] b :=
  mem_of_superset (Ioo_mem_nhdsLT H.1) <| Ioo_subset_Ioo_right H.2

protected theorem CovBy.nhdsLT (h : a ⋖ b) : 𝓝[<] b = ⊥ :=
  empty_mem_iff_bot.mp <| h.Ioo_eq ▸ Ioo_mem_nhdsLT h.1

protected theorem PredOrder.nhdsLT [PredOrder α] : 𝓝[<] a = ⊥ := by
  if h : IsMin a then simp [h.Iio_eq]
  else exact (Order.pred_covBy_of_not_isMin h).nhdsLT

theorem PredOrder.nhdsGT_eq_nhdsNE [PredOrder α] (a : α) : 𝓝[>] a = 𝓝[≠] a := by
  rw [← nhdsLT_sup_nhdsGT, PredOrder.nhdsLT, bot_sup_eq]

theorem PredOrder.nhdsGE_eq_nhds [PredOrder α] (a : α) : 𝓝[≥] a = 𝓝 a := by
  rw [← nhdsLT_sup_nhdsGE, PredOrder.nhdsLT, bot_sup_eq]

theorem Ico_mem_nhdsLT_of_mem (H : b ∈ Ioc a c) : Ico a c ∈ 𝓝[<] b :=
  mem_of_superset (Ioo_mem_nhdsLT_of_mem H) Ioo_subset_Ico_self

theorem Ico_mem_nhdsLT (H : a < b) : Ico a b ∈ 𝓝[<] b := Ico_mem_nhdsLT_of_mem ⟨H, le_rfl⟩

theorem Ioc_mem_nhdsLT_of_mem (H : b ∈ Ioc a c) : Ioc a c ∈ 𝓝[<] b :=
  mem_of_superset (Ioo_mem_nhdsLT_of_mem H) Ioo_subset_Ioc_self

theorem Ioc_mem_nhdsLT (H : a < b) : Ioc a b ∈ 𝓝[<] b := Ioc_mem_nhdsLT_of_mem ⟨H, le_rfl⟩

theorem Icc_mem_nhdsLT_of_mem (H : b ∈ Ioc a c) : Icc a c ∈ 𝓝[<] b :=
  mem_of_superset (Ioo_mem_nhdsLT_of_mem H) Ioo_subset_Icc_self

theorem Icc_mem_nhdsLT (H : a < b) : Icc a b ∈ 𝓝[<] b := Icc_mem_nhdsLT_of_mem ⟨H, le_rfl⟩

@[simp]
theorem nhdsWithin_Ico_eq_nhdsLT (h : a < b) : 𝓝[Ico a b] b = 𝓝[<] b :=
  nhdsWithin_inter_of_mem <| nhdsWithin_le_nhds <| Ici_mem_nhds h

@[simp]
theorem nhdsWithin_Ioo_eq_nhdsLT (h : a < b) : 𝓝[Ioo a b] b = 𝓝[<] b :=
  nhdsWithin_inter_of_mem <| nhdsWithin_le_nhds <| Ioi_mem_nhds h

@[simp]
theorem continuousWithinAt_Ico_iff_Iio (h : a < b) :
    ContinuousWithinAt f (Ico a b) b ↔ ContinuousWithinAt f (Iio b) b := by
  simp only [ContinuousWithinAt, nhdsWithin_Ico_eq_nhdsLT h]

@[simp]
theorem continuousWithinAt_Ioo_iff_Iio (h : a < b) :
    ContinuousWithinAt f (Ioo a b) b ↔ ContinuousWithinAt f (Iio b) b := by
  simp only [ContinuousWithinAt, nhdsWithin_Ioo_eq_nhdsLT h]

/-!
#### Point included
-/

protected theorem CovBy.nhdsLE (H : a ⋖ b) : 𝓝[≤] b = pure b := by
  rw [← Iio_insert, nhdsWithin_insert, H.nhdsLT, sup_bot_eq]

protected theorem PredOrder.nhdsLE [PredOrder α] : 𝓝[≤] b = pure b := by
  rw [← Iio_insert, nhdsWithin_insert, PredOrder.nhdsLT, sup_bot_eq]

theorem Ioc_mem_nhdsLE (H : a < b) : Ioc a b ∈ 𝓝[≤] b :=
  inter_mem (nhdsWithin_le_nhds <| Ioi_mem_nhds H) self_mem_nhdsWithin

theorem Ioo_mem_nhdsLE_of_mem (H : b ∈ Ioo a c) : Ioo a c ∈ 𝓝[≤] b :=
  mem_of_superset (Ioc_mem_nhdsLE H.1) <| Ioc_subset_Ioo_right H.2

theorem Ico_mem_nhdsLE_of_mem (H : b ∈ Ioo a c) : Ico a c ∈ 𝓝[≤] b :=
  mem_of_superset (Ioo_mem_nhdsLE_of_mem H) Ioo_subset_Ico_self

theorem Ioc_mem_nhdsLE_of_mem (H : b ∈ Ioc a c) : Ioc a c ∈ 𝓝[≤] b :=
  mem_of_superset (Ioc_mem_nhdsLE H.1) <| Ioc_subset_Ioc_right H.2

theorem Icc_mem_nhdsLE_of_mem (H : b ∈ Ioc a c) : Icc a c ∈ 𝓝[≤] b :=
  mem_of_superset (Ioc_mem_nhdsLE_of_mem H) Ioc_subset_Icc_self

theorem Icc_mem_nhdsLE (H : a < b) : Icc a b ∈ 𝓝[≤] b := Icc_mem_nhdsLE_of_mem ⟨H, le_rfl⟩

@[simp]
theorem nhdsWithin_Icc_eq_nhdsLE (h : a < b) : 𝓝[Icc a b] b = 𝓝[≤] b :=
  nhdsWithin_inter_of_mem <| nhdsWithin_le_nhds <| Ici_mem_nhds h

@[simp]
theorem nhdsWithin_Ioc_eq_nhdsLE (h : a < b) : 𝓝[Ioc a b] b = 𝓝[≤] b :=
  nhdsWithin_inter_of_mem <| nhdsWithin_le_nhds <| Ioi_mem_nhds h

@[simp]
theorem continuousWithinAt_Icc_iff_Iic (h : a < b) :
    ContinuousWithinAt f (Icc a b) b ↔ ContinuousWithinAt f (Iic b) b := by
  simp only [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsLE h]

@[simp]
theorem continuousWithinAt_Ioc_iff_Iic (h : a < b) :
    ContinuousWithinAt f (Ioc a b) b ↔ ContinuousWithinAt f (Iic b) b := by
  simp only [ContinuousWithinAt, nhdsWithin_Ioc_eq_nhdsLE h]

end LinearOrder

end ClosedIicTopology

section ClosedIciTopology

section Preorder

variable [TopologicalSpace α] [Preorder α] [ClosedIciTopology α] {f : β → α} {a b : α} {s : Set α}

theorem isClosed_Ici {a : α} : IsClosed (Ici a) :=
  ClosedIciTopology.isClosed_Ici a

instance : ClosedIicTopology αᵒᵈ where
  isClosed_Iic a := by
    have : Iic a = ofDual ⁻¹' Ici (ofDual a) := by
      ext x; simp [Iic, Ici, OrderDual.ofDual_le_ofDual]
    rw [this]
    exact (isClosed_Ici (α := α)).preimage continuous_ofDual

@[simp]
theorem closure_Ici (a : α) : closure (Ici a) = Ici a :=
  isClosed_Ici.closure_eq

lemma ge_of_tendsto_of_frequently {x : Filter β} (lim : Tendsto f x (𝓝 a))
    (h : ∃ᶠ c in x, b ≤ f c) : b ≤ a :=
  isClosed_Ici.mem_of_frequently_of_tendsto h lim

theorem ge_of_tendsto {x : Filter β} [NeBot x] (lim : Tendsto f x (𝓝 a))
    (h : ∀ᶠ c in x, b ≤ f c) : b ≤ a :=
  isClosed_Ici.mem_of_tendsto lim h

theorem ge_of_tendsto' {x : Filter β} [NeBot x] (lim : Tendsto f x (𝓝 a))
    (h : ∀ c, b ≤ f c) : b ≤ a :=
  ge_of_tendsto lim (Eventually.of_forall h)

@[simp] lemma lowerBounds_closure (s : Set α) : lowerBounds (closure s : Set α) = lowerBounds s :=
  ext fun a ↦ by simp_rw [mem_lowerBounds_iff_subset_Ici, isClosed_Ici.closure_subset_iff]

@[simp] lemma bddBelow_closure : BddBelow (closure s) ↔ BddBelow s := by
  simp_rw [BddBelow, lowerBounds_closure]

protected alias ⟨_, BddBelow.closure⟩ := bddBelow_closure

@[simp]
theorem disjoint_nhds_atTop_iff : Disjoint (𝓝 a) atTop ↔ ¬IsTop a := by
  constructor
  · intro hd htop
    rw [htop.atTop_eq, disjoint_principal_right] at hd
    exact mem_of_mem_nhds hd le_rfl
  · simp only [IsTop, not_forall]
    rintro ⟨b, hb⟩
    refine disjoint_of_disjoint_of_mem disjoint_compl_left ?_ (Ici_mem_atTop b)
    exact isClosed_Ici.isOpen_compl.mem_nhds hb

theorem IsGLB.range_of_tendsto {F : Filter β} [F.NeBot] (hle : ∀ i, a ≤ f i)
    (hlim : Tendsto f F (𝓝 a)) : IsGLB (range f) a :=
  ⟨forall_mem_range.mpr hle, fun _c hc ↦ ge_of_tendsto' hlim fun i ↦ hc <| mem_range_self i⟩

end Preorder

section NoTopOrder

variable [Preorder α] [NoTopOrder α] [TopologicalSpace α] [ClosedIciTopology α] {a : α}
  {l : Filter β} [NeBot l] {f : β → α}

theorem disjoint_nhds_atTop (a : α) : Disjoint (𝓝 a) atTop := by simp

@[simp]
theorem inf_nhds_atTop (a : α) : 𝓝 a ⊓ atTop = ⊥ := (disjoint_nhds_atTop a).eq_bot

theorem not_tendsto_nhds_of_tendsto_atTop (hf : Tendsto f l atTop) (a : α) : ¬Tendsto f l (𝓝 a) :=
  hf.not_tendsto (disjoint_nhds_atTop a).symm

theorem not_tendsto_atTop_of_tendsto_nhds (hf : Tendsto f l (𝓝 a)) : ¬Tendsto f l atTop :=
  hf.not_tendsto (disjoint_nhds_atTop a)

end NoTopOrder

theorem iInf_eq_of_forall_le_of_tendsto {ι : Type*} {F : Filter ι} [F.NeBot]
    [ConditionallyCompleteLattice α] [TopologicalSpace α] [ClosedIciTopology α]
    {a : α} {f : ι → α} (hle : ∀ i, a ≤ f i) (hlim : Tendsto f F (𝓝 a)) :
    ⨅ i, f i = a :=
  have := F.nonempty_of_neBot
  (IsGLB.range_of_tendsto hle hlim).ciInf_eq

theorem iUnion_Ici_eq_Ioi_of_lt_of_tendsto {ι : Type*} {F : Filter ι} [F.NeBot]
    [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [ClosedIciTopology α]
    {a : α} {f : ι → α} (hlt : ∀ i, a < f i) (hlim : Tendsto f F (𝓝 a)) :
    ⋃ i : ι, Ici (f i) = Ioi a := by
  have obs : a ∉ range f := by
    rw [mem_range]
    rintro ⟨i, rfl⟩
    exact (hlt i).false
  rw [← biUnion_range, (IsGLB.range_of_tendsto (le_of_lt <| hlt ·) hlim).biUnion_Ici_eq_Ioi obs]

section LinearOrder

variable [TopologicalSpace α] [LinearOrder α] [ClosedIciTopology α] [TopologicalSpace β]
  {a b c : α} {f : α → β}

theorem isOpen_Iio : IsOpen (Iio a) := by
  rw [← compl_Ici]
  exact isClosed_Ici.isOpen_compl

@[simp] theorem interior_Iio : interior (Iio a) = Iio a := isOpen_Iio.interior_eq

theorem Iio_mem_nhds (h : a < b) : Iio b ∈ 𝓝 a := isOpen_Iio.mem_nhds h

theorem eventually_lt_nhds (hab : a < b) : ∀ᶠ x in 𝓝 a, x < b := Iio_mem_nhds hab

theorem Iic_mem_nhds (h : a < b) : Iic b ∈ 𝓝 a :=
  mem_of_superset (Iio_mem_nhds h) Iio_subset_Iic_self

theorem eventually_le_nhds (hab : a < b) : ∀ᶠ x in 𝓝 a, x ≤ b := Iic_mem_nhds hab

theorem Filter.Tendsto.eventually_lt_const {l : Filter γ} {f : γ → α} {u v : α} (hv : v < u)
    (h : Filter.Tendsto f l (𝓝 v)) : ∀ᶠ a in l, f a < u :=
  h.eventually <| eventually_lt_nhds hv

theorem Filter.Tendsto.eventually_le_const {l : Filter γ} {f : γ → α} {u v : α} (hv : v < u)
    (h : Tendsto f l (𝓝 v)) : ∀ᶠ a in l, f a ≤ u :=
  h.eventually <| eventually_le_nhds hv

protected theorem Dense.exists_lt [NoMinOrder α] {s : Set α} (hs : Dense s) (x : α) :
    ∃ y ∈ s, y < x :=
  hs.exists_mem_open isOpen_Iio (exists_lt x)

protected theorem Dense.exists_le [NoMinOrder α] {s : Set α} (hs : Dense s) (x : α) :
    ∃ y ∈ s, y ≤ x :=
  (hs.exists_lt x).imp fun _ h ↦ ⟨h.1, h.2.le⟩

theorem Dense.exists_le' {s : Set α} (hs : Dense s) (hbot : ∀ x, IsBot x → x ∈ s) (x : α) :
    ∃ y ∈ s, y ≤ x := by
  by_cases hx : IsBot x
  · exact ⟨x, hbot x hx, le_rfl⟩
  · simp only [IsBot, not_forall, not_le] at hx
    rcases hs.exists_mem_open isOpen_Iio hx with ⟨y, hys, hy : y < x⟩
    exact ⟨y, hys, hy.le⟩

/-!
### Right neighborhoods on a `ClosedIciTopology`

Limits to the right of real functions are defined in terms of neighborhoods to the right,
either open or closed, i.e., members of `𝓝[>] a` and `𝓝[≥] a`.
Here we prove that all right-neighborhoods of a point are equal,
and we prove other useful characterizations which require the stronger hypothesis `OrderTopology α`
in another file.
-/

/-!
#### Point excluded
-/


theorem Ioo_mem_nhdsGT_of_mem (H : b ∈ Ico a c) : Ioo a c ∈ 𝓝[>] b :=
  mem_nhdsWithin.2
    ⟨Iio c, isOpen_Iio, H.2, by rw [inter_comm, Ioi_inter_Iio]; exact Ioo_subset_Ioo_left H.1⟩

theorem Ioo_mem_nhdsGT (H : a < b) : Ioo a b ∈ 𝓝[>] a := Ioo_mem_nhdsGT_of_mem ⟨le_rfl, H⟩

protected theorem CovBy.nhdsGT (h : a ⋖ b) : 𝓝[>] a = ⊥ :=
  empty_mem_iff_bot.mp <| h.Ioo_eq ▸ Ioo_mem_nhdsGT h.1

protected theorem SuccOrder.nhdsGT [SuccOrder α] : 𝓝[>] a = ⊥ := by
  if h : IsMax a then simp [h.Ioi_eq]
  else exact (Order.covBy_succ_of_not_isMax h).nhdsGT

theorem SuccOrder.nhdsLT_eq_nhdsNE [SuccOrder α] (a : α) : 𝓝[<] a = 𝓝[≠] a := by
  rw [← nhdsLT_sup_nhdsGT, SuccOrder.nhdsGT, sup_bot_eq]

theorem SuccOrder.nhdsLE_eq_nhds [SuccOrder α] (a : α) : 𝓝[≤] a = 𝓝 a := by
  rw [← nhdsLE_sup_nhdsGT, SuccOrder.nhdsGT, sup_bot_eq]

theorem Ioc_mem_nhdsGT_of_mem (H : b ∈ Ico a c) : Ioc a c ∈ 𝓝[>] b :=
  mem_of_superset (Ioo_mem_nhdsGT_of_mem H) Ioo_subset_Ioc_self

theorem Ioc_mem_nhdsGT (H : a < b) : Ioc a b ∈ 𝓝[>] a := Ioc_mem_nhdsGT_of_mem ⟨le_rfl, H⟩

theorem Ico_mem_nhdsGT_of_mem (H : b ∈ Ico a c) : Ico a c ∈ 𝓝[>] b :=
  mem_of_superset (Ioo_mem_nhdsGT_of_mem H) Ioo_subset_Ico_self

theorem Ico_mem_nhdsGT (H : a < b) : Ico a b ∈ 𝓝[>] a := Ico_mem_nhdsGT_of_mem ⟨le_rfl, H⟩

theorem Icc_mem_nhdsGT_of_mem (H : b ∈ Ico a c) : Icc a c ∈ 𝓝[>] b :=
  mem_of_superset (Ioo_mem_nhdsGT_of_mem H) Ioo_subset_Icc_self

theorem Icc_mem_nhdsGT (H : a < b) : Icc a b ∈ 𝓝[>] a := Icc_mem_nhdsGT_of_mem ⟨le_rfl, H⟩

@[simp]
theorem nhdsWithin_Ioc_eq_nhdsGT (h : a < b) : 𝓝[Ioc a b] a = 𝓝[>] a :=
  nhdsWithin_inter_of_mem' <| nhdsWithin_le_nhds <| Iic_mem_nhds h

@[simp]
theorem nhdsWithin_Ioo_eq_nhdsGT (h : a < b) : 𝓝[Ioo a b] a = 𝓝[>] a :=
  nhdsWithin_inter_of_mem' <| nhdsWithin_le_nhds <| Iio_mem_nhds h

@[simp]
theorem continuousWithinAt_Ioc_iff_Ioi (h : a < b) :
    ContinuousWithinAt f (Ioc a b) a ↔ ContinuousWithinAt f (Ioi a) a := by
  simp only [ContinuousWithinAt, nhdsWithin_Ioc_eq_nhdsGT h]

@[simp]
theorem continuousWithinAt_Ioo_iff_Ioi (h : a < b) :
    ContinuousWithinAt f (Ioo a b) a ↔ ContinuousWithinAt f (Ioi a) a := by
  simp only [ContinuousWithinAt, nhdsWithin_Ioo_eq_nhdsGT h]

/-!
### Point included
-/

protected theorem CovBy.nhdsGE (H : a ⋖ b) : 𝓝[≥] a = pure a := by
  rw [← Ioi_insert, nhdsWithin_insert, H.nhdsGT, sup_bot_eq]

protected theorem SuccOrder.nhdsGE [SuccOrder α] : 𝓝[≥] a = pure a := by
  rw [← Ioi_insert, nhdsWithin_insert, SuccOrder.nhdsGT, sup_bot_eq]

theorem Ico_mem_nhdsGE (H : a < b) : Ico a b ∈ 𝓝[≥] a :=
  inter_mem_nhdsWithin _ <| Iio_mem_nhds H

theorem Ico_mem_nhdsGE_of_mem (H : b ∈ Ico a c) : Ico a c ∈ 𝓝[≥] b :=
  mem_of_superset (Ico_mem_nhdsGE H.2) <| Ico_subset_Ico_left H.1

theorem Ioo_mem_nhdsGE_of_mem (H : b ∈ Ioo a c) : Ioo a c ∈ 𝓝[≥] b :=
  mem_of_superset (Ico_mem_nhdsGE H.2) <| Ico_subset_Ioo_left H.1

theorem Ioc_mem_nhdsGE_of_mem (H : b ∈ Ioo a c) : Ioc a c ∈ 𝓝[≥] b :=
  mem_of_superset (Ioo_mem_nhdsGE_of_mem H) Ioo_subset_Ioc_self

theorem Icc_mem_nhdsGE_of_mem (H : b ∈ Ico a c) : Icc a c ∈ 𝓝[≥] b :=
  mem_of_superset (Ico_mem_nhdsGE_of_mem H) Ico_subset_Icc_self

theorem Icc_mem_nhdsGE (H : a < b) : Icc a b ∈ 𝓝[≥] a := Icc_mem_nhdsGE_of_mem ⟨le_rfl, H⟩

@[simp]
theorem nhdsWithin_Icc_eq_nhdsGE (h : a < b) : 𝓝[Icc a b] a = 𝓝[≥] a :=
  nhdsWithin_inter_of_mem' <| nhdsWithin_le_nhds <| Iic_mem_nhds h

@[simp]
theorem nhdsWithin_Ico_eq_nhdsGE (h : a < b) : 𝓝[Ico a b] a = 𝓝[≥] a :=
  nhdsWithin_inter_of_mem' <| nhdsWithin_le_nhds <| Iio_mem_nhds h

@[simp]
theorem continuousWithinAt_Icc_iff_Ici (h : a < b) :
    ContinuousWithinAt f (Icc a b) a ↔ ContinuousWithinAt f (Ici a) a := by
  simp only [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsGE h]

@[simp]
theorem continuousWithinAt_Ico_iff_Ici (h : a < b) :
    ContinuousWithinAt f (Ico a b) a ↔ ContinuousWithinAt f (Ici a) a := by
  simp only [ContinuousWithinAt, nhdsWithin_Ico_eq_nhdsGE h]

end LinearOrder

end ClosedIciTopology

section OrderClosedTopology

section Preorder

variable [TopologicalSpace α] [Preorder α] [t : OrderClosedTopology α]

namespace Subtype

-- todo: add `OrderEmbedding.orderClosedTopology`
instance {p : α → Prop} : OrderClosedTopology (Subtype p) :=
  have this : Continuous fun p : Subtype p × Subtype p => ((p.fst : α), (p.snd : α)) :=
    continuous_subtype_val.prodMap continuous_subtype_val
  OrderClosedTopology.mk (t.isClosed_le'.preimage this)

end Subtype

theorem isClosed_le_prod : IsClosed { p : α × α | p.1 ≤ p.2 } :=
  t.isClosed_le'

theorem isClosed_le [TopologicalSpace β] {f g : β → α} (hf : Continuous f) (hg : Continuous g) :
    IsClosed { b | f b ≤ g b } :=
  continuous_iff_isClosed.mp (hf.prodMk hg) _ isClosed_le_prod

instance : ClosedIicTopology α where
  isClosed_Iic _ := isClosed_le continuous_id continuous_const

instance : ClosedIciTopology α where
  isClosed_Ici _ := isClosed_le continuous_const continuous_id

instance : OrderClosedTopology αᵒᵈ := by
  constructor
  have : {p : αᵒᵈ × αᵒᵈ | p.1 ≤ p.2} =
      (fun p : αᵒᵈ × αᵒᵈ => (ofDual p.2, ofDual p.1)) ⁻¹' {p : α × α | p.1 ≤ p.2} := by
    ext ⟨a, b⟩; simp [OrderDual.ofDual_le_ofDual]
  rw [this]
  exact (OrderClosedTopology.isClosed_le' (α := α)).preimage
    ((continuous_ofDual.comp continuous_snd).prodMk (continuous_ofDual.comp continuous_fst))

theorem isClosed_Icc {a b : α} : IsClosed (Icc a b) :=
  IsClosed.inter isClosed_Ici isClosed_Iic

@[simp]
theorem closure_Icc (a b : α) : closure (Icc a b) = Icc a b :=
  isClosed_Icc.closure_eq

theorem le_of_tendsto_of_tendsto_of_frequently {f g : β → α} {b : Filter β} {a₁ a₂ : α}
    (hf : Tendsto f b (𝓝 a₁)) (hg : Tendsto g b (𝓝 a₂)) (h : ∃ᶠ x in b, f x ≤ g x) : a₁ ≤ a₂ :=
  t.isClosed_le'.mem_of_frequently_of_tendsto h (hf.prodMk_nhds hg)

theorem le_of_tendsto_of_tendsto {f g : β → α} {b : Filter β} {a₁ a₂ : α} [NeBot b]
    (hf : Tendsto f b (𝓝 a₁)) (hg : Tendsto g b (𝓝 a₂)) (h : f ≤ᶠ[b] g) : a₁ ≤ a₂ :=
  le_of_tendsto_of_tendsto_of_frequently hf hg <| Eventually.frequently h

alias tendsto_le_of_eventuallyLE := le_of_tendsto_of_tendsto

theorem le_of_tendsto_of_tendsto' {f g : β → α} {b : Filter β} {a₁ a₂ : α} [NeBot b]
    (hf : Tendsto f b (𝓝 a₁)) (hg : Tendsto g b (𝓝 a₂)) (h : ∀ x, f x ≤ g x) : a₁ ≤ a₂ :=
  le_of_tendsto_of_tendsto hf hg (Eventually.of_forall h)

@[simp]
theorem closure_le_eq [TopologicalSpace β] {f g : β → α} (hf : Continuous f) (hg : Continuous g) :
    closure { b | f b ≤ g b } = { b | f b ≤ g b } :=
  (isClosed_le hf hg).closure_eq

theorem closure_lt_subset_le [TopologicalSpace β] {f g : β → α} (hf : Continuous f)
    (hg : Continuous g) : closure { b | f b < g b } ⊆ { b | f b ≤ g b } :=
  (closure_minimal fun _ => le_of_lt) <| isClosed_le hf hg

theorem ContinuousWithinAt.closure_le [TopologicalSpace β] {f g : β → α} {s : Set β} {x : β}
    (hx : x ∈ closure s) (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x)
    (h : ∀ y ∈ s, f y ≤ g y) : f x ≤ g x :=
  show (f x, g x) ∈ { p : α × α | p.1 ≤ p.2 } from
    OrderClosedTopology.isClosed_le'.closure_subset ((hf.prodMk hg).mem_closure hx h)

/-- If `s` is a closed set and two functions `f` and `g` are continuous on `s`,
then the set `{x ∈ s | f x ≤ g x}` is a closed set. -/
theorem IsClosed.isClosed_le [TopologicalSpace β] {f g : β → α} {s : Set β} (hs : IsClosed s)
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) : IsClosed ({ x ∈ s | f x ≤ g x }) :=
  (hf.prodMk hg).preimage_isClosed_of_isClosed hs OrderClosedTopology.isClosed_le'

theorem le_on_closure [TopologicalSpace β] {f g : β → α} {s : Set β} (h : ∀ x ∈ s, f x ≤ g x)
    (hf : ContinuousOn f (closure s)) (hg : ContinuousOn g (closure s)) ⦃x⦄ (hx : x ∈ closure s) :
    f x ≤ g x :=
  have : s ⊆ { y ∈ closure s | f y ≤ g y } := fun y hy => ⟨subset_closure hy, h y hy⟩
  (closure_minimal this (isClosed_closure.isClosed_le hf hg) hx).2

theorem IsClosed.epigraph [TopologicalSpace β] {f : β → α} {s : Set β} (hs : IsClosed s)
    (hf : ContinuousOn f s) : IsClosed { p : β × α | p.1 ∈ s ∧ f p.1 ≤ p.2 } :=
  (hs.preimage continuous_fst).isClosed_le (hf.comp continuousOn_fst Subset.rfl) continuousOn_snd

theorem IsClosed.hypograph [TopologicalSpace β] {f : β → α} {s : Set β} (hs : IsClosed s)
    (hf : ContinuousOn f s) : IsClosed { p : β × α | p.1 ∈ s ∧ p.2 ≤ f p.1 } :=
  (hs.preimage continuous_fst).isClosed_le continuousOn_snd (hf.comp continuousOn_fst Subset.rfl)

/-- The set of monotone functions on a set is closed. -/
theorem isClosed_monotoneOn [Preorder β] {s : Set β} : IsClosed {f : β → α | MonotoneOn f s} := by
  simp only [isClosed_iff_clusterPt, clusterPt_principal_iff_frequently]
  intro g hg a ha b hb hab
  have hmain (x) : Tendsto (fun f' ↦ f' x) (𝓝 g) (𝓝 (g x)) := continuousAt_apply x _
  exact le_of_tendsto_of_tendsto_of_frequently (hmain a) (hmain b) (hg.mono fun g h ↦ h ha hb hab)

/-- The set of monotone functions is closed. -/
theorem isClosed_monotone [Preorder β] : IsClosed {f : β → α | Monotone f} := by
  simp_rw [← monotoneOn_univ]
  exact isClosed_monotoneOn

/-- The set of antitone functions on a set is closed. -/
theorem isClosed_antitoneOn [Preorder β] {s : Set β} : IsClosed {f : β → α | AntitoneOn f s} := by
  simp only [isClosed_iff_clusterPt, clusterPt_principal_iff_frequently]
  intro g hg a ha b hb hab
  have hmain (x) : Tendsto (fun f' ↦ f' x) (𝓝 g) (𝓝 (g x)) := continuousAt_apply x _
  exact le_of_tendsto_of_tendsto_of_frequently (hmain b) (hmain a) (hg.mono fun g h ↦ h ha hb hab)

/-- The set of antitone functions is closed. -/
theorem isClosed_antitone [Preorder β] : IsClosed {f : β → α | Antitone f} := by
  simp_rw [← antitoneOn_univ]
  exact isClosed_antitoneOn

end Preorder

section PartialOrder

variable [TopologicalSpace α] [PartialOrder α] [t : OrderClosedTopology α]

-- see Note [lower instance priority]
instance (priority := 90) OrderClosedTopology.to_t2Space : T2Space α :=
  t2_iff_isClosed_diagonal.2 <| by
    simpa only [diagonal, le_antisymm_iff] using
      t.isClosed_le'.inter (isClosed_le continuous_snd continuous_fst)

end PartialOrder

section LinearOrder

variable [TopologicalSpace α] [LinearOrder α] [OrderClosedTopology α]

theorem isOpen_lt [TopologicalSpace β] {f g : β → α} (hf : Continuous f) (hg : Continuous g) :
    IsOpen { b | f b < g b } := by
  simpa only [lt_iff_not_ge] using (isClosed_le hg hf).isOpen_compl

theorem isOpen_lt_prod : IsOpen { p : α × α | p.1 < p.2 } :=
  isOpen_lt continuous_fst continuous_snd

variable {a b : α}

theorem isOpen_Ioo : IsOpen (Ioo a b) :=
  IsOpen.inter isOpen_Ioi isOpen_Iio

@[simp]
theorem interior_Ioo : interior (Ioo a b) = Ioo a b :=
  isOpen_Ioo.interior_eq

theorem Ioo_subset_closure_interior : Ioo a b ⊆ closure (interior (Ioo a b)) := by
  simp only [interior_Ioo, subset_closure]

theorem Ioo_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Ioo a b ∈ 𝓝 x :=
  IsOpen.mem_nhds isOpen_Ioo ⟨ha, hb⟩

theorem Ioc_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Ioc a b ∈ 𝓝 x :=
  mem_of_superset (Ioo_mem_nhds ha hb) Ioo_subset_Ioc_self

theorem Ico_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Ico a b ∈ 𝓝 x :=
  mem_of_superset (Ioo_mem_nhds ha hb) Ioo_subset_Ico_self

theorem Icc_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Icc a b ∈ 𝓝 x :=
  mem_of_superset (Ioo_mem_nhds ha hb) Ioo_subset_Icc_self

/-- The only order closed topology on a linear order which is a `PredOrder` and a `SuccOrder`
is the discrete topology.

This theorem is not an instance,
because it causes searches for `PredOrder` and `SuccOrder` with their `Preorder` arguments
and very rarely matches. -/
theorem DiscreteTopology.of_predOrder_succOrder [PredOrder α] [SuccOrder α] :
    DiscreteTopology α := by
  refine discreteTopology_iff_nhds.mpr fun a ↦ ?_
  rw [← nhdsWithin_univ, ← Iic_union_Ioi, nhdsWithin_union, PredOrder.nhdsLE, SuccOrder.nhdsGT,
    sup_bot_eq]

end LinearOrder

section LinearOrder

variable [TopologicalSpace α] [LinearOrder α] [OrderClosedTopology α] {f g : β → α}

section

variable [TopologicalSpace β]

theorem lt_subset_interior_le (hf : Continuous f) (hg : Continuous g) :
    { b | f b < g b } ⊆ interior { b | f b ≤ g b } :=
  (interior_maximal fun _ => le_of_lt) <| isOpen_lt hf hg

theorem frontier_le_subset_eq (hf : Continuous f) (hg : Continuous g) :
    frontier { b | f b ≤ g b } ⊆ { b | f b = g b } := by
  rw [frontier_eq_closure_inter_closure, closure_le_eq hf hg]
  rintro b ⟨hb₁, hb₂⟩
  refine le_antisymm hb₁ (closure_lt_subset_le hg hf ?_)
  convert hb₂ using 2; simp only [not_le.symm]; rfl

theorem frontier_Iic_subset (a : α) : frontier (Iic a) ⊆ {a} :=
  frontier_le_subset_eq (@continuous_id α _) continuous_const

theorem frontier_Ici_subset (a : α) : frontier (Ici a) ⊆ {a} :=
  fun _ hx ↦ (frontier_le_subset_eq continuous_const continuous_id hx).symm

theorem frontier_lt_subset_eq (hf : Continuous f) (hg : Continuous g) :
    frontier { b | f b < g b } ⊆ { b | f b = g b } := by
  simpa only [← not_lt, ← compl_setOf, frontier_compl, eq_comm] using frontier_le_subset_eq hg hf

theorem continuous_if_le [TopologicalSpace γ] [∀ x, Decidable (f x ≤ g x)] {f' g' : β → γ}
    (hf : Continuous f) (hg : Continuous g) (hf' : ContinuousOn f' { x | f x ≤ g x })
    (hg' : ContinuousOn g' { x | g x ≤ f x }) (hfg : ∀ x, f x = g x → f' x = g' x) :
    Continuous fun x => if f x ≤ g x then f' x else g' x := by
  refine continuous_if (fun a ha => hfg _ (frontier_le_subset_eq hf hg ha)) ?_ (hg'.mono ?_)
  · rwa [(isClosed_le hf hg).closure_eq]
  · simp only [not_le]
    exact closure_lt_subset_le hg hf

theorem Continuous.if_le [TopologicalSpace γ] [∀ x, Decidable (f x ≤ g x)] {f' g' : β → γ}
    (hf' : Continuous f') (hg' : Continuous g') (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ x, f x = g x → f' x = g' x) : Continuous fun x => if f x ≤ g x then f' x else g' x :=
  continuous_if_le hf hg hf'.continuousOn hg'.continuousOn hfg

theorem Filter.Tendsto.eventually_lt {l : Filter γ} {f g : γ → α} {y z : α} (hf : Tendsto f l (𝓝 y))
    (hg : Tendsto g l (𝓝 z)) (hyz : y < z) : ∀ᶠ x in l, f x < g x :=
  let ⟨_a, ha, _b, hb, h⟩ := hyz.exists_disjoint_Iio_Ioi
  (hg.eventually (Ioi_mem_nhds hb)).mp <| (hf.eventually (Iio_mem_nhds ha)).mono fun _ h₁ h₂ =>
    h _ h₁ _ h₂

nonrec theorem ContinuousAt.eventually_lt {x₀ : β} (hf : ContinuousAt f x₀) (hg : ContinuousAt g x₀)
    (hfg : f x₀ < g x₀) : ∀ᶠ x in 𝓝 x₀, f x < g x :=
  hf.eventually_lt hg hfg

@[continuity, fun_prop]
protected theorem Continuous.min (hf : Continuous f) (hg : Continuous g) :
    Continuous fun b => min (f b) (g b) := by
  simp only [min_def]
  exact hf.if_le hg hf hg fun x => id

@[continuity, fun_prop]
protected theorem Continuous.max (hf : Continuous f) (hg : Continuous g) :
    Continuous fun b => max (f b) (g b) := by
  simp only [max_def]
  exact hg.if_le hf hf hg fun _ => Eq.symm

end

theorem continuous_min : Continuous fun p : α × α => min p.1 p.2 :=
  continuous_fst.min continuous_snd

theorem continuous_max : Continuous fun p : α × α => max p.1 p.2 :=
  continuous_fst.max continuous_snd

protected theorem Filter.Tendsto.max {b : Filter β} {a₁ a₂ : α} (hf : Tendsto f b (𝓝 a₁))
    (hg : Tendsto g b (𝓝 a₂)) : Tendsto (fun b => max (f b) (g b)) b (𝓝 (max a₁ a₂)) :=
  (continuous_max.tendsto (a₁, a₂)).comp (hf.prodMk_nhds hg)

protected theorem Filter.Tendsto.min {b : Filter β} {a₁ a₂ : α} (hf : Tendsto f b (𝓝 a₁))
    (hg : Tendsto g b (𝓝 a₂)) : Tendsto (fun b => min (f b) (g b)) b (𝓝 (min a₁ a₂)) :=
  (continuous_min.tendsto (a₁, a₂)).comp (hf.prodMk_nhds hg)

protected theorem Filter.Tendsto.max_right {l : Filter β} {a : α} (h : Tendsto f l (𝓝 a)) :
    Tendsto (fun i => max a (f i)) l (𝓝 a) := by
  simpa only [sup_idem] using (tendsto_const_nhds (x := a)).max h

protected theorem Filter.Tendsto.max_left {l : Filter β} {a : α} (h : Tendsto f l (𝓝 a)) :
    Tendsto (fun i => max (f i) a) l (𝓝 a) := by
  simp_rw [max_comm _ a]
  exact h.max_right

theorem Filter.tendsto_nhds_max_right {l : Filter β} {a : α} (h : Tendsto f l (𝓝[>] a)) :
    Tendsto (fun i => max a (f i)) l (𝓝[>] a) := by
  obtain ⟨h₁ : Tendsto f l (𝓝 a), h₂ : ∀ᶠ i in l, f i ∈ Ioi a⟩ := tendsto_nhdsWithin_iff.mp h
  exact tendsto_nhdsWithin_iff.mpr ⟨h₁.max_right, h₂.mono fun i hi => lt_max_of_lt_right hi⟩

theorem Filter.tendsto_nhds_max_left {l : Filter β} {a : α} (h : Tendsto f l (𝓝[>] a)) :
    Tendsto (fun i => max (f i) a) l (𝓝[>] a) := by
  simp_rw [max_comm _ a]
  exact Filter.tendsto_nhds_max_right h

theorem Filter.Tendsto.min_right {l : Filter β} {a : α} (h : Tendsto f l (𝓝 a)) :
    Tendsto (fun i => min a (f i)) l (𝓝 a) := by
  simpa only [inf_idem] using (tendsto_const_nhds (x := a)).min h

theorem Filter.Tendsto.min_left {l : Filter β} {a : α} (h : Tendsto f l (𝓝 a)) :
    Tendsto (fun i => min (f i) a) l (𝓝 a) := by
  simp_rw [min_comm _ a]
  exact h.min_right

theorem Filter.tendsto_nhds_min_right {l : Filter β} {a : α} (h : Tendsto f l (𝓝[<] a)) :
    Tendsto (fun i => min a (f i)) l (𝓝[<] a) := by
  obtain ⟨h₁ : Tendsto f l (𝓝 a), h₂ : ∀ᶠ i in l, f i ∈ Iio a⟩ := tendsto_nhdsWithin_iff.mp h
  exact tendsto_nhdsWithin_iff.mpr ⟨h₁.min_right, h₂.mono fun i hi => min_lt_of_right_lt hi⟩

theorem Filter.tendsto_nhds_min_left {l : Filter β} {a : α} (h : Tendsto f l (𝓝[<] a)) :
    Tendsto (fun i => min (f i) a) l (𝓝[<] a) := by
  simp_rw [min_comm _ a]
  exact Filter.tendsto_nhds_min_right h

theorem Dense.exists_between [DenselyOrdered α] {s : Set α} (hs : Dense s) {x y : α} (h : x < y) :
    ∃ z ∈ s, z ∈ Ioo x y :=
  hs.exists_mem_open isOpen_Ioo (nonempty_Ioo.2 h)

theorem Dense.Ioi_eq_biUnion [DenselyOrdered α] {s : Set α} (hs : Dense s) (x : α) :
    Ioi x = ⋃ y ∈ s ∩ Ioi x, Ioi y := by
  refine Subset.antisymm (fun z hz ↦ ?_) (iUnion₂_subset fun y hy ↦ Ioi_subset_Ioi (le_of_lt hy.2))
  rcases hs.exists_between hz with ⟨y, hys, hxy, hyz⟩
  exact mem_iUnion₂.2 ⟨y, ⟨hys, hxy⟩, hyz⟩

theorem Dense.Iio_eq_biUnion [DenselyOrdered α] {s : Set α} (hs : Dense s) (x : α) :
    Iio x = ⋃ y ∈ s ∩ Iio x, Iio y := by
  refine Subset.antisymm (fun z hz ↦ ?_) (iUnion₂_subset fun y hy ↦ Iio_subset_Iio (le_of_lt hy.2))
  rcases hs.exists_between hz with ⟨y, hys, hzy, hyx⟩
  exact mem_iUnion₂.2 ⟨y, ⟨hys, hyx⟩, hzy⟩

end LinearOrder

end OrderClosedTopology

instance [Preorder α] [TopologicalSpace α] [OrderClosedTopology α] [Preorder β] [TopologicalSpace β]
    [OrderClosedTopology β] : OrderClosedTopology (α × β) :=
  ⟨(isClosed_le continuous_fst.fst continuous_snd.fst).inter
    (isClosed_le continuous_fst.snd continuous_snd.snd)⟩

instance {ι : Type*} {α : ι → Type*} [∀ i, Preorder (α i)] [∀ i, TopologicalSpace (α i)]
    [∀ i, OrderClosedTopology (α i)] : OrderClosedTopology (∀ i, α i) := by
  constructor
  simp only [Pi.le_def, setOf_forall]
  exact isClosed_iInter fun i => isClosed_le (continuous_apply i).fst' (continuous_apply i).snd'

instance Pi.orderClosedTopology' [Preorder β] [TopologicalSpace β] [OrderClosedTopology β] :
    OrderClosedTopology (α → β) :=
  inferInstance
