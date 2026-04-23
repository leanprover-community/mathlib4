/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
module

public import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Lattice.Image
import Mathlib.Init
import Mathlib.Order.BoundedOrder.Lattice
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Order.Cover
import Mathlib.Order.Filter.Tendsto
import Mathlib.Order.Interval.Set.Disjoint
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.Translate.ToDual
import Mathlib.Topology.Closure
import Mathlib.Topology.ClusterPt
import Mathlib.Topology.Continuous
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.Piecewise

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
open OrderDual (toDual)
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
@[to_dual existing]
class ClosedIciTopology (α : Type*) [TopologicalSpace α] [Preorder α] : Prop where
  /-- For any `a`, the set `[a, +∞)` is closed. -/
  isClosed_Ici (a : α) : IsClosed (Ici a)

/-- A topology on a set which is both a topological space and a preorder is _order-closed_ if the
set of points `(x, y)` with `x ≤ y` is closed in the product space. We introduce this as a mixin.
This property is satisfied for the order topology on a linear order, but it can be satisfied more
generally, and suffices to derive many interesting properties relating order and topology. -/
class OrderClosedTopology (α : Type*) [TopologicalSpace α] [Preorder α] : Prop where
  /-- The set `{ (x, y) | x ≤ y }` is a closed set. -/
  protected isClosed_le' : IsClosed { p : α × α | p.1 ≤ p.2 }

instance [TopologicalSpace α] [h : FirstCountableTopology α] : FirstCountableTopology αᵒᵈ := h
instance [TopologicalSpace α] [h : SecondCountableTopology α] : SecondCountableTopology αᵒᵈ := h
instance [TopologicalSpace α] [h : SeparableSpace α] : SeparableSpace αᵒᵈ := h

theorem Dense.orderDual [TopologicalSpace α] {s : Set α} (hs : Dense s) :
    Dense (OrderDual.ofDual ⁻¹' s) :=
  hs

section General
variable [TopologicalSpace α] [Preorder α] {s : Set α}

@[to_dual]
protected lemma BddAbove.of_closure : BddAbove (closure s) → BddAbove s :=
  BddAbove.mono subset_closure

end General

section ClosedIicTopology

section Preorder

variable [TopologicalSpace α] [Preorder α] [ClosedIicTopology α] {f : β → α} {a b : α} {s : Set α}

@[to_dual]
theorem isClosed_Iic : IsClosed (Iic a) :=
  ClosedIicTopology.isClosed_Iic a

@[to_dual]
instance : ClosedIciTopology αᵒᵈ where
  isClosed_Ici _ := isClosed_Iic (α := α)

@[to_dual (attr := simp)]
theorem closure_Iic (a : α) : closure (Iic a) = Iic a :=
  isClosed_Iic.closure_eq

@[to_dual ge_of_tendsto_of_frequently]
theorem le_of_tendsto_of_frequently {x : Filter β} (lim : Tendsto f x (𝓝 a))
    (h : ∃ᶠ c in x, f c ≤ b) : a ≤ b :=
  isClosed_Iic.mem_of_frequently_of_tendsto h lim

@[to_dual ge_of_tendsto]
theorem le_of_tendsto {x : Filter β} [NeBot x] (lim : Tendsto f x (𝓝 a))
    (h : ∀ᶠ c in x, f c ≤ b) : a ≤ b :=
  isClosed_Iic.mem_of_tendsto lim h

@[to_dual ge_of_tendsto']
theorem le_of_tendsto' {x : Filter β} [NeBot x] (lim : Tendsto f x (𝓝 a))
    (h : ∀ c, f c ≤ b) : a ≤ b :=
  le_of_tendsto lim (Eventually.of_forall h)

@[to_dual (attr := simp)]
lemma upperBounds_closure (s : Set α) : upperBounds (closure s : Set α) = upperBounds s :=
  ext fun a ↦ by simp_rw [mem_upperBounds_iff_subset_Iic, isClosed_Iic.closure_subset_iff]

@[to_dual (attr := simp)]
lemma bddAbove_closure : BddAbove (closure s) ↔ BddAbove s := by
  simp_rw [BddAbove, upperBounds_closure]

@[to_dual]
protected alias ⟨_, BddAbove.closure⟩ := bddAbove_closure

@[to_dual (attr := simp) disjoint_nhds_atTop_iff]
theorem disjoint_nhds_atBot_iff : Disjoint (𝓝 a) atBot ↔ ¬IsBot a := by
  constructor
  · intro hd hbot
    rw [hbot.atBot_eq, disjoint_principal_right] at hd
    exact mem_of_mem_nhds hd le_rfl
  · simp only [IsBot, not_forall]
    rintro ⟨b, hb⟩
    refine disjoint_of_disjoint_of_mem disjoint_compl_left ?_ (Iic_mem_atBot b)
    exact isClosed_Iic.isOpen_compl.mem_nhds hb

@[to_dual]
theorem IsLUB.range_of_tendsto {F : Filter β} [F.NeBot] (hle : ∀ i, f i ≤ a)
    (hlim : Tendsto f F (𝓝 a)) : IsLUB (range f) a :=
  ⟨forall_mem_range.mpr hle, fun _c hc ↦ le_of_tendsto' hlim fun i ↦ hc <| mem_range_self i⟩

end Preorder

section NoBotOrder

variable [Preorder α] [NoBotOrder α] [TopologicalSpace α] [ClosedIicTopology α] {a : α}
  {l : Filter β} [NeBot l] {f : β → α}

@[to_dual disjoint_nhds_atTop]
theorem disjoint_nhds_atBot (a : α) : Disjoint (𝓝 a) atBot := by simp

@[to_dual (attr := simp) nhds_inf_atTop]
theorem nhds_inf_atBot (a : α) : 𝓝 a ⊓ atBot = ⊥ := (disjoint_nhds_atBot a).eq_bot

@[deprecated (since := "2026-04-07")] alias inf_nhds_atBot := nhds_inf_atBot
@[deprecated (since := "2026-04-07")] alias inf_nhds_atTop := nhds_inf_atTop

@[to_dual]
theorem not_tendsto_nhds_of_tendsto_atBot (hf : Tendsto f l atBot) (a : α) : ¬Tendsto f l (𝓝 a) :=
  hf.not_tendsto (disjoint_nhds_atBot a).symm

@[to_dual]
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

@[to_dual]
theorem isOpen_Ioi : IsOpen (Ioi a) := by
  rw [← compl_Iic]
  exact isClosed_Iic.isOpen_compl

@[to_dual (attr := simp)]
theorem interior_Ioi : interior (Ioi a) = Ioi a :=
  isOpen_Ioi.interior_eq

@[to_dual]
theorem Ioi_mem_nhds (h : a < b) : Ioi a ∈ 𝓝 b := IsOpen.mem_nhds isOpen_Ioi h

@[to_dual eventually_lt_nhds]
theorem eventually_gt_nhds (hab : b < a) : ∀ᶠ x in 𝓝 a, b < x := Ioi_mem_nhds hab

@[to_dual]
theorem Ici_mem_nhds (h : a < b) : Ici a ∈ 𝓝 b :=
  mem_of_superset (Ioi_mem_nhds h) Ioi_subset_Ici_self

@[to_dual eventually_le_nhds]
theorem eventually_ge_nhds (hab : b < a) : ∀ᶠ x in 𝓝 a, b ≤ x := Ici_mem_nhds hab

@[to_dual eventually_lt_const]
theorem Filter.Tendsto.eventually_const_lt {l : Filter γ} {f : γ → α} {u v : α} (hv : u < v)
    (h : Filter.Tendsto f l (𝓝 v)) : ∀ᶠ a in l, u < f a :=
  h.eventually <| eventually_gt_nhds hv

@[to_dual eventually_le_const]
theorem Filter.Tendsto.eventually_const_le {l : Filter γ} {f : γ → α} {u v : α} (hv : u < v)
    (h : Tendsto f l (𝓝 v)) : ∀ᶠ a in l, u ≤ f a :=
  h.eventually <| eventually_ge_nhds hv

@[to_dual exists_lt]
protected theorem Dense.exists_gt [NoMaxOrder α] {s : Set α} (hs : Dense s) (x : α) :
    ∃ y ∈ s, x < y :=
  hs.exists_mem_open isOpen_Ioi (exists_gt x)

@[to_dual exists_le]
protected theorem Dense.exists_ge [NoMaxOrder α] {s : Set α} (hs : Dense s) (x : α) :
    ∃ y ∈ s, x ≤ y :=
  (hs.exists_gt x).imp fun _ h ↦ ⟨h.1, h.2.le⟩

@[to_dual exists_le']
theorem Dense.exists_ge' {s : Set α} (hs : Dense s) (htop : ∀ x, IsTop x → x ∈ s) (x : α) :
    ∃ y ∈ s, x ≤ y := by
  by_cases hx : IsTop x
  · exact ⟨x, htop x hx, le_rfl⟩
  · simp only [IsTop, not_forall, not_le] at hx
    rcases hs.exists_mem_open isOpen_Ioi hx with ⟨y, hys, hy : x < y⟩
    exact ⟨y, hys, hy.le⟩

/-!
### Left neighborhoods on a `ClosedIicTopology`

Limits to the left of real functions are defined in terms of neighborhoods to the left, either open
or closed, i.e., members of `𝓝[<] a` and `𝓝[≤] a`. Here we prove that all left-neighborhoods of a
point are equal, and we prove other useful characterizations which require the stronger hypothesis
`OrderTopology α` in another file.
-/

/-!
#### Point excluded
-/

@[to_dual]
theorem Ioo_mem_nhdsLT (H : a < b) : Ioo a b ∈ 𝓝[<] b := by
  simpa only [← Iio_inter_Ioi] using inter_mem_nhdsWithin _ (Ioi_mem_nhds H)

@[to_dual]
theorem Ioo_mem_nhdsLT_of_mem (H : b ∈ Ioc a c) : Ioo a c ∈ 𝓝[<] b :=
  mem_of_superset (Ioo_mem_nhdsLT H.1) <| Ioo_subset_Ioo_right H.2

@[to_dual]
protected theorem CovBy.nhdsLT (h : a ⋖ b) : 𝓝[<] b = ⊥ :=
  empty_mem_iff_bot.mp <| h.Ioo_eq ▸ Ioo_mem_nhdsLT h.1

@[to_dual]
protected theorem PredOrder.nhdsLT [PredOrder α] : 𝓝[<] a = ⊥ := by
  if h : IsMin a then simp [h.Iio_eq]
  else exact (Order.pred_covBy_of_not_isMin h).nhdsLT

@[to_dual]
theorem PredOrder.nhdsGT_eq_nhdsNE [PredOrder α] (a : α) : 𝓝[>] a = 𝓝[≠] a := by
  rw [← nhdsLT_sup_nhdsGT, PredOrder.nhdsLT, bot_sup_eq]

@[to_dual]
theorem PredOrder.nhdsGE_eq_nhds [PredOrder α] (a : α) : 𝓝[≥] a = 𝓝 a := by
  rw [← nhdsLT_sup_nhdsGE, PredOrder.nhdsLT, bot_sup_eq]

@[to_dual]
theorem Ico_mem_nhdsLT_of_mem (H : b ∈ Ioc a c) : Ico a c ∈ 𝓝[<] b :=
  mem_of_superset (Ioo_mem_nhdsLT_of_mem H) Ioo_subset_Ico_self

@[to_dual]
theorem Ico_mem_nhdsLT (H : a < b) : Ico a b ∈ 𝓝[<] b := Ico_mem_nhdsLT_of_mem ⟨H, le_rfl⟩

@[to_dual]
theorem Ioc_mem_nhdsLT_of_mem (H : b ∈ Ioc a c) : Ioc a c ∈ 𝓝[<] b :=
  mem_of_superset (Ioo_mem_nhdsLT_of_mem H) Ioo_subset_Ioc_self

@[to_dual]
theorem Ioc_mem_nhdsLT (H : a < b) : Ioc a b ∈ 𝓝[<] b := Ioc_mem_nhdsLT_of_mem ⟨H, le_rfl⟩

@[to_dual]
theorem Icc_mem_nhdsLT_of_mem (H : b ∈ Ioc a c) : Icc a c ∈ 𝓝[<] b :=
  mem_of_superset (Ioo_mem_nhdsLT_of_mem H) Ioo_subset_Icc_self

@[to_dual]
theorem Icc_mem_nhdsLT (H : a < b) : Icc a b ∈ 𝓝[<] b := Icc_mem_nhdsLT_of_mem ⟨H, le_rfl⟩

@[to_dual (attr := simp)]
theorem nhdsWithin_Ico_eq_nhdsLT (h : a < b) : 𝓝[Ico a b] b = 𝓝[<] b :=
  nhdsWithin_inter_of_mem <| nhdsWithin_le_nhds <| Ici_mem_nhds h

@[to_dual (attr := simp)]
theorem nhdsWithin_Ioo_eq_nhdsLT (h : a < b) : 𝓝[Ioo a b] b = 𝓝[<] b :=
  nhdsWithin_inter_of_mem <| nhdsWithin_le_nhds <| Ioi_mem_nhds h

@[to_dual (attr := simp)]
theorem continuousWithinAt_Ico_iff_Iio (h : a < b) :
    ContinuousWithinAt f (Ico a b) b ↔ ContinuousWithinAt f (Iio b) b := by
  simp only [ContinuousWithinAt, nhdsWithin_Ico_eq_nhdsLT h]

@[to_dual (attr := simp)]
theorem continuousWithinAt_Ioo_iff_Iio (h : a < b) :
    ContinuousWithinAt f (Ioo a b) b ↔ ContinuousWithinAt f (Iio b) b := by
  simp only [ContinuousWithinAt, nhdsWithin_Ioo_eq_nhdsLT h]

/-!
#### Point included
-/

@[to_dual]
protected theorem CovBy.nhdsLE (H : a ⋖ b) : 𝓝[≤] b = pure b := by
  rw [← Iio_insert, nhdsWithin_insert, H.nhdsLT, sup_bot_eq]

@[to_dual]
protected theorem PredOrder.nhdsLE [PredOrder α] : 𝓝[≤] b = pure b := by
  rw [← Iio_insert, nhdsWithin_insert, PredOrder.nhdsLT, sup_bot_eq]

@[to_dual]
theorem Ioc_mem_nhdsLE (H : a < b) : Ioc a b ∈ 𝓝[≤] b :=
  inter_mem (nhdsWithin_le_nhds <| Ioi_mem_nhds H) self_mem_nhdsWithin

@[to_dual]
theorem Ioo_mem_nhdsLE_of_mem (H : b ∈ Ioo a c) : Ioo a c ∈ 𝓝[≤] b :=
  mem_of_superset (Ioc_mem_nhdsLE H.1) <| Ioc_subset_Ioo_right H.2

@[to_dual]
theorem Ico_mem_nhdsLE_of_mem (H : b ∈ Ioo a c) : Ico a c ∈ 𝓝[≤] b :=
  mem_of_superset (Ioo_mem_nhdsLE_of_mem H) Ioo_subset_Ico_self

@[to_dual]
theorem Ioc_mem_nhdsLE_of_mem (H : b ∈ Ioc a c) : Ioc a c ∈ 𝓝[≤] b :=
  mem_of_superset (Ioc_mem_nhdsLE H.1) <| Ioc_subset_Ioc_right H.2

@[to_dual]
theorem Icc_mem_nhdsLE_of_mem (H : b ∈ Ioc a c) : Icc a c ∈ 𝓝[≤] b :=
  mem_of_superset (Ioc_mem_nhdsLE_of_mem H) Ioc_subset_Icc_self

@[to_dual]
theorem Icc_mem_nhdsLE (H : a < b) : Icc a b ∈ 𝓝[≤] b := Icc_mem_nhdsLE_of_mem ⟨H, le_rfl⟩

@[to_dual (attr := simp)]
theorem nhdsWithin_Icc_eq_nhdsLE (h : a < b) : 𝓝[Icc a b] b = 𝓝[≤] b :=
  nhdsWithin_inter_of_mem <| nhdsWithin_le_nhds <| Ici_mem_nhds h

@[to_dual (attr := simp)]
theorem nhdsWithin_Ioc_eq_nhdsLE (h : a < b) : 𝓝[Ioc a b] b = 𝓝[≤] b :=
  nhdsWithin_inter_of_mem <| nhdsWithin_le_nhds <| Ioi_mem_nhds h

@[to_dual (attr := simp)]
theorem continuousWithinAt_Icc_iff_Iic (h : a < b) :
    ContinuousWithinAt f (Icc a b) b ↔ ContinuousWithinAt f (Iic b) b := by
  simp only [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsLE h]

@[to_dual (attr := simp)]
theorem continuousWithinAt_Ioc_iff_Iic (h : a < b) :
    ContinuousWithinAt f (Ioc a b) b ↔ ContinuousWithinAt f (Iic b) b := by
  simp only [ContinuousWithinAt, nhdsWithin_Ioc_eq_nhdsLE h]

end LinearOrder

end ClosedIicTopology

section ClosedIciTopology

-- TODO: we're missing some to_dual tags for conditionally complete lattices

@[to_dual existing]
theorem iInf_eq_of_forall_le_of_tendsto {ι : Type*} {F : Filter ι} [F.NeBot]
    [ConditionallyCompleteLattice α] [TopologicalSpace α] [ClosedIciTopology α]
    {a : α} {f : ι → α} (hle : ∀ i, a ≤ f i) (hlim : Tendsto f F (𝓝 a)) :
    ⨅ i, f i = a :=
  iSup_eq_of_forall_le_of_tendsto (α := αᵒᵈ) hle hlim

@[to_dual existing]
theorem iUnion_Ici_eq_Ioi_of_lt_of_tendsto {ι : Type*} {F : Filter ι} [F.NeBot]
    [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [ClosedIciTopology α]
    {a : α} {f : ι → α} (hlt : ∀ i, a < f i) (hlim : Tendsto f F (𝓝 a)) :
    ⋃ i : ι, Ici (f i) = Ioi a :=
  iUnion_Iic_eq_Iio_of_lt_of_tendsto (α := αᵒᵈ) hlt hlim

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

-- The binder info on both theorems is slightly different, see
-- https://github.com/leanprover/lean4/issues/9727
theorem isClosed_le_prod : IsClosed { p : α × α | p.1 ≤ p.2 } :=
  t.isClosed_le'

@[to_dual existing isClosed_le_prod]
theorem isClosed_le_prod' : IsClosed { p : α × α | p.2 ≤ p.1 } :=
  (isClosed_le_prod (α := α)).preimage continuous_swap

@[to_dual self (reorder := f g, hf hg)]
theorem isClosed_le [TopologicalSpace β] {f g : β → α} (hf : Continuous f) (hg : Continuous g) :
    IsClosed { b | f b ≤ g b } :=
  continuous_iff_isClosed.mp (hf.prodMk hg) _ isClosed_le_prod

@[to_dual]
instance : ClosedIicTopology α where
  isClosed_Iic _ := isClosed_le continuous_id continuous_const

instance : OrderClosedTopology αᵒᵈ :=
  ⟨isClosed_le_prod' (α := α)⟩

@[to_dual self]
theorem isClosed_Icc {a b : α} : IsClosed (Icc a b) :=
  IsClosed.inter isClosed_Ici isClosed_Iic

@[to_dual self, simp]
theorem closure_Icc (a b : α) : closure (Icc a b) = Icc a b :=
  isClosed_Icc.closure_eq

@[to_dual self (reorder := f g, a₁ a₂, hf hg)]
theorem le_of_tendsto_of_tendsto_of_frequently {f g : β → α} {b : Filter β} {a₁ a₂ : α}
    (hf : Tendsto f b (𝓝 a₁)) (hg : Tendsto g b (𝓝 a₂)) (h : ∃ᶠ x in b, f x ≤ g x) : a₁ ≤ a₂ :=
  t.isClosed_le'.mem_of_frequently_of_tendsto h (hf.prodMk_nhds hg)

@[to_dual self (reorder := f g, a₁ a₂, hf hg)]
theorem le_of_tendsto_of_tendsto {f g : β → α} {b : Filter β} {a₁ a₂ : α} [NeBot b]
    (hf : Tendsto f b (𝓝 a₁)) (hg : Tendsto g b (𝓝 a₂)) (h : f ≤ᶠ[b] g) : a₁ ≤ a₂ :=
  le_of_tendsto_of_tendsto_of_frequently hf hg <| Eventually.frequently h

@[to_dual self (reorder := f g, a₁ a₂, hf hg)]
alias tendsto_le_of_eventuallyLE := le_of_tendsto_of_tendsto

@[to_dual self (reorder := f g, a₁ a₂, hf hg)]
theorem le_of_tendsto_of_tendsto' {f g : β → α} {b : Filter β} {a₁ a₂ : α} [NeBot b]
    (hf : Tendsto f b (𝓝 a₁)) (hg : Tendsto g b (𝓝 a₂)) (h : ∀ x, f x ≤ g x) : a₁ ≤ a₂ :=
  le_of_tendsto_of_tendsto hf hg (Eventually.of_forall h)

@[to_dual self (reorder := f g, hf hg), simp]
theorem closure_le_eq [TopologicalSpace β] {f g : β → α} (hf : Continuous f) (hg : Continuous g) :
    closure { b | f b ≤ g b } = { b | f b ≤ g b } :=
  (isClosed_le hf hg).closure_eq

@[to_dual self (reorder := f g, hf hg)]
theorem closure_lt_subset_le [TopologicalSpace β] {f g : β → α} (hf : Continuous f)
    (hg : Continuous g) : closure { b | f b < g b } ⊆ { b | f b ≤ g b } :=
  (closure_minimal fun _ => le_of_lt) <| isClosed_le hf hg

@[to_dual self (reorder := f g, hf hg)]
theorem ContinuousWithinAt.closure_le [TopologicalSpace β] {f g : β → α} {s : Set β} {x : β}
    (hx : x ∈ closure s) (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x)
    (h : ∀ y ∈ s, f y ≤ g y) : f x ≤ g x :=
  show (f x, g x) ∈ { p : α × α | p.1 ≤ p.2 } from
    OrderClosedTopology.isClosed_le'.closure_subset ((hf.prodMk hg).mem_closure hx h)

/-- If `s` is a closed set and two functions `f` and `g` are continuous on `s`,
then the set `{x ∈ s | f x ≤ g x}` is a closed set. -/
@[to_dual self (reorder := f g, hf hg)]
theorem IsClosed.isClosed_le [TopologicalSpace β] {f g : β → α} {s : Set β} (hs : IsClosed s)
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) : IsClosed ({ x ∈ s | f x ≤ g x }) :=
  (hf.prodMk hg).preimage_isClosed_of_isClosed hs OrderClosedTopology.isClosed_le'

@[to_dual self (reorder := f g, hf hg)]
theorem le_on_closure [TopologicalSpace β] {f g : β → α} {s : Set β} (h : ∀ x ∈ s, f x ≤ g x)
    (hf : ContinuousOn f (closure s)) (hg : ContinuousOn g (closure s)) ⦃x⦄ (hx : x ∈ closure s) :
    f x ≤ g x :=
  have : s ⊆ { y ∈ closure s | f y ≤ g y } := fun y hy => ⟨subset_closure hy, h y hy⟩
  (closure_minimal this (isClosed_closure.isClosed_le hf hg) hx).2

@[to_dual]
theorem IsClosed.epigraph [TopologicalSpace β] {f : β → α} {s : Set β} (hs : IsClosed s)
    (hf : ContinuousOn f s) : IsClosed { p : β × α | p.1 ∈ s ∧ f p.1 ≤ p.2 } :=
  (hs.preimage continuous_fst).isClosed_le (hf.comp continuousOn_fst Subset.rfl) continuousOn_snd

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
theorem isClosed_antitoneOn [Preorder β] {s : Set β} : IsClosed {f : β → α | AntitoneOn f s} :=
  isClosed_monotoneOn (α := αᵒᵈ) (β := β)

/-- The set of antitone functions is closed. -/
theorem isClosed_antitone [Preorder β] : IsClosed {f : β → α | Antitone f} :=
  isClosed_monotone (α := αᵒᵈ) (β := β)

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

@[to_dual self (reorder := f g, hf hg)]
theorem isOpen_lt [TopologicalSpace β] {f g : β → α} (hf : Continuous f) (hg : Continuous g) :
    IsOpen { b | f b < g b } := by
  simpa only [lt_iff_not_ge] using (isClosed_le hg hf).isOpen_compl

@[to_dual isOpen_lt_prod']
theorem isOpen_lt_prod : IsOpen { p : α × α | p.1 < p.2 } :=
  isOpen_lt continuous_fst continuous_snd

variable {a b : α}

@[to_dual self]
theorem isOpen_Ioo : IsOpen (Ioo a b) :=
  IsOpen.inter isOpen_Ioi isOpen_Iio

@[to_dual self, simp]
theorem interior_Ioo : interior (Ioo a b) = Ioo a b :=
  isOpen_Ioo.interior_eq

@[to_dual self]
theorem Ioo_subset_closure_interior : Ioo a b ⊆ closure (interior (Ioo a b)) := by
  simp only [interior_Ioo, subset_closure]

@[to_dual self (reorder := a b, ha hb)]
theorem Ioo_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Ioo a b ∈ 𝓝 x :=
  IsOpen.mem_nhds isOpen_Ioo ⟨ha, hb⟩

@[to_dual (reorder := ha hb)]
theorem Ioc_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Ioc a b ∈ 𝓝 x :=
  mem_of_superset (Ioo_mem_nhds ha hb) Ioo_subset_Ioc_self

@[to_dual self (reorder := a b, ha hb)]
theorem Icc_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Icc a b ∈ 𝓝 x :=
  mem_of_superset (Ioo_mem_nhds ha hb) Ioo_subset_Icc_self

/-- The only order closed topology on a linear order which is a `PredOrder` and a `SuccOrder`
is the discrete topology.

This theorem is not an instance,
because it causes searches for `PredOrder` and `SuccOrder` with their `Preorder` arguments
and very rarely matches. -/
@[to_dual self (reorder := 5 6)]
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

@[to_dual self (reorder := f g, hf hg)]
theorem lt_subset_interior_le (hf : Continuous f) (hg : Continuous g) :
    { b | f b < g b } ⊆ interior { b | f b ≤ g b } :=
  (interior_maximal fun _ => le_of_lt) <| isOpen_lt hf hg

@[to_dual (reorder := f g, hf hg) frontier_ge_subset_eq]
theorem frontier_le_subset_eq (hf : Continuous f) (hg : Continuous g) :
    frontier { b | f b ≤ g b } ⊆ { b | f b = g b } := by
  rw [frontier_eq_closure_inter_closure, closure_le_eq hf hg]
  rintro b ⟨hb₁, hb₂⟩
  refine le_antisymm hb₁ (closure_lt_subset_le hg hf ?_)
  convert hb₂ using 2; simp only [not_le.symm]; rfl

@[to_dual]
theorem frontier_Iic_subset (a : α) : frontier (Iic a) ⊆ {a} :=
  frontier_le_subset_eq (@continuous_id α _) continuous_const

@[to_dual (reorder := f g, hf hg) frontier_gt_subset_eq]
theorem frontier_lt_subset_eq (hf : Continuous f) (hg : Continuous g) :
    frontier { b | f b < g b } ⊆ { b | f b = g b } := by
  simpa only [← not_lt, ← compl_setOf, frontier_compl, eq_comm] using frontier_le_subset_eq hg hf

@[to_dual none]
theorem continuous_if_le [TopologicalSpace γ] [∀ x, Decidable (f x ≤ g x)] {f' g' : β → γ}
    (hf : Continuous f) (hg : Continuous g) (hf' : ContinuousOn f' { x | f x ≤ g x })
    (hg' : ContinuousOn g' { x | g x ≤ f x }) (hfg : ∀ x, f x = g x → f' x = g' x) :
    Continuous fun x => if f x ≤ g x then f' x else g' x := by
  refine continuous_if (fun a ha => hfg _ (frontier_le_subset_eq hf hg ha)) ?_ (hg'.mono ?_)
  · rwa [(isClosed_le hf hg).closure_eq]
  · simp only [not_le]
    exact closure_lt_subset_le hg hf

@[to_dual if_ge]
theorem Continuous.if_le [TopologicalSpace γ] [∀ x, Decidable (f x ≤ g x)] {f' g' : β → γ}
    (hf' : Continuous f') (hg' : Continuous g') (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ x, f x = g x → f' x = g' x) : Continuous fun x => if f x ≤ g x then f' x else g' x :=
  continuous_if_le hf hg hf'.continuousOn hg'.continuousOn hfg

@[to_dual self (reorder := f g, y z, hf hg)]
theorem Filter.Tendsto.eventually_lt {l : Filter γ} {f g : γ → α} {y z : α} (hf : Tendsto f l (𝓝 y))
    (hg : Tendsto g l (𝓝 z)) (hyz : y < z) : ∀ᶠ x in l, f x < g x :=
  let ⟨_a, ha, _b, hb, h⟩ := hyz.exists_disjoint_Iio_Ioi
  (hg.eventually (Ioi_mem_nhds hb)).mp <| (hf.eventually (Iio_mem_nhds ha)).mono fun _ h₁ h₂ =>
    h _ h₁ _ h₂

@[to_dual self (reorder := f g, hf hg)]
nonrec theorem ContinuousAt.eventually_lt {x₀ : β} (hf : ContinuousAt f x₀) (hg : ContinuousAt g x₀)
    (hfg : f x₀ < g x₀) : ∀ᶠ x in 𝓝 x₀, f x < g x :=
  hf.eventually_lt hg hfg

@[to_dual (attr := continuity, fun_prop)]
protected theorem Continuous.max (hf : Continuous f) (hg : Continuous g) :
    Continuous fun b => max (f b) (g b) := by
  simp only [max_def]
  exact hg.if_ge hf hg hf fun x => id

end

@[to_dual]
theorem continuous_max : Continuous fun p : α × α => max p.1 p.2 :=
  continuous_fst.max continuous_snd

@[to_dual]
protected theorem Filter.Tendsto.max {b : Filter β} {a₁ a₂ : α} (hf : Tendsto f b (𝓝 a₁))
    (hg : Tendsto g b (𝓝 a₂)) : Tendsto (fun b => max (f b) (g b)) b (𝓝 (max a₁ a₂)) :=
  (continuous_max.tendsto (a₁, a₂)).comp (hf.prodMk_nhds hg)

@[to_dual]
protected theorem Filter.Tendsto.max_right {l : Filter β} {a : α} (h : Tendsto f l (𝓝 a)) :
    Tendsto (fun i => max a (f i)) l (𝓝 a) := by
  simpa only [sup_idem] using (tendsto_const_nhds (x := a)).max h

@[to_dual]
protected theorem Filter.Tendsto.max_left {l : Filter β} {a : α} (h : Tendsto f l (𝓝 a)) :
    Tendsto (fun i => max (f i) a) l (𝓝 a) := by
  simp_rw [max_comm _ a]
  exact h.max_right

@[to_dual]
theorem Filter.tendsto_nhds_max_right {l : Filter β} {a : α} (h : Tendsto f l (𝓝[>] a)) :
    Tendsto (fun i => max a (f i)) l (𝓝[>] a) := by
  obtain ⟨h₁, h₂⟩ := tendsto_nhdsWithin_iff.mp h
  exact tendsto_nhdsWithin_iff.mpr ⟨h₁.max_right, h₂.mono fun i hi => lt_max_of_lt_right hi⟩

@[to_dual]
theorem Filter.tendsto_nhds_max_left {l : Filter β} {a : α} (h : Tendsto f l (𝓝[>] a)) :
    Tendsto (fun i => max (f i) a) l (𝓝[>] a) := by
  simp_rw [max_comm _ a]
  exact Filter.tendsto_nhds_max_right h

@[to_dual self]
theorem Dense.exists_between [DenselyOrdered α] {s : Set α} (hs : Dense s) {x y : α} (h : x < y) :
    ∃ z ∈ s, z ∈ Ioo x y :=
  hs.exists_mem_open isOpen_Ioo (nonempty_Ioo.2 h)

@[to_dual]
theorem Dense.Ioi_eq_biUnion [DenselyOrdered α] {s : Set α} (hs : Dense s) (x : α) :
    Ioi x = ⋃ y ∈ s ∩ Ioi x, Ioi y := by
  refine Subset.antisymm (fun z hz ↦ ?_) (iUnion₂_subset fun y hy ↦ Ioi_subset_Ioi (le_of_lt hy.2))
  rcases hs.exists_between hz with ⟨y, hys, hy⟩
  exact mem_iUnion₂.2 ⟨y, ⟨hys, hy.1⟩, hy.2⟩

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
