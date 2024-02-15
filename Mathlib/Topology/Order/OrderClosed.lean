/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
import Mathlib.Topology.Separation

/-!
# Order-closed topologies

In this file we introduce 3 typeclass mixins that relate topology and order structures:

- `ClosedIicTopology` says that all the intervals $(-∞, a]$ (formally, `Set.Iic a`)
  are closed sets;
- `ClosedIciTopoplogy` says that all the intervals $[a, +∞)$ (formally, `Set.Ici a`)
  are closed sets;
- `OrderClosedTopology` says that the set of points `(x, y)` such that `x ≤ y`
  is closed in the product topology.

The last predicate implies the first two.

We prove many basic properties of such topologies.

## Main statements

This file contains the proofs of the following facts.
For exact requirements
(`OrderClosedTopology` vs `ClosedIciTopoplogy` vs `ClosedIicTopology,
`Preorder` vs `PartialOrder` vs `LinearOrder` etc)
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

open Set Filter
open OrderDual (toDual)
open scoped Topology

universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}

/-- If `α` is a topological space and a preorder, `ClosedIicTopology α` means that `Iic a` is
closed for all `a : α`. -/
class ClosedIicTopology (α : Type*) [TopologicalSpace α] [Preorder α] : Prop where
  /-- For any `a`, the set `{b | b ≤ a}` is closed. -/
  isClosed_le' (a : α) : IsClosed { b : α | b ≤ a }

export ClosedIicTopology (isClosed_le')
#align is_closed_le' ClosedIicTopology.isClosed_le'

/-- If `α` is a topological space and a preorder, `ClosedIciTopology α` means that `Ici a` is
closed for all `a : α`. -/
class ClosedIciTopology (α : Type*) [TopologicalSpace α] [Preorder α] : Prop where
  /-- For any `a`, the set `{b | a ≤ b}` is closed. -/
  isClosed_ge' (a : α) : IsClosed { b : α | a ≤ b }

export ClosedIciTopology (isClosed_ge')
#align is_closed_ge' ClosedIciTopology.isClosed_ge'

/-- A topology on a set which is both a topological space and a preorder is _order-closed_ if the
set of points `(x, y)` with `x ≤ y` is closed in the product space. We introduce this as a mixin.
This property is satisfied for the order topology on a linear order, but it can be satisfied more
generally, and suffices to derive many interesting properties relating order and topology. -/
class OrderClosedTopology (α : Type*) [TopologicalSpace α] [Preorder α] : Prop where
  /-- The set `{ (x, y) | x ≤ y }` is a closed set. -/
  isClosed_le' : IsClosed { p : α × α | p.1 ≤ p.2 }
#align order_closed_topology OrderClosedTopology

instance [TopologicalSpace α] [h : FirstCountableTopology α] : FirstCountableTopology αᵒᵈ := h
instance [TopologicalSpace α] [h : SecondCountableTopology α] : SecondCountableTopology αᵒᵈ := h

theorem Dense.orderDual [TopologicalSpace α] {s : Set α} (hs : Dense s) :
    Dense (OrderDual.ofDual ⁻¹' s) :=
  hs
#align dense.order_dual Dense.orderDual

section General
variable [TopologicalSpace α] [Preorder α] {s : Set α}

protected lemma BddAbove.of_closure : BddAbove (closure s) → BddAbove s :=
  BddAbove.mono subset_closure

protected lemma BddBelow.of_closure : BddBelow (closure s) → BddBelow s :=
  BddBelow.mono subset_closure

end General

section ClosedIicTopology

variable [TopologicalSpace α] [Preorder α] [ClosedIicTopology α] {s : Set α}

instance : ClosedIciTopology αᵒᵈ where
  isClosed_ge' a := isClosed_le' (α := α) a

theorem isClosed_Iic {a : α} : IsClosed (Iic a) :=
  isClosed_le' a
#align is_closed_Iic isClosed_Iic

@[simp]
theorem closure_Iic (a : α) : closure (Iic a) = Iic a :=
  isClosed_Iic.closure_eq
#align closure_Iic closure_Iic

theorem le_of_tendsto_of_frequently {f : β → α} {a b : α} {x : Filter β} (lim : Tendsto f x (𝓝 a))
    (h : ∃ᶠ c in x, f c ≤ b) : a ≤ b :=
  (isClosed_le' b).mem_of_frequently_of_tendsto h lim

theorem le_of_tendsto {f : β → α} {a b : α} {x : Filter β} [NeBot x] (lim : Tendsto f x (𝓝 a))
    (h : ∀ᶠ c in x, f c ≤ b) : a ≤ b :=
  (isClosed_le' b).mem_of_tendsto lim h
#align le_of_tendsto le_of_tendsto

theorem le_of_tendsto' {f : β → α} {a b : α} {x : Filter β} [NeBot x] (lim : Tendsto f x (𝓝 a))
    (h : ∀ c, f c ≤ b) : a ≤ b :=
  le_of_tendsto lim (eventually_of_forall h)
#align le_of_tendsto' le_of_tendsto'

@[simp] lemma upperBounds_closure (s : Set α) : upperBounds (closure s : Set α) = upperBounds s :=
  ext fun a ↦ by simp_rw [mem_upperBounds_iff_subset_Iic, isClosed_Iic.closure_subset_iff]
#align upper_bounds_closure upperBounds_closure

@[simp] lemma bddAbove_closure : BddAbove (closure s) ↔ BddAbove s := by
  simp_rw [BddAbove, upperBounds_closure]
#align bdd_above_closure bddAbove_closure

protected alias ⟨_, BddAbove.closure⟩ := bddAbove_closure
#align bdd_above.of_closure BddAbove.of_closure
#align bdd_above.closure BddAbove.closure

end ClosedIicTopology

section ClosedIciTopology

variable [TopologicalSpace α] [Preorder α] [ClosedIciTopology α] {s : Set α}

instance : ClosedIicTopology αᵒᵈ where
  isClosed_le' a := isClosed_ge' (α := α) a

theorem isClosed_Ici {a : α} : IsClosed (Ici a) :=
  isClosed_ge' a
#align is_closed_Ici isClosed_Ici

@[simp]
theorem closure_Ici (a : α) : closure (Ici a) = Ici a :=
  isClosed_Ici.closure_eq
#align closure_Ici closure_Ici

lemma ge_of_tendsto_of_frequently {f : β → α} {a b : α} {x : Filter β} (lim : Tendsto f x (𝓝 a))
    (h : ∃ᶠ c in x, b ≤ f c) : b ≤ a :=
  (isClosed_ge' b).mem_of_frequently_of_tendsto h lim

theorem ge_of_tendsto {f : β → α} {a b : α} {x : Filter β} [NeBot x] (lim : Tendsto f x (𝓝 a))
    (h : ∀ᶠ c in x, b ≤ f c) : b ≤ a :=
  (isClosed_ge' b).mem_of_tendsto lim h
#align ge_of_tendsto ge_of_tendsto

theorem ge_of_tendsto' {f : β → α} {a b : α} {x : Filter β} [NeBot x] (lim : Tendsto f x (𝓝 a))
    (h : ∀ c, b ≤ f c) : b ≤ a :=
  ge_of_tendsto lim (eventually_of_forall h)
#align ge_of_tendsto' ge_of_tendsto'

@[simp] lemma lowerBounds_closure (s : Set α) : lowerBounds (closure s : Set α) = lowerBounds s :=
  ext fun a ↦ by simp_rw [mem_lowerBounds_iff_subset_Ici, isClosed_Ici.closure_subset_iff]
#align lower_bounds_closure lowerBounds_closure

@[simp] lemma bddBelow_closure : BddBelow (closure s) ↔ BddBelow s := by
  simp_rw [BddBelow, lowerBounds_closure]
#align bdd_below_closure bddBelow_closure

protected alias ⟨_, BddBelow.closure⟩ := bddBelow_closure
#align bdd_below.of_closure BddBelow.of_closure
#align bdd_below.closure BddBelow.closure

end ClosedIciTopology

section OrderClosedTopology

section Preorder

variable [TopologicalSpace α] [Preorder α] [t : OrderClosedTopology α]

namespace Subtype

-- todo: add `OrderEmbedding.orderClosedTopology`
instance {p : α → Prop} : OrderClosedTopology (Subtype p) :=
  have this : Continuous fun p : Subtype p × Subtype p => ((p.fst : α), (p.snd : α)) :=
    continuous_subtype_val.prod_map continuous_subtype_val
  OrderClosedTopology.mk (t.isClosed_le'.preimage this)

end Subtype

theorem isClosed_le_prod : IsClosed { p : α × α | p.1 ≤ p.2 } :=
  t.isClosed_le'
#align is_closed_le_prod isClosed_le_prod

theorem isClosed_le [TopologicalSpace β] {f g : β → α} (hf : Continuous f) (hg : Continuous g) :
    IsClosed { b | f b ≤ g b } :=
  continuous_iff_isClosed.mp (hf.prod_mk hg) _ isClosed_le_prod
#align is_closed_le isClosed_le

instance : ClosedIicTopology α where
  isClosed_le' _ := isClosed_le continuous_id continuous_const

instance : ClosedIciTopology α where
  isClosed_ge' _ := isClosed_le continuous_const continuous_id

instance : OrderClosedTopology αᵒᵈ :=
  ⟨(OrderClosedTopology.isClosed_le' (α := α)).preimage continuous_swap⟩

theorem isClosed_Icc {a b : α} : IsClosed (Icc a b) :=
  IsClosed.inter isClosed_Ici isClosed_Iic
#align is_closed_Icc isClosed_Icc

@[simp]
theorem closure_Icc (a b : α) : closure (Icc a b) = Icc a b :=
  isClosed_Icc.closure_eq
#align closure_Icc closure_Icc

theorem le_of_tendsto_of_tendsto {f g : β → α} {b : Filter β} {a₁ a₂ : α} [NeBot b]
    (hf : Tendsto f b (𝓝 a₁)) (hg : Tendsto g b (𝓝 a₂)) (h : f ≤ᶠ[b] g) : a₁ ≤ a₂ :=
  have : Tendsto (fun b => (f b, g b)) b (𝓝 (a₁, a₂)) := hf.prod_mk_nhds hg
  show (a₁, a₂) ∈ { p : α × α | p.1 ≤ p.2 } from t.isClosed_le'.mem_of_tendsto this h
#align le_of_tendsto_of_tendsto le_of_tendsto_of_tendsto

alias tendsto_le_of_eventuallyLE := le_of_tendsto_of_tendsto
#align tendsto_le_of_eventually_le tendsto_le_of_eventuallyLE

theorem le_of_tendsto_of_tendsto' {f g : β → α} {b : Filter β} {a₁ a₂ : α} [NeBot b]
    (hf : Tendsto f b (𝓝 a₁)) (hg : Tendsto g b (𝓝 a₂)) (h : ∀ x, f x ≤ g x) : a₁ ≤ a₂ :=
  le_of_tendsto_of_tendsto hf hg (eventually_of_forall h)
#align le_of_tendsto_of_tendsto' le_of_tendsto_of_tendsto'

@[simp]
theorem closure_le_eq [TopologicalSpace β] {f g : β → α} (hf : Continuous f) (hg : Continuous g) :
    closure { b | f b ≤ g b } = { b | f b ≤ g b } :=
  (isClosed_le hf hg).closure_eq
#align closure_le_eq closure_le_eq

theorem closure_lt_subset_le [TopologicalSpace β] {f g : β → α} (hf : Continuous f)
    (hg : Continuous g) : closure { b | f b < g b } ⊆ { b | f b ≤ g b } :=
  (closure_minimal fun _ => le_of_lt) <| isClosed_le hf hg
#align closure_lt_subset_le closure_lt_subset_le

theorem ContinuousWithinAt.closure_le [TopologicalSpace β] {f g : β → α} {s : Set β} {x : β}
    (hx : x ∈ closure s) (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x)
    (h : ∀ y ∈ s, f y ≤ g y) : f x ≤ g x :=
  show (f x, g x) ∈ { p : α × α | p.1 ≤ p.2 } from
    OrderClosedTopology.isClosed_le'.closure_subset ((hf.prod hg).mem_closure hx h)
#align continuous_within_at.closure_le ContinuousWithinAt.closure_le

/-- If `s` is a closed set and two functions `f` and `g` are continuous on `s`,
then the set `{x ∈ s | f x ≤ g x}` is a closed set. -/
theorem IsClosed.isClosed_le [TopologicalSpace β] {f g : β → α} {s : Set β} (hs : IsClosed s)
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) : IsClosed ({ x ∈ s | f x ≤ g x }) :=
  (hf.prod hg).preimage_isClosed_of_isClosed hs OrderClosedTopology.isClosed_le'
#align is_closed.is_closed_le IsClosed.isClosed_le

theorem le_on_closure [TopologicalSpace β] {f g : β → α} {s : Set β} (h : ∀ x ∈ s, f x ≤ g x)
    (hf : ContinuousOn f (closure s)) (hg : ContinuousOn g (closure s)) ⦃x⦄ (hx : x ∈ closure s) :
    f x ≤ g x :=
  have : s ⊆ { y ∈ closure s | f y ≤ g y } := fun y hy => ⟨subset_closure hy, h y hy⟩
  (closure_minimal this (isClosed_closure.isClosed_le hf hg) hx).2
#align le_on_closure le_on_closure

theorem IsClosed.epigraph [TopologicalSpace β] {f : β → α} {s : Set β} (hs : IsClosed s)
    (hf : ContinuousOn f s) : IsClosed { p : β × α | p.1 ∈ s ∧ f p.1 ≤ p.2 } :=
  (hs.preimage continuous_fst).isClosed_le (hf.comp continuousOn_fst Subset.rfl) continuousOn_snd
#align is_closed.epigraph IsClosed.epigraph

theorem IsClosed.hypograph [TopologicalSpace β] {f : β → α} {s : Set β} (hs : IsClosed s)
    (hf : ContinuousOn f s) : IsClosed { p : β × α | p.1 ∈ s ∧ p.2 ≤ f p.1 } :=
  (hs.preimage continuous_fst).isClosed_le continuousOn_snd (hf.comp continuousOn_fst Subset.rfl)
#align is_closed.hypograph IsClosed.hypograph

end Preorder

section PartialOrder

variable [TopologicalSpace α] [PartialOrder α] [t : OrderClosedTopology α]

-- see Note [lower instance priority]
instance (priority := 90) OrderClosedTopology.to_t2Space : T2Space α :=
  t2_iff_isClosed_diagonal.2 <| by
    simpa only [diagonal, le_antisymm_iff] using
      t.isClosed_le'.inter (isClosed_le continuous_snd continuous_fst)
#align order_closed_topology.to_t2_space OrderClosedTopology.to_t2Space

end PartialOrder

section LinearOrder

variable [TopologicalSpace α] [LinearOrder α] [OrderClosedTopology α]

theorem isOpen_lt [TopologicalSpace β] {f g : β → α} (hf : Continuous f) (hg : Continuous g) :
    IsOpen { b | f b < g b } := by
  simpa only [lt_iff_not_le] using (isClosed_le hg hf).isOpen_compl
#align is_open_lt isOpen_lt

theorem isOpen_lt_prod : IsOpen { p : α × α | p.1 < p.2 } :=
  isOpen_lt continuous_fst continuous_snd
#align is_open_lt_prod isOpen_lt_prod

variable {a b : α}

theorem isOpen_Iio : IsOpen (Iio a) :=
  isOpen_lt continuous_id continuous_const
#align is_open_Iio isOpen_Iio

theorem isOpen_Ioi : IsOpen (Ioi a) :=
  isOpen_lt continuous_const continuous_id
#align is_open_Ioi isOpen_Ioi

theorem isOpen_Ioo : IsOpen (Ioo a b) :=
  IsOpen.inter isOpen_Ioi isOpen_Iio
#align is_open_Ioo isOpen_Ioo

@[simp]
theorem interior_Ioi : interior (Ioi a) = Ioi a :=
  isOpen_Ioi.interior_eq
#align interior_Ioi interior_Ioi

@[simp]
theorem interior_Iio : interior (Iio a) = Iio a :=
  isOpen_Iio.interior_eq
#align interior_Iio interior_Iio

@[simp]
theorem interior_Ioo : interior (Ioo a b) = Ioo a b :=
  isOpen_Ioo.interior_eq
#align interior_Ioo interior_Ioo

theorem Ioo_subset_closure_interior : Ioo a b ⊆ closure (interior (Ioo a b)) := by
  simp only [interior_Ioo, subset_closure]
#align Ioo_subset_closure_interior Ioo_subset_closure_interior

theorem Iio_mem_nhds {a b : α} (h : a < b) : Iio b ∈ 𝓝 a :=
  IsOpen.mem_nhds isOpen_Iio h
#align Iio_mem_nhds Iio_mem_nhds

theorem Ioi_mem_nhds {a b : α} (h : a < b) : Ioi a ∈ 𝓝 b :=
  IsOpen.mem_nhds isOpen_Ioi h
#align Ioi_mem_nhds Ioi_mem_nhds

theorem Iic_mem_nhds {a b : α} (h : a < b) : Iic b ∈ 𝓝 a :=
  mem_of_superset (Iio_mem_nhds h) Iio_subset_Iic_self
#align Iic_mem_nhds Iic_mem_nhds

theorem Ici_mem_nhds {a b : α} (h : a < b) : Ici a ∈ 𝓝 b :=
  mem_of_superset (Ioi_mem_nhds h) Ioi_subset_Ici_self
#align Ici_mem_nhds Ici_mem_nhds

theorem Ioo_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Ioo a b ∈ 𝓝 x :=
  IsOpen.mem_nhds isOpen_Ioo ⟨ha, hb⟩
#align Ioo_mem_nhds Ioo_mem_nhds

theorem Ioc_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Ioc a b ∈ 𝓝 x :=
  mem_of_superset (Ioo_mem_nhds ha hb) Ioo_subset_Ioc_self
#align Ioc_mem_nhds Ioc_mem_nhds

theorem Ico_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Ico a b ∈ 𝓝 x :=
  mem_of_superset (Ioo_mem_nhds ha hb) Ioo_subset_Ico_self
#align Ico_mem_nhds Ico_mem_nhds

theorem Icc_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Icc a b ∈ 𝓝 x :=
  mem_of_superset (Ioo_mem_nhds ha hb) Ioo_subset_Icc_self
#align Icc_mem_nhds Icc_mem_nhds

theorem eventually_lt_of_tendsto_lt {l : Filter γ} {f : γ → α} {u v : α} (hv : v < u)
    (h : Filter.Tendsto f l (𝓝 v)) : ∀ᶠ a in l, f a < u :=
  tendsto_nhds.1 h (· < u) isOpen_Iio hv
#align eventually_lt_of_tendsto_lt eventually_lt_of_tendsto_lt

theorem eventually_gt_of_tendsto_gt {l : Filter γ} {f : γ → α} {u v : α} (hv : u < v)
    (h : Filter.Tendsto f l (𝓝 v)) : ∀ᶠ a in l, u < f a :=
  tendsto_nhds.1 h (· > u) isOpen_Ioi hv
#align eventually_gt_of_tendsto_gt eventually_gt_of_tendsto_gt

theorem eventually_le_of_tendsto_lt {l : Filter γ} {f : γ → α} {u v : α} (hv : v < u)
    (h : Tendsto f l (𝓝 v)) : ∀ᶠ a in l, f a ≤ u :=
  (eventually_lt_of_tendsto_lt hv h).mono fun _ => le_of_lt
#align eventually_le_of_tendsto_lt eventually_le_of_tendsto_lt

theorem eventually_ge_of_tendsto_gt {l : Filter γ} {f : γ → α} {u v : α} (hv : u < v)
    (h : Tendsto f l (𝓝 v)) : ∀ᶠ a in l, u ≤ f a :=
  (eventually_gt_of_tendsto_gt hv h).mono fun _ => le_of_lt
#align eventually_ge_of_tendsto_gt eventually_ge_of_tendsto_gt

variable [TopologicalSpace γ]

/-!
### Neighborhoods to the left and to the right on an `OrderClosedTopology`

Limits to the left and to the right of real functions are defined in terms of neighborhoods to
the left and to the right, either open or closed, i.e., members of `𝓝[>] a` and
`𝓝[≥] a` on the right, and similarly on the left. Here we simply prove that all
right-neighborhoods of a point are equal, and we'll prove later other useful characterizations which
require the stronger hypothesis `OrderTopology α` -/


/-!
#### Right neighborhoods, point excluded
-/

theorem Ioo_mem_nhdsWithin_Ioi {a b c : α} (H : b ∈ Ico a c) : Ioo a c ∈ 𝓝[>] b :=
  mem_nhdsWithin.2
    ⟨Iio c, isOpen_Iio, H.2, by rw [inter_comm, Ioi_inter_Iio]; exact Ioo_subset_Ioo_left H.1⟩
#align Ioo_mem_nhds_within_Ioi Ioo_mem_nhdsWithin_Ioi

-- porting note: new lemma; todo: swap `'`?
theorem Ioo_mem_nhdsWithin_Ioi' {a b : α} (H : a < b) : Ioo a b ∈ 𝓝[>] a :=
  Ioo_mem_nhdsWithin_Ioi ⟨le_rfl, H⟩

theorem CovBy.nhdsWithin_Ioi {a b : α} (h : a ⋖ b) : 𝓝[>] a = ⊥ :=
  empty_mem_iff_bot.mp <| h.Ioo_eq ▸ Ioo_mem_nhdsWithin_Ioi' h.1

theorem Ioc_mem_nhdsWithin_Ioi {a b c : α} (H : b ∈ Ico a c) : Ioc a c ∈ 𝓝[>] b :=
  mem_of_superset (Ioo_mem_nhdsWithin_Ioi H) Ioo_subset_Ioc_self
#align Ioc_mem_nhds_within_Ioi Ioc_mem_nhdsWithin_Ioi

-- porting note: new lemma; todo: swap `'`?
theorem Ioc_mem_nhdsWithin_Ioi' {a b : α} (H : a < b) : Ioc a b ∈ 𝓝[>] a :=
  Ioc_mem_nhdsWithin_Ioi ⟨le_rfl, H⟩

theorem Ico_mem_nhdsWithin_Ioi {a b c : α} (H : b ∈ Ico a c) : Ico a c ∈ 𝓝[>] b :=
  mem_of_superset (Ioo_mem_nhdsWithin_Ioi H) Ioo_subset_Ico_self
#align Ico_mem_nhds_within_Ioi Ico_mem_nhdsWithin_Ioi

-- porting note: new lemma; todo: swap `'`?
theorem Ico_mem_nhdsWithin_Ioi' {a b : α} (H : a < b) : Ico a b ∈ 𝓝[>] a :=
  Ico_mem_nhdsWithin_Ioi ⟨le_rfl, H⟩

theorem Icc_mem_nhdsWithin_Ioi {a b c : α} (H : b ∈ Ico a c) : Icc a c ∈ 𝓝[>] b :=
  mem_of_superset (Ioo_mem_nhdsWithin_Ioi H) Ioo_subset_Icc_self
#align Icc_mem_nhds_within_Ioi Icc_mem_nhdsWithin_Ioi

-- porting note: new lemma; todo: swap `'`?
theorem Icc_mem_nhdsWithin_Ioi' {a b : α} (H : a < b) : Icc a b ∈ 𝓝[>] a :=
  Icc_mem_nhdsWithin_Ioi ⟨le_rfl, H⟩

@[simp]
theorem nhdsWithin_Ioc_eq_nhdsWithin_Ioi {a b : α} (h : a < b) : 𝓝[Ioc a b] a = 𝓝[>] a :=
  nhdsWithin_inter_of_mem' <| nhdsWithin_le_nhds <| Iic_mem_nhds h
#align nhds_within_Ioc_eq_nhds_within_Ioi nhdsWithin_Ioc_eq_nhdsWithin_Ioi

@[simp]
theorem nhdsWithin_Ioo_eq_nhdsWithin_Ioi {a b : α} (h : a < b) : 𝓝[Ioo a b] a = 𝓝[>] a :=
  nhdsWithin_inter_of_mem' <| nhdsWithin_le_nhds <| Iio_mem_nhds h
#align nhds_within_Ioo_eq_nhds_within_Ioi nhdsWithin_Ioo_eq_nhdsWithin_Ioi

@[simp]
theorem continuousWithinAt_Ioc_iff_Ioi [TopologicalSpace β] {a b : α} {f : α → β} (h : a < b) :
    ContinuousWithinAt f (Ioc a b) a ↔ ContinuousWithinAt f (Ioi a) a := by
  simp only [ContinuousWithinAt, nhdsWithin_Ioc_eq_nhdsWithin_Ioi h]
#align continuous_within_at_Ioc_iff_Ioi continuousWithinAt_Ioc_iff_Ioi

@[simp]
theorem continuousWithinAt_Ioo_iff_Ioi [TopologicalSpace β] {a b : α} {f : α → β} (h : a < b) :
    ContinuousWithinAt f (Ioo a b) a ↔ ContinuousWithinAt f (Ioi a) a := by
  simp only [ContinuousWithinAt, nhdsWithin_Ioo_eq_nhdsWithin_Ioi h]
#align continuous_within_at_Ioo_iff_Ioi continuousWithinAt_Ioo_iff_Ioi

/-!
#### Left neighborhoods, point excluded
-/

theorem Ioo_mem_nhdsWithin_Iio {a b c : α} (H : b ∈ Ioc a c) : Ioo a c ∈ 𝓝[<] b := by
  simpa only [dual_Ioo] using
    Ioo_mem_nhdsWithin_Ioi (show toDual b ∈ Ico (toDual c) (toDual a) from H.symm)
#align Ioo_mem_nhds_within_Iio Ioo_mem_nhdsWithin_Iio

-- porting note: new lemma; todo: swap `'`?
theorem Ioo_mem_nhdsWithin_Iio' {a b : α} (H : a < b) : Ioo a b ∈ 𝓝[<] b :=
  Ioo_mem_nhdsWithin_Iio ⟨H, le_rfl⟩

theorem CovBy.nhdsWithin_Iio {a b : α} (h : a ⋖ b) : 𝓝[<] b = ⊥ :=
  empty_mem_iff_bot.mp <| h.Ioo_eq ▸ Ioo_mem_nhdsWithin_Iio' h.1

theorem Ico_mem_nhdsWithin_Iio {a b c : α} (H : b ∈ Ioc a c) : Ico a c ∈ 𝓝[<] b :=
  mem_of_superset (Ioo_mem_nhdsWithin_Iio H) Ioo_subset_Ico_self
#align Ico_mem_nhds_within_Iio Ico_mem_nhdsWithin_Iio

-- porting note: new lemma; todo: swap `'`?
theorem Ico_mem_nhdsWithin_Iio' {a b : α} (H : a < b) : Ico a b ∈ 𝓝[<] b :=
  Ico_mem_nhdsWithin_Iio ⟨H, le_rfl⟩

theorem Ioc_mem_nhdsWithin_Iio {a b c : α} (H : b ∈ Ioc a c) : Ioc a c ∈ 𝓝[<] b :=
  mem_of_superset (Ioo_mem_nhdsWithin_Iio H) Ioo_subset_Ioc_self
#align Ioc_mem_nhds_within_Iio Ioc_mem_nhdsWithin_Iio

-- porting note: new lemma; todo: swap `'`?
theorem Ioc_mem_nhdsWithin_Iio' {a b : α} (H : a < b) : Ioc a b ∈ 𝓝[<] b :=
  Ioc_mem_nhdsWithin_Iio ⟨H, le_rfl⟩

theorem Icc_mem_nhdsWithin_Iio {a b c : α} (H : b ∈ Ioc a c) : Icc a c ∈ 𝓝[<] b :=
  mem_of_superset (Ioo_mem_nhdsWithin_Iio H) Ioo_subset_Icc_self
#align Icc_mem_nhds_within_Iio Icc_mem_nhdsWithin_Iio

theorem Icc_mem_nhdsWithin_Iio' {a b : α} (H : a < b) : Icc a b ∈ 𝓝[<] b :=
  Icc_mem_nhdsWithin_Iio ⟨H, le_rfl⟩

@[simp]
theorem nhdsWithin_Ico_eq_nhdsWithin_Iio {a b : α} (h : a < b) : 𝓝[Ico a b] b = 𝓝[<] b := by
  simpa only [dual_Ioc] using nhdsWithin_Ioc_eq_nhdsWithin_Ioi h.dual
#align nhds_within_Ico_eq_nhds_within_Iio nhdsWithin_Ico_eq_nhdsWithin_Iio

@[simp]
theorem nhdsWithin_Ioo_eq_nhdsWithin_Iio {a b : α} (h : a < b) : 𝓝[Ioo a b] b = 𝓝[<] b := by
  simpa only [dual_Ioo] using nhdsWithin_Ioo_eq_nhdsWithin_Ioi h.dual
#align nhds_within_Ioo_eq_nhds_within_Iio nhdsWithin_Ioo_eq_nhdsWithin_Iio

@[simp]
theorem continuousWithinAt_Ico_iff_Iio {a b : α} {f : α → γ} (h : a < b) :
    ContinuousWithinAt f (Ico a b) b ↔ ContinuousWithinAt f (Iio b) b := by
  simp only [ContinuousWithinAt, nhdsWithin_Ico_eq_nhdsWithin_Iio h]
#align continuous_within_at_Ico_iff_Iio continuousWithinAt_Ico_iff_Iio

@[simp]
theorem continuousWithinAt_Ioo_iff_Iio {a b : α} {f : α → γ} (h : a < b) :
    ContinuousWithinAt f (Ioo a b) b ↔ ContinuousWithinAt f (Iio b) b := by
  simp only [ContinuousWithinAt, nhdsWithin_Ioo_eq_nhdsWithin_Iio h]
#align continuous_within_at_Ioo_iff_Iio continuousWithinAt_Ioo_iff_Iio

/-!
#### Right neighborhoods, point included
-/

theorem Ioo_mem_nhdsWithin_Ici {a b c : α} (H : b ∈ Ioo a c) : Ioo a c ∈ 𝓝[≥] b :=
  mem_nhdsWithin_of_mem_nhds <| IsOpen.mem_nhds isOpen_Ioo H
#align Ioo_mem_nhds_within_Ici Ioo_mem_nhdsWithin_Ici

theorem Ioc_mem_nhdsWithin_Ici {a b c : α} (H : b ∈ Ioo a c) : Ioc a c ∈ 𝓝[≥] b :=
  mem_of_superset (Ioo_mem_nhdsWithin_Ici H) Ioo_subset_Ioc_self
#align Ioc_mem_nhds_within_Ici Ioc_mem_nhdsWithin_Ici

theorem Ico_mem_nhdsWithin_Ici {a b c : α} (H : b ∈ Ico a c) : Ico a c ∈ 𝓝[≥] b :=
  mem_nhdsWithin.2
    ⟨Iio c, isOpen_Iio, H.2, by simp only [inter_comm, Ici_inter_Iio, Ico_subset_Ico_left H.1]⟩
#align Ico_mem_nhds_within_Ici Ico_mem_nhdsWithin_Ici

theorem Ico_mem_nhdsWithin_Ici' {a b : α} (H : a < b) : Ico a b ∈ 𝓝[≥] a :=
  Ico_mem_nhdsWithin_Ici ⟨le_rfl, H⟩

theorem Icc_mem_nhdsWithin_Ici {a b c : α} (H : b ∈ Ico a c) : Icc a c ∈ 𝓝[≥] b :=
  mem_of_superset (Ico_mem_nhdsWithin_Ici H) Ico_subset_Icc_self
#align Icc_mem_nhds_within_Ici Icc_mem_nhdsWithin_Ici

theorem Icc_mem_nhdsWithin_Ici' {a b : α} (H : a < b) : Icc a b ∈ 𝓝[≥] a :=
  Icc_mem_nhdsWithin_Ici ⟨le_rfl, H⟩

@[simp]
theorem nhdsWithin_Icc_eq_nhdsWithin_Ici {a b : α} (h : a < b) : 𝓝[Icc a b] a = 𝓝[≥] a :=
  nhdsWithin_inter_of_mem' <| nhdsWithin_le_nhds <| Iic_mem_nhds h
#align nhds_within_Icc_eq_nhds_within_Ici nhdsWithin_Icc_eq_nhdsWithin_Ici

@[simp]
theorem nhdsWithin_Ico_eq_nhdsWithin_Ici {a b : α} (h : a < b) : 𝓝[Ico a b] a = 𝓝[≥] a :=
  nhdsWithin_inter_of_mem' <| nhdsWithin_le_nhds <| Iio_mem_nhds h
#align nhds_within_Ico_eq_nhds_within_Ici nhdsWithin_Ico_eq_nhdsWithin_Ici

@[simp]
theorem continuousWithinAt_Icc_iff_Ici [TopologicalSpace β] {a b : α} {f : α → β} (h : a < b) :
    ContinuousWithinAt f (Icc a b) a ↔ ContinuousWithinAt f (Ici a) a := by
  simp only [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsWithin_Ici h]
#align continuous_within_at_Icc_iff_Ici continuousWithinAt_Icc_iff_Ici

@[simp]
theorem continuousWithinAt_Ico_iff_Ici [TopologicalSpace β] {a b : α} {f : α → β} (h : a < b) :
    ContinuousWithinAt f (Ico a b) a ↔ ContinuousWithinAt f (Ici a) a := by
  simp only [ContinuousWithinAt, nhdsWithin_Ico_eq_nhdsWithin_Ici h]
#align continuous_within_at_Ico_iff_Ici continuousWithinAt_Ico_iff_Ici

/-!
#### Left neighborhoods, point included
-/


theorem Ioo_mem_nhdsWithin_Iic {a b c : α} (H : b ∈ Ioo a c) : Ioo a c ∈ 𝓝[≤] b :=
  mem_nhdsWithin_of_mem_nhds <| IsOpen.mem_nhds isOpen_Ioo H
#align Ioo_mem_nhds_within_Iic Ioo_mem_nhdsWithin_Iic

theorem Ico_mem_nhdsWithin_Iic {a b c : α} (H : b ∈ Ioo a c) : Ico a c ∈ 𝓝[≤] b :=
  mem_of_superset (Ioo_mem_nhdsWithin_Iic H) Ioo_subset_Ico_self
#align Ico_mem_nhds_within_Iic Ico_mem_nhdsWithin_Iic

theorem Ioc_mem_nhdsWithin_Iic {a b c : α} (H : b ∈ Ioc a c) : Ioc a c ∈ 𝓝[≤] b := by
  simpa only [dual_Ico] using
    Ico_mem_nhdsWithin_Ici (show toDual b ∈ Ico (toDual c) (toDual a) from H.symm)
#align Ioc_mem_nhds_within_Iic Ioc_mem_nhdsWithin_Iic

theorem Ioc_mem_nhdsWithin_Iic' {a b : α} (H : a < b) : Ioc a b ∈ 𝓝[≤] b :=
  Ioc_mem_nhdsWithin_Iic ⟨H, le_rfl⟩

theorem Icc_mem_nhdsWithin_Iic {a b c : α} (H : b ∈ Ioc a c) : Icc a c ∈ 𝓝[≤] b :=
  mem_of_superset (Ioc_mem_nhdsWithin_Iic H) Ioc_subset_Icc_self
#align Icc_mem_nhds_within_Iic Icc_mem_nhdsWithin_Iic

theorem Icc_mem_nhdsWithin_Iic' {a b : α} (H : a < b) : Icc a b ∈ 𝓝[≤] b :=
  Icc_mem_nhdsWithin_Iic ⟨H, le_rfl⟩

@[simp]
theorem nhdsWithin_Icc_eq_nhdsWithin_Iic {a b : α} (h : a < b) : 𝓝[Icc a b] b = 𝓝[≤] b := by
  simpa only [dual_Icc] using nhdsWithin_Icc_eq_nhdsWithin_Ici h.dual
#align nhds_within_Icc_eq_nhds_within_Iic nhdsWithin_Icc_eq_nhdsWithin_Iic

@[simp]
theorem nhdsWithin_Ioc_eq_nhdsWithin_Iic {a b : α} (h : a < b) : 𝓝[Ioc a b] b = 𝓝[≤] b := by
  simpa only [dual_Ico] using nhdsWithin_Ico_eq_nhdsWithin_Ici h.dual
#align nhds_within_Ioc_eq_nhds_within_Iic nhdsWithin_Ioc_eq_nhdsWithin_Iic

@[simp]
theorem continuousWithinAt_Icc_iff_Iic [TopologicalSpace β] {a b : α} {f : α → β} (h : a < b) :
    ContinuousWithinAt f (Icc a b) b ↔ ContinuousWithinAt f (Iic b) b := by
  simp only [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsWithin_Iic h]
#align continuous_within_at_Icc_iff_Iic continuousWithinAt_Icc_iff_Iic

@[simp]
theorem continuousWithinAt_Ioc_iff_Iic [TopologicalSpace β] {a b : α} {f : α → β} (h : a < b) :
    ContinuousWithinAt f (Ioc a b) b ↔ ContinuousWithinAt f (Iic b) b := by
  simp only [ContinuousWithinAt, nhdsWithin_Ioc_eq_nhdsWithin_Iic h]
#align continuous_within_at_Ioc_iff_Iic continuousWithinAt_Ioc_iff_Iic

end LinearOrder

section LinearOrder

variable [TopologicalSpace α] [LinearOrder α] [OrderClosedTopology α] {f g : β → α}

section

variable [TopologicalSpace β]

theorem lt_subset_interior_le (hf : Continuous f) (hg : Continuous g) :
    { b | f b < g b } ⊆ interior { b | f b ≤ g b } :=
  (interior_maximal fun _ => le_of_lt) <| isOpen_lt hf hg
#align lt_subset_interior_le lt_subset_interior_le

theorem frontier_le_subset_eq (hf : Continuous f) (hg : Continuous g) :
    frontier { b | f b ≤ g b } ⊆ { b | f b = g b } := by
  rw [frontier_eq_closure_inter_closure, closure_le_eq hf hg]
  rintro b ⟨hb₁, hb₂⟩
  refine' le_antisymm hb₁ (closure_lt_subset_le hg hf _)
  convert hb₂ using 2; simp only [not_le.symm]; rfl
#align frontier_le_subset_eq frontier_le_subset_eq

theorem frontier_Iic_subset (a : α) : frontier (Iic a) ⊆ {a} :=
  frontier_le_subset_eq (@continuous_id α _) continuous_const
#align frontier_Iic_subset frontier_Iic_subset

theorem frontier_Ici_subset (a : α) : frontier (Ici a) ⊆ {a} :=
  frontier_Iic_subset (α := αᵒᵈ) _
#align frontier_Ici_subset frontier_Ici_subset

theorem frontier_lt_subset_eq (hf : Continuous f) (hg : Continuous g) :
    frontier { b | f b < g b } ⊆ { b | f b = g b } := by
  simpa only [← not_lt, ← compl_setOf, frontier_compl, eq_comm] using frontier_le_subset_eq hg hf
#align frontier_lt_subset_eq frontier_lt_subset_eq

theorem continuous_if_le [TopologicalSpace γ] [∀ x, Decidable (f x ≤ g x)] {f' g' : β → γ}
    (hf : Continuous f) (hg : Continuous g) (hf' : ContinuousOn f' { x | f x ≤ g x })
    (hg' : ContinuousOn g' { x | g x ≤ f x }) (hfg : ∀ x, f x = g x → f' x = g' x) :
    Continuous fun x => if f x ≤ g x then f' x else g' x := by
  refine' continuous_if (fun a ha => hfg _ (frontier_le_subset_eq hf hg ha)) _ (hg'.mono _)
  · rwa [(isClosed_le hf hg).closure_eq]
  · simp only [not_le]
    exact closure_lt_subset_le hg hf
#align continuous_if_le continuous_if_le

theorem Continuous.if_le [TopologicalSpace γ] [∀ x, Decidable (f x ≤ g x)] {f' g' : β → γ}
    (hf' : Continuous f') (hg' : Continuous g') (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ x, f x = g x → f' x = g' x) : Continuous fun x => if f x ≤ g x then f' x else g' x :=
  continuous_if_le hf hg hf'.continuousOn hg'.continuousOn hfg
#align continuous.if_le Continuous.if_le

theorem Filter.Tendsto.eventually_lt {l : Filter γ} {f g : γ → α} {y z : α} (hf : Tendsto f l (𝓝 y))
    (hg : Tendsto g l (𝓝 z)) (hyz : y < z) : ∀ᶠ x in l, f x < g x :=
  let ⟨_a, ha, _b, hb, h⟩ := hyz.exists_disjoint_Iio_Ioi
  (hg.eventually (Ioi_mem_nhds hb)).mp <| (hf.eventually (Iio_mem_nhds ha)).mono fun _ h₁ h₂ =>
    h _ h₁ _ h₂
#align tendsto.eventually_lt Filter.Tendsto.eventually_lt

nonrec theorem ContinuousAt.eventually_lt {x₀ : β} (hf : ContinuousAt f x₀) (hg : ContinuousAt g x₀)
    (hfg : f x₀ < g x₀) : ∀ᶠ x in 𝓝 x₀, f x < g x :=
  hf.eventually_lt hg hfg
#align continuous_at.eventually_lt ContinuousAt.eventually_lt

@[continuity, fun_prop]
protected theorem Continuous.min (hf : Continuous f) (hg : Continuous g) :
    Continuous fun b => min (f b) (g b) := by
  simp only [min_def]
  exact hf.if_le hg hf hg fun x => id
#align continuous.min Continuous.min

@[continuity, fun_prop]
protected theorem Continuous.max (hf : Continuous f) (hg : Continuous g) :
    Continuous fun b => max (f b) (g b) :=
  Continuous.min (α := αᵒᵈ) hf hg
#align continuous.max Continuous.max

end

theorem continuous_min : Continuous fun p : α × α => min p.1 p.2 :=
  continuous_fst.min continuous_snd
#align continuous_min continuous_min

theorem continuous_max : Continuous fun p : α × α => max p.1 p.2 :=
  continuous_fst.max continuous_snd
#align continuous_max continuous_max

protected theorem Filter.Tendsto.max {b : Filter β} {a₁ a₂ : α} (hf : Tendsto f b (𝓝 a₁))
    (hg : Tendsto g b (𝓝 a₂)) : Tendsto (fun b => max (f b) (g b)) b (𝓝 (max a₁ a₂)) :=
  (continuous_max.tendsto (a₁, a₂)).comp (hf.prod_mk_nhds hg)
#align filter.tendsto.max Filter.Tendsto.max

protected theorem Filter.Tendsto.min {b : Filter β} {a₁ a₂ : α} (hf : Tendsto f b (𝓝 a₁))
    (hg : Tendsto g b (𝓝 a₂)) : Tendsto (fun b => min (f b) (g b)) b (𝓝 (min a₁ a₂)) :=
  (continuous_min.tendsto (a₁, a₂)).comp (hf.prod_mk_nhds hg)
#align filter.tendsto.min Filter.Tendsto.min

protected theorem Filter.Tendsto.max_right {l : Filter β} {a : α} (h : Tendsto f l (𝓝 a)) :
    Tendsto (fun i => max a (f i)) l (𝓝 a) := by
  convert ((continuous_max.comp (@Continuous.Prod.mk α α _ _ a)).tendsto a).comp h
  simp
#align filter.tendsto.max_right Filter.Tendsto.max_right

protected theorem Filter.Tendsto.max_left {l : Filter β} {a : α} (h : Tendsto f l (𝓝 a)) :
    Tendsto (fun i => max (f i) a) l (𝓝 a) := by
  simp_rw [max_comm _ a]
  exact h.max_right
#align filter.tendsto.max_left Filter.Tendsto.max_left

theorem Filter.tendsto_nhds_max_right {l : Filter β} {a : α} (h : Tendsto f l (𝓝[>] a)) :
    Tendsto (fun i => max a (f i)) l (𝓝[>] a) := by
  obtain ⟨h₁ : Tendsto f l (𝓝 a), h₂ : ∀ᶠ i in l, f i ∈ Ioi a⟩ := tendsto_nhdsWithin_iff.mp h
  exact tendsto_nhdsWithin_iff.mpr ⟨h₁.max_right, h₂.mono fun i hi => lt_max_of_lt_right hi⟩
#align filter.tendsto_nhds_max_right Filter.tendsto_nhds_max_right

theorem Filter.tendsto_nhds_max_left {l : Filter β} {a : α} (h : Tendsto f l (𝓝[>] a)) :
    Tendsto (fun i => max (f i) a) l (𝓝[>] a) := by
  simp_rw [max_comm _ a]
  exact Filter.tendsto_nhds_max_right h
#align filter.tendsto_nhds_max_left Filter.tendsto_nhds_max_left

theorem Filter.Tendsto.min_right {l : Filter β} {a : α} (h : Tendsto f l (𝓝 a)) :
    Tendsto (fun i => min a (f i)) l (𝓝 a) :=
  Filter.Tendsto.max_right (α := αᵒᵈ) h
#align filter.tendsto.min_right Filter.Tendsto.min_right

theorem Filter.Tendsto.min_left {l : Filter β} {a : α} (h : Tendsto f l (𝓝 a)) :
    Tendsto (fun i => min (f i) a) l (𝓝 a) :=
  Filter.Tendsto.max_left (α := αᵒᵈ) h
#align filter.tendsto.min_left Filter.Tendsto.min_left

theorem Filter.tendsto_nhds_min_right {l : Filter β} {a : α} (h : Tendsto f l (𝓝[<] a)) :
    Tendsto (fun i => min a (f i)) l (𝓝[<] a) :=
  Filter.tendsto_nhds_max_right (α := αᵒᵈ) h
#align filter.tendsto_nhds_min_right Filter.tendsto_nhds_min_right

theorem Filter.tendsto_nhds_min_left {l : Filter β} {a : α} (h : Tendsto f l (𝓝[<] a)) :
    Tendsto (fun i => min (f i) a) l (𝓝[<] a) :=
  Filter.tendsto_nhds_max_left (α := αᵒᵈ) h
#align filter.tendsto_nhds_min_left Filter.tendsto_nhds_min_left

protected theorem Dense.exists_lt [NoMinOrder α] {s : Set α} (hs : Dense s) (x : α) :
    ∃ y ∈ s, y < x :=
  hs.exists_mem_open isOpen_Iio (exists_lt x)
#align dense.exists_lt Dense.exists_lt

protected theorem Dense.exists_gt [NoMaxOrder α] {s : Set α} (hs : Dense s) (x : α) :
    ∃ y ∈ s, x < y :=
  hs.orderDual.exists_lt x
#align dense.exists_gt Dense.exists_gt

protected theorem Dense.exists_le [NoMinOrder α] {s : Set α} (hs : Dense s) (x : α) :
    ∃ y ∈ s, y ≤ x :=
  (hs.exists_lt x).imp fun _ h => ⟨h.1, h.2.le⟩
#align dense.exists_le Dense.exists_le

protected theorem Dense.exists_ge [NoMaxOrder α] {s : Set α} (hs : Dense s) (x : α) :
    ∃ y ∈ s, x ≤ y :=
  hs.orderDual.exists_le x
#align dense.exists_ge Dense.exists_ge

theorem Dense.exists_le' {s : Set α} (hs : Dense s) (hbot : ∀ x, IsBot x → x ∈ s) (x : α) :
    ∃ y ∈ s, y ≤ x := by
  by_cases hx : IsBot x
  · exact ⟨x, hbot x hx, le_rfl⟩
  · simp only [IsBot, not_forall, not_le] at hx
    rcases hs.exists_mem_open isOpen_Iio hx with ⟨y, hys, hy : y < x⟩
    exact ⟨y, hys, hy.le⟩
#align dense.exists_le' Dense.exists_le'

theorem Dense.exists_ge' {s : Set α} (hs : Dense s) (htop : ∀ x, IsTop x → x ∈ s) (x : α) :
    ∃ y ∈ s, x ≤ y :=
  hs.orderDual.exists_le' htop x
#align dense.exists_ge' Dense.exists_ge'

theorem Dense.exists_between [DenselyOrdered α] {s : Set α} (hs : Dense s) {x y : α} (h : x < y) :
    ∃ z ∈ s, z ∈ Ioo x y :=
  hs.exists_mem_open isOpen_Ioo (nonempty_Ioo.2 h)
#align dense.exists_between Dense.exists_between

theorem Dense.Ioi_eq_biUnion [DenselyOrdered α] {s : Set α} (hs : Dense s) (x : α) :
    Ioi x = ⋃ y ∈ s ∩ Ioi x, Ioi y := by
  refine Subset.antisymm (fun z hz ↦ ?_) (iUnion₂_subset fun y hy ↦ Ioi_subset_Ioi (le_of_lt hy.2))
  rcases hs.exists_between hz with ⟨y, hys, hxy, hyz⟩
  exact mem_iUnion₂.2 ⟨y, ⟨hys, hxy⟩, hyz⟩

theorem Dense.Iio_eq_biUnion [DenselyOrdered α] {s : Set α} (hs : Dense s) (x : α) :
    Iio x = ⋃ y ∈ s ∩ Iio x, Iio y :=
  Dense.Ioi_eq_biUnion (α := αᵒᵈ) hs x

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
#align pi.order_closed_topology' Pi.orderClosedTopology'

section OrderClosedTopology

variable [TopologicalSpace α] [LinearOrder α] [OrderClosedTopology α] {a b : α}

theorem eventually_le_nhds (hab : a < b) : ∀ᶠ x in 𝓝 a, x ≤ b := Iic_mem_nhds hab
#align eventually_le_nhds eventually_le_nhds

theorem eventually_lt_nhds (hab : a < b) : ∀ᶠ x in 𝓝 a, x < b := Iio_mem_nhds hab
#align eventually_lt_nhds eventually_lt_nhds

theorem eventually_ge_nhds (hab : b < a) : ∀ᶠ x in 𝓝 a, b ≤ x := Ici_mem_nhds hab
#align eventually_ge_nhds eventually_ge_nhds

theorem eventually_gt_nhds (hab : b < a) : ∀ᶠ x in 𝓝 a, b < x := Ioi_mem_nhds hab
#align eventually_gt_nhds eventually_gt_nhds

end OrderClosedTopology

