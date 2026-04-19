/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Alistair Tucker, Wen Yang
-/
module

public import Mathlib.Order.Interval.Set.Image
public import Mathlib.Order.CompleteLatticeIntervals
public import Mathlib.Topology.Order.DenselyOrdered
public import Mathlib.Topology.Order.Monotone
public import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Intermediate Value Theorem

In this file we prove the Intermediate Value Theorem: if `f : α → β` is a function defined on a
connected set `s` that takes both values `≤ a` and values `≥ a` on `s`, then it is equal to `a` at
some point of `s`. We also prove that intervals in a dense conditionally complete order are
preconnected and any preconnected set is an interval. Then we specialize IVT to functions continuous
on intervals.

## Main results

* `IsPreconnected_I??` : all intervals `I??` are preconnected,
* `IsPreconnected.intermediate_value`, `intermediate_value_univ` : Intermediate Value Theorem for
  connected sets and connected spaces, respectively;
* `intermediate_value_Icc`, `intermediate_value_Icc'`: Intermediate Value Theorem for functions
  on closed intervals.

### Miscellaneous facts

* `IsClosed.Icc_subset_of_forall_mem_nhdsWithin` : “Continuous induction” principle;
  if `s ∩ [a, b]` is closed, `a ∈ s`, and for each `x ∈ [a, b) ∩ s` some of its right neighborhoods
  is included in `s`, then `[a, b] ⊆ s`.
* `IsClosed.Icc_subset_of_forall_exists_gt`, `IsClosed.mem_of_ge_of_forall_exists_gt` : two
  other versions of the “continuous induction” principle.
* `ContinuousOn.StrictMonoOn_of_InjOn_Ioo` :
  Every continuous injective `f : (a, b) → δ` is strictly monotone
  or antitone (increasing or decreasing).

## Tags

intermediate value theorem, connected space, connected set
-/

@[expose] public section


open Filter OrderDual TopologicalSpace Function Set
open scoped Topology Filter Interval

universe u v

/-!
### Intermediate value theorem on a (pre)connected space

In this section we prove the following theorem (see `IsPreconnected.intermediate_value₂`): if `f`
and `g` are two functions continuous on a preconnected set `s`, `f a ≤ g a` at some `a ∈ s` and
`g b ≤ f b` at some `b ∈ s`, then `f c = g c` at some `c ∈ s`. We prove several versions of this
statement, including the classical IVT that corresponds to a constant function `g`.
-/

section

variable {X : Type u} {α : Type v} [TopologicalSpace X] [LinearOrder α] [TopologicalSpace α]
  [OrderClosedTopology α]

/-- Intermediate value theorem for two functions: if `f` and `g` are two continuous functions
on a preconnected space and `f a ≤ g a` and `g b ≤ f b`, then for some `x` we have `f x = g x`. -/
theorem intermediate_value_univ₂ [PreconnectedSpace X] {a b : X} {f g : X → α} (hf : Continuous f)
    (hg : Continuous g) (ha : f a ≤ g a) (hb : g b ≤ f b) : ∃ x, f x = g x := by
  obtain ⟨x, _, hfg, hgf⟩ : (univ ∩ { x | f x ≤ g x ∧ g x ≤ f x }).Nonempty :=
    isPreconnected_closed_iff.1 PreconnectedSpace.isPreconnected_univ _ _ (isClosed_le hf hg)
      (isClosed_le hg hf) (fun _ _ => le_total _ _) ⟨a, trivial, ha⟩ ⟨b, trivial, hb⟩
  exact ⟨x, le_antisymm hfg hgf⟩

theorem intermediate_value_univ₂_eventually₁ [PreconnectedSpace X] {a : X} {l : Filter X} [NeBot l]
    {f g : X → α} (hf : Continuous f) (hg : Continuous g) (ha : f a ≤ g a) (he : g ≤ᶠ[l] f) :
    ∃ x, f x = g x :=
  let ⟨_, h⟩ := he.exists; intermediate_value_univ₂ hf hg ha h

theorem intermediate_value_univ₂_eventually₂ [PreconnectedSpace X] {l₁ l₂ : Filter X} [NeBot l₁]
    [NeBot l₂] {f g : X → α} (hf : Continuous f) (hg : Continuous g) (he₁ : f ≤ᶠ[l₁] g)
    (he₂ : g ≤ᶠ[l₂] f) : ∃ x, f x = g x :=
  let ⟨_, h₁⟩ := he₁.exists
  let ⟨_, h₂⟩ := he₂.exists
  intermediate_value_univ₂ hf hg h₁ h₂

/-- Intermediate value theorem for two functions: if `f` and `g` are two functions continuous
on a preconnected set `s` and for some `a b ∈ s` we have `f a ≤ g a` and `g b ≤ f b`,
then for some `x ∈ s` we have `f x = g x`. -/
theorem IsPreconnected.intermediate_value₂ {s : Set X} (hs : IsPreconnected s) {a b : X}
    (ha : a ∈ s) (hb : b ∈ s) {f g : X → α} (hf : ContinuousOn f s) (hg : ContinuousOn g s)
    (ha' : f a ≤ g a) (hb' : g b ≤ f b) : ∃ x ∈ s, f x = g x :=
  let ⟨x, hx⟩ :=
    @intermediate_value_univ₂ s α _ _ _ _ (Subtype.preconnectedSpace hs) ⟨a, ha⟩ ⟨b, hb⟩ _ _
      (continuousOn_iff_continuous_restrict.1 hf) (continuousOn_iff_continuous_restrict.1 hg) ha'
      hb'
  ⟨x, x.2, hx⟩

theorem IsPreconnected.intermediate_value₂_eventually₁ {s : Set X} (hs : IsPreconnected s) {a : X}
    {l : Filter X} (ha : a ∈ s) [NeBot l] (hl : l ≤ 𝓟 s) {f g : X → α} (hf : ContinuousOn f s)
    (hg : ContinuousOn g s) (ha' : f a ≤ g a) (he : g ≤ᶠ[l] f) : ∃ x ∈ s, f x = g x := by
  rw [continuousOn_iff_continuous_restrict] at hf hg
  obtain ⟨b, h⟩ :=
    @intermediate_value_univ₂_eventually₁ _ _ _ _ _ _ (Subtype.preconnectedSpace hs) ⟨a, ha⟩ _
      (comap_coe_neBot_of_le_principal hl) _ _ hf hg ha' (he.comap _)
  exact ⟨b, b.prop, h⟩

theorem IsPreconnected.intermediate_value₂_eventually₂ {s : Set X} (hs : IsPreconnected s)
    {l₁ l₂ : Filter X} [NeBot l₁] [NeBot l₂] (hl₁ : l₁ ≤ 𝓟 s) (hl₂ : l₂ ≤ 𝓟 s) {f g : X → α}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) (he₁ : f ≤ᶠ[l₁] g) (he₂ : g ≤ᶠ[l₂] f) :
    ∃ x ∈ s, f x = g x := by
  rw [continuousOn_iff_continuous_restrict] at hf hg
  obtain ⟨b, h⟩ :=
    @intermediate_value_univ₂_eventually₂ _ _ _ _ _ _ (Subtype.preconnectedSpace hs) _ _
      (comap_coe_neBot_of_le_principal hl₁) (comap_coe_neBot_of_le_principal hl₂) _ _ hf hg
      (he₁.comap _) (he₂.comap _)
  exact ⟨b, b.prop, h⟩

/-- **Intermediate Value Theorem** for continuous functions on connected sets. -/
theorem IsPreconnected.intermediate_value {s : Set X} (hs : IsPreconnected s) {a b : X} (ha : a ∈ s)
    (hb : b ∈ s) {f : X → α} (hf : ContinuousOn f s) : Icc (f a) (f b) ⊆ f '' s := fun _x hx =>
  hs.intermediate_value₂ ha hb hf continuousOn_const hx.1 hx.2

theorem IsPreconnected.intermediate_value_Ico {s : Set X} (hs : IsPreconnected s) {a : X}
    {l : Filter X} (ha : a ∈ s) [NeBot l] (hl : l ≤ 𝓟 s) {f : X → α} (hf : ContinuousOn f s) {v : α}
    (ht : Tendsto f l (𝓝 v)) : Ico (f a) v ⊆ f '' s := fun _ h =>
  hs.intermediate_value₂_eventually₁ ha hl hf continuousOn_const h.1 (ht.eventually_const_le h.2)

theorem IsPreconnected.intermediate_value_Ioc {s : Set X} (hs : IsPreconnected s) {a : X}
    {l : Filter X} (ha : a ∈ s) [NeBot l] (hl : l ≤ 𝓟 s) {f : X → α} (hf : ContinuousOn f s) {v : α}
    (ht : Tendsto f l (𝓝 v)) : Ioc v (f a) ⊆ f '' s := fun _ h =>
  (hs.intermediate_value₂_eventually₁ ha hl continuousOn_const hf h.2
    (ht.eventually_le_const h.1)).imp fun _ h => h.imp_right Eq.symm

theorem IsPreconnected.intermediate_value_Ioo {s : Set X} (hs : IsPreconnected s) {l₁ l₂ : Filter X}
    [NeBot l₁] [NeBot l₂] (hl₁ : l₁ ≤ 𝓟 s) (hl₂ : l₂ ≤ 𝓟 s) {f : X → α} (hf : ContinuousOn f s)
    {v₁ v₂ : α} (ht₁ : Tendsto f l₁ (𝓝 v₁)) (ht₂ : Tendsto f l₂ (𝓝 v₂)) :
    Ioo v₁ v₂ ⊆ f '' s := fun _ h =>
  hs.intermediate_value₂_eventually₂ hl₁ hl₂ hf continuousOn_const
    (ht₁.eventually_le_const h.1) (ht₂.eventually_const_le h.2)

theorem IsPreconnected.intermediate_value_Ici {s : Set X} (hs : IsPreconnected s) {a : X}
    {l : Filter X} (ha : a ∈ s) [NeBot l] (hl : l ≤ 𝓟 s) {f : X → α} (hf : ContinuousOn f s)
    (ht : Tendsto f l atTop) : Ici (f a) ⊆ f '' s := fun y h =>
  hs.intermediate_value₂_eventually₁ ha hl hf continuousOn_const h (tendsto_atTop.1 ht y)

theorem IsPreconnected.intermediate_value_Iic {s : Set X} (hs : IsPreconnected s) {a : X}
    {l : Filter X} (ha : a ∈ s) [NeBot l] (hl : l ≤ 𝓟 s) {f : X → α} (hf : ContinuousOn f s)
    (ht : Tendsto f l atBot) : Iic (f a) ⊆ f '' s := fun y h =>
  (hs.intermediate_value₂_eventually₁ ha hl continuousOn_const hf h (tendsto_atBot.1 ht y)).imp
    fun _ h => h.imp_right Eq.symm

theorem IsPreconnected.intermediate_value_Ioi {s : Set X} (hs : IsPreconnected s) {l₁ l₂ : Filter X}
    [NeBot l₁] [NeBot l₂] (hl₁ : l₁ ≤ 𝓟 s) (hl₂ : l₂ ≤ 𝓟 s) {f : X → α} (hf : ContinuousOn f s)
    {v : α} (ht₁ : Tendsto f l₁ (𝓝 v)) (ht₂ : Tendsto f l₂ atTop) : Ioi v ⊆ f '' s := fun y h =>
  hs.intermediate_value₂_eventually₂ hl₁ hl₂ hf continuousOn_const
    (ht₁.eventually_le_const h) (ht₂.eventually_ge_atTop y)

theorem IsPreconnected.intermediate_value_Iio {s : Set X} (hs : IsPreconnected s) {l₁ l₂ : Filter X}
    [NeBot l₁] [NeBot l₂] (hl₁ : l₁ ≤ 𝓟 s) (hl₂ : l₂ ≤ 𝓟 s) {f : X → α} (hf : ContinuousOn f s)
    {v : α} (ht₁ : Tendsto f l₁ atBot) (ht₂ : Tendsto f l₂ (𝓝 v)) : Iio v ⊆ f '' s := fun y h =>
  hs.intermediate_value₂_eventually₂ hl₁ hl₂ hf continuousOn_const (ht₁.eventually_le_atBot y)
    (ht₂.eventually_const_le h)

theorem IsPreconnected.intermediate_value_Iii {s : Set X} (hs : IsPreconnected s) {l₁ l₂ : Filter X}
    [NeBot l₁] [NeBot l₂] (hl₁ : l₁ ≤ 𝓟 s) (hl₂ : l₂ ≤ 𝓟 s) {f : X → α} (hf : ContinuousOn f s)
    (ht₁ : Tendsto f l₁ atBot) (ht₂ : Tendsto f l₂ atTop) : univ ⊆ f '' s := fun y _ =>
  hs.intermediate_value₂_eventually₂ hl₁ hl₂ hf continuousOn_const (ht₁.eventually_le_atBot y)
    (ht₂.eventually_ge_atTop y)

/-- **Intermediate Value Theorem** for continuous functions on connected spaces. -/
theorem intermediate_value_univ [PreconnectedSpace X] (a b : X) {f : X → α} (hf : Continuous f) :
    Icc (f a) (f b) ⊆ range f := fun _ hx => intermediate_value_univ₂ hf continuous_const hx.1 hx.2

/-- **Intermediate Value Theorem** for continuous functions on connected spaces. -/
theorem mem_range_of_exists_le_of_exists_ge [PreconnectedSpace X] {c : α} {f : X → α}
    (hf : Continuous f) (h₁ : ∃ a, f a ≤ c) (h₂ : ∃ b, c ≤ f b) : c ∈ range f :=
  let ⟨a, ha⟩ := h₁; let ⟨b, hb⟩ := h₂; intermediate_value_univ a b hf ⟨ha, hb⟩

/-!
### (Pre)connected sets in a linear order

In this section we prove the following results:

* `IsPreconnected.ordConnected`: any preconnected set `s` in a linear order is `OrdConnected`,
  i.e. `a ∈ s` and `b ∈ s` imply `Icc a b ⊆ s`;

* `IsPreconnected.mem_intervals`: any preconnected set `s` in a conditionally complete linear order
  is one of the intervals `Set.Icc`, `Set.Ico`, `Set.Ioc`, `Set.Ioo`, `Set.Ici`, `Set.Iic`,
  `Set.Ioi`, `Set.Iio`; note that this is false for non-complete orders: e.g., in `ℝ \ {0}`, the set
  of positive numbers cannot be represented as `Set.Ioi _`.

-/


/-- If a preconnected set contains endpoints of an interval, then it includes the whole interval. -/
theorem IsPreconnected.Icc_subset {s : Set α} (hs : IsPreconnected s) {a b : α} (ha : a ∈ s)
    (hb : b ∈ s) : Icc a b ⊆ s := by
  simpa only [image_id] using hs.intermediate_value ha hb continuousOn_id

theorem IsPreconnected.ordConnected {s : Set α} (h : IsPreconnected s) : OrdConnected s :=
  ⟨fun _ hx _ hy => h.Icc_subset hx hy⟩

/-- If a preconnected set contains endpoints of an interval, then it includes the whole interval. -/
theorem IsConnected.Icc_subset {s : Set α} (hs : IsConnected s) {a b : α} (ha : a ∈ s)
    (hb : b ∈ s) : Icc a b ⊆ s :=
  hs.2.Icc_subset ha hb

/-- If a preconnected set in a linear order space is unbounded below and above, then it is the whole
space. -/
theorem IsPreconnected.eq_univ_of_unbounded {s : Set α} (hs : IsPreconnected s) (hb : ¬BddBelow s)
    (ha : ¬BddAbove s) : s = univ := by
  refine eq_univ_of_forall fun x => ?_
  obtain ⟨y, ys, hy⟩ : ∃ y ∈ s, y < x := not_bddBelow_iff.1 hb x
  obtain ⟨z, zs, hz⟩ : ∃ z ∈ s, x < z := not_bddAbove_iff.1 ha x
  exact hs.Icc_subset ys zs ⟨le_of_lt hy, le_of_lt hz⟩

end

variable {α : Type u} [TopologicalSpace α]

theorem denselyOrdered_of_preconnectedSpace [LinearOrder α] [OrderTopology α]
    [PreconnectedSpace α] : DenselyOrdered α where
  dense x y hxy := by
    suffices (Iio y ∩ Ioi x).Nonempty by grind [Set.inter_nonempty_iff_exists_left]
    exact nonempty_inter (isOpen_Iio' y) (isOpen_Ioi' x) (Set.Iio_union_Ioi_of_lt hxy)
      ⟨x, Set.mem_Iio.mpr hxy⟩ ⟨y, Set.mem_Ioi.mpr hxy⟩

variable [ConditionallyCompleteLinearOrder α] [OrderTopology α]

/-- A bounded connected subset of a conditionally complete linear order includes the open interval
`(Inf s, Sup s)`. -/
theorem IsConnected.Ioo_csInf_csSup_subset {s : Set α} (hs : IsConnected s) (hb : BddBelow s)
    (ha : BddAbove s) : Ioo (sInf s) (sSup s) ⊆ s := fun _x hx =>
  let ⟨_y, ys, hy⟩ := (isGLB_lt_iff (isGLB_csInf hs.nonempty hb)).1 hx.1
  let ⟨_z, zs, hz⟩ := (lt_isLUB_iff (isLUB_csSup hs.nonempty ha)).1 hx.2
  hs.Icc_subset ys zs ⟨hy.le, hz.le⟩

theorem eq_Icc_csInf_csSup_of_connected_bdd_closed {s : Set α} (hc : IsConnected s)
    (hb : BddBelow s) (ha : BddAbove s) (hcl : IsClosed s) : s = Icc (sInf s) (sSup s) :=
  (subset_Icc_csInf_csSup hb ha).antisymm <|
    hc.Icc_subset (hcl.csInf_mem hc.nonempty hb) (hcl.csSup_mem hc.nonempty ha)

theorem IsPreconnected.Ioi_csInf_subset {s : Set α} (hs : IsPreconnected s) (hb : BddBelow s)
    (ha : ¬BddAbove s) : Ioi (sInf s) ⊆ s := fun x hx =>
  have sne : s.Nonempty := nonempty_of_not_bddAbove ha
  let ⟨_y, ys, hy⟩ : ∃ y ∈ s, y < x := (isGLB_lt_iff (isGLB_csInf sne hb)).1 hx
  let ⟨_z, zs, hz⟩ : ∃ z ∈ s, x < z := not_bddAbove_iff.1 ha x
  hs.Icc_subset ys zs ⟨hy.le, hz.le⟩

theorem IsPreconnected.Iio_csSup_subset {s : Set α} (hs : IsPreconnected s) (hb : ¬BddBelow s)
    (ha : BddAbove s) : Iio (sSup s) ⊆ s :=
  IsPreconnected.Ioi_csInf_subset (α := αᵒᵈ) hs ha hb

/-- A preconnected set in a conditionally complete linear order is either one of the intervals
`[Inf s, Sup s]`, `[Inf s, Sup s)`, `(Inf s, Sup s]`, `(Inf s, Sup s)`, `[Inf s, +∞)`,
`(Inf s, +∞)`, `(-∞, Sup s]`, `(-∞, Sup s)`, `(-∞, +∞)`, or `∅`. The converse statement requires
`α` to be densely ordered. -/
theorem IsPreconnected.mem_intervals {s : Set α} (hs : IsPreconnected s) :
    s ∈
      ({Icc (sInf s) (sSup s), Ico (sInf s) (sSup s), Ioc (sInf s) (sSup s), Ioo (sInf s) (sSup s),
          Ici (sInf s), Ioi (sInf s), Iic (sSup s), Iio (sSup s), univ, ∅} : Set (Set α)) := by
  rcases s.eq_empty_or_nonempty with (rfl | hne)
  · apply_rules [Or.inr, mem_singleton]
  have hs' : IsConnected s := ⟨hne, hs⟩
  by_cases hb : BddBelow s <;> by_cases ha : BddAbove s
  · refine mem_of_subset_of_mem ?_ <| mem_Icc_Ico_Ioc_Ioo_of_subset_of_subset
      (hs'.Ioo_csInf_csSup_subset hb ha) (subset_Icc_csInf_csSup hb ha)
    simp only [insert_subset_iff, mem_insert_iff, mem_singleton_iff, true_or, or_true,
      singleton_subset_iff, and_self]
  · refine Or.inr <| Or.inr <| Or.inr <| Or.inr ?_
    rcases mem_Ici_Ioi_of_subset_of_subset (hs.Ioi_csInf_subset hb ha) fun x hx ↦
      csInf_le hb hx with hs | hs
    · exact Or.inl hs
    · exact Or.inr (Or.inl hs)
  · iterate 6 apply Or.inr
    rcases mem_Iic_Iio_of_subset_of_subset (hs.Iio_csSup_subset hb ha) fun x hx ↦
      le_csSup ha hx with hs | hs
    · exact Or.inl hs
    · exact Or.inr (Or.inl hs)
  · iterate 8 apply Or.inr
    exact Or.inl (hs.eq_univ_of_unbounded hb ha)

/-- A preconnected set is either one of the intervals `Icc`, `Ico`, `Ioc`, `Ioo`, `Ici`, `Ioi`,
`Iic`, `Iio`, or `univ`, or `∅`. The converse statement requires `α` to be densely ordered. Though
one can represent `∅` as `(Inf ∅, Inf ∅)`, we include it into the list of possible cases to improve
readability. -/
theorem setOf_isPreconnected_subset_of_ordered :
    { s : Set α | IsPreconnected s } ⊆
      -- bounded intervals
      (range (uncurry Icc) ∪ range (uncurry Ico) ∪ range (uncurry Ioc) ∪ range (uncurry Ioo)) ∪
      -- unbounded intervals and `univ`
      (range Ici ∪ range Ioi ∪ range Iic ∪ range Iio ∪ {univ, ∅}) := by
  intro s hs
  rcases hs.mem_intervals with (hs | hs | hs | hs | hs | hs | hs | hs | hs | hs) <;> rw [hs] <;>
    simp only [union_insert, union_singleton, mem_insert_iff, mem_union, mem_range, Prod.exists,
      uncurry_apply_pair, exists_apply_eq_apply, true_or, or_true, exists_apply_eq_apply2]

/-!
### Intervals are connected

In this section we prove that a closed interval (hence, any `OrdConnected` set) in a dense
conditionally complete linear order is preconnected.
-/


/-- A "continuous induction principle" for a closed interval: if a set `s` meets `[a, b]`
on a closed subset, contains `a`, and the set `s ∩ [a, b)` has no maximal point, then `b ∈ s`. -/
theorem IsClosed.mem_of_ge_of_forall_exists_gt {a b : α} {s : Set α} (hs : IsClosed (s ∩ Icc a b))
    (ha : a ∈ s) (hab : a ≤ b) (hgt : ∀ x ∈ s ∩ Ico a b, (s ∩ Ioc x b).Nonempty) : b ∈ s := by
  let S := s ∩ Icc a b
  replace ha : a ∈ S := ⟨ha, left_mem_Icc.2 hab⟩
  have Sbd : BddAbove S := ⟨b, fun z hz => hz.2.2⟩
  let c := sSup (s ∩ Icc a b)
  have c_mem : c ∈ S := hs.csSup_mem ⟨_, ha⟩ Sbd
  have c_le : c ≤ b := csSup_le ⟨_, ha⟩ fun x hx => hx.2.2
  rcases eq_or_lt_of_le c_le with hc | hc
  · exact hc ▸ c_mem.1
  exfalso
  rcases hgt c ⟨c_mem.1, c_mem.2.1, hc⟩ with ⟨x, xs, cx, xb⟩
  exact not_lt_of_ge (le_csSup Sbd ⟨xs, le_trans (le_csSup Sbd ha) (le_of_lt cx), xb⟩) cx

/-- A "continuous induction principle" for a closed interval: if a set `s` meets `[a, b]`
on a closed subset, contains `a`, and for any `a ≤ x < y ≤ b`, `x ∈ s`, the set `s ∩ (x, y]`
is not empty, then `[a, b] ⊆ s`. -/
theorem IsClosed.Icc_subset_of_forall_exists_gt {a b : α} {s : Set α} (hs : IsClosed (s ∩ Icc a b))
    (ha : a ∈ s) (hgt : ∀ x ∈ s ∩ Ico a b, ∀ y ∈ Ioi x, (s ∩ Ioc x y).Nonempty) : Icc a b ⊆ s := by
  intro y hy
  have : IsClosed (s ∩ Icc a y) := by
    suffices s ∩ Icc a y = s ∩ Icc a b ∩ Icc a y from this ▸ hs.inter isClosed_Icc
    grind [inter_assoc, inter_eq_self_of_subset_right, Icc_subset_Icc_right]
  exact IsClosed.mem_of_ge_of_forall_exists_gt this ha hy.1 fun x hx ↦
    hgt x ⟨hx.1, Ico_subset_Ico_right hy.2 hx.2⟩ y hx.2.2

/-- A "continuous induction principle" for a closed interval: if a set `s` meets `[a, b]`
on a closed subset, contains `b`, and the set `s ∩ (a, b]` has no minimal point, then `a ∈ s`. -/
theorem IsClosed.mem_of_ge_of_forall_exists_lt {a b : α} {s : Set α} (hs : IsClosed (s ∩ Icc a b))
    (hb : b ∈ s) (hab : a ≤ b) (hgt : ∀ x ∈ s ∩ Ioc a b, (s ∩ Ico a x).Nonempty) : a ∈ s := by
  suffices OrderDual.toDual a ∈ ofDual ⁻¹' s by aesop
  have : IsClosed (OrderDual.ofDual ⁻¹' (s ∩ Icc a b)) := hs
  rw [preimage_inter, ← Icc_toDual] at this
  apply this.mem_of_ge_of_forall_exists_gt (by simp_all) (by simp_all) (fun x hx ↦ ?_)
  rw [Ico_toDual, ← preimage_inter, ← Equiv.image_symm_eq_preimage, mem_image] at hx
  aesop

/-- A "continuous induction principle" for a closed interval: if a set `s` meets `[a, b]`
on a closed subset, contains `b`, and for any `a ≤ y < x ≤ b`, `x ∈ s`, the set `s ∩ [y, x)`
is not empty, then `[a, b] ⊆ s`. -/
theorem IsClosed.Icc_subset_of_forall_exists_lt {a b : α} {s : Set α} (hs : IsClosed (s ∩ Icc a b))
    (hb : b ∈ s) (hgt : ∀ x ∈ s ∩ Ioc a b, ∀ y ∈ Iio x, (s ∩ Ico y x).Nonempty) : Icc a b ⊆ s := by
  intro y hy
  have : IsClosed (s ∩ Icc y b) := by
    suffices s ∩ Icc y b = s ∩ Icc a b ∩ Icc y b from this ▸ hs.inter isClosed_Icc
    grind [Icc_subset_Icc_left, inter_eq_self_of_subset_right, inter_assoc]
  exact IsClosed.mem_of_ge_of_forall_exists_lt this hb hy.2 fun x hx ↦
    hgt x ⟨hx.1, Ioc_subset_Ioc_left hy.1 hx.2⟩ y hx.2.1

variable [DenselyOrdered α] {a b : α}

/-- A "continuous induction principle" for a closed interval: if a set `s` meets `[a, b]`
on a closed subset, contains `a`, and for any `x ∈ [a, b)` such that `[a, x]` is included in `s`,
the set `s` includes some open neighborhood of `x` within `(x, +∞)`, then `[a, b] ⊆ s`. -/
lemma IsClosed.Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset {a b : α} {s : Set α}
    (hs : IsClosed (s ∩ Icc a b)) (ha : a ∈ s)
    (h : ∀ t ∈ Ico a b, Icc a t ⊆ s → s ∈ 𝓝[>] t) :
    Icc a b ⊆ s := by
  rcases lt_or_ge b a with hab | hab
  · simp_all
  set A := {t ∈ Icc a b | Icc a t ⊆ s}
  have a_mem : a ∈ A := ⟨left_mem_Icc.mpr hab, by simp [ha]⟩
  have bdd_A : BddAbove A := ⟨b, fun t ht ↦ ht.1.2⟩
  set t₁ := sSup A
  have t₁_mem : t₁ ∈ Icc a b := ⟨le_csSup bdd_A a_mem, csSup_le ⟨a, a_mem⟩ (fun t ht ↦ ht.1.2)⟩
  obtain ⟨⟨t₁a, t₁b⟩, ht₁⟩ : t₁ ∈ A := by
    refine ⟨t₁_mem, fun t ht ↦ ?_⟩
    rcases ht.2.eq_or_lt with rfl | h
    · have : closure A ⊆ s ∩ Icc a b := by
        apply (closure_subset_iff hs).2 (fun t ht ↦ ⟨?_, ht.1⟩)
        have : t ∈ Icc a t := ⟨ht.1.1, le_rfl⟩
        exact ht.2 this
      apply this.trans inter_subset_left
      exact csSup_mem_closure ⟨a, a_mem⟩ bdd_A
    · obtain ⟨c, cA, tc⟩ : ∃ c ∈ A, t < c := (lt_csSup_iff bdd_A ⟨a, a_mem⟩).1 h
      apply cA.2
      exact ⟨ht.1, tc.le⟩
  suffices t₁ = b by simpa [this] using ht₁
  apply eq_of_le_of_not_lt t₁b fun t₁b' ↦ ?_
  obtain ⟨m, t₁m, H⟩ : ∃ m > t₁, Ioo t₁ m ⊆ s :=
    (mem_nhdsGT_iff_exists_Ioo_subset' t₁b').mp (h t₁ ⟨t₁a, t₁b'⟩ (fun s hs ↦ ht₁ hs))
  obtain ⟨t, hat, ht⟩ : ∃ t, t₁ < t ∧ t < min m b := exists_between (lt_min t₁m t₁b')
  have : t ∈ A := by
    refine ⟨⟨by order, ht.le.trans (min_le_right _ _)⟩, fun t' ht' ↦ ?_⟩
    rcases le_or_gt t' t₁ with h't' | h't'
    · exact ht₁ ⟨ht'.1, h't'⟩
    · exact H ⟨h't', ht'.2.trans_lt <| ht.trans_le <| min_le_left ..⟩
  have : t ≤ t₁ := le_csSup bdd_A this
  order

/-- A "continuous induction principle" for a closed interval: if a set `s` meets `[a, b]`
on a closed subset, contains `a`, and for any `x ∈ s ∩ [a, b)` the set `s` includes some open
neighborhood of `x` within `(x, +∞)`, then `[a, b] ⊆ s`. -/
theorem IsClosed.Icc_subset_of_forall_mem_nhdsWithin {a b : α} {s : Set α}
    (hs : IsClosed (s ∩ Icc a b)) (ha : a ∈ s) (hgt : ∀ x ∈ s ∩ Ico a b, s ∈ 𝓝[>] x) :
    Icc a b ⊆ s :=
  hs.Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset ha
    (fun _t ht h't ↦ hgt _ ⟨h't ⟨ht.1, le_rfl⟩, ht⟩)

theorem isPreconnected_Icc_aux (x y : α) (s t : Set α) (hxy : x ≤ y) (hs : IsClosed s)
    (ht : IsClosed t) (hab : Icc a b ⊆ s ∪ t) (hx : x ∈ Icc a b ∩ s) (hy : y ∈ Icc a b ∩ t) :
    (Icc a b ∩ (s ∩ t)).Nonempty := by
  have xyab : Icc x y ⊆ Icc a b := Icc_subset_Icc hx.1.1 hy.1.2
  by_contra hst
  suffices Icc x y ⊆ s from
    hst ⟨y, xyab <| right_mem_Icc.2 hxy, this <| right_mem_Icc.2 hxy, hy.2⟩
  apply (IsClosed.inter hs isClosed_Icc).Icc_subset_of_forall_mem_nhdsWithin hx.2
  rintro z ⟨zs, hz⟩
  have zt : z ∈ tᶜ := fun zt => hst ⟨z, xyab <| Ico_subset_Icc_self hz, zs, zt⟩
  have : tᶜ ∩ Ioc z y ∈ 𝓝[>] z := by
    rw [← nhdsWithin_Ioc_eq_nhdsGT hz.2]
    exact mem_nhdsWithin.2 ⟨tᶜ, ht.isOpen_compl, zt, Subset.rfl⟩
  apply mem_of_superset this
  have : Ioc z y ⊆ s ∪ t := fun w hw => hab (xyab ⟨le_trans hz.1 (le_of_lt hw.1), hw.2⟩)
  exact fun w ⟨wt, wzy⟩ => (this wzy).elim id fun h => (wt h).elim

/-- A closed interval in a densely ordered conditionally complete linear order is preconnected. -/
theorem isPreconnected_Icc : IsPreconnected (Icc a b) :=
  isPreconnected_closed_iff.2
    (by
      rintro s t hs ht hab ⟨x, hx⟩ ⟨y, hy⟩
      -- This used to use `wlog`, but it was causing timeouts.
      rcases le_total x y with h | h
      · exact isPreconnected_Icc_aux x y s t h hs ht hab hx hy
      · rw [inter_comm s t]
        rw [union_comm s t] at hab
        exact isPreconnected_Icc_aux y x t s h ht hs hab hy hx)

theorem isPreconnected_uIcc : IsPreconnected ([[a, b]]) :=
  isPreconnected_Icc

theorem Set.OrdConnected.isPreconnected {s : Set α} (h : s.OrdConnected) : IsPreconnected s :=
  isPreconnected_of_forall_pair fun x hx y hy =>
    ⟨[[x, y]], h.uIcc_subset hx hy, left_mem_uIcc, right_mem_uIcc, isPreconnected_uIcc⟩

theorem isPreconnected_iff_ordConnected {s : Set α} : IsPreconnected s ↔ OrdConnected s :=
  ⟨IsPreconnected.ordConnected, Set.OrdConnected.isPreconnected⟩

theorem isPreconnected_Ici : IsPreconnected (Ici a) :=
  ordConnected_Ici.isPreconnected

theorem isPreconnected_Iic : IsPreconnected (Iic a) :=
  ordConnected_Iic.isPreconnected

theorem isPreconnected_Iio : IsPreconnected (Iio a) :=
  ordConnected_Iio.isPreconnected

theorem isPreconnected_Ioi : IsPreconnected (Ioi a) :=
  ordConnected_Ioi.isPreconnected

theorem isPreconnected_Ioo : IsPreconnected (Ioo a b) :=
  ordConnected_Ioo.isPreconnected

theorem isPreconnected_uIoo : IsPreconnected (uIoo a b) :=
  isPreconnected_Ioo

theorem isPreconnected_Ioc : IsPreconnected (Ioc a b) :=
  ordConnected_Ioc.isPreconnected

theorem isPreconnected_uIoc : IsPreconnected (uIoc a b) :=
  isPreconnected_Ioc

theorem isPreconnected_Ico : IsPreconnected (Ico a b) :=
  ordConnected_Ico.isPreconnected

theorem isConnected_Ici : IsConnected (Ici a) :=
  ⟨nonempty_Ici, isPreconnected_Ici⟩

theorem isConnected_Iic : IsConnected (Iic a) :=
  ⟨nonempty_Iic, isPreconnected_Iic⟩

theorem isConnected_Ioi [NoMaxOrder α] : IsConnected (Ioi a) :=
  ⟨nonempty_Ioi, isPreconnected_Ioi⟩

theorem isConnected_Iio [NoMinOrder α] : IsConnected (Iio a) :=
  ⟨nonempty_Iio, isPreconnected_Iio⟩

theorem isConnected_Icc (h : a ≤ b) : IsConnected (Icc a b) :=
  ⟨nonempty_Icc.2 h, isPreconnected_Icc⟩

theorem isConnected_Ioo (h : a < b) : IsConnected (Ioo a b) :=
  ⟨nonempty_Ioo.2 h, isPreconnected_Ioo⟩

theorem isConnected_uIoo (h : a ≠ b) : IsConnected (uIoo a b) :=
  ⟨nonempty_uIoo.2 h, isPreconnected_uIoo⟩

theorem isConnected_Ioc (h : a < b) : IsConnected (Ioc a b) :=
  ⟨nonempty_Ioc.2 h, isPreconnected_Ioc⟩

theorem isConnected_uIoc (h : a ≠ b) : IsConnected (uIoc a b) :=
  ⟨nonempty_uIoc.2 h, isPreconnected_uIoc⟩

theorem isConnected_Ico (h : a < b) : IsConnected (Ico a b) :=
  ⟨nonempty_Ico.2 h, isPreconnected_Ico⟩

instance (priority := 100) ordered_connected_space : PreconnectedSpace α :=
  ⟨ordConnected_univ.isPreconnected⟩

/-- In a dense conditionally complete linear order, the set of preconnected sets is exactly
the set of the intervals `Icc`, `Ico`, `Ioc`, `Ioo`, `Ici`, `Ioi`, `Iic`, `Iio`, `(-∞, +∞)`,
or `∅`. Though one can represent `∅` as `(sInf s, sInf s)`, we include it into the list of
possible cases to improve readability. -/
theorem setOf_isPreconnected_eq_of_ordered :
    { s : Set α | IsPreconnected s } =
      -- bounded intervals
      range (uncurry Icc) ∪ range (uncurry Ico) ∪ range (uncurry Ioc) ∪ range (uncurry Ioo) ∪
      -- unbounded intervals and `univ`
      (range Ici ∪ range Ioi ∪ range Iic ∪ range Iio ∪ {univ, ∅}) := by
  refine Subset.antisymm setOf_isPreconnected_subset_of_ordered ?_
  simp only [subset_def, forall_mem_range, uncurry, or_imp, forall_and, mem_union,
    mem_setOf_eq, insert_eq, mem_singleton_iff, forall_eq, forall_true_iff, and_true,
    isPreconnected_Icc, isPreconnected_Ico, isPreconnected_Ioc, isPreconnected_Ioo,
    isPreconnected_Ioi, isPreconnected_Iio, isPreconnected_Ici, isPreconnected_Iic,
    isPreconnected_univ, isPreconnected_empty]

/-- This lemma characterizes when a subset `s` of a densely ordered conditionally complete linear
order is totally disconnected with respect to the order topology: between any two distinct points
of `s` must lie a point not in `s`. -/
lemma isTotallyDisconnected_iff_lt {s : Set α} :
    IsTotallyDisconnected s ↔ ∀ x ∈ s, ∀ y ∈ s, x < y → ∃ z ∉ s, z ∈ Ioo x y := by
  simp only [IsTotallyDisconnected, isPreconnected_iff_ordConnected, ← not_nontrivial_iff,
    nontrivial_iff_exists_lt, not_exists, not_and]
  refine ⟨fun h x hx y hy hxy ↦ ?_, fun h t hts ht x hx y hy hxy ↦ ?_⟩
  · simp_rw [← not_ordConnected_inter_Icc_iff hx hy]
    exact fun hs ↦ h _ inter_subset_left hs _ ⟨hx, le_rfl, hxy.le⟩ _ ⟨hy, hxy.le, le_rfl⟩ hxy
  · obtain ⟨z, h1z, h2z⟩ := h x (hts hx) y (hts hy) hxy
    exact h1z <| hts <| ht.1 hx hy ⟨h2z.1.le, h2z.2.le⟩

/-!
### Intermediate Value Theorem on an interval

In this section we prove several versions of the Intermediate Value Theorem for a function
continuous on an interval.
-/


variable {δ : Type*} [LinearOrder δ] [TopologicalSpace δ] [OrderClosedTopology δ]

/-- **Intermediate Value Theorem** for continuous functions on closed intervals, case
`f a ≤ t ≤ f b`. -/
@[informal "intermediate value theorem"]
@[informal "intermediate value theorem"]
theorem intermediate_value_Icc {a b : α} (hab : a ≤ b) {f : α → δ} (hf : ContinuousOn f (Icc a b)) :
    Icc (f a) (f b) ⊆ f '' Icc a b :=
  isPreconnected_Icc.intermediate_value (left_mem_Icc.2 hab) (right_mem_Icc.2 hab) hf

/-- **Intermediate Value Theorem** for continuous functions on closed intervals, case
`f a ≥ t ≥ f b`. -/
theorem intermediate_value_Icc' {a b : α} (hab : a ≤ b) {f : α → δ}
    (hf : ContinuousOn f (Icc a b)) : Icc (f b) (f a) ⊆ f '' Icc a b :=
  isPreconnected_Icc.intermediate_value (right_mem_Icc.2 hab) (left_mem_Icc.2 hab) hf

/-- **Intermediate Value Theorem** for continuous functions on closed intervals, unordered case. -/
theorem intermediate_value_uIcc {a b : α} {f : α → δ} (hf : ContinuousOn f [[a, b]]) :
    [[f a, f b]] ⊆ f '' uIcc a b := by
  cases le_total (f a) (f b) <;> simp [*, isPreconnected_uIcc.intermediate_value]

/-- If `f : α → α` is continuous on `[[a, b]]`, `a ≤ f a`, and `f b ≤ b`,
then `f` has a fixed point on `[[a, b]]`. -/
theorem exists_mem_uIcc_isFixedPt {a b : α} {f : α → α} (hf : ContinuousOn f (uIcc a b))
    (ha : a ≤ f a) (hb : f b ≤ b) : ∃ c ∈ [[a, b]], IsFixedPt f c :=
  isPreconnected_uIcc.intermediate_value₂ right_mem_uIcc left_mem_uIcc hf continuousOn_id hb ha

/-- If `f : α → α` is continuous on `[a, b]`, `a ≤ b`, `a ≤ f a`, and `f b ≤ b`,
then `f` has a fixed point on `[a, b]`.

In particular, if `[a, b]` is forward-invariant under `f`,
then `f` has a fixed point on `[a, b]`, see `exists_mem_Icc_isFixedPt_of_mapsTo`. -/
theorem exists_mem_Icc_isFixedPt {a b : α} {f : α → α} (hf : ContinuousOn f (Icc a b))
    (hle : a ≤ b) (ha : a ≤ f a) (hb : f b ≤ b) : ∃ c ∈ Icc a b, IsFixedPt f c :=
  isPreconnected_Icc.intermediate_value₂
    (right_mem_Icc.2 hle) (left_mem_Icc.2 hle) hf continuousOn_id hb ha

/-- If a closed interval is forward-invariant under a continuous map `f : α → α`,
then this map has a fixed point on this interval. -/
theorem exists_mem_Icc_isFixedPt_of_mapsTo {a b : α} {f : α → α} (hf : ContinuousOn f (Icc a b))
    (hle : a ≤ b) (hmaps : MapsTo f (Icc a b) (Icc a b)) : ∃ c ∈ Icc a b, IsFixedPt f c :=
  exists_mem_Icc_isFixedPt hf hle (hmaps <| left_mem_Icc.2 hle).1 (hmaps <| right_mem_Icc.2 hle).2

theorem intermediate_value_Ico {a b : α} (hab : a ≤ b) {f : α → δ} (hf : ContinuousOn f (Icc a b)) :
    Ico (f a) (f b) ⊆ f '' Ico a b :=
  Or.elim (eq_or_lt_of_le hab) (fun he _ h => absurd h.2 (not_lt_of_ge (he ▸ h.1))) fun hlt =>
    @IsPreconnected.intermediate_value_Ico _ _ _ _ _ _ _ isPreconnected_Ico _ _ ⟨refl a, hlt⟩
      (right_nhdsWithin_Ico_neBot hlt) inf_le_right _ (hf.mono Ico_subset_Icc_self) _
      ((hf.continuousWithinAt ⟨hab, refl b⟩).mono Ico_subset_Icc_self)

theorem intermediate_value_Ico' {a b : α} (hab : a ≤ b) {f : α → δ}
    (hf : ContinuousOn f (Icc a b)) : Ioc (f b) (f a) ⊆ f '' Ico a b :=
  Or.elim (eq_or_lt_of_le hab) (fun he _ h => absurd h.1 (not_lt_of_ge (he ▸ h.2))) fun hlt =>
    @IsPreconnected.intermediate_value_Ioc _ _ _ _ _ _ _ isPreconnected_Ico _ _ ⟨refl a, hlt⟩
      (right_nhdsWithin_Ico_neBot hlt) inf_le_right _ (hf.mono Ico_subset_Icc_self) _
      ((hf.continuousWithinAt ⟨hab, refl b⟩).mono Ico_subset_Icc_self)

theorem intermediate_value_Ioc {a b : α} (hab : a ≤ b) {f : α → δ} (hf : ContinuousOn f (Icc a b)) :
    Ioc (f a) (f b) ⊆ f '' Ioc a b :=
  Or.elim (eq_or_lt_of_le hab) (fun he _ h => absurd h.2 (not_le_of_gt (he ▸ h.1))) fun hlt =>
    @IsPreconnected.intermediate_value_Ioc _ _ _ _ _ _ _ isPreconnected_Ioc _ _ ⟨hlt, refl b⟩
      (left_nhdsWithin_Ioc_neBot hlt) inf_le_right _ (hf.mono Ioc_subset_Icc_self) _
      ((hf.continuousWithinAt ⟨refl a, hab⟩).mono Ioc_subset_Icc_self)

theorem intermediate_value_Ioc' {a b : α} (hab : a ≤ b) {f : α → δ}
    (hf : ContinuousOn f (Icc a b)) : Ico (f b) (f a) ⊆ f '' Ioc a b :=
  Or.elim (eq_or_lt_of_le hab) (fun he _ h => absurd h.1 (not_le_of_gt (he ▸ h.2))) fun hlt =>
    @IsPreconnected.intermediate_value_Ico _ _ _ _ _ _ _ isPreconnected_Ioc _ _ ⟨hlt, refl b⟩
      (left_nhdsWithin_Ioc_neBot hlt) inf_le_right _ (hf.mono Ioc_subset_Icc_self) _
      ((hf.continuousWithinAt ⟨refl a, hab⟩).mono Ioc_subset_Icc_self)

theorem intermediate_value_Ioo {a b : α} (hab : a ≤ b) {f : α → δ} (hf : ContinuousOn f (Icc a b)) :
    Ioo (f a) (f b) ⊆ f '' Ioo a b :=
  Or.elim (eq_or_lt_of_le hab) (fun he _ h => absurd h.2 (not_lt_of_gt (he ▸ h.1))) fun hlt =>
    @IsPreconnected.intermediate_value_Ioo _ _ _ _ _ _ _ isPreconnected_Ioo _ _
      (left_nhdsWithin_Ioo_neBot hlt) (right_nhdsWithin_Ioo_neBot hlt) inf_le_right inf_le_right _
      (hf.mono Ioo_subset_Icc_self) _ _
      ((hf.continuousWithinAt ⟨refl a, hab⟩).mono Ioo_subset_Icc_self)
      ((hf.continuousWithinAt ⟨hab, refl b⟩).mono Ioo_subset_Icc_self)

theorem intermediate_value_Ioo' {a b : α} (hab : a ≤ b) {f : α → δ}
    (hf : ContinuousOn f (Icc a b)) : Ioo (f b) (f a) ⊆ f '' Ioo a b :=
  Or.elim (eq_or_lt_of_le hab) (fun he _ h => absurd h.1 (not_lt_of_gt (he ▸ h.2))) fun hlt =>
    @IsPreconnected.intermediate_value_Ioo _ _ _ _ _ _ _ isPreconnected_Ioo _ _
      (right_nhdsWithin_Ioo_neBot hlt) (left_nhdsWithin_Ioo_neBot hlt) inf_le_right inf_le_right _
      (hf.mono Ioo_subset_Icc_self) _ _
      ((hf.continuousWithinAt ⟨hab, refl b⟩).mono Ioo_subset_Icc_self)
      ((hf.continuousWithinAt ⟨refl a, hab⟩).mono Ioo_subset_Icc_self)

/-- **Intermediate value theorem**: if `f` is continuous on an order-connected set `s` and `a`,
`b` are two points of this set, then `f` sends `s` to a superset of `Icc (f a) (f b)`. -/
theorem ContinuousOn.surjOn_Icc {s : Set α} [hs : OrdConnected s] {f : α → δ}
    (hf : ContinuousOn f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) : SurjOn f s (Icc (f a) (f b)) :=
  hs.isPreconnected.intermediate_value ha hb hf

/-- **Intermediate value theorem**: if `f` is continuous on an order-connected set `s` and `a`,
`b` are two points of this set, then `f` sends `s` to a superset of `[f a, f b]`. -/
theorem ContinuousOn.surjOn_uIcc {s : Set α} [hs : OrdConnected s] {f : α → δ}
    (hf : ContinuousOn f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) :
    SurjOn f s (uIcc (f a) (f b)) := by
  rcases le_total (f a) (f b) with hab | hab <;> simp [hf.surjOn_Icc, *]

/-- A continuous function which tends to `Filter.atTop` along `Filter.atTop` and to `Filter.atBot`
along `Filter.atBot` is surjective. -/
theorem Continuous.surjective {f : α → δ} (hf : Continuous f) (h_top : Tendsto f atTop atTop)
    (h_bot : Tendsto f atBot atBot) : Function.Surjective f := fun p =>
  mem_range_of_exists_le_of_exists_ge hf (h_bot.eventually (eventually_le_atBot p)).exists
    (h_top.eventually (eventually_ge_atTop p)).exists

/-- A continuous function which tends to `Filter.atBot` along `Filter.atTop` and to `Filter.atTop`
along `Filter.atBot` is surjective. -/
theorem Continuous.surjective' {f : α → δ} (hf : Continuous f) (h_top : Tendsto f atBot atTop)
    (h_bot : Tendsto f atTop atBot) : Function.Surjective f :=
  Continuous.surjective (α := αᵒᵈ) hf h_top h_bot

/-- If a function `f : α → β` is continuous on a nonempty interval `s`, its restriction to `s`
tends to `Filter.atBot : Filter β` along `Filter.atBot : Filter ↥s` and tends to
`Filter.atTop : Filter β` along `Filter.atTop : Filter ↥s`, then the restriction of `f` to `s` is
surjective. We formulate the conclusion as `Function.surjOn f s Set.univ`. -/
theorem ContinuousOn.surjOn_of_tendsto {f : α → δ} {s : Set α} [OrdConnected s] (hs : s.Nonempty)
    (hf : ContinuousOn f s) (hbot : Tendsto (fun x : s => f x) atBot atBot)
    (htop : Tendsto (fun x : s => f x) atTop atTop) : SurjOn f s univ :=
  haveI := Classical.inhabited_of_nonempty hs.to_subtype
  surjOn_iff_surjective.2 <| hf.restrict.surjective htop hbot

/-- If a function `f : α → β` is continuous on a nonempty interval `s`, its restriction to `s`
tends to `Filter.atTop : Filter β` along `Filter.atBot : Filter ↥s` and tends to
`Filter.atBot : Filter β` along `Filter.atTop : Filter ↥s`, then the restriction of `f` to `s` is
surjective. We formulate the conclusion as `Function.surjOn f s Set.univ`. -/
theorem ContinuousOn.surjOn_of_tendsto' {f : α → δ} {s : Set α} [OrdConnected s] (hs : s.Nonempty)
    (hf : ContinuousOn f s) (hbot : Tendsto (fun x : s => f x) atBot atTop)
    (htop : Tendsto (fun x : s => f x) atTop atBot) : SurjOn f s univ :=
  ContinuousOn.surjOn_of_tendsto (δ := δᵒᵈ) hs hf hbot htop

theorem Continuous.strictMono_of_inj_boundedOrder [BoundedOrder α] {f : α → δ}
    (hf_c : Continuous f) (hf : f ⊥ ≤ f ⊤) (hf_i : Injective f) : StrictMono f := by
  intro a b hab
  by_contra! h
  have H : f b < f a := lt_of_le_of_ne h <| hf_i.ne hab.ne'
  by_cases! ha : f a ≤ f ⊥
  · obtain ⟨u, hu⟩ := intermediate_value_Ioc le_top hf_c.continuousOn ⟨H.trans_le ha, hf⟩
    have : u = ⊥ := hf_i hu.2
    simp_all
  · by_cases! hb : f ⊥ < f b
    · obtain ⟨u, hu⟩ := intermediate_value_Ioo bot_le hf_c.continuousOn ⟨hb, H⟩
      rw [hf_i hu.2] at hu
      exact (hab.trans hu.1.2).false
    · replace hb : f b < f ⊥ := lt_of_le_of_ne hb <| hf_i.ne (lt_of_lt_of_le' hab bot_le).ne'
      obtain ⟨u, hu⟩ := intermediate_value_Ioo' hab.le hf_c.continuousOn ⟨hb, ha⟩
      have : u = ⊥ := hf_i hu.2
      simp_all

theorem Continuous.strictAnti_of_inj_boundedOrder [BoundedOrder α] {f : α → δ}
    (hf_c : Continuous f) (hf : f ⊤ ≤ f ⊥) (hf_i : Injective f) : StrictAnti f :=
  hf_c.strictMono_of_inj_boundedOrder (δ := δᵒᵈ) hf hf_i

theorem Continuous.strictMono_of_inj_boundedOrder' [BoundedOrder α] {f : α → δ}
    (hf_c : Continuous f) (hf_i : Injective f) : StrictMono f ∨ StrictAnti f :=
  (le_total (f ⊥) (f ⊤)).imp
    (hf_c.strictMono_of_inj_boundedOrder · hf_i)
    (hf_c.strictAnti_of_inj_boundedOrder · hf_i)

/-- Suppose `α` is equipped with a conditionally complete linear dense order and `f : α → δ` is
continuous and injective. Then `f` is strictly monotone (increasing) if
it is strictly monotone (increasing) on some closed interval `[a, b]`. -/
theorem Continuous.strictMonoOn_of_inj_rigidity {f : α → δ}
    (hf_c : Continuous f) (hf_i : Injective f) {a b : α} (hab : a < b)
    (hf_mono : StrictMonoOn f (Icc a b)) : StrictMono f := by
  intro x y hxy
  let s := min a x
  let t := max b y
  have hsa : s ≤ a := min_le_left a x
  have hbt : b ≤ t := le_max_left b y
  have hf_mono_st : StrictMonoOn f (Icc s t) ∨ StrictAntiOn f (Icc s t) := by
    have : Fact (s ≤ t) := ⟨hsa.trans <| hbt.trans' hab.le⟩
    have := Continuous.strictMono_of_inj_boundedOrder' (f := Set.restrict (Icc s t) f)
      hf_c.continuousOn.restrict hf_i.injOn.injective
    exact this.imp strictMono_restrict.mp strictAntiOn_iff_strictAnti.mpr
  have (h : StrictAntiOn f (Icc s t)) : False := by
    have : Icc a b ⊆ Icc s t := Icc_subset_Icc hsa hbt
    replace : StrictAntiOn f (Icc a b) := StrictAntiOn.mono h this
    replace : IsAntichain (· ≤ ·) (Icc a b) :=
      IsAntichain.of_strictMonoOn_antitoneOn hf_mono this.antitoneOn
    exact this.not_lt (left_mem_Icc.mpr (le_of_lt hab)) (right_mem_Icc.mpr (le_of_lt hab)) hab
  replace hf_mono_st : StrictMonoOn f (Icc s t) := hf_mono_st.resolve_right this
  have hsx : s ≤ x := min_le_right a x
  have hyt : y ≤ t := le_max_right b y
  replace : Icc x y ⊆ Icc s t := Icc_subset_Icc hsx hyt
  replace : StrictMonoOn f (Icc x y) := StrictMonoOn.mono hf_mono_st this
  exact this (left_mem_Icc.mpr (le_of_lt hxy)) (right_mem_Icc.mpr (le_of_lt hxy)) hxy

/-- Suppose `f : [a, b] → δ` is
continuous and injective. Then `f` is strictly monotone (increasing) if `f(a) ≤ f(b)`. -/
theorem ContinuousOn.strictMonoOn_of_injOn_Icc {a b : α} {f : α → δ}
    (hab : a ≤ b) (hfab : f a ≤ f b)
    (hf_c : ContinuousOn f (Icc a b)) (hf_i : InjOn f (Icc a b)) :
    StrictMonoOn f (Icc a b) := by
  have : Fact (a ≤ b) := ⟨hab⟩
  refine StrictMono.of_restrict ?_
  set g : Icc a b → δ := Set.restrict (Icc a b) f
  have hgab : g ⊥ ≤ g ⊤ := by aesop
  exact Continuous.strictMono_of_inj_boundedOrder (f := g) hf_c.restrict hgab hf_i.injective

/-- Suppose `f : [a, b] → δ` is
continuous and injective. Then `f` is strictly antitone (decreasing) if `f(b) ≤ f(a)`. -/
theorem ContinuousOn.strictAntiOn_of_injOn_Icc {a b : α} {f : α → δ}
    (hab : a ≤ b) (hfab : f b ≤ f a)
    (hf_c : ContinuousOn f (Icc a b)) (hf_i : InjOn f (Icc a b)) :
    StrictAntiOn f (Icc a b) := ContinuousOn.strictMonoOn_of_injOn_Icc (δ := δᵒᵈ) hab hfab hf_c hf_i

/-- Suppose `f : [a, b] → δ` is continuous and injective. Then `f` is strictly monotone
or antitone (increasing or decreasing). -/
theorem ContinuousOn.strictMonoOn_of_injOn_Icc' {a b : α} {f : α → δ} (hab : a ≤ b)
    (hf_c : ContinuousOn f (Icc a b)) (hf_i : InjOn f (Icc a b)) :
    StrictMonoOn f (Icc a b) ∨ StrictAntiOn f (Icc a b) :=
  (le_total (f a) (f b)).imp
    (ContinuousOn.strictMonoOn_of_injOn_Icc hab · hf_c hf_i)
    (ContinuousOn.strictAntiOn_of_injOn_Icc hab · hf_c hf_i)

/-- Suppose `α` is equipped with a conditionally complete linear dense order and `f : α → δ` is
continuous and injective. Then `f` is strictly monotone or antitone (increasing or decreasing). -/
theorem Continuous.strictMono_of_inj {f : α → δ}
    (hf_c : Continuous f) (hf_i : Injective f) : StrictMono f ∨ StrictAnti f := by
  have H {c d : α} (hcd : c < d) : StrictMono f ∨ StrictAnti f :=
    (hf_c.continuousOn.strictMonoOn_of_injOn_Icc' hcd.le hf_i.injOn).imp
      (hf_c.strictMonoOn_of_inj_rigidity hf_i hcd)
      (hf_c.strictMonoOn_of_inj_rigidity (δ := δᵒᵈ) hf_i hcd)
  cases subsingleton_or_nontrivial α with
  | inl h => exact Or.inl <| Subsingleton.strictMono f
  | inr h =>
    obtain ⟨a, b, hab⟩ := exists_pair_lt α
    exact H hab

/-- Every continuous injective `f : (a, b) → δ` is strictly monotone
or antitone (increasing or decreasing). -/
theorem ContinuousOn.strictMonoOn_of_injOn_Ioo {a b : α} {f : α → δ} (hab : a < b)
    (hf_c : ContinuousOn f (Ioo a b)) (hf_i : InjOn f (Ioo a b)) :
    StrictMonoOn f (Ioo a b) ∨ StrictAntiOn f (Ioo a b) := by
  haveI : Inhabited (Ioo a b) := Classical.inhabited_of_nonempty (nonempty_Ioo_subtype hab)
  let g : Ioo a b → δ := Set.restrict (Ioo a b) f
  have : StrictMono g ∨ StrictAnti g :=
    Continuous.strictMono_of_inj hf_c.restrict hf_i.injective
  exact this.imp strictMono_restrict.mp strictAntiOn_iff_strictAnti.mpr
