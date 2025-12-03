/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
module

public import Mathlib.Order.Filter.AtTopBot.CompleteLattice
public import Mathlib.Order.Filter.AtTopBot.Group
public import Mathlib.Topology.Order.Basic

/-!
# Neighborhoods to the left and to the right on an `OrderTopology`

We've seen some properties of left and right neighborhood of a point in an `OrderClosedTopology`.
In an `OrderTopology`, such neighborhoods can be characterized as the sets containing suitable
intervals to the right or to the left of `a`. We give now these characterizations. -/

@[expose] public section

open Set Filter TopologicalSpace Topology Function

open OrderDual (toDual ofDual)

variable {α β γ : Type*}

section LinearOrder

variable [TopologicalSpace α] [LinearOrder α]

section OrderTopology

variable [OrderTopology α]

open List in
/-- The following statements are equivalent:

0. `s` is a neighborhood of `a` within `(a, +∞)`;
1. `s` is a neighborhood of `a` within `(a, b]`;
2. `s` is a neighborhood of `a` within `(a, b)`;
3. `s` includes `(a, u)` for some `u ∈ (a, b]`;
4. `s` includes `(a, u)` for some `u > a`.
-/
theorem TFAE_mem_nhdsGT {a b : α} (hab : a < b) (s : Set α) :
    TFAE [s ∈ 𝓝[>] a,
      s ∈ 𝓝[Ioc a b] a,
      s ∈ 𝓝[Ioo a b] a,
      ∃ u ∈ Ioc a b, Ioo a u ⊆ s,
      ∃ u ∈ Ioi a, Ioo a u ⊆ s] := by
  tfae_have 1 ↔ 2 := by
    rw [nhdsWithin_Ioc_eq_nhdsGT hab]
  tfae_have 1 ↔ 3 := by
    rw [nhdsWithin_Ioo_eq_nhdsGT hab]
  tfae_have 4 → 5 := fun ⟨u, umem, hu⟩ => ⟨u, umem.1, hu⟩
  tfae_have 5 → 1
  | ⟨u, hau, hu⟩ => mem_of_superset (Ioo_mem_nhdsGT hau) hu
  tfae_have 1 → 4
  | h => by
    rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.1 h with ⟨v, va, hv⟩
    rcases exists_Ico_subset_of_mem_nhds' va hab with ⟨u, au, hu⟩
    exact ⟨u, au, fun x hx => hv ⟨hu ⟨le_of_lt hx.1, hx.2⟩, hx.1⟩⟩
  tfae_finish

theorem mem_nhdsGT_iff_exists_mem_Ioc_Ioo_subset {a u' : α} {s : Set α} (hu' : a < u') :
    s ∈ 𝓝[>] a ↔ ∃ u ∈ Ioc a u', Ioo a u ⊆ s :=
  (TFAE_mem_nhdsGT hu' s).out 0 3

/-- A set is a neighborhood of `a` within `(a, +∞)` if and only if it contains an interval `(a, u)`
with `a < u < u'`, provided `a` is not a top element. -/
theorem mem_nhdsGT_iff_exists_Ioo_subset' {a u' : α} {s : Set α} (hu' : a < u') :
    s ∈ 𝓝[>] a ↔ ∃ u ∈ Ioi a, Ioo a u ⊆ s :=
  (TFAE_mem_nhdsGT hu' s).out 0 4

theorem nhdsGT_basis_of_exists_gt {a : α} (h : ∃ b, a < b) : (𝓝[>] a).HasBasis (a < ·) (Ioo a) :=
  let ⟨_, h⟩ := h
  ⟨fun _ => mem_nhdsGT_iff_exists_Ioo_subset' h⟩

lemma nhdsGT_basis [NoMaxOrder α] (a : α) : (𝓝[>] a).HasBasis (a < ·) (Ioo a) :=
  nhdsGT_basis_of_exists_gt <| exists_gt a

theorem nhdsGT_eq_bot_iff {a : α} : 𝓝[>] a = ⊥ ↔ IsTop a ∨ ∃ b, a ⋖ b := by
  by_cases ha : IsTop a
  · simp [ha, ha.isMax.Ioi_eq]
  · simp only [ha, false_or]
    rw [isTop_iff_isMax, not_isMax_iff] at ha
    simp only [(nhdsGT_basis_of_exists_gt ha).eq_bot_iff, covBy_iff_Ioo_eq]

/-- A set is a neighborhood of `a` within `(a, +∞)` if and only if it contains an interval `(a, u)`
with `a < u`. -/
theorem mem_nhdsGT_iff_exists_Ioo_subset [NoMaxOrder α] {a : α} {s : Set α} :
    s ∈ 𝓝[>] a ↔ ∃ u ∈ Ioi a, Ioo a u ⊆ s :=
  let ⟨_u', hu'⟩ := exists_gt a
  mem_nhdsGT_iff_exists_Ioo_subset' hu'

/-- The set of points which are isolated on the right is countable when the space is
second-countable. -/
theorem countable_setOf_isolated_right [SecondCountableTopology α] :
    { x : α | 𝓝[>] x = ⊥ }.Countable := by
  simp only [nhdsGT_eq_bot_iff, setOf_or]
  exact (subsingleton_isTop α).countable.union countable_setOf_covBy_right

/-- The set of points which are isolated on the left is countable when the space is
second-countable. -/
theorem countable_setOf_isolated_left [SecondCountableTopology α] :
    { x : α | 𝓝[<] x = ⊥ }.Countable :=
  countable_setOf_isolated_right (α := αᵒᵈ)

/-- The set of points in a set which are isolated on the right in this set is countable when the
space is second-countable. -/
theorem countable_setOf_isolated_right_within [SecondCountableTopology α] {s : Set α} :
    { x ∈ s | 𝓝[s ∩ Ioi x] x = ⊥ }.Countable := by
  /- This does not follow from `countable_setOf_isolated_right`, which gives the result when `s`
  is the whole space, as one cannot use it inside the subspace since it doesn't have the order
  topology. Instead, we follow the main steps of its proof. -/
  let t := { x ∈ s | 𝓝[s ∩ Ioi x] x = ⊥ ∧ ¬ IsTop x}
  suffices H : t.Countable by
    have : { x ∈ s | 𝓝[s ∩ Ioi x] x = ⊥ } ⊆ t ∪ {x | IsTop x} := by
      intro x hx
      by_cases h'x : IsTop x
      · simp [h'x]
      · simpa [-sep_and, t, h'x]
    apply Countable.mono this
    simp [H, (subsingleton_isTop α).countable]
  have (x) (hx : x ∈ t) : ∃ y > x, s ∩ Ioo x y = ∅ := by
    simp only [← empty_mem_iff_bot, mem_nhdsWithin_iff_exists_mem_nhds_inter,
      subset_empty_iff, IsTop, not_forall, not_le, mem_setOf_eq, t] at hx
    rcases hx.2.1 with ⟨u, hu, h'u⟩
    obtain ⟨y, hxy, hy⟩ : ∃ y, x < y ∧ Ico x y ⊆ u := exists_Ico_subset_of_mem_nhds hu hx.2.2
    refine ⟨y, hxy, ?_⟩
    contrapose! h'u
    apply h'u.mono
    intro z hz
    exact ⟨hy ⟨hz.2.1.le, hz.2.2⟩, hz.1, hz.2.1⟩
  choose! y hy h'y using this
  apply Set.PairwiseDisjoint.countable_of_Ioo (y := y) _ hy
  simp only [PairwiseDisjoint, Set.Pairwise, Function.onFun]
  intro a ha b hb hab
  wlog! H : a < b generalizing a b with h
  · have : b < a := lt_of_le_of_ne H hab.symm
    exact (h hb ha hab.symm this).symm
  have : y a ≤ b := by
    by_contra!
    have : b ∈ s ∩ Ioo a (y a) := by simp [hb.1, H, this]
    simp [h'y a ha] at this
  rw [disjoint_iff_forall_ne]
  exact fun u hu v hv ↦ ((hu.2.trans_le this).trans hv.1).ne

/-- The set of points in a set which are isolated on the left in this set is countable when the
space is second-countable. -/
theorem countable_setOf_isolated_left_within [SecondCountableTopology α] {s : Set α} :
    { x ∈ s | 𝓝[s ∩ Iio x] x = ⊥ }.Countable :=
  countable_setOf_isolated_right_within (α := αᵒᵈ)

/-- A set is a neighborhood of `a` within `(a, +∞)` if and only if it contains an interval `(a, u]`
with `a < u`. -/
theorem mem_nhdsGT_iff_exists_Ioc_subset [NoMaxOrder α] [DenselyOrdered α] {a : α} {s : Set α} :
    s ∈ 𝓝[>] a ↔ ∃ u ∈ Ioi a, Ioc a u ⊆ s := by
  rw [mem_nhdsGT_iff_exists_Ioo_subset]
  constructor
  · rintro ⟨u, au, as⟩
    rcases exists_between au with ⟨v, hv⟩
    exact ⟨v, hv.1, fun x hx => as ⟨hx.1, lt_of_le_of_lt hx.2 hv.2⟩⟩
  · rintro ⟨u, au, as⟩
    exact ⟨u, au, Subset.trans Ioo_subset_Ioc_self as⟩

open List in
/-- The following statements are equivalent:

0. `s` is a neighborhood of `b` within `(-∞, b)`
1. `s` is a neighborhood of `b` within `[a, b)`
2. `s` is a neighborhood of `b` within `(a, b)`
3. `s` includes `(l, b)` for some `l ∈ [a, b)`
4. `s` includes `(l, b)` for some `l < b` -/
theorem TFAE_mem_nhdsLT {a b : α} (h : a < b) (s : Set α) :
    TFAE [s ∈ 𝓝[<] b,-- 0 : `s` is a neighborhood of `b` within `(-∞, b)`
        s ∈ 𝓝[Ico a b] b,-- 1 : `s` is a neighborhood of `b` within `[a, b)`
        s ∈ 𝓝[Ioo a b] b,-- 2 : `s` is a neighborhood of `b` within `(a, b)`
        ∃ l ∈ Ico a b, Ioo l b ⊆ s,-- 3 : `s` includes `(l, b)` for some `l ∈ [a, b)`
        ∃ l ∈ Iio b, Ioo l b ⊆ s] := by-- 4 : `s` includes `(l, b)` for some `l < b`
  simpa using TFAE_mem_nhdsGT h.dual (ofDual ⁻¹' s)

theorem mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset {a l' : α} {s : Set α} (hl' : l' < a) :
    s ∈ 𝓝[<] a ↔ ∃ l ∈ Ico l' a, Ioo l a ⊆ s :=
  (TFAE_mem_nhdsLT hl' s).out 0 3

/-- A set is a neighborhood of `a` within `(-∞, a)` if and only if it contains an interval `(l, a)`
with `l < a`, provided `a` is not a bottom element. -/
theorem mem_nhdsLT_iff_exists_Ioo_subset' {a l' : α} {s : Set α} (hl' : l' < a) :
    s ∈ 𝓝[<] a ↔ ∃ l ∈ Iio a, Ioo l a ⊆ s :=
  (TFAE_mem_nhdsLT hl' s).out 0 4

/-- A set is a neighborhood of `a` within `(-∞, a)` if and only if it contains an interval `(l, a)`
with `l < a`. -/
theorem mem_nhdsLT_iff_exists_Ioo_subset [NoMinOrder α] {a : α} {s : Set α} :
    s ∈ 𝓝[<] a ↔ ∃ l ∈ Iio a, Ioo l a ⊆ s :=
  let ⟨_, h⟩ := exists_lt a
  mem_nhdsLT_iff_exists_Ioo_subset' h

/-- A set is a neighborhood of `a` within `(-∞, a)` if and only if it contains an interval `[l, a)`
with `l < a`. -/
theorem mem_nhdsLT_iff_exists_Ico_subset [NoMinOrder α] [DenselyOrdered α] {a : α} {s : Set α} :
    s ∈ 𝓝[<] a ↔ ∃ l ∈ Iio a, Ico l a ⊆ s := by
  have : ofDual ⁻¹' s ∈ 𝓝[>] toDual a ↔ _ := mem_nhdsGT_iff_exists_Ioc_subset
  simpa using this

theorem nhdsLT_basis_of_exists_lt {a : α} (h : ∃ b, b < a) : (𝓝[<] a).HasBasis (· < a) (Ioo · a) :=
  let ⟨_, h⟩ := h
  ⟨fun _ => mem_nhdsLT_iff_exists_Ioo_subset' h⟩

theorem nhdsLT_basis [NoMinOrder α] (a : α) : (𝓝[<] a).HasBasis (· < a) (Ioo · a) :=
  nhdsLT_basis_of_exists_lt <| exists_lt a

theorem nhdsLT_eq_bot_iff {a : α} : 𝓝[<] a = ⊥ ↔ IsBot a ∨ ∃ b, b ⋖ a := by
  convert (config := {preTransparency := .default}) nhdsGT_eq_bot_iff (a := OrderDual.toDual a)
    using 4
  exact ofDual_covBy_ofDual_iff

open List in
/-- The following statements are equivalent:

0. `s` is a neighborhood of `a` within `[a, +∞)`;
1. `s` is a neighborhood of `a` within `[a, b]`;
2. `s` is a neighborhood of `a` within `[a, b)`;
3. `s` includes `[a, u)` for some `u ∈ (a, b]`;
4. `s` includes `[a, u)` for some `u > a`.
-/
theorem TFAE_mem_nhdsGE {a b : α} (hab : a < b) (s : Set α) :
    TFAE [s ∈ 𝓝[≥] a,
      s ∈ 𝓝[Icc a b] a,
      s ∈ 𝓝[Ico a b] a,
      ∃ u ∈ Ioc a b, Ico a u ⊆ s,
      ∃ u ∈ Ioi a, Ico a u ⊆ s] := by
  tfae_have 1 ↔ 2 := by
    rw [nhdsWithin_Icc_eq_nhdsGE hab]
  tfae_have 1 ↔ 3 := by
    rw [nhdsWithin_Ico_eq_nhdsGE hab]
  tfae_have 1 ↔ 5 := (nhdsGE_basis_of_exists_gt ⟨b, hab⟩).mem_iff
  tfae_have 4 → 5 := fun ⟨u, umem, hu⟩ => ⟨u, umem.1, hu⟩
  tfae_have 5 → 4
  | ⟨u, hua, hus⟩ => ⟨min u b, ⟨lt_min hua hab, min_le_right _ _⟩,
      (Ico_subset_Ico_right <| min_le_left _ _).trans hus⟩
  tfae_finish

theorem mem_nhdsGE_iff_exists_mem_Ioc_Ico_subset {a u' : α} {s : Set α} (hu' : a < u') :
    s ∈ 𝓝[≥] a ↔ ∃ u ∈ Ioc a u', Ico a u ⊆ s :=
  (TFAE_mem_nhdsGE hu' s).out 0 3 (by simp) (by simp)

/-- A set is a neighborhood of `a` within `[a, +∞)` if and only if it contains an interval `[a, u)`
with `a < u < u'`, provided `a` is not a top element. -/
theorem mem_nhdsGE_iff_exists_Ico_subset' {a u' : α} {s : Set α} (hu' : a < u') :
    s ∈ 𝓝[≥] a ↔ ∃ u ∈ Ioi a, Ico a u ⊆ s :=
  (TFAE_mem_nhdsGE hu' s).out 0 4 (by simp) (by simp)

/-- A set is a neighborhood of `a` within `[a, +∞)` if and only if it contains an interval `[a, u)`
with `a < u`. -/
theorem mem_nhdsGE_iff_exists_Ico_subset [NoMaxOrder α] {a : α} {s : Set α} :
    s ∈ 𝓝[≥] a ↔ ∃ u ∈ Ioi a, Ico a u ⊆ s :=
  let ⟨_, hu'⟩ := exists_gt a
  mem_nhdsGE_iff_exists_Ico_subset' hu'

theorem nhdsGE_basis_Ico [NoMaxOrder α] (a : α) : (𝓝[≥] a).HasBasis (fun u => a < u) (Ico a) :=
  ⟨fun _ => mem_nhdsGE_iff_exists_Ico_subset⟩

/-- The filter of right neighborhoods has a basis of closed intervals. -/
theorem nhdsGE_basis_Icc [NoMaxOrder α] [DenselyOrdered α] {a : α} :
    (𝓝[≥] a).HasBasis (a < ·) (Icc a) :=
  (nhdsGE_basis _).to_hasBasis
    (fun _u hu ↦ (exists_between hu).imp fun _v hv ↦ hv.imp_right Icc_subset_Ico_right) fun u hu ↦
    ⟨u, hu, Ico_subset_Icc_self⟩

/-- A set is a neighborhood of `a` within `[a, +∞)` if and only if it contains an interval `[a, u]`
with `a < u`. -/
theorem mem_nhdsGE_iff_exists_Icc_subset [NoMaxOrder α] [DenselyOrdered α] {a : α} {s : Set α} :
    s ∈ 𝓝[≥] a ↔ ∃ u, a < u ∧ Icc a u ⊆ s :=
  nhdsGE_basis_Icc.mem_iff

open List in
/-- The following statements are equivalent:

0. `s` is a neighborhood of `b` within `(-∞, b]`
1. `s` is a neighborhood of `b` within `[a, b]`
2. `s` is a neighborhood of `b` within `(a, b]`
3. `s` includes `(l, b]` for some `l ∈ [a, b)`
4. `s` includes `(l, b]` for some `l < b` -/
theorem TFAE_mem_nhdsLE {a b : α} (h : a < b) (s : Set α) :
    TFAE [s ∈ 𝓝[≤] b,-- 0 : `s` is a neighborhood of `b` within `(-∞, b]`
      s ∈ 𝓝[Icc a b] b,-- 1 : `s` is a neighborhood of `b` within `[a, b]`
      s ∈ 𝓝[Ioc a b] b,-- 2 : `s` is a neighborhood of `b` within `(a, b]`
      ∃ l ∈ Ico a b, Ioc l b ⊆ s,-- 3 : `s` includes `(l, b]` for some `l ∈ [a, b)`
      ∃ l ∈ Iio b, Ioc l b ⊆ s] := by-- 4 : `s` includes `(l, b]` for some `l < b`
  simpa using TFAE_mem_nhdsGE h.dual (ofDual ⁻¹' s)

theorem mem_nhdsLE_iff_exists_mem_Ico_Ioc_subset {a l' : α} {s : Set α} (hl' : l' < a) :
    s ∈ 𝓝[≤] a ↔ ∃ l ∈ Ico l' a, Ioc l a ⊆ s :=
  (TFAE_mem_nhdsLE hl' s).out 0 3 (by simp) (by simp)

/-- A set is a neighborhood of `a` within `(-∞, a]` if and only if it contains an interval `(l, a]`
with `l < a`, provided `a` is not a bottom element. -/
theorem mem_nhdsLE_iff_exists_Ioc_subset' {a l' : α} {s : Set α} (hl' : l' < a) :
    s ∈ 𝓝[≤] a ↔ ∃ l ∈ Iio a, Ioc l a ⊆ s :=
  (TFAE_mem_nhdsLE hl' s).out 0 4 (by simp) (by simp)

/-- A set is a neighborhood of `a` within `(-∞, a]` if and only if it contains an interval `(l, a]`
with `l < a`. -/
theorem mem_nhdsLE_iff_exists_Ioc_subset [NoMinOrder α] {a : α} {s : Set α} :
    s ∈ 𝓝[≤] a ↔ ∃ l ∈ Iio a, Ioc l a ⊆ s :=
  let ⟨_, hl'⟩ := exists_lt a
  mem_nhdsLE_iff_exists_Ioc_subset' hl'

/-- A set is a neighborhood of `a` within `(-∞, a]` if and only if it contains an interval `[l, a]`
with `l < a`. -/
theorem mem_nhdsLE_iff_exists_Icc_subset [NoMinOrder α] [DenselyOrdered α] {a : α}
    {s : Set α} : s ∈ 𝓝[≤] a ↔ ∃ l, l < a ∧ Icc l a ⊆ s :=
  calc s ∈ 𝓝[≤] a ↔ ofDual ⁻¹' s ∈ 𝓝[≥] (toDual a) := Iff.rfl
  _ ↔ ∃ u : α, toDual a < toDual u ∧ Icc (toDual a) (toDual u) ⊆ ofDual ⁻¹' s :=
    mem_nhdsGE_iff_exists_Icc_subset
  _ ↔ ∃ l, l < a ∧ Icc l a ⊆ s := by simp

/-- The filter of left neighborhoods has a basis of closed intervals. -/
theorem nhdsLE_basis_Icc [NoMinOrder α] [DenselyOrdered α] {a : α} :
    (𝓝[≤] a).HasBasis (· < a) (Icc · a) :=
  ⟨fun _ ↦ mem_nhdsLE_iff_exists_Icc_subset⟩

end OrderTopology

end LinearOrder

section LinearOrderedCommGroup

variable [TopologicalSpace α] [CommGroup α] [LinearOrder α] [IsOrderedMonoid α]
  [OrderTopology α]
variable {l : Filter β} {f g : β → α}

@[to_additive]
theorem nhds_eq_iInf_mabs_div (a : α) : 𝓝 a = ⨅ r > 1, 𝓟 { b | |a / b|ₘ < r } := by
  simp only [nhds_eq_order, mabs_lt, setOf_and, ← inf_principal, iInf_inf_eq]
  refine (congr_arg₂ _ ?_ ?_).trans (inf_comm ..)
  · refine (Equiv.divLeft a).iInf_congr fun x => ?_; simp [Ioi]
  · refine (Equiv.divRight a).iInf_congr fun x => ?_; simp [Iio]

@[to_additive]
theorem orderTopology_of_nhds_mabs {α : Type*} [TopologicalSpace α] [CommGroup α] [LinearOrder α]
    [IsOrderedMonoid α]
    (h_nhds : ∀ a : α, 𝓝 a = ⨅ r > 1, 𝓟 { b | |a / b|ₘ < r }) : OrderTopology α := by
  refine ⟨TopologicalSpace.ext_nhds fun a => ?_⟩
  rw [h_nhds]
  letI := Preorder.topology α; letI : OrderTopology α := ⟨rfl⟩
  exact (nhds_eq_iInf_mabs_div a).symm

@[to_additive]
theorem LinearOrderedCommGroup.tendsto_nhds {x : Filter β} {a : α} :
    Tendsto f x (𝓝 a) ↔ ∀ ε > (1 : α), ∀ᶠ b in x, |f b / a|ₘ < ε := by
  simp [nhds_eq_iInf_mabs_div, mabs_div_comm a]

@[to_additive]
theorem eventually_mabs_div_lt (a : α) {ε : α} (hε : 1 < ε) : ∀ᶠ x in 𝓝 a, |x / a|ₘ < ε :=
  (nhds_eq_iInf_mabs_div a).symm ▸
    mem_iInf_of_mem ε (mem_iInf_of_mem hε <| by simp only [mabs_div_comm, mem_principal_self])

/-- In a linearly ordered commutative group with the order topology,
if `f` tends to `C` and `g` tends to `atTop` then `f * g` tends to `atTop`. -/
@[to_additive add_atTop /-- In a linearly ordered additive commutative group with the order
topology, if `f` tends to `C` and `g` tends to `atTop` then `f + g` tends to `atTop`. -/]
theorem Filter.Tendsto.mul_atTop' {C : α} (hf : Tendsto f l (𝓝 C)) (hg : Tendsto g l atTop) :
    Tendsto (fun x => f x * g x) l atTop := by
  nontriviality α
  obtain ⟨C', hC'⟩ : ∃ C', C' < C := exists_lt C
  refine tendsto_atTop_mul_left_of_le' _ C' ?_ hg
  exact (hf.eventually (lt_mem_nhds hC')).mono fun x => le_of_lt

/-- In a linearly ordered commutative group with the order topology,
if `f` tends to `C` and `g` tends to `atBot` then `f * g` tends to `atBot`. -/
@[to_additive add_atBot /-- In a linearly ordered additive commutative group with the order
topology, if `f` tends to `C` and `g` tends to `atBot` then `f + g` tends to `atBot`. -/]
theorem Filter.Tendsto.mul_atBot' {C : α} (hf : Tendsto f l (𝓝 C)) (hg : Tendsto g l atBot) :
    Tendsto (fun x => f x * g x) l atBot :=
  Filter.Tendsto.mul_atTop' (α := αᵒᵈ) hf hg

/-- In a linearly ordered commutative group with the order topology,
if `f` tends to `atTop` and `g` tends to `C` then `f * g` tends to `atTop`. -/
@[to_additive atTop_add /-- In a linearly ordered additive commutative group with the order
topology, if `f` tends to `atTop` and `g` tends to `C` then `f + g` tends to `atTop`. -/]
theorem Filter.Tendsto.atTop_mul' {C : α} (hf : Tendsto f l atTop) (hg : Tendsto g l (𝓝 C)) :
    Tendsto (fun x => f x * g x) l atTop := by
  conv in _ * _ => rw [mul_comm]
  exact hg.mul_atTop' hf

/-- In a linearly ordered commutative group with the order topology,
if `f` tends to `atBot` and `g` tends to `C` then `f * g` tends to `atBot`. -/
@[to_additive atBot_add /-- In a linearly ordered additive commutative group with the order
topology, if `f` tends to `atBot` and `g` tends to `C` then `f + g` tends to `atBot`. -/]
theorem Filter.Tendsto.atBot_mul' {C : α} (hf : Tendsto f l atBot) (hg : Tendsto g l (𝓝 C)) :
    Tendsto (fun x => f x * g x) l atBot := by
  conv in _ * _ => rw [mul_comm]
  exact hg.mul_atBot' hf

@[to_additive]
theorem nhds_basis_mabs_div_lt [NoMaxOrder α] (a : α) :
    (𝓝 a).HasBasis (fun ε : α => (1 : α) < ε) fun ε => { b | |b / a|ₘ < ε } := by
  simp only [nhds_eq_iInf_mabs_div, mabs_div_comm (a := a)]
  refine hasBasis_biInf_principal' (fun x hx y hy => ?_) (exists_gt _)
  exact ⟨min x y, lt_min hx hy, fun _ hz => hz.trans_le (min_le_left _ _),
    fun _ hz => hz.trans_le (min_le_right _ _)⟩

@[to_additive]
theorem nhds_basis_Ioo_one_lt [NoMaxOrder α] (a : α) :
    (𝓝 a).HasBasis (fun ε : α => (1 : α) < ε) fun ε => Ioo (a / ε) (a * ε) := by
  convert nhds_basis_mabs_div_lt a
  simp only [Ioo, mabs_lt, ← div_lt_iff_lt_mul, inv_lt_div_iff_lt_mul, div_lt_comm]

@[to_additive]
theorem nhds_basis_Icc_one_lt [NoMaxOrder α] [DenselyOrdered α] (a : α) :
    (𝓝 a).HasBasis ((1 : α) < ·) fun ε ↦ Icc (a / ε) (a * ε) :=
  (nhds_basis_Ioo_one_lt a).to_hasBasis
    (fun _ε ε₁ ↦ let ⟨δ, δ₁, δε⟩ := exists_between ε₁
      ⟨δ, δ₁, Icc_subset_Ioo (by gcongr) (by gcongr)⟩)
    (fun ε ε₁ ↦ ⟨ε, ε₁, Ioo_subset_Icc_self⟩)

variable (α) in
@[to_additive]
theorem nhds_basis_one_mabs_lt [NoMaxOrder α] :
    (𝓝 (1 : α)).HasBasis (fun ε : α => (1 : α) < ε) fun ε => { b | |b|ₘ < ε } := by
  simpa using nhds_basis_mabs_div_lt (1 : α)

/-- If `a > 1`, then open intervals `(a / ε, aε)`, `1 < ε ≤ a`,
form a basis of neighborhoods of `a`.

This upper bound for `ε` guarantees that all elements of these intervals are greater than one. -/
@[to_additive /-- If `a` is positive, then the intervals `(a - ε, a + ε)`, `0 < ε ≤ a`,
form a basis of neighborhoods of `a`.

This upper bound for `ε` guarantees that all elements of these intervals are positive. -/]
theorem nhds_basis_Ioo_one_lt_of_one_lt [NoMaxOrder α] {a : α} (ha : 1 < a) :
    (𝓝 a).HasBasis (fun ε : α => (1 : α) < ε ∧ ε ≤ a) fun ε => Ioo (a / ε) (a * ε) :=
  (nhds_basis_Ioo_one_lt a).restrict fun ε hε ↦
    ⟨min a ε, lt_min ha hε, min_le_left _ _, by gcongr <;> apply min_le_right⟩

end LinearOrderedCommGroup

namespace Set.OrdConnected

section ClosedIciTopology

variable [TopologicalSpace α] [LinearOrder α] [ClosedIciTopology α] {S : Set α} {x y : α}

/-- If `S` is order-connected and contains two points `x < y`,
then `S` is a right neighbourhood of `x`. -/
lemma mem_nhdsGE (hS : OrdConnected S) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) : S ∈ 𝓝[≥] x :=
  mem_of_superset (Icc_mem_nhdsGE hxy) <| hS.out hx hy

/-- If `S` is order-connected and contains two points `x < y`,
then `S` is a punctured right neighbourhood of `x`. -/
lemma mem_nhdsGT (hS : OrdConnected S) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) : S ∈ 𝓝[>] x :=
  nhdsWithin_mono _ Ioi_subset_Ici_self <| hS.mem_nhdsGE hx hy hxy

end ClosedIciTopology

variable [TopologicalSpace α] [LinearOrder α] [ClosedIicTopology α] {S : Set α} {x y : α}

/-- If `S` is order-connected and contains two points `x < y`, then `S` is a left neighbourhood
of `y`. -/
lemma mem_nhdsLE (hS : OrdConnected S) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) : S ∈ 𝓝[≤] y :=
  hS.dual.mem_nhdsGE hy hx hxy

/-- If `S` is order-connected and contains two points `x < y`, then `S` is a punctured left
neighbourhood of `y`. -/
lemma mem_nhdsLT (hS : OrdConnected S) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) : S ∈ 𝓝[<] y :=
  hS.dual.mem_nhdsGT hy hx hxy

end OrdConnected

end Set
