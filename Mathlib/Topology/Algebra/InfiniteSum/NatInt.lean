/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/

import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Logic.Encodable.Lattice

/-!
# Infinite sums over `ℕ` and `ℤ`

This file contains lemmas about `HasSum`, `Summable`, and `tsum` applied to the important special
cases where the domain is `ℕ` or `ℤ`. For instance, we prove the formula
`∑ i in range k, f i + ∑' i, f (i + k) = ∑' i, f i`, in `sum_add_tsum_nat_add`, as well as several
results relating sums on `ℕ` and `ℤ`.
-/

noncomputable section

open Filter Finset Function Encodable

open scoped BigOperators Topology

variable {α β γ δ : Type*}

/-!
## Sums over `ℕ`
-/

section Nat

section Monoid

variable [AddCommMonoid α] [TopologicalSpace α]

namespace HasSum

variable {a b : α}

/-- If `f : ℕ → α` has sum `a`, then the partial sums `∑_{i=0}^{n-1} f i` converge to `a`. -/
theorem tendsto_sum_nat {f : ℕ → α} (h : HasSum f a) :
    Tendsto (fun n : ℕ ↦ ∑ i in range n, f i) atTop (𝓝 a) :=
  h.comp tendsto_finset_range
#align has_sum.tendsto_sum_nat HasSum.tendsto_sum_nat

section ContinuousAdd

variable [ContinuousAdd α]

theorem sum_range_add {f : ℕ → α}
    {k : ℕ} {a : α} (h : HasSum (fun n ↦ f (n + k)) a) : HasSum f ((∑ i in range k, f i) + a) := by
  refine ((range k).hasSum f).add_compl ?_
  rwa [← (notMemRangeEquiv k).symm.hasSum_iff]

theorem zero_add {f : ℕ → α} {a : α} (h : HasSum (fun n ↦ f (n + 1)) a) :
    HasSum f (f 0 + a) := by
  simpa only [sum_range_one] using h.sum_range_add

theorem even_add_odd {f : ℕ → α} (he : HasSum (fun k ↦ f (2 * k)) a)
    (ho : HasSum (fun k ↦ f (2 * k + 1)) b) : HasSum f (a + b) := by
  have := mul_right_injective₀ (two_ne_zero' ℕ)
  replace ho := ((add_left_injective 1).comp this).hasSum_range_iff.2 ho
  refine' (this.hasSum_range_iff.2 he).add_isCompl _ ho
  simpa [(· ∘ ·)] using Nat.isCompl_even_odd
#align has_sum.even_add_odd HasSum.even_add_odd

end ContinuousAdd

end HasSum

namespace Summable

theorem hasSum_iff_tendsto_nat [T2Space α] {f : ℕ → α} {a : α} (hf : Summable f) :
    HasSum f a ↔ Tendsto (fun n : ℕ ↦ ∑ i in range n, f i) atTop (𝓝 a) := by
  refine ⟨fun h ↦ h.tendsto_sum_nat, fun h ↦ ?_⟩
  rw [tendsto_nhds_unique h hf.hasSum.tendsto_sum_nat]
  exact hf.hasSum
#align summable.has_sum_iff_tendsto_nat Summable.hasSum_iff_tendsto_nat

section ContinuousAdd

variable [ContinuousAdd α]

theorem comp_nat_add {f : ℕ → α} {k : ℕ} (h : Summable fun n ↦ f (n + k)) : Summable f :=
  h.hasSum.sum_range_add.summable

theorem even_add_odd {f : ℕ → α} (he : Summable fun k ↦ f (2 * k))
    (ho : Summable fun k ↦ f (2 * k + 1)) : Summable f :=
  (he.hasSum.even_add_odd ho.hasSum).summable

end ContinuousAdd

end Summable

section tsum

variable [T2Space α]

section Encodable

variable [Encodable γ]

/-- You can compute a sum over an encodable type by summing over the natural numbers and
  taking a supremum. This is useful for outer measures. -/
theorem tsum_iSup_decode₂ [CompleteLattice β] (m : β → α) (m0 : m ⊥ = 0) (s : γ → β) :
    ∑' i : ℕ, m (⨆ b ∈ decode₂ γ i, s b) = ∑' b : γ, m (s b) := by
  rw [← tsum_extend_zero (@encode_injective γ _)]
  refine tsum_congr fun n ↦ ?_
  rcases em (n ∈ Set.range (encode : γ → ℕ)) with ⟨a, rfl⟩ | hn
  · simp [encode_injective.extend_apply]
  · rw [extend_apply' _ _ _ hn]
    rw [← decode₂_ne_none_iff, ne_eq, not_not] at hn
    simp [hn, m0]
#align tsum_supr_decode₂ tsum_iSup_decode₂

/-- `tsum_iSup_decode₂` specialized to the complete lattice of sets. -/
theorem tsum_iUnion_decode₂ (m : Set β → α) (m0 : m ∅ = 0) (s : γ → Set β) :
    ∑' i, m (⋃ b ∈ decode₂ γ i, s b) = ∑' b, m (s b) :=
  tsum_iSup_decode₂ m m0 s
#align tsum_Union_decode₂ tsum_iUnion_decode₂

end Encodable

/-! Some properties about measure-like functions. These could also be functions defined on complete
  sublattices of sets, with the property that they are countably sub-additive.
  `R` will probably be instantiated with `(≤)` in all applications.
-/
section Countable

variable [Countable γ]

/-- If a function is countably sub-additive then it is sub-additive on countable types -/
theorem rel_iSup_tsum [CompleteLattice β] (m : β → α) (m0 : m ⊥ = 0) (R : α → α → Prop)
    (m_iSup : ∀ s : ℕ → β, R (m (⨆ i, s i)) (∑' i, m (s i))) (s : γ → β) :
    R (m (⨆ b : γ, s b)) (∑' b : γ, m (s b)) := by
  cases nonempty_encodable γ
  rw [← iSup_decode₂, ← tsum_iSup_decode₂ _ m0 s]
  exact m_iSup _
#align rel_supr_tsum rel_iSup_tsum

/-- If a function is countably sub-additive then it is sub-additive on finite sets -/
theorem rel_iSup_sum [CompleteLattice β] (m : β → α) (m0 : m ⊥ = 0) (R : α → α → Prop)
    (m_iSup : ∀ s : ℕ → β, R (m (⨆ i, s i)) (∑' i, m (s i))) (s : δ → β) (t : Finset δ) :
    R (m (⨆ d ∈ t, s d)) (∑ d in t, m (s d)) := by
  rw [iSup_subtype', ← Finset.tsum_subtype]
  exact rel_iSup_tsum m m0 R m_iSup _
#align rel_supr_sum rel_iSup_sum

/-- If a function is countably sub-additive then it is binary sub-additive -/
theorem rel_sup_add [CompleteLattice β] (m : β → α) (m0 : m ⊥ = 0) (R : α → α → Prop)
    (m_iSup : ∀ s : ℕ → β, R (m (⨆ i, s i)) (∑' i, m (s i))) (s₁ s₂ : β) :
    R (m (s₁ ⊔ s₂)) (m s₁ + m s₂) := by
  convert rel_iSup_tsum m m0 R m_iSup fun b ↦ cond b s₁ s₂
  · simp only [iSup_bool_eq, cond]
  · rw [tsum_fintype, Fintype.sum_bool, cond, cond]
#align rel_sup_add rel_sup_add

end Countable

section ContinuousAdd

variable [ContinuousAdd α]

theorem sum_add_tsum_nat_add'
    {f : ℕ → α} {k : ℕ} (h : Summable (fun n ↦ f (n + k))) :
    ((∑ i in range k, f i) + ∑' i, f (i + k)) = ∑' i, f i :=
  h.hasSum.sum_range_add.tsum_eq.symm

theorem tsum_eq_zero_add'
    {f : ℕ → α} (hf : Summable (fun n ↦ f (n + 1))) :
    ∑' b, f b = f 0 + ∑' b, f (b + 1) := by
  simpa only [sum_range_one] using (sum_add_tsum_nat_add' hf).symm

theorem tsum_even_add_odd {f : ℕ → α} (he : Summable fun k ↦ f (2 * k))
    (ho : Summable fun k ↦ f (2 * k + 1)) :
    ∑' k, f (2 * k) + ∑' k, f (2 * k + 1) = ∑' k, f k :=
  (he.hasSum.even_add_odd ho.hasSum).tsum_eq.symm
#align tsum_even_add_odd tsum_even_add_odd

end ContinuousAdd

end tsum

end Monoid

section TopologicalGroup

variable [AddCommGroup α] [TopologicalSpace α] [TopologicalAddGroup α]

theorem hasSum_nat_add_iff {f : ℕ → α} (k : ℕ) {a : α} :
    HasSum (fun n ↦ f (n + k)) a ↔ HasSum f (a + ∑ i in range k, f i) := by
  refine' Iff.trans _ (range k).hasSum_compl_iff
  rw [← (notMemRangeEquiv k).symm.hasSum_iff]
  rfl
#align has_sum_nat_add_iff hasSum_nat_add_iff

theorem summable_nat_add_iff {f : ℕ → α} (k : ℕ) : (Summable fun n ↦ f (n + k)) ↔ Summable f :=
  Iff.symm <|
    (Equiv.addRight (∑ i in range k, f i)).surjective.summable_iff_of_hasSum_iff
      (hasSum_nat_add_iff k).symm
#align summable_nat_add_iff summable_nat_add_iff

theorem hasSum_nat_add_iff' {f : ℕ → α} (k : ℕ) {a : α} :
    HasSum (fun n ↦ f (n + k)) (a - ∑ i in range k, f i) ↔ HasSum f a := by
  simp [hasSum_nat_add_iff]
#align has_sum_nat_add_iff' hasSum_nat_add_iff'

theorem sum_add_tsum_nat_add [T2Space α] {f : ℕ → α} (k : ℕ) (h : Summable f) :
    ((∑ i in range k, f i) + ∑' i, f (i + k)) = ∑' i, f i :=
  sum_add_tsum_nat_add' <| (summable_nat_add_iff k).2 h
#align sum_add_tsum_nat_add sum_add_tsum_nat_add

theorem tsum_eq_zero_add [T2Space α] {f : ℕ → α} (hf : Summable f) :
    ∑' b, f b = f 0 + ∑' b, f (b + 1) :=
  tsum_eq_zero_add' <| (summable_nat_add_iff 1).2 hf
#align tsum_eq_zero_add tsum_eq_zero_add

/-- For `f : ℕ → α`, then `∑' k, f (k + i)` tends to zero. This does not require a summability
assumption on `f`, as otherwise all sums are zero. -/
theorem tendsto_sum_nat_add [T2Space α] (f : ℕ → α) :
    Tendsto (fun i ↦ ∑' k, f (k + i)) atTop (𝓝 0) := by
  by_cases hf : Summable f
  · have h₀ : (fun i ↦ ∑' i, f i - ∑ j in range i, f j) = fun i ↦ ∑' k : ℕ, f (k + i) := by
      ext1 i
      rw [sub_eq_iff_eq_add, add_comm, sum_add_tsum_nat_add i hf]
    have h₁ : Tendsto (fun _ : ℕ ↦ ∑' i, f i) atTop (𝓝 (∑' i, f i)) := tendsto_const_nhds
    simpa only [h₀, sub_self] using Tendsto.sub h₁ hf.hasSum.tendsto_sum_nat
  · refine tendsto_const_nhds.congr fun n ↦ (tsum_eq_zero_of_not_summable ?_).symm
    rwa [summable_nat_add_iff n]
#align tendsto_sum_nat_add tendsto_sum_nat_add

end TopologicalGroup

section UniformGroup

variable [AddCommGroup α] [UniformSpace α] [UniformAddGroup α]

theorem cauchySeq_finset_iff_nat_tsum_vanishing {f : ℕ → α} :
    (CauchySeq fun s : Finset ℕ ↦ ∑ n in s, f n) ↔
      ∀ e ∈ 𝓝 (0 : α), ∃ N : ℕ, ∀ t ⊆ {n | N ≤ n}, (∑' n : t, f n) ∈ e := by
  refine cauchySeq_finset_iff_tsum_vanishing.trans ⟨fun vanish e he ↦ ?_, fun vanish e he ↦ ?_⟩
  · obtain ⟨s, hs⟩ := vanish e he
    refine ⟨if h : s.Nonempty then s.max' h + 1 else 0, fun t ht ↦ hs _ <| Set.disjoint_left.mpr ?_⟩
    split_ifs at ht with h
    · exact fun m hmt hms ↦ (s.le_max' _ hms).not_lt (Nat.succ_le_iff.mp <| ht hmt)
    · exact fun _ _ hs ↦ h ⟨_, hs⟩
  · obtain ⟨N, hN⟩ := vanish e he
    exact ⟨range N, fun t ht ↦ hN _ fun n hnt ↦
      le_of_not_lt fun h ↦ Set.disjoint_left.mp ht hnt (mem_range.mpr h)⟩

variable [CompleteSpace α]

theorem summable_iff_nat_tsum_vanishing {f : ℕ → α} : Summable f ↔
    ∀ e ∈ 𝓝 (0 : α), ∃ N : ℕ, ∀ t ⊆ {n | N ≤ n}, (∑' n : t, f n) ∈ e := by
  rw [summable_iff_cauchySeq_finset, cauchySeq_finset_iff_nat_tsum_vanishing]

end UniformGroup

section TopologicalGroup

variable [TopologicalSpace α] [AddCommGroup α] [TopologicalAddGroup α]

theorem Summable.nat_tsum_vanishing {f : ℕ → α} (hf : Summable f) ⦃e : Set α⦄ (he : e ∈ 𝓝 0) :
    ∃ N : ℕ, ∀ t ⊆ {n | N ≤ n}, (∑' n : t, f n) ∈ e :=
  letI : UniformSpace α := TopologicalAddGroup.toUniformSpace α
  have : UniformAddGroup α := comm_topologicalAddGroup_is_uniform
  cauchySeq_finset_iff_nat_tsum_vanishing.1 hf.hasSum.cauchySeq e he

theorem Summable.tendsto_atTop_zero {f : ℕ → α} (hf : Summable f) : Tendsto f atTop (𝓝 0) := by
  rw [← Nat.cofinite_eq_atTop]
  exact hf.tendsto_cofinite_zero
#align summable.tendsto_at_top_zero Summable.tendsto_atTop_zero

end TopologicalGroup

end Nat

/-!
## Sums over `ℤ`

In this section we prove a variety of lemmas relating sums over `ℕ` to sums over `ℤ`.
-/

section Int

section Monoid

variable [AddCommMonoid α] [TopologicalSpace α] {a b : α}

lemma HasSum.natCast_add_negSucc {f : ℤ → α} (hf : HasSum f a) :
    HasSum (fun n : ℕ ↦ f n + f (Int.negSucc n)) a := by
  have : Injective Int.negSucc := @Int.negSucc.inj
  refine hf.hasSum_of_sum_eq fun u ↦ ?_
  refine ⟨u.preimage _ (Nat.cast_injective.injOn _) ∪ u.preimage _ (this.injOn _),
      fun v' hv' ↦ ⟨v'.image Nat.cast ∪ v'.image Int.negSucc, fun x hx ↦ ?_, ?_⟩⟩
  · simp only [mem_union, mem_image]
    cases x
    · exact Or.inl ⟨_, hv' (by simpa using Or.inl hx), rfl⟩
    · exact Or.inr ⟨_, hv' (by simpa using Or.inr hx), rfl⟩
  · rw [sum_union, sum_image (Nat.cast_injective.injOn _), sum_image (this.injOn _),
      sum_add_distrib]
    simp only [disjoint_iff_ne, mem_image, ne_eq, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, not_false_eq_true, implies_true, forall_const]

lemma Summable.natCast_add_negSucc {f : ℤ → α} (hf : Summable f) :
    Summable (fun n : ℕ ↦ f n + f (Int.negSucc n)) :=
  hf.hasSum.natCast_add_negSucc.summable

lemma tsum_natCast_add_negSucc [T2Space α] {f : ℤ → α} (hf : Summable f) :
    ∑' (n : ℕ), (f n + f (Int.negSucc n)) = ∑' (n : ℤ), f n :=
  hf.hasSum.natCast_add_negSucc.tsum_eq

section ContinuousAdd

variable [ContinuousAdd α]

lemma HasSum.of_natCast_negSucc {f : ℤ → α}
    (hf₁ : HasSum (fun n : ℕ ↦ f n) a) (hf₂ : HasSum (fun n : ℕ ↦ f (Int.negSucc n)) b) :
    HasSum f (a + b) := by
  have hi₁ : Injective ((↑) : ℕ → ℤ) := @Int.ofNat.inj
  have hi₂ : Injective Int.negSucc := @Int.negSucc.inj
  have : IsCompl (Set.range ((↑) : ℕ → ℤ)) (Set.range Int.negSucc) := by
    constructor
    · rw [disjoint_iff_inf_le]
      rintro _ ⟨⟨i, rfl⟩, ⟨j, ⟨⟩⟩⟩
    · rw [codisjoint_iff_le_sup]
      rintro (i | j) <;> simp
  exact (hi₁.hasSum_range_iff.mpr hf₁).add_isCompl this (hi₂.hasSum_range_iff.mpr hf₂)
#align has_sum.nonneg_add_neg HasSum.of_natCast_negSucc

-- deprecated 2024-03-04
@[deprecated] alias HasSum.nonneg_add_neg := HasSum.of_natCast_negSucc

lemma Summable.of_natCast_negSucc {f : ℤ → α}
    (hf₁ : Summable fun n : ℕ ↦ f n)  (hf₂ : Summable fun n : ℕ ↦ f (Int.negSucc n)) :
    Summable f :=
  (hf₁.hasSum.of_natCast_negSucc hf₂.hasSum).summable

lemma tsum_of_natCast_negSucc [T2Space α] {f : ℤ → α}
    (hf₁ : Summable fun n : ℕ ↦ f n) (hf₂ : Summable fun n : ℕ ↦ f (Int.negSucc n)) :
    ∑' n : ℤ, f n = ∑' n : ℕ, f n + ∑' n : ℕ, f (Int.negSucc n) :=
  (hf₁.hasSum.of_natCast_negSucc hf₂.hasSum).tsum_eq

/-- If `f₀, f₁, f₂, ...` and `g₀, g₁, g₂, ...` have sums `a`, `b` respectively, then the `ℤ`-indexed
sequence: `..., g₂, g₁, g₀, f₀, f₁, f₂, ...` (with `f₀` at the `0`-th position) has sum `a + b`. -/
lemma HasSum.int_rec {f g : ℕ → α} (hf : HasSum f a) (hg : HasSum g b) :
    HasSum (Int.rec f g) (a + b) :=
  HasSum.of_natCast_negSucc hf hg
#align has_sum.int_rec HasSum.int_rec

/-- If `f₀, f₁, f₂, ...` and `g₀, g₁, g₂, ...` are both summable then so is the `ℤ`-indexed
sequence: `..., g₂, g₁, g₀, f₀, f₁, f₂, ...` (with `f₀` at the `0`-th position). -/
lemma Summable.int_rec {f g : ℕ → α} (hf : Summable f) (hg : Summable g) : Summable (Int.rec f g) :=
  .of_natCast_negSucc hf hg

/-- If `f₀, f₁, f₂, ...` and `g₀, g₁, g₂, ...` are both summable, then the sum of the `ℤ`-indexed
sequence: `..., g₂, g₁, g₀, f₀, f₁, f₂, ...` (with `f₀` at the `0`-th position) is
`∑' n, f n + ∑' n, g n`. -/
lemma tsum_int_rec [T2Space α] {f g : ℕ → α} (hf : Summable f) (hg : Summable g) :
    ∑' n : ℤ, Int.rec f g n = ∑' n : ℕ, f n + ∑' n : ℕ, g n :=
  (hf.hasSum.int_rec hg.hasSum).tsum_eq

theorem HasSum.natCast_add_neg_natCast {f : ℤ → α} (hf : HasSum f a) :
    HasSum (fun n : ℕ ↦ f n + f (-n)) (a + f 0) := by
  apply (hf.add (hasSum_ite_eq (0 : ℤ) (f 0))).hasSum_of_sum_eq fun u ↦ ?_
  refine' ⟨u.image Int.natAbs, fun v' hv' ↦ _⟩
  let u1 := v'.image fun x : ℕ ↦ (x : ℤ)
  let u2 := v'.image fun x : ℕ ↦ -(x : ℤ)
  have A : u ⊆ u1 ∪ u2 := by
    intro x hx
    simp only [u1, u2, mem_union, mem_image, exists_prop]
    rcases le_total 0 x with (h'x | h'x)
    · left
      refine' ⟨Int.natAbs x, hv' _, _⟩
      · simp only [mem_image, exists_prop]
        exact ⟨x, hx, rfl⟩
      · simp only [h'x, Int.coe_natAbs, abs_eq_self]
    · right
      refine' ⟨Int.natAbs x, hv' _, _⟩
      · simp only [mem_image, exists_prop]
        exact ⟨x, hx, rfl⟩
      · simp only [abs_of_nonpos h'x, Int.coe_natAbs, neg_neg]
  refine' ⟨u1 ∪ u2, A, _⟩
  calc
    (∑ x in u1 ∪ u2, (f x + ite (x = 0) (f 0) 0)) =
        (∑ x in u1 ∪ u2, f x) + ∑ x in u1 ∩ u2, f x := by
      rw [sum_add_distrib]
      congr 1
      refine' (sum_subset_zero_on_sdiff inter_subset_union _ _).symm
      · intro x hx
        suffices x ≠ 0 by simp only [this, if_false]
        rintro rfl
        simp only [mem_sdiff, mem_union, mem_image, Nat.cast_eq_zero, exists_eq_right, neg_eq_zero,
          or_self, mem_inter, and_self, and_not_self, u1, u2] at hx
      · intro x hx
        simp only [u1, u2, mem_inter, mem_image, exists_prop] at hx
        have : x = 0 := by
          apply le_antisymm
          · rcases hx.2 with ⟨a, _, rfl⟩
            simp only [Right.neg_nonpos_iff, Nat.cast_nonneg]
          · rcases hx.1 with ⟨a, _, rfl⟩
            simp only [Nat.cast_nonneg]
        simp only [this, eq_self_iff_true, if_true]
    _ = (∑ x in u1, f x) + ∑ x in u2, f x := sum_union_inter
    _ = (∑ b in v', f b) + ∑ b in v', f (-b) := by
      simp only [u1, u2, Nat.cast_inj, imp_self, implies_true, forall_const, sum_image, neg_inj]
    _ = ∑ b in v', (f b + f (-b)) := sum_add_distrib.symm
#align has_sum.sum_nat_of_sum_int HasSum.natCast_add_neg_natCast

-- deprecated 2024-03-04
@[deprecated HasSum.natCast_add_neg_natCast] alias HasSum.sum_nat_of_sum_int :=
  HasSum.natCast_add_neg_natCast

theorem Summable.natCast_add_neg_natCast {f : ℤ → α} (hf : Summable f) :
    Summable fun n : ℕ ↦ f n + f (-n) :=
  hf.hasSum.natCast_add_neg_natCast.summable

lemma tsum_natCast_add_neg_natCast [T2Space α] {f : ℤ → α} (hf : Summable f) :
    ∑' n : ℕ, (f n + f (-n)) = (∑' n : ℤ, f n) + f 0 :=
  hf.hasSum.natCast_add_neg_natCast.tsum_eq

theorem HasSum.of_succ_negSucc {a b : α} {f : ℤ → α}
    (hf₁ : HasSum (fun n : ℕ ↦ f (n + 1)) a) (hf₂ : HasSum (fun n : ℕ ↦ f (Int.negSucc n)) b) :
    HasSum f (a + f 0 + b) :=
  haveI : ∀ g : ℕ → α, HasSum (fun k ↦ g (k + 1)) a → HasSum g (a + g 0) :=
    fun g hg ↦ by simpa using (add_comm _ a ▸ hg.sum_range_add :)
  (this (fun n ↦ f n) hf₁).nonneg_add_neg hf₂
#align has_sum.pos_add_zero_add_neg HasSum.of_succ_negSucc

-- deprecated 2024-03-04
@[deprecated HasSum.of_succ_negSucc] alias HasSum.pos_add_zero_add_neg :=
  HasSum.of_succ_negSucc

lemma Summable.of_succ_negSucc {f : ℤ → α}
    (hf₁ : Summable fun n : ℕ ↦ f (n + 1)) (hf₂ : Summable fun n : ℕ ↦ f (Int.negSucc n)) :
    Summable f :=
  (hf₁.hasSum.of_succ_negSucc hf₂.hasSum).summable

lemma tsum_of_succ_negSucc [T2Space α] {f : ℤ → α}
    (hf₁ : Summable fun n : ℕ ↦ f (n + 1)) (hf₂ : Summable fun n : ℕ ↦ f (Int.negSucc n)) :
    ∑' n : ℤ, f n = ∑' n : ℕ, f (n + 1) + f 0 + ∑' n : ℕ, f (Int.negSucc n) :=
  (hf₁.hasSum.of_succ_negSucc hf₂.hasSum).tsum_eq

end ContinuousAdd

end Monoid

section TopologicalGroup

variable [AddCommGroup α] [TopologicalSpace α] [TopologicalAddGroup α]

lemma HasSum.of_natCast_neg_natCast {a b : α} {f : ℤ → α} (hf₁ : HasSum (fun n : ℕ ↦ f n) a)
    (hf₂ : HasSum (fun n : ℕ ↦ f (-n)) b) : HasSum f (a + b - f 0) := by
  refine add_sub_assoc' a .. ▸ hf₁.nonneg_add_neg (b := b - f 0) ?_
  rwa [← hasSum_nat_add_iff' 1, sum_range_one, Nat.cast_zero, neg_zero] at hf₂

lemma Summable.of_natCast_neg_natCast {f : ℤ → α} (hf₁ : Summable fun n : ℕ ↦ f n)
    (hf₂ : Summable fun n : ℕ ↦ f (-n)) : Summable f :=
  (hf₁.hasSum.of_natCast_neg_natCast hf₂.hasSum).summable
#align summable_int_of_summable_nat Summable.of_natCast_neg_natCast

-- deprecated 2024-03-04
@[deprecated Summable.of_natCast_neg_natCast] alias summable_int_of_summable_nat :=
  Summable.of_natCast_neg_natCast

lemma tsum_of_natCast_neg_natCast [T2Space α] {f : ℤ → α}
    (hf₁ : Summable fun n : ℕ ↦ f n) (hf₂ : Summable fun n : ℕ ↦ f (-n)) :
    ∑' n : ℤ, f n = ∑' n : ℕ, f n + ∑' n : ℕ, f (-n) - f 0 :=
  (hf₁.hasSum.of_natCast_neg_natCast hf₂.hasSum).tsum_eq

end TopologicalGroup

section UniformGroup -- results which depend on completeness

variable [AddCommGroup α] [UniformSpace α] [UniformAddGroup α] [CompleteSpace α]

/-- "iff" version of `Summable.of_natCast_negSucc`. -/
lemma summable_int_iff_summable_natCast_negSucc {f : ℤ → α} :
    Summable f ↔ (Summable fun n : ℕ ↦ f n) ∧ (Summable fun n : ℕ ↦ f (Int.negSucc n)) := by
  refine ⟨fun p ↦ ⟨?_, ?_⟩, fun ⟨hf₁, hf₂⟩ ↦ Summable.of_natCast_negSucc hf₁ hf₂⟩ <;>
  apply p.comp_injective
  exacts [Nat.cast_injective, @Int.negSucc.inj]

/-- "iff" version of `Summable.of_natCast_neg_natCast`. -/
lemma summable_int_iff_summable_natCast_neg_natCast {f : ℤ → α} :
    Summable f ↔ (Summable fun n : ℕ ↦ f n) ∧ (Summable fun n : ℕ ↦ f (-n)) := by
  refine ⟨fun p ↦ ⟨?_, ?_⟩, fun ⟨hf₁, hf₂⟩ ↦ Summable.of_natCast_neg_natCast hf₁ hf₂⟩ <;>
  apply p.comp_injective
  exacts [Nat.cast_injective, neg_injective.comp Nat.cast_injective]

end UniformGroup

end Int
