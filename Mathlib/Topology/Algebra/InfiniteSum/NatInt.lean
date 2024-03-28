/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Logic.Encodable.Lattice
import Mathlib.Topology.Algebra.InfiniteSum.Group

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

variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M] {m m' : M}

variable {G : Type*} [AddCommGroup G] {g g' : G}
-- don't declare [TopologicalAddGroup G] here as some results require [UniformAddGroup G] instead

/-!
## Sums over `ℕ`
-/

section Nat

section Monoid

namespace HasSum

/-- If `f : ℕ → M` has sum `m`, then the partial sums `∑ i in range n, f i` converge to `m`. -/
theorem tendsto_sum_nat {f : ℕ → M} (h : HasSum f m) :
    Tendsto (fun n ↦ ∑ i in range n, f i) atTop (𝓝 m) :=
  h.comp tendsto_finset_range
#align has_sum.tendsto_sum_nat HasSum.tendsto_sum_nat

section ContinuousAdd

variable [ContinuousAdd M]

theorem sum_range_add {f : ℕ → M} {k : ℕ} (h : HasSum (fun n ↦ f (n + k)) m) :
    HasSum f ((∑ i in range k, f i) + m) := by
  refine ((range k).hasSum f).add_compl ?_
  rwa [← (notMemRangeEquiv k).symm.hasSum_iff]

theorem zero_add {f : ℕ → M} (h : HasSum (fun n ↦ f (n + 1)) m) :
    HasSum f (f 0 + m) := by
  simpa only [sum_range_one] using h.sum_range_add

theorem even_add_odd {f : ℕ → M} (he : HasSum (fun k ↦ f (2 * k)) m)
    (ho : HasSum (fun k ↦ f (2 * k + 1)) m') : HasSum f (m + m') := by
  have := mul_right_injective₀ (two_ne_zero' ℕ)
  replace ho := ((add_left_injective 1).comp this).hasSum_range_iff.2 ho
  refine (this.hasSum_range_iff.2 he).add_isCompl ?_ ho
  simpa [(· ∘ ·)] using Nat.isCompl_even_odd
#align has_sum.even_add_odd HasSum.even_add_odd

end ContinuousAdd

end HasSum

namespace Summable

theorem hasSum_iff_tendsto_nat [T2Space M] {f : ℕ → M} (hf : Summable f) :
    HasSum f m ↔ Tendsto (fun n : ℕ ↦ ∑ i in range n, f i) atTop (𝓝 m) := by
  refine ⟨fun h ↦ h.tendsto_sum_nat, fun h ↦ ?_⟩
  rw [tendsto_nhds_unique h hf.hasSum.tendsto_sum_nat]
  exact hf.hasSum
#align summable.has_sum_iff_tendsto_nat Summable.hasSum_iff_tendsto_nat

section ContinuousAdd

variable [ContinuousAdd M]

theorem comp_nat_add {f : ℕ → M} {k : ℕ} (h : Summable fun n ↦ f (n + k)) : Summable f :=
  h.hasSum.sum_range_add.summable

theorem even_add_odd {f : ℕ → M} (he : Summable fun k ↦ f (2 * k))
    (ho : Summable fun k ↦ f (2 * k + 1)) : Summable f :=
  (he.hasSum.even_add_odd ho.hasSum).summable

end ContinuousAdd

end Summable

section tsum

variable [T2Space M] {α β γ  : Type*}

section Encodable

variable [Encodable β]

/-- You can compute a sum over an encodable type by summing over the natural numbers and
  taking a supremum. This is useful for outer measures. -/
theorem tsum_iSup_decode₂ [CompleteLattice α] (m : α → M) (m0 : m ⊥ = 0) (s : β → α) :
    ∑' i : ℕ, m (⨆ b ∈ decode₂ β i, s b) = ∑' b : β, m (s b) := by
  rw [← tsum_extend_zero (@encode_injective β _)]
  refine tsum_congr fun n ↦ ?_
  rcases em (n ∈ Set.range (encode : β → ℕ)) with ⟨a, rfl⟩ | hn
  · simp [encode_injective.extend_apply]
  · rw [extend_apply' _ _ _ hn]
    rw [← decode₂_ne_none_iff, ne_eq, not_not] at hn
    simp [hn, m0]
#align tsum_supr_decode₂ tsum_iSup_decode₂

/-- `tsum_iSup_decode₂` specialized to the complete lattice of sets. -/
theorem tsum_iUnion_decode₂ (m : Set α → M) (m0 : m ∅ = 0) (s : β → Set α) :
    ∑' i, m (⋃ b ∈ decode₂ β i, s b) = ∑' b, m (s b) :=
  tsum_iSup_decode₂ m m0 s
#align tsum_Union_decode₂ tsum_iUnion_decode₂

end Encodable

/-! Some properties about measure-like functions. These could also be functions defined on complete
  sublattices of sets, with the property that they are countably sub-additive.
  `R` will probably be instantiated with `(≤)` in all applications.
-/
section Countable

variable [Countable β]

/-- If a function is countably sub-additive then it is sub-additive on countable types -/
theorem rel_iSup_tsum [CompleteLattice α] (m : α → M) (m0 : m ⊥ = 0) (R : M → M → Prop)
    (m_iSup : ∀ s : ℕ → α, R (m (⨆ i, s i)) (∑' i, m (s i))) (s : β → α) :
    R (m (⨆ b : β, s b)) (∑' b : β, m (s b)) := by
  cases nonempty_encodable β
  rw [← iSup_decode₂, ← tsum_iSup_decode₂ _ m0 s]
  exact m_iSup _
#align rel_supr_tsum rel_iSup_tsum

/-- If a function is countably sub-additive then it is sub-additive on finite sets -/
theorem rel_iSup_sum [CompleteLattice α] (m : α → M) (m0 : m ⊥ = 0) (R : M → M → Prop)
    (m_iSup : ∀ s : ℕ → α, R (m (⨆ i, s i)) (∑' i, m (s i))) (s : γ → α) (t : Finset γ) :
    R (m (⨆ d ∈ t, s d)) (∑ d in t, m (s d)) := by
  rw [iSup_subtype', ← Finset.tsum_subtype]
  exact rel_iSup_tsum m m0 R m_iSup _
#align rel_supr_sum rel_iSup_sum

/-- If a function is countably sub-additive then it is binary sub-additive -/
theorem rel_sup_add [CompleteLattice α] (m : α → M) (m0 : m ⊥ = 0) (R : M → M → Prop)
    (m_iSup : ∀ s : ℕ → α, R (m (⨆ i, s i)) (∑' i, m (s i))) (s₁ s₂ : α) :
    R (m (s₁ ⊔ s₂)) (m s₁ + m s₂) := by
  convert rel_iSup_tsum m m0 R m_iSup fun b ↦ cond b s₁ s₂
  · simp only [iSup_bool_eq, cond]
  · rw [tsum_fintype, Fintype.sum_bool, cond, cond]
#align rel_sup_add rel_sup_add

end Countable

section ContinuousAdd

variable [ContinuousAdd M]

theorem sum_add_tsum_nat_add'
    {f : ℕ → M} {k : ℕ} (h : Summable (fun n ↦ f (n + k))) :
    ((∑ i in range k, f i) + ∑' i, f (i + k)) = ∑' i, f i :=
  h.hasSum.sum_range_add.tsum_eq.symm

theorem tsum_eq_zero_add'
    {f : ℕ → M} (hf : Summable (fun n ↦ f (n + 1))) :
    ∑' b, f b = f 0 + ∑' b, f (b + 1) := by
  simpa only [sum_range_one] using (sum_add_tsum_nat_add' hf).symm

theorem tsum_even_add_odd {f : ℕ → M} (he : Summable fun k ↦ f (2 * k))
    (ho : Summable fun k ↦ f (2 * k + 1)) :
    ∑' k, f (2 * k) + ∑' k, f (2 * k + 1) = ∑' k, f k :=
  (he.hasSum.even_add_odd ho.hasSum).tsum_eq.symm
#align tsum_even_add_odd tsum_even_add_odd

end ContinuousAdd

end tsum

end Monoid

section TopologicalGroup

variable [TopologicalSpace G] [TopologicalAddGroup G]

theorem hasSum_nat_add_iff {f : ℕ → G} (k : ℕ) :
    HasSum (fun n ↦ f (n + k)) g ↔ HasSum f (g + ∑ i in range k, f i) := by
  refine Iff.trans ?_ (range k).hasSum_compl_iff
  rw [← (notMemRangeEquiv k).symm.hasSum_iff, Function.comp_def, coe_notMemRangeEquiv_symm]
#align has_sum_nat_add_iff hasSum_nat_add_iff

theorem summable_nat_add_iff {f : ℕ → G} (k : ℕ) : (Summable fun n ↦ f (n + k)) ↔ Summable f :=
  Iff.symm <|
    (Equiv.addRight (∑ i in range k, f i)).surjective.summable_iff_of_hasSum_iff
      (hasSum_nat_add_iff k).symm
#align summable_nat_add_iff summable_nat_add_iff

theorem hasSum_nat_add_iff' {f : ℕ → G} (k : ℕ) :
    HasSum (fun n ↦ f (n + k)) (g - ∑ i in range k, f i) ↔ HasSum f g := by
  simp [hasSum_nat_add_iff]
#align has_sum_nat_add_iff' hasSum_nat_add_iff'

theorem sum_add_tsum_nat_add [T2Space G] {f : ℕ → G} (k : ℕ) (h : Summable f) :
    ((∑ i in range k, f i) + ∑' i, f (i + k)) = ∑' i, f i :=
  sum_add_tsum_nat_add' <| (summable_nat_add_iff k).2 h
#align sum_add_tsum_nat_add sum_add_tsum_nat_add

theorem tsum_eq_zero_add [T2Space G] {f : ℕ → G} (hf : Summable f) :
    ∑' b, f b = f 0 + ∑' b, f (b + 1) :=
  tsum_eq_zero_add' <| (summable_nat_add_iff 1).2 hf
#align tsum_eq_zero_add tsum_eq_zero_add

/-- For `f : ℕ → G`, then `∑' k, f (k + i)` tends to zero. This does not require a summability
assumption on `f`, as otherwise all sums are zero. -/
theorem tendsto_sum_nat_add [T2Space G] (f : ℕ → G) :
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

variable [UniformSpace G] [UniformAddGroup G]

theorem cauchySeq_finset_iff_nat_tsum_vanishing {f : ℕ → G} :
    (CauchySeq fun s : Finset ℕ ↦ ∑ n in s, f n) ↔
      ∀ e ∈ 𝓝 (0 : G), ∃ N : ℕ, ∀ t ⊆ {n | N ≤ n}, (∑' n : t, f n) ∈ e := by
  refine cauchySeq_finset_iff_tsum_vanishing.trans ⟨fun vanish e he ↦ ?_, fun vanish e he ↦ ?_⟩
  · obtain ⟨s, hs⟩ := vanish e he
    refine ⟨if h : s.Nonempty then s.max' h + 1 else 0, fun t ht ↦ hs _ <| Set.disjoint_left.mpr ?_⟩
    split_ifs at ht with h
    · exact fun m hmt hms ↦ (s.le_max' _ hms).not_lt (Nat.succ_le_iff.mp <| ht hmt)
    · exact fun _ _ hs ↦ h ⟨_, hs⟩
  · obtain ⟨N, hN⟩ := vanish e he
    exact ⟨range N, fun t ht ↦ hN _ fun n hnt ↦
      le_of_not_lt fun h ↦ Set.disjoint_left.mp ht hnt (mem_range.mpr h)⟩

variable [CompleteSpace G]

theorem summable_iff_nat_tsum_vanishing {f : ℕ → G} : Summable f ↔
    ∀ e ∈ 𝓝 0, ∃ N : ℕ, ∀ t ⊆ {n | N ≤ n}, (∑' n : t, f n) ∈ e := by
  rw [summable_iff_cauchySeq_finset, cauchySeq_finset_iff_nat_tsum_vanishing]

end UniformGroup

section TopologicalGroup

variable [TopologicalSpace G] [TopologicalAddGroup G]

theorem Summable.nat_tsum_vanishing {f : ℕ → G} (hf : Summable f) ⦃e : Set G⦄ (he : e ∈ 𝓝 0) :
    ∃ N : ℕ, ∀ t ⊆ {n | N ≤ n}, (∑' n : t, f n) ∈ e :=
  letI : UniformSpace G := TopologicalAddGroup.toUniformSpace G
  have : UniformAddGroup G := comm_topologicalAddGroup_is_uniform
  cauchySeq_finset_iff_nat_tsum_vanishing.1 hf.hasSum.cauchySeq e he

theorem Summable.tendsto_atTop_zero {f : ℕ → G} (hf : Summable f) : Tendsto f atTop (𝓝 0) := by
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

lemma HasSum.nat_add_neg_add_one {f : ℤ → M} (hf : HasSum f m) :
    HasSum (fun n : ℕ ↦ f n + f (-(n + 1))) m := by
  change HasSum (fun n : ℕ ↦ f n + f (Int.negSucc n)) m
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

lemma Summable.nat_add_neg_add_one {f : ℤ → M} (hf : Summable f) :
    Summable (fun n : ℕ ↦ f n + f (-(n + 1))) :=
  hf.hasSum.nat_add_neg_add_one.summable

lemma tsum_nat_add_neg_add_one [T2Space M] {f : ℤ → M} (hf : Summable f) :
    ∑' (n : ℕ), (f n + f (-(n + 1))) = ∑' (n : ℤ), f n :=
  hf.hasSum.nat_add_neg_add_one.tsum_eq

section ContinuousAdd

variable [ContinuousAdd M]

lemma HasSum.of_nat_of_neg_add_one {f : ℤ → M}
    (hf₁ : HasSum (fun n : ℕ ↦ f n) m) (hf₂ : HasSum (fun n : ℕ ↦ f (-(n + 1))) m') :
    HasSum f (m + m') := by
  have hi₁ : Injective ((↑) : ℕ → ℤ) := @Int.ofNat.inj
  have hi₂ : Injective Int.negSucc := @Int.negSucc.inj
  have : IsCompl (Set.range ((↑) : ℕ → ℤ)) (Set.range Int.negSucc) := by
    constructor
    · rw [disjoint_iff_inf_le]
      rintro _ ⟨⟨i, rfl⟩, ⟨j, ⟨⟩⟩⟩
    · rw [codisjoint_iff_le_sup]
      rintro (i | j) <;> simp
  exact (hi₁.hasSum_range_iff.mpr hf₁).add_isCompl this (hi₂.hasSum_range_iff.mpr hf₂)
#align has_sum.nonneg_add_neg HasSum.of_nat_of_neg_add_one

-- deprecated 2024-03-04
@[deprecated] alias HasSum.nonneg_add_neg := HasSum.of_nat_of_neg_add_one

lemma Summable.of_nat_of_neg_add_one {f : ℤ → M}
    (hf₁ : Summable fun n : ℕ ↦ f n)  (hf₂ : Summable fun n : ℕ ↦ f (-(n + 1))) :
    Summable f :=
  (hf₁.hasSum.of_nat_of_neg_add_one hf₂.hasSum).summable

lemma tsum_of_nat_of_neg_add_one [T2Space M] {f : ℤ → M}
    (hf₁ : Summable fun n : ℕ ↦ f n) (hf₂ : Summable fun n : ℕ ↦ f (-(n + 1))) :
    ∑' n : ℤ, f n = ∑' n : ℕ, f n + ∑' n : ℕ, f (-(n + 1)) :=
  (hf₁.hasSum.of_nat_of_neg_add_one hf₂.hasSum).tsum_eq

/-- If `f₀, f₁, f₂, ...` and `g₀, g₁, g₂, ...` have sums `a`, `b` respectively, then the `ℤ`-indexed
sequence: `..., g₂, g₁, g₀, f₀, f₁, f₂, ...` (with `f₀` at the `0`-th position) has sum `a + b`. -/
lemma HasSum.int_rec {f g : ℕ → M} (hf : HasSum f m) (hg : HasSum g m') :
    HasSum (Int.rec f g) (m + m') :=
  HasSum.of_nat_of_neg_add_one hf hg
#align has_sum.int_rec HasSum.int_rec

/-- If `f₀, f₁, f₂, ...` and `g₀, g₁, g₂, ...` are both summable then so is the `ℤ`-indexed
sequence: `..., g₂, g₁, g₀, f₀, f₁, f₂, ...` (with `f₀` at the `0`-th position). -/
lemma Summable.int_rec {f g : ℕ → M} (hf : Summable f) (hg : Summable g) : Summable (Int.rec f g) :=
  .of_nat_of_neg_add_one hf hg

/-- If `f₀, f₁, f₂, ...` and `g₀, g₁, g₂, ...` are both summable, then the sum of the `ℤ`-indexed
sequence: `..., g₂, g₁, g₀, f₀, f₁, f₂, ...` (with `f₀` at the `0`-th position) is
`∑' n, f n + ∑' n, g n`. -/
lemma tsum_int_rec [T2Space M] {f g : ℕ → M} (hf : Summable f) (hg : Summable g) :
    ∑' n : ℤ, Int.rec f g n = ∑' n : ℕ, f n + ∑' n : ℕ, g n :=
  (hf.hasSum.int_rec hg.hasSum).tsum_eq

theorem HasSum.nat_add_neg {f : ℤ → M} (hf : HasSum f m) :
    HasSum (fun n : ℕ ↦ f n + f (-n)) (m + f 0) := by
  -- Note this is much easier to prove if you assume more about the target space, but we have to
  -- work hard to prove it under the very minimal assumptions here.
  apply (hf.add (hasSum_ite_eq (0 : ℤ) (f 0))).hasSum_of_sum_eq fun u ↦ ?_
  refine ⟨u.image Int.natAbs, fun v' hv' ↦ ?_⟩
  let u1 := v'.image fun x : ℕ ↦ (x : ℤ)
  let u2 := v'.image fun x : ℕ ↦ -(x : ℤ)
  have A : u ⊆ u1 ∪ u2 := by
    intro x hx
    simp only [u1, u2, mem_union, mem_image, exists_prop]
    rcases le_total 0 x with (h'x | h'x)
    · refine Or.inl ⟨_, hv' <| mem_image.mpr ⟨x, hx, rfl⟩, ?_⟩
      simp only [Int.coe_natAbs, abs_eq_self, h'x]
    · refine Or.inr ⟨_, hv' <| mem_image.mpr ⟨x, hx, rfl⟩, ?_⟩
      simp only [abs_of_nonpos h'x, Int.coe_natAbs, neg_neg]
  exact ⟨_, A, calc
    (∑ x in u1 ∪ u2, (f x + if x = 0 then f 0 else 0)) =
        (∑ x in u1 ∪ u2, f x) + ∑ x in u1 ∩ u2, f x := by
      rw [sum_add_distrib]
      congr 1
      refine (sum_subset_zero_on_sdiff inter_subset_union ?_ ?_).symm
      · intro x hx
        suffices x ≠ 0 by simp only [this, if_false]
        rintro rfl
        simp only [mem_sdiff, mem_union, mem_image, Nat.cast_eq_zero, exists_eq_right, neg_eq_zero,
          or_self, mem_inter, and_self, and_not_self, u1, u2] at hx
      · intro x hx
        simp only [u1, u2, mem_inter, mem_image, exists_prop] at hx
        suffices x = 0 by simp only [this, eq_self_iff_true, if_true]
        apply le_antisymm
        · rcases hx.2 with ⟨a, _, rfl⟩
          simp only [Right.neg_nonpos_iff, Nat.cast_nonneg]
        · rcases hx.1 with ⟨a, _, rfl⟩
          simp only [Nat.cast_nonneg]
    _ = (∑ x in u1, f x) + ∑ x in u2, f x := sum_union_inter
    _ = (∑ b in v', f b) + ∑ b in v', f (-b) := by
      simp only [u1, u2, Nat.cast_inj, imp_self, implies_true, forall_const, sum_image, neg_inj]
    _ = ∑ b in v', (f b + f (-b)) := sum_add_distrib.symm⟩
#align has_sum.sum_nat_of_sum_int HasSum.nat_add_neg

-- deprecated 2024-03-04
@[deprecated HasSum.nat_add_neg] alias HasSum.sum_nat_of_sum_int :=
  HasSum.nat_add_neg

theorem Summable.nat_add_neg {f : ℤ → M} (hf : Summable f) :
    Summable fun n : ℕ ↦ f n + f (-n) :=
  hf.hasSum.nat_add_neg.summable

lemma tsum_nat_add_neg [T2Space M] {f : ℤ → M} (hf : Summable f) :
    ∑' n : ℕ, (f n + f (-n)) = (∑' n : ℤ, f n) + f 0 :=
  hf.hasSum.nat_add_neg.tsum_eq

theorem HasSum.of_add_one_of_neg_add_one {f : ℤ → M}
    (hf₁ : HasSum (fun n : ℕ ↦ f (n + 1)) m) (hf₂ : HasSum (fun n : ℕ ↦ f (-(n + 1))) m') :
    HasSum f (m + f 0 + m') :=
  HasSum.of_nat_of_neg_add_one (add_comm _ m ▸ HasSum.zero_add hf₁) hf₂
#align has_sum.pos_add_zero_add_neg HasSum.of_add_one_of_neg_add_one

-- deprecated 2024-03-04
@[deprecated HasSum.of_add_one_of_neg_add_one] alias HasSum.pos_add_zero_add_neg :=
  HasSum.of_add_one_of_neg_add_one

lemma Summable.of_add_one_of_neg_add_one {f : ℤ → M}
    (hf₁ : Summable fun n : ℕ ↦ f (n + 1)) (hf₂ : Summable fun n : ℕ ↦ f (-(n + 1))) :
    Summable f :=
  (hf₁.hasSum.of_add_one_of_neg_add_one hf₂.hasSum).summable

lemma tsum_of_add_one_of_neg_add_one [T2Space M] {f : ℤ → M}
    (hf₁ : Summable fun n : ℕ ↦ f (n + 1)) (hf₂ : Summable fun n : ℕ ↦ f (-(n + 1))) :
    ∑' n : ℤ, f n = ∑' n : ℕ, f (n + 1) + f 0 + ∑' n : ℕ, f (-(n + 1)) :=
  (hf₁.hasSum.of_add_one_of_neg_add_one hf₂.hasSum).tsum_eq

end ContinuousAdd

end Monoid

section TopologicalGroup

variable [TopologicalSpace G] [TopologicalAddGroup G]

lemma HasSum.of_nat_of_neg {f : ℤ → G} (hf₁ : HasSum (fun n : ℕ ↦ f n) g)
    (hf₂ : HasSum (fun n : ℕ ↦ f (-n)) g') : HasSum f (g + g' - f 0) := by
  refine add_sub_assoc' g .. ▸ hf₁.nonneg_add_neg (m' := g' - f 0) ?_
  rwa [← hasSum_nat_add_iff' 1, sum_range_one, Nat.cast_zero, neg_zero] at hf₂

lemma Summable.of_nat_of_neg {f : ℤ → G} (hf₁ : Summable fun n : ℕ ↦ f n)
    (hf₂ : Summable fun n : ℕ ↦ f (-n)) : Summable f :=
  (hf₁.hasSum.of_nat_of_neg hf₂.hasSum).summable
#align summable_int_of_summable_nat Summable.of_nat_of_neg

-- deprecated 2024-03-04
@[deprecated Summable.of_nat_of_neg] alias summable_int_of_summable_nat :=
  Summable.of_nat_of_neg

lemma tsum_of_nat_of_neg [T2Space G] {f : ℤ → G}
    (hf₁ : Summable fun n : ℕ ↦ f n) (hf₂ : Summable fun n : ℕ ↦ f (-n)) :
    ∑' n : ℤ, f n = ∑' n : ℕ, f n + ∑' n : ℕ, f (-n) - f 0 :=
  (hf₁.hasSum.of_nat_of_neg hf₂.hasSum).tsum_eq

end TopologicalGroup

section UniformGroup -- results which depend on completeness

variable [UniformSpace G] [UniformAddGroup G] [CompleteSpace G]

/-- "iff" version of `Summable.of_nat_of_neg_add_one`. -/
lemma summable_int_iff_summable_nat_and_neg_add_one {f : ℤ → G} :
    Summable f ↔ (Summable fun n : ℕ ↦ f n) ∧ (Summable fun n : ℕ ↦ f (-(n + 1))) := by
  refine ⟨fun p ↦ ⟨?_, ?_⟩, fun ⟨hf₁, hf₂⟩ ↦ Summable.of_nat_of_neg_add_one hf₁ hf₂⟩ <;>
  apply p.comp_injective
  exacts [Nat.cast_injective, @Int.negSucc.inj]

/-- "iff" version of `Summable.of_natCast_neg_natCast`. -/
lemma summable_int_iff_summable_nat_and_neg {f : ℤ → G} :
    Summable f ↔ (Summable fun n : ℕ ↦ f n) ∧ (Summable fun n : ℕ ↦ f (-n)) := by
  refine ⟨fun p ↦ ⟨?_, ?_⟩, fun ⟨hf₁, hf₂⟩ ↦ Summable.of_nat_of_neg hf₁ hf₂⟩ <;>
  apply p.comp_injective
  exacts [Nat.cast_injective, neg_injective.comp Nat.cast_injective]

end UniformGroup

end Int
