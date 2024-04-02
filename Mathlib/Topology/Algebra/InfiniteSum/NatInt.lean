/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/

import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Logic.Encodable.Lattice

/-!
# Infinite sums over `ℕ` and `ℤ`

This file contains lemmas about `HasSum`, `Summable`, `tsum`, `HasProd`, `Multipliable`, `tprod`
applied to the important special cases where the domain is `ℕ` or `ℤ`. For instance, we prove the
formula `∑ i in range k, f i + ∑' i, f (i + k) = ∑' i, f i`, in `sum_add_tsum_nat_add`, as well as
several results relating sums on `ℕ` and `ℤ`.
-/

noncomputable section

open Filter Finset Function Encodable

open scoped BigOperators Topology

variable {M : Type*} [CommMonoid M] [TopologicalSpace M] {m m' : M}

variable {G : Type*} [CommGroup G] {g g' : G}
-- don't declare [TopologicalAddGroup G] here as some results require [UniformAddGroup G] instead

/-!
## Sums over `ℕ`
-/

section Nat

section Monoid

namespace HasProd

/-- If `f : ℕ → M` has product `m`, then the partial products `∏ i in range n, f i` converge
to `m`. -/
@[to_additive "If `f : ℕ → M` has sum `m`, then the partial sums `∑ i in range n, f i` converge
to `m`."]
theorem tendsto_prod_nat {f : ℕ → M} (h : HasProd f m) :
    Tendsto (fun n ↦ ∏ i in range n, f i) atTop (𝓝 m) :=
  h.comp tendsto_finset_range
#align has_sum.tendsto_sum_nat HasSum.tendsto_sum_nat

section ContinuousMul

variable [ContinuousMul M]

@[to_additive]
theorem prod_range_mul {f : ℕ → M} {k : ℕ} (h : HasProd (fun n ↦ f (n + k)) m) :
    HasProd f ((∏ i in range k, f i) * m) := by
  refine ((range k).hasProd f).mul_compl ?_
  rwa [← (notMemRangeEquiv k).symm.hasProd_iff]

@[to_additive]
theorem zero_mul {f : ℕ → M} (h : HasProd (fun n ↦ f (n + 1)) m) :
    HasProd f (f 0 * m) := by
  simpa only [prod_range_one] using h.prod_range_mul

@[to_additive]
theorem even_mul_odd {f : ℕ → M} (he : HasProd (fun k ↦ f (2 * k)) m)
    (ho : HasProd (fun k ↦ f (2 * k + 1)) m') : HasProd f (m * m') := by
  have := mul_right_injective₀ (two_ne_zero' ℕ)
  replace ho := ((add_left_injective 1).comp this).hasProd_range_iff.2 ho
  refine (this.hasProd_range_iff.2 he).mul_isCompl ?_ ho
  simpa [(· ∘ ·)] using Nat.isCompl_even_odd
#align has_sum.even_add_odd HasSum.even_add_odd

end ContinuousMul

end HasProd

namespace Multipliable

@[to_additive]
theorem hasProd_iff_tendsto_nat [T2Space M] {f : ℕ → M} (hf : Multipliable f) :
    HasProd f m ↔ Tendsto (fun n : ℕ ↦ ∏ i in range n, f i) atTop (𝓝 m) := by
  refine ⟨fun h ↦ h.tendsto_prod_nat, fun h ↦ ?_⟩
  rw [tendsto_nhds_unique h hf.hasProd.tendsto_prod_nat]
  exact hf.hasProd
#align summable.has_sum_iff_tendsto_nat Summable.hasSum_iff_tendsto_nat

section ContinuousMul

variable [ContinuousMul M]

@[to_additive]
theorem comp_nat_add {f : ℕ → M} {k : ℕ} (h : Multipliable fun n ↦ f (n + k)) : Multipliable f :=
  h.hasProd.prod_range_mul.multipliable

@[to_additive]
theorem even_mul_odd {f : ℕ → M} (he : Multipliable fun k ↦ f (2 * k))
    (ho : Multipliable fun k ↦ f (2 * k + 1)) : Multipliable f :=
  (he.hasProd.even_mul_odd ho.hasProd).multipliable

end ContinuousMul

end Multipliable

section tprod

variable [T2Space M] {α β γ  : Type*}

section Encodable

variable [Encodable β]

/-- You can compute a product over an encodable type by multiplying over the natural numbers and
taking a supremum. -/
@[to_additive "You can compute a sum over an encodable type by summing over the natural numbers and
  taking a supremum. This is useful for outer measures."]
theorem tprod_iSup_decode₂ [CompleteLattice α] (m : α → M) (m0 : m ⊥ = 1) (s : β → α) :
    ∏' i : ℕ, m (⨆ b ∈ decode₂ β i, s b) = ∏' b : β, m (s b) := by
  rw [← tprod_extend_one (@encode_injective β _)]
  refine tprod_congr fun n ↦ ?_
  rcases em (n ∈ Set.range (encode : β → ℕ)) with ⟨a, rfl⟩ | hn
  · simp [encode_injective.extend_apply]
  · rw [extend_apply' _ _ _ hn]
    rw [← decode₂_ne_none_iff, ne_eq, not_not] at hn
    simp [hn, m0]
#align tsum_supr_decode₂ tsum_iSup_decode₂

/-- `tprod_iSup_decode₂` specialized to the complete lattice of sets. -/
@[to_additive "`tsum_iSup_decode₂` specialized to the complete lattice of sets."]
theorem tprod_iUnion_decode₂ (m : Set α → M) (m0 : m ∅ = 1) (s : β → Set α) :
    ∏' i, m (⋃ b ∈ decode₂ β i, s b) = ∏' b, m (s b) :=
  tprod_iSup_decode₂ m m0 s
#align tsum_Union_decode₂ tsum_iUnion_decode₂

end Encodable

/-! Some properties about measure-like functions. These could also be functions defined on complete
  sublattices of sets, with the property that they are countably sub-additive.
  `R` will probably be instantiated with `(≤)` in all applications.
-/
section Countable

variable [Countable β]

/-- If a function is countably sub-multiplicative then it is sub-multiplicative on countable
types -/
@[to_additive "If a function is countably sub-additive then it is sub-additive on countable types"]
theorem rel_iSup_tprod [CompleteLattice α] (m : α → M) (m0 : m ⊥ = 1) (R : M → M → Prop)
    (m_iSup : ∀ s : ℕ → α, R (m (⨆ i, s i)) (∏' i, m (s i))) (s : β → α) :
    R (m (⨆ b : β, s b)) (∏' b : β, m (s b)) := by
  cases nonempty_encodable β
  rw [← iSup_decode₂, ← tprod_iSup_decode₂ _ m0 s]
  exact m_iSup _
#align rel_supr_tsum rel_iSup_tsum

/-- If a function is countably sub-multiplicative then it is sub-multiplicative on finite sets -/
@[to_additive "If a function is countably sub-additive then it is sub-additive on finite sets"]
theorem rel_iSup_prod [CompleteLattice α] (m : α → M) (m0 : m ⊥ = 1) (R : M → M → Prop)
    (m_iSup : ∀ s : ℕ → α, R (m (⨆ i, s i)) (∏' i, m (s i))) (s : γ → α) (t : Finset γ) :
    R (m (⨆ d ∈ t, s d)) (∏ d in t, m (s d)) := by
  rw [iSup_subtype', ← Finset.tprod_subtype]
  exact rel_iSup_tprod m m0 R m_iSup _
#align rel_supr_sum rel_iSup_sum

/-- If a function is countably sub-multiplicative then it is binary sub-multiplicative -/
@[to_additive "If a function is countably sub-additive then it is binary sub-additive"]
theorem rel_sup_mul [CompleteLattice α] (m : α → M) (m0 : m ⊥ = 1) (R : M → M → Prop)
    (m_iSup : ∀ s : ℕ → α, R (m (⨆ i, s i)) (∏' i, m (s i))) (s₁ s₂ : α) :
    R (m (s₁ ⊔ s₂)) (m s₁ * m s₂) := by
  convert rel_iSup_tprod m m0 R m_iSup fun b ↦ cond b s₁ s₂
  · simp only [iSup_bool_eq, cond]
  · rw [tprod_fintype, Fintype.prod_bool, cond, cond]
#align rel_sup_add rel_sup_add

end Countable

section ContinuousMul

variable [ContinuousMul M]

@[to_additive]
theorem prod_mul_tprod_nat_mul'
    {f : ℕ → M} {k : ℕ} (h : Multipliable (fun n ↦ f (n + k))) :
    ((∏ i in range k, f i) * ∏' i, f (i + k)) = ∏' i, f i :=
  h.hasProd.prod_range_mul.tprod_eq.symm

@[to_additive]
theorem tprod_eq_zero_mul'
    {f : ℕ → M} (hf : Multipliable (fun n ↦ f (n + 1))) :
    ∏' b, f b = f 0 * ∏' b, f (b + 1) := by
  simpa only [prod_range_one] using (prod_mul_tprod_nat_mul' hf).symm

@[to_additive]
theorem tprod_even_mul_odd {f : ℕ → M} (he : Multipliable fun k ↦ f (2 * k))
    (ho : Multipliable fun k ↦ f (2 * k + 1)) :
    (∏' k, f (2 * k)) * ∏' k, f (2 * k + 1) = ∏' k, f k :=
  (he.hasProd.even_mul_odd ho.hasProd).tprod_eq.symm
#align tsum_even_add_odd tsum_even_add_odd

end ContinuousMul

end tprod

end Monoid

section TopologicalGroup

variable [TopologicalSpace G] [TopologicalGroup G]

@[to_additive]
theorem hasProd_nat_add_iff {f : ℕ → G} (k : ℕ) :
    HasProd (fun n ↦ f (n + k)) g ↔ HasProd f (g * ∏ i in range k, f i) := by
  refine Iff.trans ?_ (range k).hasProd_compl_iff
  rw [← (notMemRangeEquiv k).symm.hasProd_iff, Function.comp_def, coe_notMemRangeEquiv_symm]
#align has_sum_nat_add_iff hasSum_nat_add_iff

@[to_additive]
theorem multipliable_nat_add_iff {f : ℕ → G} (k : ℕ) :
    (Multipliable fun n ↦ f (n + k)) ↔ Multipliable f :=
  Iff.symm <|
    (Equiv.mulRight (∏ i in range k, f i)).surjective.multipliable_iff_of_hasProd_iff
      (hasProd_nat_add_iff k).symm
#align summable_nat_add_iff summable_nat_add_iff

@[to_additive]
theorem hasProd_nat_add_iff' {f : ℕ → G} (k : ℕ) :
    HasProd (fun n ↦ f (n + k)) (g / ∏ i in range k, f i) ↔ HasProd f g := by
  simp [hasProd_nat_add_iff]
#align has_sum_nat_add_iff' hasSum_nat_add_iff'

@[to_additive]
theorem prod_mul_tprod_nat_add [T2Space G] {f : ℕ → G} (k : ℕ) (h : Multipliable f) :
    ((∏ i in range k, f i) * ∏' i, f (i + k)) = ∏' i, f i :=
  prod_mul_tprod_nat_mul' <| (multipliable_nat_add_iff k).2 h
#align sum_add_tsum_nat_add sum_add_tsum_nat_add

@[to_additive]
theorem tprod_eq_zero_mul [T2Space G] {f : ℕ → G} (hf : Multipliable f) :
    ∏' b, f b = f 0 * ∏' b, f (b + 1) :=
  tprod_eq_zero_mul' <| (multipliable_nat_add_iff 1).2 hf
#align tsum_eq_zero_add tsum_eq_zero_add

/-- For `f : ℕ → G`, the product `∏' k, f (k + i)` tends to one. This does not require a
multipliability assumption on `f`, as otherwise all such products are one. -/
@[to_additive "For `f : ℕ → G`, the sum `∑' k, f (k + i)` tends to zero. This does not require a
summability assumption on `f`, as otherwise all such sums are zero."]
theorem tendsto_prod_nat_add [T2Space G] (f : ℕ → G) :
    Tendsto (fun i ↦ ∏' k, f (k + i)) atTop (𝓝 1) := by
  by_cases hf : Multipliable f
  · have h₀ : (fun i ↦ (∏' i, f i) / ∏ j in range i, f j) = fun i ↦ ∏' k : ℕ, f (k + i) := by
      ext1 i
      rw [div_eq_iff_eq_mul, mul_comm, prod_mul_tprod_nat_add i hf]
    have h₁ : Tendsto (fun _ : ℕ ↦ ∏' i, f i) atTop (𝓝 (∏' i, f i)) := tendsto_const_nhds
    simpa only [h₀, div_self'] using Tendsto.div' h₁ hf.hasProd.tendsto_prod_nat
  · refine tendsto_const_nhds.congr fun n ↦ (tprod_eq_one_of_not_multipliable ?_).symm
    rwa [multipliable_nat_add_iff n]
#align tendsto_sum_nat_add tendsto_sum_nat_add

end TopologicalGroup

section UniformGroup

variable [UniformSpace G] [UniformGroup G]

@[to_additive]
theorem cauchySeq_finset_iff_nat_tprod_vanishing {f : ℕ → G} :
    (CauchySeq fun s : Finset ℕ ↦ ∏ n in s, f n) ↔
      ∀ e ∈ 𝓝 (1 : G), ∃ N : ℕ, ∀ t ⊆ {n | N ≤ n}, (∏' n : t, f n) ∈ e := by
  refine cauchySeq_finset_iff_tprod_vanishing.trans ⟨fun vanish e he ↦ ?_, fun vanish e he ↦ ?_⟩
  · obtain ⟨s, hs⟩ := vanish e he
    refine ⟨if h : s.Nonempty then s.max' h + 1 else 0,
      fun t ht ↦ hs _ <| Set.disjoint_left.mpr ?_⟩
    split_ifs at ht with h
    · exact fun m hmt hms ↦ (s.le_max' _ hms).not_lt (Nat.succ_le_iff.mp <| ht hmt)
    · exact fun _ _ hs ↦ h ⟨_, hs⟩
  · obtain ⟨N, hN⟩ := vanish e he
    exact ⟨range N, fun t ht ↦ hN _ fun n hnt ↦
      le_of_not_lt fun h ↦ Set.disjoint_left.mp ht hnt (mem_range.mpr h)⟩

variable [CompleteSpace G]

@[to_additive]
theorem multipliable_iff_nat_tprod_vanishing {f : ℕ → G} : Multipliable f ↔
    ∀ e ∈ 𝓝 1, ∃ N : ℕ, ∀ t ⊆ {n | N ≤ n}, (∏' n : t, f n) ∈ e := by
  rw [multipliable_iff_cauchySeq_finset, cauchySeq_finset_iff_nat_tprod_vanishing]

end UniformGroup

section TopologicalGroup

variable [TopologicalSpace G] [TopologicalGroup G]

@[to_additive]
theorem Multipliable.nat_tprod_vanishing {f : ℕ → G} (hf : Multipliable f) ⦃e : Set G⦄
    (he : e ∈ 𝓝 1) : ∃ N : ℕ, ∀ t ⊆ {n | N ≤ n}, (∏' n : t, f n) ∈ e :=
  letI : UniformSpace G := TopologicalGroup.toUniformSpace G
  have : UniformGroup G := comm_topologicalGroup_is_uniform
  cauchySeq_finset_iff_nat_tprod_vanishing.1 hf.hasProd.cauchySeq e he

@[to_additive]
theorem Multipliable.tendsto_atTop_one {f : ℕ → G} (hf : Multipliable f) :
    Tendsto f atTop (𝓝 1) := by
  rw [← Nat.cofinite_eq_atTop]
  exact hf.tendsto_cofinite_one
#align summable.tendsto_at_top_zero Summable.tendsto_atTop_zero

end TopologicalGroup

end Nat

/-!
## Sums over `ℤ`

In this section we prove a variety of lemmas relating sums over `ℕ` to sums over `ℤ`.
-/

section Int

section Monoid

@[to_additive HasSum.nat_add_neg_add_one]
lemma HasProd.nat_mul_neg_add_one {f : ℤ → M} (hf : HasProd f m) :
    HasProd (fun n : ℕ ↦ f n * f (-(n + 1))) m := by
  change HasProd (fun n : ℕ ↦ f n * f (Int.negSucc n)) m
  have : Injective Int.negSucc := @Int.negSucc.inj
  refine hf.hasProd_of_prod_eq fun u ↦ ?_
  refine ⟨u.preimage _ (Nat.cast_injective.injOn _) ∪ u.preimage _ (this.injOn _),
      fun v' hv' ↦ ⟨v'.image Nat.cast ∪ v'.image Int.negSucc, fun x hx ↦ ?_, ?_⟩⟩
  · simp only [mem_union, mem_image]
    cases x
    · exact Or.inl ⟨_, hv' (by simpa using Or.inl hx), rfl⟩
    · exact Or.inr ⟨_, hv' (by simpa using Or.inr hx), rfl⟩
  · rw [prod_union, prod_image (Nat.cast_injective.injOn _), prod_image (this.injOn _),
      prod_mul_distrib]
    simp only [disjoint_iff_ne, mem_image, ne_eq, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, not_false_eq_true, implies_true, forall_const]

@[to_additive Summable.nat_add_neg_add_one]
lemma Multipliable.nat_mul_neg_add_one {f : ℤ → M} (hf : Multipliable f) :
    Multipliable (fun n : ℕ ↦ f n * f (-(n + 1))) :=
  hf.hasProd.nat_mul_neg_add_one.multipliable

@[to_additive tsum_nat_add_neg_add_one]
lemma tprod_nat_mul_neg_add_one [T2Space M] {f : ℤ → M} (hf : Multipliable f) :
    ∏' (n : ℕ), (f n * f (-(n + 1))) = ∏' (n : ℤ), f n :=
  hf.hasProd.nat_mul_neg_add_one.tprod_eq

section ContinuousMul

variable [ContinuousMul M]

@[to_additive HasSum.of_nat_of_neg_add_one]
lemma HasProd.of_nat_of_neg_add_one {f : ℤ → M}
    (hf₁ : HasProd (fun n : ℕ ↦ f n) m) (hf₂ : HasProd (fun n : ℕ ↦ f (-(n + 1))) m') :
    HasProd f (m * m') := by
  have hi₁ : Injective ((↑) : ℕ → ℤ) := @Int.ofNat.inj
  have hi₂ : Injective Int.negSucc := @Int.negSucc.inj
  have : IsCompl (Set.range ((↑) : ℕ → ℤ)) (Set.range Int.negSucc) := by
    constructor
    · rw [disjoint_iff_inf_le]
      rintro _ ⟨⟨i, rfl⟩, ⟨j, ⟨⟩⟩⟩
    · rw [codisjoint_iff_le_sup]
      rintro (i | j) <;> simp
  exact (hi₁.hasProd_range_iff.mpr hf₁).mul_isCompl this (hi₂.hasProd_range_iff.mpr hf₂)
#align has_sum.nonneg_add_neg HasSum.of_nat_of_neg_add_one

-- deprecated 2024-03-04
@[deprecated] alias HasSum.nonneg_add_neg := HasSum.of_nat_of_neg_add_one

@[to_additive Summable.of_nat_of_neg_add_one]
lemma Multipliable.of_nat_of_neg_add_one {f : ℤ → M}
    (hf₁ : Multipliable fun n : ℕ ↦ f n)  (hf₂ : Multipliable fun n : ℕ ↦ f (-(n + 1))) :
    Multipliable f :=
  (hf₁.hasProd.of_nat_of_neg_add_one hf₂.hasProd).multipliable

@[to_additive tsum_of_nat_of_neg_add_one]
lemma tprod_of_nat_of_neg_add_one [T2Space M] {f : ℤ → M}
    (hf₁ : Multipliable fun n : ℕ ↦ f n) (hf₂ : Multipliable fun n : ℕ ↦ f (-(n + 1))) :
    ∏' n : ℤ, f n = (∏' n : ℕ, f n) * ∏' n : ℕ, f (-(n + 1)) :=
  (hf₁.hasProd.of_nat_of_neg_add_one hf₂.hasProd).tprod_eq

/-- If `f₀, f₁, f₂, ...` and `g₀, g₁, g₂, ...` have products `a`, `b` respectively, then
the `ℤ`-indexed sequence: `..., g₂, g₁, g₀, f₀, f₁, f₂, ...` (with `f₀` at the `0`-th position) has
product `a + b`. -/
@[to_additive "If `f₀, f₁, f₂, ...` and `g₀, g₁, g₂, ...` have sums `a`, `b` respectively, then
the `ℤ`-indexed sequence: `..., g₂, g₁, g₀, f₀, f₁, f₂, ...` (with `f₀` at the `0`-th position) has
sum `a + b`."]
lemma HasProd.int_rec {f g : ℕ → M} (hf : HasProd f m) (hg : HasProd g m') :
    HasProd (Int.rec f g) (m * m') :=
  HasProd.of_nat_of_neg_add_one hf hg
#align has_sum.int_rec HasSum.int_rec

/-- If `f₀, f₁, f₂, ...` and `g₀, g₁, g₂, ...` are both multipliable then so is the
`ℤ`-indexed sequence: `..., g₂, g₁, g₀, f₀, f₁, f₂, ...` (with `f₀` at the `0`-th position). -/
@[to_additive "If `f₀, f₁, f₂, ...` and `g₀, g₁, g₂, ...` are both summable then so is the
`ℤ`-indexed sequence: `..., g₂, g₁, g₀, f₀, f₁, f₂, ...` (with `f₀` at the `0`-th position)."]
lemma Multipliable.int_rec {f g : ℕ → M} (hf : Multipliable f) (hg : Multipliable g) :
    Multipliable (Int.rec f g) :=
  .of_nat_of_neg_add_one hf hg

/-- If `f₀, f₁, f₂, ...` and `g₀, g₁, g₂, ...` are both multipliable, then the product of the
`ℤ`-indexed sequence: `..., g₂, g₁, g₀, f₀, f₁, f₂, ...` (with `f₀` at the `0`-th position) is
`(∏' n, f n) * ∏' n, g n`. -/
@[to_additive "If `f₀, f₁, f₂, ...` and `g₀, g₁, g₂, ...` are both summable, then the sum of the
`ℤ`-indexed sequence: `..., g₂, g₁, g₀, f₀, f₁, f₂, ...` (with `f₀` at the `0`-th position) is
`∑' n, f n + ∑' n, g n`."]
lemma tprod_int_rec [T2Space M] {f g : ℕ → M} (hf : Multipliable f) (hg : Multipliable g) :
    ∏' n : ℤ, Int.rec f g n = (∏' n : ℕ, f n) * ∏' n : ℕ, g n :=
  (hf.hasProd.int_rec hg.hasProd).tprod_eq

@[to_additive]
theorem HasProd.nat_mul_neg {f : ℤ → M} (hf : HasProd f m) :
    HasProd (fun n : ℕ ↦ f n * f (-n)) (m * f 0) := by
  -- Note this is much easier to prove if you assume more about the target space, but we have to
  -- work hard to prove it under the very minimal assumptions here.
  apply (hf.mul (hasProd_ite_eq (0 : ℤ) (f 0))).hasProd_of_prod_eq fun u ↦ ?_
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
    (∏ x in u1 ∪ u2, (f x * if x = 0 then f 0 else 1)) =
        (∏ x in u1 ∪ u2, f x) * ∏ x in u1 ∩ u2, f x := by
      rw [prod_mul_distrib]
      congr 1
      refine (prod_subset_one_on_sdiff inter_subset_union ?_ ?_).symm
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
    _ = (∏ x in u1, f x) * ∏ x in u2, f x := prod_union_inter
    _ = (∏ b in v', f b) * ∏ b in v', f (-b) := by
      simp only [u1, u2, Nat.cast_inj, imp_self, implies_true, forall_const, prod_image, neg_inj]
    _ = ∏ b in v', (f b * f (-b)) := prod_mul_distrib.symm⟩
#align has_sum.sum_nat_of_sum_int HasSum.nat_add_neg

-- deprecated 2024-03-04
@[deprecated HasSum.nat_add_neg] alias HasSum.sum_nat_of_sum_int :=
  HasSum.nat_add_neg

@[to_additive]
theorem Multipliable.nat_mul_neg {f : ℤ → M} (hf : Multipliable f) :
    Multipliable fun n : ℕ ↦ f n * f (-n) :=
  hf.hasProd.nat_mul_neg.multipliable

@[to_additive]
lemma tprod_nat_mul_neg [T2Space M] {f : ℤ → M} (hf : Multipliable f) :
    ∏' n : ℕ, (f n * f (-n)) = (∏' n : ℤ, f n) * f 0 :=
  hf.hasProd.nat_mul_neg.tprod_eq

@[to_additive HasSum.of_add_one_of_neg_add_one]
theorem HasProd.of_add_one_of_neg_add_one {f : ℤ → M}
    (hf₁ : HasProd (fun n : ℕ ↦ f (n + 1)) m) (hf₂ : HasProd (fun n : ℕ ↦ f (-(n + 1))) m') :
    HasProd f (m * f 0 * m') :=
  HasProd.of_nat_of_neg_add_one (mul_comm _ m ▸ HasProd.zero_mul hf₁) hf₂
#align has_sum.pos_add_zero_add_neg HasSum.of_add_one_of_neg_add_one

-- deprecated 2024-03-04
@[deprecated HasSum.of_add_one_of_neg_add_one] alias HasSum.pos_add_zero_add_neg :=
  HasSum.of_add_one_of_neg_add_one

@[to_additive Summable.of_add_one_of_neg_add_one]
lemma Multipliable.of_add_one_of_neg_add_one {f : ℤ → M}
    (hf₁ : Multipliable fun n : ℕ ↦ f (n + 1)) (hf₂ : Multipliable fun n : ℕ ↦ f (-(n + 1))) :
    Multipliable f :=
  (hf₁.hasProd.of_add_one_of_neg_add_one hf₂.hasProd).multipliable

@[to_additive tsum_of_add_one_of_neg_add_one]
lemma tprod_of_add_one_of_neg_add_one [T2Space M] {f : ℤ → M}
    (hf₁ : Multipliable fun n : ℕ ↦ f (n + 1)) (hf₂ : Multipliable fun n : ℕ ↦ f (-(n + 1))) :
    ∏' n : ℤ, f n = (∏' n : ℕ, f (n + 1)) * f 0 * ∏' n : ℕ, f (-(n + 1)) :=
  (hf₁.hasProd.of_add_one_of_neg_add_one hf₂.hasProd).tprod_eq

end ContinuousMul

end Monoid

section TopologicalGroup

variable [TopologicalSpace G] [TopologicalGroup G]

@[to_additive]
lemma HasProd.of_nat_of_neg {f : ℤ → G} (hf₁ : HasProd (fun n : ℕ ↦ f n) g)
    (hf₂ : HasProd (fun n : ℕ ↦ f (-n)) g') : HasProd f (g * g' / f 0) := by
  refine mul_div_assoc' g .. ▸ hf₁.of_nat_of_neg_add_one (m' := g' / f 0) ?_
  rwa [← hasProd_nat_add_iff' 1, prod_range_one, Nat.cast_zero, neg_zero] at hf₂

@[to_additive]
lemma Multipliable.of_nat_of_neg {f : ℤ → G} (hf₁ : Multipliable fun n : ℕ ↦ f n)
    (hf₂ : Multipliable fun n : ℕ ↦ f (-n)) : Multipliable f :=
  (hf₁.hasProd.of_nat_of_neg hf₂.hasProd).multipliable
#align summable_int_of_summable_nat Summable.of_nat_of_neg

-- deprecated 2024-03-04
@[deprecated Summable.of_nat_of_neg] alias summable_int_of_summable_nat :=
  Summable.of_nat_of_neg

@[to_additive]
lemma tprod_of_nat_of_neg [T2Space G] {f : ℤ → G}
    (hf₁ : Multipliable fun n : ℕ ↦ f n) (hf₂ : Multipliable fun n : ℕ ↦ f (-n)) :
    ∏' n : ℤ, f n = (∏' n : ℕ, f n) * (∏' n : ℕ, f (-n)) / f 0 :=
  (hf₁.hasProd.of_nat_of_neg hf₂.hasProd).tprod_eq

end TopologicalGroup

section UniformGroup -- results which depend on completeness

variable [UniformSpace G] [UniformGroup G] [CompleteSpace G]

/-- "iff" version of `Multipliable.of_nat_of_neg_add_one`. -/
@[to_additive "\"iff\" version of `Summable.of_nat_of_neg_add_one`."]
lemma multipliable_int_iff_multipliable_nat_and_neg_add_one {f : ℤ → G} : Multipliable f ↔
    (Multipliable fun n : ℕ ↦ f n) ∧ (Multipliable fun n : ℕ ↦ f (-(n + 1))) := by
  refine ⟨fun p ↦ ⟨?_, ?_⟩, fun ⟨hf₁, hf₂⟩ ↦ Multipliable.of_nat_of_neg_add_one hf₁ hf₂⟩ <;>
  apply p.comp_injective
  exacts [Nat.cast_injective, @Int.negSucc.inj]

/-- "iff" version of `Multipliable.of_nat_of_neg`. -/
@[to_additive "\"iff\" version of `Summable.of_nat_of_neg`."]
lemma multipliable_int_iff_multipliable_nat_and_neg {f : ℤ → G} :
    Multipliable f ↔ (Multipliable fun n : ℕ ↦ f n) ∧ (Multipliable fun n : ℕ ↦ f (-n)) := by
  refine ⟨fun p ↦ ⟨?_, ?_⟩, fun ⟨hf₁, hf₂⟩ ↦ Multipliable.of_nat_of_neg hf₁ hf₂⟩ <;>
  apply p.comp_injective
  exacts [Nat.cast_injective, neg_injective.comp Nat.cast_injective]

end UniformGroup

end Int
