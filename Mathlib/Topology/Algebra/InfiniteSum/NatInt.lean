/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.Group.EvenFunction
public import Mathlib.Logic.Encodable.Lattice
public import Mathlib.Order.Filter.AtTopBot.Finset
public import Mathlib.Topology.Algebra.InfiniteSum.Group

/-!
# Infinite sums and products over `ℕ` and `ℤ`

This file contains lemmas about `HasSum`, `Summable`, `tsum`, `HasProd`, `Multipliable`, and `tprod`
applied to the important special cases where the domain is `ℕ` or `ℤ`. For instance, we prove the
formula `∑ i ∈ range k, f i + ∑' i, f (i + k) = ∑' i, f i`, ∈ `sum_add_tsum_nat_add`, as well as
several results relating sums and products on `ℕ` to sums and products on `ℤ`.
-/
set_option backward.defeqAttrib.useBackward true

public section

noncomputable section

open Filter Finset Function Encodable

open scoped Topology

variable {M : Type*} [CommMonoid M] [TopologicalSpace M] {m m' : M}

variable {G : Type*} [CommGroup G] {g g' : G}
-- don't declare `[IsTopologicalAddGroup G]`, here as some results require
-- `[IsUniformAddGroup G]` instead

/-!
## Sums over `ℕ`
-/

section Nat

section Monoid

/-- If `f : ℕ → M` has product `m`, then the partial products `∏ i ∈ range n, f i` converge
to `m`. -/
@[to_additive /-- If `f : ℕ → M` has sum `m`, then the partial sums `∑ i ∈ range n, f i` converge
to `m`. -/]
theorem HasProd.tendsto_prod_nat {f : ℕ → M} (h : HasProd f m) :
    Tendsto (fun n ↦ ∏ i ∈ range n, f i) atTop (𝓝 m) :=
  h.comp tendsto_finset_range

/-- If `f : ℕ → M` is multipliable, then the partial products `∏ i ∈ range n, f i` converge
to `∏' i, f i`. -/
@[to_additive /-- If `f : ℕ → M` is summable, then the partial sums `∑ i ∈ range n, f i` converge
to `∑' i, f i`. -/]
theorem Multipliable.tendsto_prod_tprod_nat {f : ℕ → M} (h : Multipliable f) :
    Tendsto (fun n ↦ ∏ i ∈ range n, f i) atTop (𝓝 (∏' i, f i)) :=
  h.hasProd.tendsto_prod_nat

namespace HasProd

section ContinuousMul

variable [ContinuousMul M]

@[to_additive]
theorem prod_range_mul {f : ℕ → M} {k : ℕ} (h : HasProd (fun n ↦ f (n + k)) m) :
    HasProd f ((∏ i ∈ range k, f i) * m) :=
  ((range k).hasProd f).mul_compl <| (notMemRangeEquiv k).symm.hasProd_iff.mp h

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
  simpa [Function.comp_def] using Nat.isCompl_even_odd

end ContinuousMul

end HasProd

namespace Multipliable

@[to_additive]
theorem hasProd_iff_tendsto_nat [T2Space M] {f : ℕ → M} (hf : Multipliable f) :
    HasProd f m ↔ Tendsto (fun n : ℕ ↦ ∏ i ∈ range n, f i) atTop (𝓝 m) := by
  refine ⟨fun h ↦ h.tendsto_prod_nat, fun h ↦ ?_⟩
  rw [tendsto_nhds_unique h hf.hasProd.tendsto_prod_nat]
  exact hf.hasProd

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

variable {α β γ : Type*}

section Encodable

variable [Encodable β]

/-- You can compute a product over an encodable type by multiplying over the natural numbers and
taking a supremum. -/
@[to_additive /-- You can compute a sum over an encodable type by summing over the natural numbers
and taking a supremum. This is useful for outer measures. -/]
theorem tprod_iSup_decode₂ [CompleteLattice α] (m : α → M) (m0 : m ⊥ = 1) (s : β → α) :
    ∏' i : ℕ, m (⨆ b ∈ decode₂ β i, s b) = ∏' b : β, m (s b) := by
  rw [← tprod_extend_one (@encode_injective β _)]
  refine tprod_congr fun n ↦ ?_
  rcases em (n ∈ Set.range (encode : β → ℕ)) with ⟨a, rfl⟩ | hn
  · simp [encode_injective.extend_apply]
  · rw [extend_apply' _ _ _ hn]
    rw [← decode₂_ne_none_iff, ne_eq, not_not] at hn
    simp [hn, m0]

/-- `tprod_iSup_decode₂` specialized to the complete lattice of sets. -/
@[to_additive /-- `tsum_iSup_decode₂` specialized to the complete lattice of sets. -/]
theorem tprod_iUnion_decode₂ (m : Set α → M) (m0 : m ∅ = 1) (s : β → Set α) :
    ∏' i, m (⋃ b ∈ decode₂ β i, s b) = ∏' b, m (s b) :=
  tprod_iSup_decode₂ m m0 s

end Encodable

/-! Some properties about measure-like functions. These could also be functions defined on complete
  sublattices of sets, with the property that they are countably sub-additive.
  `R` will probably be instantiated with `(≤)` in all applications.
-/
section Countable

variable [Countable β]

/-- If a function is countably sub-multiplicative then it is sub-multiplicative on countable
types -/
@[to_additive
/-- If a function is countably sub-additive then it is sub-additive on countable types -/]
theorem rel_iSup_tprod [CompleteLattice α] (m : α → M) (m0 : m ⊥ = 1) (R : M → M → Prop)
    (m_iSup : ∀ s : ℕ → α, R (m (⨆ i, s i)) (∏' i, m (s i))) (s : β → α) :
    R (m (⨆ b : β, s b)) (∏' b : β, m (s b)) := by
  cases nonempty_encodable β
  rw [← iSup_decode₂, ← tprod_iSup_decode₂ _ m0 s]
  exact m_iSup _

/-- If a function is countably sub-multiplicative then it is sub-multiplicative on finite sets -/
@[to_additive /-- If a function is countably sub-additive then it is sub-additive on finite sets -/]
theorem rel_iSup_prod [CompleteLattice α] (m : α → M) (m0 : m ⊥ = 1) (R : M → M → Prop)
    (m_iSup : ∀ s : ℕ → α, R (m (⨆ i, s i)) (∏' i, m (s i))) (s : γ → α) (t : Finset γ) :
    R (m (⨆ d ∈ t, s d)) (∏ d ∈ t, m (s d)) := by
  rw [iSup_subtype', ← Finset.tprod_subtype]
  exact rel_iSup_tprod m m0 R m_iSup _

/-- If a function is countably sub-multiplicative then it is binary sub-multiplicative -/
@[to_additive /-- If a function is countably sub-additive then it is binary sub-additive -/]
theorem rel_sup_mul [CompleteLattice α] (m : α → M) (m0 : m ⊥ = 1) (R : M → M → Prop)
    (m_iSup : ∀ s : ℕ → α, R (m (⨆ i, s i)) (∏' i, m (s i))) (s₁ s₂ : α) :
    R (m (s₁ ⊔ s₂)) (m s₁ * m s₂) := by
  convert rel_iSup_tprod m m0 R m_iSup fun b ↦ cond b s₁ s₂
  · simp only [iSup_bool_eq, cond]
  · rw [tprod_fintype, Fintype.prod_bool, cond, cond]

end Countable

section ContinuousMul

variable [T2Space M] [ContinuousMul M]

@[to_additive]
protected theorem Multipliable.prod_mul_tprod_nat_mul'
    {f : ℕ → M} {k : ℕ} (h : Multipliable (fun n ↦ f (n + k))) :
    ((∏ i ∈ range k, f i) * ∏' i, f (i + k)) = ∏' i, f i :=
  h.hasProd.prod_range_mul.tprod_eq.symm

@[to_additive]
theorem tprod_eq_zero_mul'
    {f : ℕ → M} (hf : Multipliable (fun n ↦ f (n + 1))) :
    ∏' b, f b = f 0 * ∏' b, f (b + 1) := by
  simpa only [prod_range_one] using hf.prod_mul_tprod_nat_mul'.symm

@[to_additive]
theorem tprod_even_mul_odd {f : ℕ → M} (he : Multipliable fun k ↦ f (2 * k))
    (ho : Multipliable fun k ↦ f (2 * k + 1)) :
    (∏' k, f (2 * k)) * ∏' k, f (2 * k + 1) = ∏' k, f k :=
  (he.hasProd.even_mul_odd ho.hasProd).tprod_eq.symm

end ContinuousMul

end tprod

end Monoid

section IsTopologicalGroup

variable [TopologicalSpace G] [IsTopologicalGroup G]

@[to_additive]
theorem hasProd_nat_add_iff {f : ℕ → G} (k : ℕ) :
    HasProd (fun n ↦ f (n + k)) g ↔ HasProd f (g * ∏ i ∈ range k, f i) := by
  refine Iff.trans ?_ (range k).hasProd_compl_iff
  rw [← (notMemRangeEquiv k).symm.hasProd_iff, Function.comp_def, coe_notMemRangeEquiv_symm]

@[to_additive]
theorem multipliable_nat_add_iff {f : ℕ → G} (k : ℕ) :
    (Multipliable fun n ↦ f (n + k)) ↔ Multipliable f :=
  Iff.symm <|
    (Equiv.mulRight (∏ i ∈ range k, f i)).surjective.multipliable_iff_of_hasProd_iff
      (hasProd_nat_add_iff k).symm

@[to_additive]
theorem hasProd_nat_add_iff' {f : ℕ → G} (k : ℕ) :
    HasProd (fun n ↦ f (n + k)) (g / ∏ i ∈ range k, f i) ↔ HasProd f g := by
  simp [hasProd_nat_add_iff]

@[to_additive]
protected theorem Multipliable.prod_mul_tprod_nat_add [T2Space G] {f : ℕ → G} (k : ℕ)
    (h : Multipliable f) : ((∏ i ∈ range k, f i) * ∏' i, f (i + k)) = ∏' i, f i :=
  Multipliable.prod_mul_tprod_nat_mul' <| (multipliable_nat_add_iff k).2 h

@[to_additive]
protected theorem Multipliable.tprod_eq_zero_mul [T2Space G] {f : ℕ → G} (hf : Multipliable f) :
    ∏' b, f b = f 0 * ∏' b, f (b + 1) :=
  tprod_eq_zero_mul' <| (multipliable_nat_add_iff 1).2 hf

/-- For `f : ℕ → G`, the product `∏' k, f (k + i)` tends to one. This does not require a
multipliability assumption on `f`, as otherwise all such products are one. -/
@[to_additive /-- For `f : ℕ → G`, the sum `∑' k, f (k + i)` tends to zero. This does not require a
summability assumption on `f`, as otherwise all such sums are zero. -/]
theorem tendsto_prod_nat_add [T2Space G] (f : ℕ → G) :
    Tendsto (fun i ↦ ∏' k, f (k + i)) atTop (𝓝 1) := by
  by_cases hf : Multipliable f
  · have h₀ : (fun i ↦ (∏' i, f i) / ∏ j ∈ range i, f j) = fun i ↦ ∏' k : ℕ, f (k + i) := by
      ext1 i
      rw [div_eq_iff_eq_mul, mul_comm, hf.prod_mul_tprod_nat_add i]
    have h₁ : Tendsto (fun _ : ℕ ↦ ∏' i, f i) atTop (𝓝 (∏' i, f i)) := tendsto_const_nhds
    simpa only [h₀, div_self'] using Tendsto.div' h₁ hf.hasProd.tendsto_prod_nat
  · refine tendsto_const_nhds.congr fun n ↦ (tprod_eq_one_of_not_multipliable ?_).symm
    rwa [multipliable_nat_add_iff n]

end IsTopologicalGroup

section IsUniformGroup

variable [UniformSpace G] [IsUniformGroup G]

@[to_additive]
theorem cauchySeq_finset_iff_nat_tprod_vanishing {f : ℕ → G} :
    (CauchySeq fun s : Finset ℕ ↦ ∏ n ∈ s, f n) ↔
      ∀ e ∈ 𝓝 (1 : G), ∃ N : ℕ, ∀ t ⊆ {n | N ≤ n}, (∏' n : t, f n) ∈ e := by
  refine cauchySeq_finset_iff_tprod_vanishing.trans ⟨fun vanish e he ↦ ?_, fun vanish e he ↦ ?_⟩
  · obtain ⟨s, hs⟩ := vanish e he
    refine ⟨if h : s.Nonempty then s.max' h + 1 else 0,
      fun t ht ↦ hs _ <| Set.disjoint_left.mpr ?_⟩
    split_ifs at ht with h
    · exact fun m hmt hms ↦ (s.le_max' _ hms).not_gt (Nat.succ_le_iff.mp <| ht hmt)
    · exact fun _ _ hs ↦ h ⟨_, hs⟩
  · obtain ⟨N, hN⟩ := vanish e he
    exact ⟨range N, fun t ht ↦ hN _ fun n hnt ↦
      le_of_not_gt fun h ↦ Set.disjoint_left.mp ht hnt (mem_range.mpr h)⟩

variable [CompleteSpace G]

@[to_additive]
theorem multipliable_iff_nat_tprod_vanishing {f : ℕ → G} : Multipliable f ↔
    ∀ e ∈ 𝓝 1, ∃ N : ℕ, ∀ t ⊆ {n | N ≤ n}, (∏' n : t, f n) ∈ e := by
  rw [multipliable_iff_cauchySeq_finset, cauchySeq_finset_iff_nat_tprod_vanishing]

end IsUniformGroup

section IsTopologicalGroup

variable [TopologicalSpace G] [IsTopologicalGroup G]

@[to_additive]
theorem Multipliable.nat_tprod_vanishing {f : ℕ → G} (hf : Multipliable f) ⦃e : Set G⦄
    (he : e ∈ 𝓝 1) : ∃ N : ℕ, ∀ t ⊆ {n | N ≤ n}, (∏' n : t, f n) ∈ e :=
  letI : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
  have : IsUniformGroup G := isUniformGroup_of_commGroup
  cauchySeq_finset_iff_nat_tprod_vanishing.1 hf.hasProd.cauchySeq e he

@[to_additive]
theorem Multipliable.tendsto_atTop_one {f : ℕ → G} (hf : Multipliable f) :
    Tendsto f atTop (𝓝 1) := by
  rw [← Nat.cofinite_eq_atTop]
  exact hf.tendsto_cofinite_one

end IsTopologicalGroup

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
  refine ⟨u.preimage _ Nat.cast_injective.injOn ∪ u.preimage _ this.injOn,
      fun v' hv' ↦ ⟨v'.image Nat.cast ∪ v'.image Int.negSucc, fun x hx ↦ ?_, ?_⟩⟩
  · simp only [mem_union, mem_image]
    cases x
    · exact Or.inl ⟨_, hv' (by simpa using Or.inl hx), rfl⟩
    · exact Or.inr ⟨_, hv' (by simpa using Or.inr hx), rfl⟩
  · rw [prod_union, prod_image Nat.cast_injective.injOn, prod_image this.injOn,
      prod_mul_distrib]
    simp only [disjoint_iff_ne, mem_image, ne_eq, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, not_false_eq_true, implies_true, reduceCtorEq]

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
  have hi₂ : Injective Int.negSucc := @Int.negSucc.inj
  have : IsCompl (Set.range ((↑) : ℕ → ℤ)) (Set.range Int.negSucc) := by
    constructor
    · rw [disjoint_iff_inf_le]
      rintro _ ⟨⟨i, rfl⟩, ⟨j, ⟨⟩⟩⟩
    · rw [codisjoint_iff_le_sup]
      rintro (i | j) <;> simp
  exact (Nat.cast_injective.hasProd_range_iff.mpr hf₁).mul_isCompl
    this (hi₂.hasProd_range_iff.mpr hf₂)


@[to_additive Summable.of_nat_of_neg_add_one]
lemma Multipliable.of_nat_of_neg_add_one {f : ℤ → M}
    (hf₁ : Multipliable fun n : ℕ ↦ f n) (hf₂ : Multipliable fun n : ℕ ↦ f (-(n + 1))) :
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
@[to_additive /-- If `f₀, f₁, f₂, ...` and `g₀, g₁, g₂, ...` have sums `a`, `b` respectively, then
the `ℤ`-indexed sequence: `..., g₂, g₁, g₀, f₀, f₁, f₂, ...` (with `f₀` at the `0`-th position) has
sum `a + b`. -/]
lemma HasProd.int_rec {f g : ℕ → M} (hf : HasProd f m) (hg : HasProd g m') :
    HasProd (Int.rec f g) (m * m') :=
  HasProd.of_nat_of_neg_add_one hf hg

/-- If `f₀, f₁, f₂, ...` and `g₀, g₁, g₂, ...` are both multipliable then so is the
`ℤ`-indexed sequence: `..., g₂, g₁, g₀, f₀, f₁, f₂, ...` (with `f₀` at the `0`-th position). -/
@[to_additive /-- If `f₀, f₁, f₂, ...` and `g₀, g₁, g₂, ...` are both summable then so is the
`ℤ`-indexed sequence: `..., g₂, g₁, g₀, f₀, f₁, f₂, ...` (with `f₀` at the `0`-th position). -/]
lemma Multipliable.int_rec {f g : ℕ → M} (hf : Multipliable f) (hg : Multipliable g) :
    Multipliable (Int.rec f g) :=
  .of_nat_of_neg_add_one hf hg

/-- If `f₀, f₁, f₂, ...` and `g₀, g₁, g₂, ...` are both multipliable, then the product of the
`ℤ`-indexed sequence: `..., g₂, g₁, g₀, f₀, f₁, f₂, ...` (with `f₀` at the `0`-th position) is
`(∏' n, f n) * ∏' n, g n`. -/
@[to_additive /-- If `f₀, f₁, f₂, ...` and `g₀, g₁, g₂, ...` are both summable, then the sum of the
`ℤ`-indexed sequence: `..., g₂, g₁, g₀, f₀, f₁, f₂, ...` (with `f₀` at the `0`-th position) is
`∑' n, f n + ∑' n, g n`. -/]
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
    simp only [u1, u2, mem_union, mem_image]
    rcases le_total 0 x with (h'x | h'x)
    · refine Or.inl ⟨_, hv' <| mem_image.mpr ⟨x, hx, rfl⟩, ?_⟩
      simp only [Int.natCast_natAbs, abs_eq_self, h'x]
    · refine Or.inr ⟨_, hv' <| mem_image.mpr ⟨x, hx, rfl⟩, ?_⟩
      simp only [abs_of_nonpos h'x, Int.natCast_natAbs, neg_neg]
  exact ⟨_, A, calc
    (∏ x ∈ u1 ∪ u2, (f x * if x = 0 then f 0 else 1)) =
        (∏ x ∈ u1 ∪ u2, f x) * ∏ x ∈ u1 ∩ u2, f x := by
      rw [prod_mul_distrib]
      congr 1
      refine (prod_subset_one_on_sdiff inter_subset_union ?_ ?_).symm
      · intro x hx
        suffices x ≠ 0 by simp only [this, if_false]
        rintro rfl
        simp [u1, u2] at hx
      · intro x hx
        simp only [u1, u2, mem_inter, mem_image] at hx
        suffices x = 0 by simp only [this, if_true]
        lia
    _ = (∏ x ∈ u1, f x) * ∏ x ∈ u2, f x := prod_union_inter
    _ = (∏ b ∈ v', f b) * ∏ b ∈ v', f (-b) := by simp [u1, u2]
    _ = ∏ b ∈ v', (f b * f (-b)) := prod_mul_distrib.symm⟩

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

section IsTopologicalGroup

variable [TopologicalSpace G] [IsTopologicalGroup G]

@[to_additive]
lemma HasProd.of_nat_of_neg {f : ℤ → G} (hf₁ : HasProd (fun n : ℕ ↦ f n) g)
    (hf₂ : HasProd (fun n : ℕ ↦ f (-n)) g') : HasProd f (g * g' / f 0) := by
  refine mul_div_assoc' g .. ▸ hf₁.of_nat_of_neg_add_one (m' := g' / f 0) ?_
  rwa [← hasProd_nat_add_iff' 1, prod_range_one, Nat.cast_zero, neg_zero] at hf₂

@[to_additive]
lemma Multipliable.of_nat_of_neg {f : ℤ → G} (hf₁ : Multipliable fun n : ℕ ↦ f n)
    (hf₂ : Multipliable fun n : ℕ ↦ f (-n)) : Multipliable f :=
  (hf₁.hasProd.of_nat_of_neg hf₂.hasProd).multipliable

@[to_additive]
protected lemma Multipliable.tprod_of_nat_of_neg [T2Space G] {f : ℤ → G}
    (hf₁ : Multipliable fun n : ℕ ↦ f n) (hf₂ : Multipliable fun n : ℕ ↦ f (-n)) :
    ∏' n : ℤ, f n = (∏' n : ℕ, f n) * (∏' n : ℕ, f (-n)) / f 0 :=
  (hf₁.hasProd.of_nat_of_neg hf₂.hasProd).tprod_eq

end IsTopologicalGroup

section IsUniformGroup -- results which depend on completeness

variable [UniformSpace G] [IsUniformGroup G] [CompleteSpace G]

/-- "iff" version of `Multipliable.of_nat_of_neg_add_one`. -/
@[to_additive /-- "iff" version of `Summable.of_nat_of_neg_add_one`. -/]
lemma multipliable_int_iff_multipliable_nat_and_neg_add_one {f : ℤ → G} : Multipliable f ↔
    (Multipliable fun n : ℕ ↦ f n) ∧ (Multipliable fun n : ℕ ↦ f (-(n + 1))) := by
  refine ⟨fun p ↦ ⟨?_, ?_⟩, fun ⟨hf₁, hf₂⟩ ↦ Multipliable.of_nat_of_neg_add_one hf₁ hf₂⟩ <;>
  apply p.comp_injective
  exacts [Nat.cast_injective, @Int.negSucc.inj]

/-- "iff" version of `Multipliable.of_nat_of_neg`. -/
@[to_additive /-- "iff" version of `Summable.of_nat_of_neg`. -/]
lemma multipliable_int_iff_multipliable_nat_and_neg {f : ℤ → G} :
    Multipliable f ↔ (Multipliable fun n : ℕ ↦ f n) ∧ (Multipliable fun n : ℕ ↦ f (-n)) := by
  refine ⟨fun p ↦ ⟨?_, ?_⟩, fun ⟨hf₁, hf₂⟩ ↦ Multipliable.of_nat_of_neg hf₁ hf₂⟩ <;>
  apply p.comp_injective
  exacts [Nat.cast_injective, neg_injective.comp Nat.cast_injective]

-- We're not really using the ring structure here:
-- we only use multiplication by `-1`, so perhaps this can be generalised further.
theorem Summable.alternating {α} [Ring α]
    [UniformSpace α] [IsUniformAddGroup α] [CompleteSpace α] {f : ℕ → α} (hf : Summable f) :
    Summable (fun n => (-1) ^ n * f n) := by
  apply Summable.even_add_odd
  · simp only [even_two, Even.mul_right, Even.neg_pow, one_pow, one_mul]
    exact hf.comp_injective (mul_right_injective₀ (two_ne_zero' ℕ))
  · simp only [pow_add, even_two, Even.mul_right, Even.neg_pow, one_pow, pow_one, mul_neg, mul_one,
      neg_mul, one_mul]
    apply Summable.neg
    apply hf.comp_injective
    exact (add_left_injective 1).comp (mul_right_injective₀ (two_ne_zero' ℕ))

end IsUniformGroup

end Int

section PNat

@[to_additive]
theorem multipliable_pnat_iff_multipliable_succ {f : ℕ → M} :
    Multipliable (fun x : ℕ+ ↦ f x) ↔ Multipliable fun x ↦ f (x + 1) :=
  Equiv.pnatEquivNat.symm.multipliable_iff.symm

@[to_additive]
lemma multipliable_pnat_iff_multipliable_nat [TopologicalSpace G] [IsTopologicalGroup G]
    {f : ℕ → G} : Multipliable (fun n : ℕ+ ↦ f n) ↔ Multipliable f := by
  rw [multipliable_pnat_iff_multipliable_succ, multipliable_nat_add_iff]

@[to_additive]
theorem tprod_pnat_eq_tprod_succ {f : ℕ → M} : ∏' n : ℕ+, f n = ∏' n, f (n + 1) :=
  (Equiv.pnatEquivNat.symm.tprod_eq _).symm

@[to_additive]
lemma tprod_zero_pnat_eq_tprod_nat [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    {f : ℕ → G} (hf : Multipliable f) :
    f 0 * ∏' n : ℕ+, f ↑n = ∏' n, f n := by
  simpa [hf.tprod_eq_zero_mul] using tprod_pnat_eq_tprod_succ

@[to_additive]
theorem tprod_int_eq_zero_mul_tprod_pnat [UniformSpace G] [IsUniformGroup G] [CompleteSpace G]
    [T2Space G] {f : ℤ → G} (hf2 : Multipliable f) :
    ∏' n, f n = f 0 * (∏' n : ℕ+, f n) * (∏' n : ℕ+, f (-n)) := by
  have h1 : Multipliable fun n : ℕ ↦ f n :=
    (multipliable_int_iff_multipliable_nat_and_neg.mp hf2).1
  have h2 : Multipliable fun n : ℕ ↦ f (-n) :=
    (multipliable_int_iff_multipliable_nat_and_neg.mp hf2).2
  have h3 : Multipliable fun n : ℕ+ ↦ f n := by
    rwa [multipliable_pnat_iff_multipliable_succ (f := (f ·)),
      multipliable_nat_add_iff 1 (f := (f ·))]
  have h4 : Multipliable fun n : ℕ+ ↦ f (-n) := by
    rwa [multipliable_pnat_iff_multipliable_succ (f := (fun x ↦ f (-x))),
      multipliable_nat_add_iff 1 (f := (fun x ↦ f (-x)))]
  have := tprod_nat_mul_neg hf2
  simp only [← tprod_zero_pnat_eq_tprod_nat (by simpa using h1.mul h2), Nat.cast_zero, neg_zero,
    mul_comm _ (f 0), mul_assoc, mul_right_inj] at this
  simp [← this, h3.tprod_mul h4, ← mul_assoc]

@[to_additive tsum_int_eq_zero_add_two_mul_tsum_pnat]
theorem tprod_int_eq_zero_mul_tprod_pnat_sq [UniformSpace G] [IsUniformGroup G] [CompleteSpace G]
    [T2Space G] {f : ℤ → G} (hf : f.Even) (hf2 : Multipliable f) :
    ∏' n, f n = f 0 * (∏' n : ℕ+, f n) ^ 2 := by
  simpa only [sq, ← mul_assoc, hf _] using tprod_int_eq_zero_mul_tprod_pnat hf2

end PNat
