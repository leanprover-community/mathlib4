/-
Copyright (c) 2024 Mitchell Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Lee
-/
module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Topology.Algebra.InfiniteSum.GroupCompletion
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Topology.Algebra.Nonarchimedean.Completion

/-!
# Infinite sums and products in nonarchimedean abelian groups

Let `G` be a complete nonarchimedean abelian group and let `f : α → G` be a function. We prove that
`f` is unconditionally summable if and only if `f a` tends to zero on the cofinite filter on `α`
(`NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero`). We also prove the analogous result in
the multiplicative setting (`NonarchimedeanGroup.multipliable_iff_tendsto_cofinite_one`).

We also prove that multiplication distributes over arbitrarily indexed sums in a nonarchimedean
ring. That is, let `R` be a nonarchimedean ring, let `f : α → R` be a function that sums to `a : R`,
and let `g : β → R` be a function that sums to `b : R`. Then `fun (i : α × β) ↦ (f i.1) * (g i.2)`
sums to `a * b` (`HasSum.mul_of_nonarchimedean`).

-/
set_option backward.defeqAttrib.useBackward true

public section

open Filter Topology

namespace NonarchimedeanGroup

variable {α G : Type*}
variable [CommGroup G] [UniformSpace G] [IsUniformGroup G] [NonarchimedeanGroup G]

/-- Let `G` be a nonarchimedean multiplicative abelian group, and let `f : α → G` be a function that
tends to one on the filter of cofinite sets. For each finite subset of `α`, consider the partial
product of `f` on that subset. These partial products form a Cauchy filter. -/
@[to_additive /-- Let `G` be a nonarchimedean additive abelian group, and let `f : α → G` be a
function that tends to zero on the filter of cofinite sets. For each finite subset of `α`, consider
the partial sum of `f` on that subset. These partial sums form a Cauchy filter. -/]
theorem cauchySeq_prod_of_tendsto_cofinite_one {f : α → G} (hf : Tendsto f cofinite (𝓝 1)) :
    CauchySeq (fun s ↦ ∏ i ∈ s, f i) := by
  /- Let `U` be a neighborhood of `1`. It suffices to show that there exists `s : Finset α` such
  that for any `t : Finset α` disjoint from `s`, we have `∏ i ∈ t, f i ∈ U`. -/
  apply cauchySeq_finset_iff_prod_vanishing.mpr
  intro U hU
  -- Since `G` is nonarchimedean, `U` contains an open subgroup `V`.
  rcases is_nonarchimedean U hU with ⟨V, hV⟩
  /- Let `s` be the set of all indices `i : α` such that `f i ∉ V`. By our assumption `hf`, this is
  finite. -/
  use (tendsto_def.mp hf V V.mem_nhds_one).toFinset
  /- For any `t : Finset α` disjoint from `s`, the product `∏ i ∈ t, f i` is a product of elements
  of `V`, so it is an element of `V` too. Thus, `∏ i ∈ t, f i ∈ U`, as desired. -/
  intro t ht
  apply hV
  apply Subgroup.prod_mem
  intro i hi
  simpa using Finset.disjoint_left.mp ht hi

/-- Let `G` be a nonarchimedean abelian group, and let `f : ℕ → G` be a function
such that the quotients `f (n + 1) / f n` tend to one. Then the function is a Cauchy sequence. -/
@[to_additive /-- Let `G` be a nonarchimedean additive abelian group, and let `f : ℕ → G` be a
function such that the differences `f (n + 1) - f n` tend to zero.
Then the function is a Cauchy sequence. -/]
lemma cauchySeq_of_tendsto_div_nhds_one {f : ℕ → G}
    (hf : Tendsto (fun n ↦ f (n + 1) / f n) atTop (𝓝 1)) :
    CauchySeq f := by
  suffices Tendsto (fun p : ℕ × ℕ ↦ f p.2 / f p.1) atTop (𝓝 1) by simpa [CauchySeq,
      cauchy_map_iff, prod_atTop_atTop_eq, uniformity_eq_comap_nhds_one G, atTop_neBot]
  rw [tendsto_atTop']
  intro s hs
  obtain ⟨t, ht⟩ := is_nonarchimedean s hs
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ b, N ≤ b → f (b + 1) / f b ∈ t := by
    simpa using tendsto_def.mp hf t t.mem_nhds_one
  refine ⟨(N, N), ?_⟩
  rintro ⟨M, M'⟩ ⟨(hMN : N ≤ M), (hMN' : N ≤ M')⟩
  apply ht
  wlog h : M ≤ M' generalizing M M'
  · simpa [inv_div] using t.inv_mem <| this _ _ hMN' hMN (le_of_not_ge h)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h hMN'
  induction k with
  | zero => simp
  | succ k ih => simpa using t.mul_mem (hN _ (by lia : N ≤ M + k)) ih

/-- Let `G` be a complete nonarchimedean multiplicative abelian group, and let `f : α → G` be a
function that tends to one on the filter of cofinite sets. Then `f` is unconditionally
multipliable. -/
@[to_additive /-- Let `G` be a complete nonarchimedean additive abelian group, and let `f : α → G`
be a function that tends to zero on the filter of cofinite sets. Then `f` is unconditionally
summable. -/]
theorem multipliable_of_tendsto_cofinite_one [CompleteSpace G] {f : α → G}
    (hf : Tendsto f cofinite (𝓝 1)) : Multipliable f :=
  CompleteSpace.complete (cauchySeq_prod_of_tendsto_cofinite_one hf)

/-- Let `G` be a complete nonarchimedean multiplicative abelian group. Then a function `f : α → G`
is unconditionally multipliable if and only if it tends to one on the filter of cofinite sets. -/
@[to_additive /-- Let `G` be a complete nonarchimedean additive abelian group. Then a function
`f : α → G` is unconditionally summable if and only if it tends to zero on the filter of cofinite
sets. -/]
theorem multipliable_iff_tendsto_cofinite_one [CompleteSpace G] (f : α → G) :
    Multipliable f ↔ Tendsto f cofinite (𝓝 1) :=
  ⟨Multipliable.tendsto_cofinite_one, multipliable_of_tendsto_cofinite_one⟩

end NonarchimedeanGroup

section NonarchimedeanRing

variable {α β R : Type*}
variable [Ring R] [UniformSpace R] [IsUniformAddGroup R] [NonarchimedeanRing R]

/- Let `R` be a complete nonarchimedean ring. If functions `f : α → R` and `g : β → R` are summable,
then so is `fun i : α × β ↦ f i.1 * g i.2`. We will prove later that the assumption that `R`
is complete is not necessary. -/
private theorem Summable.mul_of_complete_nonarchimedean [CompleteSpace R] {f : α → R} {g : β → R}
    (hf : Summable f) (hg : Summable g) : Summable (fun i : α × β ↦ f i.1 * g i.2) := by
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero] at *
  exact tendsto_mul_cofinite_nhds_zero hf hg

/-- Let `R` be a nonarchimedean ring, let `f : α → R` be a function that sums to `a : R`,
and let `g : β → R` be a function that sums to `b : R`. Then `fun i : α × β ↦ f i.1 * g i.2`
sums to `a * b`. -/
theorem HasSum.mul_of_nonarchimedean {f : α → R} {g : β → R} {a b : R} (hf : HasSum f a)
    (hg : HasSum g b) : HasSum (fun i : α × β ↦ f i.1 * g i.2) (a * b) := by
  rw [← hasSum_iff_hasSum_compl] at *
  simp only [Function.comp_def, UniformSpace.Completion.toCompl_apply,
    UniformSpace.Completion.coe_mul]
  exact (hf.mul hg) (hf.summable.mul_of_complete_nonarchimedean hg.summable :)

/-- Let `R` be a nonarchimedean ring. If functions `f : α → R` and `g : β → R` are summable, then
so is `fun i : α × β ↦ f i.1 * g i.2`. -/
theorem Summable.mul_of_nonarchimedean {f : α → R} {g : β → R} (hf : Summable f)
    (hg : Summable g) : Summable (fun i : α × β ↦ f i.1 * g i.2) :=
  (hf.hasSum.mul_of_nonarchimedean hg.hasSum).summable

theorem tsum_mul_tsum_of_nonarchimedean [T0Space R] {f : α → R} {g : β → R} (hf : Summable f)
    (hg : Summable g) : (∑' i, f i) * (∑' i, g i) = ∑' i : α × β, f i.1 * g i.2 :=
  (hf.hasSum.mul_of_nonarchimedean hg.hasSum).tsum_eq.symm

end NonarchimedeanRing
