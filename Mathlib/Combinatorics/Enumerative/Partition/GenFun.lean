/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.RingTheory.PowerSeries.PiTopology

/-!
# Generating functions for partitions

This file defines generating functions related to partitions. Given a character function $f(i, c)$
of a part $i$ and the number of occurrences of the part $c$, the related generating function is
$$
G_f(X) = \sum_{n = 0}^{\infty} \left(\sum_{p \in P_{n}} \prod_{i \in p} f(i, \#i)\right) X^n
= \prod_{i = 1}^{\infty}\left(1 + \sum_{j = 1}^{\infty} f(i, j) X^{ij}\right)
$$
where $P_n$ is all partitions of $n$, $\#i$ is the count of $i$ in the partition $p$.
We give the definition `Nat.Partition.genFun` using the first equation, and prove the second
equation in `Nat.Partition.hasProd_genFun` (with shifted indices).

This generating function can be specialized to
* When $f(i, c) = 1$, this is the generating function for partition function $p(n)$.
* When $f(i, 1) = 1$ and $f(i, c) = 0$ for $c > 1$, this is the generating function for
    `#(Nat.Partition.distincts n)`.
* When $f(i, c) = 1$ for odd $i$ and $f(i, c) = 0$ for even $i$, this is the generating function for
    `#(Nat.Partition.odds n)`.
(TODO: prove these)

The definition of `Nat.Partition.genFun` ignores the value of $f(0, c)$ and $f(i, 0)$. The formula
can be interpreted as assuming $f(i, 0) = 1$ and $f(0, c) = 0$ for $c \ne 0$. In theory we could
respect the actual value of $f(0, c)$ and $f(i, 0)$, but it makes the otherwise finite sum and
product potentially infinite.
-/

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace Nat.Partition
variable {M : Type*} [CommSemiring M]

/-- Convert a `Partition n` to a member of `(Finset.Icc 1 n).finsuppAntidiag n`
(see `Nat.Partition.range_toFinsuppAntidiag` for the proof).
`p.toFinsuppAntidiag i` is defined as `i` times the number of occurrence of `i` in `p`. -/
def toFinsuppAntidiag {n : ℕ} (p : Partition n) : ℕ →₀ ℕ where
  toFun m := p.parts.count m * m
  support := p.parts.toFinset
  mem_support_toFun m := by
    suffices m ∈ p.parts → m ≠ 0 by simpa
    grind [→ parts_pos]

theorem toFinsuppAntidiag_injective (n : ℕ) :
    Function.Injective (toFinsuppAntidiag (n := n)) := by
  unfold toFinsuppAntidiag
  intro p q h
  rw [Finsupp.mk.injEq] at h
  obtain ⟨hfinset, hcount⟩ := h
  rw [Nat.Partition.ext_iff, Multiset.ext]
  intro m
  obtain rfl | h0 := Nat.eq_zero_or_pos m
  · grind [Multiset.count_eq_zero, → parts_pos]
  · exact Nat.eq_of_mul_eq_mul_right h0 <| funext_iff.mp hcount m

theorem range_toFinsuppAntidiag (n : ℕ) :
    Set.range (toFinsuppAntidiag (n := n)) ⊆ (Finset.Icc 1 n).finsuppAntidiag n := by
  unfold toFinsuppAntidiag
  rw [Set.range_subset_iff]
  intro p
  have hp : p.parts.toFinset ⊆ Finset.Icc 1 n := by
    grind [Multiset.mem_toFinset, Finset.mem_Icc, → parts_pos]
  suffices ∑ m ∈ Finset.Icc 1 n, Multiset.count m p.parts * m = n by simpa [hp]
  convert ← p.parts_sum
  rw [Finset.sum_multiset_count]
  apply Finset.sum_subset hp
  suffices ∀ (x : ℕ), 1 ≤ x → x ≤ n → x ∉ p.parts → x ∉ p.parts ∨ x = 0 by simpa
  grind [→ parts_pos]

/-- Generating function associated with character $f(i, c)$ for partition functions, where $i$ is a
part of the partition, and $c$ is the count of that part in the partition. The character function is
multiplied within one `n.Partition`, and summed among all `n.Partition` for a fixed `n`. This way,
each `n` is assigned a value, which we use as the coefficients of the power series. -/
def genFun (f : ℕ → ℕ → M) : M⟦X⟧ :=
  PowerSeries.mk fun n ↦ ∑ p : n.Partition, ∏ i ∈ p.parts.toFinset, f i (p.parts.count i)

variable [TopologicalSpace M]

/-- The infinite sum in the formula `Nat.Partition.hasProd_genFun` always converges. -/
theorem summable_genFun_term (f : ℕ → ℕ → M) (i : ℕ) :
    Summable fun j ↦ f (i + 1) (j + 1) • (X : M⟦X⟧) ^ ((i + 1) * (j + 1)) := by
  rcases subsingleton_or_nontrivial M with h | h
  · simpa [Subsingleton.eq_zero] using summable_zero
  apply WithPiTopology.summable_of_tendsto_order_atTop_nhds_top
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr (fun n ↦ Filter.eventually_atTop.mpr ⟨n, ?_⟩)
  intro m hm
  grw [PowerSeries.smul_eq_C_mul, ← le_order_mul]
  refine lt_add_of_nonneg_of_lt (by simp) ?_
  rw [order_X_pow]
  norm_cast
  grind

/-- Alternative form of `summable_genFun_term` that unshifts the first index. -/
theorem summable_genFun_term' (f : ℕ → ℕ → M) {i : ℕ} (hi : i ≠ 0) :
    Summable fun j ↦ f i (j + 1) • (X : M⟦X⟧) ^ (i * (j + 1)) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hi
  apply summable_genFun_term

variable [T2Space M]

private theorem aux_dvd_of_coeff_ne_zero {f : ℕ → ℕ → M} {d : ℕ} {s : Finset ℕ} (hs0 : 0 ∉ s)
    {g : ℕ →₀ ℕ} (hg : g ∈ s.finsuppAntidiag d)
    (hprod : ∀ i ∈ s, (coeff (g i)) (1 + ∑' j, f i (j + 1) • X ^ (i * (j + 1))) ≠ (0 : M))
    (x : ℕ) : x ∣ g x := by
  by_cases hx : x ∈ s
  · specialize hprod x hx
    contrapose! hprod
    have hx0 : x ≠ 0 := fun h ↦ hs0 (h ▸ hx)
    rw [map_add, (summable_genFun_term' f hx0).map_tsum _ (WithPiTopology.continuous_coeff _ _)]
    rw [show (0 : M) = 0 + ∑' (i : ℕ), 0 by simp]
    congrm (?_ + ∑' (i : ℕ), ?_)
    · suffices g x ≠ 0 by simp [this]
      contrapose! hprod
      simp [hprod]
    · rw [map_smul, coeff_X_pow]
      apply smul_eq_zero_of_right
      suffices g x ≠ x * (i + 1) by simp [this]
      contrapose! hprod
      simp [hprod]
  · suffices g x = 0 by simp [this]
    contrapose! hx
    exact Finset.mem_of_subset (Finset.mem_finsuppAntidiag.mp hg).2 <| by simpa using hx

private theorem aux_prod_coeff_eq_zero_of_notMem_range (f : ℕ → ℕ → M) {d : ℕ} {s : Finset ℕ}
    (hs0 : 0 ∉ s) {g : ℕ →₀ ℕ} (hg : g ∈ s.finsuppAntidiag d)
    (hg' : g ∉ Set.range (toFinsuppAntidiag (n := d))) :
    ∏ i ∈ s, (coeff (g i)) (1 + ∑' j, f i (j + 1) • X ^ (i * (j + 1)) : M⟦X⟧) = 0 := by
  suffices ∃ i ∈ s, (coeff (g i)) ((1 : M⟦X⟧) + ∑' j, f i (j + 1) • X ^ (i * (j + 1))) = 0 by
    obtain ⟨i, hi, hi'⟩ := this
    apply Finset.prod_eq_zero hi hi'
  contrapose! hg' with hprod
  rw [Set.mem_range]
  have hgne0 (i : ℕ) : g i ≠ 0 ↔ i ≠ 0 ∧ i ≤ g i := by
    refine ⟨fun h ↦ ⟨?_, ?_⟩, by grind⟩
    · contrapose! hs0 with rfl
      exact Finset.mem_of_subset (Finset.mem_finsuppAntidiag.mp hg).2 (by simpa using h)
    · exact Nat.le_of_dvd (Nat.pos_of_ne_zero h) <| aux_dvd_of_coeff_ne_zero hs0 hg hprod _
  refine ⟨Nat.Partition.mk (Finsupp.mk g.support (fun i ↦ g i / i) ?_).toMultiset ?_ ?_, ?_⟩
  · simpa using hgne0
  · suffices ∀ i, g i ≠ 0 → i ≠ 0 by simpa [Nat.pos_iff_ne_zero]
    exact fun i h ↦ ((hgne0 i).mp h).1
  · obtain ⟨h1, h2⟩ := Finset.mem_finsuppAntidiag.mp hg
    refine Eq.trans ?_ h1
    suffices ∑ x ∈ g.support, g x / x * x = ∑ x ∈ s, g x by simpa [Finsupp.sum]
    apply Finset.sum_subset_zero_on_sdiff h2 (by simp)
    exact fun x hx ↦ Nat.div_mul_cancel <| aux_dvd_of_coeff_ne_zero hs0 hg hprod x
  · ext x
    simpa [toFinsuppAntidiag] using Nat.div_mul_cancel <| aux_dvd_of_coeff_ne_zero hs0 hg hprod x

private theorem aux_prod_f_eq_prod_coeff (f : ℕ → ℕ → M) {n : ℕ} (p : Partition n) {s : Finset ℕ}
    (hs : Finset.Icc 1 n ⊆ s) (hs0 : 0 ∉ s) :
    ∏ i ∈ p.parts.toFinset, f i (Multiset.count i p.parts) =
    ∏ i ∈ s, coeff (p.toFinsuppAntidiag i) (1 + ∑' j, f i (j + 1) • X ^ (i * (j + 1))) := by
  apply Finset.prod_subset_one_on_sdiff
  · grind [Multiset.mem_toFinset, Finset.mem_Icc, → parts_pos]
  · intro x hx
    rw [Finset.mem_sdiff, Multiset.mem_toFinset] at hx
    have hx0 : x ≠ 0 := fun h ↦ hs0 (h ▸ hx.1)
    have hsum := (summable_genFun_term' f hx0).map_tsum _
      (WithPiTopology.continuous_constantCoeff M)
    simp [toFinsuppAntidiag, hsum, hx.2, hx0]
  · intro i hi
    rw [Multiset.mem_toFinset] at hi
    have hi0 : i ≠ 0 := (p.parts_pos hi).ne.symm
    rw [map_add, (summable_genFun_term' f hi0).map_tsum _ (WithPiTopology.continuous_coeff _ _)]
    suffices f i (Multiset.count i p.parts) =
        ∑' j, if Multiset.count i p.parts * i = i * (j + 1) then f i (j + 1) else 0 by
      simpa [toFinsuppAntidiag, hi, hi0, coeff_X_pow]
    rw [tsum_eq_single (Multiset.count i p.parts - 1) ?_]
    · rw [mul_comm]
      simp [Nat.sub_add_cancel (Multiset.one_le_count_iff_mem.mpr hi)]
    intro b hb
    suffices Multiset.count i p.parts * i ≠ i * (b + 1) by simp [this]
    rw [mul_comm i, (mul_left_inj' (Nat.ne_zero_of_lt (p.parts_pos hi))).ne]
    grind

theorem hasProd_genFun (f : ℕ → ℕ → M) :
    HasProd (fun i ↦ 1 + ∑' j, f (i + 1) (j + 1) • X ^ ((i + 1) * (j + 1))) (genFun f) := by
  rw [HasProd, WithPiTopology.tendsto_iff_coeff_tendsto]
  refine fun d ↦ tendsto_atTop_of_eventually_const (fun s (hs : s ≥ Finset.range d) ↦ ?_)
  have : ∏ i ∈ s, ((1 : M⟦X⟧) + ∑' j, f (i + 1) (j + 1) • X ^ ((i + 1) * (j + 1)))
      = ∏ i ∈ s.map (addRightEmbedding 1), (1 + ∑' j, f i (j + 1) • X ^ (i * (j + 1))) := by
    simp
  rw [this]
  have hs : Finset.Icc 1 d ⊆ s.map (addRightEmbedding 1) := by
    intro i
    suffices 1 ≤ i → i ≤ d → ∃ a ∈ s, a + 1 = i by simpa
    intro h1 h2
    refine ⟨i - 1, Finset.mem_of_subset hs ?_, ?_⟩ <;> grind
  rw [genFun, coeff_mk, coeff_prod]
  refine (Finset.sum_of_injOn toFinsuppAntidiag (toFinsuppAntidiag_injective d).injOn ?_ ?_ ?_).symm
  · refine (Set.mapsTo_range _ _).mono_right ((range_toFinsuppAntidiag d).trans ?_)
    simpa using Finset.finsuppAntidiag_mono hs.le _
  · exact fun g hg hg' ↦ aux_prod_coeff_eq_zero_of_notMem_range f (by simp) hg (by simpa using hg')
  · exact fun p _ ↦ aux_prod_f_eq_prod_coeff f p hs.le (by simp)

end Nat.Partition
