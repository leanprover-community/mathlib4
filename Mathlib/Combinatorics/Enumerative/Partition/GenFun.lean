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

variable [T2Space M]

private theorem aux_injOn_sub_one_parts {n : ℕ} (p : Partition n) :
    Set.InjOn (fun x ↦ x - 1) p.parts.toFinset := by
  intro a ha b hb
  exact tsub_inj_left (p.parts_pos (by simpa using ha)) (p.parts_pos (by simpa using hb))

private theorem aux_map_sub_one_parts_subset {n : ℕ} (p : Partition n) :
    (Multiset.map (fun x ↦ x - 1) p.parts).toFinset ⊆ Finset.range n := by
  intro m
  rw [Multiset.mem_toFinset, Finset.mem_range]
  suffices ∀ x ∈ p.parts, x - 1 = m → m < n by simpa
  rintro x h1 rfl
  exact Nat.sub_one_lt_of_le (p.parts_pos h1) (le_of_mem_parts h1)

private theorem aux_mapsTo_sub_one_parts {n : ℕ} (p : Partition n) :
    Set.MapsTo (fun x ↦ x - 1) p.parts.toFinset (Finset.range n) := by
  intro a ha
  apply Finset.mem_of_subset (aux_map_sub_one_parts_subset p)
  rw [Multiset.mem_toFinset, Multiset.mem_map]
  exact ⟨a, by simpa using ha⟩

private def toFinsuppAntidiag {n : ℕ} (p : Partition n) : ℕ →₀ ℕ where
  toFun m := p.parts.count (m + 1) * (m + 1)
  support := (p.parts.map (· - 1)).toFinset
  mem_support_toFun m := by
    suffices (∃ a ∈ p.parts, a - 1 = m) ↔ m + 1 ∈ p.parts by simpa
    grind [→ Partition.parts_pos]

private theorem aux_toFinsuppAntidiag_injective (n : ℕ) :
    Function.Injective (toFinsuppAntidiag (n := n)) := by
  unfold toFinsuppAntidiag
  intro p q h
  rw [Finsupp.mk.injEq] at h
  obtain ⟨hfinset, hcount⟩ := h
  rw [Nat.Partition.ext_iff, Multiset.ext]
  intro m
  obtain rfl | h0 := Nat.eq_zero_or_pos m
  · trans 0
    · rw [Multiset.count_eq_zero]
      exact fun h ↦ lt_irrefl _ <| p.parts_pos h
    · symm
      rw [Multiset.count_eq_zero]
      exact fun h ↦ lt_irrefl _ <| q.parts_pos h
  · refine Nat.eq_of_mul_eq_mul_right h0 <| ?_
    convert funext_iff.mp hcount (m - 1) <;> exact (Nat.sub_eq_iff_eq_add h0).mp rfl

private theorem aux_range_toFinsuppAntidiag (n : ℕ) :
    Set.range (toFinsuppAntidiag (n := n)) ⊆ (Finset.range n).finsuppAntidiag n := by
  unfold toFinsuppAntidiag
  rw [Set.range_subset_iff]
  intro p
  suffices ∑ m ∈ Finset.range n, Multiset.count (m + 1) p.parts * (m + 1) = n by
    simpa [aux_map_sub_one_parts_subset p]
  refine Eq.trans ?_ p.parts_sum
  simp_rw [Finset.sum_multiset_count, smul_eq_mul]
  refine (Finset.sum_of_injOn (· - 1) (aux_injOn_sub_one_parts p)
    (aux_mapsTo_sub_one_parts p) ?_ ?_).symm
  · suffices ∀ i ∈ Finset.range n, (∀ x ∈ p.parts, x - 1 ≠ i) → i + 1 ∉ p.parts by simpa
    intro i hi h
    contrapose! h
    exact ⟨i + 1, by simpa using h⟩
  · intro i hi
    suffices i - 1 + 1 = i by simp [this]
    rw [Nat.sub_add_cancel (Nat.one_le_of_lt (p.parts_pos (by simpa using hi)))]

private theorem aux_dvd_of_coeff_ne_zero {f : ℕ → ℕ → M} {d : ℕ} {s : Finset ℕ}
    {g : ℕ →₀ ℕ} (hg : g ∈ s.finsuppAntidiag d)
    (hprod : ∀ x ∈ s,
      (coeff (g x)) (1 + ∑' (j : ℕ), f (x + 1) (j + 1) • X ^ ((x + 1) * (j + 1))) ≠ (0 : M))
    (x : ℕ) : x + 1 ∣ g x := by
  by_cases hx : x ∈ s
  · specialize hprod x hx
    contrapose! hprod
    rw [map_add, (summable_genFun_term f x).map_tsum _ (WithPiTopology.continuous_coeff _ _)]
    rw [show (0 : M) = 0 + ∑' (i : ℕ), 0 by simp]
    congrm (?_ + ∑' (i : ℕ), ?_)
    · suffices g x ≠ 0 by simp [this]
      contrapose! hprod
      simp [hprod]
    · rw [map_smul, coeff_X_pow]
      apply smul_eq_zero_of_right
      suffices g x ≠ (x + 1) * (i + 1) by simp [this]
      contrapose! hprod
      simp [hprod]
  · suffices g x = 0 by simp [this]
    contrapose! hx
    exact Finset.mem_of_subset (Finset.mem_finsuppAntidiag.mp hg).2 <| by simpa using hx

private theorem aux_prod_coeff_eq_zero_of_notMem_range (f : ℕ → ℕ → M) {d : ℕ} {s : Finset ℕ}
    {g : ℕ →₀ ℕ} (hg : g ∈ s.finsuppAntidiag d)
    (hg' : g ∉ Set.range (toFinsuppAntidiag (n := d))) :
    ∏ i ∈ s, (coeff (g i)) (1 + ∑' (j : ℕ),
    f (i + 1) (j + 1) • X ^ ((i + 1) * (j + 1)) : M⟦X⟧) = 0 := by
  suffices ∃ i ∈ s, (coeff (g i)) ((1 : M⟦X⟧) +
      ∑' (j : ℕ), f (i + 1) (j + 1) • X ^ ((i + 1) * (j + 1))) = 0 by
    obtain ⟨i, hi, hi'⟩ := this
    apply Finset.prod_eq_zero hi hi'
  contrapose! hg' with hprod
  rw [Set.mem_range]
  refine ⟨Nat.Partition.mk (Finsupp.toMultiset
    (Finsupp.mk (g.support.map (Function.Embedding.mk (· + 1) (add_left_injective 1)))
    (fun i ↦ if i = 0 then 0 else g (i - 1) / i) ?_)) (by simp) ?_, ?_⟩
  · intro a
    suffices (∃ b, g b ≠ 0 ∧ b + 1 = a) ↔ a ≠ 0 ∧ a ≤ g (a - 1) by simpa
    constructor
    · rintro ⟨b, h1, rfl⟩
      simpa using Nat.le_of_dvd (Nat.pos_of_ne_zero h1) <| aux_dvd_of_coeff_ne_zero hg hprod b
    · rintro ⟨h1, h2⟩
      exact ⟨a - 1, by grind⟩
  · obtain ⟨h1, h2⟩ := Finset.mem_finsuppAntidiag.mp hg
    refine Eq.trans ?_ h1
    suffices ∑ x ∈ g.support, g x / (x + 1) * (x + 1) = ∑ x ∈ s, g x by simpa [Finsupp.sum]
    rw [Finset.sum_subset h2 (by
      intro x _
      suffices g x = 0 → g x < x + 1 by simpa;
      grind)]
    exact Finset.sum_congr rfl fun x _ ↦ Nat.div_mul_cancel <| aux_dvd_of_coeff_ne_zero hg hprod x
  · ext x
    simpa [toFinsuppAntidiag] using Nat.div_mul_cancel <| aux_dvd_of_coeff_ne_zero hg hprod x

private theorem aux_prod_f_eq_prod_coeff
    (f : ℕ → ℕ → M) {n : ℕ} (p : Partition n) {s : Finset ℕ} (hs : Finset.range n ≤ s) :
    ∏ i ∈ p.parts.toFinset, f i (Multiset.count i p.parts) =
    ∏ i ∈ s, coeff (p.toFinsuppAntidiag i)
    (1 + ∑' j : ℕ, f (i + 1) (j + 1) • X ^ ((i + 1) * (j + 1))) := by
  refine Finset.prod_of_injOn (· - 1) (aux_injOn_sub_one_parts _)
    ((aux_mapsTo_sub_one_parts p).mono_right hs) ?_ ?_
  · intro x hx h
    have hx : x + 1 ∉ p.parts := by
      contrapose! h
      exact ⟨x + 1, by simpa using h⟩
    have hsum := (summable_genFun_term f x).map_tsum _ (WithPiTopology.continuous_constantCoeff M)
    simp [toFinsuppAntidiag, hx, hsum]
  · intro i hi
    have hi : i ∈ p.parts := by simpa using hi
    rw [map_add, (summable_genFun_term f _).map_tsum _ (WithPiTopology.continuous_coeff _ _)]
    suffices f i (Multiset.count i p.parts) =
      ∑' j : ℕ, if Multiset.count i p.parts * i = i * (j + 1) then f i (j + 1) else 0 by
      simpa [Nat.one_le_of_lt (p.parts_pos hi), toFinsuppAntidiag, hi,
        Nat.ne_zero_of_lt (p.parts_pos hi), coeff_X_pow]
    rw [tsum_eq_single (Multiset.count i p.parts - 1) ?_]
    · rw [mul_comm]
      simp [Nat.sub_add_cancel (Multiset.one_le_count_iff_mem.mpr hi)]
    intro b hb
    suffices Multiset.count i p.parts * i ≠ i * (b + 1) by simp [this]
    rw [mul_comm i, (mul_left_inj' (Nat.ne_zero_of_lt (p.parts_pos hi))).ne]
    grind

theorem hasProd_genFun (f : ℕ → ℕ → M) :
    HasProd (fun i ↦ (1 : M⟦X⟧) + ∑' j : ℕ, f (i + 1) (j + 1) • X ^ ((i + 1) * (j + 1)))
    (genFun f) := by
  rw [HasProd, WithPiTopology.tendsto_iff_coeff_tendsto]
  refine fun d ↦ tendsto_atTop_of_eventually_const (fun s (hs : s ≥ Finset.range d) ↦ ?_)
  rw [genFun, coeff_mk, coeff_prod]
  refine (Finset.sum_of_injOn toFinsuppAntidiag
    (aux_toFinsuppAntidiag_injective d).injOn ?_ ?_ ?_).symm
  · refine (Set.mapsTo_range _ _).mono_right ((aux_range_toFinsuppAntidiag d).trans ?_)
    simpa using Finset.finsuppAntidiag_mono hs.le _
  · exact fun g hg hg' ↦ aux_prod_coeff_eq_zero_of_notMem_range f hg (by simpa using hg')
  · exact fun p _ ↦ aux_prod_f_eq_prod_coeff f p hs.le

end Nat.Partition
