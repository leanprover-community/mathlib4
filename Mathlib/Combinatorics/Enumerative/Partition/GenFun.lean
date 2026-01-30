/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.RingTheory.PowerSeries.PiTopology

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
* When $f(i, c) = 1$, this is the generating function for partition function $p(n)$
  (TODO: prove this).
* When $f(i, 1) = 1$ and $f(i, c) = 0$ for $c > 1$, this is the generating function for
  `#(Nat.Partition.distincts n)`. More generally, setting $f(i, c) = 1$ only for $c < m$ gives
  the generating function for `#(Nat.Partition.countRestricted n m)`.
  (See `Nat.Partition.hasProd_powerSeriesMk_card_countRestricted`).
* When $f(i, c) = 1$ for odd $i$ and $f(i, c) = 0$ for even $i$, this is the generating function for
  `#(Nat.Partition.odds n)`. More generally, setting $f(i, c) = 1$ only for $i$ satisfying certain
  `p : Prop` gives the generating function for `#(Nat.Partition.restricted n p)`.
  (See `Nat.Partition.hasProd_powerSeriesMk_card_restricted`)

The definition of `Nat.Partition.genFun` ignores the value of $f(0, c)$ and $f(i, 0)$. The formula
can be interpreted as assuming $f(i, 0) = 1$ and $f(0, c) = 0$ for $c \ne 0$. In theory we could
respect the actual value of $f(0, c)$ and $f(i, 0)$, but it makes the otherwise finite sum and
product potentially infinite.
-/

@[expose] public section

open Finset PowerSeries
open scoped PowerSeries.WithPiTopology

namespace Nat.Partition
variable {R : Type*} [CommSemiring R]

/-- Generating function associated with character $f(i, c)$ for partition functions, where $i$ is a
part of the partition, and $c$ is the count of that part in the partition. The character function is
multiplied within one `n.Partition`, and summed among all `n.Partition` for a fixed `n`. This way,
each `n` is assigned a value, which we use as the coefficients of the power series.

See the module docstring of `Combinatorics.Enumerative.Partition.GenFun` for more details. -/
def genFun (f : ℕ → ℕ → R) : R⟦X⟧ :=
  PowerSeries.mk fun n ↦ ∑ p : n.Partition, p.parts.toFinsupp.prod f

@[simp]
lemma coeff_genFun (f : ℕ → ℕ → R) (n : ℕ) :
    (genFun f).coeff n = ∑ p : n.Partition, p.parts.toFinsupp.prod f :=
  PowerSeries.coeff_mk _ _

/-- The summands in the formula `Nat.Partition.hasProd_genFun` tends to infinity in their order. -/
theorem tendsto_order_genFun_term_atTop_nhds_top (f : ℕ → ℕ → R) (i : ℕ) :
    Filter.Tendsto (fun j ↦ (f (i + 1) (j + 1) • (X : R⟦X⟧) ^ ((i + 1) * (j + 1))).order)
    Filter.atTop (nhds ⊤) := by
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr (fun n ↦ Filter.eventually_atTop.mpr ⟨n, ?_⟩)
  intro m hm
  grw [PowerSeries.smul_eq_C_mul, ← le_order_mul]
  refine lt_add_of_nonneg_of_lt (by simp) ?_
  nontriviality R using Subsingleton.eq_zero
  rw [order_X_pow]
  norm_cast
  grind

variable [TopologicalSpace R]

/-- The infinite sum in the formula `Nat.Partition.hasProd_genFun` always converges. -/
theorem summable_genFun_term (f : ℕ → ℕ → R) (i : ℕ) :
    Summable fun j ↦ f (i + 1) (j + 1) • (X : R⟦X⟧) ^ ((i + 1) * (j + 1)) := by
  apply WithPiTopology.summable_of_tendsto_order_atTop_nhds_top
  apply tendsto_order_genFun_term_atTop_nhds_top

/-- Alternative form of `summable_genFun_term` that unshifts the first index. -/
theorem summable_genFun_term' (f : ℕ → ℕ → R) {i : ℕ} (hi : i ≠ 0) :
    Summable fun j ↦ f i (j + 1) • (X : R⟦X⟧) ^ (i * (j + 1)) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hi
  apply summable_genFun_term

variable [T2Space R]

private theorem aux_dvd_of_coeff_ne_zero {f : ℕ → ℕ → R} {d : ℕ} {s : Finset ℕ} (hs0 : 0 ∉ s)
    {g : ℕ →₀ ℕ} (hg : g ∈ s.finsuppAntidiag d)
    (hprod : ∀ i ∈ s, (coeff (g i)) (1 + ∑' j, f i (j + 1) • X ^ (i * (j + 1))) ≠ (0 : R)) (x : ℕ) :
    x ∣ g x := by
  by_cases hx : x ∈ s
  · specialize hprod x hx
    contrapose! hprod
    have hx0 : x ≠ 0 := fun h ↦ hs0 (h ▸ hx)
    rw [map_add, (summable_genFun_term' f hx0).map_tsum _ (WithPiTopology.continuous_coeff _ _)]
    rw [show (0 : R) = 0 + ∑' (i : ℕ), 0 by simp]
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
    exact mem_of_subset (mem_finsuppAntidiag.mp hg).2 <| by simpa using hx

private theorem aux_prod_coeff_eq_zero_of_notMem_range (f : ℕ → ℕ → R) {d : ℕ} {s : Finset ℕ}
    (hs0 : 0 ∉ s) {g : ℕ →₀ ℕ} (hg : g ∈ s.finsuppAntidiag d)
    (hg' : g ∉ Set.range (toFinsuppAntidiag (n := d))) :
    ∏ i ∈ s, (coeff (g i)) (1 + ∑' j, f i (j + 1) • X ^ (i * (j + 1)) : R⟦X⟧) = 0 := by
  suffices ∃ i ∈ s, (coeff (g i)) ((1 : R⟦X⟧) + ∑' j, f i (j + 1) • X ^ (i * (j + 1))) = 0 by
    obtain ⟨i, hi, hi'⟩ := this
    apply prod_eq_zero hi hi'
  contrapose! hg' with hprod
  rw [Set.mem_range]
  have hgne0 (i : ℕ) : g i ≠ 0 ↔ i ≠ 0 ∧ i ≤ g i := by
    refine ⟨fun h ↦ ⟨?_, ?_⟩, by grind⟩
    · contrapose! hs0 with rfl
      exact mem_of_subset (mem_finsuppAntidiag.mp hg).2 (by simpa using h)
    · exact Nat.le_of_dvd (Nat.pos_of_ne_zero h) <| aux_dvd_of_coeff_ne_zero hs0 hg hprod _
  refine ⟨Nat.Partition.mk (Finsupp.mk g.support (fun i ↦ g i / i) ?_).toMultiset ?_ ?_, ?_⟩
  · simpa using hgne0
  · suffices ∀ i, g i ≠ 0 → i ≠ 0 by simpa [Nat.pos_iff_ne_zero]
    exact fun i h ↦ ((hgne0 i).mp h).1
  · obtain ⟨h1, h2⟩ := mem_finsuppAntidiag.mp hg
    refine Eq.trans ?_ h1
    suffices ∑ x ∈ g.support, g x / x * x = ∑ x ∈ s, g x by simpa [Finsupp.sum]
    apply sum_subset_zero_on_sdiff h2 (by simp)
    exact fun x hx ↦ Nat.div_mul_cancel <| aux_dvd_of_coeff_ne_zero hs0 hg hprod x
  · ext x
    simpa [toFinsuppAntidiag] using Nat.div_mul_cancel <| aux_dvd_of_coeff_ne_zero hs0 hg hprod x

private theorem aux_prod_f_eq_prod_coeff (f : ℕ → ℕ → R) {n : ℕ} (p : Partition n) {s : Finset ℕ}
    (hs : Icc 1 n ⊆ s) (hs0 : 0 ∉ s) :
    p.parts.toFinsupp.prod f =
    ∏ i ∈ s, coeff (p.toFinsuppAntidiag i) (1 + ∑' j, f i (j + 1) • X ^ (i * (j + 1))) := by
  simp_rw [Finsupp.prod, Multiset.toFinsupp_support, Multiset.toFinsupp_apply]
  apply prod_subset_one_on_sdiff
  · grind
  · intro x hx
    rw [mem_sdiff, Multiset.mem_toFinset] at hx
    have hx0 : x ≠ 0 := fun h ↦ hs0 (h ▸ hx.1)
    have hsum := (summable_genFun_term' f hx0).map_tsum _
      (WithPiTopology.continuous_constantCoeff R)
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

theorem hasProd_genFun (f : ℕ → ℕ → R) :
    HasProd (fun i ↦ 1 + ∑' j, f (i + 1) (j + 1) • X ^ ((i + 1) * (j + 1))) (genFun f) := by
  rw [HasProd, WithPiTopology.tendsto_iff_coeff_tendsto]
  refine fun d ↦ tendsto_atTop_of_eventually_const (fun s (hs : s ≥ range d) ↦ ?_)
  have : ∏ i ∈ s, ((1 : R⟦X⟧) + ∑' j, f (i + 1) (j + 1) • X ^ ((i + 1) * (j + 1)))
      = ∏ i ∈ s.map (addRightEmbedding 1), (1 + ∑' j, f i (j + 1) • X ^ (i * (j + 1))) := by simp
  rw [this]
  have hs : Icc 1 d ⊆ s.map (addRightEmbedding 1) := by
    intro i
    suffices 1 ≤ i → i ≤ d → ∃ a ∈ s, a + 1 = i by simpa
    intro h1 h2
    refine ⟨i - 1, mem_of_subset hs ?_, ?_⟩ <;> grind
  rw [coeff_genFun, coeff_prod]
  refine (sum_of_injOn toFinsuppAntidiag (toFinsuppAntidiag_injective d).injOn ?_ ?_ ?_).symm
  · intro p _
    exact mem_of_subset (finsuppAntidiag_mono hs.le _) p.toFinsuppAntidiag_mem_finsuppAntidiag
  · exact fun g hg hg' ↦ aux_prod_coeff_eq_zero_of_notMem_range f (by simp) hg (by simpa using hg')
  · exact fun p _ ↦ aux_prod_f_eq_prod_coeff f p hs.le (by simp)

theorem multipliable_genFun (f : ℕ → ℕ → R) :
    Multipliable fun i ↦ (1 : R⟦X⟧) + ∑' j, f (i + 1) (j + 1) • X ^ ((i + 1) * (j + 1)) :=
  (hasProd_genFun f).multipliable

theorem genFun_eq_tprod (f : ℕ → ℕ → R) :
    genFun f = ∏' i, (1 + ∑' j, f (i + 1) (j + 1) • X ^ ((i + 1) * (j + 1))) :=
  (hasProd_genFun f).tprod_eq.symm

end Nat.Partition
