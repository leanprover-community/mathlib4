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
equation in `Nat.Partition.hasProd_genFun` (with shifted indices). To avoid nested infinite
expression, the factors in the second equation is defined as `Nat.Partition.genFunFactor`, and its
equivalence to the infinite sum is shown at `Nat.Partition.hasSum_genFunFactor`.

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
noncomputable def genFun (f : ℕ → ℕ → R) : R⟦X⟧ :=
  PowerSeries.mk fun n ↦ ∑ p : n.Partition, p.parts.toFinsupp.prod f

@[simp]
lemma coeff_genFun (f : ℕ → ℕ → R) (n : ℕ) :
    (genFun f).coeff n = ∑ p : n.Partition, p.parts.toFinsupp.prod f :=
  PowerSeries.coeff_mk _ _

-- TODO: this was an intermediate lemma in this file but is no longer in use. Generalize this
-- and move this to a better place.
theorem tendsto_order_genFun_term_atTop_nhds_top (f : ℕ → ℕ → R) (i : ℕ) :
    Filter.Tendsto (fun j ↦ (f (i + 1) (j + 1) • (X : R⟦X⟧) ^ ((i + 1) * (j + 1))).order)
    Filter.atTop (nhds ⊤) := by
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr (fun n ↦ Filter.eventually_atTop.mpr ⟨n, ?_⟩)
  intro m hm
  grw [PowerSeries.smul_eq_C_mul, ← le_order_mul]
  refine lt_add_of_nonneg_of_lt (by simp) ?_
  nontriviality R using Subsingleton.eq_zero (α := R⟦X⟧)
  rw [order_X_pow]
  norm_cast
  grind

/-- Factor for part $i$ of the generating function associated with character $f(i, c)$ for partition
functions. -/
noncomputable def genFunFactor (f : ℕ → ℕ → R) (i : ℕ) : R⟦X⟧ :=
  PowerSeries.mk fun n ↦ if n ≠ 0 ∧ i ∣ n then f i (n / i) else 0

@[simp]
theorem constantCoeff_genFunFactor (f : ℕ → ℕ → R) (i : ℕ) :
    (genFunFactor f i).constantCoeff = 0 := by
  simp [genFunFactor]

@[simp]
theorem coeff_genFunFactor (f : ℕ → ℕ → R) {i j : ℕ} (hi : i ≠ 0) (hj : j ≠ 0) :
    (genFunFactor f i).coeff (j * i) = f i j := by
  simp [genFunFactor, hi, hj]

@[simp]
theorem coeff_genFunFactor_self (f : ℕ → ℕ → R) {i : ℕ} (hi : i ≠ 0) :
    (genFunFactor f i).coeff i = f i 1 := by
  simpa using coeff_genFunFactor f hi (one_ne_zero)

theorem dvd_of_coeff_genFunFactor_ne_zero {f : ℕ → ℕ → R} {i n : ℕ}
    (h : (genFunFactor f i).coeff n ≠ 0) : i ∣ n := by
  simp_all [genFunFactor]

private theorem aux_prod_f_eq_prod_coeff (f : ℕ → ℕ → R) {n : ℕ} (p : Partition n) {s : Finset ℕ}
    (hs : Icc 1 n ⊆ s) :
    p.parts.toFinsupp.prod f = ∏ i ∈ s, coeff (p.toFinsuppAntidiag i) (1 + genFunFactor f i) := by
  simp_rw [Finsupp.prod, Multiset.toFinsupp_support, Multiset.toFinsupp_apply]
  refine prod_subset_one_on_sdiff ?_ (fun i hi ↦ ?_) (fun i hi ↦ ?_)
  · grind
  · rw [mem_sdiff, Multiset.mem_toFinset] at hi
    simp [hi.2]
  · rw [Multiset.mem_toFinset] at hi
    simp [(p.parts_pos hi).ne.symm, Multiset.count_ne_zero.mpr hi]

private theorem aux_dvd_of_coeff_ne_zero {f : ℕ → ℕ → R} {d : ℕ} {s : Finset ℕ}
    {g : ℕ →₀ ℕ} (hg : g ∈ s.finsuppAntidiag d) (hcoeff : ∀ i ∈ s, (coeff (g i))
    (1 + genFunFactor f i) ≠ 0) (x : ℕ) :
    x ∣ g x := by
  by_cases hx : x ∈ s
  · by_cases hgx : g x = 0
    · simp [hgx]
    specialize hcoeff x hx
    simp only [map_add, coeff_one, hgx, ↓reduceIte, zero_add] at hcoeff
    exact dvd_of_coeff_genFunFactor_ne_zero hcoeff
  · suffices g x = 0 by simp [this]
    contrapose! hx
    exact mem_of_subset (mem_finsuppAntidiag.mp hg).2 <| by simpa using hx

private theorem aux_prod_coeff_eq_zero_of_notMem_range (f : ℕ → ℕ → R) {d : ℕ} {s : Finset ℕ}
    (hs0 : 0 ∉ s) {g : ℕ →₀ ℕ} (hg : g ∈ s.finsuppAntidiag d)
    (hg' : g ∉ Set.range (toFinsuppAntidiag (n := d))) :
    ∏ i ∈ s, (1 + genFunFactor f i).coeff (g i) = 0 := by
  suffices ∃ i ∈ s, (1 + genFunFactor f i).coeff (g i) = 0 by
    obtain ⟨i, hi, hi'⟩ := this
    exact prod_eq_zero hi hi'
  contrapose! hg' with hprod
  have hgne0 (i : ℕ) : g i ≠ 0 ↔ i ≠ 0 ∧ i ≤ g i := by
    refine ⟨fun h ↦ ⟨?_, ?_⟩, by grind⟩
    · contrapose hs0 with rfl
      exact mem_of_subset (mem_finsuppAntidiag.mp hg).2 (by simpa using h)
    · exact Nat.le_of_dvd (Nat.pos_of_ne_zero h) <| aux_dvd_of_coeff_ne_zero hg hprod _
  refine ⟨Nat.Partition.mk (Finsupp.mk g.support (fun i ↦ g i / i) ?_).toMultiset ?_ ?_, ?_⟩
  · simpa using hgne0
  · suffices ∀ i, g i ≠ 0 → 0 < i by simpa
    exact fun i h ↦ Nat.pos_iff_ne_zero.mpr ((hgne0 i).mp h).1
  · obtain ⟨rfl, h⟩ := mem_finsuppAntidiag.mp hg
    suffices ∑ x ∈ g.support, g x / x * x = ∑ x ∈ s, g x by simpa [Finsupp.sum]
    apply sum_subset_zero_on_sdiff h (by simp)
    exact fun x hx ↦ Nat.div_mul_cancel <| aux_dvd_of_coeff_ne_zero hg hprod x
  · ext x
    simpa using Nat.div_mul_cancel <| aux_dvd_of_coeff_ne_zero hg hprod x

variable [TopologicalSpace R]

theorem hasSum_genFunFactor (f : ℕ → ℕ → R) {i : ℕ} (hi : i ≠ 0) :
    HasSum (fun j ↦ (f i (j + 1) • (X : R⟦X⟧) ^ (i * (j + 1)))) (genFunFactor f i) := by
  have hinj : Function.Injective (fun j ↦ i * (j + 1)) :=
    (mul_right_injective₀ hi).comp (add_left_injective 1)
  convert! (hinj.hasSum_iff ?_).mpr (genFunFactor f i).hasSum_of_monomials_self with j
  · simp [genFunFactor, hi, monomial_eq_C_mul_X_pow, smul_eq_C_mul]
  intro n h
  suffices ¬(n ≠ 0 ∧ i ∣ n) by simp [genFunFactor, this]
  contrapose! h
  obtain ⟨h0, k, rfl⟩ := h
  have : k ≠ 0 := fun h ↦ by simp [h] at h0
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero this
  simp

theorem summable_genFun_term (f : ℕ → ℕ → R) (i : ℕ) :
    Summable fun j ↦ f (i + 1) (j + 1) • (X : R⟦X⟧) ^ ((i + 1) * (j + 1)) :=
  (hasSum_genFunFactor f (by simp)).summable

theorem summable_genFun_term' (f : ℕ → ℕ → R) {i : ℕ} (hi : i ≠ 0) :
    Summable fun j ↦ f i (j + 1) • (X : R⟦X⟧) ^ (i * (j + 1)) :=
  (hasSum_genFunFactor f hi).summable

theorem hasProd_genFun (f : ℕ → ℕ → R) :
    HasProd (fun i ↦ 1 + genFunFactor f (i + 1)) (genFun f) := by
  rw [HasProd, WithPiTopology.tendsto_iff_coeff_tendsto]
  refine fun d ↦ tendsto_atTop_of_eventually_const (fun s (hs : s ≥ range d) ↦ ?_)
  have : ∏ i ∈ s, (1 + genFunFactor f (i + 1)) =
    ∏ i ∈ s.map (addRightEmbedding 1), (1 + genFunFactor f i) := by simp
  rw [this]
  have hs : Icc 1 d ⊆ s.map (addRightEmbedding 1) := by
    intro i
    suffices 1 ≤ i → i ≤ d → ∃ a ∈ s, a + 1 = i by simpa
    intro h1 h2
    refine ⟨i - 1, mem_of_subset hs ?_, ?_⟩ <;> grind
  rw [coeff_genFun, coeff_prod]
  refine (sum_of_injOn toFinsuppAntidiag (toFinsuppAntidiag_injective d).injOn ?_ ?_ ?_).symm
  · intro p _
    exact mem_of_subset (finsuppAntidiag_mono hs _) p.toFinsuppAntidiag_mem_finsuppAntidiag
  · exact fun g hg hg' ↦ aux_prod_coeff_eq_zero_of_notMem_range f (by simp) hg (by simpa using hg')
  · exact fun p _ ↦ aux_prod_f_eq_prod_coeff f p hs

theorem multipliable_one_add_genFunFactor (f : ℕ → ℕ → R) :
    Multipliable fun i ↦ 1 + genFunFactor f (i + 1) :=
  (hasProd_genFun f).multipliable

@[deprecated (since := "2026-08-30")] alias multipliable_genFun := multipliable_one_add_genFunFactor

variable [T2Space R]

theorem hasProd_genFun' (f : ℕ → ℕ → R) :
    HasProd (fun i ↦ 1 + ∑' j, f (i + 1) (j + 1) • X ^ ((i + 1) * (j + 1))) (genFun f) := by
  convert hasProd_genFun f with i
  exact (hasSum_genFunFactor f (by simp)).tsum_eq

theorem genFun_eq_tprod (f : ℕ → ℕ → R) :
    genFun f = ∏' i, (1 + genFunFactor f (i + 1)) :=
  (hasProd_genFun f).tprod_eq.symm

end Nat.Partition
