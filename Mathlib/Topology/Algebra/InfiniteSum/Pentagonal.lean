/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Topology.Algebra.TopologicallyNilpotent

/-!
# Pentagonal number theorem

This is an intermediate file that proves the pentagonal number theorem in general topological ring
modulo summability and multipliability. The complete proof for formal power series is in
`Mathlib/RingTheory/PowerSeries/Pentagonal.lean`. TODO: also prove for real/complex numbers.

# Declarations
The following two declarations are exposed
* `Pentagonal.aux`: an auxiliary sequence for which the user needs to prove summability and growth
  rate.
* `Pentagonal.tprod_one_sub_pow`: pentagonal number theorem with a few summability and
  multipliability assumptions.

Reference:
https://math.stackexchange.com/questions/55738/how-to-prove-eulers-pentagonal-theorem-some-hints-will-help

-/

namespace Pentagonal
open Filter
variable {R : Type*} [CommRing R]

/--
We define an auxiliary sequence

$$ a_{k, n} = \left( x^{(k+1)n} \prod_{i=0}^{n} 1 - x^{k + i + 1} \right) $$

We will also use its sum

$$ A_k = \sum_{n=0}^{\infty} a_{k, n} $$ -/
public abbrev aux (k n : ℕ) (x : R) : R :=
  x ^ ((k + 1) * n) * ∏ i ∈ Finset.range (n + 1), (1 - x ^ (k + i + 1))

/-- And a second auxiliary sequence

$$ b_{k, n} = x^{(k+1)n} (x^{2k + n + 3} - 1) \prod_{i=0}^{n-1} 1 - x^{k + i + 2} $$ -/
abbrev aux2 (k n : ℕ) (x : R) : R :=
  x ^ ((k + 1) * n) * (x ^ (2 * k + n + 3) - 1) * ∏ i ∈ Finset.range n, (1 - x ^ (k + i + 2))

/-- $aux$ and $aux2$ have relation

$$ a_{k,n} + x^{3k + 5}a_{k + 1, n} = b_{k, n+1} - b_{k, n} $$ -/
theorem aux2_sub_aux2 (k n : ℕ) (x : R) :
    aux k n x + x ^ (3 * k + 5) * aux (k + 1) n x = aux2 k (n + 1) x - aux2 k n x := by
  simp_rw [aux2, Finset.prod_range_succ, aux]
  rw [Finset.prod_range_succ', Finset.prod_range_succ]
  ring_nf

variable [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]

/-- By summing with telescoping, we get a recurrence formula for $A$

$$ A_k = 1 - x^{2k + 3} - x^{3k + 5}A_{k + 1} $$
-/
theorem tsum_aux (k : ℕ) {x : R} (hx : IsTopologicallyNilpotent x)
    (haux : ∀ k, Summable (aux k · x)) (h : ∀ k, Multipliable (fun n ↦ 1 - x ^ (n + k + 1))) :
    ∑' n, aux k n x = 1 - x ^ (2 * k + 3) - x ^ (3 * k + 5) * ∑' n, aux (k + 1) n x := by
  rw [eq_sub_iff_add_eq, show 1 - x ^ (2 * k + 3) = 0 - aux2 k 0 x by simp [aux2]]
  rw [← (haux _).tsum_mul_left, ← (haux _).tsum_add ((haux _).mul_left _)]
  apply HasSum.tsum_eq
  rw [((haux _).add ((haux _).mul_left _)).hasSum_iff_tendsto_nat]
  simp_rw [aux2_sub_aux2, Finset.sum_range_sub (aux2 k · x)]
  apply Tendsto.sub_const
  rw [show nhds 0 = nhds (0 * (0 - 1) * ∏' i, (1 - x ^ (k + i + 2))) by simp]
  refine (Tendsto.mul ?_ ?_).mul ?_
  · exact hx.comp (strictMono_mul_left_of_pos (by simp)).tendsto_atTop
  · exact (hx.comp (add_right_strictMono.add_monotone monotone_const).tendsto_atTop).sub_const _
  · apply Multipliable.tendsto_prod_tprod_nat
    convert h (k + 1) using 4
    ring

/-- The Euler function is related to $A_0$ by

$$ \prod_{n = 0}^{\infty} 1 - x^{n + 1} = 1 - x - x^2 A_0 $$ -/
theorem tprod_one_sub_pow_eq_aux_zero {x : R}
    (haux : ∀ k, Summable (aux k · x)) (h : ∀ k, Multipliable fun n ↦ 1 - x ^ (n + k + 1)) :
    ∏' n, (1 - x ^ (n + 1)) = 1 - x - x ^ 2 * ∑' n, aux 0 n x := by
  obtain hsum := haux 0
  simp_rw [aux, zero_add, one_mul] at hsum
  have hsum' : Summable fun i ↦ x ^ (i + 1) * ∏ n ∈ Finset.range i, (1 - x ^ (n + 1)) := by
    apply Summable.comp_nat_add (k := 1)
    conv in fun k ↦ _ =>
      ext k
      rw [pow_add, pow_add, mul_assoc (x ^ k), mul_comm (x ^ k), mul_assoc (x ^ 1 * x ^ 1)]
    exact hsum.mul_left _
  rw [tprod_one_sub_ordered (by simpa [Nat.Iio_eq_range] using hsum') (by simpa using h 0)]
  simp_rw [Nat.Iio_eq_range, sub_sub, sub_right_inj, hsum'.tsum_eq_zero_add]
  conv in fun k ↦ x ^ (k + 1 + 1) * _ =>
    ext k
    rw [pow_add, pow_add, mul_assoc (x ^ k), mul_comm (x ^ k),
      ← pow_add x 1 1, one_add_one_eq_two, mul_assoc (x ^ 2)]
  simp [hsum.tsum_mul_left, aux]

/-- Applying the recurrence formula repeatedly, we get

$$ \prod_{n = 0}^{\infty} 1 - x^{n + 1} =
\left(\sum_{k=0}^{j} (-1)^k \left(x^{k(3k+1)/2} - x^{(k+1)(3k+2)/2}\right) \right) +
(-1)^{j+1}x^{(j+1)(3j+4)/2}A_j $$ -/
theorem tprod_one_sub_pow_eq_aux (j : ℕ) {x : R} (hx : IsTopologicallyNilpotent x)
    (haux : ∀ k, Summable (aux k · x)) (h : ∀ k, Multipliable (fun n ↦ 1 - x ^ (n + k + 1))) :
    ∏' n, (1 - x ^ (n + 1)) = ∑ k ∈ Finset.range (j + 1),
      (-1) ^ k * (x ^ (k * (3 * k + 1) / 2) - x ^ ((k + 1) * (3 * k + 2) / 2))
      + (-1) ^ (j + 1) * x ^ ((j + 1) * (3 * j + 4) / 2) * ∑' n, aux j n x := by
  induction j with
  | zero => simp [tprod_one_sub_pow_eq_aux_zero haux h, aux, ← sub_eq_add_neg]
  | succ n ih =>
    rw [ih, tsum_aux _ hx haux h, Finset.sum_range_succ _ (n + 1)]
    have h (n) : (n + 1 + 1) * (3 * (n + 1) + 2) / 2 =
        (n + 1) * (3 * n + 4) / 2 + (2 * n + 3) := by
      rw [← Nat.add_mul_div_left _ _ (by simp)]
      ring_nf
    simp_rw [h]
    have h (n) : (n + 1 + 1) * (3 * (n + 1) + 4) / 2 =
        (n + 1) * (3 * n + 4) / 2 + (3 * n + 5) := by
      rw [← Nat.add_mul_div_left _ _ (by simp)]
      ring_nf
    simp_rw [h]
    ring_nf

/-- Pentagonal number theorem, assuming appropriate multipliability and summability.

$$ \prod_{n = 0}^{\infty} 1 - x^{n + 1} =
\sum_{k=0}^{\infty} (-1)^k \left(x^{k(3k+1)/2} - x^{(k+1)(3k+2)/2}\right) $$ -/
public theorem tprod_one_sub_pow {x : R} (hx : IsTopologicallyNilpotent x)
    (haux : ∀ k, Summable (Pentagonal.aux k · x))
    (hlhs : ∀ k, Multipliable (fun n ↦ 1 - x ^ (n + k + 1)))
    (hrhs : Summable fun (k : ℕ) ↦
      (-1) ^ k * (x ^ (k * (3 * k + 1) / 2) - x ^ ((k + 1) * (3 * k + 2) / 2)))
    (htail : Tendsto (fun k ↦ (-1) ^ (k + 1) * x ^ ((k + 1) * (3 * k + 4) / 2) *
      ∑' (n : ℕ), Pentagonal.aux k n x) atTop (nhds 0)) :
    ∏' n, (1 - x ^ (n + 1)) =
    ∑' k, (-1) ^ k * (x ^ (k * (3 * k + 1) / 2) - x ^ ((k + 1) * (3 * k + 2) / 2)) := by
  obtain h := fun n ↦ tprod_one_sub_pow_eq_aux n hx haux hlhs
  simp_rw [← sub_eq_iff_eq_add] at h
  refine (HasSum.tsum_eq ?_).symm
  rw [hrhs.hasSum_iff_tendsto_nat, (map_add_atTop_eq_nat 1).symm]
  apply tendsto_map'
  simp_rw [Function.comp_def, ← h]
  rw [← tendsto_sub_nhds_zero_iff]
  simpa using htail.neg

end Pentagonal
