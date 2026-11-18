/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Module.Lattice.Summable
public import Mathlib.Algebra.Module.ZLattice.Basic


/-!
# Convergence of `p`-series on lattices

Let `E` be a finite dimensional normed `ℝ`-space, and `L` a discrete subgroup of `E` of rank `d`.
We show that `∑ z ∈ L, ‖z - x‖ʳ` is convergent for `r < -d`.

## Main results
- `ZLattice.summable_norm_rpow`: `∑ z ∈ L, ‖z‖ʳ` converges when `r < -d`.
- `ZLattice.summable_norm_sub_rpow`: `∑ z ∈ L, ‖z - x‖ʳ` converges when `r < -d`.
- `ZLattice.tsum_norm_rpow_le`:
  `∑ z ∈ L, ‖z‖ʳ ≤ Aʳ * ∑ k : ℕ, kᵈ⁺ʳ⁻¹` for some `A > 0` depending only on `L`.

All results in this file are deprecated in favour of `Mathlib/Algebra/Module/Lattice/Summable.lean`.
-/

@[expose] public section

noncomputable section

open Module

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] {L : Submodule ℤ E} [DiscreteTopology L]
variable {ι : Type*} (b : Basis ι ℤ L)

namespace ZLattice

@[deprecated Submodule.IsLattice.exists_forall_abs_repr_le_norm +typeChanged
  (since := "2026-10-28")]
lemma exists_forall_abs_repr_le_norm :
    ∃ (ε : ℝ), 0 < ε ∧ ∀ (x : L), ∀ i, ε * |b.repr x i| ≤ ‖x‖ :=
  have := Submodule.IsLattice.of_discreteTopology (K := ℝ) L
  Submodule.IsLattice.exists_forall_abs_repr_le_norm b

/--
Given a basis of a (possibly not full rank) `ℤ`-lattice, there exists a `ε > 0` such that
`|b.repr x i| < n` for all `‖x‖ < n * ε` (i.e. `b.repr x i = O(x)` depending only on `b`).
This is an arbitrary choice of such an `ε`.
-/
@[deprecated Submodule.IsLattice.normBound +typeChanged (since := "2026-10-28")]
def normBound {ι : Type*} (b : Basis ι ℤ L) : ℝ :=
  have := Submodule.IsLattice.of_discreteTopology (K := ℝ) L
  Submodule.IsLattice.normBound b

@[deprecated Submodule.IsLattice.normBound_pos +typeChanged (since := "2026-10-28")]
lemma normBound_pos {ι : Type*} (b : Basis ι ℤ L) : 0 < normBound b :=
  have := Submodule.IsLattice.of_discreteTopology (K := ℝ) L
  Submodule.IsLattice.normBound_pos b

@[deprecated Submodule.IsLattice.normBound_spec +typeChanged (since := "2026-10-28")]
lemma normBound_spec {ι : Type*} (b : Basis ι ℤ L) (x : L) (i : ι) :
    normBound b * |b.repr x i| ≤ ‖x‖ :=
  have := Submodule.IsLattice.of_discreteTopology (K := ℝ) L
  Submodule.IsLattice.normBound_spec b x i

@[deprecated Submodule.IsLattice.abs_repr_le +typeChanged (since := "2026-10-28")]
lemma abs_repr_le {ι : Type*} (b : Basis ι ℤ L) (x : L) (i : ι) :
    |b.repr x i| ≤ (normBound b)⁻¹ * ‖x‖ :=
  have := Submodule.IsLattice.of_discreteTopology (K := ℝ) L
  Submodule.IsLattice.abs_repr_le b x i

@[deprecated Submodule.IsLattice.abs_repr_lt_of_norm_lt +typeChanged (since := "2026-10-28")]
lemma abs_repr_lt_of_norm_lt {ι : Type*} (b : Basis ι ℤ L) (x : L) (n : ℕ)
    (hxn : ‖x‖ < normBound b * n) (i : ι) : |b.repr x i| < n :=
  have := Submodule.IsLattice.of_discreteTopology (K := ℝ) L
  Submodule.IsLattice.abs_repr_lt_of_norm_lt b x n hxn i

@[deprecated Submodule.IsLattice.le_norm_of_le_abs_repr +typeChanged (since := "2026-10-28")]
lemma le_norm_of_le_abs_repr {ι : Type*} (b : Basis ι ℤ L) (x : L) (n : ℕ) (i : ι)
    (hi : n ≤ |b.repr x i|) : normBound b * n ≤ ‖x‖ :=
  have := Submodule.IsLattice.of_discreteTopology (K := ℝ) L
  Submodule.IsLattice.le_norm_of_le_abs_repr b x n i hi

open Finset in
@[deprecated Submodule.IsLattice.sum_piFinset_Icc_rpow_le +typeChanged (since := "2026-10-28")]
lemma sum_piFinset_Icc_rpow_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℤ L) {d : ℕ} (hd : d = Fintype.card ι)
    (n : ℕ) (r : ℝ) (hr : r < -d) :
    ∑ p ∈ Fintype.piFinset fun _ : ι ↦ Icc (-n : ℤ) n, ‖∑ i, p i • b i‖ ^ r ≤
      2 * d * 3 ^ (d - 1) * normBound b ^ r * ∑' k : ℕ, (k : ℝ) ^ (d - 1 + r) :=
  have := Submodule.IsLattice.of_discreteTopology (K := ℝ) L
  Submodule.IsLattice.sum_piFinset_Icc_rpow_le b hd n r hr

variable (L)

@[deprecated Submodule.IsLattice.exists_finsetSum_norm_rpow_le_tsum +typeChanged
  (since := "2026-10-28")]
lemma exists_finsetSum_norm_rpow_le_tsum :
    ∃ A > (0 : ℝ), ∀ r < (-Module.finrank ℤ L : ℝ), ∀ s : Finset L,
      ∑ z ∈ s, ‖z‖ ^ r ≤ A ^ r * ∑' k : ℕ, (k : ℝ) ^ (Module.finrank ℤ L - 1 + r) :=
  have := Submodule.IsLattice.of_discreteTopology (K := ℝ) L
  Submodule.IsLattice.exists_finsetSum_norm_rpow_le_tsum L

/--
Let `L` be a lattice with (possibly non-full) rank `d`, and `r : ℝ` such that `d < r`.
Then `∑ z ∈ L, ‖z‖⁻ʳ ≤ A⁻ʳ * ∑ k : ℕ, kᵈ⁻ʳ⁻¹` for some `A > 0` depending only on `L`.
This is an arbitrary choice of `A`. See `ZLattice.tsum_norm_rpow_le`.
-/
@[deprecated Submodule.IsLattice.tsumNormRPowBound +typeChanged (since := "2026-10-28")]
def tsumNormRPowBound : ℝ :=
  have := Submodule.IsLattice.of_discreteTopology (K := ℝ) L
  Submodule.IsLattice.tsumNormRPowBound L

@[deprecated Submodule.IsLattice.tsumNormRPowBound_pos +typeChanged (since := "2026-10-28")]
lemma tsumNormRPowBound_pos : 0 < tsumNormRPowBound L :=
  have := Submodule.IsLattice.of_discreteTopology (K := ℝ) L
  Submodule.IsLattice.tsumNormRPowBound_pos L

@[deprecated Submodule.IsLattice.tsumNormRPowBound_spec +typeChanged (since := "2026-10-28")]
lemma tsumNormRPowBound_spec (r : ℝ) (h : r < -Module.finrank ℤ L) (s : Finset L) :
    ∑ z ∈ s, ‖z‖ ^ r ≤
      tsumNormRPowBound L ^ r * ∑' k : ℕ, (k : ℝ) ^ (Module.finrank ℤ L - 1 + r) :=
  have := Submodule.IsLattice.of_discreteTopology (K := ℝ) L
  Submodule.IsLattice.tsumNormRPowBound_spec L r h s

/-- If `L` is a `ℤ`-lattice with rank `d` in `E`, then `∑ z ∈ L, ‖z‖ʳ` converges when `r < -d`. -/
@[deprecated Submodule.IsLattice.summable_norm_rpow +typeChanged (since := "2026-10-28")]
lemma summable_norm_rpow (r : ℝ) (hr : r < -Module.finrank ℤ L) :
    Summable fun z : L ↦ ‖z‖ ^ r :=
  have := Submodule.IsLattice.of_discreteTopology (K := ℝ) L
  Submodule.IsLattice.summable_norm_rpow L r hr

/-- `∑ z ∈ L, ‖z‖⁻ʳ ≤ A⁻ʳ * ∑ k : ℕ, kᵈ⁻ʳ⁻¹` for some `A > 0` depending only on `L`. -/
@[deprecated Submodule.IsLattice.tsum_norm_rpow_le +typeChanged (since := "2026-10-28")]
lemma tsum_norm_rpow_le (r : ℝ) (hr : r < -Module.finrank ℤ L) :
    ∑' z : L, ‖z‖ ^ r ≤
      tsumNormRPowBound L ^ r * ∑' k : ℕ, (k : ℝ) ^ (Module.finrank ℤ L - 1 + r) :=
  have := Submodule.IsLattice.of_discreteTopology (K := ℝ) L
  Submodule.IsLattice.tsum_norm_rpow_le L r hr

@[deprecated Submodule.IsLattice.summable_norm_sub_rpow +typeChanged (since := "2026-10-28")]
lemma summable_norm_sub_rpow (r : ℝ) (hr : r < -Module.finrank ℤ L) (x : E) :
    Summable fun z : L ↦ ‖z - x‖ ^ r :=
  have := Submodule.IsLattice.of_discreteTopology (K := ℝ) L
  Submodule.IsLattice.summable_norm_sub_rpow L r hr x

@[deprecated Submodule.IsLattice.summable_norm_sub_zpow +typeChanged (since := "2026-10-28")]
lemma summable_norm_sub_zpow (n : ℤ) (hn : n < -Module.finrank ℤ L) (x : E) :
    Summable fun z : L ↦ ‖z - x‖ ^ n :=
  have := Submodule.IsLattice.of_discreteTopology (K := ℝ) L
  Submodule.IsLattice.summable_norm_sub_zpow L n hn x

@[deprecated Submodule.IsLattice.summable_norm_zpow +typeChanged (since := "2026-10-28")]
lemma summable_norm_zpow (n : ℤ) (hn : n < -Module.finrank ℤ L) :
    Summable fun z : L ↦ ‖z‖ ^ n :=
  have := Submodule.IsLattice.of_discreteTopology (K := ℝ) L
  Submodule.IsLattice.summable_norm_zpow L n hn

@[deprecated Submodule.IsLattice.summable_norm_sub_inv_pow +typeChanged (since := "2026-10-28")]
lemma summable_norm_sub_inv_pow (n : ℕ) (hn : Module.finrank ℤ L < n) (x : E) :
    Summable fun z : L ↦ ‖z - x‖⁻¹ ^ n :=
  have := Submodule.IsLattice.of_discreteTopology (K := ℝ) L
  Submodule.IsLattice.summable_norm_sub_inv_pow L n hn x

@[deprecated Submodule.IsLattice.summable_norm_pow_inv +typeChanged (since := "2026-10-28")]
lemma summable_norm_pow_inv (n : ℕ) (hn : Module.finrank ℤ L < n) :
    Summable fun z : L ↦ ‖z‖⁻¹ ^ n :=
  have := Submodule.IsLattice.of_discreteTopology (K := ℝ) L
  Submodule.IsLattice.summable_norm_pow_inv L n hn

end ZLattice
