/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Ideal.Operations

/-!
# Primary submodules

A proper submodule `S : Submodule R M` is primary iff
  `r • x ∈ S` implies `x ∈ S` or `∃ n : ℕ, r ^ n • (⊤ : Submodule R M) ≤ S`.

## Main results

* `Submodule.isPrimary_iff_zero_divisor_quotient_imp_nilpotent_smul`:
  A `N : Submodule R M` is primary if any zero divisor on `M ⧸ N` is nilpotent.
  See https://mathoverflow.net/questions/3910/primary-decomposition-for-modules
  for a comparison of this definition (a la Atiyah-Macdonald) vs "locally nilpotent" (Matsumura).

## Implementation details

This is a generalization of `Ideal.IsPrimary`. For brevity, the pointwise instances are used
to define the nilpotency of `r : R`.

## References

* [M. F. Atiyah and I. G. Macdonald, *Introduction to commutative algebra*][atiyah-macdonald]
  Chapter 4, Exercise 21.

-/

open Pointwise

namespace Submodule

section CommSemiring

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- A proper submodule `S : Submodule R M` is primary iff
  `r • x ∈ S` implies `x ∈ S` or `∃ n : ℕ, r ^ n • (⊤ : Submodule R M) ≤ S`.
  This generalizes `Ideal.IsPrimary`. -/
protected def IsPrimary (S : Submodule R M) : Prop :=
  S ≠ ⊤ ∧ ∀ {r : R} {x : M}, r • x ∈ S → x ∈ S ∨ ∃ n : ℕ, (r ^ n • ⊤ : Submodule R M) ≤ S

variable {S : Submodule R M}

lemma IsPrimary.ne_top (h : S.IsPrimary) : S ≠ ⊤ := h.left

end CommSemiring

section CommRing

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {S : Submodule R M}

lemma isPrimary_iff_zero_divisor_quotient_imp_nilpotent_smul :
    S.IsPrimary ↔ S ≠ ⊤ ∧ ∀ (r : R) (x : M ⧸ S), x ≠ 0 → r • x = 0 →
      ∃ n : ℕ, r ^ n • (⊤ : Submodule R (M ⧸ S)) = ⊥ := by
  refine (and_congr_right fun _ ↦ ?_)
  simp_rw [S.mkQ_surjective.forall, ← map_smul, ne_eq, ← LinearMap.mem_ker, ker_mkQ]
  congr! 2
  rw [forall_comm, ← or_iff_not_imp_left,
    ← LinearMap.range_eq_top.mpr S.mkQ_surjective, ← map_top]
  simp_rw [eq_bot_iff, ← map_pointwise_smul, map_le_iff_le_comap, comap_bot, ker_mkQ]

end CommRing

end Submodule
