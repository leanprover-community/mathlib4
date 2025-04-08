/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.Polynomial.Eisenstein.Generalized
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Tactic.ComputeDegree

/-! # Example of an application of the generalized Eisenstein criterion

We show here how `Polynomial.generalizedEisenstein` can be applied
to establish the irreducibility of the explicit polynomial of degree 4
  `X ^ 4 - 10 * X + 1 : ℤ[X]`.
(to which the standard criterion) wouldn't apply.
One argues modulo `3`, with `q := X ^ 2 + 1`.

-/

namespace Polynomial

open Ideal.Quotient Ideal

example : Irreducible (X ^ 4 - 10 * X ^ 2 + 1 : ℤ[X]) := by
  -- We will apply the generalized Eisenstein criterion with `q = X ^ 2 + 1` and `K = ZMod 3`.
  set f : ℤ[X] := X ^ 4 - 10 * X ^ 2 + 1 with hf_eq
  have hdeg_f : f.natDegree = 4 := by unfold f; compute_degree!
  set q : ℤ [X] := X ^ 2 + 1 with hq_eq
  have hq_deg : q.natDegree = 2 := by unfold q; compute_degree!
  have hq_monic : q.Monic := by unfold q; monicity!
  have hfq : f = q ^ 2 - 12 * q + 12 := by ring
   -- On the other hand, `f %ₘ q = 12`, which is not a multiple of `9`.
  apply generalizedEisenstein (K := ZMod 3) (q := q) (p := 2)
  · set q₃ : (ZMod 3)[X] := X ^ 2 + 1
    have hdeg_q₃ : q₃.natDegree = 2 := by unfold q₃; compute_degree!
    suffices Irreducible q₃ by simpa [q] using this.prime
    apply irreducible_of_degree_le_three_of_not_isRoot
      (by simp_all) (by simp_all [q₃]; decide)
  · unfold q; monicity!
  · simp_all
  · unfold f; monicity!
  · rw [hfq, ← sub_eq_zero]
    have : (12 : (ZMod 3)[X]) = 0 := by apply CharP.ofNat_eq_zero' _ 3 12; norm_num
    simp [q, this]
  · suffices f %ₘ q = 12 by
      rw [this, ← map_ofNat C, Polynomial.map_C, ne_eq, C_eq_zero, eq_zero_iff_mem,
      CharP.ker_intAlgebraMap_eq_span 3, span_singleton_pow, mem_span_singleton]
      norm_num
    rw [hfq, ← modByMonicHom_apply, LinearMap.map_add]
    convert zero_add _
    · rw [← LinearMap.mem_ker, mem_ker_modByMonic hq_monic]
      rw [pow_two, ← sub_mul]
      apply dvd_mul_left
    · symm
      simp only [modByMonicHom_apply, Polynomial.modByMonic_eq_self_iff hq_monic, f]
      rw [show q.degree = 2 by unfold q; compute_degree!]
      rw [show degree _ = 0 by compute_degree!]
      norm_num

end Polynomial
