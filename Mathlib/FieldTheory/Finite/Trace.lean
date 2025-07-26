/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.RingTheory.Trace.Basic
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# The trace and norm maps for finite fields

We state several lemmas about the trace and norm maps for finite fields.

## Main Results

- `trace_to_zmod_nondegenerate`: the trace map from a finite field of characteristic `p` to
  `ZMod p` is nondegenerate.
- `algebraMap_trace_eq_sum_pow`: an explicit formula for the trace map:
  `trace[L/K](x) = ∑ i < [L:K], x ^ ((#K) ^ i)`.
- `algebraMap_norm_eq_prod_pow`: an explicit formula for the norm map:
  `norm[L/K](x) = ∏ i < [L:K], x ^ ((#K) ^ i)`.

## Tags
finite field, trace, norm
-/


namespace FiniteField

/-- The trace map from a finite field to its prime field is nongedenerate. -/
theorem trace_to_zmod_nondegenerate (F : Type*) [Field F] [Finite F]
    [Algebra (ZMod (ringChar F)) F] {a : F} (ha : a ≠ 0) :
    ∃ b : F, Algebra.trace (ZMod (ringChar F)) F (a * b) ≠ 0 := by
  haveI : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F _⟩
  have htr := traceForm_nondegenerate (ZMod (ringChar F)) F a
  simp_rw [Algebra.traceForm_apply] at htr
  by_contra! hf
  exact ha (htr hf)

/-- An explicit formula for the trace map: `trace[L/K](x) = ∑ i < [L:K], x ^ ((#K) ^ i)`. -/
theorem algebraMap_trace_eq_sum_pow (K L : Type*) [Field K] [Field L]
    [Fintype K] [Finite L] [Algebra K L] (x : L) :
    algebraMap K L (Algebra.trace K L x) =
      ∑ i ∈ Finset.range (Module.finrank K L), x ^ (Fintype.card K ^ i) := by
  rw [trace_eq_sum_automorphisms, Finset.sum_range]
  exact Eq.symm <| Fintype.sum_bijective _ (bijective_frobeniusAlgEquivOfAlgebraic_pow K L) _ _ <|
    fun i ↦ by rw [AlgEquiv.coe_pow, coe_frobeniusAlgEquivOfAlgebraic_iterate]

/-- An explicit formula for the norm map: `norm[L/K](x) = ∏ i < [L:K], x ^ ((#K) ^ i)`. -/
theorem algebraMap_norm_eq_prod_pow (K L : Type*) [Field K] [Field L]
    [Fintype K] [Finite L] [Algebra K L] (x : L) :
    algebraMap K L (Algebra.norm K x) =
      ∏ i ∈ Finset.range (Module.finrank K L), x ^ (Fintype.card K ^ i) := by
  rw [Algebra.norm_eq_prod_automorphisms, Finset.prod_range]
  exact Eq.symm <| Fintype.prod_bijective _ (bijective_frobeniusAlgEquivOfAlgebraic_pow K L) _ _ <|
    fun i ↦ by rw [AlgEquiv.coe_pow, coe_frobeniusAlgEquivOfAlgebraic_iterate]

/-- An explicit formula for the norm map: `norm[L/K](x) = x ^ (∑ i < [L:K], (#K) ^ i)`. -/
theorem algebraMap_norm_eq_pow_sum (K L : Type*) [Field K] [Field L]
    [Fintype K] [Finite L] [Algebra K L] (x : L) :
    algebraMap K L (Algebra.norm K x) =
      x ^ ∑ i ∈ Finset.range (Module.finrank K L), Fintype.card K ^ i := by
  rw [algebraMap_norm_eq_prod_pow, Finset.prod_pow_eq_pow_sum]

end FiniteField
