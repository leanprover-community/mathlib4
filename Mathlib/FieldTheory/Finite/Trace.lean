/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.RingTheory.Trace
import Mathlib.FieldTheory.Finite.GaloisField

#align_import field_theory.finite.trace from "leanprover-community/mathlib"@"0723536a0522d24fc2f159a096fb3304bef77472"

/-!
# The trace map for finite fields

We state the fact that the trace map from a finite field of
characteristic `p` to `ZMod p` is nondegenerate.

## Tags
finite field, trace
-/


namespace FiniteField

/-- The trace map from a finite field to its prime field is nongedenerate. -/
theorem trace_to_zmod_nondegenerate (F : Type*) [Field F] [Finite F]
    [Algebra (ZMod (ringChar F)) F] {a : F} (ha : a ≠ 0) :
    ∃ b : F, Algebra.trace (ZMod (ringChar F)) F (a * b) ≠ 0 := by
  haveI : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F _⟩
  -- ⊢ ∃ b, ↑(Algebra.trace (ZMod (ringChar F)) F) (a * b) ≠ 0
  have htr := traceForm_nondegenerate (ZMod (ringChar F)) F a
  -- ⊢ ∃ b, ↑(Algebra.trace (ZMod (ringChar F)) F) (a * b) ≠ 0
  simp_rw [Algebra.traceForm_apply] at htr
  -- ⊢ ∃ b, ↑(Algebra.trace (ZMod (ringChar F)) F) (a * b) ≠ 0
  by_contra' hf
  -- ⊢ False
  exact ha (htr hf)
  -- 🎉 no goals
#align finite_field.trace_to_zmod_nondegenerate FiniteField.trace_to_zmod_nondegenerate

end FiniteField
