/-
Copyright (c) 2025 X. Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

/-!
# CM-extension of number fields

A CM-extension of number fields is a totally complex number field that is a quadratic extension of
a totally real number field. In this situation, the totally real number is the maximal real
subfield.

## Main definitions

* `maximalRealSubfield`: the maximal real subfield of a number field.

-/

open NumberField InfinitePlace ComplexEmbedding

namespace NumberField

section maximalRealSubfield

variable (K : Type*) [Field K] [NumberField K]

/--
The maximal real subfield of `K`. It is totally real, see `isTotallyReal_maximalRealSubfield`, and
contains all the other totally real subfields of `K`, see `IsTotallyReal.le_maximalRealSubfield`.
-/
def maximalRealSubfield : Subfield K where
  carrier := {x | ∀ φ : K →+* ℂ, star (φ x) = φ x}
  mul_mem' hx hy _ := by rw [map_mul, star_mul, hx, hy, mul_comm]
  one_mem' := by simp
  add_mem' hx hy _ := by rw [map_add, star_add, hx, hy]
  zero_mem' := by simp
  neg_mem' := by simp
  inv_mem' := by simp

instance isTotallyReal_maximalRealSubfield :
    IsTotallyReal (maximalRealSubfield K) where
  isReal w := by
    rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    letI := w.embedding.toAlgebra
    -- We provide some hints to Lean otherwise elaboration takes quite a long time
    let φ : K →+* ℂ := (@IsAlgClosed.lift ℂ _ _ (maximalRealSubfield K) _ K _ _ _ _
      NoZeroSMulDivisors.instOfFaithfulSMul NoZeroSMulDivisors.instOfFaithfulSMul).toRingHom
    have hφ {x} : w.embedding x = φ x :=
      (RingHom.congr_fun (AlgHom.comp_algebraMap_of_tower (maximalRealSubfield K)
        IsAlgClosed.lift) x).symm
    ext x
    rw [RingHom.star_apply, hφ, x.prop]

theorem IsTotallyReal.le_maximalRealSubfield {E : Subfield K} [h : IsTotallyReal E] :
    E ≤ maximalRealSubfield K := by
  intro x hx φ
  rw [show φ x = (φ.comp E.subtype) ⟨x, hx⟩ by rfl, RCLike.star_def, ← conjugate_coe_eq]
  refine RingHom.congr_fun ?_ _
  exact ComplexEmbedding.isReal_iff.mp  <|isReal_mk_iff.mp <| isReal _

end maximalRealSubfield

end NumberField
