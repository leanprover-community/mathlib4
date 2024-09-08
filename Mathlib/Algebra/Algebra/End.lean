/-
Copyright (c) XXX. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XXX
-/

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.PUnitInstances.Algebra -- XXX rm
import Mathlib.Tactic.ApplyFun

/-!
# XXX
-/

universe u v w u₁ v₁

open scoped Algebra

namespace Module

variable (R : Type u) (S : Type v) (M : Type w)
variable [CommSemiring R] [Semiring S] [AddCommMonoid M] [Module R M] [Module S M]
variable [SMulCommClass S R M] [SMul R S] [IsScalarTower R S M]

instance End.instAlgebra : Algebra R (Module.End S M) :=
  Algebra.ofModule smul_mul_assoc fun r f g => (smul_comm r f g).symm

-- to prove this is a special case of the above
example : Algebra R (Module.End R M) := End.instAlgebra _ _ _

theorem algebraMap_end_eq_smul_id (a : R) : algebraMap R (End S M) a = a • LinearMap.id :=
  rfl

@[simp]
theorem algebraMap_end_apply (a : R) (m : M) : algebraMap R (End S M) a m = a • m :=
  rfl

@[simp]
theorem ker_algebraMap_end (K : Type u) (V : Type v) [Field K] [AddCommGroup V] [Module K V] (a : K)
    (ha : a ≠ 0) : LinearMap.ker ((algebraMap K (End K V)) a) = ⊥ :=
  LinearMap.ker_smul _ _ ha

section

variable {R M}

theorem End_algebraMap_isUnit_inv_apply_eq_iff {x : R}
    (h : IsUnit (algebraMap R (Module.End S M) x)) (m m' : M) :
    (↑(h.unit⁻¹) : Module.End S M) m = m' ↔ m = x • m' :=
  { mp := fun H => ((congr_arg h.unit H).symm.trans (End_isUnit_apply_inv_apply_of_isUnit h _)).symm
    mpr := fun H =>
      H.symm ▸ by
        apply_fun ⇑h.unit.val using ((Module.End_isUnit_iff _).mp h).injective
        simpa using End_isUnit_apply_inv_apply_of_isUnit h (x • m') }

theorem End_algebraMap_isUnit_inv_apply_eq_iff' {x : R}
    (h : IsUnit (algebraMap R (Module.End S M) x)) (m m' : M) :
    m' = (↑h.unit⁻¹ : Module.End S M) m ↔ m = x • m' :=
  { mp := fun H => ((congr_arg h.unit H).trans (End_isUnit_apply_inv_apply_of_isUnit h _)).symm
    mpr := fun H =>
      H.symm ▸ by
        apply_fun (↑h.unit : M → M) using ((Module.End_isUnit_iff _).mp h).injective
        simpa using End_isUnit_apply_inv_apply_of_isUnit h (x • m') |>.symm }

end

end Module
