/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.Algebra.GroupWithZero.Subgroup
import Mathlib.Algebra.Ring.Submonoid.Pointwise
import Mathlib.Algebra.Module.Defs

/-!
# Additive subgroups of rings
-/

open scoped Pointwise

variable {R M : Type*}

namespace AddSubgroup
section NonUnitalNonAssocRing
variable [NonUnitalNonAssocRing R]

/-- For additive subgroups `S` and `T` of a ring, the product of `S` and `T` as submonoids
is automatically a subgroup, which we define as the product of `S` and `T` as subgroups. -/
protected def mul : Mul (AddSubgroup R) where
  mul M N :=
  { __ := M.toAddSubmonoid * N.toAddSubmonoid
    neg_mem' := fun h ↦ AddSubmonoid.mul_induction_on h
      (fun m hm n hn ↦ by rw [← neg_mul]; exact AddSubmonoid.mul_mem_mul (M.neg_mem hm) hn)
      fun r₁ r₂ h₁ h₂ ↦ by rw [neg_add]; exact (M.1 * N.1).add_mem h₁ h₂ }

scoped[Pointwise] attribute [instance] AddSubgroup.mul

lemma mul_toAddSubmonoid (M N : AddSubgroup R) :
    (M * N).toAddSubmonoid = M.toAddSubmonoid * N.toAddSubmonoid := rfl

end NonUnitalNonAssocRing

section Semiring
variable [Semiring R] [AddCommGroup M] [Module R M]

@[simp] protected lemma zero_smul (s : AddSubgroup M) : (0 : R) • s = ⊥ := by
  simp [eq_bot_iff_forall, pointwise_smul_def]

end Semiring
end AddSubgroup
