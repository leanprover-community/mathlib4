/-
Copyright (c) 2023 Wen Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wen Yang
-/
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Projective Special Linear Group

## Notation

In the `MatrixGroups` locale:

* `PSL(n, R)` is a shorthand for `Matrix.ProjectiveSpecialLinearGroup (Fin n) R`
-/

namespace Matrix

universe u v

open Matrix LinearMap

open scoped MatrixGroups

variable (n : Type u) [DecidableEq n] [Fintype n] (R : Type v) [CommRing R]

/-- A projective special linear group is the quotient of a special linear group by its center.-/
abbrev ProjectiveSpecialLinearGroup : Type _ :=
    SpecialLinearGroup n R ⧸ Subgroup.center (SpecialLinearGroup n R)

/-- `PSL(n, R)` is the projective special linear group `SL(n, R)/Z(SL(n, R))`.-/
scoped[MatrixGroups] notation "PSL(" n ", " R ")" => Matrix.ProjectiveSpecialLinearGroup (Fin n) R

namespace ProjectiveSpecialLinearGroup

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R] [Inhabited n]
    {α : Type*}

/-- A version of `Quotient.liftOn'` specialized for projective special linear group.-/
def lift (f : SpecialLinearGroup n R → α)
    (hf : ∀ (A B : SpecialLinearGroup n R), ∀ (c : R),
    (c ^ Fintype.card n = 1 ∧ A.val = c • B.val) → f A = f B)
    (g : ProjectiveSpecialLinearGroup n R) : α :=
  Quotient.liftOn' g f fun A B hAB => by
    rw [@QuotientGroup.leftRel_apply] at hAB
    replace ⟨hc, hAB⟩ := SpecialLinearGroup.mem_center_iff.mp hAB
    set c := (A⁻¹ * B).val default default
    refine hf A B (c ^ (Fintype.card n - 1)) ⟨?hc, ?_⟩
    · rw [@pow_right_comm, hc, @one_pow]
    · replace hAB := congrArg (HSMul.hSMul <| c ^ (Fintype.card n - 1)) hAB
      rw [SpecialLinearGroup.coe_mul] at hAB
      have hn : 0 < Fintype.card n := Fintype.card_pos_iff.mpr instNonempty
      rw [@smul_smul, ← @pow_succ', Nat.sub_add_cancel hn, hc, one_smul, ← mul_smul_comm] at hAB
      have : A.val * A⁻¹.val * (c ^ (Fintype.card n - 1) • B.val) = A.val := by
        rw [mul_assoc, hAB, mul_one]
      rw [← this, ← @SpecialLinearGroup.coe_mul, @mul_inv_self,
          SpecialLinearGroup.coe_one, @Matrix.one_mul]

end ProjectiveSpecialLinearGroup
