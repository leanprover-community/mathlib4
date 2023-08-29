/-
Copyright (c) 2021 Eric Weiser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Algebra.Operations
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.RingTheory.Subring.Pointwise
import Mathlib.RingTheory.Adjoin.Basic

#align_import algebra.algebra.subalgebra.pointwise from "leanprover-community/mathlib"@"b2c707cd190a58ea0565c86695a19e99ccecc215"

/-!
# Pointwise actions on subalgebras.

If `R'` acts on an `R`-algebra `A` (so that `R'` and `R` actions commute)
then we get an `R'` action on the collection of `R`-subalgebras.
-/


namespace Subalgebra

section Pointwise

variable {R : Type*} {A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

theorem mul_toSubmodule_le (S T : Subalgebra R A) :
    (Subalgebra.toSubmodule S)* (Subalgebra.toSubmodule T) ≤ Subalgebra.toSubmodule (S ⊔ T) := by
  rw [Submodule.mul_le]
  -- ⊢ ∀ (m : A), m ∈ ↑toSubmodule S → ∀ (n : A), n ∈ ↑toSubmodule T → m * n ∈ ↑toS …
  intro y hy z hz
  -- ⊢ y * z ∈ ↑toSubmodule (S ⊔ T)
  show y * z ∈ S ⊔ T
  -- ⊢ y * z ∈ S ⊔ T
  exact mul_mem (Algebra.mem_sup_left hy) (Algebra.mem_sup_right hz)
  -- 🎉 no goals
#align subalgebra.mul_to_submodule_le Subalgebra.mul_toSubmodule_le

/-- As submodules, subalgebras are idempotent. -/
@[simp]
theorem mul_self (S : Subalgebra R A) : (Subalgebra.toSubmodule S) * (Subalgebra.toSubmodule S)
    = (Subalgebra.toSubmodule S) := by
  apply le_antisymm
  -- ⊢ ↑toSubmodule S * ↑toSubmodule S ≤ ↑toSubmodule S
  · refine' (mul_toSubmodule_le _ _).trans_eq _
    -- ⊢ ↑toSubmodule (S ⊔ S) = ↑toSubmodule S
    rw [sup_idem]
    -- 🎉 no goals
  · intro x hx1
    -- ⊢ x ∈ ↑toSubmodule S * ↑toSubmodule S
    rw [← mul_one x]
    -- ⊢ x * 1 ∈ ↑toSubmodule S * ↑toSubmodule S
    exact Submodule.mul_mem_mul hx1 (show (1 : A) ∈ S from one_mem S)
    -- 🎉 no goals
#align subalgebra.mul_self Subalgebra.mul_self

/-- When `A` is commutative, `Subalgebra.mul_toSubmodule_le` is strict. -/
theorem mul_toSubmodule {R : Type*} {A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (S T : Subalgebra R A) : (Subalgebra.toSubmodule S) * (Subalgebra.toSubmodule T)
        = Subalgebra.toSubmodule (S ⊔ T) := by
  refine' le_antisymm (mul_toSubmodule_le _ _) _
  -- ⊢ ↑toSubmodule (S ⊔ T) ≤ ↑toSubmodule S * ↑toSubmodule T
  rintro x (hx : x ∈ Algebra.adjoin R (S ∪ T : Set A))
  -- ⊢ x ∈ ↑toSubmodule S * ↑toSubmodule T
  refine'
    Algebra.adjoin_induction hx (fun x hx => _) (fun r => _) (fun _ _ => Submodule.add_mem _)
      fun x y hx hy => _
  · cases' hx with hxS hxT
    -- ⊢ x ∈ ↑toSubmodule S * ↑toSubmodule T
    · rw [← mul_one x]
      -- ⊢ x * 1 ∈ ↑toSubmodule S * ↑toSubmodule T
      exact Submodule.mul_mem_mul hxS (show (1 : A) ∈ T from one_mem T)
      -- 🎉 no goals
    · rw [← one_mul x]
      -- ⊢ 1 * x ∈ ↑toSubmodule S * ↑toSubmodule T
      exact Submodule.mul_mem_mul (show (1 : A) ∈ S from one_mem S) hxT
      -- 🎉 no goals
  · rw [← one_mul (algebraMap _ _ _)]
    -- ⊢ 1 * ↑(algebraMap R A) r ∈ ↑toSubmodule S * ↑toSubmodule T
    exact Submodule.mul_mem_mul (show (1 : A) ∈ S from one_mem S) (algebraMap_mem T _)
    -- 🎉 no goals
  have := Submodule.mul_mem_mul hx hy
  -- ⊢ x * y ∈ ↑toSubmodule S * ↑toSubmodule T
  rwa [mul_assoc, mul_comm _ (Subalgebra.toSubmodule T), ← mul_assoc _ _ (Subalgebra.toSubmodule S),
    mul_self, mul_comm (Subalgebra.toSubmodule T), ← mul_assoc, mul_self] at this
#align subalgebra.mul_to_submodule Subalgebra.mul_toSubmodule

variable {R' : Type*} [Semiring R'] [MulSemiringAction R' A] [SMulCommClass R' R A]

/-- The action on a subalgebra corresponding to applying the action to every element.

This is available as an instance in the `pointwise` locale. -/
protected def pointwiseMulAction : MulAction R' (Subalgebra R A)
    where
  smul a S := S.map (MulSemiringAction.toAlgHom _ _ a)
  one_smul S := (congr_arg (fun f => S.map f) (AlgHom.ext <| one_smul R')).trans S.map_id
  mul_smul _a₁ _a₂ S :=
    (congr_arg (fun f => S.map f) (AlgHom.ext <| mul_smul _ _)).trans (S.map_map _ _).symm
#align subalgebra.pointwise_mul_action Subalgebra.pointwiseMulAction

scoped[Pointwise] attribute [instance] Subalgebra.pointwiseMulAction

open Pointwise

@[simp]
theorem coe_pointwise_smul (m : R') (S : Subalgebra R A) : ↑(m • S) = m • (S : Set A) :=
  rfl
#align subalgebra.coe_pointwise_smul Subalgebra.coe_pointwise_smul

@[simp]
theorem pointwise_smul_toSubsemiring (m : R') (S : Subalgebra R A) :
    (m • S).toSubsemiring = m • S.toSubsemiring :=
  rfl
#align subalgebra.pointwise_smul_to_subsemiring Subalgebra.pointwise_smul_toSubsemiring

@[simp]
theorem pointwise_smul_toSubmodule (m : R') (S : Subalgebra R A) :
    Subalgebra.toSubmodule (m • S) = m • Subalgebra.toSubmodule S :=
  rfl
#align subalgebra.pointwise_smul_to_submodule Subalgebra.pointwise_smul_toSubmodule

@[simp]
theorem pointwise_smul_toSubring {R' R A : Type*} [Semiring R'] [CommRing R] [Ring A]
    [MulSemiringAction R' A] [Algebra R A] [SMulCommClass R' R A] (m : R') (S : Subalgebra R A) :
    (m • S).toSubring = m • S.toSubring :=
  rfl
#align subalgebra.pointwise_smul_to_subring Subalgebra.pointwise_smul_toSubring

theorem smul_mem_pointwise_smul (m : R') (r : A) (S : Subalgebra R A) : r ∈ S → m • r ∈ m • S :=
  (Set.smul_mem_smul_set : _ → _ ∈ m • (S : Set A))
#align subalgebra.smul_mem_pointwise_smul Subalgebra.smul_mem_pointwise_smul

end Pointwise

end Subalgebra
