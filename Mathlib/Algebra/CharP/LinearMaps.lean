/-
Copyright (c) 2024 **ALL YOUR NAMES**. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: **ALL YOUR NAMES**
-/

import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.CharP.Algebra

variable {D : Type*} [DivisionRing D]

local notation "k" => (Subring.center D)


instance {p : ℕ} [Fact p.Prime] [CharP D p] : CharP (D →ₗ[k] D) p := by
  let f : D →+* (D →ₗ[k] D) := {
      toFun := fun a => {
        toFun := fun x => a * x
        map_add' := fun x y ↦ LeftDistribClass.left_distrib a x y
        map_smul' := fun m x ↦ mul_smul_comm m a x
      }
      map_one' := LinearMap.ext fun x ↦ one_mul x
      map_mul' := fun x y => LinearMap.ext fun z ↦ mul_assoc x y z
      map_zero' := LinearMap.ext fun x ↦ zero_mul x
      map_add' := fun x y => LinearMap.ext fun z ↦ add_mul x y z
    }
  have inj : Function.Injective f := by
    intros x y h
    have eq : ∀ x : D, (f x) 1 = x := by
      intro x
      have : f x = fun a : D => x * a := by rfl
      rw [this]
      simp only [mul_one]
    rw [← eq x, ← eq y]
    exact congrFun (congrArg DFunLike.coe h) 1
  apply charP_of_injective_ringHom inj
