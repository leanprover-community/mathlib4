/-
Copyright (c) 2024 Wanyi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wanyi He
-/
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.CharP.Algebra

variable {D : Type*} [DivisionRing D]

local notation "k" => (Subring.center D)

instance {p : ℕ} [CharP D p] : CharP (D →ₗ[k] D) p :=
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
    have eq : ∀ x : D, (f x) 1 = x := fun x => by
      simp only [Subring.center_toSubsemiring, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
        LinearMap.coe_mk, AddHom.coe_mk, mul_one, f]
    rw [← eq x, ← eq y]
    exact congrFun (congrArg DFunLike.coe h) 1
  charP_of_injective_ringHom inj p
