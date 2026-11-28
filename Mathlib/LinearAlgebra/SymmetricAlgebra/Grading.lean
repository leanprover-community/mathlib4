/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Grading of the symmetric algebra

This file shows that the symmetric algebra `SymmetricAlgebra R M` is `ℕ`-graded, the component of
degree `n` being the `n`-th power of the image of `SymmetricAlgebra.ι R M`.

## Main results

* `SymmetricAlgebra.gradedAlgebra`: `SymmetricAlgebra R M` is a `GradedAlgebra` for the family
  `n ↦ LinearMap.range (ι R M) ^ n`.
-/

@[expose] public section

open scoped DirectSum

namespace SymmetricAlgebra

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The symmetric algebra is graded by the powers of the image of `SymmetricAlgebra.ι R M`. -/
instance gradedAlgebra :
    GradedAlgebra ((LinearMap.range (ι R M) ^ ·) : ℕ → Submodule R (SymmetricAlgebra R M)) :=
  fast_instance% GradedAlgebra.ofAlgHom _
    (lift <| DirectSum.lof R ℕ (fun i => ↥(LinearMap.range (ι R M) ^ i)) 1 ∘ₗ
      (ι R M).codRestrict _ fun m => by simpa only [pow_one] using LinearMap.mem_range_self _ m)
    (algHom_ext <| LinearMap.ext fun m => by simp [DirectSum.lof_eq_of])
    fun i x => by
    obtain ⟨x, hx⟩ := x
    dsimp only [Subtype.coe_mk, DirectSum.lof_eq_of]
    induction hx using Submodule.pow_induction_on_left' with
    | algebraMap r =>
      rw [AlgHom.commutes, DirectSum.algebraMap_apply]; rfl
    | add x y i hx hy ihx ihy =>
      rw [map_add, ihx, ihy, ← map_add]
      rfl
    | mem_mul m hm i x hx ih =>
      obtain ⟨_, rfl⟩ := hm
      rw [map_mul, ih, lift_ι_apply, LinearMap.comp_apply, DirectSum.lof_eq_of, DirectSum.of_mul_of]
      exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.subtype_ext (add_comm _ _) rfl)

end SymmetricAlgebra

end
