/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module linear_algebra.exterior_algebra.grading
! leanprover-community/mathlib commit 34020e531ebc4e8aac6d449d9eecbcd1508ea8d0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Results about the grading structure of the exterior algebra

Many of these results are copied with minimal modification from the tensor algebra.

The main result is `exterior_algebra.graded_algebra`, which says that the exterior algebra is a
ℕ-graded algebra.
-/


namespace ExteriorAlgebra

variable {R M : Type _} [CommRing R] [AddCommGroup M] [Module R M]

variable (R M)

open scoped DirectSum

/-- A version of `exterior_algebra.ι` that maps directly into the graded structure. This is
primarily an auxiliary construction used to provide `exterior_algebra.graded_algebra`. -/
def GradedAlgebra.ι : M →ₗ[R] ⨁ i : ℕ, ↥((ι R : M →ₗ[_] _).range ^ i) :=
  DirectSum.lof R ℕ (fun i => ↥((ι R : M →ₗ[_] _).range ^ i)) 1 ∘ₗ
    (ι R).codRestrict _ fun m => by simpa only [pow_one] using LinearMap.mem_range_self _ m
#align exterior_algebra.graded_algebra.ι ExteriorAlgebra.GradedAlgebra.ι

theorem GradedAlgebra.ι_apply (m : M) :
    GradedAlgebra.ι R M m =
      DirectSum.of (fun i => ↥((ι R : M →ₗ[_] _).range ^ i)) 1
        ⟨ι R m, by simpa only [pow_one] using LinearMap.mem_range_self _ m⟩ :=
  rfl
#align exterior_algebra.graded_algebra.ι_apply ExteriorAlgebra.GradedAlgebra.ι_apply

theorem GradedAlgebra.ι_sq_zero (m : M) : GradedAlgebra.ι R M m * GradedAlgebra.ι R M m = 0 := by
  rw [graded_algebra.ι_apply, DirectSum.of_mul_of]
  refine' dfinsupp.single_eq_zero.mpr (Subtype.ext <| ι_sq_zero _)
#align exterior_algebra.graded_algebra.ι_sq_zero ExteriorAlgebra.GradedAlgebra.ι_sq_zero

/-- `exterior_algebra.graded_algebra.ι` lifted to exterior algebra. This is
primarily an auxiliary construction used to provide `exterior_algebra.graded_algebra`. -/
def GradedAlgebra.liftι :
    ExteriorAlgebra R M →ₐ[R] ⨁ i : ℕ, ↥((ι R).range ^ i : Submodule R (ExteriorAlgebra R M)) :=
  lift R ⟨by apply graded_algebra.ι R M, GradedAlgebra.ι_sq_zero R M⟩
#align exterior_algebra.graded_algebra.lift_ι ExteriorAlgebra.GradedAlgebra.liftι

variable (R M)

theorem GradedAlgebra.liftι_eq (i : ℕ)
    (x : ((ι R : M →ₗ[R] ExteriorAlgebra R M).range ^ i : Submodule R (ExteriorAlgebra R M))) :
    GradedAlgebra.liftι R M x =
      DirectSum.of (fun i => ↥((ι R).range ^ i : Submodule R (ExteriorAlgebra R M))) i x := by
  cases' x with x hx
  dsimp only [Subtype.coe_mk, DirectSum.lof_eq_of]
  refine'
    Submodule.pow_induction_on_left' _ (fun r => _) (fun x y i hx hy ihx ihy => _)
      (fun m hm i x hx ih => _) hx
  · rw [AlgHom.commutes, DirectSum.algebraMap_apply]; rfl
  · rw [AlgHom.map_add, ihx, ihy, ← map_add]; rfl
  · obtain ⟨_, rfl⟩ := hm
    rw [AlgHom.map_mul, ih, graded_algebra.lift_ι, lift_ι_apply, graded_algebra.ι_apply R M,
      DirectSum.of_mul_of]
    exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.subtype_ext (add_comm _ _) rfl)
#align exterior_algebra.graded_algebra.lift_ι_eq ExteriorAlgebra.GradedAlgebra.liftι_eq

/-- The exterior algebra is graded by the powers of the submodule `(exterior_algebra.ι R).range`. -/
instance gradedAlgebra :
    GradedAlgebra ((· ^ ·) (ι R : M →ₗ[R] ExteriorAlgebra R M).range : ℕ → Submodule R _) :=
  GradedAlgebra.ofAlgHom _
    (-- while not necessary, the `by apply` makes this elaborate faster
    by apply graded_algebra.lift_ι R M)
    (-- the proof from here onward is identical to the `tensor_algebra` case by
      ext m
      dsimp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply,
        AlgHom.id_apply, graded_algebra.lift_ι]
      rw [lift_ι_apply, graded_algebra.ι_apply R M, DirectSum.coeAlgHom_of, Subtype.coe_mk])
    (by apply graded_algebra.lift_ι_eq R M)
#align exterior_algebra.graded_algebra ExteriorAlgebra.gradedAlgebra

end ExteriorAlgebra

