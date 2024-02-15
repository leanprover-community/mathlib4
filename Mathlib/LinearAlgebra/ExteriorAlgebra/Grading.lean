/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Basic

#align_import linear_algebra.exterior_algebra.grading from "leanprover-community/mathlib"@"34020e531ebc4e8aac6d449d9eecbcd1508ea8d0"

/-!
# Results about the grading structure of the exterior algebra

Many of these results are copied with minimal modification from the tensor algebra.

The main result is `ExteriorAlgebra.gradedAlgebra`, which says that the exterior algebra is a
ℕ-graded algebra.
-/


namespace ExteriorAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

variable (R M)

open scoped DirectSum

/-- A version of `ExteriorAlgebra.ι` that maps directly into the graded structure. This is
primarily an auxiliary construction used to provide `ExteriorAlgebra.gradedAlgebra`. -/
-- porting note: protected
protected def GradedAlgebra.ι :
    M →ₗ[R] ⨁ i : ℕ, ↥(LinearMap.range (ι R : M →ₗ[R] ExteriorAlgebra R M) ^ i) :=
  DirectSum.lof R ℕ (fun i => ↥(LinearMap.range (ι R : M →ₗ[R] ExteriorAlgebra R M) ^ i)) 1 ∘ₗ
    (ι R).codRestrict _ fun m => by simpa only [pow_one] using LinearMap.mem_range_self _ m
#align exterior_algebra.graded_algebra.ι ExteriorAlgebra.GradedAlgebra.ι

theorem GradedAlgebra.ι_apply (m : M) :
    GradedAlgebra.ι R M m =
      DirectSum.of (fun i : ℕ => ↥(LinearMap.range (ι R : M →ₗ[R] ExteriorAlgebra R M) ^ i)) 1
        ⟨ι R m, by simpa only [pow_one] using LinearMap.mem_range_self _ m⟩ :=
  rfl
#align exterior_algebra.graded_algebra.ι_apply ExteriorAlgebra.GradedAlgebra.ι_apply

-- Porting note: Lean needs to be reminded of this instance otherwise it cannot
-- synthesize 0 in the next theorem
attribute [instance 1100] MulZeroClass.toZero in
theorem GradedAlgebra.ι_sq_zero (m : M) : GradedAlgebra.ι R M m * GradedAlgebra.ι R M m = 0 := by
  rw [GradedAlgebra.ι_apply, DirectSum.of_mul_of]
  refine DFinsupp.single_eq_zero.mpr (Subtype.ext <| ExteriorAlgebra.ι_sq_zero _)
#align exterior_algebra.graded_algebra.ι_sq_zero ExteriorAlgebra.GradedAlgebra.ι_sq_zero

/-- `ExteriorAlgebra.GradedAlgebra.ι` lifted to exterior algebra. This is
primarily an auxiliary construction used to provide `ExteriorAlgebra.gradedAlgebra`. -/
def GradedAlgebra.liftι :
    ExteriorAlgebra R M →ₐ[R] ⨁ i : ℕ,
    (LinearMap.range (ι R : M →ₗ[R] ExteriorAlgebra R M) ^ i : Submodule R (ExteriorAlgebra R M)) :=
  lift R ⟨by apply GradedAlgebra.ι R M, GradedAlgebra.ι_sq_zero R M⟩
#align exterior_algebra.graded_algebra.lift_ι ExteriorAlgebra.GradedAlgebra.liftι

theorem GradedAlgebra.liftι_eq (i : ℕ)
    (x : (LinearMap.range (ι R : M →ₗ[R] ExteriorAlgebra R M) ^ i :
      Submodule R (ExteriorAlgebra R M))) :
    GradedAlgebra.liftι R M x =
    DirectSum.of (fun i =>
      ↥(LinearMap.range (ι R : M →ₗ[R] ExteriorAlgebra R M) ^ i :
      Submodule R (ExteriorAlgebra R M))) i x := by
  cases' x with x hx
  dsimp only [Subtype.coe_mk, DirectSum.lof_eq_of]
  -- Porting note: original statement was
  --  refine Submodule.pow_induction_on_left' _ (fun r => ?_) (fun x y i hx hy ihx ihy => ?_)
  --    (fun m hm i x hx ih => ?_) hx
  -- but it created invalid goals
  induction hx using Submodule.pow_induction_on_left' with
  | hr => simp_rw [AlgHom.commutes, DirectSum.algebraMap_apply]; rfl
  -- FIXME: specialized `map_add` to avoid a (whole-declaration) timeout
  | hadd _ _ _ _ _ ihx ihy => simp_rw [AlgHom.map_add, ihx, ihy, ← AddMonoidHom.map_add]; rfl
  | hmul _ hm _ _ _ ih =>
      obtain ⟨_, rfl⟩ := hm
      simp_rw [AlgHom.map_mul, ih, GradedAlgebra.liftι, lift_ι_apply, GradedAlgebra.ι_apply R M,
        DirectSum.of_mul_of]
      exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.subtype_ext (add_comm _ _) rfl)
#align exterior_algebra.graded_algebra.lift_ι_eq ExteriorAlgebra.GradedAlgebra.liftι_eq

/-- The exterior algebra is graded by the powers of the submodule `(ExteriorAlgebra.ι R).range`. -/
instance gradedAlgebra :
    GradedAlgebra (LinearMap.range (ι R : M →ₗ[R] ExteriorAlgebra R M) ^ · : ℕ → Submodule R _) :=
  GradedAlgebra.ofAlgHom _
    (-- while not necessary, the `by apply` makes this elaborate faster
    by apply GradedAlgebra.liftι R M)
    -- the proof from here onward is identical to the `TensorAlgebra` case
    (by
      ext m
      dsimp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply,
        AlgHom.id_apply, GradedAlgebra.liftι]
      rw [lift_ι_apply, GradedAlgebra.ι_apply R M, DirectSum.coeAlgHom_of, Subtype.coe_mk])
    (by apply GradedAlgebra.liftι_eq R M)
#align exterior_algebra.graded_algebra ExteriorAlgebra.gradedAlgebra

end ExteriorAlgebra
