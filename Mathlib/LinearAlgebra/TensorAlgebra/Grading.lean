/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.LinearAlgebra.TensorAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Basic

#align_import linear_algebra.tensor_algebra.grading from "leanprover-community/mathlib"@"2a7ceb0e411e459553a303d48eecdbb8553bd7ed"

/-!
# Results about the grading structure of the tensor algebra

The main result is `TensorAlgebra.gradedAlgebra`, which says that the tensor algebra is a
ℕ-graded algebra.
-/


namespace TensorAlgebra

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

open scoped DirectSum

variable (R M)

/-- A version of `TensorAlgebra.ι` that maps directly into the graded structure. This is
primarily an auxiliary construction used to provide `TensorAlgebra.gradedAlgebra`. -/
nonrec def GradedAlgebra.ι : M →ₗ[R] ⨁ i : ℕ, ↥(LinearMap.range (ι R : M →ₗ[_] _) ^ i) :=
  DirectSum.lof R ℕ (fun i => ↥(LinearMap.range (ι R : M →ₗ[_] _) ^ i)) 1 ∘ₗ
    (ι R).codRestrict _ fun m => by simpa only [pow_one] using LinearMap.mem_range_self _ m
                                    -- 🎉 no goals
#align tensor_algebra.graded_algebra.ι TensorAlgebra.GradedAlgebra.ι

theorem GradedAlgebra.ι_apply (m : M) :
    GradedAlgebra.ι R M m =
      DirectSum.of (fun (i : ℕ) => ↥(LinearMap.range (TensorAlgebra.ι R : M →ₗ[_] _) ^ i)) 1
        ⟨TensorAlgebra.ι R m, by simpa only [pow_one] using LinearMap.mem_range_self _ m⟩ :=
                                 -- 🎉 no goals
  rfl
#align tensor_algebra.graded_algebra.ι_apply TensorAlgebra.GradedAlgebra.ι_apply

variable {R M}

/-- The tensor algebra is graded by the powers of the submodule `(TensorAlgebra.ι R).range`. -/
instance gradedAlgebra :
    GradedAlgebra ((LinearMap.range (ι R : M →ₗ[R] TensorAlgebra R M) ^ ·) : ℕ → Submodule R _) :=
  GradedAlgebra.ofAlgHom _ (lift R <| GradedAlgebra.ι R M)
    (by
      ext m
      -- ⊢ ↑(LinearMap.comp (AlgHom.toLinearMap (AlgHom.comp (DirectSum.coeAlgHom fun x …
      dsimp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply,
        AlgHom.id_apply]
      rw [lift_ι_apply, GradedAlgebra.ι_apply R M, DirectSum.coeAlgHom_of, Subtype.coe_mk])
      -- 🎉 no goals
    fun i x => by
    cases' x with x hx
    -- ⊢ ↑(↑(lift R) (GradedAlgebra.ι R M)) ↑{ val := x, property := hx } = ↑(DirectS …
    dsimp only [Subtype.coe_mk, DirectSum.lof_eq_of]
    -- ⊢ ↑(↑(lift R) (GradedAlgebra.ι R M)) x = ↑(DirectSum.of (fun i => { x // x ∈ L …
    -- porting note: use new `induction using` support that failed in Lean 3
    induction hx using Submodule.pow_induction_on_left' with
    | hr r =>
      rw [AlgHom.commutes, DirectSum.algebraMap_apply]; rfl
    | hadd x y i hx hy ihx ihy =>
      rw [AlgHom.map_add, ihx, ihy, ← map_add]; rfl
    | hmul m hm i x hx ih =>
      obtain ⟨_, rfl⟩ := hm
      rw [AlgHom.map_mul, ih, lift_ι_apply, GradedAlgebra.ι_apply R M, DirectSum.of_mul_of]
      exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.subtype_ext (add_comm _ _) rfl)
#align tensor_algebra.graded_algebra TensorAlgebra.gradedAlgebra

end TensorAlgebra
