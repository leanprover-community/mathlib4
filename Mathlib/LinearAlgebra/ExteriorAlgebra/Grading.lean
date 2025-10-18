/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Basic

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
protected def GradedAlgebra.ι :
    M →ₗ[R] ⨁ i : ℕ, ⋀[R]^i M :=
  DirectSum.lof R ℕ (fun i => ⋀[R]^i M) 1 ∘ₗ
    (ι R).codRestrict _ fun m => by simpa only [pow_one] using LinearMap.mem_range_self _ m

theorem GradedAlgebra.ι_apply (m : M) :
    GradedAlgebra.ι R M m =
      DirectSum.of (fun i : ℕ => ⋀[R]^i M) 1
        ⟨ι R m, by simpa only [pow_one] using LinearMap.mem_range_self _ m⟩ :=
  rfl

-- Defining this instance manually, because Lean doesn't seem to be able to synthesize it.
-- Strangely, this problem only appears when we use the abbreviation or notation for the
-- exterior powers.
instance : SetLike.GradedMonoid fun i : ℕ ↦ ⋀[R]^i M :=
  Submodule.nat_power_gradedMonoid (LinearMap.range (ι R : M →ₗ[R] ExteriorAlgebra R M))

theorem GradedAlgebra.ι_sq_zero (m : M) : GradedAlgebra.ι R M m * GradedAlgebra.ι R M m = 0 := by
  rw [GradedAlgebra.ι_apply, DirectSum.of_mul_of]
  exact DFinsupp.single_eq_zero.mpr (Subtype.ext <| ExteriorAlgebra.ι_sq_zero _)

/-- `ExteriorAlgebra.GradedAlgebra.ι` lifted to exterior algebra. This is
primarily an auxiliary construction used to provide `ExteriorAlgebra.gradedAlgebra`. -/
def GradedAlgebra.liftι :
    ExteriorAlgebra R M →ₐ[R] ⨁ i : ℕ, ⋀[R]^i M :=
  lift R ⟨by apply GradedAlgebra.ι R M, GradedAlgebra.ι_sq_zero R M⟩

theorem GradedAlgebra.liftι_eq (i : ℕ) (x : ⋀[R]^i M) :
    GradedAlgebra.liftι R M x = DirectSum.of (fun i => ⋀[R]^i M) i x := by
  obtain ⟨x, hx⟩ := x
  dsimp only [Subtype.coe_mk, DirectSum.lof_eq_of]
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap => simp_rw [AlgHom.commutes, DirectSum.algebraMap_apply]; rfl
  | add _ _ _ _ _ ihx ihy => simp_rw [map_add, ihx, ihy, ← AddMonoidHom.map_add]; rfl
  | mem_mul _ hm _ _ _ ih =>
      obtain ⟨_, rfl⟩ := hm
      simp_rw [map_mul, ih, GradedAlgebra.liftι, lift_ι_apply, GradedAlgebra.ι_apply R M,
        DirectSum.of_mul_of]
      exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.subtype_ext (add_comm _ _) rfl)

/-- The exterior algebra is graded by the powers of the submodule `(ExteriorAlgebra.ι R).range`. -/
instance gradedAlgebra : GradedAlgebra (fun i : ℕ ↦ ⋀[R]^i M) :=
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

/-- The union of the images of the maps `ExteriorAlgebra.ιMulti R n` for `n` running through
all natural numbers spans the exterior algebra. -/
lemma ιMulti_span :
    Submodule.span R (Set.range fun x : Σ n, (Fin n → M) => ιMulti R x.1 x.2) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  induction x using DirectSum.Decomposition.inductionOn fun i => ⋀[R]^i M with
  | zero => exact Submodule.zero_mem _
  | add _ _ hm hm' => exact Submodule.add_mem _ hm hm'
  | homogeneous hm =>
    let ⟨m, hm⟩ := hm
    apply Set.mem_of_mem_of_subset hm
    rw [← ιMulti_span_fixedDegree]
    refine Submodule.span_mono fun _ hx ↦ ?_
    obtain ⟨y, rfl⟩ := hx
    exact ⟨⟨_, y⟩, rfl⟩

end ExteriorAlgebra
