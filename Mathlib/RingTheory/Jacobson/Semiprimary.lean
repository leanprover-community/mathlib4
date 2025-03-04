/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.RingTheory.Jacobson.Radical
import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Semiprimary rings

## Main definition

* `IsSemiprimaryRing R`: a ring `R` is semiprimary if
  `Ring.jacobson R` is nilpotent and `R ⧸ Ring.jacobson R` is semisimple.
-/

variable (R R₂ M M₂ : Type*) [Ring R] [Ring R₂]
variable [AddCommGroup M] [Module R M] [AddCommGroup M₂] [Module R₂ M₂]
variable {τ₁₂ : R →+* R₂} [RingHomSurjective τ₁₂]
variable {F : Type*} [FunLike F M M₂] [SemilinearMapClass F τ₁₂ M M₂] (f : F)

theorem IsSimpleModule.jacobson_eq_bot [IsSimpleModule R M] : Module.jacobson R M = ⊥ :=
  le_bot_iff.mp <| sInf_le isCoatom_bot

theorem IsSemisimpleModule.jacobson_eq_bot [IsSemisimpleModule R M] :
    Module.jacobson R M = ⊥ :=
  have ⟨s, e, simple⟩ := isSemisimpleModule_iff_exists_linearEquiv_dfinsupp.mp ‹_›
  let f : M →ₗ[R] ∀ m : s, m.1 := (LinearMap.pi DFinsupp.lapply).comp e.toLinearMap
  Module.jacobson_eq_bot_of_injective f (DFinsupp.injective_pi_lapply (R := R).comp e.injective)
    (Module.jacobson_pi_eq_bot _ _ fun i ↦ IsSimpleModule.jacobson_eq_bot R _)

theorem IsSemisimpleRing.jacobson_eq_bot [IsSemisimpleRing R] : Ring.jacobson R = ⊥ :=
  IsSemisimpleModule.jacobson_eq_bot R R

theorem IsSemisimpleModule.jacobson_le_ker [IsSemisimpleModule R₂ M₂] :
    Module.jacobson R M ≤ LinearMap.ker f :=
  (Module.le_comap_jacobson f).trans <| by simp_rw [jacobson_eq_bot, LinearMap.ker, le_rfl]

/-- The Jacobson radical of a ring annihilates every semisimple module. -/
theorem IsSemisimpleModule.jacobson_le_annihilator [IsSemisimpleModule R M] :
    Ring.jacobson R ≤ Module.annihilator R M :=
  fun r hr ↦ Module.mem_annihilator.mpr fun m ↦ by
    have := Module.le_comap_jacobson (LinearMap.toSpanSingleton R M m) hr
    rwa [jacobson_eq_bot] at this

instance (priority := low) (R) [CommRing R] [IsSemisimpleRing R] : IsReduced R where
  eq_zero _ := fun ⟨n, eq⟩ ↦ (IsSemisimpleRing.jacobson_eq_bot R).le <| Ideal.mem_sInf.mpr
    fun I hI ↦ (Ideal.isMaximal_def.mpr hI).isPrime.mem_of_pow_mem n (eq ▸ I.zero_mem)

/-- A ring is semiprimary if its Jacobson radical is nilpotent and its quotient by the
Jacobson radical is semisimple. -/
@[mk_iff] class IsSemiprimaryRing : Prop where
  isSemisimpleRing : IsSemisimpleRing (R ⧸ Ring.jacobson R)
  isNilpotent : IsNilpotent (Ring.jacobson R)

attribute [instance] IsSemiprimaryRing.isSemisimpleRing
