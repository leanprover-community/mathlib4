/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Lie.Nilpotent
import Mathlib.LinearAlgebra.Trace

/-!
# The trace and Killing forms of a Lie algebra.

Let `L` be a Lie algebra with coefficients in a commutative ring `R`. Suppose `M` is a finite, free
`R`-module and we have a representation `φ : L → End M`. This data induces a natural bilinear form
`B` on `L`, called the trace form associated to `M`; it is defined as `B(x, y) = Tr (φ x) (φ y)`.

In the special case that `M` is `L` itself and `φ` is the adjoint representation, the trace form
is known as the Killing form.

We define the trace / Killing form in this file and prove some basic properties.

## Main definitions

 * `LieModule.traceForm`
 * `killingForm`

## TODO

 * Show that `LieModule.traceForm R L M` vanishes when `M` is nilpotent (using
   `isNilpotent_toEndomorphism_of_isNilpotent₂`).
 * Prove Cartan's criterion for semisimplicity.
-/

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

namespace LieModule

open LinearMap (trace)

variable (M : Type _) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable [Module.Free R M] [Module.Finite R M]

local notation "φ" => toEndomorphism R L M

/-- A finite, free representation of a Lie algebra `L` induces a bilinear form on `L` called
the trace Form. See also `killingForm`. -/
noncomputable def traceForm : L →ₗ[R] L →ₗ[R] R :=
  ((LinearMap.mul _ _).compl₁₂ (φ).toLinearMap (φ).toLinearMap).compr₂ (trace R M)

@[simp] lemma traceForm_apply_apply (x y : L) :
    traceForm R L M x y = trace R _ (φ x ∘ₗ φ y) :=
  rfl

lemma traceForm_comm (x y : L) : traceForm R L M x y = traceForm R L M y x :=
  LinearMap.trace_mul_comm R (φ x) (φ y)

@[simp] lemma traceForm_flip : (traceForm R L M).flip = traceForm R L M :=
  Eq.symm <| LinearMap.ext₂ <| traceForm_comm R L M

lemma traceForm_apply_lie_apply (x y z : L) :
    traceForm R L M ⁅x, y⁆ z = traceForm R L M x ⁅y, z⁆ := by
  calc traceForm R L M ⁅x, y⁆ z
      = trace R _ (φ ⁅x, y⁆ ∘ₗ φ z) := by simp only [traceForm_apply_apply]
    _ = trace R _ ((φ x * φ y - φ y * φ x) * φ z) := ?_
    _ = trace R _ (φ x * (φ y * φ z)) - trace R _ (φ y * (φ x * φ z)) := ?_
    _ = trace R _ (φ x * (φ y * φ z)) - trace R _ (φ x * (φ z * φ y)) := ?_
    _ = traceForm R L M x ⁅y, z⁆ := ?_
  · simp only [LieHom.map_lie, Ring.lie_def, ← LinearMap.mul_eq_comp]
    -- 🎉 no goals
  · simp only [sub_mul, mul_sub, map_sub, mul_assoc]
    -- 🎉 no goals
  · simp only [LinearMap.trace_mul_cycle' R (φ x) (φ z) (φ y)]
    -- 🎉 no goals
  · simp only [traceForm_apply_apply, LieHom.map_lie, Ring.lie_def, mul_sub, map_sub,
      ← LinearMap.mul_eq_comp]

end LieModule

section LieAlgebra

variable [Module.Free R L] [Module.Finite R L]

/-- A finite, free (as an `R`-module) Lie algebra `L` carries a bilinear form on `L`.

This is a specialisation of `LieModule.traceForm` to the adjoint representation of `L`. -/
noncomputable abbrev killingForm : L →ₗ[R] L →ₗ[R] R := LieModule.traceForm R L L

end LieAlgebra
