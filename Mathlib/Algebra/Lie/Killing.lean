/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Lie.Nilpotent
import Mathlib.Algebra.Lie.Semisimple
import Mathlib.LinearAlgebra.PID
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
 * `LieModule.traceForm_eq_zero_of_isNilpotent`
 * `killingForm`
 * `LieAlgebra.IsKilling`
 * `LieAlgebra.IsKilling.isSemisimple`

## TODO

 * Prove that in characteristic zero, a semisimple Lie algebra has non-singular Killing form.
 * If the Killing form is non-degenerate, then so is its restriction to a Cartan subalgebra.
-/

variable (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [Module.Free R M] [Module.Finite R M]

local notation "φ" => LieModule.toEndomorphism R L M

open LinearMap (trace)

namespace LieModule

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
  · simp only [sub_mul, mul_sub, map_sub, mul_assoc]
  · simp only [LinearMap.trace_mul_cycle' R (φ x) (φ z) (φ y)]
  · simp only [traceForm_apply_apply, LieHom.map_lie, Ring.lie_def, mul_sub, map_sub,
      ← LinearMap.mul_eq_comp]

@[simp] lemma traceForm_eq_zero_of_isNilpotent [IsReduced R] [IsNilpotent R L M] :
    traceForm R L M = 0 := by
  ext x y
  simp only [traceForm_apply_apply, LinearMap.zero_apply, ← isNilpotent_iff_eq_zero]
  apply LinearMap.isNilpotent_trace_of_isNilpotent
  exact isNilpotent_toEndomorphism_of_isNilpotent₂ R L M x y

-- This is barely worth having: it usually follows from `LieModule.traceForm_eq_zero_of_isNilpotent`
@[simp] lemma traceForm_eq_zero_of_isTrivial [IsTrivial L M] :
    traceForm R L M = 0 := by
  ext x y
  suffices φ x ∘ₗ φ y = 0 by simp [this]
  ext m
  simp

end LieModule

namespace LieSubmodule

open LieModule (traceForm)

variable {R L M}
variable [IsDomain R] [IsPrincipalIdealRing R]
  (N : LieSubmodule R L M) (I : LieIdeal R L) (h : I ≤ N.idealizer) (x : L) {y : L} (hy : y ∈ I)

lemma trace_eq_trace_restrict_of_le_idealizer
    (hy' : ∀ m ∈ N, (φ x ∘ₗ φ y) m ∈ N := fun m _ ↦ N.lie_mem (N.mem_idealizer.mp (h hy) m)) :
    trace R M (φ x ∘ₗ φ y) = trace R N ((φ x ∘ₗ φ y).restrict hy') := by
  suffices ∀ m, ⁅x, ⁅y, m⁆⁆ ∈ N by simp [(φ x ∘ₗ φ y).trace_restrict_eq_of_forall_mem _ this]
  exact fun m ↦ N.lie_mem (h hy m)

lemma traceForm_eq_of_le_idealizer :
    traceForm R I N = (traceForm R L M).compl₁₂ I.subtype I.subtype := by
  ext ⟨x, hx⟩ ⟨y, hy⟩
  change _ = trace R M (φ x ∘ₗ φ y)
  rw [N.trace_eq_trace_restrict_of_le_idealizer I h x hy]
  rfl

/-- Note that this result is slightly stronger than it might look at first glance: we only assume
that `N` is trivial over `I` rather than all of `L`. This means that it applies in the important
case of an Abelian ideal (which has `M = L` and `N = I`). -/
lemma traceForm_eq_zero_of_isTrivial [LieModule.IsTrivial I N] :
    trace R M (φ x ∘ₗ φ y) = 0 := by
  let hy' : ∀ m ∈ N, (φ x ∘ₗ φ y) m ∈ N := fun m _ ↦ N.lie_mem (N.mem_idealizer.mp (h hy) m)
  suffices : (φ x ∘ₗ φ y).restrict hy' = 0
  · simp [this, N.trace_eq_trace_restrict_of_le_idealizer I h x hy]
  ext n
  suffices ⁅y, (n : M)⁆ = 0 by simp [this]
  exact Submodule.coe_eq_zero.mpr (LieModule.IsTrivial.trivial (⟨y, hy⟩ : I) n)

end LieSubmodule

section LieAlgebra

variable [Module.Free R L] [Module.Finite R L] [IsDomain R] [IsPrincipalIdealRing R]

/-- A finite, free (as an `R`-module) Lie algebra `L` carries a bilinear form on `L`.

This is a specialisation of `LieModule.traceForm` to the adjoint representation of `L`. -/
noncomputable abbrev killingForm : L →ₗ[R] L →ₗ[R] R := LieModule.traceForm R L L

namespace LieIdeal

variable (I : LieIdeal R L)

/-- The orthogonal complement of an ideal with respect to the killing form is an ideal. -/
noncomputable def killingCompl : LieIdeal R L :=
  { LinearMap.ker ((killingForm R L).compl₁₂ LinearMap.id I.subtype) with
    lie_mem := by
      intro x y hy
      ext ⟨z, hz⟩
      suffices killingForm R L ⁅x, y⁆ z = 0 by simpa
      rw [LieModule.traceForm_comm, ← LieModule.traceForm_apply_lie_apply, LieModule.traceForm_comm]
      simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
        Submodule.mem_toAddSubmonoid, LinearMap.mem_ker] at hy
      replace hy := LinearMap.congr_fun hy ⟨⁅z, x⁆, lie_mem_left R L I z x hz⟩
      simpa using hy }

@[simp] lemma mem_killingCompl {x : L} :
    x ∈ I.killingCompl ↔ ∀ y ∈ I, killingForm R L x y = 0 := by
  change x ∈ LinearMap.ker ((killingForm R L).compl₁₂ LinearMap.id I.subtype) ↔ _
  simp only [LinearMap.mem_ker, LieModule.traceForm_apply_apply, LinearMap.ext_iff,
    LinearMap.compl₁₂_apply, LinearMap.id_coe, id_eq, Submodule.coeSubtype,
    LieModule.traceForm_apply_apply, LinearMap.zero_apply, Subtype.forall]
  rfl

lemma killingForm_eq :
    killingForm R I = (killingForm R L).compl₁₂ I.subtype I.subtype :=
  LieSubmodule.traceForm_eq_of_le_idealizer I I $ by simp

@[simp] lemma le_killingCompl_top_of_isLieAbelian [IsLieAbelian I] :
    I ≤ LieIdeal.killingCompl R L ⊤ := by
  intro x (hx : x ∈ I)
  simp only [mem_killingCompl, LieSubmodule.mem_top, forall_true_left]
  intro y
  rw [LieModule.traceForm_comm, LieModule.traceForm_apply_apply]
  exact LieSubmodule.traceForm_eq_zero_of_isTrivial I I (by simp) _ hx

end LieIdeal

namespace LieAlgebra

/-- We say a Lie algebra is Killing if its Killing form is non-singular.

NB: The is not standard terminology (the literature does not seem to name Lie algebras with this
property). -/
class IsKilling : Prop :=
  /-- We say a Lie algebra is Killing if its Killing form is non-singular. -/
  killingCompl_top_eq_bot : LieIdeal.killingCompl R L ⊤ = ⊥

/-- The converse of this is true over a field of characteristic zero. There are counterexamples
over fields with positive characteristic. -/
instance IsKilling.isSemisimple [IsKilling R L] : IsSemisimple R L := by
  refine' (isSemisimple_iff_no_abelian_ideals R L).mpr fun I hI ↦ _
  rw [eq_bot_iff, ← IsKilling.killingCompl_top_eq_bot]
  exact I.le_killingCompl_top_of_isLieAbelian

-- TODO: formalize a positive-characteristic counterexample to the above instance

end LieAlgebra

end LieAlgebra
