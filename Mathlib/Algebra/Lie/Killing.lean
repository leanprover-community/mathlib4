/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Lie.Semisimple
import Mathlib.Algebra.Lie.TraceForm

/-!
# Lie algebras with non-degenerate Killing forms.

In characteristic zero, the following three conditions are equivalent:
 1. The solvable radical of a Lie algebra is trivial
 2. A Lie algebra is a direct sum of its simple ideals
 3. A Lie algebra has non-degenerate Killing form

In positive characteristic, it is still true that 3 implies 2, and that 2 implies 1, but there are
counterexamples to the remaining implications. Thus condition 3 is the strongest assumption.
Furthermore, much of the Cartan-Killing classification of semisimple Lie algebras in characteristic
zero, continues to hold in positive characteristic (over a perfect field) if the Lie algebra has a
non-degenerate Killing form.

This file contains basic definitions and results for such Lie algebras.

## Main definitions
 * `LieAlgebra.IsKilling`: a typeclass encoding the fact that a Lie algebra has a non-singular
   Killing form.
 * `LieAlgebra.IsKilling.instIsSemisimple`: if a Lie algebra has non-singular Killing form then it
   is semisimple.

## TODO

 * Prove that in characteristic zero, a semisimple Lie algebra has non-singular Killing form.

-/

variable (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

namespace LieAlgebra

/-- We say a Lie algebra is Killing if its Killing form is non-singular.

NB: This is not standard terminology (the literature does not seem to name Lie algebras with this
property). -/
class IsKilling : Prop :=
  /-- We say a Lie algebra is Killing if its Killing form is non-singular. -/
  killingCompl_top_eq_bot : LieIdeal.killingCompl R L ⊤ = ⊥

attribute [simp] IsKilling.killingCompl_top_eq_bot

namespace IsKilling

variable [Module.Free R L] [Module.Finite R L] [IsKilling R L]

@[simp] lemma ker_killingForm_eq_bot :
    LinearMap.ker (killingForm R L) = ⊥ := by
  simp [← LieIdeal.coe_killingCompl_top, killingCompl_top_eq_bot]

lemma killingForm_nondegenerate :
    (killingForm R L).Nondegenerate := by
  simp [LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot]

/-- The converse of this is true over a field of characteristic zero. There are counterexamples
over fields with positive characteristic. -/
instance instIsSemisimple [IsDomain R] [IsPrincipalIdealRing R] : IsSemisimple R L := by
  refine' (isSemisimple_iff_no_abelian_ideals R L).mpr fun I hI ↦ _
  rw [eq_bot_iff, ← killingCompl_top_eq_bot]
  exact I.le_killingCompl_top_of_isLieAbelian

end IsKilling

section LieEquiv

variable {R L}
variable {L' : Type*} [LieRing L'] [LieAlgebra R L']

/-- Given an equivalence `e` of Lie algebras from `L` to `L'`, and elements `x y : L`, the
respective Killing forms of `L` and `L'` satisfy `κ'(e x, e y) = κ(x, y)`. -/
@[simp] lemma killingForm_of_equiv_apply (e : L ≃ₗ⁅R⁆ L') (x y : L) :
    killingForm R L' (e x) (e y) = killingForm R L x y := by
  simp_rw [killingForm_apply_apply, ← LieAlgebra.conj_ad_apply, ← LinearEquiv.conj_comp,
    LinearMap.trace_conj']

/-- Given a Killing Lie algebra `L`, if `L'` is isomorphic to `L`, then `L'` is Killing too. -/
lemma isKilling_of_equiv [IsKilling R L] (e : L ≃ₗ⁅R⁆ L') : IsKilling R L' := by
  constructor
  ext x'
  simp_rw [LieIdeal.mem_killingCompl, LieModule.traceForm_comm]
  refine ⟨fun hx' ↦ ?_, fun hx y _ ↦ hx ▸ LinearMap.map_zero₂ (killingForm R L') y⟩
  suffices e.symm x' ∈ LinearMap.ker (killingForm R L) by
    rw [IsKilling.ker_killingForm_eq_bot] at this
    simpa using (e : L ≃ₗ[R] L').congr_arg this
  ext y
  replace hx' : ∀ y', killingForm R L' x' y' = 0 := by simpa using hx'
  specialize hx' (e y)
  rwa [← e.apply_symm_apply x', killingForm_of_equiv_apply] at hx'

alias _root_.LieEquiv.isKilling := LieAlgebra.isKilling_of_equiv

end LieEquiv

end LieAlgebra
