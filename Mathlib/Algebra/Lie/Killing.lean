/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.InvariantForm
public import Mathlib.Algebra.Lie.Semisimple.Basic
public import Mathlib.Algebra.Lie.TraceForm

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

## Main declarations

* `LieAlgebra.IsKilling`: a typeclass encoding the fact that a Lie algebra has a non-singular
  Killing form.
* `LieAlgebra.IsKilling.instSemisimple`: if a finite-dimensional Lie algebra over a field
  has non-singular Killing form then it is semisimple.
* `LieAlgebra.IsKilling.instHasTrivialRadical`: if a Lie algebra over a PID
  has non-singular Killing form then it has trivial radical.
* `LieIdeal.isCompl_killingCompl`: if a Lie algebra has non-singular Killing form then for all
  ideals, an ideal and its Killing orthogonal complement are complements.

## TODO

* Prove that in characteristic zero, a semisimple Lie algebra has non-singular Killing form.

-/

@[expose] public section

variable (R K L : Type*) [CommRing R] [Field K] [LieRing L] [LieAlgebra R L] [LieAlgebra K L]

namespace LieAlgebra

/-- We say a Lie algebra is Killing if its Killing form is non-singular.

NB: This is not standard terminology (the literature does not seem to name Lie algebras with this
property). -/
class IsKilling : Prop where
  /-- We say a Lie algebra is Killing if its Killing form is non-singular. -/
  killingCompl_top_eq_bot : LieIdeal.killingCompl R L ⊤ = ⊥

attribute [simp] IsKilling.killingCompl_top_eq_bot

namespace IsKilling

variable [IsKilling R L]

@[simp] lemma ker_killingForm_eq_bot :
    LinearMap.ker (killingForm R L) = ⊥ := by
  simp [← LieIdeal.coe_killingCompl_top, killingCompl_top_eq_bot]

lemma killingForm_nondegenerate :
    (killingForm R L).Nondegenerate := by
  refine (LieModule.traceForm_isSymm R L L).isRefl.nondegenerate_iff_separatingLeft.mpr ?_
  simp [LinearMap.separatingLeft_iff_ker_eq_bot]

set_option backward.isDefEq.respectTransparency false in
variable {R L} in
lemma ideal_eq_bot_of_isLieAbelian
    [Module.Free R L] [Module.Finite R L] [IsDomain R] [IsPrincipalIdealRing R]
    (I : LieIdeal R L) [IsLieAbelian I] : I = ⊥ := by
  rw [eq_bot_iff, ← killingCompl_top_eq_bot]
  exact I.le_killingCompl_top_of_isLieAbelian

set_option backward.isDefEq.respectTransparency false in
instance instSemisimple [IsKilling K L] [Module.Finite K L] : IsSemisimple K L := by
  apply InvariantForm.isSemisimple_of_nondegenerate (Φ := killingForm K L)
  · exact IsKilling.killingForm_nondegenerate _ _
  · exact LieModule.traceForm_lieInvariant _ _ _
  · exact (LieModule.traceForm_isSymm K L L).isRefl
  · intro I h₁ h₂
    exact h₁.1 <| IsKilling.ideal_eq_bot_of_isLieAbelian I

/-- The converse of this is true over a field of characteristic zero. There are counterexamples
over fields with positive characteristic.

Note that when the coefficients are a field this instance is redundant since we have
`LieAlgebra.IsKilling.instSemisimple` and `LieAlgebra.IsSemisimple.instHasTrivialRadical`. -/
instance instHasTrivialRadical
    [Module.Free R L] [Module.Finite R L] [IsDomain R] [IsPrincipalIdealRing R] :
    HasTrivialRadical R L :=
  (hasTrivialRadical_iff_no_abelian_ideals R L).mpr IsKilling.ideal_eq_bot_of_isLieAbelian

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
    simpa [map_zero] using (e : L ≃ₗ[R] L').congr_arg this
  ext y
  replace hx' : ∀ y', killingForm R L' x' y' = 0 := by simpa using hx'
  specialize hx' (e y)
  rwa [← e.apply_symm_apply x', killingForm_of_equiv_apply] at hx'

alias _root_.LieEquiv.isKilling := LieAlgebra.isKilling_of_equiv

end LieEquiv

end LieAlgebra

set_option backward.isDefEq.respectTransparency false in
open LieAlgebra in
variable {K L} in
lemma LieIdeal.isCompl_killingCompl [IsKilling K L] [Module.Finite K L] (I : LieIdeal K L) :
    IsCompl I I.killingCompl := by
  suffices Disjoint I I.killingCompl by
    rwa [← LieSubmodule.isCompl_toSubmodule, I.toSubmodule_killingCompl,
      LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint (LieModule.traceForm_isSymm K L L).isRefl,
      ← I.toSubmodule_killingCompl, LieSubmodule.disjoint_toSubmodule]
  suffices IsLieAbelian (I ⊓ I.killingCompl : LieIdeal K L) by
    rw [disjoint_iff]
    exact IsKilling.ideal_eq_bot_of_isLieAbelian _
  suffices ∀ (x y z : L) (hx : x ∈ killingCompl K L I) (hy : y ∈ I),
      LieModule.traceForm K L L ⁅x, y⁆ z = 0 by
    rw [LieSubmodule.lie_abelian_iff_lie_self_eq_bot, LieSubmodule.lie_eq_bot_iff]
    rintro x ⟨-, hx⟩ y ⟨hy, -⟩
    exact (IsKilling.killingForm_nondegenerate K L).1 _ fun z ↦ this x y z hx hy
  intro x y z hx hy
  rw [LieModule.traceForm_apply_lie_apply K L L x y z, LieModule.traceForm_comm K L L]
  exact I.mem_killingCompl.mp hx _ <| lie_mem_left K L I y z hy
