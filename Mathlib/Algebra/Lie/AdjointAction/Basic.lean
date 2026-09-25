/-
Copyright (c) 2026 Janos Wolosz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Janos Wolosz
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.LinearAlgebra.Semisimple
public import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# Properties of the adjoint action

Theorems about the adjoint action `LieAlgebra.ad` on associative algebras.

## Main results

* `LieAlgebra.commute_ad_of_commute`: commuting elements have commuting adjoints.
* `LieAlgebra.ad_nilpotent_of_nilpotent`: the adjoint of a nilpotent element is nilpotent.
* `LieAlgebra.ad_isSemisimple_of_isSemisimple`: the adjoint of a semisimple element is semisimple.
-/

@[expose] public section

section CommRing

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- Commuting elements have commuting adjoint actions. -/
theorem LieAlgebra.commute_ad_of_commute {a b : A} (h : Commute a b) :
    Commute (LieAlgebra.ad R A a) (LieAlgebra.ad R A b) := by
  rw [Commute, SemiconjBy, ← sub_eq_zero, ← Ring.lie_def,
    ← (LieAlgebra.ad R A).map_lie, Ring.lie_def, sub_eq_zero.mpr h, map_zero]

/-- The adjoint of a nilpotent element is nilpotent. -/
theorem LieAlgebra.ad_nilpotent_of_nilpotent {a : A} (h : IsNilpotent a) :
    IsNilpotent (LieAlgebra.ad R A a) := by
  rw [LieAlgebra.ad_eq_lmul_left_sub_lmul_right]
  have hl : IsNilpotent (LinearMap.mulLeft R a) := by rwa [LinearMap.isNilpotent_mulLeft_iff]
  have hr : IsNilpotent (LinearMap.mulRight R a) := by rwa [LinearMap.isNilpotent_mulRight_iff]
  exact (LinearMap.commute_mulLeft_right a a).isNilpotent_sub hl hr

theorem LieSubalgebra.isNilpotent_ad_of_isNilpotent_ad {L : Type*} [LieRing L] [LieAlgebra R L]
    (K : LieSubalgebra R L) {x : K} (h : IsNilpotent (LieAlgebra.ad R L ↑x)) :
    IsNilpotent (LieAlgebra.ad R K x) := by
  obtain ⟨n, hn⟩ := h
  use n
  exact Module.End.submodule_pow_eq_zero_of_pow_eq_zero (K.ad_comp_incl_eq x) hn

theorem LieAlgebra.isNilpotent_ad_of_isNilpotent
    {L : LieSubalgebra R A} {x : L} (h : IsNilpotent (x : A)) :
    IsNilpotent (LieAlgebra.ad R L x) :=
  L.isNilpotent_ad_of_isNilpotent_ad <| LieAlgebra.ad_nilpotent_of_nilpotent h

end CommRing

section Field

variable {K V : Type*} [Field K] [PerfectField K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V]

/-- The adjoint of a semisimple element is semisimple. -/
theorem LieAlgebra.ad_isSemisimple_of_isSemisimple {a : Module.End K V} (ha : a.IsSemisimple) :
    (LieAlgebra.ad K (Module.End K V) a).IsSemisimple := by
  rw [LieAlgebra.ad_eq_lmul_left_sub_lmul_right]
  have hl : Module.End.IsSemisimple (LinearMap.mulLeft K a) := by
    apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero ha.minpoly_squarefree
    have : Polynomial.aeval (Algebra.lmul K (Module.End K V) a) (minpoly K a) = 0 := by
      rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
    simpa using this
  have hr : Module.End.IsSemisimple (LinearMap.mulRight K a) := by
    apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero ha.minpoly_squarefree
    have hrw : LinearMap.mulRight K a =
        (Algebra.lsmul (A := (Module.End K V)ᵐᵒᵖ) K K (Module.End K V)) (.op a) := by
      ext; simp [Algebra.lsmul]
    rw [hrw, Polynomial.aeval_algHom_apply, Polynomial.aeval_op_apply, minpoly.aeval,
      MulOpposite.op_zero, map_zero]
  exact hl.sub_of_commute (LinearMap.commute_mulLeft_right a a) hr

end Field
