/-
Copyright (c) 2026 Janos Wolosz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Janos Wolosz
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.LinearAlgebra.Semisimple
public import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# Properties of the adjoint action

This file collects results about the adjoint action `ad` on associative algebras.

## Main results

* `LieAlgebra.commute_ad_of_commute`: commuting elements have commuting adjoints.
* `LieAlgebra.ad_nilpotent_of_nilpotent`: ad of a nilpotent element is nilpotent.
* `LieAlgebra.ad_isSemisimple_of_isSemisimple`: ad of a semisimple endomorphism is semisimple.
* `LieAlgebra.ad_semisimple_part`: ad preserves the Jordan-Chevalley decomposition.
-/

@[expose] public section

/-- Commuting elements have commuting adjoint actions. -/
theorem LieAlgebra.commute_ad_of_commute {R : Type*} [CommRing R]
    {A : Type*} [Ring A] [Algebra R A] {a b : A} (h : Commute a b) :
    Commute (LieAlgebra.ad R A a) (LieAlgebra.ad R A b) := by
  rw [Commute, SemiconjBy, ← sub_eq_zero, ← Ring.lie_def,
    ← (LieAlgebra.ad R A).map_lie, Ring.lie_def, sub_eq_zero.mpr h, map_zero]

theorem LieAlgebra.ad_nilpotent_of_nilpotent (R : Type*) {A : Type*}
    [CommRing R] [Ring A] [Algebra R A]
    {a : A} (h : IsNilpotent a) :
    IsNilpotent (LieAlgebra.ad R A a) := by
  rw [LieAlgebra.ad_eq_lmul_left_sub_lmul_right]
  have hl : IsNilpotent (LinearMap.mulLeft R a) := by rwa [LinearMap.isNilpotent_mulLeft_iff]
  have hr : IsNilpotent (LinearMap.mulRight R a) := by rwa [LinearMap.isNilpotent_mulRight_iff]
  have := @LinearMap.commute_mulLeft_right R A _ _ _ _ _ a a
  exact this.isNilpotent_sub hl hr

theorem LieSubalgebra.isNilpotent_ad_of_isNilpotent_ad {R : Type*} {L : Type*}
    [CommRing R] [LieRing L] [LieAlgebra R L]
    (K : LieSubalgebra R L) {x : K} (h : IsNilpotent (LieAlgebra.ad R L ↑x)) :
    IsNilpotent (LieAlgebra.ad R K x) := by
  obtain ⟨n, hn⟩ := h
  use n
  exact Module.End.submodule_pow_eq_zero_of_pow_eq_zero (K.ad_comp_incl_eq x) hn

theorem LieAlgebra.isNilpotent_ad_of_isNilpotent {R : Type*} {A : Type*}
    [CommRing R] [Ring A] [Algebra R A]
    {L : LieSubalgebra R A} {x : L}
    (h : IsNilpotent (x : A)) : IsNilpotent (LieAlgebra.ad R L x) :=
  L.isNilpotent_ad_of_isNilpotent_ad <| LieAlgebra.ad_nilpotent_of_nilpotent R h

open Polynomial in
private lemma aeval_mulRight_apply {R : Type*} {M : Type*}
    [CommRing R] [AddCommGroup M] [Module R M]
    (a : Module.End R M) (p : R[X]) (T : Module.End R M) :
    (aeval (LinearMap.mulRight R a) p) T = T * aeval a p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq, mul_add]
  | monomial n c =>
    simp only [aeval_monomial, ← Algebra.smul_def, LinearMap.smul_apply,
      mul_smul_comm, LinearMap.pow_mulRight, LinearMap.mulRight_apply]

private theorem isSemisimple_mulLeft_of_isSemisimple {R : Type*} {M : Type*}
    [Field R] [AddCommGroup M] [Module R M] [FiniteDimensional R M]
    {a : Module.End R M} (ha : a.IsSemisimple) :
    Module.End.IsSemisimple (LinearMap.mulLeft R a) := by
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero ha.minpoly_squarefree
  have : Polynomial.aeval (Algebra.lmul R (Module.End R M) a) (minpoly R a) = 0 := by
    rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  simpa using this

private theorem isSemisimple_mulRight_of_isSemisimple {R : Type*} {M : Type*}
    [Field R] [AddCommGroup M] [Module R M] [FiniteDimensional R M]
    {a : Module.End R M} (ha : a.IsSemisimple) :
    Module.End.IsSemisimple (LinearMap.mulRight R a) := by
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero ha.minpoly_squarefree
  ext1 T
  simp only [LinearMap.zero_apply, aeval_mulRight_apply, minpoly.aeval, mul_zero]

/-- The adjoint of a semisimple endomorphism is semisimple. -/
theorem LieAlgebra.ad_isSemisimple_of_isSemisimple {R : Type*} {M : Type*}
    [Field R] [AddCommGroup M] [Module R M] [FiniteDimensional R M] [PerfectField R]
    {a : Module.End R M} (ha : a.IsSemisimple) :
    (LieAlgebra.ad R (Module.End R M) a).IsSemisimple := by
  rw [LieAlgebra.ad_eq_lmul_left_sub_lmul_right]
  exact (isSemisimple_mulLeft_of_isSemisimple ha).sub_of_commute
    (LinearMap.commute_mulLeft_right a a)
    (isSemisimple_mulRight_of_isSemisimple ha)

/-- If `x = n + s` with `n` nilpotent and `s` semisimple, then `ad(x) = ad(n) + ad(s)`
is the Jordan-Chevalley decomposition of `ad(x)`: `ad(n)` is nilpotent and
`ad(s)` is semisimple. -/
theorem LieAlgebra.ad_semisimple_part {R : Type*} {M : Type*}
    [Field R] [AddCommGroup M] [Module R M] [FiniteDimensional R M] [PerfectField R]
    (x n s : Module.End R M)
    (hn_nil : IsNilpotent n) (hs_ss : s.IsSemisimple)
    (hxns : x = n + s) :
    LieAlgebra.ad R (Module.End R M) x =
      LieAlgebra.ad R (Module.End R M) n + LieAlgebra.ad R (Module.End R M) s ∧
    IsNilpotent (LieAlgebra.ad R (Module.End R M) n) ∧
    (LieAlgebra.ad R (Module.End R M) s).IsSemisimple :=
  ⟨by rw [hxns, map_add],
   LieAlgebra.ad_nilpotent_of_nilpotent R hn_nil,
   LieAlgebra.ad_isSemisimple_of_isSemisimple hs_ss⟩
