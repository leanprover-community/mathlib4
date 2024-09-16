/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.LinearAlgebra.RootSystem.Defs

/-!
# Root pairings made from bilinear forms
A common construction of root systems is given by taking the set of all vectors in an integral
lattice for which reflection yields an automorphism of the lattice.  In this file, we generalize
this construction, replacing the ring of integers with an arbitrary commutative ring and the
integral lattice with an arbitrary reflexive module equipped with a bilinear form.

## Main definitions:
 * `IsReflective`: Length is a regular value of `R`, and reflection is definable.
 * `coroot_of_reflective`: The coroot corresponding to a reflective vector.
 * `of_Bilinear`: The root pairing whose roots are reflective vectors.

## TODO
 * properties
-/

open Set Function Module

noncomputable section

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace RootPairing

section Construction

/-- A vector `x` is reflective with respect to a bilinear form if multiplication by its norm is
injective, and for any other vector `y`, there is a scalar that takes the norm of `x` to twice the
inner product of `x` and `y`. These conditions are what we need when describing reflection as a map
taking `y` to `y - 2 • (B x y) / (B x x) • x`. -/
structure IsReflective (B : M →ₗ[R] M →ₗ[R] R) (x : M) : Prop :=
  regular : IsRegular (B x x)
  dvd_two_mul : ∀ y, B x x ∣ 2 * B x y

variable (B : M →ₗ[R] M →ₗ[R] R) {x : M}

lemma isReflective_of_dvd_two [IsDomain R] [NeZero (2 : R)] (hx : B x x ∣ 2) :
    IsReflective B x where
  regular := isRegular_of_ne_zero <| fun contra ↦ by simp [contra, two_ne_zero (α := R)] at hx
  dvd_two_mul y := hx.mul_right (B x y)

/-- The coroot attached to a reflective vector. -/
def coroot_of_reflective (hx : IsReflective B x) :
    M →ₗ[R] R where
  toFun y := (hx.2 y).choose
  map_add' a b := by
    refine hx.regular.left ?_
    simp only
    rw [← (hx.dvd_two_mul (a + b)).choose_spec, mul_add, ← (hx.2 a).choose_spec,
      ← (hx.2 b).choose_spec, map_add, mul_add]
  map_smul' r a := by
    refine hx.1.1 ?_
    simp only [RingHom.id_apply]
    rw [← (hx.2 (r • a)).choose_spec, smul_eq_mul, mul_left_comm, ← (hx.2 a).choose_spec, map_smul,
      two_mul, smul_eq_mul, two_mul, mul_add]

@[simp]
lemma coroot_of_reflective_apply {y : M} (hx : IsReflective B x) :
    B x x * coroot_of_reflective B hx y = 2 * B x y := by
  dsimp [coroot_of_reflective]
  rw [← (hx.2 y).choose_spec]

@[simp]
lemma coroot_of_reflective_apply_self (hx : IsReflective B x) :
    coroot_of_reflective B hx x = 2 := by
  refine hx.1.1 ?_
  dsimp only
  rw [coroot_of_reflective_apply B hx, mul_two, two_mul]

lemma reflection_reflective_vector {y : M}
    (hx : IsReflective B x) : Module.reflection (coroot_of_reflective_apply_self B hx) y =
    y - (coroot_of_reflective B hx y) • x :=
  rfl

lemma bilinear_apply_reflection_reflective_vector (B : M →ₗ[R] M →ₗ[R] R) (hSB : LinearMap.IsSymm B)
    {x y z : M} (hx : IsReflective B x) :
    B (Module.reflection (coroot_of_reflective_apply_self B hx) y)
      (Module.reflection (coroot_of_reflective_apply_self B hx) z) = B y z := by
  rw [reflection_reflective_vector, LinearMap.map_sub₂, LinearMap.map_smul₂,
    reflection_reflective_vector, LinearMap.map_sub, LinearMap.map_sub, LinearMap.map_smul]
  refine hx.1.1 ?_
  simp only [smul_eq_mul, map_smul, mul_sub, ← mul_assoc, coroot_of_reflective_apply]
  rw [sub_eq_iff_eq_add, ← hSB x y, RingHom.id_apply, mul_assoc _ _ (B x x), mul_comm _ (B x x),
    coroot_of_reflective_apply]
  ring

lemma reflective_reflection_reflective (B : M →ₗ[R] M →ₗ[R] R) (hSB : LinearMap.IsSymm B) {x y : M}
    (hx : IsReflective B x) (hy : IsReflective B y) :
    IsReflective B (Module.reflection (coroot_of_reflective_apply_self B hx) y) := by
  constructor
  · rw [bilinear_apply_reflection_reflective_vector B hSB]
    exact hy.1
  · intro z
    have hz : Module.reflection (coroot_of_reflective_apply_self B hx)
        (Module.reflection (coroot_of_reflective_apply_self B hx) z) = z := by
      exact
        (LinearEquiv.eq_symm_apply (Module.reflection (coroot_of_reflective_apply_self B hx))).mp
          rfl
    rw [← hz, bilinear_apply_reflection_reflective_vector B hSB,
      bilinear_apply_reflection_reflective_vector B hSB]
    exact hy.2 _

@[simp]
lemma dual_apply [IsReflexive R M] (B : M →ₗ[R] M →ₗ[R] R) {x y : M} (hx : IsReflective B x) :
    IsReflexive.toPerfectPairingDual (R := R) (coroot_of_reflective B hx) y =
    (coroot_of_reflective B hx) y :=
  rfl

/-- The root pairing given by all reflective vectors for a bilinear form. -/
def of_Bilinear [IsReflexive R M] (B : M →ₗ[R] M →ₗ[R] R) (hNB : LinearMap.Nondegenerate B)
    (hSB : LinearMap.IsSymm B) (h2 : IsRegular (2 : R)) :
    RootPairing {x : M | IsReflective B x} R M (Dual R M) where
  toPerfectPairing := (IsReflexive.toPerfectPairingDual (R := R) (M := M)).flip
  root := Embedding.subtype fun x ↦ IsReflective B x
  coroot :=
  {
    toFun := fun x => coroot_of_reflective B x.2
    inj' := by
      intro x y hxy
      simp only [mem_setOf_eq] at hxy -- x* = y*
      have h1 : ∀ z, coroot_of_reflective B x.2 z = coroot_of_reflective B y.2 z :=
        fun z => congrFun (congrArg DFunLike.coe hxy) z
      have h2x : ∀ z, B x x * coroot_of_reflective B x.2 z =
          B x x * coroot_of_reflective B y.2 z :=
        fun z => congrArg (HMul.hMul ((B x) x)) (h1 z)
      have h2y : ∀ z, B y y * coroot_of_reflective B x.2 z =
          B y y * coroot_of_reflective B y.2 z :=
        fun z => congrArg (HMul.hMul ((B y) y)) (h1 z)
      simp_rw [coroot_of_reflective_apply B x.2] at h2x -- 2(x,z) = (x,x)y*(z)
      simp_rw [coroot_of_reflective_apply B y.2] at h2y -- (y,y)x*(z) = 2(y,z)
      have h2xy : B x x = B y y := by
        refine h2.1 ?_
        dsimp only
        specialize h2x y
        rw [coroot_of_reflective_apply_self] at h2x
        specialize h2y x
        rw [coroot_of_reflective_apply_self] at h2y
        rw [mul_comm, ← h2x, ← hSB, RingHom.id_apply, ← h2y, mul_comm]
      rw [Subtype.ext_iff_val, ← sub_eq_zero]
      refine hNB.1 _ (fun z => ?_)
      rw [map_sub, LinearMap.sub_apply, sub_eq_zero]
      refine h2.1 ?_
      dsimp only
      rw [h2x z, ← h2y z, hxy, h2xy] }
  root_coroot_two := by
    intro x
    dsimp only [coe_setOf, Embedding.coe_subtype, PerfectPairing.toLin_apply, mem_setOf_eq, id_eq,
      eq_mp_eq_cast, RingHom.id_apply, eq_mpr_eq_cast, cast_eq, LinearMap.sub_apply,
      Embedding.coeFn_mk, PerfectPairing.flip_apply_apply]
    exact coroot_of_reflective_apply_self B x.2
  reflection_perm := fun x =>
    { toFun := fun y => ⟨(Module.reflection (coroot_of_reflective_apply_self B x.2) y),
        reflective_reflection_reflective B hSB x.2 y.2⟩
      invFun := fun y => ⟨(Module.reflection (coroot_of_reflective_apply_self B x.2) y),
        reflective_reflection_reflective B hSB x.2 y.2⟩
      left_inv := by
        intro y
        simp [involutive_reflection (coroot_of_reflective_apply_self B x.2) y]
      right_inv := by
        intro y
        simp [involutive_reflection (coroot_of_reflective_apply_self B x.2) y] }
  reflection_perm_root := by
    intro x y
    simp only [coe_setOf, Embedding.coe_subtype, mem_setOf_eq, Embedding.coeFn_mk, Equiv.coe_fn_mk]
    rw [reflection_reflective_vector B x.2, PerfectPairing.flip_apply_apply, dual_apply]
  reflection_perm_coroot := by
    intro x y
    simp only [coe_setOf, mem_setOf_eq, Embedding.coeFn_mk, Embedding.coe_subtype,
      PerfectPairing.flip_apply_apply, dual_apply, Equiv.coe_fn_mk]
    ext z
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    refine y.2.1.1 ?_
    simp only [mem_setOf_eq, PerfectPairing.flip_apply_apply, mul_sub,
      coroot_of_reflective_apply B y.2, ← mul_assoc]
    rw [← bilinear_apply_reflection_reflective_vector B hSB x.2 (z := y),
      coroot_of_reflective_apply, ← hSB z, ← hSB z, RingHom.id_apply, RingHom.id_apply,
      reflection_reflective_vector, map_sub, mul_sub, sub_eq_sub_iff_comm, sub_left_inj]
    refine x.2.1.1 ?_
    simp only [mem_setOf_eq, map_smul, smul_eq_mul]
    rw [← mul_assoc _ _ (B z x), ← mul_assoc _ _ (B z x), mul_left_comm,
      coroot_of_reflective_apply B x.2, mul_left_comm (B x x), coroot_of_reflective_apply B x.2,
      ← hSB x y, RingHom.id_apply, ← hSB x z, RingHom.id_apply]
    ring

end Construction

end RootPairing
