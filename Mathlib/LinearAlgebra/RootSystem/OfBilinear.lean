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
 * `IsReflective.coroot`: The coroot corresponding to a reflective vector.
 * `of_Bilinear`: The root pairing whose roots are reflective vectors.

## TODO
 * properties
-/

open Set Function Module

noncomputable section

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace LinearMap

/-- A vector `x` is reflective with respect to a bilinear form if multiplication by its norm is
injective, and for any other vector `y`, there is a scalar that takes the norm of `x` to twice the
inner product of `x` and `y`. These conditions are what we need when describing reflection as a map
taking `y` to `y - 2 • (B x y) / (B x x) • x`. -/
structure IsReflective (B : M →ₗ[R] M →ₗ[R] R) (x : M) : Prop :=
  regular : IsRegular (B x x)
  dvd_two_mul : ∀y, B x x ∣ 2 * B x y

variable (B : M →ₗ[R] M →ₗ[R] R) {x : M}

namespace IsReflective

lemma of_dvd_two [IsDomain R] [NeZero (2 : R)] (hx : B x x ∣ 2) :
    IsReflective B x where
  regular := isRegular_of_ne_zero <| fun contra => by simp [contra, two_ne_zero (α := R)] at hx
  dvd_two_mul y := hx.mul_right (B x y)

variable (hx : IsReflective B x)

/-- The coroot attached to a reflective vector. -/
def coroot : M →ₗ[R] R where
  toFun y := (hx.2 y).choose
  map_add' a b := by
    refine hx.1.1 ?_
    simp only
    rw [← (hx.2 (a + b)).choose_spec, mul_add, ← (hx.2 a).choose_spec, ← (hx.2 b).choose_spec,
      map_add, mul_add]
  map_smul' r a := by
    refine hx.1.1 ?_
    simp only [RingHom.id_apply]
    rw [← (hx.2 (r • a)).choose_spec, smul_eq_mul, mul_left_comm, ← (hx.2 a).choose_spec, map_smul,
      two_mul, smul_eq_mul, two_mul, mul_add]

@[simp]
lemma smul_coroot : B x x • coroot B hx = 2 • B x := by
  ext y
  simp only [LinearMap.smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
  exact (hx.dvd_two_mul y).choose_spec.symm

@[simp]
lemma coroot_apply {y : M} :
    B x x * coroot B hx y = 2 * B x y :=
  (hx.dvd_two_mul y).choose_spec.symm

@[simp]
lemma coroot_apply_self : coroot B hx x = 2 :=
  hx.regular.left <| by simp [mul_comm _ (B x x)]

lemma isOrthogonal_reflection (hSB : LinearMap.IsSymm B) :
    B.IsOrthogonal (Module.reflection (coroot_apply_self B hx)) := by
  intro y z
  simp only [LinearEquiv.coe_coe, reflection_apply, LinearMap.map_sub, map_smul, sub_apply,
    smul_apply, smul_eq_mul]
  refine hx.1.1 ?_
  simp only [mul_sub, ← mul_assoc, coroot_apply]
  rw [sub_eq_iff_eq_add, ← hSB x y, RingHom.id_apply, mul_assoc _ _ (B x x), mul_comm _ (B x x),
    coroot_apply]
  ring

lemma reflective_reflection_reflective (B : M →ₗ[R] M →ₗ[R] R) (hSB : LinearMap.IsSymm B) {x y : M}
    (hx : IsReflective B x) (hy : IsReflective B y) :
    IsReflective B (Module.reflection (coroot_apply_self B hx) y) := by
  constructor
  · rw [← LinearEquiv.coe_coe, (isOrthogonal_reflection B hx hSB) y y]
    exact hy.1
  · intro z
    have hz : Module.reflection (coroot_apply_self B hx)
        (Module.reflection (coroot_apply_self B hx) z) = z := by
      exact
        (LinearEquiv.eq_symm_apply (Module.reflection (coroot_apply_self B hx))).mp
          rfl
    rw [← hz, ← LinearEquiv.coe_coe, isOrthogonal_reflection B hx hSB,
      isOrthogonal_reflection B hx hSB]
    exact hy.2 _

@[simp]
lemma dual_apply [IsReflexive R M] (B : M →ₗ[R] M →ₗ[R] R) {x y : M} (hx : IsReflective B x) :
    IsReflexive.toPerfectPairingDual (R := R) (coroot B hx) y =
    (coroot B hx) y :=
  rfl

end IsReflective

end LinearMap

namespace RootPairing

open LinearMap

/-- The root pairing given by all reflective vectors for a bilinear form. -/
def of_Bilinear [IsReflexive R M] (B : M →ₗ[R] M →ₗ[R] R) (hNB : Nondegenerate B)
    (hSB : IsSymm B) (h2 : IsRegular (2 : R)) :
    RootPairing {x : M | IsReflective B x} R M (Dual R M) where
  toPerfectPairing := (IsReflexive.toPerfectPairingDual (R := R) (M := M)).flip
  root := Embedding.subtype fun x ↦ IsReflective B x
  coroot :=
  {
    toFun := fun x => IsReflective.coroot B x.2
    inj' := by
      intro x y hxy
      simp only [mem_setOf_eq] at hxy -- x* = y*
      have h1 : ∀ z, IsReflective.coroot B x.2 z = IsReflective.coroot B y.2 z :=
        fun z => congrFun (congrArg DFunLike.coe hxy) z
      have h2x : ∀ z, B x x * IsReflective.coroot B x.2 z =
          B x x * IsReflective.coroot B y.2 z :=
        fun z => congrArg (HMul.hMul ((B x) x)) (h1 z)
      have h2y : ∀ z, B y y * IsReflective.coroot B x.2 z =
          B y y * IsReflective.coroot B y.2 z :=
        fun z => congrArg (HMul.hMul ((B y) y)) (h1 z)
      simp_rw [IsReflective.coroot_apply B x.2] at h2x -- 2(x,z) = (x,x)y*(z)
      simp_rw [IsReflective.coroot_apply B y.2] at h2y -- (y,y)x*(z) = 2(y,z)
      have h2xy : B x x = B y y := by
        refine h2.1 ?_
        dsimp only
        specialize h2x y
        rw [IsReflective.coroot_apply_self] at h2x
        specialize h2y x
        rw [IsReflective.coroot_apply_self] at h2y
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
    exact IsReflective.coroot_apply_self B x.2
  reflection_perm := fun x =>
    { toFun := fun y => ⟨(Module.reflection (IsReflective.coroot_apply_self B x.2) y),
        IsReflective.reflective_reflection_reflective B hSB x.2 y.2⟩
      invFun := fun y => ⟨(Module.reflection (IsReflective.coroot_apply_self B x.2) y),
        IsReflective.reflective_reflection_reflective B hSB x.2 y.2⟩
      left_inv := by
        intro y
        simp [involutive_reflection (IsReflective.coroot_apply_self B x.2) y]
      right_inv := by
        intro y
        simp [involutive_reflection (IsReflective.coroot_apply_self B x.2) y] }
  reflection_perm_root := by
    intro x y
    simp only [coe_setOf, Embedding.coe_subtype, mem_setOf_eq, Embedding.coeFn_mk, Equiv.coe_fn_mk]
    rw [Module.reflection_apply, PerfectPairing.flip_apply_apply,
      IsReflective.dual_apply]
  reflection_perm_coroot := by
    intro x y
    simp only [coe_setOf, mem_setOf_eq, Embedding.coeFn_mk, Embedding.coe_subtype,
      PerfectPairing.flip_apply_apply, IsReflective.dual_apply, Equiv.coe_fn_mk]
    ext z
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    refine y.2.1.1 ?_
    simp only [mem_setOf_eq, PerfectPairing.flip_apply_apply, mul_sub,
      IsReflective.coroot_apply B y.2, ← mul_assoc]
    rw [← IsReflective.isOrthogonal_reflection B x.2 hSB y y,
      IsReflective.coroot_apply, ← hSB z, ← hSB z, RingHom.id_apply, RingHom.id_apply,
      LinearEquiv.coe_coe, Module.reflection_apply, map_sub, mul_sub, sub_eq_sub_iff_comm,
      sub_left_inj]
    refine x.2.1.1 ?_
    simp only [mem_setOf_eq, map_smul, smul_eq_mul]
    rw [← mul_assoc _ _ (B z x), ← mul_assoc _ _ (B z x), mul_left_comm,
      IsReflective.coroot_apply B x.2, mul_left_comm (B x x), IsReflective.coroot_apply B x.2,
      ← hSB x y, RingHom.id_apply, ← hSB x z, RingHom.id_apply]
    ring

end RootPairing
