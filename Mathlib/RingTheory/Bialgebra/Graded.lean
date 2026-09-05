/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Coalgebra.Graded
public import Mathlib.RingTheory.GradedAlgebra.Connected

/-!
# Graded bialgebras

This file defines the typeclass `GradedBialgebra 𝒜` and proves structural lemmas about
connected graded bialgebras.

## Main definitions

* `GradedBialgebra 𝒜`: an internally graded bialgebra.
* `GradedAlgebra.IsConnected.zeroLEquiv`: the counit of a connected graded bialgebra restricts
  to an isomorphism `𝒜 0 ≃ₗ[R] R`.

## References

* [Grinberg, D. and Reiner, V., *Hopf Algebras in Combinatorics*][GrinbergReiner2020],
  Exercise 1.3.20 and the proof of Proposition 1.4.16.
-/

public section

open Coalgebra TensorProduct

variable {ι R A : Type*} [CommSemiring R] [Semiring A] [Bialgebra R A]

/-- An internally graded bialgebra is a bialgebra graded simultaneously as an algebra and as a
coalgebra. -/
class GradedBialgebra [DecidableEq ι] [AddMonoid ι] (𝒜 : ι → Submodule R A) extends
  GradedAlgebra 𝒜, GradedCoalgebra 𝒜

/-! ### The degree-zero part of a connected graded bialgebra -/

namespace GradedAlgebra.IsConnected

variable [Zero ι] (𝒜 : ι → Submodule R A)

/-- For a bialgebra, the degree-zero condition alone implies connectedness: the counit forces
the unit map to be injective. -/
theorem of_eq_one (h : 𝒜 0 = 1) : IsConnected 𝒜 where
  eq_one := h
  algebraMap_injective := Bialgebra.algebraMap_injective A

variable [IsConnected 𝒜]

/-- Every element of the degree-zero part equals its counit times the unit. -/
theorem eq_counit_smul_one {a : A} (ha : a ∈ 𝒜 0) : a = counit (R := R) a • 1 := by
  obtain ⟨r, rfl⟩ := (mem_zero_iff 𝒜).mp ha
  simp

/-- The degree-zero submodule of a connected graded bialgebra is canonically isomorphic to
the base ring via the counit. -/
@[expose] def zeroLEquiv : 𝒜 0 ≃ₗ[R] R where
  toFun a := counit (a : A)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  invFun r := ⟨r • 1, (mem_zero_iff 𝒜).mpr ⟨r, rfl⟩⟩
  left_inv a := Subtype.ext (eq_counit_smul_one 𝒜 a.2).symm
  right_inv _ := by simp

@[simp]
theorem zeroLEquiv_apply (a : 𝒜 0) : zeroLEquiv 𝒜 a = counit (a : A) := rfl

@[simp]
theorem zeroLEquiv_symm_apply_coe (r : R) : ((zeroLEquiv 𝒜).symm r : A) = r • 1 := rfl

end GradedAlgebra.IsConnected

namespace Bialgebra

variable [DecidableEq ι] [AddMonoid ι] (𝒜 : ι → Submodule R A)
variable [GradedAlgebra 𝒜] [SetLike.GradedCounit 𝒜]

/-- The counit factors through the degree-zero projection. -/
theorem counit_eq_counit_proj_zero (a : A) :
    counit (R := R) a = counit (GradedAlgebra.proj 𝒜 0 a) := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous i x =>
    rcases eq_or_ne i 0 with rfl | hi
    · simp [GradedAlgebra.proj_apply]
    · rw [SetLike.GradedCounit.counit_eq_zero x.2 hi, GradedAlgebra.proj_apply]
      simp [DirectSum.decompose_coe, DirectSum.of_eq_of_ne _ _ _ hi.symm]
  | add m m' hm hm' => simp [map_add, hm, hm']

variable [GradedAlgebra.IsConnected 𝒜]

/-- Under connectedness, the degree-zero projection equals `algebraMap ∘ counit`. -/
theorem proj_zero_eq_algebraMap_comp_counit :
    (GradedAlgebra.proj 𝒜 0 : A →ₗ[R] A) = Algebra.linearMap R A ∘ₗ counit := by
  ext x
  calc GradedAlgebra.proj 𝒜 0 x
      = counit (R := R) (GradedAlgebra.proj 𝒜 0 x) • 1 :=
        GradedAlgebra.IsConnected.eq_counit_smul_one 𝒜 (SetLike.coe_mem _)
    _ = counit (R := R) x • 1 := by rw [← counit_eq_counit_proj_zero]
    _ = algebraMap R A (counit (R := R) x) := (Algebra.algebraMap_eq_smul_one _).symm

@[simp]
theorem lTensor_proj_zero_comul (x : A) :
    (GradedAlgebra.proj 𝒜 0).lTensor A (comul x) = x ⊗ₜ[R] 1 := by
  simp [proj_zero_eq_algebraMap_comp_counit 𝒜, LinearMap.lTensor_comp_apply]

@[simp]
theorem rTensor_proj_zero_comul (x : A) :
    (GradedAlgebra.proj 𝒜 0).rTensor A (comul x) = 1 ⊗ₜ[R] x := by
  simp [proj_zero_eq_algebraMap_comp_counit 𝒜, LinearMap.rTensor_comp_apply]

end Bialgebra
