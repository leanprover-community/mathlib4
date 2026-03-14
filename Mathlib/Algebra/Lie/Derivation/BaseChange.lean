/-
Copyright (c) 2026 Leonid Ryvkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonid Ryvkin
-/
module

public import Mathlib.Algebra.Lie.BaseChange
public import Mathlib.Algebra.Lie.Derivation.Basic
public import Mathlib.RingTheory.Derivation.Lie

/-!
# LieDerivations of a Lie algebra created through BaseChange

When, given an `R`-algebra `A` and an `R`-Lie algebra `L` the (Lie algebra) basechange `A⊗[R] L`,
both derivations of `A` and Lie derivations of `L` induce Lie derivations of `A⊗[R] L`. Moreover,
both these procedures are Lie algebra homomorphisms themselves.


## Tags

lie algebra, extension of scalars, base change, derivation

-/

@[expose] public section
namespace Lie.Derivation

open TensorProduct
variable {R : Type*} [CommRing R]
variable {A : Type*} [CommRing A] [Algebra R A]
variable {L : Type*} [LieRing L] [LieAlgebra R L]

variable (L) in
/-- The Lie Derivation of `A ⊗[R] L` induced by a derivation of `A` -/
def BaseChangeDer (d : Derivation R A A) : LieDerivation R (A ⊗[R] L) (A ⊗[R] L) where
  toFun := d.toLinearMap.rTensor L
  map_add' := by simp
  map_smul' := by simp
  leibniz' x y := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    refine x.induction_on (by simp) ?_ ?_
    · intros _ l
      refine y.induction_on (by simp) ?_ ?_
      · intros _ l'
        rw [←sub_eq_zero]
        simp only [LieAlgebra.ExtendScalars.bracket_tmul, LinearMap.rTensor_tmul,
          Derivation.coeFn_coe, Derivation.leibniz, smul_eq_mul, add_tmul]
        rw [←(lie_skew l' l), tmul_neg]
        abel_nf
      · intros _ _ h1 h2
        rw [←sub_eq_zero]
        simp [h1, h2]
        abel_nf
    · intros _ _ h1 h2
      rw [←sub_eq_zero]
      simp [h1, h2]
      abel_nf

@[simp]
lemma BaseChangeDer_apply (d : Derivation R A A) (x : A ⊗[R] L) :
  (BaseChangeDer L d) x = d.toLinearMap.rTensor L x := rfl

variable (R A L) in
/-- The assignment `BaseChangeDer` is a Lie algebra homomorphism -/
def BaseChangeDerHom : (Derivation R A A) →ₗ⁅R⁆ (LieDerivation R (A ⊗[R] L) (A ⊗[R] L)) where
  toFun := BaseChangeDer L
  map_add' _ _ := by ext _; simp
  map_smul' _ _ := by ext _; simp
  map_lie' {_ _} := by
    ext z
    simp only [BaseChangeDer_apply, Derivation.commutator_coe_linear_map,
      LieDerivation.lie_apply]
    refine z.induction_on (by simp) ?_ ?_
    · intros _ _
      simp [sub_tmul]
    · intros _ _ hx hy
      simp [hx, hy]
      abel_nf

@[simp]
lemma BaseChangeDerHom_apply (d : Derivation R A A) (x : A ⊗[R] L) :
  (BaseChangeDerHom R A L d) x = d.toLinearMap.rTensor L x := rfl

variable (A) in
/-- The Lie Derivation of `A ⊗[R] L` induced by a Lie derivation of `L` -/
def BaseChangeLieDer (d : LieDerivation R L L) : LieDerivation R (A ⊗[R] L) (A ⊗[R] L) where
  toFun := d.toLinearMap.lTensor A
  map_add' := by simp
  map_smul' := by simp
  leibniz' x y:= by
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    refine x.induction_on (by simp) ?_ ?_
    · intros _ _
      refine y.induction_on (by simp) ?_ ?_
      · intros _ _
        simp [LieAlgebra.ExtendScalars.bracket_tmul, tmul_sub, mul_comm]
      · intros _ _ h1 h2
        simp [h1, h2]
        abel_nf
    · intros _ _ h1 h2
      simp [h1, h2]
      abel_nf

@[simp]
lemma BaseChangeLieDer_apply (d : LieDerivation R L L) (x : A ⊗[R] L) :
  (BaseChangeLieDer A d) x = d.toLinearMap.lTensor A x := rfl

variable (R A L) in
/-- The assignment `BaseChangeLieDer` is a Lie algebra homomorphism -/
def BaseChangeLieDerHom : (LieDerivation R L L) →ₗ⁅R⁆ (LieDerivation R (A ⊗[R] L) (A ⊗[R] L)) where
  toFun := BaseChangeLieDer A
  map_add' _ _ := by ext _; simp
  map_smul' _ _ := by ext _; simp
  map_lie' {_ _} := by
    ext z
    simp only [BaseChangeLieDer_apply, LieDerivation.commutator_coe_linear_map,
      LieDerivation.lie_apply]
    refine z.induction_on (by simp) ?_ ?_
    · intros a l
      simp_rw [LinearMap.lTensor_tmul, LieHom.lie_apply, LieDerivation.coeFn_coe,
        Module.End.lie_apply]
      rw [← sub_eq_zero, tmul_sub]
      simp
    · intros _ _ hx hy
      simp [hx, hy]
      abel_nf

end Lie.Derivation
end
