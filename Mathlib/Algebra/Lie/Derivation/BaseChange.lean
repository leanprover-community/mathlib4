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
/-- A derivation of an associative `R-`algebra `A`, induces a Lie derivation of `A ⊗[R] L` for any
Lie algebra `L` over `R`. -/
def ofDerivation : Derivation R A A →ₗ⁅R⁆ LieDerivation R (A ⊗[R] L) (A ⊗[R] L) where
  toFun d :=
    { toFun := d.rTensor L
      map_add' := by simp
      map_smul' := by simp
      leibniz' x y := by
        -- Probably the below can be golfed (low priority)
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
          abel_nf }
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  map_lie' {_ _} := by
    ext z
    refine z.induction_on (by simp) (by simp [sub_tmul]) (fun _ _ hx hy ↦ ?_)
    simp_all
    abel

@[simp]
lemma ofDerivation_apply (d : Derivation R A A) (x : A ⊗[R] L) :
  (ofDerivation L d) x = d.toLinearMap.rTensor L x := rfl

variable (A) in
/-- A Lie derivation of an `R-`Lie algebra `L`, induces a Lie derivation of `A ⊗[R] L` for any
Algebra `A` over `R`. -/
def ofLieDerivation : (LieDerivation R L L) →ₗ⁅R⁆ (LieDerivation R (A ⊗[R] L) (A ⊗[R] L)) where
  toFun d :=
    { toFun := d.toLinearMap.lTensor A
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
          abel_nf }
  map_add' _ _ := by ext _; simp
  map_smul' _ _ := by ext _; simp
  map_lie' {_ _} := by
    ext z
    simp only [LieDerivation.commutator_coe_linear_map,
      LieDerivation.lie_apply]
    refine z.induction_on (by simp) ?_ ?_
    · intros a l
      simp [LieHom.lie_apply, LieDerivation.coeFn_coe, Module.End.lie_apply, tmul_sub]
    · intros _ _ hx hy
      simp at hx hy
      simp [hx, hy]
      abel_nf

@[simp]
lemma ofLieDerivation_apply (d : LieDerivation R L L) (x : A ⊗[R] L) :
  (ofLieDerivation A d) x = d.toLinearMap.lTensor A x := rfl

end Lie.Derivation
end
