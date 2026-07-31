/-
Copyright (c) 2026 Leonid Ryvkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonid Ryvkin
-/

module

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.Algebra.Module.TransferInstance

/-!
# Transfer Lie brackets along AddEquiv, LinearEquiv and Equiv

Main definitions:
* `AddEquiv.lieRing` transferring a LieRing structure along an additive equivalence.
* `LinearEquiv.lieAlgebra` transferring a Lie algebra structure along a linear equivalence.
* `Equiv.lieRing` transferring a LieRing structure along an equivalence (transfers the additive
  structure using `Equiv.addCommGroup` and then the bracket using `AddEquiv.lieRing`)
* `Equiv.lieAlgebra` transferring a Lie algebra structure along an equivalence

-/

@[expose] public section

section

variable {R M L : Type*} [CommRing R] [AddCommGroup M] [Module R M] [LieRing L] [LieAlgebra R L]

/-- Transfer `LieRing` across an `AddEquiv` -/
protected abbrev AddEquiv.lieRing (e : M ≃+ L) : LieRing M where
  bracket x y := e.symm ⁅e x, e y⁆
  add_lie _ _ _ := by simp
  lie_add _ _ _ := by simp
  lie_self _ := by simp
  leibniz_lie _ _ _ := by simp

lemma AddEquiv.bracket_def (e : M ≃+ L) (x y : M) :
    letI := e.lieRing
    ⁅x, y⁆ = e.symm ⁅e x, e y⁆ := rfl

/-- Transfer `LieAlgebra` across a `LinearEquiv` -/
protected abbrev LinearEquiv.lieAlgebra (e : M ≃ₗ[R] L) :
    letI := e.toAddEquiv.lieRing
    LieAlgebra R M :=
  letI := e.toAddEquiv.lieRing
  { lie_smul _ _ _ := by simp [AddEquiv.bracket_def] }

variable (R) in
/-- An equivalence `e : M ≃ₗ[R] L` gives a Lie algebra equivalence `M ≃ₗ⁅R⁆ L` where the Lie bracket
on `M` is the one obtained by transporting a Lie Bracket on `L` back along `e`. -/
def LinearEquiv.lieEquiv (e : M ≃ₗ[R] L) :
    letI := e.toAddEquiv.lieRing
    letI := e.lieAlgebra
    M ≃ₗ⁅R⁆ L :=
  letI := e.toAddEquiv.lieRing
  letI := e.lieAlgebra
  { e with map_lie' := by simp [AddEquiv.bracket_def] }

@[simp]
lemma LinearEquiv.lieEquiv_apply (e : M ≃ₗ[R] L) (a : M) :
    e.lieEquiv R a = e a := rfl

@[simp]
lemma LinearEquiv.lieEquiv_symm_apply (e : M ≃ₗ[R] L) (b : L) :
    letI := e.toAddEquiv.lieRing
    letI := e.lieAlgebra
    (e.lieEquiv R).symm b = e.symm b := rfl

end

namespace Equiv

variable {R L' L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] (e : L' ≃ L)

/-- Transfer `LieRing` across an `Equiv` -/
protected abbrev lieRing : LieRing L' :=
  letI := e.addCommGroup
  e.addEquiv.lieRing

lemma bracket_def (x y : L') :
    letI := e.lieRing
    ⁅x, y⁆ = e.symm ⁅e x, e y⁆ := rfl

variable (R) in
/-- Transfer `LieAlgebra` across an `Equiv` -/
protected abbrev lieAlgebra :
    letI := e.lieRing
    LieAlgebra R L' :=
  letI := e.lieRing
  letI := e.module R
  { lie_smul _ _ _ := by simp [Equiv.smul_def, AddEquiv.bracket_def] }

variable (R) in
/-- An equivalence `e : L' ≃ L` gives a Lie algebra equivalence `L' ≃ₗ⁅R⁆ L` where the algebraic
structures on `L'` are obtained by transporting the structures on `L` back along `e`. -/
def lieEquiv :
    letI := e.lieRing
    letI := e.lieAlgebra R
    L' ≃ₗ⁅R⁆ L :=
  letI := e.lieRing
  letI := e.lieAlgebra R
  { e.linearEquiv R with map_lie' {x y} := by simp [AddEquiv.bracket_def] }

@[simp] lemma lieEquiv_apply (a : L') : e.lieEquiv R a = e a := rfl

@[simp] lemma lieEquiv_symm_apply (b : L) :
    letI := e.lieRing
    letI := e.lieAlgebra R
    (e.lieEquiv R).symm b = e.symm b := rfl

end Equiv
