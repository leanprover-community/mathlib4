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
variable {α β : Type*} [AddCommGroup α] [LieRing β]
variable {R : Type*} [CommRing R] [Module R α] [LieAlgebra R β]

/-- Transfer `LieRing` across an `AddEquiv` -/
protected abbrev AddEquiv.lieRing (e : α ≃+ β) : LieRing α where
  bracket x y := e.symm ⁅e x, e y⁆
  add_lie _ _ _ := by simp
  lie_add _ _ _ := by simp
  lie_self _ := by simp
  leibniz_lie _ _ _ := by simp

lemma AddEquiv.bracket_def (e : α ≃+ β) (x y : α) :
    letI := e.lieRing
    ⁅x, y⁆ = e.symm ⁅e x, e y⁆ := rfl

/-- Transfer `LieAlgebra` across a `LinearEquiv` -/
protected abbrev LinearEquiv.lieAlgebra (e : α ≃ₗ[R] β) :
    letI := e.toAddEquiv.lieRing
    LieAlgebra R α :=
  letI := e.toAddEquiv.lieRing
  { lie_smul _ _ _ := by simp [AddEquiv.bracket_def] }

variable (R) in
/-- An equivalence `e : α ≃ₗ[R] β` gives a Lie algebra equivalence `α ≃ₗ⁅R⁆ β` where the Lie bracket
on `α` is the one obtained by transporting a Lie Bracket on `β` back along `e`. -/
def LinearEquiv.lieEquiv (e : α ≃ₗ[R] β) :
    letI := e.toAddEquiv.lieRing
    letI := e.lieAlgebra
    α ≃ₗ⁅R⁆ β :=
  letI := e.toAddEquiv.lieRing
  letI := e.lieAlgebra
  { e with map_lie' := by simp [AddEquiv.bracket_def] }

@[simp]
lemma LinearEquiv.lieEquiv_apply (e : α ≃ₗ[R] β) (a : α) :
    e.lieEquiv R a = e a := rfl

@[simp]
lemma LinearEquiv.lieEquiv_symm_apply (e : α ≃ₗ[R] β) (b : β) :
    letI := e.toAddEquiv.lieRing
    letI := e.lieAlgebra
    (e.lieEquiv R).symm b = e.symm b := rfl

end

namespace Equiv

variable {α β : Type*} [LieRing β] (e : α ≃ β)
variable {R : Type*} [CommRing R] [LieAlgebra R β]

/-- Transfer `LieRing` across an `Equiv` -/
protected abbrev lieRing : LieRing α :=
  letI := e.addCommGroup
  e.addEquiv.lieRing

lemma bracket_def (x y : α) :
    letI := e.lieRing
    ⁅x, y⁆ = e.symm ⁅e x, e y⁆ := rfl

variable (R) in
/-- Transfer `LieAlgebra` across an `Equiv` -/
protected abbrev lieAlgebra :
    letI := e.lieRing
    LieAlgebra R α :=
  letI := e.lieRing
  letI := e.module R
  { lie_smul _ _ _ := by simp [Equiv.smul_def, AddEquiv.bracket_def] }

variable (R) in
/-- An equivalence `e : α ≃ β` gives a Lie algebra equivalence `α ≃ₗ⁅R⁆ β` where the algebraic
structures on `α` are obtained by transporting the structures on `β` back along `e`. -/
def lieEquiv :
    letI := e.lieRing
    letI := e.lieAlgebra R
    α ≃ₗ⁅R⁆ β :=
  letI := e.lieRing
  letI := e.lieAlgebra R
  { e.linearEquiv R with map_lie' {x y} := by simp [AddEquiv.bracket_def] }

@[simp] lemma lieEquiv_apply (a : α) : e.lieEquiv R a = e a := rfl

@[simp] lemma lieEquiv_symm_apply (b : β) :
    letI := e.lieRing
    letI := e.lieAlgebra R
    (e.lieEquiv R).symm b = e.symm b := rfl

end Equiv
