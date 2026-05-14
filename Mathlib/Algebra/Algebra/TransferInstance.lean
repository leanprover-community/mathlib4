/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Ring.TransferInstance

/-!
# Transfer algebraic structures across `Equiv`s

This continues the pattern set in `Mathlib/Algebra/Group/TransferInstance.lean`.
-/

@[expose] public section

universe v
variable {R α β : Type*} [CommSemiring R]

namespace Equiv
variable (e : α ≃ β)

variable (R) in
/-- Transfer `Algebra` across an `Equiv` -/
protected abbrev algebra (e : α ≃ β) [Semiring β] :
    let _ := Equiv.semiring e
    ∀ [Algebra R β], Algebra R α := fast_instance%
  letI := Equiv.semiring e
  letI := e.smul R
  { algebraMap :=
    { toFun r := e.symm (algebraMap R β r)
      __ := e.ringEquiv.symm.toRingHom.comp (algebraMap R β) }
    commutes' r x :=
      show e.symm ((e (e.symm (algebraMap R β r)) * e x)) =
          e.symm (e x * e (e.symm (algebraMap R β r))) by
        simp [Algebra.commutes]
    smul_def' r x :=
      show e.symm (r • e x) = e.symm (e (e.symm (algebraMap R β r)) * e x) by
        simp [Algebra.smul_def] }

lemma algebraMap_def (e : α ≃ β) [Semiring β] [Algebra R β] (r : R) :
    letI := Equiv.semiring e
    letI := Equiv.algebra R e
    algebraMap R α r = e.symm (algebraMap R β r) := rfl

variable (R) in
/-- An equivalence `e : α ≃ β` gives an algebra equivalence `α ≃ₐ[R] β`
where the `R`-algebra structure on `α` is
the one obtained by transporting an `R`-algebra structure on `β` back along `e`. -/
def algEquiv (e : α ≃ β) [Semiring β] [Algebra R β] : by
    let semiring := Equiv.semiring e
    let algebra := Equiv.algebra R e
    exact α ≃ₐ[R] β := by
  intros
  exact
    { Equiv.ringEquiv e with
      commutes' := fun r => by
        apply e.symm.injective
        simp only [RingEquiv.toEquiv_eq_coe, toFun_as_coe, EquivLike.coe_coe, ringEquiv_apply,
          symm_apply_apply, algebraMap_def] }

@[simp]
theorem algEquiv_apply (e : α ≃ β) [Semiring β] [Algebra R β] (a : α) : (algEquiv R e) a = e a :=
  rfl

theorem algEquiv_symm_apply (e : α ≃ β) [Semiring β] [Algebra R β] (b : β) : by
    letI := Equiv.semiring e
    letI := Equiv.algebra R e
    exact (algEquiv R e).symm b = e.symm b := rfl

end Equiv
