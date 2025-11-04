/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Algebra.Ring.TransferInstance

/-!
# Transfer algebraic structures across `Equiv`s

This continues the pattern set in `Mathlib/Algebra/Group/TransferInstance.lean`.
-/

universe v
variable {R α β : Type*} [CommSemiring R]

namespace Equiv
variable (e : α ≃ β)

variable (R) in
/-- Transfer `Algebra` across an `Equiv` -/
protected abbrev algebra (e : α ≃ β) [Semiring β] :
    let _ := Equiv.semiring e
    ∀ [Algebra R β], Algebra R α := by
  intros
  letI := Equiv.semiring e
  letI := e.smul R
  refine ⟨{
    toFun r := e.symm (algebraMap R β r)
    map_one' := by rw [map_one]; rfl
    map_mul' x y := by
      nth_rw 1 [map_mul, ← e.apply_symm_apply (algebraMap R β x),
        ← e.apply_symm_apply (algebraMap R β y)]; rfl
    map_zero' := by simp; rfl
    map_add' x y := by
      nth_rw 1 [map_add, ← e.apply_symm_apply (algebraMap R β x),
        ← e.apply_symm_apply (algebraMap R β y)]; rfl
  },
  fun r x ↦ ?_, fun r x ↦ ?_⟩
  · simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    calc
    _ = e.symm ((e (e.symm (algebraMap R β r)) * e x)) := rfl
    _ = e.symm (e x * e (e.symm (algebraMap R β r))) := by simp [Algebra.commutes]
    _ = x * e.symm (algebraMap R β r) := rfl
  · simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    calc r • x
      = e.symm (r • e x) := rfl
    _ = e.symm (e (e.symm (algebraMap R β r)) * e x) := by simp [Algebra.smul_def]
    _ = e.symm (algebraMap R β r) * x := rfl

lemma algebraMap_def (e : α ≃ β) [Semiring β] [Algebra R β] (r : R) :
    (@algebraMap R α _ (Equiv.semiring e) (Equiv.algebra R e)) r = e.symm ((algebraMap R β) r) := by
  let _ := Equiv.semiring e
  simp only [Algebra.algebraMap_eq_smul_one]
  change e.symm (r • e 1) = e.symm (r • 1)
  simp only [Equiv.one_def, apply_symm_apply]

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
