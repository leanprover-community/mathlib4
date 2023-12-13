/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Module.Pi
import Mathlib.Data.Polynomial.Basic
import Mathlib.GroupTheory.GroupAction.Prod
import Mathlib.GroupTheory.GroupAction.Units
import Mathlib.Data.Complex.Module
import Mathlib.RingTheory.Algebraic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.TensorProduct

/-! # Tests that instances do not form diamonds -/


/-! ## Scalar action instances -/


section SMul

open scoped Polynomial

example : (SubNegMonoid.SMulInt : SMul ℤ ℂ) = (Complex.instSMulRealComplex : SMul ℤ ℂ) :=
  rfl

example : RestrictScalars.module ℝ ℂ ℂ = Complex.instModuleComplexToAddCommMonoidToNonUnitalNonAssocSemiringToNonUnitalNonAssocCommSemiringToNonUnitalNonAssocCommRingToNonUnitalCommRingCommRing :=
  rfl

example : RestrictScalars.algebra ℝ ℂ ℂ = Complex.instAlgebraComplexInstSemiringComplex :=
  rfl

example (α β : Type _) [AddMonoid α] [AddMonoid β] :
    (Prod.smul : SMul ℕ (α × β)) = AddMonoid.toNatSMul :=
  rfl

example (α β : Type _) [SubNegMonoid α] [SubNegMonoid β] :
    (Prod.smul : SMul ℤ (α × β)) = SubNegMonoid.SMulInt :=
  rfl

example (α : Type _) (β : α → Type _) [∀ a, AddMonoid (β a)] :
    (Pi.instSMul : SMul ℕ (∀ a, β a)) = AddMonoid.toNatSMul :=
  rfl

example (α : Type _) (β : α → Type _) [∀ a, SubNegMonoid (β a)] :
    (Pi.instSMul : SMul ℤ (∀ a, β a)) = SubNegMonoid.SMulInt :=
  rfl

namespace TensorProduct

open scoped TensorProduct

open Complex

/-! The `example` below times out. TODO Fix it!

/- `tensor_product.algebra.module` forms a diamond with `has_mul.to_has_smul` and
`algebra.tensor_product.tensor_product.semiring`. Given a commutative semiring `A` over a
commutative semiring `R`, we get two mathematically different scalar actions of `A ⊗[R] A` on
itself. -/
def f : ℂ ⊗[ℝ] ℂ →ₗ[ℝ] ℝ :=
tensor_product.lift
{ to_fun    := λ z, z.re • re_lm,
  map_add'  := λ z w, by simp [add_smul],
  map_smul' := λ r z, by simp [mul_smul], }

@[simp] lemma f_apply (z w : ℂ) : f (z ⊗ₜ[ℝ] w) = z.re * w.re := by simp [f]

/- `tensor_product.algebra.module` forms a diamond with `has_mul.to_has_smul` and
`algebra.tensor_product.tensor_product.semiring`. Given a commutative semiring `A` over a
commutative semiring `R`, we get two mathematically different scalar actions of `A ⊗[R] A` on
itself. -/
example :
  has_mul.to_has_smul (ℂ ⊗[ℝ] ℂ) ≠
  (@tensor_product.algebra.module ℝ ℂ ℂ (ℂ ⊗[ℝ] ℂ) _ _ _ _ _ _ _ _ _ _ _ _).to_has_smul :=
begin
  have contra : I ⊗ₜ[ℝ] I ≠ (-1) ⊗ₜ[ℝ] 1 := λ c, by simpa using congr_arg f c,
  contrapose! contra,
  rw has_smul.ext_iff at contra,
  replace contra := congr_fun (congr_fun contra (1 ⊗ₜ I)) (I ⊗ₜ 1),
  rw @tensor_product.algebra.smul_def ℝ ℂ ℂ (ℂ ⊗[ℝ] ℂ) _ _ _ _ _ _ _ _ _ _ _ _
    (1 : ℂ) I (I ⊗ₜ[ℝ] (1 : ℂ)) at contra,
  simpa only [algebra.id.smul_eq_mul, algebra.tensor_product.tmul_mul_tmul, one_mul, mul_one,
    one_smul, tensor_product.smul_tmul', I_mul_I] using contra,
end

-/


end TensorProduct

section Units

example (α : Type _) [Monoid α] : (Units.instMulActionUnitsToMonoidToDivInvMonoidInstGroupUnits : MulAction αˣ (α × α)) = Prod.mulAction :=
  rfl

example (R α : Type _) (β : α → Type _) [Monoid R] [∀ i, MulAction R (β i)] :
    (Units.instMulActionUnitsToMonoidToDivInvMonoidInstGroupUnits : MulAction Rˣ (∀ i, β i)) = Pi.mulAction _ :=
  rfl

example (R α : Type _) [Monoid R] [Semiring α] [DistribMulAction R α] :
    (Units.instDistribMulActionUnitsToMonoidToDivInvMonoidInstGroupUnits : DistribMulAction Rˣ α[X]) = Polynomial.distribMulAction :=
  rfl

/-!
TODO: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/units.2Emul_action'.20diamond/near/246402813
```lean
example {α : Type*} [comm_monoid α] :
  (units.mul_action' : mul_action αˣ αˣ) = monoid.to_mul_action _ :=
rfl -- fails
```
-/


end Units

end SMul

/-! ## `with_top` (Type with point at infinity) instances -/


section WithTop

example (R : Type _) [h : StrictOrderedSemiring R] :
    @WithTop.addCommMonoid R
        (@NonUnitalNonAssocSemiring.toAddCommMonoid R
          (@NonAssocSemiring.toNonUnitalNonAssocSemiring R
            (@Semiring.toNonAssocSemiring R (@StrictOrderedSemiring.toSemiring R h)))) =
      @OrderedAddCommMonoid.toAddCommMonoid (WithTop R)
        (@WithTop.orderedAddCommMonoid R
          (@OrderedCancelAddCommMonoid.toOrderedAddCommMonoid R
            (@StrictOrderedSemiring.toOrderedCancelAddCommMonoid R h))) :=
  rfl

end WithTop

/-! ## `multiplicative` instances -/


section Multiplicative

example :
    @Monoid.toMulOneClass (Multiplicative ℕ) CommMonoid.toMonoid = Multiplicative.mulOneClass :=
  rfl

end Multiplicative

/-! ## `finsupp` instances-/


section Finsupp

open Finsupp

/-- `finsupp.comap_has_smul` can form a non-equal diamond with `finsupp.smul_zero_class` -/
example {k : Type _} [Semiring k] [Nontrivial k] :
    (Finsupp.comapSMul : SMul k (k →₀ k)) ≠ Finsupp.smulZeroClass.toSMul :=
  by
  obtain ⟨u : k, hu⟩ := exists_ne (1 : k)
  intro h
  simp only [SMul.ext_iff, SMul.smul_eq, Function.funext_iff, FunLike.ext_iff] at h
  replace h := h u (Finsupp.single 1 1) u
  classical
  rw [comapSMul_single, smul_apply, smul_eq_mul, mul_one, single_eq_same, smul_eq_mul,
    single_eq_of_ne hu.symm, MulZeroClass.mul_zero] at h
  exact one_ne_zero h

/-- `finsupp.comap_has_smul` can form a non-equal diamond with `finsupp.smul_zero_class` even when
the domain is a group. -/
example {k : Type _} [Semiring k] [Nontrivial kˣ] :
    (Finsupp.comapSMul : SMul kˣ (kˣ →₀ k)) ≠ Finsupp.smulZeroClass.toSMul :=
  by
  obtain ⟨u : kˣ, hu⟩ := exists_ne (1 : kˣ)
  haveI : Nontrivial k := ⟨⟨u, 1, Units.ext.ne hu⟩⟩
  intro h
  simp only [SMul.ext_iff, SMul.smul_eq, Function.funext_iff, FunLike.ext_iff] at h
  replace h := h u (Finsupp.single 1 1) u
  classical
  rw [comapSMul_single, smul_apply, Units.smul_def, smul_eq_mul, mul_one, single_eq_same,
    smul_eq_mul, single_eq_of_ne hu.symm, MulZeroClass.mul_zero] at h
  exact one_ne_zero h

end Finsupp

/-! ## `polynomial` instances -/


section Polynomial

variable (R A : Type _)

open scoped Polynomial

open Polynomial

/-- `polynomial.has_smul_pi` forms a diamond with `pi.has_smul`. -/
example [Semiring R] [Nontrivial R] :
    Polynomial.hasSMulPi _ _ ≠ (Pi.instSMul : SMul R[X] (R → R[X])) :=
  by
  intro h
  simp_rw [SMul.ext_iff, Function.funext_iff, Polynomial.ext_iff] at h
  simpa using h X 1 1 0

/-- `polynomial.has_smul_pi'` forms a diamond with `pi.has_smul`. -/
example [CommSemiring R] [Nontrivial R] :
    Polynomial.hasSMulPi' _ _ _ ≠ (Pi.instSMul : SMul R[X] (R → R[X])) :=
  by
  intro h
  simp_rw [SMul.ext_iff, Function.funext_iff, Polynomial.ext_iff] at h
  simpa using h X 1 1 0

/-- `polynomial.has_smul_pi'` is consistent with `polynomial.has_smul_pi`. -/
example [CommSemiring R] [Nontrivial R] :
    Polynomial.hasSMulPi' _ _ _ = (Polynomial.hasSMulPi _ _ : SMul R[X] (R → R[X])) :=
  rfl

/-- `polynomial.algebra_of_algebra` is consistent with `algebra_nat`. -/
example [Semiring R] : (Polynomial.algebraOfAlgebra : Algebra ℕ R[X]) = algebraNat :=
  rfl

/-- `polynomial.algebra_of_algebra` is consistent with `algebra_int`. -/
example [Ring R] : (Polynomial.algebraOfAlgebra : Algebra ℤ R[X]) = algebraInt _ :=
  rfl

end Polynomial

/-! ## `subtype` instances -/


section Subtype

-- this diamond is the reason that `fintype.to_locally_finite_order` is not an instance
example {α} [Preorder α] [LocallyFiniteOrder α] [Fintype α] [@DecidableRel α (· < ·)]
    [@DecidableRel α (· ≤ ·)] (p : α → Prop) [DecidablePred p] :
    Subtype.instLocallyFiniteOrder p = Fintype.toLocallyFiniteOrder :=
  by
  fail_if_success rfl
  exact Subsingleton.elim _ _

end Subtype

/-! ## `zmod` instances -/


section ZMod

variable {p : ℕ} [Fact p.Prime]

example :
    @EuclideanDomain.toCommRing _ (@Field.toEuclideanDomain _ (ZMod.instFieldZMod p)) = ZMod.commRing p :=
  rfl

example (n : ℕ) : ZMod.commRing (n + 1) = Fin.instCommRing (n + 1) :=
  rfl

example : ZMod.commRing 0 = Int.instCommRingInt :=
  rfl

end ZMod
