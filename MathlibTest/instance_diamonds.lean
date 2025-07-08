/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GroupWithZero.Action.Prod
import Mathlib.Algebra.GroupWithZero.Action.Units
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Complex.Module
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Algebraic.Pi
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Tests that instances do not form diamonds -/


/-! ## Scalar action instances -/


section SMul

open scoped Polynomial

example : (SubNegMonoid.toZSMul : SMul ℤ ℂ) = (Complex.SMul.instSMulRealComplex : SMul ℤ ℂ) := by
  with_reducible_and_instances rfl

example : RestrictScalars.module ℝ ℂ ℂ = Complex.instModule := by
  with_reducible_and_instances rfl

-- fails `with_reducible_and_instances` https://github.com/leanprover-community/mathlib4/issues/10906
example : RestrictScalars.algebra ℝ ℂ ℂ = Complex.instAlgebraOfReal := by
  rfl

example (α β : Type _) [AddMonoid α] [AddMonoid β] :
    (Prod.instSMul : SMul ℕ (α × β)) = AddMonoid.toNatSMul := by
  with_reducible_and_instances rfl

example (α β : Type _) [SubNegMonoid α] [SubNegMonoid β] :
    (Prod.instSMul : SMul ℤ (α × β)) = SubNegMonoid.toZSMul := by
  with_reducible_and_instances rfl

example (α : Type _) (β : α → Type _) [∀ a, AddMonoid (β a)] :
    (Pi.instSMul : SMul ℕ (∀ a, β a)) = AddMonoid.toNatSMul := by
  with_reducible_and_instances rfl

example (α : Type _) (β : α → Type _) [∀ a, SubNegMonoid (β a)] :
    (Pi.instSMul : SMul ℤ (∀ a, β a)) = SubNegMonoid.toZSMul := by
  with_reducible_and_instances rfl

namespace TensorProduct

open scoped TensorProduct

open Complex

/- `TensorProduct.Algebra.module` forms a diamond with `Mul.toSMul` and
`algebra.tensor_product.tensor_product.semiring`. Given a commutative semiring `A` over a
commutative semiring `R`, we get two mathematically different scalar actions of `A ⊗[R] A` on
itself. -/
noncomputable def f : ℂ ⊗[ℝ] ℂ →ₗ[ℝ] ℝ :=
  TensorProduct.lift
    { toFun := fun z => z.re • reLm
      map_add' := fun z w => by simp [add_smul]
      map_smul' := fun r z => by simp [mul_smul] }

@[simp]
theorem f_apply (z w : ℂ) : f (z ⊗ₜ[ℝ] w) = z.re * w.re := by simp [f]

unseal Algebra.TensorProduct.mul in
/- `TensorProduct.Algebra.module` forms a diamond with `Mul.toSMul` and
`algebra.tensor_product.tensor_product.semiring`. Given a commutative semiring `A` over a
commutative semiring `R`, we get two mathematically different scalar actions of `A ⊗[R] A` on
itself. -/
example :
    Mul.toSMul (ℂ ⊗[ℝ] ℂ) ≠
      (@TensorProduct.Algebra.module ℝ ℂ ℂ (ℂ ⊗[ℝ] ℂ) _ _ _ _ _ _ _ _ _ _ _ _).toSMul := by
  have contra : I ⊗ₜ[ℝ] I ≠ (-1) ⊗ₜ[ℝ] 1 := fun c => by simpa using congr_arg f c
  contrapose! contra
  rw [SMul.ext_iff, SMul.smul_eq_hSMul, @SMul.smul_eq_hSMul _ _ (_)] at contra
  replace contra := congr_fun (congr_fun contra (1 ⊗ₜ I)) (I ⊗ₜ 1)
  rw [TensorProduct.Algebra.smul_def (R := ℝ) (1 : ℂ) I (I ⊗ₜ[ℝ] (1 : ℂ))] at contra
  simpa only [Algebra.id.smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one,
    one_smul, TensorProduct.smul_tmul', I_mul_I] using contra

end TensorProduct

section Units

example (α : Type _) [Monoid α] :
    (Units.instMulAction : MulAction αˣ (α × α)) = Prod.mulAction := by
  with_reducible_and_instances rfl

example (R α : Type _) (β : α → Type _) [Monoid R] [∀ i, MulAction R (β i)] :
    (Units.instMulAction : MulAction Rˣ (∀ i, β i)) = Pi.mulAction _ := by
  with_reducible_and_instances rfl

example (R α : Type _) [Monoid R] [Semiring α] [DistribMulAction R α] :
    (Units.instDistribMulAction : DistribMulAction Rˣ α[X]) = Polynomial.distribMulAction := by
  with_reducible_and_instances rfl

/-!
TODO: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/units.2Emul_action'.20diamond/near/246402813
```lean
example {α : Type*} [CommMonoid α] :
    (Units.mulAction' : MulAction αˣ αˣ) = Monoid.toMulAction _ :=
  rfl -- fails
```
-/

end Units

end SMul

/-! ## `Multiplicative` instances -/


section Multiplicative

example : @Monoid.toMulOneClass (Multiplicative ℕ) CommMonoid.toMonoid =
    Multiplicative.mulOneClass := by
  with_reducible_and_instances rfl

end Multiplicative

/-! ## `Finsupp` instances -/


section Finsupp

open Finsupp

/-- `Finsupp.comapSMul` can form a non-equal diamond with `Finsupp.smulZeroClass` -/
example {k : Type _} [Semiring k] [Nontrivial k] :
    (Finsupp.comapSMul : SMul k (k →₀ k)) ≠ Finsupp.smulZeroClass.toSMul := by
  obtain ⟨u : k, hu⟩ := exists_ne (1 : k)
  intro h
  simp only [SMul.ext_iff, @SMul.smul_eq_hSMul _ _ (_), funext_iff, DFunLike.ext_iff] at h
  replace h := h u (Finsupp.single 1 1) u
  classical
  rw [comapSMul_single, smul_apply, smul_eq_mul, mul_one, single_eq_same, smul_eq_mul,
    single_eq_of_ne hu.symm, MulZeroClass.mul_zero] at h
  exact one_ne_zero h

/-- `Finsupp.comapSMul` can form a non-equal diamond with `Finsupp.smulZeroClass` even when
the domain is a group. -/
example {k : Type _} [Semiring k] [Nontrivial kˣ] :
    (Finsupp.comapSMul : SMul kˣ (kˣ →₀ k)) ≠ Finsupp.smulZeroClass.toSMul := by
  obtain ⟨u : kˣ, hu⟩ := exists_ne (1 : kˣ)
  haveI : Nontrivial k := ⟨⟨u, 1, Units.ext.ne hu⟩⟩
  intro h
  simp only [SMul.ext_iff, @SMul.smul_eq_hSMul _ _ (_), funext_iff, DFunLike.ext_iff] at h
  replace h := h u (Finsupp.single 1 1) u
  classical
  rw [comapSMul_single, smul_apply, Units.smul_def, smul_eq_mul, mul_one, single_eq_same,
    smul_eq_mul, single_eq_of_ne hu.symm, MulZeroClass.mul_zero] at h
  exact one_ne_zero h

end Finsupp

/-! ## `Polynomial` instances -/


section Polynomial

variable (R A : Type _)

open scoped Polynomial

open Polynomial

/-- `Polynomial.hasSMulPi` forms a diamond with `Pi.instSMul`. -/
example [Semiring R] [Nontrivial R] :
    Polynomial.hasSMulPi _ _ ≠ (Pi.instSMul : SMul R[X] (R → R[X])) := by
  intro h
  simp_rw [SMul.ext_iff, @SMul.smul_eq_hSMul _ _ (_), funext_iff, Polynomial.ext_iff] at h
  simpa using h X 1 1 0

/-- `Polynomial.hasSMulPi'` forms a diamond with `Pi.instSMul`. -/
example [CommSemiring R] [Nontrivial R] :
    Polynomial.hasSMulPi' _ _ _ ≠ (Pi.instSMul : SMul R[X] (R → R[X])) := by
  intro h
  simp_rw [SMul.ext_iff, @SMul.smul_eq_hSMul _ _ (_), funext_iff, Polynomial.ext_iff] at h
  simpa using h X 1 1 0

-- fails `with_reducible_and_instances` https://github.com/leanprover-community/mathlib4/issues/10906
/-- `Polynomial.hasSMulPi'` is consistent with `Polynomial.hasSMulPi`. -/
example [CommSemiring R] [Nontrivial R] :
    Polynomial.hasSMulPi' _ _ _ = (Polynomial.hasSMulPi _ _ : SMul R[X] (R → R[X])) :=
  rfl

-- fails `with_reducible_and_instances` https://github.com/leanprover-community/mathlib4/issues/10906
/-- `Polynomial.algebraOfAlgebra` is consistent with `Semiring.toNatAlgebra`. -/
example [Semiring R] : (Polynomial.algebraOfAlgebra : Algebra ℕ R[X]) = Semiring.toNatAlgebra :=
  rfl

-- fails `with_reducible_and_instances` https://github.com/leanprover-community/mathlib4/issues/10906
/-- `Polynomial.algebraOfAlgebra` is consistent with `Ring.toIntAlgebra`. -/
example [Ring R] : (Polynomial.algebraOfAlgebra : Algebra ℤ R[X]) = Ring.toIntAlgebra _ :=
  rfl

end Polynomial

/-! ## `Subtype` instances -/


section Subtype

-- this diamond is the reason that `Fintype.toLocallyFiniteOrder` is not an instance
example {α} [Preorder α] [LocallyFiniteOrder α] [Fintype α] [DecidableLT α]
    [DecidableLE α] (p : α → Prop) [DecidablePred p] :
    Subtype.instLocallyFiniteOrder p = Fintype.toLocallyFiniteOrder := by
  fail_if_success rfl
  exact Subsingleton.elim _ _

end Subtype

/-! ## `ZMod` instances -/


section ZMod

variable {p : ℕ} [Fact p.Prime]

example :
    @EuclideanDomain.toCommRing _ (@Field.toEuclideanDomain _ (ZMod.instField p)) =
      ZMod.commRing p := by
  with_reducible_and_instances rfl

-- We need `open Fin.CommRing`, as otherwise `Fin.instCommRing` is not an instance,
-- so `with_reducible_and_instances` doesn't have the desired effect.
open Fin.CommRing in
example (n : ℕ) : ZMod.commRing (n + 1) = Fin.instCommRing (n + 1) := by
  with_reducible_and_instances rfl

example : ZMod.commRing 0 = Int.instCommRing := by
  with_reducible_and_instances rfl

end ZMod

/-! ## Instances involving structures over `ℝ` and `ℂ`

Given a scalar action on `ℝ`, we have an instance which produces the corresponding scalar action on
`ℂ`. In the other direction, if there is a scalar action of `ℂ` on some type, we can get a
corresponding action of `ℝ` on that type via `RestrictScalars`.

Obviously, this has the potential to cause diamonds when we can go in both directions. This shows
that at least some potential diamonds are avoided. -/

section complexToReal

-- fails `with_reducible_and_instances` https://github.com/leanprover-community/mathlib4/issues/10906
-- the two ways to get `Algebra ℝ ℂ` are definitionally equal
example : (Algebra.id ℂ).complexToReal = Complex.instAlgebraOfReal := rfl

-- fails `with_reducible_and_instances` https://github.com/leanprover-community/mathlib4/issues/10906
/- The complexification of an `ℝ`-algebra `A` (i.e., `ℂ ⊗[ℝ] A`) is a `ℂ`-algebra. Viewing this
as an `ℝ`-algebra by restricting scalars agrees with the existing `ℝ`-algebra structure on the
tensor product. -/
open Algebra TensorProduct in
example {A : Type*} [Ring A] [Algebra ℝ A]:
    (leftAlgebra : Algebra ℂ (ℂ ⊗[ℝ] A)).complexToReal = leftAlgebra := by
  rfl

end complexToReal

/-! ## Instances on `ℚ≥0`
-/

/-- This diamond arose because the semifield structure on `NNRat` needs to be defined as early as
possible, before `Nonneg.zpow` becomes available; `Nonneg.zpow` is used to then define the
`LinearOrderedCommGroupWithZero` instance. -/
example : (inferInstanceAs (Semifield ℚ≥0)).toCommGroupWithZero =
    (inferInstanceAs (LinearOrderedCommGroupWithZero ℚ≥0)).toCommGroupWithZero := rfl
