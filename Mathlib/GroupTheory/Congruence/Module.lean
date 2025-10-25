/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.GroupTheory.Congruence.Basic

/-!
# Scalar multiplication on a quotient by a congruence relation
-/

variable (R S M N : Type*)

section Instance

instance [Zero M] [SMulZeroClass S M] (c : SMulCon S M) : SMulZeroClass S c.Quotient where
  smul_zero s := congr_arg _ (smul_zero s)

instance [Zero M] [Add M] [SMulZeroClass S M] (c : AddSMulCon S M) : SMulZeroClass S c.Quotient :=
  inferInstanceAs (SMulZeroClass S c.toSMulCon.Quotient)

instance [Zero S] [Zero M] [SMulWithZero S M] (c : SMulCon S M) : SMulWithZero S c.Quotient where
  zero_smul := by rintro ⟨⟩; exact congr_arg _ (zero_smul ..)

instance [Zero S] [Zero M] [Add M] [SMulWithZero S M] (c : AddSMulCon S M) :
    SMulWithZero S c.Quotient :=
  inferInstanceAs (SMulWithZero S c.toSMulCon.Quotient)

@[to_additive] instance [Monoid S] [MulAction S M] (c : SMulCon S M) : MulAction S c.Quotient where
  one_smul := by rintro ⟨⟩; exact congr_arg _ (one_smul ..)
  mul_smul _ _ := by rintro ⟨⟩; exact congr_arg _ (mul_smul ..)

instance [Monoid S] [Add M] [MulAction S M] (c : AddSMulCon S M) : MulAction S c.Quotient :=
  inferInstanceAs (MulAction S c.toSMulCon.Quotient)

instance [AddZeroClass M] [DistribSMul S M] (c : AddSMulCon S M) : DistribSMul S c.Quotient where
  smul_add s := by rintro ⟨⟩ ⟨⟩; exact congr_arg _ (smul_add ..)

instance [Monoid S] [AddMonoid M] [DistribMulAction S M] (c : AddSMulCon S M) :
    DistribMulAction S c.Quotient where
  __ : MulAction S c.Quotient := inferInstance
  __ : DistribSMul S c.Quotient := inferInstance

instance [Semiring S] [AddCommMonoid M] [Module S M] (c : AddSMulCon S M) :
    Module S c.Quotient where
  add_smul _ _ := by rintro ⟨⟩; exact congr_arg _ (add_smul ..)
  zero_smul := by rintro ⟨⟩; exact congr_arg _ (zero_smul ..)

end Instance

section ker

variable {R S M N}

/-- The kernel of a `MulActionHom` as a congruence relation. -/
@[to_additive /-- The kernel of an `AddActionHom` as a congruence relation. -/]
def SMulCon.ker [SMul R M] [SMul S N] {φ : R → S} (f : M →ₑ[φ] N) : SMulCon R M where
  __ := Setoid.ker f
  smul r _ _ h := by rw [Setoid.ker_def] at h ⊢; simp_rw [map_smulₛₗ, h]

/-- The kernel of a `DistribMulActionHom` as a congruence relation. -/
def AddSMulCon.ker [Monoid R] [Monoid S] [AddMonoid M] [AddMonoid N] [DistribMulAction R M]
    [DistribMulAction S N] {φ : R →* S} (f : M →ₑ+[φ] N) : AddSMulCon R M where
  __ := SMulCon.ker f.toMulActionHom
  __ := AddCon.ker f

/-- The first isomorphism theorem for semimodules in the case of a surjective homomorphism. -/
noncomputable def AddSMulCon.quotientKerEquivOfSurjective [Semiring S] [AddCommMonoid M]
    [AddCommMonoid N] [Module S M] [Module S N] (f : M →ₗ[S] N) (hf : Function.Surjective f) :
    (ker f.toDistribMulActionHom).Quotient ≃ₗ[S] N where
  __ := AddCon.quotientKerEquivOfSurjective f.toAddMonoidHom hf
  map_smul' s := by rintro ⟨⟩; apply map_smul f

end ker
