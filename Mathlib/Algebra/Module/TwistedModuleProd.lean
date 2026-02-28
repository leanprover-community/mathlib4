/-
Copyright (c) 2026 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs

/-!
# Twisted product module by a ring homomorphism

`σ : R →+* S`

TODO cf Prod.lean for module
-/

@[expose] public section

set_option linter.unusedVariables false
/-- A `WithTwist σ` with `σ : R →+* S` is a type synonym of `R`, where when there is `Module S F`,
we define `Mpdule (WithTwist σ) F` by `r • x = (σ r) • x`. -/
def WithTwist {R S : Type*} [Semiring R] [Semiring S] (σ : R →+* S) := R

namespace WithTwist

variable {R S : Type*} [Semiring R] [Semiring S] (σ : R →+* S)

instance : Semiring (WithTwist σ) := inferInstanceAs (Semiring R)

section

variable {E : Type*} [SMul R E]

instance : SMul (WithTwist σ) E where
  smul r x := (id r : R) • x

instance : SMul R (WithTwist σ) where
  smul r x := r • (id x : R)

instance : Module R (WithTwist σ) where
  mul_smul _ _ _ := by simp [mul_assoc]
  one_smul _ := by simp
  smul_zero _ := by simp
  smul_add _ _ _ := by simp [mul_add]
  add_smul _ _ _ := by simp [add_mul]
  zero_smul _ := by simp

/-- The semilinear map `(WithTwist σ) →ₛₗ[σ] S` identical to `σ`. -/
def toLinearMap : (WithTwist σ) →ₛₗ[σ] S where
  toFun r := σ r
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

end

section

variable {F : Type*} [SMul S F]

instance : SMul (WithTwist σ) F where
  smul r x := σ r • x

@[simp]
lemma smul_eq (s : WithTwist σ) (x : F) : s • x = σ s • x := rfl

end

section

variable {E : Type*} [AddCommMonoid E] [Module R E]

instance : Module (WithTwist σ) E := inferInstanceAs (Module R E)

variable {F : Type*} [AddCommMonoid F] [Module S F]

instance : Module (WithTwist σ) F where
  mul_smul _ _ _ := by simp [mul_smul]
  one_smul _ := by simp
  smul_zero _ := by simp
  smul_add _ _ _ := by simp [smul_add]
  add_smul _ _ _ := by simp [add_smul]
  zero_smul _ := by simp

end

end WithTwist

end
