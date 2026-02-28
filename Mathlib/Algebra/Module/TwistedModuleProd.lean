/-
Copyright (c) 2026 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Star.Basic
public import Mathlib.LinearAlgebra.Complex.Module

/-!
# Twisted product module by a ring homomorphism

`σ : R →+* S`

TODO cf Prod.lean for module
-/

@[expose] public section

open Complex

section

set_option linter.unusedVariables false
/-- A `TwistedModuleProd σ E F` or `E ×[σ|mr|ms] F` is a module structure on the product
`E × F` with the `SMul` given by `s • ⟨x, y⟩ := ⟨s • x, σ s • y⟩`. -/
@[ext]
structure TwistedModuleProd {R S : Type*} [Ring R] [Ring S] (σ : R →+* S) (E : Type*)
    [AddCommGroup E] [Module R E] (F : Type*) [AddCommGroup F] [Module S F] where
  /-- The first element of a pair. -/
  fst : E
  /-- The second element of a pair. -/
  snd : F

@[inherit_doc] notation:25 E " ×[" σ:25 "] " F:0 => TwistedModuleProd σ E F

namespace TwistedModuleProd

variable {R S : Type*} [Ring R] [Ring S] (σ : R →+* S) {E : Type*} [AddCommGroup E]
  [Module R E] {F : Type*} [AddCommGroup F] [Module S F]

instance : Add (TwistedModuleProd σ E F) where
  add x y := mk (x.fst + y.fst) (x.snd + y.snd)

@[simp]
lemma add_fst (x y : TwistedModuleProd σ E F) : (x + y).fst = x.fst + y.fst := rfl

@[simp]
lemma add_snd (x y : TwistedModuleProd σ E F) : (x + y).snd = x.snd + y.snd := rfl

instance : Neg (TwistedModuleProd σ E F) where
  neg x := mk (-x.fst) (-x.snd)

@[simp]
lemma neg_fst (x : TwistedModuleProd σ E F) : (-x).fst = -x.fst := rfl

@[simp]
lemma neg_snd (x : TwistedModuleProd σ E F) : (-x).snd = -x.snd := rfl

instance : Zero (TwistedModuleProd σ E F) where
  zero := mk 0 0

@[simp]
lemma zero_fst : (0 : TwistedModuleProd σ E F).fst = 0 := rfl

@[simp]
lemma zero_snd : (0 : TwistedModuleProd σ E F).snd = 0 := rfl

instance : AddCommGroup (TwistedModuleProd σ E F) where
  add_assoc x y z := by ext <;> simpa using add_assoc _ _ _
  zero_add x := by ext <;> simp
  add_zero x := by ext <;> simp
  nsmul n x := mk (n • x.fst) (n • x.snd)
  zsmul n x := mk (n • x.fst) (n • x.snd)
  neg_add_cancel x := by ext <;> simp
  add_comm x y := by ext <;> simpa using add_comm _ _
  zsmul_zero' x := by ext <;> simp
  zsmul_succ' n x := by ext <;> simp [add_smul]
  nsmul_zero x := by ext <;> simp
  nsmul_succ n x := by ext <;> simp [add_smul]
  zsmul_neg' n x := by ext <;> simp [add_smul]

instance : SMul R (TwistedModuleProd σ E F) where
  smul s x := mk (s • x.fst) (σ s • x.snd)

@[simp]
lemma smul_fst (s : R) (x : TwistedModuleProd σ E F) : (s • x).fst = s • x.fst := rfl

@[simp]
lemma smul_snd (s : R) (x : TwistedModuleProd σ E F) : (s • x).snd = σ s • x.snd := rfl

instance : Module R (TwistedModuleProd σ E F) where
  mul_smul s t x := by ext <;> simp [mul_smul]
  one_smul x := by ext <;> simp
  smul_zero s := by ext <;> simp
  smul_add s x y := by ext <;> simp [smul_add]
  add_smul s t x := by ext <;> simp [add_smul]
  zero_smul x := by ext <;> simp

end TwistedModuleProd

end

section

open TwistedModuleProd

-- the desired result. the second component is twisted.
example :
    Complex.I • (mk 0 1 : ℂ ×[starRingEnd ℂ] ℂ) = (mk 0 (-Complex.I) : ℂ ×[starRingEnd ℂ] ℂ) := by
  ext
  · simp
  · simp

-- cf. the usual `Prod` structure.
example :
  Complex.I • (⟨0, 1⟩ : ℂ × ℂ)
  = (⟨0, Complex.I⟩ : ℂ × ℂ)
  := by
  ext
  · simp
  · simp

end

-- below is a failed attempt to use a type synonym for `R`.
-- it does not work because of multiple `SMul` instances.

section

set_option linter.unusedVariables false in
/-- A `WithTwist σ` with `σ : R →+* S` is a type synonym of `R`, where when there is `Module S F`,
we define `Mpdule (WithTwist σ) F` by `r • x = (σ r) • x`. -/
@[nolint unusedArguments]
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

example :
  Complex.I • (⟨0, 1⟩ : ℂ × (WithTwist ((starRingEnd ℂ))))
  = (⟨0, Complex.I⟩ : ℂ × (WithTwist ((starRingEnd ℂ))))
  := by
  ext
  · simp
  · simp

end

end
