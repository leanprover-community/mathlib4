/-
Copyright (c) 2026 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/
module

public import Mathlib.Algebra.Module.NatInt

/-!
# Twisted product module by a ring homomorphism

`σ : R →+* S`

TODO cf Prod.lean for module
-/

@[expose] public section

section

set_option linter.unusedVariables false
@[ext]
structure twistedModuleProd {R S : Type*} [Ring R] [Ring S] (σ : R →+* S) {E : Type*}
    [AddCommGroup E] (mr : Module R E) {F : Type*} [AddCommGroup F] (ms : Module S F) where
  left : E
  right : F

namespace twistedModuleProd

variable {R S : Type*} [Ring R] [Ring S] (σ : R →+* S) {E : Type*} [AddCommGroup E]
  [mr : Module R E] {F : Type*} [AddCommGroup F] [ms : Module S F]

instance : Add (twistedModuleProd σ mr ms) where
  add x y := mk (x.left + y.left) (x.right + y.right)

@[simp]
lemma add_left (x y : twistedModuleProd σ mr ms) : (x + y).left = x.left + y.left := rfl

@[simp]
lemma add_right (x y : twistedModuleProd σ mr ms) : (x + y).right = x.right + y.right := rfl

instance : Neg (twistedModuleProd σ mr ms) where
  neg x := mk (-x.left) (-x.right)

@[simp]
lemma neg_left (x : twistedModuleProd σ mr ms) : (-x).left = -x.left := rfl

@[simp]
lemma neg_right (x : twistedModuleProd σ mr ms) : (-x).right = -x.right := rfl

instance : Zero (twistedModuleProd σ mr ms) where
  zero := mk 0 0

@[simp]
lemma zero_left : (0 : twistedModuleProd σ mr ms).left = 0 := rfl

@[simp]
lemma zero_right : (0 : twistedModuleProd σ mr ms).right = 0 := rfl

instance : AddCommGroup (twistedModuleProd σ mr ms) where
  add_assoc x y z := by ext <;> simpa using add_assoc _ _ _
  zero_add x := by ext <;> simp
  add_zero x := by ext <;> simp
  nsmul n x := mk (n • x.left) (n • x.right)
  zsmul n x := mk (n • x.left) (n • x.right)
  neg_add_cancel x := by ext <;> simp
  add_comm x y := by ext <;> simpa using add_comm _ _
  zsmul_zero' x := by ext <;> simp
  zsmul_succ' n x := by ext <;> simp [add_smul]
  nsmul_zero x := by ext <;> simp
  nsmul_succ n x := by ext <;> simp [add_smul]
  zsmul_neg' n x := by ext <;> simp [add_smul]

instance : SMul R (twistedModuleProd σ mr ms) where
  smul s x := mk (s • x.left) (σ s • x.right)

@[simp]
lemma smul_left (s : R) (x : twistedModuleProd σ mr ms) : (s • x).left = s • x.left := rfl

@[simp]
lemma smul_right (s : R) (x : twistedModuleProd σ mr ms) : (s • x).right = σ s • x.right := rfl

instance : Module R (twistedModuleProd σ mr ms) where
  mul_smul s t x := by ext <;> simp [mul_smul]
  one_smul x := by ext <;> simp
  smul_zero s := by ext <;> simp
  smul_add s x y := by ext <;> simp [smul_add]
  add_smul s t x := by ext <;> simp [add_smul]
  zero_smul x := by ext <;> simp

end twistedModuleProd

end
