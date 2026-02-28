/-
Copyright (c) 2026 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/
module

public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Notation.Prod

/-!
# Twisted product module by a ring homomorphism

`σ : R →+* S`

TODO cf Prod.lean for module
-/

@[expose] public section

section

set_option linter.unusedVariables false
/-- A `twistedModuleProd σ E mr F ms` or `E ×[σ|mr|ms] F` is a module structure on the product
`E × F` with the `SMul` given by `s • ⟨x, y⟩ := ⟨s • x, σ s • y⟩`. -/
@[ext]
structure twistedModuleProd {R S : Type*} [Ring R] [Ring S] (σ : R →+* S) (E : Type*)
    [AddCommGroup E] (mr : Module R E) (F : Type*) [AddCommGroup F] (ms : Module S F) where
  /-- The first element of a pair. -/
  fst : E
  /-- The second element of a pair. -/
  snd : F

@[inherit_doc] notation:25 E "×[" σ:25 "|" mr:25 "|" ms:25 "] " F:0 => twistedModuleProd σ E mr F ms

namespace twistedModuleProd

variable {R S : Type*} [Ring R] [Ring S] (σ : R →+* S) {E : Type*} [AddCommGroup E]
  [mr : Module R E] {F : Type*} [AddCommGroup F] [ms : Module S F]

instance : Add (twistedModuleProd σ E mr F ms) where
  add x y := mk (x.fst + y.fst) (x.snd + y.snd)

@[simp]
lemma add_fst (x y : twistedModuleProd σ E mr F ms) : (x + y).fst = x.fst + y.fst := rfl

@[simp]
lemma add_snd (x y : twistedModuleProd σ E mr F ms) : (x + y).snd = x.snd + y.snd := rfl

instance : Neg (twistedModuleProd σ E mr F ms) where
  neg x := mk (-x.fst) (-x.snd)

@[simp]
lemma neg_fst (x : twistedModuleProd σ E mr F ms) : (-x).fst = -x.fst := rfl

@[simp]
lemma neg_snd (x : twistedModuleProd σ E mr F ms) : (-x).snd = -x.snd := rfl

instance : Zero (twistedModuleProd σ E mr F ms) where
  zero := mk 0 0

@[simp]
lemma zero_fst : (0 : twistedModuleProd σ E mr F ms).fst = 0 := rfl

@[simp]
lemma zero_snd : (0 : twistedModuleProd σ E mr F ms).snd = 0 := rfl

instance : AddCommGroup (twistedModuleProd σ E mr F ms) where
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

instance : SMul R (twistedModuleProd σ E mr F ms) where
  smul s x := mk (s • x.fst) (σ s • x.snd)

@[simp]
lemma smul_fst (s : R) (x : twistedModuleProd σ E mr F ms) : (s • x).fst = s • x.fst := rfl

@[simp]
lemma smul_snd (s : R) (x : twistedModuleProd σ E mr F ms) : (s • x).snd = σ s • x.snd := rfl

instance : Module R (twistedModuleProd σ E mr F ms) where
  mul_smul s t x := by ext <;> simp [mul_smul]
  one_smul x := by ext <;> simp
  smul_zero s := by ext <;> simp
  smul_add s x y := by ext <;> simp [smul_add]
  add_smul s t x := by ext <;> simp [add_smul]
  zero_smul x := by ext <;> simp

end twistedModuleProd

end

section

variable {R S : Type*} [Ring R] [Ring S] (σ : R →+* S)
  (E : Type*) [AddCommGroup E] [mr : Module R E]
  (F : Type*) [AddCommGroup F] [ms : Module S F]

-- def twistedModuleProd' :=
  -- letI : SMul R S := { smul s t := (σ s) • t }
  -- have smulRS (s : R) (t : S) : s • t = σ s • t := rfl
  -- letI : SMul R F := { smul s x := (σ s) • x }
  -- have smulRF (s : R) (x : F) : s • x = σ s • x := rfl
  -- letI : IsScalarTower R S F :=
  --   { smul_assoc s t x := by simpa [smulRS, smulRF] using mul_smul (σ s) t x }
--  Module R (RestrictScalars R S F)
-- need `Algebra R S`

@[inherit_doc] notation:25 E "×[" σ:25 "] " F:0 => twistedModuleProd σ (E × F)

end

section

variable {R S : Type*} [Ring R] [Ring S] (σ : R →+* S)
  (E : Type*) [AddCommGroup E] [Module R E]
  (F : Type*) [AddCommGroup F] [Module S F]

def withTwist {R S : Type*} [Ring R] [Ring S] (σ : R →+* S) := R

instance : Ring (withTwist σ) := inferInstanceAs (Ring R)

instance : SMul (withTwist σ) E where
  smul s x := (id s : R) • x

instance : SMul (withTwist σ) F where
  smul s x := σ s • x

namespace WithTwist

@[simp]
lemma smul_eq (s : withTwist σ) (x : F) : s • x = σ s • x := rfl

instance : Module (withTwist σ) F where
  mul_smul s t x := by simp [mul_smul]
  one_smul x := by simp
  smul_zero s := by simp
  smul_add s x y := by simp [smul_add]
  add_smul s t x := by simp [add_smul]
  zero_smul x := by simp

end WithTwist

end
