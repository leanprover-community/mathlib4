/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.ZMod.Defs

example : (0 : UInt8) = ⟨0⟩ := rfl

set_option hygiene false in
run_cmd
  for typeName in [`UInt8, `UInt16, `UInt32, `UInt64, `USize].map Lean.mkIdent do
  Lean.Elab.Command.elabCommand (← `(
    namespace $typeName
      instance neZero : NeZero size := ⟨by decide⟩

      instance : Neg $typeName where
        neg a := mk (-a.val)

      instance : Pow $typeName ℕ where
        pow a n := mk (a.val ^ n)

      instance : SMul ℕ $typeName where
        smul n a := mk (n • a.val)

      instance : SMul ℤ $typeName where
        smul z a := mk (z • a.val)

      instance : NatCast $typeName where
        natCast n := mk n

      instance : IntCast $typeName where
        intCast z := mk z

      lemma neg_def (a : $typeName) : -a = ⟨-a.val⟩ := rfl

      lemma pow_def (a : $typeName) (n : ℕ) : a ^ n = ⟨a.val ^ n⟩ := rfl

      lemma nsmul_def (n : ℕ) (a : $typeName) : n • a = ⟨n • a.val⟩ := rfl

      lemma zsmul_def (z : ℤ) (a : $typeName) : z • a = ⟨z • a.val⟩ := rfl

      lemma natCast_def (n : ℕ) : (n : $typeName) = ⟨n⟩ := rfl

      lemma intCast_def (z : ℤ) : (z : $typeName) = ⟨z⟩ := rfl

      open $typeName (eq_of_val_eq) in
      lemma val_injective : Function.Injective val := @eq_of_val_eq

      instance : CommRing $typeName :=
        Function.Injective.commRing val val_injective
          rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
          (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)

    end $typeName
  ))

namespace UInt8

/-- Is this an uppercase ASCII letter? -/
def isUpper (c : UInt8) : Bool :=
  c ≥ 65 && c ≤ 90

/-- Is this a lowercase ASCII letter? -/
def isLower (c : UInt8) : Bool :=
  c ≥ 97 && c ≤ 122

/-- Is this an alphabetic ASCII character? -/
def isAlpha (c : UInt8) : Bool :=
  c.isUpper || c.isLower

/-- Is this an ASCII digit character? -/
def isDigit (c : UInt8) : Bool :=
  c ≥ 48 && c ≤ 57

/-- Is this an alphanumeric ASCII character? -/
def isAlphanum (c : UInt8) : Bool :=
  c.isAlpha || c.isDigit

/-- The numbers from 0 to 256 are all valid UTF-8 characters, so we can embed one in the other. -/
def toChar (n : UInt8) : Char := ⟨n.toUInt32, .inl (n.1.2.trans (by decide))⟩

end UInt8
