/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.ZMod.Defs

/-!
# Adds Mathlib specific instances to the `UIntX` data types.

The `CommRing` instances (and the `NatCast` and `IntCast` instances from which they is built) are
scoped in the `UIntX.CommRing` namespace, rather than available globally. As a result, the `ring`
tactic will not work on `UIntX` types without `open scoped UIntX.Ring`.

This is because the presence of these casting operations contradicts assumptions made by the
expression tree elaborator, namely that coercions do not form a cycle.

The UInt
version also interferes more with software-verification use-cases, which is reason to be more
cautious here.
-/

example : (0 : UInt8) = ⟨0⟩ := rfl

set_option hygiene false in
run_cmd
  for typeName' in [`UInt8, `UInt16, `UInt32, `UInt64, `USize] do
  let typeName := Lean.mkIdent typeName'
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

      lemma neg_def (a : $typeName) : -a = ⟨-a.val⟩ := rfl

      lemma pow_def (a : $typeName) (n : ℕ) : a ^ n = ⟨a.val ^ n⟩ := rfl

      lemma nsmul_def (n : ℕ) (a : $typeName) : n • a = ⟨n • a.val⟩ := rfl

      lemma zsmul_def (z : ℤ) (a : $typeName) : z • a = ⟨z • a.val⟩ := rfl

      open $typeName (eq_of_val_eq) in
      lemma val_injective : Function.Injective val := @eq_of_val_eq

      instance instCommMonoid : CommMonoid $typeName :=
        Function.Injective.commMonoid val val_injective
          rfl (fun _ _ => rfl) (fun _ _ => rfl)

      instance instNonUnitalCommRing : NonUnitalCommRing $typeName :=
        Function.Injective.nonUnitalCommRing val val_injective
          rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
          (fun _ _ => rfl) (fun _ _ => rfl)

      local instance instNatCast : NatCast $typeName where
        natCast n := mk n

      local instance instIntCast : IntCast $typeName where
        intCast z := mk z

      lemma natCast_def (n : ℕ) : (n : $typeName) = ⟨n⟩ := rfl

      lemma intCast_def (z : ℤ) : (z : $typeName) = ⟨z⟩ := rfl

      local instance instCommRing : CommRing $typeName :=
        Function.Injective.commRing val val_injective
          rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
          (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)

      namespace CommRing
      attribute [scoped instance] instCommRing instNatCast instIntCast
      end CommRing

    end $typeName
  ))
  -- interpolating docstrings above is more trouble than it's worth
  let docString :=
    s!"To use this instance, use `open scoped {typeName'}.CommRing`.\n\n" ++
    "See the module docstring for an explanation"
  Lean.addDocString (typeName'.mkStr "instCommRing") docString
  Lean.addDocString (typeName'.mkStr "instNatCast") docString
  Lean.addDocString (typeName'.mkStr "instIntCast") docString

namespace UInt8

/-- Is this an uppercase ASCII letter? -/
def isASCIIUpper (c : UInt8) : Bool :=
  c ≥ 65 && c ≤ 90

/-- Is this a lowercase ASCII letter? -/
def isASCIILower (c : UInt8) : Bool :=
  c ≥ 97 && c ≤ 122

/-- Is this an alphabetic ASCII character? -/
def isASCIIAlpha (c : UInt8) : Bool :=
  c.isASCIIUpper || c.isASCIILower

/-- Is this an ASCII digit character? -/
def isASCIIDigit (c : UInt8) : Bool :=
  c ≥ 48 && c ≤ 57

/-- Is this an alphanumeric ASCII character? -/
def isASCIIAlphanum (c : UInt8) : Bool :=
  c.isASCIIAlpha || c.isASCIIDigit

@[deprecated (since := "2024-06-06")] alias isUpper := isASCIIUpper
@[deprecated (since := "2024-06-06")] alias isLower := isASCIILower
@[deprecated (since := "2024-06-06")] alias isAlpha := isASCIIAlpha
@[deprecated (since := "2024-06-06")] alias isDigit := isASCIIDigit
@[deprecated (since := "2024-06-06")] alias isAlphanum := isASCIIAlphanum

/-- The numbers from 0 to 256 are all valid UTF-8 characters, so we can embed one in the other. -/
def toChar (n : UInt8) : Char := ⟨n.toUInt32, .inl (n.1.2.trans (by decide))⟩

end UInt8
