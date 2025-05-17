/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Init

-- Much of the content of this file was removed after
-- https://github.com/leanprover/lean4/pull/7886
-- If anyone needs to restore this functionality, please do so in a PR,
-- but otherwise we will delete the commented out parts of this file soon.

-- import Mathlib.Algebra.Ring.InjSurj
-- import Mathlib.Data.ZMod.Defs
-- import Mathlib.Data.BitVec


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

-- set_option hygiene false in
-- run_cmd
--   for typeName' in [`UInt8, `UInt16, `UInt32, `UInt64, `USize] do
--   let typeName := Lean.mkIdent typeName'
--   Lean.Elab.Command.elabCommand (← `(
--     namespace $typeName

--       instance : Pow $typeName ℕ where
--         pow a n := ofBitVec ⟨a.toFin ^ n⟩

--       instance : SMul ℕ $typeName where
--         smul n a := ofBitVec ⟨n • a.toFin⟩

--       instance : SMul ℤ $typeName where
--         smul z a := ofBitVec ⟨z • a.toFin⟩

--       lemma neg_def (a : $typeName) : -a = ⟨⟨-a.toFin⟩⟩ := rfl

--       lemma nsmul_def (n : ℕ) (a : $typeName) : n • a = ⟨⟨n • a.toFin⟩⟩ := rfl

--       lemma zsmul_def (z : ℤ) (a : $typeName) : z • a = ⟨⟨z • a.toFin⟩⟩ := rfl

--       open $typeName (eq_of_toFin_eq) in
--       lemma toFin_injective : Function.Injective toFin := @eq_of_toFin_eq

--       @[deprecated toFin_injective (since := "2025-02-13")]
--       lemma val_injective : Function.Injective toFin := toFin_injective

--       open $typeName (eq_of_toBitVec_eq) in
--       lemma toBitVec_injective : Function.Injective toBitVec := @eq_of_toBitVec_eq

--       instance instCommMonoid : CommMonoid $typeName :=
--         Function.Injective.commMonoid toBitVec toBitVec_injective
--           rfl (fun _ _ => rfl) (fun _ _ => rfl)

--       instance instNonUnitalCommRing : NonUnitalCommRing $typeName :=
--         Function.Injective.nonUnitalCommRing toBitVec toBitVec_injective
--           rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
--           (fun _ _ => rfl) (fun _ _ => rfl)

--       local instance instNatCast : NatCast $typeName where
--         natCast n := ofBitVec n

--       lemma natCast_def (n : ℕ) : (n : $typeName) = ofBitVec n := rfl

--       lemma intCast_def (z : ℤ) : (z : $typeName) = ofBitVec z := rfl

--       local instance instCommRing : CommRing $typeName :=
--         Function.Injective.commRing toBitVec toBitVec_injective
--           rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
--           (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)

--       namespace CommRing
--       attribute [scoped instance] instCommRing instNatCast instIntCast
--       end CommRing

--     end $typeName
--   ))
--   -- interpolating docstrings above is more trouble than it's worth
--   let docString :=
--     s!"To use this instance, use `open scoped {typeName'}.CommRing`.\n\n" ++
--     "See the module docstring for an explanation"
--   Lean.addDocStringCore (typeName'.mkStr "instCommRing") docString
--   Lean.addDocStringCore (typeName'.mkStr "instNatCast") docString
--   Lean.addDocStringCore (typeName'.mkStr "instIntCast") docString

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

/-- The numbers from 0 to 256 are all valid UTF-8 characters, so we can embed one in the other. -/
def toChar (n : UInt8) : Char := ⟨n.toUInt32, .inl (Nat.lt_trans n.toBitVec.isLt (by decide))⟩

end UInt8
