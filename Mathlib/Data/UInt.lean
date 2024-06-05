/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.Group.Fin
import Mathlib.Algebra.Group.Nat
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Basic
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

lemma UInt8.val_eq_of_lt {a : Nat} : a < UInt8.size → ((ofNat a).val : Nat) = a :=
  Nat.mod_eq_of_lt

lemma UInt16.val_eq_of_lt {a : Nat} : a < UInt16.size → ((ofNat a).val : Nat) = a :=
  Nat.mod_eq_of_lt

lemma UInt32.val_eq_of_lt {a : Nat} : a < UInt32.size → ((ofNat a).val : Nat) = a :=
  Nat.mod_eq_of_lt

lemma UInt64.val_eq_of_lt {a : Nat} : a < UInt64.size → ((ofNat a).val : Nat) = a :=
  Nat.mod_eq_of_lt

lemma USize.val_eq_of_lt {a : Nat} : a < USize.size → ((ofNat a).val : Nat) = a :=
  Nat.mod_eq_of_lt

instance UInt8.neZero : NeZero UInt8.size := ⟨by decide⟩

instance UInt16.neZero : NeZero UInt16.size := ⟨by decide⟩

instance UInt32.neZero : NeZero UInt32.size := ⟨by decide⟩

instance UInt64.neZero : NeZero UInt64.size := ⟨by decide⟩

instance USize.neZero : NeZero USize.size := NeZero.of_pos usize_size_gt_zero

example : (0 : UInt8) = ⟨0⟩ := rfl

set_option hygiene false in
run_cmd
  for typeName' in [`UInt8, `UInt16, `UInt32, `UInt64, `USize] do
  let typeName := Lean.mkIdent typeName'
  Lean.Elab.Command.elabCommand (← `(
    namespace $typeName
      instance : Inhabited $typeName where
        default := 0

      instance : Neg $typeName where
        neg a := mk (-a.val)

      instance : Pow $typeName ℕ where
        pow a n := mk (a.val ^ n)

      instance : SMul ℕ $typeName where
        smul n a := mk (n • a.val)

      instance : SMul ℤ $typeName where
        smul z a := mk (z • a.val)

      lemma zero_def : (0 : $typeName) = ⟨0⟩ := rfl

      lemma one_def : (1 : $typeName) = ⟨1⟩ := rfl

      lemma neg_def (a : $typeName) : -a = ⟨-a.val⟩ := rfl

      lemma sub_def (a b : $typeName) : a - b = ⟨a.val - b.val⟩ := rfl

      lemma mul_def (a b : $typeName) : a * b = ⟨a.val * b.val⟩ := rfl

      lemma mod_def (a b : $typeName) : a % b = ⟨a.val % b.val⟩ := rfl

      lemma add_def (a b : $typeName) : a + b = ⟨a.val + b.val⟩ := rfl

      lemma pow_def (a : $typeName) (n : ℕ) : a ^ n = ⟨a.val ^ n⟩ := rfl

      lemma nsmul_def (n : ℕ) (a : $typeName) : n • a = ⟨n • a.val⟩ := rfl

      lemma zsmul_def (z : ℤ) (a : $typeName) : z • a = ⟨z • a.val⟩ := rfl

      lemma eq_of_val_eq : ∀ {a b : $typeName}, a.val = b.val -> a = b
      | ⟨_⟩, ⟨_⟩, h => congrArg mk h

      lemma val_injective : Function.Injective val := @eq_of_val_eq

      lemma val_eq_of_eq : ∀ {a b : $typeName}, a = b -> a.val = b.val
      | ⟨_⟩, ⟨_⟩, h => congrArg val h

      @[simp] lemma mk_val_eq : ∀ (a : $typeName), mk a.val = a
      | ⟨_, _⟩ => rfl

      @[nolint docBlame]
      local instance instNatCast : NatCast $typeName where
        natCast n := mk n

      @[nolint docBlame]
      local instance instIntCast : IntCast $typeName where
        intCast z := mk z

      lemma natCast_def (n : ℕ) : (n : $typeName) = ⟨n⟩ := rfl

      lemma intCast_def (z : ℤ) : (z : $typeName) = ⟨z⟩ := rfl

      @[nolint docBlame]
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
