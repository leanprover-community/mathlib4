import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.ZMod.Defs

lemma UInt8.val_eq_of_lt {a : Nat} : a < UInt8.size -> (ofNat a).val = a := Nat.mod_eq_of_lt

lemma UInt16.val_eq_of_lt {a : Nat} : a < UInt16.size -> (ofNat a).val = a := Nat.mod_eq_of_lt

lemma UInt32.val_eq_of_lt {a : Nat} : a < UInt32.size -> (ofNat a).val = a := Nat.mod_eq_of_lt

lemma UInt64.val_eq_of_lt {a : Nat} : a < UInt64.size -> (ofNat a).val = a := Nat.mod_eq_of_lt

lemma USize.val_eq_of_lt {a : Nat} : a < USize.size -> (ofNat a).val = a := Nat.mod_eq_of_lt

instance UInt8.neZero : NeZero UInt8.size := ⟨by decide⟩
                                                 -- 🎉 no goals

instance UInt16.neZero : NeZero UInt16.size := ⟨by decide⟩
                                                   -- 🎉 no goals

instance UInt32.neZero : NeZero UInt32.size := ⟨by decide⟩
                                                   -- 🎉 no goals

instance UInt64.neZero : NeZero UInt64.size := ⟨by decide⟩
                                                   -- 🎉 no goals

instance USize.neZero : NeZero USize.size := NeZero.of_pos usize_size_gt_zero

example : (0 : UInt8) = ⟨0⟩ := rfl

set_option hygiene false in
run_cmd
  for typeName in [`UInt8, `UInt16, `UInt32, `UInt64, `USize].map Lean.mkIdent do
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

      instance : NatCast $typeName where
        natCast n := mk n

      instance : IntCast $typeName where
        intCast z := mk z

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

      lemma natCast_def (n : ℕ) : (n : $typeName) = ⟨n⟩ := rfl

      lemma intCast_def (z : ℤ) : (z : $typeName) = ⟨z⟩ := rfl

      lemma eq_of_val_eq : ∀ {a b : $typeName}, a.val = b.val -> a = b
      | ⟨_⟩, ⟨_⟩, h => congrArg mk h

      lemma val_injective : Function.Injective val := @eq_of_val_eq

      lemma val_eq_of_eq : ∀ {a b : $typeName}, a = b -> a.val = b.val
      | ⟨_⟩, ⟨_⟩, h => congrArg val h

      @[simp] lemma mk_val_eq : ∀ (a : $typeName), mk a.val = a
      | ⟨_, _⟩ => rfl

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

theorem toChar_aux (n : Nat) (h : n < size) : Nat.isValidChar (UInt32.ofNat n).1 := by
  rw [UInt32.val_eq_of_lt]
  -- ⊢ Nat.isValidChar n
  exact Or.inl $ Nat.lt_trans h $ by decide
  -- ⊢ n < UInt32.size
  exact Nat.lt_trans h $ by decide
  -- 🎉 no goals

/-- The numbers from 0 to 256 are all valid UTF-8 characters, so we can embed one in the other. -/
def toChar (n : UInt8) : Char := ⟨n.toUInt32, toChar_aux n.1 n.1.2⟩

end UInt8
