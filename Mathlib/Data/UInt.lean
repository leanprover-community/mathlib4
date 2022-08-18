import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Basic

lemma UInt8.size_positive : 0 < UInt8.size := by decide

lemma UInt16.size_positive : 0 < UInt16.size := by decide

lemma UInt32.size_positive : 0 < UInt32.size := by decide

lemma UInt64.size_positive : 0 < UInt64.size := by decide

lemma USize.size_positive : 0 < USize.size := usize_size_gt_zero

lemma UInt8.val_eq_of_lt {a : Nat} : a < UInt8.size -> (ofNat a).val = a := Fin.val_eq_of_lt

lemma UInt16.val_eq_of_lt {a : Nat} : a < UInt16.size -> (ofNat a).val = a := Fin.val_eq_of_lt

lemma UInt32.val_eq_of_lt {a : Nat} : a < UInt32.size -> (ofNat a).val = a := Fin.val_eq_of_lt

lemma UInt64.val_eq_of_lt {a : Nat} : a < UInt64.size -> (ofNat a).val = a := Fin.val_eq_of_lt

lemma USize.val_eq_of_lt {a : Nat} : a < USize.size -> (ofNat a).val = a := Fin.val_eq_of_lt

set_option hygiene false
/-- `genIntDeclars UInt8` generates a `CommRing UInt8` instance.  -/
local macro "genIntDeclars" typeName:ident : command => do
  `(
    namespace $typeName
      instance : Inhabited (Fin size) where
        default := Fin.ofNat' 0 size_positive

      instance : AddSemigroup $typeName where
        add_assoc := fun _ _ _ => congrArg mk (AddSemigroup.add_assoc _ _ _)

      instance : AddCommSemigroup $typeName where
        add_comm := fun _ _ => congrArg mk (AddCommSemigroup.add_comm _ _)

      instance : Semigroup $typeName where
        mul_assoc := fun _ _ _ => congrArg mk (Semigroup.mul_assoc _ _ _)

      instance : Neg $typeName where
        neg a := mk (-a.val)

      lemma sub_def (a b : $typeName) : a - b = ⟨a.val - b.val⟩ := rfl

      lemma mul_def (a b : $typeName) : a * b = ⟨a.val * b.val⟩ := rfl

      lemma mod_def (a b : $typeName) : a % b = ⟨a.val % b.val⟩ := rfl

      lemma add_def (a b : $typeName) : a + b = ⟨a.val + b.val⟩ := rfl

      lemma eq_of_val_eq : ∀ {a b : $typeName}, a.val = b.val -> a = b
      | ⟨f1⟩, ⟨f2⟩, h => congrArg mk h

      lemma val_eq_of_eq : ∀ {a b : $typeName}, a = b -> a.val = b.val
      | ⟨f1⟩, ⟨f2⟩, h => congrArg val h

      @[simp] lemma mk_val_eq : ∀ (a : $typeName), mk a.val = a
      | ⟨a, _⟩ => rfl

      lemma zero_def : (0 : $typeName) = ⟨0⟩ := rfl

      lemma neg_def (a : $typeName) : -a = ⟨-a.val⟩ := rfl

      lemma one_def : (1 : $typeName) = ⟨1⟩ := rfl

      instance : Semiring $typeName where
        add_zero := by simp [add_def, zero_def]
        zero_add := by simp [add_def, zero_def]
        add_comm := by simp [add_def, add_comm]
        mul_one  := by simp [mul_def, one_def]
        one_mul  := by simp [mul_def, one_def]
        nsmul n a := ⟨AddMonoid.nsmul n a.val⟩
        nsmul_zero' x := congrArg mk (AddMonoid.nsmul_zero' x.val)
        nsmul_succ' n a := congrArg mk (AddMonoid.nsmul_succ' n a.val)
        zero_mul := by simp [mul_def, zero_def]
        mul_zero := by simp [mul_def, zero_def]
        npow_zero' := fun _ => rfl
        npow_succ' := fun _ _ => rfl
        right_distrib a b c := by
          simp only [mul_def, add_def]
          apply eq_of_val_eq
          exact right_distrib a.val b.val c.val
        left_distrib a b c := by
          simp only [mul_def, add_def]
          apply eq_of_val_eq
          exact left_distrib a.val b.val c.val
        natCast n := ⟨n⟩
        natCast_zero := rfl
        natCast_succ _ := congrArg mk (Fin.ofNat'_succ)
        __ := inferInstanceAs (AddCommSemigroup $typeName)
        __ := inferInstanceAs (Semigroup $typeName)

      instance : Ring $typeName where
        sub_eq_add_neg := fun _ _ => congrArg mk (sub_eq_add_neg _ _)
        gsmul := fun x a => mk (Ring.gsmul x a.val)
        gsmul_zero' := fun a => congrArg mk (SubNegMonoid.gsmul_zero' a.val)
        gsmul_succ' := fun x a => congrArg mk (SubNegMonoid.gsmul_succ' x a.val)
        gsmul_neg' := fun x a => congrArg mk (SubNegMonoid.gsmul_neg' x a.val)
        add_left_neg := fun a => by apply eq_of_val_eq; simp [neg_def, add_def, zero_def]
        intCast n := ⟨n⟩
        intCast_ofNat _ := rfl
        intCast_negSucc _ := rfl

      instance : CommRing $typeName where
        mul_comm := fun _ _ => by
          apply eq_of_val_eq
          simp [mul_def, zero_def]
          exact mul_comm _ _

    end $typeName
  )

genIntDeclars UInt8
genIntDeclars UInt16
genIntDeclars UInt32
genIntDeclars UInt64
genIntDeclars USize

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
  exact Or.inl $ Nat.lt_trans h $ by decide
  exact Nat.lt_trans h $ by decide

/-- The numbers from 0 to 256 are all valid UTF-8 characters, so we can embed one in the other. -/
def toChar (n : UInt8) : Char := ⟨n.toUInt32, toChar_aux n.1 n.1.2⟩

end UInt8
