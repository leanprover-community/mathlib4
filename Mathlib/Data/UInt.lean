import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs

lemma UInt8.size_positive : 0 < UInt8.size := by decide

lemma UInt16.size_positive : 0 < UInt16.size := by decide

lemma UInt32.size_positive : 0 < UInt32.size := by decide

lemma UInt64.size_positive : 0 < UInt64.size := by decide

lemma USize.size_positive : 0 < USize.size := by
  simp only [USize.size]
  cases System.Platform.numBits_eq with
  | inl eq32 => simp [eq32]
  | inr eq64 => simp [eq64]

set_option hygiene false
macro "genIntDeclars" typeName:ident : command => do
  `(
    namespace $typeName
      instance : Zero (Fin size) := (Nat.succ_pred_eq_of_pos size_positive) ▸ inferInstance

      instance : One (Fin size) := (Nat.succ_pred_eq_of_pos size_positive) ▸ inferInstance

      instance : Neg (Fin size) := (Nat.succ_pred_eq_of_pos size_positive) ▸ inferInstance

      instance : AddSemigroup (Fin size) := (Nat.succ_pred_eq_of_pos size_positive) ▸ inferInstance

      instance : AddMonoid (Fin size) := (Nat.succ_pred_eq_of_pos size_positive) ▸ inferInstance

      instance : AddCommMonoid (Fin size) := (Nat.succ_pred_eq_of_pos size_positive) ▸ inferInstance

      instance : SubNegMonoid (Fin size) := (Nat.succ_pred_eq_of_pos size_positive) ▸ inferInstance

      instance : AddGroup (Fin size) := (Nat.succ_pred_eq_of_pos size_positive) ▸ inferInstance

      instance : Monoid (Fin size) := (Nat.succ_pred_eq_of_pos size_positive) ▸ inferInstance

      instance : CommMonoid (Fin size) := (Nat.succ_pred_eq_of_pos size_positive) ▸ inferInstance

      instance : MonoidWithZero (Fin size) := (Nat.succ_pred_eq_of_pos size_positive) ▸ inferInstance

      lemma val_eq_of_lt : a < size → (ofNat a).val = a := Fin.val_eq_of_lt

      lemma sub_def (a b : $typeName) : a - b = ⟨a.val - b.val⟩ := rfl

      lemma mul_def (a b : $typeName) : a * b = ⟨a.val * b.val⟩ := rfl

      lemma mod_def (a b : $typeName) : a % b = ⟨a.val % b.val⟩ := rfl

      lemma add_def (a b : $typeName) : a + b = ⟨a.val + b.val⟩ := rfl

      lemma eq_of_val_eq : ∀ {a b : $typeName}, a.val = b.val -> a = b
      | ⟨f1⟩, ⟨f2⟩, h => congrArg mk h

      lemma val_eq_of_eq : ∀ {a b : $typeName}, a = b -> a.val = b.val
      | ⟨f1⟩, ⟨f2⟩, h => congrArg val h

      @[simp] lemma mk_val_eq (a : $typeName) : mk a.val = a := by
        cases h:a with
        | mk aFin =>
          have _ : a.val = aFin := h ▸ rfl
          simp only [‹a.val = aFin›]

      lemma add_assoc (a b c : $typeName) : (a + b) + c = a + (b + c) :=
        congrArg mk (Fin.add_assoc _ _ _)

      lemma mul_comm (a b : $typeName) : a * b = b * a := congrArg mk (Fin.mul_comm _ _)

      lemma add_comm (a b : $typeName) : a + b = b + a := congrArg mk (Fin.add_comm _ _)

      @[simp] lemma add_zero (a : $typeName) : a + 0 = a := by
        have h0 : a.val + (0 : $typeName).val = a.val := AddMonoid.add_zero a.val
        simp only [add_def, h0, mk_val_eq]

      @[simp] lemma zero_add (a : $typeName) : 0 + a = a :=
        (add_comm _ _) ▸ add_zero _

      @[simp] lemma zero_mul (a : $typeName) : 0 * a = 0 := by
        have h0 : (0 : $typeName).val * a.val = (0 : Fin size) := MonoidWithZero.zero_mul a.val
        simp only [mul_def, h0, mk_val_eq]

      @[simp] lemma mul_zero (a : $typeName) : a * 0 = 0 :=
        (mul_comm a _) ▸ zero_mul _

      @[simp] lemma one_mul (a : $typeName) : 1 * a = a := by
        have h0 : (1 : $typeName).val * a.val = a.val := Monoid.one_mul a.val
        simp only [mul_def, h0, mk_val_eq]

      @[simp] lemma mul_one (a : $typeName) : a * 1 = a := (mul_comm _ _) ▸ one_mul _

      instance : Neg $typeName where
        neg a := mk (-a.val)

      lemma neg_def (a : $typeName) : -a = mk (-a.val) := rfl

      lemma sub_eq_add_neg (a b : $typeName) : a - b = a + -b :=
        congrArg mk (SubNegMonoid.sub_eq_add_neg _ _)

      def nsmul (x : Nat) (a : $typeName) : $typeName := mk (AddMonoid.nsmul x a.val)

      def gsmul (x : Int) (a : $typeName) : $typeName := mk (SubNegMonoid.gsmul x a.val)

      @[simp] lemma gsmul_zero' (a : $typeName) : gsmul 0 a = (0 : $typeName) :=
        congrArg mk (SubNegMonoid.gsmul_zero' a.val)

      lemma gsmul_succ' (m : ℕ) (a : $typeName) : gsmul (Int.ofNat m.succ) a = a + gsmul (Int.ofNat m) a :=
        congrArg mk (SubNegMonoid.gsmul_succ' m a.val)

      lemma gsmul_neg' (m : ℕ) (a : $typeName) : gsmul (Int.negSucc m) a = -(gsmul m.succ a) :=
        congrArg mk (SubNegMonoid.gsmul_neg' m a.val)

      instance : AddSemigroup $typeName where
        add_assoc := add_assoc

      @[simp] lemma nsmul_zero' (x : $typeName) : nsmul 0 x = 0 :=
        congrArg mk (AddMonoid.nsmul_zero' x.val)

      lemma nsmul_succ' (n : ℕ) (x : $typeName) : nsmul n.succ x = x + nsmul n x :=
        congrArg mk (AddMonoid.nsmul_succ' n x.val)

      @[simp] lemma add_left_neg (a : $typeName) : -a + a = 0 :=
        congrArg mk (AddGroup.add_left_neg a.val)

      lemma mul_assoc (a b c : $typeName) : (a * b) * c = a * (b * c) :=
        congrArg mk (Semigroup.mul_assoc _ _ _)

      instance : AddMonoid $typeName where
        add_zero := add_zero
        zero_add := zero_add
        nsmul := nsmul
        nsmul_zero' := nsmul_zero'
        nsmul_succ' := nsmul_succ'

      instance : AddCommMonoid $typeName where
        add_comm := add_comm

      instance : SubNegMonoid $typeName where
        sub_eq_add_neg := sub_eq_add_neg
        gsmul := gsmul
        gsmul_zero' := gsmul_zero'
        gsmul_succ' := gsmul_succ'
        gsmul_neg' := gsmul_neg'

      instance : Monoid $typeName where
        mul_one := mul_one
        one_mul := one_mul
        mul_assoc := mul_assoc
        npow_zero' := fun _ => rfl
        npow_succ' := fun _ _ => rfl

      instance : CommMonoid $typeName where
        mul_comm := mul_comm

      instance : MonoidWithZero $typeName where
        zero_mul := zero_mul
        mul_zero := mul_zero

      def addOverflows? (a b : $typeName) : Bool := size <= a.toNat + b.toNat

      def mulOverflows? (a b : $typeName) : Bool := size <= a.toNat * b.toNat

      def subUnderflows? (a b : $typeName) : Bool := a.toNat < b.toNat

      def overflowingAdd (a b : $typeName) : (Bool × $typeName) := (size <= a.toNat + b.toNat, a + b)

      def overflowingMul (a b : $typeName) : (Bool × $typeName) := (size <= a.toNat * b.toNat, a * b)

      def underflowingSub (a b : $typeName) : (Bool × $typeName) := (a.toNat < b.toNat, a - b)

      def checkedAdd (a b : $typeName) : Option $typeName :=
        match a.overflowingAdd b with
        | (true, _) => none
        | (false, sum) => some (sum)

      def checkedMul (a b : $typeName) : Option $typeName :=
        match a.overflowingMul b with
        | (true, _) => none
        | (false, prod) => some (prod)

      def checkedSub (a b : $typeName) : Option $typeName :=
        match a.underflowingSub b with
        | (true, _) => none
        | (false, diff) => some (diff)

      lemma checked_add_spec (a b : $typeName) : (a.checkedAdd b).isSome = true <-> a.toNat + b.toNat < size := by
        by_cases size <= a.toNat + b.toNat <;>
          simp_all [checkedAdd, Option.isSome, overflowingAdd, decide_eq_true, decide_eq_false]

      lemma checked_mul_spec (a b : $typeName) : (a.checkedMul b).isSome = true <-> a.toNat * b.toNat < size := by
        simp only [checkedMul, overflowingMul, Option.isSome]
        refine Iff.intro ?mp ?mpr <;> intro h
        case mp =>
          by_cases hx : size <= a.toNat * b.toNat
          case pos => simp only [(decide_eq_true_iff (size <= a.toNat * b.toNat)).mpr hx] at h
          case neg => exact Nat.lt_of_not_le hx
        case mpr => simp only [decide_eq_false (Nat.not_le_of_lt h : ¬size <= a.toNat * b.toNat)]

      lemma checked_sub_spec (a b : $typeName) : (a.checkedSub b).isSome = true <-> b.toNat <= a.toNat := by
        simp only [checkedSub, underflowingSub, Option.isSome]
        refine Iff.intro ?mp ?mpr <;> intro h
        case mp =>
          by_cases hx : a.val < b.val
          case pos => simp only [(decide_eq_true_iff (a.toNat < b.toNat)).mpr hx] at h
          case neg => exact Nat.le_of_not_lt hx
        case mpr => simp only [decide_eq_false (Nat.not_lt_of_le h : ¬a.toNat < b.toNat)]

      lemma mod_lt (x : $typeName) {y : $typeName} : 0 < y -> x % y < y :=
        fun y_pos => Fin.mod_lt x.val y_pos

      lemma mod_eq_of_lt {a b : $typeName} : a < b -> a % b = a :=
        fun a_lt_b => eq_of_val_eq (Fin.mod_eq_of_lt a_lt_b)

    end $typeName
  )

genIntDeclars UInt8
genIntDeclars UInt16
genIntDeclars UInt32
genIntDeclars UInt64
--genIntDeclars USize

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
