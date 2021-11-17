import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs

lemma UInt8.size_positive : 0 < UInt8.size := by decide

lemma UInt16.size_positive : 0 < UInt16.size := by decide

lemma UInt32.size_positive : 0 < UInt32.size := by decide

lemma UInt64.size_positive : 0 < UInt64.size := by decide

lemma USize.size_positive : 0 < USize.size := usize_size_gt_zero

set_option hygiene false
local macro "genIntDeclars" typeName:ident : command => do
  let deltaName := Lean.mkIdent $ Lean.Name.mkSimple s!"instOfNat{typeName.getId}"
  `(
    namespace $typeName
    instance : Inhabited (Fin size) where
      default := Fin.ofNat' 0 size_positive

    lemma val_eq_of_lt : a < size → (ofNat a).val = a := Fin.val_eq_of_lt

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

    instance : AddSemigroup $typeName where
      add_assoc := fun _ _ _ => congrArg mk (AddSemigroup.add_assoc _ _ _)

    instance : AddCommSemigroup $typeName where
      add_comm := fun _ _ => congrArg mk (AddCommSemigroup.add_comm _ _)

    instance : Semigroup $typeName where
      mul_assoc := fun _ _ _ => congrArg mk (Semigroup.mul_assoc _ _ _)

    instance : CommSemigroup $typeName where
      mul_comm := fun _ _ => congrArg mk (CommSemigroup.mul_comm _ _)

    instance : AddMonoid $typeName :=
      let add_zero_ : ∀ (a : $typeName), a + 0 = a := fun a => by
        have h0 : a.val + (0 : $typeName).val = a.val := AddMonoid.add_zero a.val
        simp only [add_def, h0, mk_val_eq]
    {
      add_zero := add_zero_
      zero_add := fun _ => by rw [add_comm]; exact add_zero_ _
      nsmul := fun x a => ⟨AddMonoid.nsmul x a.val⟩
      nsmul_zero' := fun x => congrArg mk (AddMonoid.nsmul_zero' x.val)
      nsmul_succ' := fun n x => congrArg mk (AddMonoid.nsmul_succ' n x.val)
    }

    instance : AddCommMonoid $typeName where
      add_comm := add_comm

    instance : Neg $typeName where
      neg a := mk (-a.val)

    instance : SubNegMonoid $typeName where
      sub_eq_add_neg := fun _ _ => congrArg mk (SubNegMonoid.sub_eq_add_neg _ _)
      gsmul := fun x a => ⟨SubNegMonoid.gsmul x a.val⟩
      gsmul_zero' := fun a => congrArg mk (SubNegMonoid.gsmul_zero' a.val)
      gsmul_succ' := fun m a => congrArg mk (SubNegMonoid.gsmul_succ' m a.val)
      gsmul_neg' := fun m a => congrArg mk (SubNegMonoid.gsmul_neg' m a.val)

    instance : Monoid $typeName :=
      let mul_one_ : ∀ (a : $typeName), a * (1 : $typeName) = a := fun a => by
        have h0 : a.val * (1 : $typeName).val = a.val := Monoid.mul_one a.val
        simp only [mul_def, h0, mk_val_eq]
    {
      mul_one := mul_one_
      one_mul := by intro a; rw [mul_comm]; exact mul_one_ a
      npow_zero' := fun _ => rfl
      npow_succ' := fun _ _ => rfl
    }

    instance : CommMonoid $typeName where
      mul_comm := mul_comm

    lemma val_zero : (0 : $typeName).val = (0 : Fin size) := by
      delta OfNat.ofNat
      delta $deltaName
      simp only [ofNat, instOfNat, Zero.zero]

    lemma mk_zero_eq_zero : (mk (0 : Fin size)) = (0 : $typeName) := by
     delta OfNat.ofNat
     delta $deltaName
     simp only [ofNat, instOfNat, Zero.zero]

    instance : MonoidWithZero $typeName :=
      let zero_mul_ : ∀ (a : $typeName), 0 * a = 0 := fun a => by
        have h0 : (0 : $typeName).val * a.val = (0 : Fin size) := MonoidWithZero.zero_mul a.val
        simp only [mul_def, h0, mk_zero_eq_zero]
      {
        zero_mul := zero_mul_
        mul_zero := by intro a; rw [mul_comm]; exact zero_mul_ a
      }

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
