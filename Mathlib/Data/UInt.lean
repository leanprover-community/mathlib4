import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs

theorem UInt32.val_eq_of_lt : a < UInt32.size → (UInt32.ofNat a).val = a := Fin.val_eq_of_lt

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

lemma UInt8.sub_def (a b : UInt8) : a - b = UInt8.mk (a.val - b.val) := rfl

lemma UInt8.mul_def (a b : UInt8) : a * b = UInt8.mk (a.val * b.val) := rfl

lemma UInt8.mod_def (a b : UInt8) : a % b = UInt8.mk (a.val % b.val) := rfl

lemma UInt8.add_def (a b : UInt8) : a + b = UInt8.mk (a.val + b.val) := rfl

lemma UInt8.eq_of_val_eq : ∀ {a b : UInt8}, a.val = b.val -> a = b
| ⟨f1⟩, ⟨f2⟩, h => congrArg mk h

lemma UInt8.val_eq_of_eq : ∀ {a b : UInt8}, a = b -> a.val = b.val
| ⟨f1⟩, ⟨f2⟩, h => congrArg val h

@[simp] lemma UInt8.mk_val_eq (a : UInt8) : mk a.val = a := by
  cases h:a with
  | mk aFin =>
    have _ : a.val = aFin := h ▸ rfl
    simp only [‹a.val = aFin›]

lemma UInt8.add_assoc (a b c : UInt8) : (a + b) + c = a + (b + c) :=
  congrArg UInt8.mk (Fin.add_assoc _ _ _)

lemma UInt8.mul_comm (a b : UInt8) : a * b = b * a := congrArg UInt8.mk (Fin.mul_comm _ _)

lemma UInt8.add_comm (a b : UInt8) : a + b = b + a := congrArg UInt8.mk (Fin.add_comm _ _)

@[simp] lemma UInt8.add_zero (a : UInt8) : a + 0 = a := by
  have h0 : a.val + (0 : UInt8).val = a.val := AddMonoid.add_zero a.val
  simp only [UInt8.add_def, h0, UInt8.mk_val_eq]

@[simp] lemma UInt8.zero_add (a : UInt8) : 0 + a = a :=
  (UInt8.add_comm _ _) ▸ UInt8.add_zero _

@[simp] lemma UInt8.zero_mul (a : UInt8) : 0 * a = 0 := by
  have h0 : (0 : UInt8).val * a.val = (0 : Fin UInt8.size) := MonoidWithZero.zero_mul a.val
  simp only [UInt8.mul_def, h0, UInt8.mk_val_eq]

@[simp] lemma UInt8.mul_zero (a : UInt8) : a * 0 = 0 :=
  (UInt8.mul_comm a _) ▸ UInt8.zero_mul _

@[simp] lemma UInt8.one_mul (a : UInt8) : 1 * a = a := by
  have h0 : (1 : UInt8).val * a.val = a.val := Monoid.one_mul a.val
  simp only [UInt8.mul_def, h0, UInt8.mk_val_eq]

@[simp] lemma UInt8.mul_one (a : UInt8) : a * 1 = a := (UInt8.mul_comm _ _) ▸ UInt8.one_mul _

instance : Neg UInt8 where
  neg a := UInt8.mk (-a.val)

lemma UInt8.neg_def (a : UInt8) : -a = UInt8.mk (-a.val) := rfl

lemma UInt8.sub_eq_add_neg (a b : UInt8) : a - b = a + -b :=
  congrArg UInt8.mk (SubNegMonoid.sub_eq_add_neg _ _)

def UInt8.nsmul (x : Nat) (a : UInt8) : UInt8 := UInt8.mk (AddMonoid.nsmul x a.val)

def UInt8.gsmul (x : Int) (a : UInt8) : UInt8 := UInt8.mk (SubNegMonoid.gsmul x a.val)

@[simp] lemma UInt8.gsmul_zero' (a : UInt8) : UInt8.gsmul 0 a = (0 : UInt8) :=
  congrArg UInt8.mk (SubNegMonoid.gsmul_zero' a.val)

lemma UInt8.gsmul_succ' (m : ℕ) (a : UInt8) : UInt8.gsmul (Int.ofNat m.succ) a = a + UInt8.gsmul (Int.ofNat m) a :=
  congrArg UInt8.mk (SubNegMonoid.gsmul_succ' m a.val)

lemma UInt8.gsmul_neg' (m : ℕ) (a : UInt8) : gsmul (Int.negSucc m) a = -(gsmul m.succ a) :=
  congrArg UInt8.mk (SubNegMonoid.gsmul_neg' m a.val)

instance : AddSemigroup UInt8 where
  add_assoc := UInt8.add_assoc

@[simp] lemma UInt8.nsmul_zero' (x : UInt8) : UInt8.nsmul 0 x = 0 :=
  congrArg UInt8.mk (AddMonoid.nsmul_zero' x.val)

lemma UInt8.nsmul_succ' (n : ℕ) (x : UInt8) : UInt8.nsmul n.succ x = x + UInt8.nsmul n x :=
  congrArg UInt8.mk (AddMonoid.nsmul_succ' n x.val)

@[simp] lemma UInt8.add_left_neg (a : UInt8) : -a + a = 0 :=
  congrArg UInt8.mk (AddGroup.add_left_neg a.val)

lemma UInt8.mul_assoc (a b c : UInt8) : (a * b) * c = a * (b * c) :=
  congrArg UInt8.mk (Semigroup.mul_assoc _ _ _)

instance : AddMonoid UInt8 where
  add_zero := UInt8.add_zero
  zero_add := UInt8.zero_add
  nsmul := UInt8.nsmul
  nsmul_zero' := UInt8.nsmul_zero'
  nsmul_succ' := UInt8.nsmul_succ'

instance : AddCommMonoid UInt8 where
  add_comm := UInt8.add_comm

instance : SubNegMonoid UInt8 where
  sub_eq_add_neg := UInt8.sub_eq_add_neg
  gsmul := UInt8.gsmul
  gsmul_zero' := UInt8.gsmul_zero'
  gsmul_succ' := UInt8.gsmul_succ'
  gsmul_neg' := UInt8.gsmul_neg'

instance : Monoid UInt8 where
  mul_one := UInt8.mul_one
  one_mul := UInt8.one_mul
  mul_assoc := UInt8.mul_assoc
  npow_zero' := fun _ => rfl
  npow_succ' := fun _ _ => rfl

instance : CommMonoid UInt8 where
  mul_comm := UInt8.mul_comm

instance : MonoidWithZero UInt8 where
  zero_mul := UInt8.zero_mul
  mul_zero := UInt8.mul_zero

def UInt8.addOverflows? (a b : UInt8) : Bool := UInt8.size <= a.toNat + b.toNat

def UInt8.mulOverflows? (a b : UInt8) : Bool := UInt8.size <= a.toNat * b.toNat

def UInt8.subUnderflows? (a b : UInt8) : Bool := a.toNat < b.toNat

def UInt8.overflowingAdd (a b : UInt8) : (Bool × UInt8) := (UInt8.size <= a.toNat + b.toNat, a + b)

def UInt8.overflowingMul (a b : UInt8) : (Bool × UInt8) := (UInt8.size <= a.toNat * b.toNat, a * b)

def UInt8.underflowingSub (a b : UInt8) : (Bool × UInt8) := (a.toNat < b.toNat, a - b)

def UInt8.checkedAdd (a b : UInt8) : Option UInt8 :=
  match a.overflowingAdd b with
  | (true, _) => none
  | (false, sum) => some (sum)

def UInt8.checkedMul (a b : UInt8) : Option UInt8 :=
  match a.overflowingMul b with
  | (true, _) => none
  | (false, prod) => some (prod)

def UInt8.checkedSub (a b : UInt8) : Option UInt8 :=
  match a.underflowingSub b with
  | (true, _) => none
  | (false, diff) => some (diff)

lemma UInt8.checked_add_spec (a b : UInt8) : (UInt8.checkedAdd a b).isSome = true <-> a.toNat + b.toNat < UInt8.size := by
  by_cases UInt8.size <= a.toNat + b.toNat <;>
    simp_all [checkedAdd, Option.isSome, overflowingAdd, decide_eq_true, decide_eq_false]

lemma UInt8.checked_mul_spec (a b : UInt8) : (UInt8.checkedMul a b).isSome = true <-> a.toNat * b.toNat < UInt8.size := by
  simp only [checkedMul, overflowingMul, Option.isSome]
  refine Iff.intro ?mp ?mpr <;> intro h
  case mp =>
    by_cases hx : UInt8.size <= a.toNat * b.toNat
    case pos => simp only [(decide_eq_true_iff (UInt8.size <= a.toNat * b.toNat)).mpr hx] at h
    case neg => exact Nat.lt_of_not_le hx
  case mpr => simp only [decide_eq_false (Nat.not_le_of_lt h : ¬UInt8.size <= a.toNat * b.toNat)]

lemma UInt8.checked_sub_spec (a b : UInt8) : (UInt8.checkedSub a b).isSome = true <-> b.toNat <= a.toNat := by
  simp only [checkedSub, underflowingSub, Option.isSome]
  refine Iff.intro ?mp ?mpr <;> intro h
  case mp =>
    by_cases hx : a.val < b.val
    case pos => simp only [(decide_eq_true_iff (a.toNat < b.toNat)).mpr hx] at h
    case neg => exact Nat.le_of_not_lt hx
  case mpr => simp only [decide_eq_false (Nat.not_lt_of_le h : ¬a.toNat < b.toNat)]
