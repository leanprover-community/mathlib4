import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Group.Defs

section Fin

variable {n : Nat}

instance : Zero (Fin n.succ) where
  zero := Fin.ofNat 0

@[simp]
lemma Fin.val_zero : (0 : Fin n.succ).val = (0 : Nat) :=
  show (Fin.ofNat 0).val = 0 by simp [Fin.ofNat]

instance : One (Fin n.succ) where
  one := ⟨1 % n.succ, Nat.mod_lt 1 (Nat.zero_lt_succ n)⟩

@[simp]
lemma Fin.of_nat_zero : (Fin.ofNat 0 : Fin n.succ) = (0 : Fin n.succ) := by
  apply Fin.eq_of_val_eq; simp only [Fin.ofNat, Nat.zero_mod, Fin.val_zero]

@[simp]
lemma Fin.val_one : (1 : Fin n.succ).val = (1 % n.succ : Nat) := by
  have h0 : ∀ x, (OfNat.ofNat x : Fin n.succ) = Fin.ofNat x := by simp [OfNat.ofNat]
  simp only [h0, Fin.ofNat]

/-- If you actually have an element of `Fin n`, then the `n` is always positive -/
lemma Fin.positive_size : ∀ (x : Fin n), 0 < n
| ⟨x, h⟩ =>
  match Nat.eq_or_lt_of_le (Nat.zero_le x) with
  | Or.inl h_eq => h_eq ▸ h
  | Or.inr h_lt => Nat.lt_trans h_lt h

lemma Fin.modn_def : ∀ (a : Fin n) (m : Nat), a % m = Fin.mk ((a.val % m) % n) (Nat.mod_lt (a.val % m) (Fin.positive_size a))
| ⟨a, pa⟩, m => by simp only [HMod.hMod, Fin.modn]

lemma Fin.add_def : ∀ (a b : Fin n), a + b = (Fin.mk ((a.val + b.val) % n) (Nat.mod_lt _ (Fin.positive_size a)))
| ⟨a, pa⟩, ⟨b, pb⟩ => by simp only [HAdd.hAdd, Add.add, Fin.add]

lemma Fin.mul_def : ∀ (a b : Fin n), a * b = (Fin.mk ((a.val * b.val) % n) (Nat.mod_lt _ (Fin.positive_size a)))
| ⟨a, pa⟩, ⟨b, pb⟩ => by simp only [HMul.hMul, Mul.mul, Fin.mul]

lemma Fin.sub_def : ∀ (a b : Fin n), a - b = (Fin.mk ((a + (n - b)) % n) (Nat.mod_lt _ (Fin.positive_size a)))
| ⟨a, pa⟩, ⟨b, pb⟩ => by simp only [HSub.hSub, Sub.sub, Fin.sub]

@[simp] lemma Fin.mod_eq (a : Fin n) : a % n = a := by
  apply Fin.eq_of_val_eq
  simp only [Fin.modn_def, Nat.mod_mod]
  exact Nat.mod_eq_of_lt a.isLt

lemma Fin.add_comm (a b : Fin n) : a + b = b + a := by
apply Fin.eq_of_val_eq
simp only [Fin.add_def, Nat.add_comm]

@[simp] lemma Fin.add_zero (a : Fin n.succ) : a + 0 = a := by
apply Fin.eq_of_val_eq
simp only [Fin.add_def, Fin.val_zero, Nat.add_zero]
exact Nat.mod_eq_of_lt a.isLt

@[simp] lemma Fin.zero_add (a : Fin n.succ) : 0 + a = a := by
rw [Fin.add_comm]
exact Fin.add_zero a

@[simp] lemma Fin.zero_mul (a : Fin n.succ) : 0 * a = 0 := by
apply Fin.eq_of_val_eq
simp only [Fin.mul_def, Fin.val_zero, Nat.zero_mul]
simp [Nat.zero_mod]

lemma Fin.mul_comm (a b : Fin n) : a * b = b * a := by
apply Fin.eq_of_val_eq
simp only [Fin.mul_def, Nat.mul_comm]

lemma Fin.add_assoc (a b c : Fin n) : (a + b) + c = a + (b + c) := by
apply Fin.eq_of_val_eq
simp only [Fin.mul_def, Fin.add_def, Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc]

instance : Neg (Fin n) where
  neg a := ⟨(n - a) % n, Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le _) a.isLt)⟩

@[simp] lemma Fin.add_left_neg : ∀ (a : Fin n.succ), -a + a = 0
| ⟨a, isLt⟩ => by
  apply Fin.eq_of_val_eq
  simp only [Neg.neg, Fin.add_def, Fin.val_zero]
  cases a with
  | zero => rw [Nat.sub_zero, Nat.add_zero, Nat.mod_mod, Nat.mod_self]
  | succ a =>
    have h1 : (n.succ - a.succ) % n.succ = (n.succ - a.succ) :=
      Nat.mod_eq_of_lt (Nat.sub_lt (Nat.succ_pos _) (Nat.succ_pos _))
    have h_aux : (Nat.succ n - Nat.succ a + Nat.succ a) = Nat.succ n := by
      rw [Nat.add_comm]
      exact Nat.add_sub_of_le (Nat.le_of_lt isLt)
    rw [h1, h_aux, Nat.mod_self]

def Fin.nsmul (x : Nat) (a : Fin n.succ) : Fin n.succ := (Fin.ofNat x) * a

def Fin.gsmul (x : Int) (a : Fin n.succ) : Fin n.succ :=
  match x with
  | Int.ofNat x' => Fin.nsmul x' a
  | Int.negSucc x' => -(Fin.nsmul x'.succ a)

/- Aux lemma that makes nsmul_succ' easier -/
lemma Fin.nsmuls_eq (x : Nat) : ∀ (a : Fin n.succ), Fin.nsmul x a = Fin.ofNat (x * a.val)
| ⟨a, isLt⟩ => by
  apply Fin.eq_of_val_eq
  simp only [Fin.nsmul, Fin.ofNat, Fin.mul_def]
  have hh : a % n.succ = a := Nat.mod_eq_of_lt isLt
  generalize hq : x * a % Nat.succ n = q
  rw [<- hh, <- Nat.mul_mod, hq]

lemma Fin.nsmul_succ' (x : Nat) (a : Fin n.succ) : Fin.nsmul x.succ a = a + (Fin.nsmul x a) := by
  simp only [Fin.nsmuls_eq]
  simp [nsmul, Fin.ofNat, Fin.add_def]
  exact congrArg (fun x => x % n.succ) (Nat.add_comm (x * a.val) (a.val) ▸ Nat.succ_mul x a.val)

lemma Fin.sub_eq_add_neg (a b : Fin n) : a - b = a + -b := by
  simp [Fin.add_def, Fin.sub_def, Neg.neg]

@[simp] lemma Fin.gsmul_zero' (a : Fin n.succ) : Fin.gsmul 0 a = (0 : Fin n.succ) := by
  simp only [Fin.gsmul, Fin.nsmul, Fin.of_nat_zero, Fin.zero_mul]

lemma Fin.gsmul_succ' (m : ℕ) (a : Fin n.succ) : Fin.gsmul (Int.ofNat m.succ) a = a + Fin.gsmul (Int.ofNat m) a := by
  simp only [Fin.gsmul, Fin.nsmul_succ']

lemma Fin.gsmul_neg' (m : ℕ) (a : Fin n.succ) : gsmul (Int.negSucc m) a = -(gsmul (m.succ) a) := by
  simp only [Fin.gsmul, Fin.nsmul]

instance : AddSemigroup (Fin n.succ) where
  add_assoc := Fin.add_assoc

instance : AddMonoid (Fin n.succ) where
  add_zero := Fin.add_zero
  zero_add := Fin.zero_add
  nsmul := Fin.nsmul
  nsmul_zero' := Fin.zero_mul
  nsmul_succ' := Fin.nsmul_succ'

instance : SubNegMonoid (Fin n.succ) where
  sub_eq_add_neg := Fin.sub_eq_add_neg
  gsmul := Fin.gsmul
  gsmul_zero' := Fin.gsmul_zero'
  gsmul_succ' := Fin.gsmul_succ'
  gsmul_neg' := Fin.gsmul_neg'

instance : AddGroup (Fin n.succ) where
  add_left_neg := Fin.add_left_neg

def Fin.overflowingAdd (a b : Fin n) : (Bool × Fin n) := (n <= a.val + b.val, a + b)

def Fin.overflowingMul (a b : Fin n) : (Bool × Fin n) := (n <= a.val * b.val, a * b)

def Fin.underflowingSub (a b : Fin n) : (Bool × Fin n) := (a.val < b.val, a - b)

def Fin.checkedAdd (a b : Fin n) : Option (Fin n) :=
  match Fin.overflowingAdd a b with
  | (true, _) => none
  | (false, sum) => some (sum)

def Fin.checkedMul (a b : Fin n) : Option (Fin n) :=
  match Fin.overflowingMul a b with
  | (true, _) => none
  | (false, prod) => some (prod)

def Fin.checkedSub (a b : Fin n) : Option (Fin n) :=
  match Fin.underflowingSub a b with
  | (true, _) => none
  | (false, diff) => some (diff)

lemma Fin.checked_add_spec (a b : Fin n) : (Fin.checkedAdd a b).isSome = true <-> a.val + b.val < n := by
  by_cases n <= a.val + b.val <;>
    simp_all [checkedAdd, Option.isSome, overflowingAdd, decide_eq_true, decide_eq_false]

lemma Fin.checked_mul_spec (a b : Fin n) : (Fin.checkedMul a b).isSome = true <-> a.val * b.val < n := by
  simp only [checkedMul, overflowingMul, Option.isSome]
  refine Iff.intro ?mp ?mpr <;> intro h
  case mp =>
    by_cases hx : n <= a.val * b.val
    case pos => simp only [(decide_eq_true_iff (n <= a.val * b.val)).mpr hx] at h
    case neg => exact Nat.lt_of_not_le hx
  case mpr => simp only [decide_eq_false (Nat.not_le_of_lt h : ¬n <= a.val * b.val)]

lemma Fin.checked_sub_spec (a b : Fin n) : (Fin.checkedSub a b).isSome = true <-> b.val <= a.val := by
  simp only [checkedSub, underflowingSub, Option.isSome]
  refine Iff.intro ?mp ?mpr <;> intro h
  case mp =>
    by_cases hx : a.val < b.val
    case pos => simp only [(decide_eq_true_iff (a.val < b.val)).mpr hx] at h
    case neg => exact Nat.le_of_not_lt hx
  case mpr => simp only [decide_eq_false (Nat.not_lt_of_le h : ¬a.val < b.val)]

end Fin
