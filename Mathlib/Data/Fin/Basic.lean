import Mathlib.Data.Nat.Basic
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs

/-- If you actually have an element of `Fin n`, then the `n` is always positive -/
lemma Fin.positive_size : ∀ (x : Fin n), 0 < n
| ⟨x, h⟩ =>
  match Nat.eq_or_lt_of_le (Nat.zero_le x) with
  | Or.inl h_eq => h_eq ▸ h
  | Or.inr h_lt => Nat.lt_trans h_lt h

lemma Fin.positive_size' [Inhabited (Fin n)] : 0 < n := Fin.positive_size (Inhabited.default)

lemma zero_lt_of_lt {a : Nat} : ∀ {x : Nat}, x < a -> 0 < a
| 0, h   => h
| x+1, h => Nat.lt_trans (Nat.zero_lt_succ x) h

lemma Fin.val_eq_of_lt {n a : Nat} (h : a < n) : (Fin.ofNat' a (zero_lt_of_lt h)).val = a := by
  simp only [Fin.ofNat', Nat.mod_eq_of_lt h]

lemma Fin.modn_def : ∀ (a : Fin n) (m : Nat), a % m = Fin.mk ((a.val % m) % n) (Nat.mod_lt (a.val % m) (a.positive_size))
| ⟨a, pa⟩, m => rfl

lemma Fin.mod_def : ∀ (a m : Fin n), a % m = Fin.mk ((a.val % m.val) % n) (Nat.mod_lt (a.val % m.val) (a.positive_size))
| ⟨a, pa⟩, ⟨m, pm⟩ => rfl

lemma Fin.add_def : ∀ (a b : Fin n), a + b = (Fin.mk ((a.val + b.val) % n) (Nat.mod_lt _ (a.positive_size)))
| ⟨a, pa⟩, ⟨b, pb⟩ => rfl

lemma Fin.mul_def : ∀ (a b : Fin n), a * b = (Fin.mk ((a.val * b.val) % n) (Nat.mod_lt _ (a.positive_size)))
| ⟨a, pa⟩, ⟨b, pb⟩ => rfl

lemma Fin.sub_def : ∀ (a b : Fin n), a - b = (Fin.mk ((a + (n - b)) % n) (Nat.mod_lt _ (a.positive_size)))
| ⟨a, pa⟩, ⟨b, pb⟩ => rfl

@[simp] lemma Fin.mod_eq (a : Fin n) : a % n = a := by
  apply Fin.eq_of_val_eq
  simp only [Fin.modn_def, Nat.mod_mod]
  exact Nat.mod_eq_of_lt a.isLt

@[simp] lemma Fin.mod_eq_val (a : Fin n) : a.val % n = a.val := by
  simp only [Fin.modn_def, Nat.mod_mod]
  exact Nat.mod_eq_of_lt a.isLt

theorem Fin.mod_eq_of_lt {a b : Fin n} (h : a < b) : a % b = a := by
  apply Fin.eq_of_val_eq
  simp only [Fin.mod_def]
  rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt a.isLt]

/- The basic structures on `Fin` are predicated on `Fin n` being inhabited.
The Inhabited bound is there so that we can implement `Zero` in a way that satisfies
the requirements of the relevant typeclasses (for example, AddMonoid). If we were to
use `Fin n+1` for the `Zero` implementation, we would be shutting out some irreducible
definitions (notably USize.size) that are known to be inhabited, but not defined in terms
of `Nat.succ`. Since there's a blanket implementation of `∀ n, Inhabited (Fin n+1)` in
the prelude, this hopefully won't be a significant impediment. -/
section Fin

variable {n : Nat} [Inhabited (Fin n)]

instance : AddSemigroup (Fin n) where
  add_assoc := fun _ _ _ => by
    apply Fin.eq_of_val_eq
    simp only [Fin.add_def, Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc]

instance : AddCommSemigroup (Fin n) where
  add_comm := fun _ _ => by
    apply Fin.eq_of_val_eq
    simp only [Fin.add_def, Nat.add_comm]

instance : Semigroup (Fin n) where
  mul_assoc := fun a b c => by
    apply Fin.eq_of_val_eq
    simp only [Fin.mul_def]
    generalize lhs : ((a.val * b.val) % n * c.val) % n = l
    generalize rhs : a.val * (b.val * c.val % n) % n = r
    rw [<- Nat.mod_eq_of_lt c.isLt, (Nat.mul_mod (a.val * b.val) c.val n).symm] at lhs
    rw [<- Nat.mod_eq_of_lt a.isLt, (Nat.mul_mod a.val (b.val * c.val) n).symm, <- Nat.mul_assoc] at rhs
    rw [<- lhs, <- rhs]

instance : CommSemigroup (Fin n) where
  mul_comm := fun _ _ => by apply Fin.eq_of_val_eq; simp only [Fin.mul_def, Nat.mul_comm]

instance : Zero (Fin n) where
  zero := Fin.ofNat' 0 Fin.positive_size'

@[simp] lemma Fin.val_zero : (0 : Fin n).val = (0 : Nat) :=
  show (Fin.ofNat' 0 Fin.positive_size').val = (0 : Nat) by simp only [Fin.ofNat', Nat.zero_mod]

theorem Fin.mod_lt : ∀ (i : Fin n) {m : Fin n}, (0 : Fin n) < m → (i % m) < m
| ⟨a, aLt⟩, ⟨m, mLt⟩, hp =>  by
    have zero_lt : (0 : Nat) < m := Fin.val_zero ▸ hp
    have a_mod_lt : a % m < m := Nat.mod_lt _ zero_lt
    simp only [Fin.mod_def, LT.lt]
    rw [(Nat.mod_eq_of_lt (Nat.lt_trans a_mod_lt mLt) : a % m % n = a % m)]
    exact Nat.mod_lt _ zero_lt

/- Aux lemma that makes nsmul_succ' easier -/
protected lemma Fin.nsmuls_eq (x : Nat) : ∀ (a : Fin n), ((Fin.ofNat' x Fin.positive_size') * a) = Fin.ofNat' (x * a.val) Fin.positive_size'
| ⟨a, isLt⟩ => by
  apply Fin.eq_of_val_eq
  simp only [Fin.ofNat', Fin.mul_def]
  generalize hy : x * a % n = y
  rw [<- Nat.mod_eq_of_lt isLt, <- Nat.mul_mod, hy]

instance : AddMonoid (Fin n) :=
  let add_zero_ : ∀ (a : Fin n), a + 0 = a := fun a => by
    apply Fin.eq_of_val_eq
    simp only [Fin.add_def, Fin.val_zero, Nat.add_zero]
    exact Nat.mod_eq_of_lt a.isLt
  {
    add_zero := add_zero_
    zero_add := fun _ => by rw [add_comm]; exact add_zero_ _
    nsmul := fun x a => (Fin.ofNat' x a.positive_size) * a
    nsmul_zero' := fun _ => by
      apply Fin.eq_of_val_eq
      simp [Fin.mul_def, Fin.ofNat', Fin.val_zero, Nat.zero_mul, Nat.zero_mod]
    nsmul_succ' := fun x a => by
      simp only [Fin.nsmuls_eq]
      simp [Fin.ofNat', Fin.add_def]
      exact congrArg (fun x => x % n) (Nat.add_comm (x * a.val) (a.val) ▸ Nat.succ_mul x a.val)
  }

instance : AddCommMonoid (Fin n) where
  add_comm := add_comm

instance : One (Fin n) where
  one := ⟨1 % n, (Nat.mod_lt 1 Fin.positive_size')⟩

@[simp] lemma Fin.val_one: (1 : Fin n).val = (1 % n : Nat) :=
  show (Fin.ofNat' 1 Fin.positive_size').val = 1 % n by simp [Fin.ofNat']

instance : Neg (Fin n) where
  neg a := ⟨(n - a) % n, Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le _) a.isLt)⟩

instance : SubNegMonoid (Fin n) where
  sub_eq_add_neg := fun _ _ => by simp [Fin.add_def, Fin.sub_def, Neg.neg]
  gsmul := fun x a =>
    match x with
    | Int.ofNat x' => AddMonoid.nsmul x' a
    | Int.negSucc x' => -(AddMonoid.nsmul x'.succ a)
  gsmul_zero' := fun _ => by
    apply Fin.eq_of_val_eq
    simp only [AddMonoid.nsmul, Fin.ofNat', Fin.mul_def, Nat.zero_mod, Nat.zero_mul, Fin.val_zero]
  gsmul_succ' := by simp [AddMonoid.nsmul_succ']
  gsmul_neg' := by simp [AddMonoid.nsmul]

instance : AddGroup (Fin n) where
  add_left_neg :=
    fun
    | ⟨a, isLt⟩ => by
      apply Fin.eq_of_val_eq
      simp only [Neg.neg, Fin.add_def, Fin.val_zero]
      cases a with
      | zero => rw [Nat.sub_zero, Nat.add_zero, Nat.mod_mod, Nat.mod_self]
      | succ a =>
        have h1 : (n - a.succ) % n = (n - a.succ) :=
          Nat.mod_eq_of_lt (Nat.sub_lt (Fin.positive_size') (Nat.succ_pos _))
        have h_aux : (n - a.succ + a.succ) = n := by
          rw [Nat.add_comm]
          exact Nat.add_sub_of_le (Nat.le_of_lt isLt)
        rw [h1, h_aux, Nat.mod_self]

instance : Monoid (Fin n) :=
  let mul_one_ : ∀ (a : Fin n), a * 1 = a := fun a => by
    apply Fin.eq_of_val_eq
    simp only [Fin.mul_def, Fin.val_one]
    cases n with
    | zero => exact (False.elim a.elim0)
    | succ n =>
      match Nat.lt_or_eq_of_le (Nat.mod_le 1 n.succ) with
      | Or.inl h_lt =>
        have h_eq : 1 % n.succ = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ h_lt)
        have hnz : n = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ (Nat.le_of_mod_lt h_lt))
        have haz : a.val = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ (hnz ▸ a.isLt))
        rw [h_eq, haz]
        simp only [Nat.zero_mul, Nat.zero_mod]
      | Or.inr h_eq => simp only [h_eq, Nat.mul_one, Nat.mod_eq_of_lt (a.isLt)]
  {
    mul_one := mul_one_
    one_mul := fun _ => by rw [mul_comm]; exact mul_one_ _
    npow_zero' := fun _ => rfl
    npow_succ' := fun _ _ => rfl
  }

def Fin.addOverflows? (a b : Fin n) : Bool := n <= a.val + b.val

def Fin.mulOverflows? (a b : Fin n) : Bool := n <= a.val * b.val

def Fin.subUnderflows? (a b : Fin n) : Bool := a.val < b.val

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

instance : CommMonoid (Fin n) where
  mul_comm := CommSemigroup.mul_comm

instance : MonoidWithZero (Fin n) :=
  let zero_mul_ : ∀ (x : Fin n), 0 * x = 0 := fun _ => by
    apply Fin.eq_of_val_eq
    simp only [Fin.mul_def, Fin.val_zero, Nat.zero_mul, Nat.zero_mod]
  {
    zero_mul := zero_mul_
    mul_zero := fun _ => by rw [mul_comm]; exact zero_mul_ _
  }

end Fin
