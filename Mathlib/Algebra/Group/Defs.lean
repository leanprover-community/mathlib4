import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Init.Data.Int.Notation
import Mathlib.Init.Zero
import Mathlib.Tactic.Spread
import Mathlib.Tactic.ToAdditive

-- [todo] is this correct? I think it's needed to ensure that additiveTest
-- succeeds if the relevant arg involves Nat.
attribute [to_additive] Nat
attribute [to_additive] Int

attribute [to_additive Add] Mul
attribute [to_additive Sub] Div
attribute [to_additive HAdd] HMul
attribute [to_additive instHAdd] instHMul
attribute [to_additive HSub] HDiv
attribute [to_additive instHSub] instHDiv

attribute [to_additive_reorder 1] HPow
attribute [to_additive_reorder 1 4] HPow.hPow
attribute [to_additive HMul] HPow

/-!
# Typeclasses for monoids and groups etc
-/

@[to_additive Zero]
class One.{u} (α : Type u) where
  one : α

@[to_additive Zero.toOfNat0]
instance One.toOfNat1 {α} [One α] : OfNat α (nat_lit 1) where
  ofNat := ‹One α›.1

@[to_additive Zero.ofOfNat0]
instance One.ofOfNat1 {α} [OfNat α (nat_lit 1)] : One α where
  one := 1

/-- Class of types that have an inversion operation. -/
@[to_additive Neg]
class Inv (α : Type u) where
  /-- Invert an element of α. -/
  inv : α → α

@[inheritDoc]
postfix:max "⁻¹" => Inv.inv

/-

## The trick for adding a natural action onto monoids

-/

section nat_action

variable {M : Type u}

-- see npow_rec comment for explanation about why not nsmul_rec n a + a
/-- The fundamental scalar multiplication in an additive monoid. `nsmul_rec n a = a+a+...+a` n
times. Use instead `n • a`, which has better definitional behavior. -/
def nsmul_rec [Zero M] [Add M] : ℕ → M → M
| 0  , _ => 0
| n+1, a => a + nsmul_rec n a

-- use `x * npow_rec n x` and not `npow_rec n x * x` in the definition to make sure that
-- definitional unfolding of `npow_rec` is blocked, to avoid deep recursion issues.
/-- The fundamental power operation in a monoid. `npow_rec n a = a*a*...*a` n times.
Use instead `a ^ n`,  which has better definitional behavior. -/
def npow_rec [One M] [Mul M] : ℕ → M → M
| 0  , _ => 1
| n+1, a => a * npow_rec n a

attribute [to_additive_reorder 3] npow_rec
attribute [to_additive] npow_rec

end nat_action

section int_action

/-- The fundamental scalar multiplication in an additive group. `gsmul_rec n a = a+a+...+a` n
times, for integer `n`. Use instead `n • a`, which has better definitional behavior. -/
def gsmul_rec {G : Type u} [Zero G] [Add G] [Neg G]: ℤ → G → G
| (Int.ofNat n)  , a => nsmul_rec n a
| (Int.negSucc n), a => - (nsmul_rec n.succ a)

/-- The fundamental power operation in a group. `gpow_rec n a = a*a*...*a` n times, for integer `n`.
Use instead `a ^ n`,  which has better definitional behavior. -/
def gpow_rec {G : Type u} [One G] [Mul G] [Inv G] : ℤ → G → G
| (Int.ofNat n)  , a => npow_rec n a
| (Int.negSucc n), a => (npow_rec n.succ a) ⁻¹

attribute [to_additive_reorder 4] gpow_rec
attribute [to_additive gsmul_rec] gpow_rec

end int_action

/-

## Additive semigroups, monoids and groups

-/

/-

### Semigroups

-/
class AddSemigroup (A : Type u) extends Add A where
  add_assoc (a b c : A) : (a + b) + c = a + (b + c)

theorem add_assoc {G : Type u} [AddSemigroup G] :
  ∀ a b c : G, (a + b) + c = a + (b + c) :=
  AddSemigroup.add_assoc

class AddCommSemigroup (A : Type u) extends AddSemigroup A where
  add_comm (a b : A) : a + b = b + a

theorem add_comm {A : Type u} [AddCommSemigroup A] (a b : A) : a + b = b + a :=
AddCommSemigroup.add_comm a b

/-

### Additive monoids

-/

/-- Typeclass for expressing that a type `M` with + and 0 satisfies
`0 + a = a` and `a + 0 = a` for all `a : M`. -/
class AddZeroClass (A : Type u) extends Zero A, Add A where
  add_zero (a : A) : a + 0 = a
  zero_add (a : A) : 0 + a = a

class AddMonoid (A : Type u) extends AddSemigroup A, AddZeroClass A where
  nsmul : ℕ → A → A := nsmul_rec
  nsmul_zero' : ∀ x, nsmul 0 x = 0 -- fill in with tactic once we can do this
  nsmul_succ' : ∀ (n : ℕ) x, nsmul n.succ x = x + nsmul n x -- fill in with tactic

section AddMonoid_lemmas

variable  {A : Type u} [AddMonoid A] {a b c : A}

@[simp] theorem add_zero (a : A) : a + 0 = a :=
AddMonoid.add_zero a

@[simp] theorem zero_add (a : A) : 0 + a = a :=
AddMonoid.zero_add a

theorem left_neg_eq_right_neg (hba : b + a = 0) (hac : a + c = 0) : b = c :=
by rw [←zero_add c, ←hba, add_assoc, hac, add_zero b]

end AddMonoid_lemmas

/-! ### Additive monoids with one -/

class AddMonoidWithOne (R : Type u) extends AddMonoid R, One R where
  natCast : ℕ → R
  natCast_zero : natCast 0 = 0
  natCast_succ : ∀ n, natCast (n + 1) = natCast n + 1

@[coe]
def Nat.cast [AddMonoidWithOne R] : ℕ → R := AddMonoidWithOne.natCast

instance [AddMonoidWithOne R] : CoeTail ℕ R where coe := Nat.cast
instance [AddMonoidWithOne R] : CoeHTCT ℕ R where coe := Nat.cast

@[simp, norm_cast] theorem Nat.cast_zero [AddMonoidWithOne R] : ((0 : ℕ) : R) = 0 :=
  AddMonoidWithOne.natCast_zero
@[simp 500, norm_cast 500]
theorem Nat.cast_succ [AddMonoidWithOne R] : ((Nat.succ n : ℕ) : R) = (n : R) + 1 :=
  AddMonoidWithOne.natCast_succ _
@[simp, norm_cast]
theorem Nat.cast_one [AddMonoidWithOne R] : ((1 : ℕ) : R) = 1 := by simp

@[simp, norm_cast] theorem Nat.cast_add [AddMonoidWithOne R] : ((m + n : ℕ) : R) = (m : R) + n := by
  induction n <;> simp_all [add_succ, add_assoc]

class Nat.AtLeastTwo (n : Nat) : Prop where
  prop : n ≥ 2
instance : Nat.AtLeastTwo (n + 2) where
  prop := Nat.succ_le_succ $ Nat.succ_le_succ $ Nat.zero_le _

@[nolint unusedArguments]
instance [AddMonoidWithOne R] [Nat.AtLeastTwo n] : OfNat R n where
  ofNat := n.cast

@[simp, norm_cast] theorem Nat.cast_ofNat [AddMonoidWithOne R] [Nat.AtLeastTwo n] :
  (Nat.cast (OfNat.ofNat n) : R) = OfNat.ofNat n := rfl

/-

### Commutative additive monoids

-/

class AddCommMonoid (A : Type u) extends AddMonoid A, AddCommSemigroup A where
  -- TODO: doesn't work
  zero_add a := (by rw [add_comm, add_zero])
  add_zero a := (by rw [add_comm, zero_add])

/-

### sub_neg_monoids

Additive groups can "pick up" several equal but not defeq actions of ℤ.
This trick isolates one such action, `gsmul`, and decrees it to
be "the canonical one".

-/

class SubNegMonoid (A : Type u) extends AddMonoid A, Neg A, Sub A where
  sub := λ a b => a + -b
  sub_eq_add_neg : ∀ a b : A, a - b = a + -b
  gsmul : ℤ → A → A := gsmul_rec
  gsmul_zero' : ∀ (a : A), gsmul 0 a = 0
  gsmul_succ' (n : ℕ) (a : A) : gsmul (Int.ofNat n.succ) a = a + gsmul (Int.ofNat n) a
  gsmul_neg' (n : ℕ) (a : A) : gsmul (Int.negSucc n) a = -(gsmul ↑(n.succ) a)

export SubNegMonoid (sub_eq_add_neg)

/-

### Additive groups

-/

class AddGroup (A : Type u) extends SubNegMonoid A where
  add_left_neg (a : A) : -a + a = 0

section AddGroup_lemmas

variable {A : Type u} [AddGroup A] {a b c : A}

@[simp] theorem add_left_neg : ∀ a : A, -a + a = 0 :=
AddGroup.add_left_neg

theorem neg_add_self (a : A) : -a + a = 0 := add_left_neg a

@[simp] theorem neg_add_cancel_left (a b : A) : -a + (a + b) = b :=
by rw [← add_assoc, add_left_neg, zero_add]

theorem neg_eq_of_add_eq_zero (h : a + b = 0) : -a = b :=
left_neg_eq_right_neg (neg_add_self a) h

@[simp] theorem neg_neg (a : A) : -(-a) = a :=
neg_eq_of_add_eq_zero (add_left_neg a)

@[simp] theorem add_right_neg (a : A) : a + -a = 0 := by
  rw [←add_left_neg (-a), neg_neg]

-- synonym
theorem add_neg_self (a : A) : a + -a = 0 := add_right_neg a

@[simp] theorem add_neg_cancel_right (a b : A) : a + b + -b = a :=
by rw [add_assoc, add_right_neg, add_zero]

end AddGroup_lemmas

class AddCommGroup (A : Type u) extends AddGroup A, AddCommMonoid A


/-! ### Additive groups with one -/

class AddGroupWithOne (R : Type u) extends AddMonoidWithOne R, AddGroup R where
  intCast : ℤ → R
  intCast_ofNat : ∀ n : ℕ, intCast n = natCast n
  intCast_negSucc : ∀ n : ℕ, intCast (Int.negSucc n) = - natCast (n + 1)

@[coe]
def Int.cast [AddGroupWithOne R] : ℤ → R := AddGroupWithOne.intCast

instance [AddGroupWithOne R] : CoeTail ℤ R where coe := Int.cast

theorem Int.cast_ofNat [AddGroupWithOne R] : (Int.cast (Int.ofNat n) : R) = Nat.cast n :=
  AddGroupWithOne.intCast_ofNat _
@[simp, norm_cast]
theorem Int.cast_negSucc [AddGroupWithOne R] :
    (Int.cast (Int.negSucc n) : R) = (-(Nat.cast (n + 1)) : R) :=
  AddGroupWithOne.intCast_negSucc _

@[simp, norm_cast] theorem Int.cast_zero [AddGroupWithOne R] : ((0 : ℤ) : R) = 0 := by
  erw [Int.cast_ofNat, Nat.cast_zero]
@[simp, norm_cast] theorem Int.cast_one [AddGroupWithOne R] : ((1 : ℤ) : R) = 1 := by
  erw [Int.cast_ofNat, Nat.cast_one]

/-

## Multiplicative semigroups, monoids and groups

-/

/-

## Semigroups

-/

@[to_additive AddSemigroup]
class Semigroup (G : Type u) extends Mul G where
  mul_assoc (a b c : G) : (a * b) * c = a * (b * c)

export Semigroup (mul_assoc)

@[to_additive AddCommSemigroup]
class CommSemigroup (G : Type u) extends Semigroup G where
  mul_comm (a b : G) : a * b = b * a

export CommSemigroup (mul_comm)

@[to_additive]
lemma mul_left_comm {M} [CommSemigroup M] (a b c : M) : a * (b * c) = b * (a * c) :=
by rw [← mul_assoc, mul_comm a, mul_assoc]

-- Funky Lean 3 proof of the above:
--left_comm has_mul.mul mul_comm mul_assoc

@[to_additive]
lemma mul_right_comm {M} [CommSemigroup M] (a b c : M) : a * b * c = a * c * b :=
by rw [mul_assoc, mul_comm b c, mul_assoc]


/-- Typeclass for expressing that a type `M` with multiplication and a one satisfies
`1 * a = a` and `a * 1 = a` for all `a : M`. -/
@[to_additive AddZeroClass]
class MulOneClass (M : Type u) extends One M, Mul M where
  mul_one : ∀ (a : M), a * 1 = a
  one_mul : ∀ (a : M), 1 * a = a

/-

### Monoids

-/

@[to_additive AddMonoid]
class Monoid (M : Type u) extends Semigroup M, MulOneClass M where
  npow : ℕ → M → M := npow_rec
  npow_zero' : ∀ x, npow 0 x = 1 -- fill in with tactic once we can do this
  npow_succ' : ∀ (n : ℕ) x, npow n.succ x = x * npow n x -- fill in with tactic

-- [todo] this shouldn't be needed
attribute [to_additive AddMonoid.toAddZeroClass] Monoid.toMulOneClass

section Monoid
variable {M : Type u} [Monoid M]

@[defaultInstance high] instance Monoid.HPow : HPow M ℕ M := ⟨λ a n => Monoid.npow n a⟩

@[simp, to_additive]
theorem mul_one : ∀ (a : M), a * 1 = a :=
  Monoid.mul_one

@[simp, to_additive]
theorem one_mul : ∀ (a : M), 1 * a = a :=
  Monoid.one_mul

theorem npow_eq_pow (n : ℕ) (a : M) : Monoid.npow n a = a^n := rfl

@[simp] theorem pow_zero : ∀ (a : M), a ^ (0:ℕ) = 1 :=
Monoid.npow_zero'

theorem pow_succ' : ∀ (n : ℕ) (a : M), a ^ n.succ = a * a ^ n :=
Monoid.npow_succ'

theorem pow_mul_comm (a : M) (n : ℕ) : a^n * a = a * a^n := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, pow_succ', mul_assoc]

theorem pow_succ (n : ℕ) (a : M) : a ^ n.succ = a ^ n * a :=
by rw [pow_succ', pow_mul_comm]

@[simp] theorem pow_one (a : M) : a ^ (1:ℕ) = a :=
by rw [Nat.one_eq_succ_zero, pow_succ, pow_zero, one_mul]

theorem pow_add (a : M) (m n : ℕ) : a^(m + n) = a^m * a^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.add_succ, pow_succ',ih, pow_succ', ← mul_assoc, ← mul_assoc, pow_mul_comm]

theorem pow_mul {M} [Monoid M] (a : M) (m n : ℕ) : a^(m * n) = (a^m)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, pow_add, ih, pow_succ', pow_mul_comm]

theorem left_inv_eq_right_inv {M : Type u} [Monoid M] {a b c : M}
  (hba : b * a = 1) (hac : a * c = 1) : b = c :=
by rw [←one_mul c, ←hba, mul_assoc, hac, mul_one b]

end Monoid

/-

### Commutative monoids

-/

@[to_additive AddCommMonoid]
class CommMonoid (M : Type u) extends Monoid M where
  mul_comm (a b : M) : a * b = b * a

section CommMonoid
variable {M} [CommMonoid M]

instance : CommSemigroup M where
  __ := ‹CommMonoid M›

theorem mul_pow (a b : M) (n : ℕ)  : (a * b)^n= a^n * b^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ, ih, mul_assoc, mul_left_comm _ a]

end CommMonoid

/-

### Div inv monoids
-/

@[to_additive SubNegMonoid]
class DivInvMonoid (G : Type u) extends Monoid G, Inv G, Div G :=
(div := λ a b => a * b⁻¹)
(div_eq_mul_inv : ∀ a b : G, a / b = a * b⁻¹)
(gpow : ℤ → G → G := gpow_rec)
(gpow_zero' : ∀ (a : G), gpow 0 a = 1)
(gpow_succ' :
  ∀ (n : ℕ) (a : G), gpow (Int.ofNat n.succ) a = a * gpow (Int.ofNat n) a)
(gpow_neg' :
  ∀ (n : ℕ) (a : G), gpow (Int.negSucc n) a = (gpow (Int.ofNat n.succ) a) ⁻¹)

export DivInvMonoid (div_eq_mul_inv)

alias div_eq_mul_inv ← division_def

/-

### Groups

-/

@[to_additive AddGroup]
class Group (G : Type u) extends DivInvMonoid G where
  mul_left_inv (a : G) : a⁻¹ * a = 1

section Group_lemmas

variable {G : Type u} [Group G] {a b c : G}

@[simp, to_additive]
theorem mul_left_inv : ∀ a : G, a⁻¹ * a = 1 :=
Group.mul_left_inv

@[to_additive]
theorem inv_mul_self (a : G) : a⁻¹ * a = 1 := mul_left_inv a

@[simp, to_additive] theorem inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b :=
by rw [← mul_assoc, mul_left_inv, one_mul]

@[simp, to_additive] theorem inv_eq_of_mul_eq_one (h : a * b = 1) : a⁻¹ = b :=
left_inv_eq_right_inv (inv_mul_self a) h

@[simp, to_additive] theorem inv_inv (a : G) : (a⁻¹)⁻¹ = a :=
inv_eq_of_mul_eq_one (mul_left_inv a)

@[simp, to_additive] theorem mul_right_inv (a : G) : a * a⁻¹ = 1 := by
  rw [←mul_left_inv (a⁻¹), inv_inv]

@[simp, to_additive]
theorem mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b := by
  rw [← mul_assoc, mul_right_inv, one_mul]

@[simp, to_additive]
theorem mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a := by
  rw [mul_assoc, mul_right_inv, mul_one]

@[simp, to_additive]
theorem inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a := by
  rw [mul_assoc, mul_left_inv, mul_one]

-- synonym
@[to_additive]
theorem mul_inv_self (a : G) : a * a⁻¹ = 1 := mul_right_inv a

end Group_lemmas

class CommGroup (G : Type u) extends Group G where
  mul_comm (a b : G) : a * b = b * a

instance (G : Type u) [CommGroup G] : CommMonoid G where
  __ := ‹CommGroup G›


/-- A `LeftCancelSemigroup` is a semigroup such that `a * b = a * c` implies `b = c`. -/
@[ext]
class LeftCancelSemigroup (G : Type u) extends Semigroup G where
  mul_left_cancel : ∀ a b c : G, a * b = a * c → b = c

/-- An `AddLeftCancelSemigroup` is an additive semigroup such that
`a + b = a + c` implies `b = c`. -/
@[ext]
class AddLeftCancelSemigroup (G : Type u) extends AddSemigroup G where
  add_left_cancel : ∀ a b c : G, a + b = a + c → b = c

attribute [to_additive AddLeftCancelSemigroup] LeftCancelSemigroup

section LeftCancelSemigroup

variable [LeftCancelSemigroup G] {a b c : G}

@[to_additive]
theorem mul_left_cancel : a * b = a * c → b = c :=
  LeftCancelSemigroup.mul_left_cancel a b c

@[to_additive]
theorem mul_left_cancel_iff : a * b = a * c ↔ b = c :=
  ⟨mul_left_cancel, congr_arg _⟩

@[to_additive]
theorem mul_right_injective (a : G) : Function.injective ((· * ·) a) := fun _ _ => mul_left_cancel

@[simp, to_additive]
theorem mul_right_inj (a : G) {b c : G} : a * b = a * c ↔ b = c :=
  (mul_right_injective a).eq_iff

@[to_additive]
theorem mul_ne_mul_right (a : G) {b c : G} : a * b ≠ a * c ↔ b ≠ c :=
  (mul_right_injective a).ne_iff

end LeftCancelSemigroup

/-- A `right_cancel_semigroup` is a semigroup such that `a * b = c * b` implies `a = c`. -/
@[ext]
class RightCancelSemigroup (G : Type u) extends Semigroup G where
  mul_right_cancel : ∀ a b c : G, a * b = c * b → a = c

/-- An `add_right_cancel_semigroup` is an additive semigroup such that
`a + b = c + b` implies `a = c`. -/
@[ext]
class AddRightCancelSemigroup (G : Type u) extends AddSemigroup G where
  add_right_cancel : ∀ a b c : G, a + b = c + b → a = c

attribute [to_additive AddRightCancelSemigroup] RightCancelSemigroup

section RightCancelSemigroup

variable [RightCancelSemigroup G] {a b c : G}

@[to_additive]
theorem mul_right_cancel : a * b = c * b → a = c :=
  RightCancelSemigroup.mul_right_cancel a b c

@[to_additive]
theorem mul_right_cancel_iff : b * a = c * a ↔ b = c :=
  ⟨mul_right_cancel, congr_arg (· * a)⟩

@[to_additive]
theorem mul_left_injective (a : G) : Function.injective (· * a) := fun _ _ => mul_right_cancel

@[simp, to_additive]
theorem mul_left_inj (a : G) {b c : G} : b * a = c * a ↔ b = c :=
  (mul_left_injective a).eq_iff

@[to_additive]
theorem mul_ne_mul_left (a : G) {b c : G} : b * a ≠ c * a ↔ b ≠ c :=
  (mul_left_injective a).ne_iff

end RightCancelSemigroup
