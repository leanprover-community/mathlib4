import Mathlib.Data.Nat.Basic -- *only* for notation ℕ which should be in a "prelude"
import Mathlib.Data.Int.Basic -- *only* for notation ℤ which should be in a "prelude"
import Mathlib.Tactic.Spread

/-!

# Typeclasses for monoids and groups etc

-/

/-

## Stuff which was in core Lean 3

-- this should also be in a "prelude" -- it is not in mathlib3's algebra.group.defs
-/

class Zero (α : Type u) where
  zero : α

instance [Zero α] : OfNat α (nat_lit 0) where
  ofNat := Zero.zero

class One (α : Type u) where
  one : α

instance [One α] : OfNat α (nat_lit 1) where
  ofNat := One.one

class Inv (α : Type u) where
  inv : α → α

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
| 0  , a => 0
| n+1, a => a + nsmul_rec n a

-- use `x * npow_rec n x` and not `npow_rec n x * x` in the definition to make sure that
-- definitional unfolding of `npow_rec` is blocked, to avoid deep recursion issues.
/-- The fundamental power operation in a monoid. `npow_rec n a = a*a*...*a` n times.
Use instead `a ^ n`,  which has better definitional behavior. -/
def npow_rec [One M] [Mul M] : ℕ → M → M
| 0  , a => 1
| n+1, a => a * npow_rec n a

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

### Cancellative semigroups

-/

class IsAddLeftCancel (A : Type u) [Add A] where
  add_left_cancel (a b c : A) : a + b = a + c → b = c

class IsAddRightCancel (A : Type u) [Add A] where
  add_right_cancel (a b c : A) : b + a = c + a → b = c

section AddLeftCancel_lemmas

variable {A : Type u} [AddSemigroup A] [IsAddLeftCancel A] {a b c : A}

theorem add_left_cancel : a + b = a + c → b = c :=
IsAddLeftCancel.add_left_cancel a b c

theorem add_left_cancel_iff : a + b = a + c ↔ b = c :=
⟨add_left_cancel, congrArg _⟩

-- no `function.injective`?
--theorem add_right_injective (a : G) : function.injective (c * .) :=
--λ a b => add_left_cancel

@[simp] theorem add_right_inj (a : A) {b c : A} : a + b = a + c ↔ b = c :=
⟨add_left_cancel, congrArg _⟩

--theorem add_ne_add_right (a : A) {b c : A} : a + b ≠ a + c ↔ b ≠ c :=
--(add_right_injective a).ne_iff

end AddLeftCancel_lemmas

section AddRightCancel_lemmas

variable {A : Type u} [AddSemigroup A] [IsAddRightCancel A] {a b c : A}

theorem add_right_cancel : b + a = c + a → b = c :=
IsAddRightCancel.add_right_cancel a b c

theorem add_right_cancel_iff : b + a = c + a ↔ b = c :=
⟨add_right_cancel, λ h => h ▸ rfl⟩

@[simp] theorem add_left_inj (a : A) {b c : A} : b + a = c + a ↔ b = c :=
⟨add_right_cancel, λ h => h ▸ rfl⟩

end AddRightCancel_lemmas

/-

### Additive monoids

-/

class AddMonoid (A : Type u) extends AddSemigroup A, Zero A where
  add_zero (a : A) : a + 0 = a
  zero_add (a : A) : 0 + a = a
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

/-

### Commutative additive monoids

-/

class AddCommMonoid (A : Type u) extends AddMonoid A where
  add_comm (a b : A) : a + b = b + a

instance (A : Type u) [AddCommMonoid A] : AddCommSemigroup A where
  __ := ‹AddCommMonoid A›

/-

### Additive groups

-/

class AddGroup (A : Type u) extends AddMonoid A, Neg A, Sub A where
  add_left_neg (a : A) : -a + a = 0
  sub_eq_add_neg (a b : A) : a - b = a + -b
  gsmul : ℤ → A → A := gsmul_rec
  gpow_zero' (a : A) : gsmul 0 a = 0 -- try rfl
  gpow_succ' (n : ℕ) (a : A) : gsmul (Int.ofNat n.succ) a = a + gsmul (Int.ofNat n) a
  gpow_neg' (n : ℕ) (a : A) : gsmul (Int.negSucc n) a = -(gsmul ↑(n.succ) a)

section AddGroup_lemmas

variable {A : Type u} [AddGroup A] {a b c : A}

@[simp] theorem add_left_neg : ∀ a : A, -a + a = 0 :=
AddGroup.add_left_neg

theorem neg_add_self (a : A) : -a + a = 0 := add_left_neg a

@[simp] theorem neg_add_cancel_left (a b : A) : -a + (a + b) = b :=
by rw [← add_assoc, add_left_neg, zero_add]

@[simp] theorem neg_eq_of_add_eq_zero (h : a + b = 0) : -a = b :=
left_neg_eq_right_neg (neg_add_self a) h

@[simp] theorem neg_neg (a : A) : -(-a) = a :=
neg_eq_of_add_eq_zero (add_left_neg a)

@[simp] theorem add_right_neg (a : A) : a + -a = 0 := by
  rw [←add_left_neg (-a), neg_neg]

-- synonym
theorem add_neg_self (a : A) : a + -a = 0 := add_right_neg a

@[simp] theorem add_neg_cancel_right (a b : A) : a + b + -b = a :=
by rw [add_assoc, add_right_neg, add_zero]

instance (A : Type u) [AddGroup A] : IsAddRightCancel A where
  add_right_cancel a b c h := by
  rw [← add_neg_cancel_right b a, h, add_neg_cancel_right]

instance (A : Type u) [AddGroup A] : IsAddLeftCancel A where
  add_left_cancel a b c h := by
  rw [← neg_add_cancel_left a b, h, neg_add_cancel_left]

end AddGroup_lemmas

class AddCommGroup (A : Type u) extends AddGroup A where
  add_comm (a b : A) : a + b = b + a

instance (A : Type u) [AddCommGroup A] : AddCommMonoid A where
  __ := ‹AddCommGroup A›

/-

## Multiplicative semigroups, monoids and groups

-/

/-

## Semigroups

-/

class Semigroup (G : Type u) extends Mul G where
  mul_assoc (a b c : G) : (a * b) * c = a * (b * c)

theorem mul_assoc {G : Type u} [Semigroup G] :
  ∀ a b c : G, a * b * c = a * (b * c) :=
Semigroup.mul_assoc

class CommSemigroup (G : Type u) extends Semigroup G where
  mul_comm (a b : G) : a * b = b * a

theorem mul_comm {M : Type u} [CommSemigroup M] : ∀ a b : M, a * b = b * a :=
CommSemigroup.mul_comm

/-

### Cancellative semigroups

-/

class IsMulLeftCancel (G : Type u) [Mul G] where
  mul_left_cancel (a b c : G) : a * b = a * c → b = c

class IsMulRightCancel (G : Type u) [Mul G] where
  mul_right_cancel (a b c : G) : b * a = c * a → b = c
section MulLeftCancel

variable {G : Type u} [Semigroup G] [IsMulLeftCancel G] {a b c : G}

theorem mul_left_cancel : a * b = a * c → b = c :=
IsMulLeftCancel.mul_left_cancel a b c

theorem mul_left_cancel_iff : a * b = a * c ↔ b = c :=
⟨mul_left_cancel, congrArg _⟩

-- no `function.injective`?
--theorem mul_right_injective (a : G) : function.injective (c * .) :=
--λ a b => mul_left_cancel

@[simp] theorem mul_right_inj (a : G) {b c : G} : a * b = a * c ↔ b = c :=
⟨mul_left_cancel, congrArg _⟩

--theorem mul_ne_mul_right (a : G) {b c : G} : a * b ≠ a * c ↔ b ≠ c :=
--(mul_right_injective a).ne_iff

end MulLeftCancel

section MulRightCancel

variable {G : Type u} [Semigroup G] [IsMulRightCancel G] {a b c : G}

theorem mul_right_cancel : b * a = c * a → b = c :=
IsMulRightCancel.mul_right_cancel a b c

theorem mul_right_cancel_iff : b * a = c * a ↔ b = c :=
⟨mul_right_cancel, λ h => h ▸ rfl⟩

@[simp] theorem mul_left_inj (a : G) {b c : G} : b * a = c * a ↔ b = c :=
⟨mul_right_cancel, λ h => h ▸ rfl⟩

end MulRightCancel

/-

### Monoids

-/

class Monoid (M : Type u) extends Semigroup M, One M where
  mul_one (m : M) : m * 1 = m
  one_mul (m : M) : 1 * m = m
  npow : ℕ → M → M := npow_rec
  npow_zero' : ∀ x, npow 0 x = 1 -- fill in with tactic once we can do this
  npow_succ' : ∀ (n : ℕ) x, npow n.succ x = x * npow n x -- fill in with tactic

@[simp] theorem mul_one {M : Type u} [Monoid M] : ∀ (m : M), m * 1 = m :=
Monoid.mul_one

@[simp] theorem one_mul {M : Type u} [Monoid M] : ∀ (m : M), 1 * m = m :=
Monoid.one_mul

theorem left_inv_eq_right_inv {M : Type u} [Monoid M] {a b c : M}
  (hba : b * a = 1) (hac : a * c = 1) : b = c :=
by rw [←one_mul c, ←hba, mul_assoc, hac, mul_one b]

/-

### Commutative monoids

-/

class CommMonoid (M : Type u) extends Monoid M where
  mul_comm (a b : M) : a * b = b * a

instance (M : Type u) [CommMonoid M] : CommSemigroup M where
  __ := ‹CommMonoid M›

/-

### Groups

-/

class Group (G : Type u) extends Monoid G, Inv G, Div G where
  mul_left_inv (a : G) : a⁻¹ * a = 1
  div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
  gpow : ℤ → G → G := gpow_rec
  gpow_zero' (a : G) : gpow 0 a = 1 -- try rfl
  gpow_succ' (n : ℕ) (a : G) : gpow (Int.ofNat n.succ) a = a * gpow (Int.ofNat n) a
  gpow_neg' (n : ℕ) (a : G) : gpow (Int.negSucc n) a = (gpow ↑(n.succ) a)⁻¹

section Group_lemmas

variable {G : Type u} [Group G] {a b c : G}

@[simp] theorem mul_left_inv : ∀ a : G, a⁻¹ * a = 1 :=
Group.mul_left_inv

theorem inv_mul_self (a : G) : a⁻¹ * a = 1 := mul_left_inv a

@[simp] theorem inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b :=
by rw [← mul_assoc, mul_left_inv, one_mul]

@[simp] theorem inv_eq_of_mul_eq_one (h : a * b = 1) : a⁻¹ = b :=
left_inv_eq_right_inv (inv_mul_self a) h

@[simp] theorem inv_inv (a : G) : (a⁻¹)⁻¹ = a :=
inv_eq_of_mul_eq_one (mul_left_inv a)

@[simp] theorem mul_right_inv (a : G) : a * a⁻¹ = 1 := by
  rw [←mul_left_inv (a⁻¹), inv_inv]

-- synonym
theorem mul_inv_self (a : G) : a * a⁻¹ = 1 := mul_right_inv a

@[simp] theorem mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a :=
by rw [mul_assoc, mul_right_inv, mul_one]

end Group_lemmas

class CommGroup (G : Type u) extends Group G where
  mul_comm (a b : G) : a * b = b * a

instance (G : Type u) [CommGroup G] : CommMonoid G where
  __ := ‹CommGroup G›
