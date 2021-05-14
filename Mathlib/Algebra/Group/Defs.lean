/-!
# Typeclasses for monoids and groups etc

TODO: port all lemmas about semigroups, monoids and groups
to the Add case

-/

/-
## Stuff which was in core Lean 3
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

notation "ℕ" => Nat

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

notation "ℤ" => Int

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

# Additive groups

-/

class AddSemigroup (A : Type u) extends Add A where
  add_assoc (a b c : A) : (a + b) + c = a + (b + c)

class AddMonoid (A : Type u) extends AddSemigroup A, Zero A where
  add_zero (a : A) : a + 0 = a
  zero_add (a : A) : 0 + a = a
  nsmul : ℕ → A → A := nsmul_rec
  nsmul_zero' : ∀ x, nsmul 0 x = 0 -- fill in with tactic once we can do this
  nsmul_succ' : ∀ (n : ℕ) x, nsmul n.succ x = x + nsmul n x -- fill in with tactic

class AddCommMonoid (A : Type u) extends AddMonoid A where
  add_comm (a b : A) : a + b = b + a

class IsAddRightCancel (A : Type u) extends Add A where
  add_right_cancel (a b c : A) : a + b = c + b → a = c

class AddGroup (A : Type u) extends AddMonoid A, Neg A, Sub A where
  add_left_neg (a : A) : -a + a = 0
  sub_eq_add_neg (a b : A) : a - b = a + -b 
  gsmul : ℤ → A → A := gsmul_rec
  gpow_zero' (a : A) : gsmul 0 a = 0 -- try rfl
  gpow_succ' (n : ℕ) (a : A) : gsmul (Int.ofNat n.succ) a = a + gsmul (Int.ofNat n) a 
  gpow_neg' (n : ℕ) (a : A) : gsmul (Int.negSucc n) a = -(gsmul ↑(n.succ) a)

class AddCommGroup (A : Type u) extends AddGroup A where
  add_comm (a b : A) : a + b = b + a

-- the automatically generated name is something like instAddCommMonoid
instance AddCommGroup.toAddCommMonoid (A : Type u) [h : AddCommGroup A] :
  AddCommMonoid A :=
{ h with }

/-

# Multiplicative groups

-/


class IsMulLeftCancel (G : Type u) [Mul G] where
  mul_left_cancel (a b c : G) : a * b = a * c → b = c

class IsMulRightCancel (G : Type u) [Mul G] where
  mul_right_cancel (a b c : G) : b * a = c * a → b = c

class Semigroup (G : Type u) extends Mul G where
  mul_assoc (a b c : G) : (a * b) * c = a * (b * c)

theorem mul_assoc {G : Type u} [Semigroup G] :
  ∀ a b c : G, a * b * c = a * (b * c) :=
Semigroup.mul_assoc

/-

## left and right cancel semigroup lemmas

-/

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

-- if anyone bothers to make CommSemigroup we need an instance
-- from CommMonoid to it, as we're no longer extending it
class CommMonoid (M : Type u) extends Monoid M where
  mul_comm (a b : M) : a * b = b * a

theorem mul_comm {M : Type u} [CommMonoid M] : ∀ a b : M, a * b = b * a :=
CommMonoid.mul_comm

class Group (G : Type u) extends Monoid G, Inv G, Div G where
  mul_left_inv (a : G) : a⁻¹ * a = 1
  div_eq_mul_inv (a b : G) : a / b = a * b⁻¹ 
  gpow : ℤ → G → G := gpow_rec
  gpow_zero' (a : G) : gpow 0 a = 1 -- try rfl
  gpow_succ' (n : ℕ) (a : G) : gpow (Int.ofNat n.succ) a = a * gpow (Int.ofNat n) a 
  gpow_neg' (n : ℕ) (a : G) : gpow (Int.negSucc n) a = (gpow ↑(n.succ) a)⁻¹

/-

# Lemmas about Groups

-/
section Group

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

end Group

class CommGroup (G : Type u) extends Group G where
  mul_comm (a b : G) : a * b = b * a

instance (G : Type u) [h : CommGroup G] : CommMonoid G :=
{ h with }