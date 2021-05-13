/-!
# Typeclasses for monoids and groups etc
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
class Semigroup (G : Type u) extends Mul G where
  mul_assoc (a b c : G) : (a * b) * c = a * (b * c)

class Monoid (M : Type u) extends Semigroup M, One M where
  mul_one (m : M) : m * 1 = m
  one_mul (m : M) : 1 * m = m
  npow : ℕ → M → M := npow_rec
  npow_zero' : ∀ x, npow 0 x = 1 -- fill in with tactic once we can do this
  npow_succ' : ∀ (n : ℕ) x, npow n.succ x = x * npow n x -- fill in with tactic

-- if anyone bothers to make CommSemigroup we need an instance
-- from CommMonoid to it, as we're no longer extending it
class CommMonoid (M : Type u) extends Monoid M where
  mul_comm (a b : M) : a * b = b * a

class Group (G : Type u) extends Monoid G, Inv G, Div G where
  mul_left_inv (a : G) : a⁻¹ * a = 1
  div_eq_mul_inv (a b : G) : a / b = a * b⁻¹ 
  gpow : ℤ → G → G := gpow_rec
  gpow_zero' (a : G) : gpow 0 a = 1 -- try rfl
  gpow_succ' (n : ℕ) (a : G) : gpow (Int.ofNat n.succ) a = a * gpow (Int.ofNat n) a 
  gpow_neg' (n : ℕ) (a : G) : gpow (Int.negSucc n) a = (gpow ↑(n.succ) a)⁻¹

class CommGroup (G : Type u) extends Group G where
  mul_comm (a b : G) : a * b = b * a

instance (G : Type u) [h : CommGroup G] : CommMonoid G :=
{ h with }