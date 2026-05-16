/-
Copyright (c) 2026 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Tactic.Common

/-!
# Huntington and Robbins algebras

In 1904, Edward Huntington gave a minimal set of 8 axioms for Boolean algebra,
in the sense that every axiom is independent of the rest.
Expressed with the lattice-theoretic notation of mathlib's `BooleanAlgebra` class:
* `⊔` and `⊓` are commutative
* `⊔` has identity `⊥`, `⊓` has identity `⊤`
* `⊔` and `⊓` distribute over each other
* For all `a`, `a ⊔ aᶜ = ⊤` and `a ⊓ aᶜ = ⊥`

This was followed in 1933 by a set of 3 axioms involving only `⊔` and `ᶜ` –
`a ⊓ b := (aᶜ ⊔ bᶜ)ᶜ`, `⊤ := a ⊔ aᶜ` and `⊥ := (a ⊔ aᶜ)ᶜ`:
* `⊔` is commutative and associative
* For all `a` and `b`, `(aᶜ ⊔ bᶜ)ᶜ ⊔ (aᶜ ⊔ b)ᶜ = a` (Huntington's axiom)

Very soon afterwards, Herbert Robbins asked whether replacing Huntington's axiom by
* For all `a` and `b`, `((a ⊔ b)ᶜ ⊔ (a ⊔ bᶜ)ᶜ)ᶜ = a` (Robbins's axiom)

still yielded an algebra equivalent to Boolean algebra. This came to be known as the
**Robbins conjecture**, and was only proved in 1997 by an early automated theorem prover
under the direction of William McCune.

The formalisation in this file largely follows Matthew Wampler-Doty's [Isabelle formalisation](https://www.isa-afp.org/entries/Robbins-Conjecture.html),
which in turn follows Allen L. Mann's [A Complete Proof of the Robbins Conjecture](https://math.colgate.edu/~amann/MA/robbins_complete.pdf).
Some differences include:
* For ease of typing and clarity around negations, algebraic notation is used
  for the newly defined algebras: `- + * 0 1` instead of `ᶜ ⊔ ⊓ ⊥ ⊤`.
* To link the 1933 Huntington and Robbins algebras to the native Boolean algebra class,
  Wampler-Doty went through an axiomatisation with 9 axioms found in a textbook.
  We go through the 1904 Huntington algebra (`H1904Algebra`).
* To make the manipulations in Mann's presentation explicit, we only appeal to proof automation
  in the forms of `ac_rfl` for rearranging terms in the 1933 Huntington and Robbins algebras,
  and `lia` for numeric comparisons. In particular, we do not use `grind`.
  Wampler-Doty's formalisation relies a lot on `metis`, a rough Isabelle equivalent of `grind`.
-/

variable {α : Type*}

/-- Huntington's 1904 axioms for Boolean algebra. -/
class H1904Algebra (α) extends Neg α, Add α, Mul α, Zero α, One α where
  /-- `+` is commutative -/
  add_comm (a b : α) : a + b = b + a
  /-- `*` is commutative -/
  mul_comm (a b : α) : a * b = b * a
  /-- 0 is an identity for `+` -/
  add_zero (a : α) : a + 0 = a
  /-- 1 is an identity for `*` -/
  mul_one (a : α) : a * 1 = a
  /-- `+` distributes over `*` -/
  add_mul_left (a b c : α) : a + (b * c) = (a + b) * (a + c)
  /-- `*` distributes over `+` -/
  mul_add_left (a b c : α) : a * (b + c) = a * b + a * c
  /-- `a + -a = 1` -/
  add_neg_self (a : α) : a + -a = 1
  /-- `a * -a = 0` -/
  mul_neg_self (a : α) : a * -a = 0

/-- Derive a `H1904Algebra` from a Boolean algebra. -/
def BooleanAlgebra.h1904Algebra [BooleanAlgebra α] : H1904Algebra α where
  neg := (·ᶜ)
  add := (· ⊔ ·)
  mul := (· ⊓ ·)
  zero := ⊥
  one := ⊤
  add_comm := sup_comm
  mul_comm := inf_comm
  add_zero := sup_bot_eq
  mul_one := inf_top_eq
  add_mul_left := sup_inf_left
  mul_add_left := inf_sup_left
  add_neg_self _ := sup_compl_eq_top
  mul_neg_self := inf_compl_self

namespace H1904Algebra

variable [H1904Algebra α] (a b c : α)

lemma zero_add : 0 + a = a := by
  rw [add_comm, add_zero]

lemma one_mul : 1 * a = a := by
  rw [mul_comm, mul_one]

lemma add_mul_right : a * b + c = (a + c) * (b + c) := by
  rw [add_comm, add_mul_left, add_comm, add_comm c]

lemma mul_add_right : (a + b) * c = a * c + b * c := by
  rw [mul_comm, mul_add_left, mul_comm, mul_comm c]

lemma neg_self_add : -a + a = 1 := by
  rw [add_comm, add_neg_self]

lemma neg_self_mul : -a * a = 0 := by
  rw [mul_comm, mul_neg_self]

lemma add_self : a + a = a := by
  rw [← mul_one (a + a), ← add_neg_self a, ← add_mul_left, mul_neg_self, add_zero]

lemma mul_self : a * a = a := by
  rw [← add_zero (a * a), ← mul_neg_self a, ← mul_add_left, add_neg_self, mul_one]

lemma add_one : a + 1 = 1 := by
  nth_rw 1 [← one_mul (a + 1), ← add_neg_self a, ← add_mul_left, mul_one, add_neg_self]

lemma mul_zero : a * 0 = 0 := by
  nth_rw 1 [← zero_add (a * 0), ← mul_neg_self a, ← mul_add_left, add_zero, mul_neg_self]

lemma one_add : 1 + a = 1 := by
  rw [add_comm, add_one]

lemma zero_mul : 0 * a = 0 := by
  rw [mul_comm, mul_zero]

lemma neg_unique (p : a + b = 1) (q : a * b = 0) : b = -a := by
  rw [← one_mul b, ← add_neg_self a, mul_add_right, q, ← neg_self_mul a, ← mul_add_left, p, mul_one]

lemma neg_neg : - -a = a :=
  (neg_unique _ _ (neg_self_add _) (neg_self_mul _)).symm

lemma add_self_mul : a + a * b = a := by
  nth_rw 1 [← mul_one a, ← mul_add_left, add_comm, add_one, mul_one]

lemma mul_self_add : a * (a + b) = a := by
  nth_rw 1 [← add_zero a, ← add_mul_left, mul_comm, mul_zero, add_zero]

lemma add_assoc : a + b + c = a + (b + c) := by
  have lp : a * (a + b + c) = a * (a + (b + c)) := by
    rw [mul_self_add, mul_add_left, mul_self_add, add_self_mul]
  have ln : -a * (a + b + c) = -a * (a + (b + c)) := by
    rw [mul_add_left, mul_add_left (-a), neg_self_mul, zero_add,
      ← mul_add_left, mul_add_left _ a, neg_self_mul, zero_add]
  rw [← one_mul (a + b + c), ← add_neg_self a, mul_add_right, lp, ln,
    ← mul_add_right, add_neg_self, one_mul]

lemma mul_assoc : a * b * c = a * (b * c) := by
  have lp : a + a * b * c = a + a * (b * c) := by
    rw [add_self_mul, add_mul_left, add_self_mul, mul_self_add]
  have ln : -a + a * b * c = -a + a * (b * c) := by
    rw [add_mul_left, add_mul_left (-a), neg_self_add, one_mul,
      ← add_mul_left, add_mul_left _ a, neg_self_add, one_mul]
  rw [← zero_add (a * b * c), ← mul_neg_self a, add_mul_right, lp, ln,
    ← add_mul_right, mul_neg_self, zero_add]

lemma neg_add : -(a + b) = -a * -b := by
  apply (neg_unique _ _ ?_ ?_).symm
  · rw [add_mul_left, add_comm, ← add_assoc, neg_self_add,
      one_add, add_assoc, add_neg_self, add_one, mul_self]
  · rw [← mul_assoc, mul_add_right, mul_neg_self, zero_add,
      mul_comm, ← mul_assoc, neg_self_mul, zero_mul]

lemma neg_mul : -(a * b) = -a + -b := by
  apply (neg_unique _ _ ?_ ?_).symm
  · rw [← add_assoc, add_mul_right, add_neg_self, one_mul,
      add_comm, ← add_assoc, neg_self_add, one_add]
  · rw [mul_add_left, mul_comm, ← mul_assoc, neg_self_mul,
      zero_mul, mul_assoc, mul_neg_self, mul_zero, add_self]

/-- Derive a distributive lattice from a `H1904Algebra`. -/
def distribLattice : DistribLattice α where
  le a b := a + b = b
  le_refl := add_self
  le_trans _ _ _ h₁ h₂ := by rw [← h₂, ← add_assoc, h₁]
  le_antisymm _ _ h₁ h₂ := by rwa [← h₂, add_comm]
  sup := (· + ·)
  inf := (· * ·)
  le_sup_left _ _ := by rw [← add_assoc, add_self]
  le_sup_right _ _ := by rw [add_comm, add_assoc, add_self]
  sup_le _ _ _ h₁ h₂ := by rwa [add_assoc, h₂]
  inf_le_left _ _ := by rw [add_comm, add_self_mul]
  inf_le_right _ _ := by rw [add_comm, mul_comm, add_self_mul]
  le_inf _ _ _ h₁ h₂ := by rw [add_mul_left, h₁, h₂]
  le_sup_inf _ _ _ := by
    change (_ + _) * (_ + _) + (_ + _ * _) = _ + _ * _
    rw [add_mul_left, add_self]

/-- Derive a Boolean algebra from a `H1904Algebra`. -/
def booleanAlgebra : BooleanAlgebra α where
  __ := distribLattice
  compl := (-·)
  bot := 0
  top := 1
  inf_compl_le_bot a := by
    change a * -a ≤ 0
    rw [mul_neg_self]
  top_le_sup_compl a := by
    change 1 ≤ a + -a
    rw [add_neg_self]
  le_top a := by
    change a + 1 = 1
    rw [add_one]
  bot_le a := by
    change 0 + a = a
    rw [add_comm, add_zero]

end H1904Algebra

/-- Huntington's 1933 axioms for Boolean algebra. -/
class HuntingtonAlgebra (α) extends Inhabited α, AddCommSemigroup α, Neg α where
  /-- Huntington's axiom -/
  huntington (a b : α) : -(-a + -b) + -(-a + b) = a

/-- Derive a `HuntingtonAlgebra` from a `H1904Algebra`. -/
def H1904Algebra.huntingtonAlgebra [H1904Algebra α] : HuntingtonAlgebra α where
  default := 0
  add_comm := add_comm
  add_assoc := add_assoc
  huntington _ _ := by
    rw [neg_add, neg_neg, neg_neg, neg_add, neg_neg, ← mul_add_left, add_neg_self, mul_one]

namespace HuntingtonAlgebra

variable [HuntingtonAlgebra α] (a b c : α)

private instance : Std.Associative (α := α) (· + ·) := ⟨add_assoc⟩

lemma neg_neg_with_add : a + -a = -a + - -a := by
  rw [← huntington (- -a) (-a)]
  nth_rw 2 [← huntington (-a) (-a)]
  nth_rw 1 [← huntington (-a) (- -a), ← huntington a (- -a)]
  ac_rfl

lemma neg_neg : - -a = a := by
  nth_rw 2 [← huntington a (- -a)]
  nth_rw 1 [← huntington (- -a) (-a), add_comm (- - -a), ← neg_neg_with_add]
  ac_rfl

lemma exists_one : a + -a = b + -b := by
  nth_rw 1 [← huntington (-b) (-a), ← huntington b (-a),
    ← huntington (-a) (-b), ← huntington a (-b)]
  ac_rfl

private instance mul : Mul α := ⟨fun a b ↦ -(-a + -b)⟩
private instance zero : Zero α := ⟨-(default + -default)⟩
private instance one : One α := ⟨default + -default⟩

lemma mul_def : a * b = -(-a + -b) := rfl
lemma zero_def : (0 : α) = -(default + -default) := rfl
lemma one_def : (1 : α) = default + -default := rfl
lemma neg_zero : -(0 : α) = 1 := by rw [zero_def, neg_neg, one_def]
lemma neg_one : -(1 : α) = 0 := rfl
lemma mul_comm : a * b = b * a := by rw [mul_def, mul_def, add_comm]
lemma add_neg_self : a + -a = 1 := exists_one ..
lemma mul_neg_self : a * -a = 0 := by rw [mul_def, exists_one _ default, zero_def]
lemma neg_add : -(a + b) = -a * -b := by rw [mul_def, neg_neg, neg_neg]
lemma neg_mul : -(a * b) = -a + -b := by rw [mul_def, neg_neg]

lemma add_zero : a + 0 = a := by
  have l₀ := huntington (0 : α) 0
  rw [add_comm _ 0, add_neg_self, neg_zero, ← neg_one] at l₀
  have l₁ := add_neg_self (1 : α)
  rw [← l₀, add_comm, add_assoc, add_comm (-1), add_neg_self] at l₁
  have s₁ := add_neg_self (1 + 1 : α)
  rw [add_assoc, add_comm _ (-_), l₁] at s₁
  have s₀ := neg_one (α := α)
  rw [← l₀, s₁, neg_one] at s₀
  rw [← huntington a a, add_comm _ a, add_neg_self, neg_one, add_assoc, s₀]

lemma mul_one : a * 1 = a := by
  rw [mul_def, neg_one, add_zero, neg_neg]

lemma mul_assoc : a * b * c = a * (b * c) := by
  rw [mul_def, neg_mul, mul_def, neg_mul, add_assoc]

lemma mul_self : a * a = a := by
  nth_rw 3 [← huntington a a]
  rw [add_comm _ a, add_neg_self, neg_one, add_zero, mul_def]

lemma add_self : a + a = a := by
  nth_rw 3 [← neg_neg a]
  rw [← mul_self (-a), mul_def, neg_neg, neg_neg]

lemma add_one : a + 1 = 1 := by
  rw [← add_neg_self a, ← add_assoc, add_self]

lemma mul_zero : a * 0 = 0 := by
  rw [← mul_neg_self a, ← mul_assoc, mul_self]

lemma add_self_mul : a + a * b = a := by
  nth_rw 1 [← huntington a b, mul_def, add_comm, ← add_assoc, add_self, huntington]

lemma mul_self_add : a * (a + b) = a := by
  rw [mul_def, neg_add a, add_self_mul, neg_neg]

lemma huntington' : a * b + a * -b = a := by
  nth_rw 3 [← huntington a b]
  rw [mul_def, mul_def, neg_neg]

private instance : Std.Commutative (α := α) (· * ·) := ⟨mul_comm⟩
private instance : Std.Associative (α := α) (· * ·) := ⟨mul_assoc⟩

lemma mul_add_left : a * (b + c) = a * b + a * c := by
  nth_rw 1 [← huntington' (_ * _) b, mul_assoc, mul_comm _ b, mul_self_add,
    ← huntington' (a * b) c, ← huntington' (_ * -b) c]
  have rearr : a * (b + c) * -b * c = a * -b * (c * (c + b)) := by ac_rfl
  rw [rearr, mul_self_add, mul_assoc _ (-b) (-c), ← neg_add, mul_assoc _ (b + c), mul_neg_self,
    mul_zero, add_zero, ← add_self (a * b * c), add_assoc (_ * _), huntington',
    ← huntington' (a * c) b]
  ac_rfl

lemma add_mul_left : a + b * c = (a + b) * (a + c) := by
  rw [mul_def (a + b), neg_add a, neg_add a, ← mul_add_left, neg_mul, neg_neg, mul_def]

/-- Derive a `H1904Algebra` from a Huntington algebra. -/
def h1904Algebra : H1904Algebra α where
  add_comm := add_comm
  mul_comm := mul_comm
  add_zero := add_zero
  mul_one := mul_one
  add_mul_left := add_mul_left
  mul_add_left := mul_add_left
  add_neg_self := add_neg_self
  mul_neg_self := mul_neg_self

end HuntingtonAlgebra

/-- The type of **Robbins algebras**. -/
class RobbinsAlgebra (α) extends Inhabited α, AddCommSemigroup α, Neg α where
  /-- Robbins's axiom -/
  robbins (a b : α) : -(-(a + b) + -(a + -b)) = a

/-- Derive a Robbins algebra from a `H1904Algebra`. -/
def H1904Algebra.robbinsAlgebra [H1904Algebra α] : RobbinsAlgebra α where
  default := 0
  add_comm := add_comm
  add_assoc := add_assoc
  robbins _ _ := by rw [neg_add, neg_neg, neg_neg, ← add_mul_left, mul_neg_self, add_zero]

namespace RobbinsAlgebra

variable [RobbinsAlgebra α] (a b c d : α)

private instance : Std.Associative (α := α) (· + ·) := ⟨add_assoc⟩

/-- Sum a number of copies of an element. Not intended to be used for 0 copies (although the
ultimately correct value of `-(a + -a)` is included for completeness). -/
def smul : ℕ → α → α
  | 0, a => -(a + -a)
  | 1, a => a
  | k + 2, a => smul (k + 1) a + a

private instance : SMul ℕ α where smul := smul

lemma smul1 : 1 • a = a := rfl
lemma smul2 : 2 • a = a + a := rfl
lemma smul3 : 3 • a = a + a + a := rfl
lemma smul4 : 4 • a = a + a + a + a := rfl
lemma smul5 : 5 • a = a + a + a + a + a := rfl

lemma smul_succ {k : ℕ} {a : α} (hk : 1 ≤ k) : (k + 1) • a = k • a + a := by
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k ih => rfl

lemma mann_44 : -(-(-(a + b) + -a + b) + b) = -(a + b) := by
  nth_rw 2 [← robbins (-(a + b)) (-a + b)]
  nth_rw 3 [← robbins b a]
  congr 2 <;> ac_rfl

lemma mann_45 : -(-(-(-a + b) + a + b) + b) = -(-a + b) := by
  nth_rw 2 [← robbins (-(-a + b)) (a + b)]
  nth_rw 3 [← robbins b a]
  ac_rfl

lemma mann_46 : -(-(-(-a + b) + a + b + b) + -(-a + b)) = b := by
  conv_rhs => rw [← robbins b (-(-a + b) + a + b)]
  nth_rw 2 [← mann_45 a b]
  ac_rfl

lemma mann_47 : -(-(-(-(-a + b) + a + b + b) + -(-a + b) + c) + -(b + c)) = c := by
  set w := -(-(-a + b) + a + b + b) + -(-a + b)
  nth_rw 3 [← robbins c w]
  rw [mann_46 a b]
  ac_rfl

lemma mann_48 : -(-(-(-(-a + b) + a + b + b) + -(-a + b) + -(b + c) + c) + c) = -(b + c) := by
  have key := robbins (-(b + c)) (-(-(-a + b) + a + b + b) + -(-a + b) + c)
  set q := -(-(-(-a + b) + a + b + b) + -(-a + b) + c)
  conv_rhs => rw [← key, add_comm _ q, mann_47]
  ac_rfl

lemma mann_49 :
    -(-(-(-(-(-a + b) + a + b + b) + -(-a + b) + -(b + c) + c) + c + d) + -(-(b + c) + d)) = d := by
  set w := -(-(-(-a + b) + a + b + b) + -(-a + b) + -(b + c) + c) + c
  nth_rw 3 [← robbins d w]
  rw [mann_48 a b c]
  ac_rfl

/-- A common subexpression occurring in `mann_50` to `winker`. -/
def q : α := -(-(3 • a) + a)

lemma mann_50 : -(-(q a + -(3 • a)) + -(q a + 5 • a)) = q a := by
  have k₁ := mann_44 (3 • a) (q a + 2 • a)
  have rearr₁ : -(-(3 • a + (q a + 2 • a)) + -(3 • a) + (q a + 2 • a)) + (q a + 2 • a) =
      -(-(q a + 5 • a) + -(3 • a) + (q a + 2 • a)) + 2 • a + q a := by
    rw [smul2, smul3, smul5]
    ac_rfl
  rw [rearr₁] at k₁
  have k₂ : -(-(-(-(q a + 3 • a + a + a) + q a + -(a + 2 • a) + 2 • a) + 2 • a + q a) +
      -(-(a + 2 • a) + q a)) = q a := mann_49 (3 • a) a (2 • a) (q a)
  have rearr₂ : (-(q a + 3 • a + a + a) + q a + -(a + 2 • a) + 2 • a) =
      -(q a + 5 • a) + -(3 • a) + (q a + 2 • a) := by
    simp_rw [smul2, smul3, smul5, ← add_assoc]
    congr 2
    simp_rw [add_assoc]
    congr 1
    rw [add_comm]
  rw [rearr₂, k₁] at k₂
  convert k₂ using 2
  rw [smul2, smul3, smul5]
  ac_rfl

lemma mann_51 : -(q a + 5 • a) = -(3 • a) := by
  have k₁ := robbins (-(q a + 5 • a)) (q a + -(3 • a))
  have k₂ : -(-(q a + -(3 • a)) + -(q a + 5 • a)) = q a := mann_50 a
  have k₃ : -(-(-(q a + 3 • a + a + a) + q a + -(3 • a)) + q a) = -(3 • a) := by
    convert mann_47 (3 • a) a (-(3 • a)) using 3
    rw [q, add_comm]
  rw [← k₃, ← k₁, ← add_comm (-(q a + _)), k₂]
  simp_rw [smul3, smul5, ← add_assoc]

lemma mann_52 : -(-(q a + -(3 • a) + 2 • a) + -(3 • a)) = q a + 2 • a := by
  have key := robbins (q a + 2 • a) (3 • a)
  have rearr : q a + 2 • a + 3 • a = q a + 5 • a := by
    rw [smul2, smul3, smul5]
    ac_rfl
  rw [← key, rearr, mann_51]
  ac_rfl

lemma mann_53 : -(q a + -(3 • a)) = a := by
  have k₁ := robbins a (q a + 4 • a)
  have rearr : a + (q a + 4 • a) = q a + 5 • a := by
    rw [smul4, smul5]
    ac_rfl
  rw [rearr, mann_51] at k₁
  have k₂ : -(-(q a + 3 • a + a) + a) = q a := mann_45 (3 • a) a
  have rearr₂ : -(q a + 3 • a + a) + a = a + -(q a + 4 • a) := by
    rw [smul3, smul4]
    ac_rfl
  rw [rearr₂] at k₂
  rw [k₂] at k₁
  rwa [add_comm]

lemma mann_54 : -(-(q a + -(3 • a) + b) + -(a + b)) = b := by
  conv_rhs => rw [← robbins b (q a + -(3 • a)), mann_53]
  ac_rfl

/-- **Winker's first condition**,
proved in 1997 by the automated theorem prover EQP to be derivable in Robbins algebras. -/
theorem winker : ∃ x y : α, x + y = y := by
  refine ⟨q default, 2 • default, ?_⟩
  conv_lhs => rw [← mann_52]
  conv_rhs => rw [← mann_54 default (2 • default)]
  simp_rw [smul2, smul3, ← add_assoc]

section Idempotence

variable {a b c} {k : ℕ}

lemma mann_33 (h : -(a + -(b + c)) = -(a + b + -c)) : a + b = a := by
  rw [← robbins (a + b) c, ← h, add_assoc, robbins]

lemma mann_34 (h : -(a + -(b + c)) = -(b + -(a + c))) : a = b := by
  rw [← robbins a (b + c), h, show a + (b + c) = b + (a + c) by ac_rfl, robbins]

lemma mann_35 (h : -(a + -b) = c) : -(-(a + b) + c) = a := by
  rw [← h, robbins]

lemma mann_36 (hk : 1 ≤ k) (h : -(a + -b) = c) : -(a + -(b + k • (a + c))) = c := by
  induction k, hk using Nat.le_induction with
  | base =>
    nth_rw 1 [smul1, ← mann_35 h]
    conv_rhs => rw [← robbins c (a + b)]
    ac_rfl
  | succ k lk ih =>
    nth_rw 1 [smul_succ lk, ← mann_35 ih]
    conv_rhs => rw [← robbins c (a + b + k • (a + c))]
    rw [add_comm]
    congr 2 <;> ac_rfl

lemma mann_37 (hk : 1 ≤ k) (h : -(-(a + -b) + -b) = a) : -(b + k • (a + -(a + -b))) = -b := by
  set c := -(a + -b)
  have aux := mann_36 hk h
  rw [add_comm c a] at aux
  set bk := b + k • (a + c)
  apply mann_34 (c := c)
  rw [add_comm (-b), h, add_comm _ c, aux, add_comm _ a, mann_36 hk rfl, add_comm]

lemma mann_38 (hk : 1 ≤ k) (h : -(a + b) = -b) : -(b + k • (a + -(a + -b))) = -b := by
  apply mann_37 hk
  nth_rw 2 [← robbins a b, ← h]
  ac_rfl

lemma mann_39 (h₂ : -(2 • a + b) = -b) (h₃ : -(3 • a + b) = -b) : 2 • a + b = 3 • a + b := by
  conv_rhs at h₃ => rw [← h₂]
  rw [smul_succ (by lia), show 2 • a + a + b = a + (2 • a + b) by ac_rfl] at h₃
  have e₁ := mann_38 le_rfl h₂
  have e₂ := mann_38 le_rfl h₃
  rw [smul1] at e₁ e₂
  rw [show b + (2 • a + -(2 • a + -b)) = 2 • a + b + -(a + (a + -b)) by rw [smul2]; ac_rfl] at e₁
  rw [h₂] at e₂
  conv_rhs at e₁ => rw [← e₂, ← add_assoc]
  rw [← mann_33 e₁]
  rw [smul2, smul3]
  ac_rfl

lemma mann_40 (h : -(a + b) = -b ∨ -(-(a + -b) + -b) = a) :
    b + 2 • (a + -(a + -b)) = b + 3 • (a + -(a + -b)) := by
  suffices -(b + 2 • (a + -(a + -b))) = -b ∧ -(b + 3 • (a + -(a + -b))) = -b by
    rw [add_comm b, add_comm b] at this
    replace this := mann_39 this.1 this.2
    rwa [add_comm b, add_comm b]
  rcases h with h | h
  · exact ⟨mann_38 (by lia) h, mann_38 (by lia) h⟩
  · exact ⟨mann_37 (by lia) h, mann_37 (by lia) h⟩

theorem exists_idempotent : ∃ x : α, x + x = x := by
  obtain ⟨a, b, h⟩ := winker (α := α)
  let c := b + 2 • -(a + -b)
  have k₁ : a + c = c := by
    unfold c
    rw [← add_assoc, h]
  have k₂ : -b = -c := by
    rw [← mann_38 (show 1 ≤ 2 by lia) (congrArg (-·) h), smul2,
      show b + (a + -(a + -b) + (a + -(a + -b))) = a + (a + b) + (-(a + -b) + -(a + -b)) by ac_rfl,
      h, h, ← smul2]
  have k₃ : c + -(a + -c) = c := by
    rw [← k₂]
    conv_lhs => simp only [c]
    nth_rw 1 [add_assoc, smul2, ← h, ← h, ← h,
      show a + (a + (a + b)) + (-(a + -b) + -(a + -b) + -(a + -b)) =
        b + ((a + -(a + -b)) + (a + -(a + -b)) + (a + -(a + -b))) by ac_rfl,
      ← smul3, ← mann_40 (.inl (by rw [h])), smul2,
      show b + (a + -(a + -b) + (a + -(a + -b))) =
        a + (a + b) + (-(a + -b) + -(a + -b)) by ac_rfl, ← smul2, h, h]
  have k₄ : -(-(c + -c) + -c) = c := by
    nth_rw 4 [← robbins c (a + -c)]
    nth_rw 3 [← k₃]
    nth_rw 1 [← k₁]
    ac_rfl
  replace k₄ := mann_40 (.inr k₄)
  set d := c + -(c + -c)
  have fin : 3 • d + d = 2 • d + d := by
    change _ + (c + -(c + -c)) = _ + (c + -(c + -c))
    simp_rw [← add_assoc]
    rw [add_comm (2 • d), k₄, add_comm (3 • d)]
  use 3 • d
  nth_rw 2 [smul3]
  rw [← add_assoc, ← add_assoc _ d]
  iterate 3 rw [fin, ← smul_succ (by lia)]

end Idempotence

theorem exists_zero : ∃ z : α, ∀ a, a + z = a := by
  obtain ⟨a, ha⟩ := exists_idempotent (α := α)
  refine ⟨-(a + -a), fun x ↦ ?_⟩
  set z := -(a + -a)
  have k₁ : a = -(-a + z) := by nth_rw 1 [← robbins a a, ha]
  have k₂ (x) : a + x = -(-(a + x) + -(a + x + -a)) := by
    nth_rw 1 [← robbins (a + x) a, show a + x + a = a + a + x by ac_rfl, ha]
  have k₃ (x) : x = -(-(x + -a + z) + -(x + a)) := by
    nth_rw 1 [← robbins x (-a + z), ← k₁, add_assoc]
  have k₄ : -a = -(-(a + -a + -a) + a) := by
    nth_rw 1 [← robbins (-a) (a + -a), ← k₁]
    ac_rfl
  have k₅ : a = -(-(a + -a + z) + -a) := by nth_rw 1 [k₃ a, ha]
  have k₆ : a = -(-(a + -a + -a) + -a) := by
    nth_rw 1 [← robbins a (a + -a + -a), add_comm a (-(_ + _)), ← k₄, ← add_assoc, ← add_assoc, ha]
  have k₇ : -(a + -a + -a) = z := by rw [← robbins (-(a + -a + -a)) a, ← k₄, ← k₆, add_comm]
  have k₈ : -a = -(a + z) := by rw [k₄, k₇, add_comm]
  have k₉ : a + z = a := by
    rw [k₂ z, ← k₈]
    conv_rhs => rw [k₅]
    ac_rfl
  nth_rw 2 [k₃ x]
  rw [← robbins (x + z) a, add_assoc, add_comm z, k₉]
  ac_rfl

theorem neg_neg : - -a = a := by
  obtain ⟨z, hz⟩ := exists_zero (α := α)
  have k₁ (x) : z = -(-x + - -x) := by rw [← robbins z x, add_comm z, hz, add_comm z, hz]
  have k₂ (x : α) : -x = - -(-x + - - -x) := by
    nth_rw 1 [← robbins (-x) (- -x), ← k₁, add_comm z, hz]
  have k₃ (x : α) : - - -x = -x := by
    nth_rw 1 [← robbins (- - -x) (-x), add_comm _ (- -x), ← k₁ (-x), hz, add_comm, ← k₂]
  simpa only [robbins] using k₃ (-(a + z) + -(a + -z))

/-- Derive a Huntington algebra from a Robbins algebra. -/
def huntingtonAlgebra : HuntingtonAlgebra α where
  huntington a b := by
    conv_rhs => rw [← neg_neg a, ← robbins (-a) b, neg_neg]
    ac_rfl

/-- Derive a Boolean algebra from a Robbins algebra. -/
def booleanAlgebra : BooleanAlgebra α :=
  let _ : HuntingtonAlgebra α := huntingtonAlgebra
  let _ : H1904Algebra α := HuntingtonAlgebra.h1904Algebra
  H1904Algebra.booleanAlgebra

end RobbinsAlgebra
