/-
Copyright (c) 2022 Siddhartha Prasad, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Prasad, Yaël Dillies
-/
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Ring.InjSurj
import Mathlib.Algebra.Ring.Pi
import Mathlib.Algebra.Ring.Prod
import Mathlib.Tactic.Monotonicity.Attr

/-!
# Kleene Algebras

This file defines idempotent semirings and Kleene algebras, which are used extensively in the theory
of computation.

An idempotent semiring is a semiring whose addition is idempotent. An idempotent semiring is
naturally a semilattice by setting `a ≤ b` if `a + b = b`.

A Kleene algebra is an idempotent semiring equipped with an additional unary operator `∗`, the
Kleene star.

## Main declarations

* `IdemSemiring`: Idempotent semiring
* `IdemCommSemiring`: Idempotent commutative semiring
* `KleeneAlgebra`: Kleene algebra

## Notation

`a∗` is notation for `kstar a` in scope `Computability`.

## References

* [D. Kozen, *A completeness theorem for Kleene algebras and the algebra of regular events*]
  [kozen1994]
* https://planetmath.org/idempotentsemiring
* https://encyclopediaofmath.org/wiki/Idempotent_semi-ring
* https://planetmath.org/kleene_algebra

## TODO

Instances for `AddOpposite`, `MulOpposite`, `ULift`, `Subsemiring`, `Subring`, `Subalgebra`.

## Tags

kleene algebra, idempotent semiring
-/


open Function

universe u

variable {α β ι : Type*} {π : ι → Type*}

/-- An idempotent semiring is a semiring with the additional property that addition is idempotent.
-/
class IdemSemiring (α : Type u) extends Semiring α, SemilatticeSup α where
  protected sup := (· + ·)
  protected add_eq_sup : ∀ a b : α, a + b = a ⊔ b := by
    intros
    rfl
  /-- The bottom element of an idempotent semiring: `0` by default -/
  protected bot : α := 0
  protected bot_le : ∀ a, bot ≤ a

/-- An idempotent commutative semiring is a commutative semiring with the additional property that
addition is idempotent. -/
class IdemCommSemiring (α : Type u) extends CommSemiring α, IdemSemiring α

/-- Notation typeclass for the Kleene star `∗`. -/
class KStar (α : Type*) where
  /-- The Kleene star operator on a Kleene algebra -/
  protected kstar : α → α

@[inherit_doc] scoped[Computability] postfix:1024 "∗" => KStar.kstar

open Computability

/-- A Kleene Algebra is an idempotent semiring with an additional unary operator `kstar` (for Kleene
star) that satisfies the following properties:
* `1 + a * a∗ ≤ a∗`
* `1 + a∗ * a ≤ a∗`
* If `a * c + b ≤ c`, then `a∗ * b ≤ c`
* If `c * a + b ≤ c`, then `b * a∗ ≤ c`
-/
class KleeneAlgebra (α : Type*) extends IdemSemiring α, KStar α where
  protected one_le_kstar : ∀ a : α, 1 ≤ a∗
  protected mul_kstar_le_kstar : ∀ a : α, a * a∗ ≤ a∗
  protected kstar_mul_le_kstar : ∀ a : α, a∗ * a ≤ a∗
  protected mul_kstar_le_self : ∀ a b : α, b * a ≤ b → b * a∗ ≤ b
  protected kstar_mul_le_self : ∀ a b : α, a * b ≤ b → a∗ * b ≤ b

-- See note [lower instance priority]
instance (priority := 100) IdemSemiring.toOrderBot [IdemSemiring α] : OrderBot α :=
  { ‹IdemSemiring α› with }

-- See note [reducible non-instances]
/-- Construct an idempotent semiring from an idempotent addition. -/
abbrev IdemSemiring.ofSemiring [Semiring α] (h : ∀ a : α, a + a = a) : IdemSemiring α :=
  { ‹Semiring α› with
    le := fun a b ↦ a + b = b
    le_refl := h
    le_trans := fun a b c hab hbc ↦ by
      rw [← hbc, ← add_assoc, hab]
    le_antisymm := fun a b hab hba ↦ by rwa [← hba, add_comm]
    sup := (· + ·)
    le_sup_left := fun a b ↦ by
      rw [← add_assoc, h]
    le_sup_right := fun a b ↦ by
      rw [add_comm, add_assoc, h]
    sup_le := fun a b c hab hbc ↦ by
      rwa [add_assoc, hbc]
    bot := 0
    bot_le := zero_add }

section IdemSemiring

variable [IdemSemiring α] {a b c : α}

theorem add_eq_sup (a b : α) : a + b = a ⊔ b :=
  IdemSemiring.add_eq_sup _ _

scoped[Computability] attribute [simp] add_eq_sup

theorem add_idem (a : α) : a + a = a := by simp

lemma natCast_eq_one {n : ℕ} (nezero : n ≠ 0) : (n : α) = 1 := by
  rw [← Nat.one_le_iff_ne_zero] at nezero
  induction n, nezero using Nat.le_induction with
  | base => exact Nat.cast_one
  | succ x _ hx => rw [Nat.cast_add, hx, Nat.cast_one, add_idem 1]

lemma ofNat_eq_one {n : ℕ} [n.AtLeastTwo] : (ofNat(n) : α) = 1 :=
  natCast_eq_one <| Nat.ne_zero_of_lt Nat.AtLeastTwo.prop

theorem nsmul_eq_self : ∀ {n : ℕ} (_ : n ≠ 0) (a : α), n • a = a
  | 0, h => (h rfl).elim
  | 1, _ => one_nsmul
  | n + 2, _ => fun a ↦ by rw [succ_nsmul, nsmul_eq_self n.succ_ne_zero, add_idem]

theorem add_eq_left_iff_le : a + b = a ↔ b ≤ a := by simp

theorem add_eq_right_iff_le : a + b = b ↔ a ≤ b := by simp

alias ⟨_, LE.le.add_eq_left⟩ := add_eq_left_iff_le

alias ⟨_, LE.le.add_eq_right⟩ := add_eq_right_iff_le

theorem add_le_iff : a + b ≤ c ↔ a ≤ c ∧ b ≤ c := by simp

theorem add_le (ha : a ≤ c) (hb : b ≤ c) : a + b ≤ c :=
  add_le_iff.2 ⟨ha, hb⟩

-- See note [lower instance priority]
instance (priority := 100) IdemSemiring.toIsOrderedAddMonoid :
    IsOrderedAddMonoid α :=
  { add_le_add_left := fun a b hbc c ↦ by
      simp_rw [add_eq_sup]
      grw [hbc] }

-- See note [lower instance priority]
instance (priority := 100) IdemSemiring.toCanonicallyOrderedAdd :
    CanonicallyOrderedAdd α where
  exists_add_of_le h := ⟨_, h.add_eq_right.symm⟩
  le_add_self a b := add_eq_left_iff_le.1 <| by rw [add_assoc, add_idem]
  le_self_add a b := add_eq_right_iff_le.1 <| by rw [← add_assoc, add_idem]

-- See note [lower instance priority]
instance (priority := 100) IdemSemiring.toMulLeftMono : MulLeftMono α :=
  ⟨fun a b c hbc ↦ add_eq_left_iff_le.1 <| by rw [← mul_add, hbc.add_eq_left]⟩

-- See note [lower instance priority]
instance (priority := 100) IdemSemiring.toMulRightMono : MulRightMono α :=
  ⟨fun a b c hbc ↦ add_eq_left_iff_le.1 <| by rw [← add_mul, hbc.add_eq_left]⟩

end IdemSemiring

section KleeneAlgebra

variable [KleeneAlgebra α] {a b c : α}

@[simp]
theorem one_le_kstar : 1 ≤ a∗ :=
  KleeneAlgebra.one_le_kstar _

theorem mul_kstar_le_kstar : a * a∗ ≤ a∗ :=
  KleeneAlgebra.mul_kstar_le_kstar _

theorem kstar_mul_le_kstar : a∗ * a ≤ a∗ :=
  KleeneAlgebra.kstar_mul_le_kstar _

theorem mul_kstar_le_self : b * a ≤ b → b * a∗ ≤ b :=
  KleeneAlgebra.mul_kstar_le_self _ _

theorem kstar_mul_le_self : a * b ≤ b → a∗ * b ≤ b :=
  KleeneAlgebra.kstar_mul_le_self _ _

theorem mul_kstar_le (hb : b ≤ c) (ha : c * a ≤ c) : b * a∗ ≤ c := by grw [hb, mul_kstar_le_self ha]

theorem kstar_mul_le (hb : b ≤ c) (ha : a * c ≤ c) : a∗ * b ≤ c := by grw [hb, kstar_mul_le_self ha]

theorem kstar_le_of_mul_le_left (hb : 1 ≤ b) : b * a ≤ b → a∗ ≤ b := by
  simpa using mul_kstar_le hb

theorem kstar_le_of_mul_le_right (hb : 1 ≤ b) : a * b ≤ b → a∗ ≤ b := by
  simpa using kstar_mul_le hb

@[simp]
theorem le_kstar : a ≤ a∗ :=
  le_trans (le_mul_of_one_le_left' one_le_kstar) kstar_mul_le_kstar

@[mono]
theorem kstar_mono : Monotone (KStar.kstar : α → α) :=
  fun _ _ h ↦
    kstar_le_of_mul_le_left one_le_kstar <| kstar_mul_le (h.trans le_kstar) <| mul_kstar_le_kstar

@[simp]
theorem kstar_eq_one : a∗ = 1 ↔ a ≤ 1 :=
  ⟨le_kstar.trans_eq,
    fun h ↦ one_le_kstar.antisymm' <| kstar_le_of_mul_le_left le_rfl <| by rwa [one_mul]⟩

@[simp] lemma kstar_zero : (0 : α)∗ = 1 := kstar_eq_one.2 (zero_le _)

@[simp]
theorem kstar_one : (1 : α)∗ = 1 :=
  kstar_eq_one.2 le_rfl

@[simp]
theorem kstar_mul_kstar (a : α) : a∗ * a∗ = a∗ :=
  (mul_kstar_le le_rfl <| kstar_mul_le_kstar).antisymm <| le_mul_of_one_le_left' one_le_kstar

@[simp]
theorem kstar_eq_self : a∗ = a ↔ a * a = a ∧ 1 ≤ a :=
  ⟨fun h ↦ ⟨by rw [← h, kstar_mul_kstar], one_le_kstar.trans_eq h⟩,
    fun h ↦ (kstar_le_of_mul_le_left h.2 h.1.le).antisymm le_kstar⟩

@[simp]
theorem kstar_idem (a : α) : a∗∗ = a∗ :=
  kstar_eq_self.2 ⟨kstar_mul_kstar _, one_le_kstar⟩

@[simp]
theorem pow_le_kstar : ∀ {n : ℕ}, a ^ n ≤ a∗
  | 0 => (pow_zero _).trans_le one_le_kstar
  | n + 1 => by grw [pow_succ', pow_le_kstar, mul_kstar_le_kstar]

end KleeneAlgebra

namespace Prod

instance instIdemSemiring [IdemSemiring α] [IdemSemiring β] : IdemSemiring (α × β) :=
  { Prod.instSemiring, Prod.instSemilatticeSup _ _, Prod.instOrderBot _ _ with
    add_eq_sup := fun _ _ ↦ Prod.ext (add_eq_sup _ _) (add_eq_sup _ _) }

instance [IdemCommSemiring α] [IdemCommSemiring β] : IdemCommSemiring (α × β) :=
  { Prod.instCommSemiring, Prod.instIdemSemiring with }

variable [KleeneAlgebra α] [KleeneAlgebra β]

instance : KleeneAlgebra (α × β) :=
  { Prod.instIdemSemiring with
    kstar := fun a ↦ (a.1∗, a.2∗)
    one_le_kstar := fun _ ↦ ⟨one_le_kstar, one_le_kstar⟩
    mul_kstar_le_kstar := fun _ ↦ ⟨mul_kstar_le_kstar, mul_kstar_le_kstar⟩
    kstar_mul_le_kstar := fun _ ↦ ⟨kstar_mul_le_kstar, kstar_mul_le_kstar⟩
    mul_kstar_le_self := fun _ _ ↦ And.imp mul_kstar_le_self mul_kstar_le_self
    kstar_mul_le_self := fun _ _ ↦ And.imp kstar_mul_le_self kstar_mul_le_self }

theorem kstar_def (a : α × β) : a∗ = (a.1∗, a.2∗) :=
  rfl

@[simp]
theorem fst_kstar (a : α × β) : a∗.1 = a.1∗ :=
  rfl

@[simp]
theorem snd_kstar (a : α × β) : a∗.2 = a.2∗ :=
  rfl

end Prod

namespace Pi

instance instIdemSemiring [∀ i, IdemSemiring (π i)] : IdemSemiring (∀ i, π i) :=
  { Pi.semiring, Pi.instSemilatticeSup, Pi.instOrderBot with
    add_eq_sup := fun _ _ ↦ funext fun _ ↦ add_eq_sup _ _ }

instance [∀ i, IdemCommSemiring (π i)] : IdemCommSemiring (∀ i, π i) :=
  { Pi.commSemiring, Pi.instIdemSemiring with }

variable [∀ i, KleeneAlgebra (π i)]

instance : KleeneAlgebra (∀ i, π i) :=
  { Pi.instIdemSemiring with
    kstar := fun a i ↦ (a i)∗
    one_le_kstar := fun _ _ ↦ one_le_kstar
    mul_kstar_le_kstar := fun _ _ ↦ mul_kstar_le_kstar
    kstar_mul_le_kstar := fun _ _ ↦ kstar_mul_le_kstar
    mul_kstar_le_self := fun _ _ h _ ↦ mul_kstar_le_self <| h _
    kstar_mul_le_self := fun _ _ h _ ↦ kstar_mul_le_self <| h _ }

@[push ←]
theorem kstar_def (a : ∀ i, π i) : a∗ = fun i ↦ (a i)∗ :=
  rfl

@[simp]
theorem kstar_apply (a : ∀ i, π i) (i : ι) : a∗ i = (a i)∗ :=
  rfl

end Pi

namespace Function.Injective

-- See note [reducible non-instances]
/-- Pullback an `IdemSemiring` instance along an injective function. -/
protected abbrev idemSemiring [IdemSemiring α] [Zero β] [One β] [Add β] [Mul β] [Pow β ℕ] [SMul ℕ β]
    [NatCast β] [Max β] [Bot β] (f : β → α) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) (sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (bot : f ⊥ = ⊥) :
    IdemSemiring β :=
  { hf.semiring f zero one add mul nsmul npow natCast, hf.semilatticeSup _ sup,
    ‹Bot β› with
    add_eq_sup := fun a b ↦ hf <| by rw [sup, add, add_eq_sup]
    bot := ⊥
    bot_le := fun a ↦ bot.trans_le <| @bot_le _ _ _ <| f a }

-- See note [reducible non-instances]
/-- Pullback an `IdemCommSemiring` instance along an injective function. -/
protected abbrev idemCommSemiring [IdemCommSemiring α] [Zero β] [One β] [Add β] [Mul β] [Pow β ℕ]
    [SMul ℕ β] [NatCast β] [Max β] [Bot β] (f : β → α) (hf : Injective f) (zero : f 0 = 0)
    (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) (sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (bot : f ⊥ = ⊥) :
    IdemCommSemiring β :=
  { hf.commSemiring f zero one add mul nsmul npow natCast,
    hf.idemSemiring f zero one add mul nsmul npow natCast sup bot with }

-- See note [reducible non-instances]
/-- Pullback a `KleeneAlgebra` instance along an injective function. -/
protected abbrev kleeneAlgebra [KleeneAlgebra α] [Zero β] [One β] [Add β] [Mul β] [Pow β ℕ]
    [SMul ℕ β] [NatCast β] [Max β] [Bot β] [KStar β] (f : β → α) (hf : Injective f) (zero : f 0 = 0)
    (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) (sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (bot : f ⊥ = ⊥)
    (kstar : ∀ a, f a∗ = (f a)∗) : KleeneAlgebra β :=
  { hf.idemSemiring f zero one add mul nsmul npow natCast sup bot,
    ‹KStar β› with
    one_le_kstar := fun a ↦ one.trans_le <| by
      rw [kstar]
      exact one_le_kstar
    mul_kstar_le_kstar := fun a ↦ by
      change f _ ≤ _
      rw [mul, kstar]
      exact mul_kstar_le_kstar
    kstar_mul_le_kstar := fun a ↦ by
      change f _ ≤ _
      rw [mul, kstar]
      exact kstar_mul_le_kstar
    mul_kstar_le_self := fun a b (h : f _ ≤ _) ↦ by
      change f _ ≤ _
      rw [mul, kstar]
      rw [mul] at h
      exact mul_kstar_le_self h
    kstar_mul_le_self := fun a b (h : f _ ≤ _) ↦ by
      change f _ ≤ _
      rw [mul, kstar]
      rw [mul] at h
      exact kstar_mul_le_self h }

end Function.Injective
