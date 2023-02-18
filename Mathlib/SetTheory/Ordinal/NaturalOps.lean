/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios

! This file was ported from Lean 3 source module set_theory.ordinal.natural_ops
! leanprover-community/mathlib commit 740acc0e6f9adf4423f92a485d0456fc271482da
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.SetTheory.Ordinal.Arithmetic

/-!
# Natural operations on ordinals

The goal of this file is to define natural addition and multiplication on ordinals, also known as
the Hessenberg sum and product, and provide a basic API. The natural addition of two ordinals
`a ♯ b` is recursively defined as the least ordinal greater than `a' ♯ b` and `a ♯ b'` for `a' < a`
and `b' < b`. The natural multiplication `a ⨳ b` is likewise recursively defined as the least
ordinal such that `a ⨳ b ♯ a' ⨳ b'` is greater than `a' ⨳ b ♯ a ⨳ b'` for any `a' < a` and
`b' < b`.

These operations form a rich algebraic structure: they're commutative, associative, preserve order,
have the usual `0` and `1` from ordinals, and distribute over one another.

Moreover, these operations are the addition and multiplication of ordinals when viewed as
combinatorial `game`s. This makes them particularly useful for game theory.

Finally, both operations admit simple, intuitive descriptions in terms of the Cantor normal form.
The natural addition of two ordinals corresponds to adding their Cantor normal forms as if they were
polynomials in `ω`. Likewise, their natural multiplication corresponds to multiplying the Cantor
normal forms as polynomials.

# Implementation notes

Given the rich algebraic structure of these two operations, we choose to create a type synonym
`nat_ordinal`, where we provide the appropriate instances. However, to avoid casting back and forth
between both types, we attempt to prove and state most results on `ordinal`.

# Todo

- Define natural multiplication and provide a basic API.
- Prove the characterizations of natural addition and multiplication in terms of the Cantor normal
  form.
-/


universe u v

open Function Order

noncomputable section

/-- A type synonym for ordinals with natural addition and multiplication. -/
def NatOrdinal : Type _ :=
  Ordinal deriving Zero, Inhabited, One, LinearOrder, SuccOrder, WellFoundedRelation
#align nat_ordinal NatOrdinal

/-- The identity function between `ordinal` and `nat_ordinal`. -/
@[match_pattern]
def Ordinal.toNatOrdinal : Ordinal ≃o NatOrdinal :=
  OrderIso.refl _
#align ordinal.to_nat_ordinal Ordinal.toNatOrdinal

/-- The identity function between `nat_ordinal` and `ordinal`. -/
@[match_pattern]
def NatOrdinal.toOrdinal : NatOrdinal ≃o Ordinal :=
  OrderIso.refl _
#align nat_ordinal.to_ordinal NatOrdinal.toOrdinal

open Ordinal

namespace NatOrdinal

variable {a b c : NatOrdinal.{u}}

@[simp]
theorem toOrdinal_symm_eq : NatOrdinal.toOrdinal.symm = Ordinal.toNatOrdinal :=
  rfl
#align nat_ordinal.to_ordinal_symm_eq NatOrdinal.toOrdinal_symm_eq

@[simp]
theorem toOrdinal_toNatOrdinal (a : NatOrdinal) : a.toOrdinal.toNatOrdinal = a :=
  rfl
#align nat_ordinal.to_ordinal_to_nat_ordinal NatOrdinal.toOrdinal_toNatOrdinal

theorem lt_wf : @WellFounded NatOrdinal (· < ·) :=
  Ordinal.lt_wf
#align nat_ordinal.lt_wf NatOrdinal.lt_wf

instance : WellFoundedLT NatOrdinal :=
  Ordinal.wellFoundedLT

instance : IsWellOrder NatOrdinal (· < ·) :=
  Ordinal.HasLt.Lt.isWellOrder

@[simp]
theorem toOrdinal_zero : toOrdinal 0 = 0 :=
  rfl
#align nat_ordinal.to_ordinal_zero NatOrdinal.toOrdinal_zero

@[simp]
theorem toOrdinal_one : toOrdinal 1 = 1 :=
  rfl
#align nat_ordinal.to_ordinal_one NatOrdinal.toOrdinal_one

@[simp]
theorem toOrdinal_eq_zero (a) : toOrdinal a = 0 ↔ a = 0 :=
  Iff.rfl
#align nat_ordinal.to_ordinal_eq_zero NatOrdinal.toOrdinal_eq_zero

@[simp]
theorem toOrdinal_eq_one (a) : toOrdinal a = 1 ↔ a = 1 :=
  Iff.rfl
#align nat_ordinal.to_ordinal_eq_one NatOrdinal.toOrdinal_eq_one

@[simp]
theorem toOrdinal_max : (max a b).toOrdinal = max a.toOrdinal b.toOrdinal :=
  rfl
#align nat_ordinal.to_ordinal_max NatOrdinal.toOrdinal_max

@[simp]
theorem toOrdinal_min : (min a b).toOrdinal = min a.toOrdinal b.toOrdinal :=
  rfl
#align nat_ordinal.to_ordinal_min NatOrdinal.toOrdinal_min

theorem succ_def (a : NatOrdinal) : succ a = (a.toOrdinal + 1).toNatOrdinal :=
  rfl
#align nat_ordinal.succ_def NatOrdinal.succ_def

/-- A recursor for `nat_ordinal`. Use as `induction x using nat_ordinal.rec`. -/
protected def rec {β : NatOrdinal → Sort _} (h : ∀ a, β (toNatOrdinal a)) : ∀ a, β a := fun a =>
  h a.toOrdinal
#align nat_ordinal.rec NatOrdinal.rec

/-- `ordinal.induction` but for `nat_ordinal`. -/
theorem induction {p : NatOrdinal → Prop} : ∀ (i) (h : ∀ j, (∀ k, k < j → p k) → p j), p i :=
  Ordinal.induction
#align nat_ordinal.induction NatOrdinal.induction

end NatOrdinal

namespace Ordinal

variable {a b c : Ordinal.{u}}

@[simp]
theorem toNatOrdinal_symm_eq : toNatOrdinal.symm = NatOrdinal.toOrdinal :=
  rfl
#align ordinal.to_nat_ordinal_symm_eq Ordinal.toNatOrdinal_symm_eq

@[simp]
theorem toNatOrdinal_toOrdinal (a : Ordinal) : a.toNatOrdinal.toOrdinal = a :=
  rfl
#align ordinal.to_nat_ordinal_to_ordinal Ordinal.toNatOrdinal_toOrdinal

@[simp]
theorem toNatOrdinal_zero : toNatOrdinal 0 = 0 :=
  rfl
#align ordinal.to_nat_ordinal_zero Ordinal.toNatOrdinal_zero

@[simp]
theorem toNatOrdinal_one : toNatOrdinal 1 = 1 :=
  rfl
#align ordinal.to_nat_ordinal_one Ordinal.toNatOrdinal_one

@[simp]
theorem toNatOrdinal_eq_zero (a) : toNatOrdinal a = 0 ↔ a = 0 :=
  Iff.rfl
#align ordinal.to_nat_ordinal_eq_zero Ordinal.toNatOrdinal_eq_zero

@[simp]
theorem toNatOrdinal_eq_one (a) : toNatOrdinal a = 1 ↔ a = 1 :=
  Iff.rfl
#align ordinal.to_nat_ordinal_eq_one Ordinal.toNatOrdinal_eq_one

@[simp]
theorem toNatOrdinal_max : toNatOrdinal (max a b) = max a.toNatOrdinal b.toNatOrdinal :=
  rfl
#align ordinal.to_nat_ordinal_max Ordinal.toNatOrdinal_max

@[simp]
theorem toNatOrdinal_min :
    (LinearOrder.min a b).toNatOrdinal = LinearOrder.min a.toNatOrdinal b.toNatOrdinal :=
  rfl
#align ordinal.to_nat_ordinal_min Ordinal.toNatOrdinal_min

/-- Natural addition on ordinals `a ♯ b`, also known as the Hessenberg sum, is recursively defined
as the least ordinal greater than `a' ♯ b` and `a ♯ b'` for all `a' < a` and `b' < b`. In contrast
to normal ordinal addition, it is commutative.

Natural addition can equivalently be characterized as the ordinal resulting from adding up
corresponding coefficients in the Cantor normal forms of `a` and `b`. -/
noncomputable def nadd : Ordinal → Ordinal → Ordinal
  | a, b =>
    max (blsub.{u, u} a fun a' h => nadd a' b) (blsub.{u, u} b fun b' h => nadd a b')decreasing_by
  solve_by_elim [PSigma.Lex.left, PSigma.Lex.right]
#align ordinal.nadd Ordinal.nadd

-- mathport name: ordinal.nadd
scoped[NaturalOps] infixl:65 " ♯ " => Ordinal.nadd

theorem nadd_def (a b : Ordinal) :
    a ♯ b = max (blsub.{u, u} a fun a' h => a' ♯ b) (blsub.{u, u} b fun b' h => a ♯ b') := by
  rw [nadd]
#align ordinal.nadd_def Ordinal.nadd_def

theorem lt_nadd_iff : a < b ♯ c ↔ (∃ b' < b, a ≤ b' ♯ c) ∨ ∃ c' < c, a ≤ b ♯ c' :=
  by
  rw [nadd_def]
  simp [lt_blsub_iff]
#align ordinal.lt_nadd_iff Ordinal.lt_nadd_iff

theorem nadd_le_iff : b ♯ c ≤ a ↔ (∀ b' < b, b' ♯ c < a) ∧ ∀ c' < c, b ♯ c' < a :=
  by
  rw [nadd_def]
  simp [blsub_le_iff]
#align ordinal.nadd_le_iff Ordinal.nadd_le_iff

theorem nadd_lt_nadd_left (h : b < c) (a) : a ♯ b < a ♯ c :=
  lt_nadd_iff.2 (Or.inr ⟨b, h, le_rfl⟩)
#align ordinal.nadd_lt_nadd_left Ordinal.nadd_lt_nadd_left

theorem nadd_lt_nadd_right (h : b < c) (a) : b ♯ a < c ♯ a :=
  lt_nadd_iff.2 (Or.inl ⟨b, h, le_rfl⟩)
#align ordinal.nadd_lt_nadd_right Ordinal.nadd_lt_nadd_right

theorem nadd_le_nadd_left (h : b ≤ c) (a) : a ♯ b ≤ a ♯ c :=
  by
  rcases lt_or_eq_of_le h with (h | rfl)
  · exact (nadd_lt_nadd_left h a).le
  · exact le_rfl
#align ordinal.nadd_le_nadd_left Ordinal.nadd_le_nadd_left

theorem nadd_le_nadd_right (h : b ≤ c) (a) : b ♯ a ≤ c ♯ a :=
  by
  rcases lt_or_eq_of_le h with (h | rfl)
  · exact (nadd_lt_nadd_right h a).le
  · exact le_rfl
#align ordinal.nadd_le_nadd_right Ordinal.nadd_le_nadd_right

variable (a b)

theorem nadd_comm : ∀ a b, a ♯ b = b ♯ a
  | a, b => by
    rw [nadd_def, nadd_def, max_comm]
    congr <;> ext (c hc) <;> apply nadd_comm decreasing_by
  solve_by_elim [PSigma.Lex.left, PSigma.Lex.right]
#align ordinal.nadd_comm Ordinal.nadd_comm

theorem blsub_nadd_of_mono {f : ∀ c < a ♯ b, Ordinal.{max u v}}
    (hf : ∀ {i j} (hi hj), i ≤ j → f i hi ≤ f j hj) :
    blsub _ f =
      max (blsub.{u, v} a fun a' ha' => f (a' ♯ b) <| nadd_lt_nadd_right ha' b)
        (blsub.{u, v} b fun b' hb' => f (a ♯ b') <| nadd_lt_nadd_left hb' a) :=
  by
  apply (blsub_le_iff.2 fun i h => _).antisymm (max_le _ _)
  · rcases lt_nadd_iff.1 h with (⟨a', ha', hi⟩ | ⟨b', hb', hi⟩)
    · exact lt_max_of_lt_left ((hf h (nadd_lt_nadd_right ha' b) hi).trans_lt (lt_blsub _ _ _))
    · exact lt_max_of_lt_right ((hf h (nadd_lt_nadd_left hb' a) hi).trans_lt (lt_blsub _ _ _))
  all_goals
    apply blsub_le_of_brange_subset.{u, u, v}
    rintro c ⟨d, hd, rfl⟩
    apply mem_brange_self
#align ordinal.blsub_nadd_of_mono Ordinal.blsub_nadd_of_mono

theorem nadd_assoc : ∀ a b c, a ♯ b ♯ c = a ♯ (b ♯ c)
  | a, b, c =>
    by
    rw [nadd_def a (b ♯ c), nadd_def, blsub_nadd_of_mono, blsub_nadd_of_mono, max_assoc]
    · congr <;> ext (d hd) <;> apply nadd_assoc
    · exact fun i j _ _ h => nadd_le_nadd_left h a
    · exact fun i j _ _ h => nadd_le_nadd_right h c decreasing_by
  solve_by_elim [PSigma.Lex.left, PSigma.Lex.right]
#align ordinal.nadd_assoc Ordinal.nadd_assoc

@[simp]
theorem nadd_zero : a ♯ 0 = a :=
  by
  induction' a using Ordinal.induction with a IH
  rw [nadd_def, blsub_zero, max_zero_right]
  convert blsub_id a
  ext (b hb)
  exact IH _ hb
#align ordinal.nadd_zero Ordinal.nadd_zero

@[simp]
theorem zero_nadd : 0 ♯ a = a := by rw [nadd_comm, nadd_zero]
#align ordinal.zero_nadd Ordinal.zero_nadd

@[simp]
theorem nadd_one : a ♯ 1 = succ a :=
  by
  induction' a using Ordinal.induction with a IH
  rw [nadd_def, blsub_one, nadd_zero, max_eq_right_iff, blsub_le_iff]
  intro i hi
  rwa [IH i hi, succ_lt_succ_iff]
#align ordinal.nadd_one Ordinal.nadd_one

@[simp]
theorem one_nadd : 1 ♯ a = succ a := by rw [nadd_comm, nadd_one]
#align ordinal.one_nadd Ordinal.one_nadd

theorem nadd_succ : a ♯ succ b = succ (a ♯ b) := by rw [← nadd_one (a ♯ b), nadd_assoc, nadd_one]
#align ordinal.nadd_succ Ordinal.nadd_succ

theorem succ_nadd : succ a ♯ b = succ (a ♯ b) := by rw [← one_nadd (a ♯ b), ← nadd_assoc, one_nadd]
#align ordinal.succ_nadd Ordinal.succ_nadd

@[simp]
theorem nadd_nat (n : ℕ) : a ♯ n = a + n :=
  by
  induction' n with n hn
  · simp
  · rw [Nat.cast_succ, add_one_eq_succ, nadd_succ, add_succ, hn]
#align ordinal.nadd_nat Ordinal.nadd_nat

@[simp]
theorem nat_nadd (n : ℕ) : ↑n ♯ a = a + n := by rw [nadd_comm, nadd_nat]
#align ordinal.nat_nadd Ordinal.nat_nadd

theorem add_le_nadd : a + b ≤ a ♯ b := by
  apply b.limit_rec_on
  · simp
  · intro c h
    rwa [add_succ, nadd_succ, succ_le_succ_iff]
  · intro c hc H
    rw [← IsNormal.blsub_eq.{u, u} (add_is_normal a) hc, blsub_le_iff]
    exact fun i hi => (H i hi).trans_lt (nadd_lt_nadd_left hi a)
#align ordinal.add_le_nadd Ordinal.add_le_nadd

end Ordinal

open Ordinal

namespace NatOrdinal

instance : Add NatOrdinal :=
  ⟨nadd⟩

instance add_covariantClass_lt : CovariantClass NatOrdinal.{u} NatOrdinal.{u} (· + ·) (· < ·) :=
  ⟨fun a b c h => nadd_lt_nadd_left h a⟩
#align nat_ordinal.add_covariant_class_lt NatOrdinal.add_covariantClass_lt

instance add_covariantClass_le : CovariantClass NatOrdinal.{u} NatOrdinal.{u} (· + ·) (· ≤ ·) :=
  ⟨fun a b c h => nadd_le_nadd_left h a⟩
#align nat_ordinal.add_covariant_class_le NatOrdinal.add_covariantClass_le

instance add_contravariantClass_le :
    ContravariantClass NatOrdinal.{u} NatOrdinal.{u} (· + ·) (· ≤ ·) :=
  ⟨fun a b c h => by
    by_contra' h'
    exact h.not_lt (add_lt_add_left h' a)⟩
#align nat_ordinal.add_contravariant_class_le NatOrdinal.add_contravariantClass_le

instance : OrderedCancelAddCommMonoid NatOrdinal :=
  { NatOrdinal.linearOrder with
    add := (· + ·)
    add_assoc := nadd_assoc
    add_le_add_left := fun a b => add_le_add_left
    le_of_add_le_add_left := fun a b c => le_of_add_le_add_left
    zero := 0
    zero_add := zero_nadd
    add_zero := nadd_zero
    add_comm := nadd_comm }

instance : AddMonoidWithOne NatOrdinal :=
  AddMonoidWithOne.unary

@[simp]
theorem add_one_eq_succ : ∀ a : NatOrdinal, a + 1 = succ a :=
  nadd_one
#align nat_ordinal.add_one_eq_succ NatOrdinal.add_one_eq_succ

@[simp]
theorem toOrdinal_cast_nat (n : ℕ) : toOrdinal n = n :=
  by
  induction' n with n hn
  · rfl
  · change nadd (to_ordinal n) 1 = n + 1
    rw [hn]
    apply nadd_one
#align nat_ordinal.to_ordinal_cast_nat NatOrdinal.toOrdinal_cast_nat

end NatOrdinal

open NatOrdinal

open NaturalOps

namespace Ordinal

@[simp]
theorem toNatOrdinal_cast_nat (n : ℕ) : toNatOrdinal n = n :=
  by
  rw [← to_ordinal_cast_nat n]
  rfl
#align ordinal.to_nat_ordinal_cast_nat Ordinal.toNatOrdinal_cast_nat

theorem lt_of_nadd_lt_nadd_left : ∀ {a b c}, a ♯ b < a ♯ c → b < c :=
  @lt_of_add_lt_add_left NatOrdinal _ _ _
#align ordinal.lt_of_nadd_lt_nadd_left Ordinal.lt_of_nadd_lt_nadd_left

theorem lt_of_nadd_lt_nadd_right : ∀ {a b c}, b ♯ a < c ♯ a → b < c :=
  @lt_of_add_lt_add_right NatOrdinal _ _ _
#align ordinal.lt_of_nadd_lt_nadd_right Ordinal.lt_of_nadd_lt_nadd_right

theorem le_of_nadd_le_nadd_left : ∀ {a b c}, a ♯ b ≤ a ♯ c → b ≤ c :=
  @le_of_add_le_add_left NatOrdinal _ _ _
#align ordinal.le_of_nadd_le_nadd_left Ordinal.le_of_nadd_le_nadd_left

theorem le_of_nadd_le_nadd_right : ∀ {a b c}, b ♯ a ≤ c ♯ a → b ≤ c :=
  @le_of_add_le_add_right NatOrdinal _ _ _
#align ordinal.le_of_nadd_le_nadd_right Ordinal.le_of_nadd_le_nadd_right

theorem nadd_lt_nadd_iff_left : ∀ (a) {b c}, a ♯ b < a ♯ c ↔ b < c :=
  @add_lt_add_iff_left NatOrdinal _ _ _ _
#align ordinal.nadd_lt_nadd_iff_left Ordinal.nadd_lt_nadd_iff_left

theorem nadd_lt_nadd_iff_right : ∀ (a) {b c}, b ♯ a < c ♯ a ↔ b < c :=
  @add_lt_add_iff_right NatOrdinal _ _ _ _
#align ordinal.nadd_lt_nadd_iff_right Ordinal.nadd_lt_nadd_iff_right

theorem nadd_le_nadd_iff_left : ∀ (a) {b c}, a ♯ b ≤ a ♯ c ↔ b ≤ c :=
  @add_le_add_iff_left NatOrdinal _ _ _ _
#align ordinal.nadd_le_nadd_iff_left Ordinal.nadd_le_nadd_iff_left

theorem nadd_le_nadd_iff_right : ∀ (a) {b c}, b ♯ a ≤ c ♯ a ↔ b ≤ c :=
  @add_le_add_iff_right NatOrdinal _ _ _ _
#align ordinal.nadd_le_nadd_iff_right Ordinal.nadd_le_nadd_iff_right

theorem nadd_left_cancel : ∀ {a b c}, a ♯ b = a ♯ c → b = c :=
  @add_left_cancel NatOrdinal _ _
#align ordinal.nadd_left_cancel Ordinal.nadd_left_cancel

theorem nadd_right_cancel : ∀ {a b c}, a ♯ b = c ♯ b → a = c :=
  @add_right_cancel NatOrdinal _ _
#align ordinal.nadd_right_cancel Ordinal.nadd_right_cancel

theorem nadd_left_cancel_iff : ∀ {a b c}, a ♯ b = a ♯ c ↔ b = c :=
  @add_left_cancel_iff NatOrdinal _ _
#align ordinal.nadd_left_cancel_iff Ordinal.nadd_left_cancel_iff

theorem nadd_right_cancel_iff : ∀ {a b c}, b ♯ a = c ♯ a ↔ b = c :=
  @add_right_cancel_iff NatOrdinal _ _
#align ordinal.nadd_right_cancel_iff Ordinal.nadd_right_cancel_iff

end Ordinal

