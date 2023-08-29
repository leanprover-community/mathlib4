/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Tactic.Abel

#align_import set_theory.ordinal.natural_ops from "leanprover-community/mathlib"@"31b269b60935483943542d547a6dd83a66b37dc7"

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
combinatorial `Game`s. This makes them particularly useful for game theory.

Finally, both operations admit simple, intuitive descriptions in terms of the Cantor normal form.
The natural addition of two ordinals corresponds to adding their Cantor normal forms as if they were
polynomials in `ω`. Likewise, their natural multiplication corresponds to multiplying the Cantor
normal forms as polynomials.

# Implementation notes

Given the rich algebraic structure of these two operations, we choose to create a type synonym
`NatOrdinal`, where we provide the appropriate instances. However, to avoid casting back and forth
between both types, we attempt to prove and state most results on `Ordinal`.

# Todo

- Prove the characterizations of natural addition and multiplication in terms of the Cantor normal
  form.
-/

set_option autoImplicit true


universe u v

open Function Order

noncomputable section

/-! ### Basic casts between `ordinal` and `nat_ordinal` -/

/-- A type synonym for ordinals with natural addition and multiplication. -/
def NatOrdinal : Type _ :=
  -- porting note: used to derive LinearOrder & SuccOrder but need to manually define
  Ordinal deriving Zero, Inhabited, One, WellFoundedRelation
#align nat_ordinal NatOrdinal

instance NatOrdinal.linearOrder: LinearOrder NatOrdinal := {Ordinal.linearOrder with}

instance NatOrdinal.succOrder: SuccOrder NatOrdinal := {Ordinal.succOrder with}

/-- The identity function between `Ordinal` and `NatOrdinal`. -/
@[match_pattern]
def Ordinal.toNatOrdinal : Ordinal ≃o NatOrdinal :=
  OrderIso.refl _
#align ordinal.to_nat_ordinal Ordinal.toNatOrdinal

/-- The identity function between `NatOrdinal` and `Ordinal`. -/
@[match_pattern]
def NatOrdinal.toOrdinal : NatOrdinal ≃o Ordinal :=
  OrderIso.refl _
#align nat_ordinal.to_ordinal NatOrdinal.toOrdinal

namespace NatOrdinal

open Ordinal

@[simp]
theorem toOrdinal_symm_eq : NatOrdinal.toOrdinal.symm = Ordinal.toNatOrdinal :=
  rfl
#align nat_ordinal.to_ordinal_symm_eq NatOrdinal.toOrdinal_symm_eq

-- porting note: used to use dot notation, but doesn't work in Lean 4 with `OrderIso`
@[simp]
theorem toOrdinal_toNatOrdinal (a : NatOrdinal) : Ordinal.toNatOrdinal (NatOrdinal.toOrdinal a) = a
 := rfl
#align nat_ordinal.to_ordinal_to_nat_ordinal NatOrdinal.toOrdinal_toNatOrdinal

theorem lt_wf : @WellFounded NatOrdinal (· < ·) :=
  Ordinal.lt_wf
#align nat_ordinal.lt_wf NatOrdinal.lt_wf

instance : WellFoundedLT NatOrdinal :=
  Ordinal.wellFoundedLT

instance : IsWellOrder NatOrdinal (· < ·) :=
  Ordinal.isWellOrder

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
theorem toOrdinal_max : toOrdinal (max a b) = max (toOrdinal a) (toOrdinal b) :=
  rfl
#align nat_ordinal.to_ordinal_max NatOrdinal.toOrdinal_max

@[simp]
theorem toOrdinal_min : toOrdinal (min a b)= min (toOrdinal a) (toOrdinal b) :=
  rfl
#align nat_ordinal.to_ordinal_min NatOrdinal.toOrdinal_min

theorem succ_def (a : NatOrdinal) : succ a = toNatOrdinal (toOrdinal a + 1) :=
  rfl
#align nat_ordinal.succ_def NatOrdinal.succ_def

/-- A recursor for `NatOrdinal`. Use as `induction x using NatOrdinal.rec`. -/
protected def rec {β : NatOrdinal → Sort*} (h : ∀ a, β (toNatOrdinal a)) : ∀ a, β a := fun a =>
  h (toOrdinal a)
#align nat_ordinal.rec NatOrdinal.rec

/-- `Ordinal.induction` but for `NatOrdinal`. -/
theorem induction {p : NatOrdinal → Prop} : ∀ (i) (_ : ∀ j, (∀ k, k < j → p k) → p j), p i :=
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
theorem toNatOrdinal_toOrdinal (a : Ordinal) :  NatOrdinal.toOrdinal (toNatOrdinal a) = a :=
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
theorem toNatOrdinal_max (a b : Ordinal) :
    toNatOrdinal (max a b) = max (toNatOrdinal a) (toNatOrdinal b) :=
  rfl
#align ordinal.to_nat_ordinal_max Ordinal.toNatOrdinal_max

@[simp]
theorem toNatOrdinal_min (a b : Ordinal) :
    toNatOrdinal (linearOrder.min a b) = linearOrder.min (toNatOrdinal a) (toNatOrdinal b) :=
  rfl
#align ordinal.to_nat_ordinal_min Ordinal.toNatOrdinal_min

/-! We place the definitions of `nadd` and `nmul` before actually developing their API, as this
guarantees we only need to open the `NaturalOps` locale once. -/

/-- Natural addition on ordinals `a ♯ b`, also known as the Hessenberg sum, is recursively defined
as the least ordinal greater than `a' ♯ b` and `a ♯ b'` for all `a' < a` and `b' < b`. In contrast
to normal ordinal addition, it is commutative.

Natural addition can equivalently be characterized as the ordinal resulting from adding up
corresponding coefficients in the Cantor normal forms of `a` and `b`. -/
noncomputable def nadd : Ordinal → Ordinal → Ordinal
  | a, b =>
    max (blsub.{u, u} a fun a' _ => nadd a' b) (blsub.{u, u} b fun b' _ => nadd a b')
  termination_by nadd o₁ o₂ => (o₁, o₂)
#align ordinal.nadd Ordinal.nadd

@[inherit_doc]
scoped[NaturalOps] infixl:65 " ♯ " => Ordinal.nadd

open NaturalOps

/-- Natural multiplication on ordinals `a ⨳ b`, also known as the Hessenberg product, is recursively
defined as the least ordinal such that `a ⨳ b + a' ⨳ b'` is greater than `a' ⨳ b + a ⨳ b'` for all
`a' < a` and `b < b'`. In contrast to normal ordinal multiplication, it is commutative and
distributive (over natural addition).

Natural multiplication can equivalently be characterized as the ordinal resulting from multiplying
the Cantor normal forms of `a` and `b` as if they were polynomials in `ω`. Addition of exponents is
done via natural addition. -/
noncomputable def nmul : Ordinal.{u} → Ordinal.{u} → Ordinal.{u}
  | a, b => sInf {c | ∀ a' < a, ∀ b' < b, nmul a' b ♯ nmul a b' < c ♯ nmul a' b'}
termination_by nmul a b => (a, b)
#align ordinal.nmul Ordinal.nmul

@[inherit_doc]
scoped[NaturalOps] infixl:70 " ⨳ " => Ordinal.nmul

/-! ### Natural addition -/

theorem nadd_def (a b : Ordinal) :
    a ♯ b = max (blsub.{u, u} a fun a' _ => a' ♯ b) (blsub.{u, u} b fun b' _ => a ♯ b') := by
  rw [nadd]
  -- 🎉 no goals
#align ordinal.nadd_def Ordinal.nadd_def

theorem lt_nadd_iff : a < b ♯ c ↔ (∃ b' < b, a ≤ b' ♯ c) ∨ ∃ c' < c, a ≤ b ♯ c' := by
  rw [nadd_def]
  -- ⊢ a < max (blsub b fun a' x => a' ♯ c) (blsub c fun b' x => b ♯ b') ↔ (∃ b', b …
  simp [lt_blsub_iff]
  -- 🎉 no goals
#align ordinal.lt_nadd_iff Ordinal.lt_nadd_iff

theorem nadd_le_iff : b ♯ c ≤ a ↔ (∀ b' < b, b' ♯ c < a) ∧ ∀ c' < c, b ♯ c' < a := by
  rw [nadd_def]
  -- ⊢ max (blsub b fun a' x => a' ♯ c) (blsub c fun b' x => b ♯ b') ≤ a ↔ (∀ (b' : …
  simp [blsub_le_iff]
  -- 🎉 no goals
#align ordinal.nadd_le_iff Ordinal.nadd_le_iff

theorem nadd_lt_nadd_left (h : b < c) (a) : a ♯ b < a ♯ c :=
  lt_nadd_iff.2 (Or.inr ⟨b, h, le_rfl⟩)
#align ordinal.nadd_lt_nadd_left Ordinal.nadd_lt_nadd_left

theorem nadd_lt_nadd_right (h : b < c) (a) : b ♯ a < c ♯ a :=
  lt_nadd_iff.2 (Or.inl ⟨b, h, le_rfl⟩)
#align ordinal.nadd_lt_nadd_right Ordinal.nadd_lt_nadd_right

theorem nadd_le_nadd_left (h : b ≤ c) (a) : a ♯ b ≤ a ♯ c := by
  rcases lt_or_eq_of_le h with (h | rfl)
  -- ⊢ a ♯ b ≤ a ♯ c
  · exact (nadd_lt_nadd_left h a).le
    -- 🎉 no goals
  · exact le_rfl
    -- 🎉 no goals
#align ordinal.nadd_le_nadd_left Ordinal.nadd_le_nadd_left

theorem nadd_le_nadd_right (h : b ≤ c) (a) : b ♯ a ≤ c ♯ a := by
  rcases lt_or_eq_of_le h with (h | rfl)
  -- ⊢ b ♯ a ≤ c ♯ a
  · exact (nadd_lt_nadd_right h a).le
    -- 🎉 no goals
  · exact le_rfl
    -- 🎉 no goals
#align ordinal.nadd_le_nadd_right Ordinal.nadd_le_nadd_right

variable (a b)

theorem nadd_comm : ∀ a b, a ♯ b = b ♯ a
  | a, b => by
    rw [nadd_def, nadd_def, max_comm]
    -- ⊢ max (blsub b fun b' x => a ♯ b') (blsub a fun a' x => a' ♯ b) = max (blsub b …
    congr <;> ext <;> apply nadd_comm
    -- ⊢ (fun b' x => a ♯ b') = fun a' x => a' ♯ a
              -- ⊢ a ♯ x✝¹ = x✝¹ ♯ a
              -- ⊢ x✝¹ ♯ b = b ♯ x✝¹
                      -- 🎉 no goals
                      -- 🎉 no goals
    -- porting note: below was decreasing_by solve_by_elim [PSigma.Lex.left, PSigma.Lex.right]
  termination_by nadd_comm a b => (a,b)
#align ordinal.nadd_comm Ordinal.nadd_comm

theorem blsub_nadd_of_mono {f : ∀ c < a ♯ b, Ordinal.{max u v}}
    (hf : ∀ {i j} (hi hj), i ≤ j → f i hi ≤ f j hj) :
    -- Porting note: needed to add universe hint blsub.{u,v} in the line below
    blsub.{u,v} _ f =
      max (blsub.{u, v} a fun a' ha' => f (a' ♯ b) <| nadd_lt_nadd_right ha' b)
        (blsub.{u, v} b fun b' hb' => f (a ♯ b') <| nadd_lt_nadd_left hb' a) := by
  apply (blsub_le_iff.2 fun i h => _).antisymm (max_le _ _)
  intro i h
  · rcases lt_nadd_iff.1 h with (⟨a', ha', hi⟩ | ⟨b', hb', hi⟩)
    -- ⊢ f i h < max (blsub a fun a' ha' => f (a' ♯ b) (_ : a' ♯ b < a ♯ b)) (blsub b …
    · exact lt_max_of_lt_left ((hf h (nadd_lt_nadd_right ha' b) hi).trans_lt (lt_blsub _ _ ha'))
      -- 🎉 no goals
    · exact lt_max_of_lt_right ((hf h (nadd_lt_nadd_left hb' a) hi).trans_lt (lt_blsub _ _ hb'))
      -- 🎉 no goals
  all_goals
    apply blsub_le_of_brange_subset.{u, u, v}
    rintro c ⟨d, hd, rfl⟩
    apply mem_brange_self
#align ordinal.blsub_nadd_of_mono Ordinal.blsub_nadd_of_mono

theorem nadd_assoc (a b c) : a ♯ b ♯ c = a ♯ (b ♯ c) := by
  rw [nadd_def a (b ♯ c), nadd_def, blsub_nadd_of_mono, blsub_nadd_of_mono, max_assoc]
  · congr <;> ext (d hd) <;> apply nadd_assoc
              -- ⊢ d ♯ b ♯ c = d ♯ (b ♯ c)
              -- ⊢ a ♯ d ♯ c = a ♯ (d ♯ c)
              -- ⊢ a ♯ b ♯ d = a ♯ (b ♯ d)
                             -- 🎉 no goals
                             -- 🎉 no goals
                             -- 🎉 no goals
  · exact fun _ _ h => nadd_le_nadd_left h a
    -- 🎉 no goals
  · exact fun _ _ h => nadd_le_nadd_right h c
    -- 🎉 no goals
termination_by _ => (a, b, c)
-- Porting note: above lines replaces
-- decreasing_by solve_by_elim [PSigma.Lex.left, PSigma.Lex.right]
#align ordinal.nadd_assoc Ordinal.nadd_assoc

@[simp]
theorem nadd_zero : a ♯ 0 = a := by
  induction' a using Ordinal.induction with a IH
  -- ⊢ a ♯ 0 = a
  rw [nadd_def, blsub_zero, max_zero_right]
  -- ⊢ (blsub a fun a' x => a' ♯ 0) = a
  convert blsub_id a
  -- ⊢ x✝¹ ♯ 0 = x✝¹
  rename_i hb
  -- ⊢ x✝ ♯ 0 = x✝
  exact IH _ hb
  -- 🎉 no goals
#align ordinal.nadd_zero Ordinal.nadd_zero

@[simp]
theorem zero_nadd : 0 ♯ a = a := by rw [nadd_comm, nadd_zero]
                                    -- 🎉 no goals
#align ordinal.zero_nadd Ordinal.zero_nadd

@[simp]
theorem nadd_one : a ♯ 1 = succ a := by
  induction' a using Ordinal.induction with a IH
  -- ⊢ a ♯ 1 = succ a
  rw [nadd_def, blsub_one, nadd_zero, max_eq_right_iff, blsub_le_iff]
  -- ⊢ ∀ (i : Ordinal.{u}), i < a → i ♯ 1 < succ a
  intro i hi
  -- ⊢ i ♯ 1 < succ a
  rwa [IH i hi, succ_lt_succ_iff]
  -- 🎉 no goals
#align ordinal.nadd_one Ordinal.nadd_one

@[simp]
theorem one_nadd : 1 ♯ a = succ a := by rw [nadd_comm, nadd_one]
                                        -- 🎉 no goals
#align ordinal.one_nadd Ordinal.one_nadd

theorem nadd_succ : a ♯ succ b = succ (a ♯ b) := by rw [← nadd_one (a ♯ b), nadd_assoc, nadd_one]
                                                    -- 🎉 no goals
#align ordinal.nadd_succ Ordinal.nadd_succ

theorem succ_nadd : succ a ♯ b = succ (a ♯ b) := by rw [← one_nadd (a ♯ b), ← nadd_assoc, one_nadd]
                                                    -- 🎉 no goals
#align ordinal.succ_nadd Ordinal.succ_nadd

@[simp]
theorem nadd_nat (n : ℕ) : a ♯ n = a + n := by
  induction' n with n hn
  -- ⊢ a ♯ ↑Nat.zero = a + ↑Nat.zero
  · simp
    -- 🎉 no goals
  · rw [Nat.cast_succ, add_one_eq_succ, nadd_succ, add_succ, hn]
    -- 🎉 no goals
#align ordinal.nadd_nat Ordinal.nadd_nat

@[simp]
theorem nat_nadd (n : ℕ) : ↑n ♯ a = a + n := by rw [nadd_comm, nadd_nat]
                                                -- 🎉 no goals
#align ordinal.nat_nadd Ordinal.nat_nadd

theorem add_le_nadd : a + b ≤ a ♯ b := by
  induction b using limitRecOn with
  | H₁ => simp
  | H₂ c h =>
    rwa [add_succ, nadd_succ, succ_le_succ_iff]
  | H₃ c hc H =>
    simp_rw [← IsNormal.blsub_eq.{u, u} (add_isNormal a) hc, blsub_le_iff]
    exact fun i hi => (H i hi).trans_lt (nadd_lt_nadd_left hi a)
#align ordinal.add_le_nadd Ordinal.add_le_nadd

end Ordinal

namespace NatOrdinal

open Ordinal NaturalOps

instance : Add NatOrdinal :=
  ⟨nadd⟩

instance add_covariantClass_lt : CovariantClass NatOrdinal.{u} NatOrdinal.{u} (· + ·) (· < ·) :=
  ⟨fun a _ _ h => nadd_lt_nadd_left h a⟩
#align nat_ordinal.add_covariant_class_lt NatOrdinal.add_covariantClass_lt

instance add_covariantClass_le : CovariantClass NatOrdinal.{u} NatOrdinal.{u} (· + ·) (· ≤ ·) :=
  ⟨fun a _ _ h => nadd_le_nadd_left h a⟩
#align nat_ordinal.add_covariant_class_le NatOrdinal.add_covariantClass_le

instance add_contravariantClass_le :
    ContravariantClass NatOrdinal.{u} NatOrdinal.{u} (· + ·) (· ≤ ·) :=
  ⟨fun a b c h => by
    by_contra' h'
    -- ⊢ False
    exact h.not_lt (add_lt_add_left h' a)⟩
    -- 🎉 no goals
#align nat_ordinal.add_contravariant_class_le NatOrdinal.add_contravariantClass_le

instance orderedCancelAddCommMonoid : OrderedCancelAddCommMonoid NatOrdinal :=
  { NatOrdinal.linearOrder with
    add := (· + ·)
    add_assoc := nadd_assoc
    add_le_add_left := fun a b => add_le_add_left
    le_of_add_le_add_left := fun a b c => le_of_add_le_add_left
    zero := 0
    zero_add := zero_nadd
    add_zero := nadd_zero
    add_comm := nadd_comm }

instance addMonoidWithOne : AddMonoidWithOne NatOrdinal :=
  AddMonoidWithOne.unary

@[simp]
theorem add_one_eq_succ : ∀ a : NatOrdinal, a + 1 = succ a :=
  nadd_one
#align nat_ordinal.add_one_eq_succ NatOrdinal.add_one_eq_succ

@[simp]
theorem toOrdinal_cast_nat (n : ℕ) : toOrdinal n = n := by
  induction' n with n hn
  -- ⊢ ↑toOrdinal ↑Nat.zero = ↑Nat.zero
  · rfl
    -- 🎉 no goals
  · change (toOrdinal n) ♯ 1 = n + 1
    -- ⊢ ↑toOrdinal ↑n ♯ 1 = ↑n + 1
    rw [hn]; exact nadd_one n
    -- ⊢ ↑n ♯ 1 = ↑n + 1
             -- 🎉 no goals
#align nat_ordinal.to_ordinal_cast_nat NatOrdinal.toOrdinal_cast_nat

end NatOrdinal

open NatOrdinal

open NaturalOps

namespace Ordinal

theorem nadd_eq_add (a b : Ordinal) : a ♯ b = toOrdinal (toNatOrdinal a + toNatOrdinal b) :=
  rfl
#align ordinal.nadd_eq_add Ordinal.nadd_eq_add

@[simp]
theorem toNatOrdinal_cast_nat (n : ℕ) : toNatOrdinal n = n := by
  rw [← toOrdinal_cast_nat n]
  -- ⊢ ↑toNatOrdinal (↑toOrdinal ↑n) = ↑n
  rfl
  -- 🎉 no goals
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
  @_root_.add_le_add_iff_right NatOrdinal _ _ _ _
#align ordinal.nadd_le_nadd_iff_right Ordinal.nadd_le_nadd_iff_right

theorem nadd_le_nadd : ∀ {a b c d}, a ≤ b → c ≤ d → a ♯ c ≤ b ♯ d :=
  @add_le_add NatOrdinal _ _ _ _
#align ordinal.nadd_le_nadd Ordinal.nadd_le_nadd

theorem nadd_lt_nadd : ∀ {a b c d}, a < b → c < d → a ♯ c < b ♯ d :=
  @add_lt_add NatOrdinal _ _ _ _
#align ordinal.nadd_lt_nadd Ordinal.nadd_lt_nadd

theorem nadd_lt_nadd_of_lt_of_le : ∀ {a b c d}, a < b → c ≤ d → a ♯ c < b ♯ d :=
  @add_lt_add_of_lt_of_le NatOrdinal _ _ _ _
#align ordinal.nadd_lt_nadd_of_lt_of_le Ordinal.nadd_lt_nadd_of_lt_of_le

theorem nadd_lt_nadd_of_le_of_lt : ∀ {a b c d}, a ≤ b → c < d → a ♯ c < b ♯ d :=
  @add_lt_add_of_le_of_lt NatOrdinal _ _ _ _
#align ordinal.nadd_lt_nadd_of_le_of_lt Ordinal.nadd_lt_nadd_of_le_of_lt

theorem nadd_left_cancel : ∀ {a b c}, a ♯ b = a ♯ c → b = c :=
  @_root_.add_left_cancel NatOrdinal _ _
#align ordinal.nadd_left_cancel Ordinal.nadd_left_cancel

theorem nadd_right_cancel : ∀ {a b c}, a ♯ b = c ♯ b → a = c :=
  @_root_.add_right_cancel NatOrdinal _ _
#align ordinal.nadd_right_cancel Ordinal.nadd_right_cancel

theorem nadd_left_cancel_iff : ∀ {a b c}, a ♯ b = a ♯ c ↔ b = c :=
  @add_left_cancel_iff NatOrdinal _ _
#align ordinal.nadd_left_cancel_iff Ordinal.nadd_left_cancel_iff

theorem nadd_right_cancel_iff : ∀ {a b c}, b ♯ a = c ♯ a ↔ b = c :=
  @add_right_cancel_iff NatOrdinal _ _
#align ordinal.nadd_right_cancel_iff Ordinal.nadd_right_cancel_iff

theorem le_nadd_self {a b} : a ≤ b ♯ a := by simpa using nadd_le_nadd_right (Ordinal.zero_le b) a
                                             -- 🎉 no goals
#align ordinal.le_nadd_self Ordinal.le_nadd_self

theorem le_nadd_left {a b c} (h : a ≤ c) : a ≤ b ♯ c :=
  le_nadd_self.trans (nadd_le_nadd_left h b)
#align ordinal.le_nadd_left Ordinal.le_nadd_left

theorem le_self_nadd {a b} : a ≤ a ♯ b := by simpa using nadd_le_nadd_left (Ordinal.zero_le b) a
                                             -- 🎉 no goals
#align ordinal.le_self_nadd Ordinal.le_self_nadd

theorem le_nadd_right {a b c} (h : a ≤ b) : a ≤ b ♯ c :=
  le_self_nadd.trans (nadd_le_nadd_right h c)
#align ordinal.le_nadd_right Ordinal.le_nadd_right

theorem nadd_left_comm : ∀ a b c, a ♯ (b ♯ c) = b ♯ (a ♯ c) :=
  @add_left_comm NatOrdinal _
#align ordinal.nadd_left_comm Ordinal.nadd_left_comm

theorem nadd_right_comm : ∀ a b c, a ♯ b ♯ c = a ♯ c ♯ b :=
  @add_right_comm NatOrdinal _
#align ordinal.nadd_right_comm Ordinal.nadd_right_comm

/-! ### Natural multiplication -/

variable {a b c d : Ordinal.{u}}

theorem nmul_def (a b : Ordinal) :
    a ⨳ b = sInf {c | ∀ a' < a, ∀ b' < b, a' ⨳ b ♯ a ⨳ b' < c ♯ a' ⨳ b'} := by rw [nmul]
                                                                               -- 🎉 no goals
#align ordinal.nmul_def Ordinal.nmul_def

/-- The set in the definition of `nmul` is nonempty. -/
theorem nmul_nonempty (a b : Ordinal.{u}) :
    {c : Ordinal.{u} | ∀ a' < a, ∀ b' < b, a' ⨳ b ♯ a ⨳ b' < c ♯ a' ⨳ b'}.Nonempty :=
  ⟨_, fun _ ha _ hb => (lt_blsub₂.{u, u, u} _ ha hb).trans_le le_self_nadd⟩
#align ordinal.nmul_nonempty Ordinal.nmul_nonempty

theorem nmul_nadd_lt {a' b' : Ordinal} (ha : a' < a) (hb : b' < b) :
    a' ⨳ b ♯ a ⨳ b' < a ⨳ b ♯ a' ⨳ b' := by
  rw [nmul_def a b]
  -- ⊢ a' ⨳ b ♯ a ⨳ b' < sInf {c | ∀ (a' : Ordinal.{u}), a' < a → ∀ (b' : Ordinal.{ …
  exact csInf_mem (nmul_nonempty a b) a' ha b' hb
  -- 🎉 no goals
#align ordinal.nmul_nadd_lt Ordinal.nmul_nadd_lt

theorem nmul_nadd_le {a' b' : Ordinal} (ha : a' ≤ a) (hb : b' ≤ b) :
    a' ⨳ b ♯ a ⨳ b' ≤ a ⨳ b ♯ a' ⨳ b' := by
  rcases lt_or_eq_of_le ha with (ha | rfl)
  -- ⊢ a' ⨳ b ♯ a ⨳ b' ≤ a ⨳ b ♯ a' ⨳ b'
  · rcases lt_or_eq_of_le hb with (hb | rfl)
    -- ⊢ a' ⨳ b ♯ a ⨳ b' ≤ a ⨳ b ♯ a' ⨳ b'
    · exact (nmul_nadd_lt ha hb).le
      -- 🎉 no goals
    · rw [nadd_comm]
      -- 🎉 no goals
  · exact le_rfl
    -- 🎉 no goals
#align ordinal.nmul_nadd_le Ordinal.nmul_nadd_le

theorem lt_nmul_iff : c < a ⨳ b ↔ ∃ a' < a, ∃ b' < b, c ♯ a' ⨳ b' ≤ a' ⨳ b ♯ a ⨳ b' := by
  refine' ⟨fun h => _, _⟩
  -- ⊢ ∃ a', a' < a ∧ ∃ b', b' < b ∧ c ♯ a' ⨳ b' ≤ a' ⨳ b ♯ a ⨳ b'
  · rw [nmul] at h
    -- ⊢ ∃ a', a' < a ∧ ∃ b', b' < b ∧ c ♯ a' ⨳ b' ≤ a' ⨳ b ♯ a ⨳ b'
    simpa using not_mem_of_lt_csInf h ⟨0, fun _ _ => bot_le⟩
    -- 🎉 no goals
  · rintro ⟨a', ha, b', hb, h⟩
    -- ⊢ c < a ⨳ b
    have := h.trans_lt (nmul_nadd_lt ha hb)
    -- ⊢ c < a ⨳ b
    rwa [nadd_lt_nadd_iff_right] at this
    -- 🎉 no goals
#align ordinal.lt_nmul_iff Ordinal.lt_nmul_iff

theorem nmul_le_iff : a ⨳ b ≤ c ↔ ∀ a' < a, ∀ b' < b, a' ⨳ b ♯ a ⨳ b' < c ♯ a' ⨳ b' := by
  rw [← not_iff_not]; simp [lt_nmul_iff]
  -- ⊢ ¬a ⨳ b ≤ c ↔ ¬∀ (a' : Ordinal.{u}), a' < a → ∀ (b' : Ordinal.{u}), b' < b →  …
                      -- 🎉 no goals
#align ordinal.nmul_le_iff Ordinal.nmul_le_iff

theorem nmul_comm : ∀ a b, a ⨳ b = b ⨳ a
  | a, b => by
    rw [nmul, nmul]
    -- ⊢ sInf {c | ∀ (a' : Ordinal.{u_1}), a' < a → ∀ (b' : Ordinal.{u_1}), b' < b →  …
    congr; ext x; constructor <;> intro H c hc d hd
    -- ⊢ {c | ∀ (a' : Ordinal.{u_1}), a' < a → ∀ (b' : Ordinal.{u_1}), b' < b → a' ⨳  …
           -- ⊢ x ∈ {c | ∀ (a' : Ordinal.{u_1}), a' < a → ∀ (b' : Ordinal.{u_1}), b' < b → a …
                  -- ⊢ x ∈ {c | ∀ (a' : Ordinal.{u_1}), a' < a → ∀ (b' : Ordinal.{u_1}), b' < b → a …
                                  -- ⊢ c ⨳ a ♯ b ⨳ d < x ♯ c ⨳ d
                                  -- ⊢ c ⨳ b ♯ a ⨳ d < x ♯ c ⨳ d
    -- Porting note: had to add additional arguments to `nmul_comm` here
    -- for the termination checker.
    · rw [nadd_comm, ← nmul_comm d b, ← nmul_comm a c, ← nmul_comm d]
      -- ⊢ d ⨳ b ♯ a ⨳ c < x ♯ d ⨳ c
      exact H _ hd _ hc
      -- 🎉 no goals
    · rw [nadd_comm, nmul_comm a d, nmul_comm c, nmul_comm c]
      -- ⊢ d ⨳ a ♯ b ⨳ c < x ♯ d ⨳ c
      exact H _ hd _ hc
      -- 🎉 no goals
termination_by nmul_comm a b => (a, b)
#align ordinal.nmul_comm Ordinal.nmul_comm

@[simp]
theorem nmul_zero (a) : a ⨳ 0 = 0 := by
  rw [← Ordinal.le_zero, nmul_le_iff]
  -- ⊢ ∀ (a' : Ordinal.{u_1}), a' < a → ∀ (b' : Ordinal.{u_1}), b' < 0 → a' ⨳ 0 ♯ a …
  exact fun _ _ a ha => (Ordinal.not_lt_zero a ha).elim
  -- 🎉 no goals
#align ordinal.nmul_zero Ordinal.nmul_zero

@[simp]
theorem zero_nmul (a) : 0 ⨳ a = 0 := by rw [nmul_comm, nmul_zero]
                                        -- 🎉 no goals
#align ordinal.zero_nmul Ordinal.zero_nmul

@[simp]
theorem nmul_one (a : Ordinal) : a ⨳ 1 = a := by
  rw [nmul]
  -- ⊢ sInf {c | ∀ (a' : Ordinal.{u_1}), a' < a → ∀ (b' : Ordinal.{u_1}), b' < 1 →  …
  simp only [lt_one_iff_zero, forall_eq, nmul_zero, nadd_zero]
  -- ⊢ sInf {c | ∀ (a' : Ordinal.{u_1}), a' < a → a' ⨳ 1 < c} = a
  convert csInf_Ici (α := Ordinal)
  -- ⊢ {c | ∀ (a' : Ordinal.{u_1}), a' < a → a' ⨳ 1 < c} = Set.Ici a
  ext b
  -- ⊢ b ∈ {c | ∀ (a' : Ordinal.{u_1}), a' < a → a' ⨳ 1 < c} ↔ b ∈ Set.Ici a
  -- Porting note: added this `simp` line, as the result from `convert`
  -- is slightly different.
  simp only [Set.mem_setOf_eq, Set.mem_Ici]
  -- ⊢ (∀ (a' : Ordinal.{u_1}), a' < a → a' ⨳ 1 < b) ↔ a ≤ b
  refine' ⟨fun H => le_of_forall_lt fun c hc => _, fun ha c hc => _⟩
  -- ⊢ c < b
  -- Porting note: had to add arguments to `nmul_one` in the next two lines
  -- for the termination checker.
  · simpa only [nmul_one c] using H c hc
    -- 🎉 no goals
  · simpa only [nmul_one c] using hc.trans_le ha
    -- 🎉 no goals
termination_by nmul_one a => a
#align ordinal.nmul_one Ordinal.nmul_one

@[simp]
theorem one_nmul (a) : 1 ⨳ a = a := by rw [nmul_comm, nmul_one]
                                       -- 🎉 no goals
#align ordinal.one_nmul Ordinal.one_nmul

theorem nmul_lt_nmul_of_pos_left (h₁ : a < b) (h₂ : 0 < c) : c ⨳ a < c ⨳ b :=
  lt_nmul_iff.2 ⟨0, h₂, a, h₁, by simp⟩
                                  -- 🎉 no goals
#align ordinal.nmul_lt_nmul_of_pos_left Ordinal.nmul_lt_nmul_of_pos_left

theorem nmul_lt_nmul_of_pos_right (h₁ : a < b) (h₂ : 0 < c) : a ⨳ c < b ⨳ c :=
  lt_nmul_iff.2 ⟨a, h₁, 0, h₂, by simp⟩
                                  -- 🎉 no goals
#align ordinal.nmul_lt_nmul_of_pos_right Ordinal.nmul_lt_nmul_of_pos_right

theorem nmul_le_nmul_of_nonneg_left (h₁ : a ≤ b) (h₂ : 0 ≤ c) : c ⨳ a ≤ c ⨳ b := by
  rcases lt_or_eq_of_le h₁ with (h₁ | rfl) <;> rcases lt_or_eq_of_le h₂ with (h₂ | rfl)
  -- ⊢ c ⨳ a ≤ c ⨳ b
                                               -- ⊢ c ⨳ a ≤ c ⨳ b
                                               -- ⊢ c ⨳ a ≤ c ⨳ a
  · exact (nmul_lt_nmul_of_pos_left h₁ h₂).le
    -- 🎉 no goals
  all_goals simp
  -- 🎉 no goals
#align ordinal.nmul_le_nmul_of_nonneg_left Ordinal.nmul_le_nmul_of_nonneg_left

theorem nmul_le_nmul_of_nonneg_right (h₁ : a ≤ b) (h₂ : 0 ≤ c) : a ⨳ c ≤ b ⨳ c := by
  rw [nmul_comm, nmul_comm b]
  -- ⊢ c ⨳ a ≤ c ⨳ b
  exact nmul_le_nmul_of_nonneg_left h₁ h₂
  -- 🎉 no goals
#align ordinal.nmul_le_nmul_of_nonneg_right Ordinal.nmul_le_nmul_of_nonneg_right

theorem nmul_nadd : ∀ a b c, a ⨳ (b ♯ c) = a ⨳ b ♯ a ⨳ c
  | a, b, c => by
    refine le_antisymm (nmul_le_iff.2 fun a' ha d hd => ?_)
      (nadd_le_iff.2 ⟨fun d hd => ?_, fun d hd => ?_⟩)
    · -- Porting note: adding arguments to `nmul_nadd` for the termination checker.
      rw [nmul_nadd a' b c]
      -- ⊢ a' ⨳ b ♯ a' ⨳ c ♯ a ⨳ d < a ⨳ b ♯ a ⨳ c ♯ a' ⨳ d
      rcases lt_nadd_iff.1 hd with (⟨b', hb, hd⟩ | ⟨c', hc, hd⟩)
      -- ⊢ a' ⨳ b ♯ a' ⨳ c ♯ a ⨳ d < a ⨳ b ♯ a ⨳ c ♯ a' ⨳ d
      · have := nadd_lt_nadd_of_lt_of_le (nmul_nadd_lt ha hb) (nmul_nadd_le ha.le hd)
        -- ⊢ a' ⨳ b ♯ a' ⨳ c ♯ a ⨳ d < a ⨳ b ♯ a ⨳ c ♯ a' ⨳ d
        -- Porting note: adding arguments to `nmul_nadd` for the termination checker.
        rw [nmul_nadd a' b' c, nmul_nadd a b' c] at this
        -- ⊢ a' ⨳ b ♯ a' ⨳ c ♯ a ⨳ d < a ⨳ b ♯ a ⨳ c ♯ a' ⨳ d
        simp only [nadd_assoc] at this
        -- ⊢ a' ⨳ b ♯ a' ⨳ c ♯ a ⨳ d < a ⨳ b ♯ a ⨳ c ♯ a' ⨳ d
        rwa [nadd_left_comm, nadd_left_comm _ (a ⨳ b'), nadd_left_comm (a ⨳ b),
          nadd_lt_nadd_iff_left, nadd_left_comm (a' ⨳ b), nadd_left_comm (a ⨳ b),
          nadd_lt_nadd_iff_left, ← nadd_assoc, ← nadd_assoc] at this
      · have := nadd_lt_nadd_of_le_of_lt (nmul_nadd_le ha.le hd) (nmul_nadd_lt ha hc)
        -- ⊢ a' ⨳ b ♯ a' ⨳ c ♯ a ⨳ d < a ⨳ b ♯ a ⨳ c ♯ a' ⨳ d
        -- Porting note: adding arguments to `nmul_nadd` for the termination checker.
        rw [nmul_nadd a' b c', nmul_nadd a b c'] at this
        -- ⊢ a' ⨳ b ♯ a' ⨳ c ♯ a ⨳ d < a ⨳ b ♯ a ⨳ c ♯ a' ⨳ d
        simp only [nadd_assoc] at this
        -- ⊢ a' ⨳ b ♯ a' ⨳ c ♯ a ⨳ d < a ⨳ b ♯ a ⨳ c ♯ a' ⨳ d
        rwa [nadd_left_comm, nadd_comm (a ⨳ c), nadd_left_comm (a' ⨳ d), nadd_left_comm (a ⨳ c'),
          nadd_left_comm (a ⨳ b), nadd_lt_nadd_iff_left, nadd_comm (a' ⨳ c), nadd_left_comm (a ⨳ d),
          nadd_left_comm (a' ⨳ b), nadd_left_comm (a ⨳ b), nadd_lt_nadd_iff_left, nadd_comm (a ⨳ d),
          nadd_comm (a' ⨳ d), ← nadd_assoc, ← nadd_assoc] at this
    · rcases lt_nmul_iff.1 hd with ⟨a', ha, b', hb, hd⟩
      -- ⊢ d ♯ a ⨳ c < a ⨳ (b ♯ c)
      have := nadd_lt_nadd_of_le_of_lt hd (nmul_nadd_lt ha (nadd_lt_nadd_right hb c))
      -- ⊢ d ♯ a ⨳ c < a ⨳ (b ♯ c)
      -- Porting note: adding arguments to `nmul_nadd` for the termination checker.
      rw [nmul_nadd a' b c, nmul_nadd a b' c, nmul_nadd a'] at this
      -- ⊢ d ♯ a ⨳ c < a ⨳ (b ♯ c)
      simp only [nadd_assoc] at this
      -- ⊢ d ♯ a ⨳ c < a ⨳ (b ♯ c)
      rwa [nadd_left_comm (a' ⨳ b'), nadd_left_comm, nadd_lt_nadd_iff_left, nadd_left_comm,
        nadd_left_comm _ (a' ⨳ b'), nadd_left_comm (a ⨳ b'), nadd_lt_nadd_iff_left,
        nadd_left_comm (a' ⨳ c), nadd_left_comm, nadd_lt_nadd_iff_left, nadd_left_comm,
        nadd_comm _ (a' ⨳ c), nadd_lt_nadd_iff_left] at this
    · rcases lt_nmul_iff.1 hd with ⟨a', ha, c', hc, hd⟩
      -- ⊢ a ⨳ b ♯ d < a ⨳ (b ♯ c)
      have := nadd_lt_nadd_of_lt_of_le (nmul_nadd_lt ha (nadd_lt_nadd_left hc b)) hd
      -- ⊢ a ⨳ b ♯ d < a ⨳ (b ♯ c)
      -- Porting note: adding arguments to `nmul_nadd` for the termination checker.
      rw [nmul_nadd a' b c, nmul_nadd a b c', nmul_nadd a'] at this
      -- ⊢ a ⨳ b ♯ d < a ⨳ (b ♯ c)
      simp only [nadd_assoc] at this
      -- ⊢ a ⨳ b ♯ d < a ⨳ (b ♯ c)
      rwa [nadd_left_comm _ (a' ⨳ b), nadd_lt_nadd_iff_left, nadd_left_comm (a' ⨳ c'),
        nadd_left_comm _ (a' ⨳ c), nadd_lt_nadd_iff_left, nadd_left_comm, nadd_comm (a' ⨳ c'),
        nadd_left_comm _ (a ⨳ c'), nadd_lt_nadd_iff_left, nadd_comm _ (a' ⨳ c'),
        nadd_comm _ (a' ⨳ c'), nadd_left_comm, nadd_lt_nadd_iff_left] at this
termination_by nmul_nadd a b c => (a, b, c)
#align ordinal.nmul_nadd Ordinal.nmul_nadd

theorem nadd_nmul (a b c) : (a ♯ b) ⨳ c = a ⨳ c ♯ b ⨳ c := by
  rw [nmul_comm, nmul_nadd, nmul_comm, nmul_comm c]
  -- 🎉 no goals
#align ordinal.nadd_nmul Ordinal.nadd_nmul

theorem nmul_nadd_lt₃ {a' b' c' : Ordinal} (ha : a' < a) (hb : b' < b) (hc : c' < c) :
    a' ⨳ b ⨳ c ♯ a ⨳ b' ⨳ c ♯ a ⨳ b ⨳ c' ♯ a' ⨳ b' ⨳ c' <
      a ⨳ b ⨳ c ♯ a' ⨳ b' ⨳ c ♯ a' ⨳ b ⨳ c' ♯ a ⨳ b' ⨳ c' := by
  simpa only [nadd_nmul, ← nadd_assoc] using nmul_nadd_lt (nmul_nadd_lt ha hb) hc
  -- 🎉 no goals
#align ordinal.nmul_nadd_lt₃ Ordinal.nmul_nadd_lt₃

theorem nmul_nadd_le₃ {a' b' c' : Ordinal} (ha : a' ≤ a) (hb : b' ≤ b) (hc : c' ≤ c) :
    a' ⨳ b ⨳ c ♯ a ⨳ b' ⨳ c ♯ a ⨳ b ⨳ c' ♯ a' ⨳ b' ⨳ c' ≤
      a ⨳ b ⨳ c ♯ a' ⨳ b' ⨳ c ♯ a' ⨳ b ⨳ c' ♯ a ⨳ b' ⨳ c' := by
  simpa only [nadd_nmul, ← nadd_assoc] using nmul_nadd_le (nmul_nadd_le ha hb) hc
  -- 🎉 no goals
#align ordinal.nmul_nadd_le₃ Ordinal.nmul_nadd_le₃

theorem nmul_nadd_lt₃' {a' b' c' : Ordinal} (ha : a' < a) (hb : b' < b) (hc : c' < c) :
    a' ⨳ (b ⨳ c) ♯ a ⨳ (b' ⨳ c) ♯ a ⨳ (b ⨳ c') ♯ a' ⨳ (b' ⨳ c') <
      a ⨳ (b ⨳ c) ♯ a' ⨳ (b' ⨳ c) ♯ a' ⨳ (b ⨳ c') ♯ a ⨳ (b' ⨳ c') := by
  simp only [nmul_comm _ (_ ⨳ _)]
  -- ⊢ b ⨳ c ⨳ a' ♯ b' ⨳ c ⨳ a ♯ b ⨳ c' ⨳ a ♯ b' ⨳ c' ⨳ a' < b ⨳ c ⨳ a ♯ b' ⨳ c ⨳ a …
  convert nmul_nadd_lt₃ hb hc ha using 1 <;>
  -- ⊢ b ⨳ c ⨳ a' ♯ b' ⨳ c ⨳ a ♯ b ⨳ c' ⨳ a ♯ b' ⨳ c' ⨳ a' = b' ⨳ c ⨳ a ♯ b ⨳ c' ⨳  …
    · simp only [nadd_eq_add, NatOrdinal.toOrdinal_toNatOrdinal]; abel_nf
      -- ⊢ ↑toOrdinal (↑toNatOrdinal (b ⨳ c ⨳ a') + ↑toNatOrdinal (b' ⨳ c ⨳ a) + ↑toNat …
                                                                  -- 🎉 no goals
      -- ⊢ ↑toOrdinal (↑toNatOrdinal (b ⨳ c ⨳ a) + ↑toNatOrdinal (b' ⨳ c ⨳ a') + ↑toNat …
                                                                  -- 🎉 no goals
#align ordinal.nmul_nadd_lt₃' Ordinal.nmul_nadd_lt₃'

theorem nmul_nadd_le₃' {a' b' c' : Ordinal} (ha : a' ≤ a) (hb : b' ≤ b) (hc : c' ≤ c) :
    a' ⨳ (b ⨳ c) ♯ a ⨳ (b' ⨳ c) ♯ a ⨳ (b ⨳ c') ♯ a' ⨳ (b' ⨳ c') ≤
      a ⨳ (b ⨳ c) ♯ a' ⨳ (b' ⨳ c) ♯ a' ⨳ (b ⨳ c') ♯ a ⨳ (b' ⨳ c') := by
  simp only [nmul_comm _ (_ ⨳ _)]
  -- ⊢ b ⨳ c ⨳ a' ♯ b' ⨳ c ⨳ a ♯ b ⨳ c' ⨳ a ♯ b' ⨳ c' ⨳ a' ≤ b ⨳ c ⨳ a ♯ b' ⨳ c ⨳ a …
  convert nmul_nadd_le₃ hb hc ha using 1 <;>
  -- ⊢ b ⨳ c ⨳ a' ♯ b' ⨳ c ⨳ a ♯ b ⨳ c' ⨳ a ♯ b' ⨳ c' ⨳ a' = b' ⨳ c ⨳ a ♯ b ⨳ c' ⨳  …
    · simp only [nadd_eq_add, NatOrdinal.toOrdinal_toNatOrdinal]; abel_nf
      -- ⊢ ↑toOrdinal (↑toNatOrdinal (b ⨳ c ⨳ a') + ↑toNatOrdinal (b' ⨳ c ⨳ a) + ↑toNat …
                                                                  -- 🎉 no goals
      -- ⊢ ↑toOrdinal (↑toNatOrdinal (b ⨳ c ⨳ a) + ↑toNatOrdinal (b' ⨳ c ⨳ a') + ↑toNat …
                                                                  -- 🎉 no goals
#align ordinal.nmul_nadd_le₃' Ordinal.nmul_nadd_le₃'

theorem lt_nmul_iff₃ :
    d < a ⨳ b ⨳ c ↔
      ∃ a' < a, ∃ b' < b, ∃ c' < c,
        d ♯ a' ⨳ b' ⨳ c ♯ a' ⨳ b ⨳ c' ♯ a ⨳ b' ⨳ c' ≤
          a' ⨳ b ⨳ c ♯ a ⨳ b' ⨳ c ♯ a ⨳ b ⨳ c' ♯ a' ⨳ b' ⨳ c' := by
  -- Porting note: was `refine' ⟨fun h => _, _⟩`, but can't get that to work?
  constructor
  -- ⊢ d < a ⨳ b ⨳ c → ∃ a', a' < a ∧ ∃ b', b' < b ∧ ∃ c', c' < c ∧ d ♯ a' ⨳ b' ⨳ c …
  · intro h
    -- ⊢ ∃ a', a' < a ∧ ∃ b', b' < b ∧ ∃ c', c' < c ∧ d ♯ a' ⨳ b' ⨳ c ♯ a' ⨳ b ⨳ c' ♯ …
    rcases lt_nmul_iff.1 h with ⟨e, he, c', hc, H₁⟩
    -- ⊢ ∃ a', a' < a ∧ ∃ b', b' < b ∧ ∃ c', c' < c ∧ d ♯ a' ⨳ b' ⨳ c ♯ a' ⨳ b ⨳ c' ♯ …
    rcases lt_nmul_iff.1 he with ⟨a', ha, b', hb, H₂⟩
    -- ⊢ ∃ a', a' < a ∧ ∃ b', b' < b ∧ ∃ c', c' < c ∧ d ♯ a' ⨳ b' ⨳ c ♯ a' ⨳ b ⨳ c' ♯ …
    refine' ⟨a', ha, b', hb, c', hc, _⟩
    -- ⊢ d ♯ a' ⨳ b' ⨳ c ♯ a' ⨳ b ⨳ c' ♯ a ⨳ b' ⨳ c' ≤ a' ⨳ b ⨳ c ♯ a ⨳ b' ⨳ c ♯ a ⨳  …
    have := nadd_le_nadd H₁ (nmul_nadd_le H₂ hc.le)
    -- ⊢ d ♯ a' ⨳ b' ⨳ c ♯ a' ⨳ b ⨳ c' ♯ a ⨳ b' ⨳ c' ≤ a' ⨳ b ⨳ c ♯ a ⨳ b' ⨳ c ♯ a ⨳  …
    simp only [nadd_nmul, nadd_assoc] at this
    -- ⊢ d ♯ a' ⨳ b' ⨳ c ♯ a' ⨳ b ⨳ c' ♯ a ⨳ b' ⨳ c' ≤ a' ⨳ b ⨳ c ♯ a ⨳ b' ⨳ c ♯ a ⨳  …
    rw [nadd_left_comm, nadd_left_comm d, nadd_left_comm, nadd_le_nadd_iff_left,
      nadd_left_comm (a ⨳ b' ⨳ c), nadd_left_comm (a' ⨳ b ⨳ c), nadd_left_comm (a ⨳ b ⨳ c'),
      nadd_le_nadd_iff_left, nadd_left_comm (a ⨳ b ⨳ c'), nadd_left_comm (a ⨳ b ⨳ c')] at this
    simpa only [nadd_assoc]
    -- 🎉 no goals
  · rintro ⟨a', ha, b', hb, c', hc, h⟩
    -- ⊢ d < a ⨳ b ⨳ c
    have := h.trans_lt (nmul_nadd_lt₃ ha hb hc)
    -- ⊢ d < a ⨳ b ⨳ c
    repeat' rw [nadd_lt_nadd_iff_right] at this
    -- ⊢ d < a ⨳ b ⨳ c
    assumption
    -- 🎉 no goals
#align ordinal.lt_nmul_iff₃ Ordinal.lt_nmul_iff₃

theorem nmul_le_iff₃ :
    a ⨳ b ⨳ c ≤ d ↔
      ∀ a' < a, ∀ b' < b, ∀ c' < c,
        a' ⨳ b ⨳ c ♯ a ⨳ b' ⨳ c ♯ a ⨳ b ⨳ c' ♯ a' ⨳ b' ⨳ c' <
          d ♯ a' ⨳ b' ⨳ c ♯ a' ⨳ b ⨳ c' ♯ a ⨳ b' ⨳ c' := by
  rw [← not_iff_not]; simp [lt_nmul_iff₃]
  -- ⊢ ¬a ⨳ b ⨳ c ≤ d ↔ ¬∀ (a' : Ordinal.{u}), a' < a → ∀ (b' : Ordinal.{u}), b' <  …
                      -- 🎉 no goals
#align ordinal.nmul_le_iff₃ Ordinal.nmul_le_iff₃

theorem lt_nmul_iff₃' :
    d < a ⨳ (b ⨳ c) ↔
      ∃ a' < a, ∃ b' < b, ∃ c' < c,
        d ♯ a' ⨳ (b' ⨳ c) ♯ a' ⨳ (b ⨳ c') ♯ a ⨳ (b' ⨳ c') ≤
          a' ⨳ (b ⨳ c) ♯ a ⨳ (b' ⨳ c) ♯ a ⨳ (b ⨳ c') ♯ a' ⨳ (b' ⨳ c') := by
  simp only [nmul_comm _ (_ ⨳ _), lt_nmul_iff₃, nadd_eq_add, NatOrdinal.toOrdinal_toNatOrdinal]
  -- ⊢ (∃ a', a' < b ∧ ∃ b', b' < c ∧ ∃ c', c' < a ∧ ↑toOrdinal (↑toNatOrdinal d +  …
  constructor <;> rintro ⟨b', hb, c', hc, a', ha, h⟩
  -- ⊢ (∃ a', a' < b ∧ ∃ b', b' < c ∧ ∃ c', c' < a ∧ ↑toOrdinal (↑toNatOrdinal d +  …
                  -- ⊢ ∃ a', a' < a ∧ ∃ b', b' < b ∧ ∃ c', c' < c ∧ ↑toOrdinal (↑toNatOrdinal d + ↑ …
                  -- ⊢ ∃ a', a' < b ∧ ∃ b', b' < c ∧ ∃ c', c' < a ∧ ↑toOrdinal (↑toNatOrdinal d + ↑ …
  · use a', ha, b', hb, c', hc; convert h using 1 <;> abel_nf
    -- ⊢ ↑toOrdinal (↑toNatOrdinal d + ↑toNatOrdinal (b' ⨳ c ⨳ a') + ↑toNatOrdinal (b …
                                -- ⊢ ↑toOrdinal (↑toNatOrdinal d + ↑toNatOrdinal (b' ⨳ c ⨳ a') + ↑toNatOrdinal (b …
                                                      -- 🎉 no goals
                                                      -- 🎉 no goals
  · use c', hc, a', ha, b', hb; convert h using 1 <;> abel_nf
    -- ⊢ ↑toOrdinal (↑toNatOrdinal d + ↑toNatOrdinal (c' ⨳ a' ⨳ a) + ↑toNatOrdinal (c …
                                -- ⊢ ↑toOrdinal (↑toNatOrdinal d + ↑toNatOrdinal (c' ⨳ a' ⨳ a) + ↑toNatOrdinal (c …
                                                      -- 🎉 no goals
                                                      -- 🎉 no goals
#align ordinal.lt_nmul_iff₃' Ordinal.lt_nmul_iff₃'

theorem nmul_le_iff₃' :
    a ⨳ (b ⨳ c) ≤ d ↔
      ∀ a' < a, ∀ b' < b, ∀ c' < c,
        a' ⨳ (b ⨳ c) ♯ a ⨳ (b' ⨳ c) ♯ a ⨳ (b ⨳ c') ♯ a' ⨳ (b' ⨳ c') <
          d ♯ a' ⨳ (b' ⨳ c) ♯ a' ⨳ (b ⨳ c') ♯ a ⨳ (b' ⨳ c') := by
  rw [← not_iff_not]; simp [lt_nmul_iff₃']
  -- ⊢ ¬a ⨳ (b ⨳ c) ≤ d ↔ ¬∀ (a' : Ordinal.{u}), a' < a → ∀ (b' : Ordinal.{u}), b'  …
                      -- 🎉 no goals
#align ordinal.nmul_le_iff₃' Ordinal.nmul_le_iff₃'

theorem nmul_assoc : ∀ a b c, a ⨳ b ⨳ c = a ⨳ (b ⨳ c)
  | a, b, c => by
    apply le_antisymm
    -- ⊢ a ⨳ b ⨳ c ≤ a ⨳ (b ⨳ c)
    · rw [nmul_le_iff₃]
      -- ⊢ ∀ (a' : Ordinal.{u_1}), a' < a → ∀ (b' : Ordinal.{u_1}), b' < b → ∀ (c' : Or …
      intro a' ha b' hb c' hc
      -- ⊢ a' ⨳ b ⨳ c ♯ a ⨳ b' ⨳ c ♯ a ⨳ b ⨳ c' ♯ a' ⨳ b' ⨳ c' < a ⨳ (b ⨳ c) ♯ a' ⨳ b'  …
      -- Porting note: the next line was just
      -- repeat' rw [nmul_assoc]
      -- but we need to spell out the arguments for the termination checker.
      rw [nmul_assoc a' b c, nmul_assoc a b' c, nmul_assoc a b c', nmul_assoc a' b' c',
        nmul_assoc a' b' c, nmul_assoc a' b c', nmul_assoc a b' c']
      exact nmul_nadd_lt₃' ha hb hc
      -- 🎉 no goals
    · rw [nmul_le_iff₃']
      -- ⊢ ∀ (a' : Ordinal.{u_1}), a' < a → ∀ (b' : Ordinal.{u_1}), b' < b → ∀ (c' : Or …
      intro a' ha b' hb c' hc
      -- ⊢ a' ⨳ (b ⨳ c) ♯ a ⨳ (b' ⨳ c) ♯ a ⨳ (b ⨳ c') ♯ a' ⨳ (b' ⨳ c') < a ⨳ b ⨳ c ♯ a' …
      -- Porting note: the next line was just
      -- repeat' rw [← nmul_assoc]
      -- but we need to spell out the arguments for the termination checker.
      rw [← nmul_assoc a' b c, ← nmul_assoc a b' c, ← nmul_assoc a b c', ← nmul_assoc a' b' c',
        ← nmul_assoc a' b' c, ← nmul_assoc a' b c', ← nmul_assoc a b' c']
      exact nmul_nadd_lt₃ ha hb hc
      -- 🎉 no goals
termination_by nmul_assoc a b c => (a, b, c)
#align ordinal.nmul_assoc Ordinal.nmul_assoc

end Ordinal

open Ordinal

instance : Mul NatOrdinal :=
  ⟨nmul⟩

-- Porting note: had to add universe annotations to ensure that the
-- two sources lived in the same universe.
instance : OrderedCommSemiring NatOrdinal.{u} :=
  { NatOrdinal.orderedCancelAddCommMonoid.{u},
    NatOrdinal.linearOrder.{u} with
    mul := (· * ·)
    left_distrib := nmul_nadd
    right_distrib := nadd_nmul
    zero_mul := zero_nmul
    mul_zero := nmul_zero
    mul_assoc := nmul_assoc
    one := 1
    one_mul := one_nmul
    mul_one := nmul_one
    mul_comm := nmul_comm
    zero_le_one := @zero_le_one Ordinal _ _ _ _
    mul_le_mul_of_nonneg_left := fun a b c => nmul_le_nmul_of_nonneg_left
    mul_le_mul_of_nonneg_right := fun a b c => nmul_le_nmul_of_nonneg_right }

namespace Ordinal

theorem nmul_eq_mul (a b) : a ⨳ b = toOrdinal (toNatOrdinal a * toNatOrdinal b) :=
  rfl
#align ordinal.nmul_eq_mul Ordinal.nmul_eq_mul

theorem nmul_nadd_one : ∀ a b, a ⨳ (b ♯ 1) = a ⨳ b ♯ a :=
  @mul_add_one NatOrdinal _ _ _
#align ordinal.nmul_nadd_one Ordinal.nmul_nadd_one

theorem nadd_one_nmul : ∀ a b, (a ♯ 1) ⨳ b = a ⨳ b ♯ b :=
  @add_one_mul NatOrdinal _ _ _
#align ordinal.nadd_one_nmul Ordinal.nadd_one_nmul

theorem nmul_succ (a b) : a ⨳ succ b = a ⨳ b ♯ a := by rw [← nadd_one, nmul_nadd_one]
                                                       -- 🎉 no goals
#align ordinal.nmul_succ Ordinal.nmul_succ

theorem succ_nmul (a b) : succ a ⨳ b = a ⨳ b ♯ b := by rw [← nadd_one, nadd_one_nmul]
                                                       -- 🎉 no goals
#align ordinal.succ_nmul Ordinal.succ_nmul

theorem nmul_add_one : ∀ a b, a ⨳ (b + 1) = a ⨳ b ♯ a :=
  nmul_succ
#align ordinal.nmul_add_one Ordinal.nmul_add_one

theorem add_one_nmul : ∀ a b, (a + 1) ⨳ b = a ⨳ b ♯ b :=
  succ_nmul
#align ordinal.add_one_nmul Ordinal.add_one_nmul

end Ordinal

namespace NatOrdinal

open Ordinal

theorem mul_le_nmul (a b : Ordinal.{u}) : a * b ≤ a ⨳ b := by
  refine b.limitRecOn ?_ ?_ ?_
  · simp
    -- 🎉 no goals
  · intro c h
    -- ⊢ a * succ c ≤ a ⨳ succ c
    rw [mul_succ, nmul_succ]
    -- ⊢ a * c + a ≤ a ⨳ c ♯ a
    exact (add_le_nadd _ a).trans (nadd_le_nadd_right h a)
    -- 🎉 no goals
  · intro c hc H
    -- ⊢ a * c ≤ a ⨳ c
    rcases eq_zero_or_pos a with (rfl | ha)
    -- ⊢ 0 * c ≤ 0 ⨳ c
    · simp
      -- 🎉 no goals
    · -- Porting note: `this` was inline in the `rw`, but now needs a preliminary `dsimp at this`.
      have := IsNormal.blsub_eq.{u, u} (mul_isNormal ha) hc
      -- ⊢ a * c ≤ a ⨳ c
      dsimp at this
      -- ⊢ a * c ≤ a ⨳ c
      rw [← this, blsub_le_iff]
      -- ⊢ ∀ (i : Ordinal.{u}), i < c → a * i < a ⨳ c
      exact fun i hi => (H i hi).trans_lt (nmul_lt_nmul_of_pos_left hi ha)
      -- 🎉 no goals
#align nat_ordinal.mul_le_nmul NatOrdinal.mul_le_nmul

end NatOrdinal
