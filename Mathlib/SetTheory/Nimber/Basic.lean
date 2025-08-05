/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Data.Nat.Bitwise
import Mathlib.SetTheory.Ordinal.Family

/-!
# Nimbers

The goal of this file is to define the nimbers, constructed as ordinals endowed with new
arithmetical operations. The nim sum `a + b` is recursively defined as the least ordinal not equal
to any `a' + b` or `a + b'` for `a' < a` and `b' < b`. There is also a nim product, defined in the
`Mathlib/SetTheory/Nimber/Field.lean` file.

Nim addition arises within the context of impartial games. By the Sprague-Grundy theorem, each
impartial game is equivalent to some game of nim. If `x ≈ nim o₁` and `y ≈ nim o₂`, then
`x + y ≈ nim (o₁ + o₂)`, where the ordinals are summed together as nimbers. Unfortunately, the
nim product admits no such characterization.

## Notation

Following [On Numbers And Games][conway2001] (p. 121), we define notation `∗o` for the cast from
`Ordinal` to `Nimber`. Note that for general `n : ℕ`, `∗n` is **not** the same as `↑n`. For
instance, `∗2 ≠ 0`, whereas `↑2 = ↑1 + ↑1 = 0`.

## Implementation notes

The nimbers inherit the order from the ordinals - this makes working with minimum excluded values
much more convenient. However, the fact that nimbers are of characteristic 2 prevents the order from
interacting with the arithmetic in any nice way.

To reduce API duplication, we opt not to implement operations on `Nimber` on `Ordinal`. The order
isomorphisms `Ordinal.toNimber` and `Nimber.toOrdinal` allow us to cast between them whenever
needed.
-/

universe u v

open Function Order

noncomputable section

/-! ### Basic casts between `Ordinal` and `Nimber` -/

/-- A type synonym for ordinals with nimber addition and multiplication. -/
def Nimber : Type _ :=
  Ordinal deriving Zero, Inhabited, One, Nontrivial, WellFoundedRelation

instance Nimber.instLinearOrder : LinearOrder Nimber := Ordinal.instLinearOrder
instance Nimber.instSuccOrder : SuccOrder Nimber := Ordinal.instSuccOrder
instance Nimber.instOrderBot : OrderBot Nimber := Ordinal.instOrderBot
instance Nimber.instNoMaxOrder : NoMaxOrder Nimber := Ordinal.instNoMaxOrder
instance Nimber.instZeroLEOneClass : ZeroLEOneClass Nimber := Ordinal.instZeroLEOneClass
instance Nimber.instNeZeroOne : NeZero (1 : Nimber) := Ordinal.instNeZeroOne

/-- The identity function between `Ordinal` and `Nimber`. -/
@[match_pattern]
def Ordinal.toNimber : Ordinal ≃o Nimber :=
  OrderIso.refl _

/-- The identity function between `Nimber` and `Ordinal`. -/
@[match_pattern]
def Nimber.toOrdinal : Nimber ≃o Ordinal :=
  OrderIso.refl _

@[inherit_doc]
scoped[Nimber] prefix:75 "∗" => Ordinal.toNimber

namespace Nimber

open Ordinal

@[simp]
theorem toOrdinal_symm_eq : Nimber.toOrdinal.symm = Ordinal.toNimber :=
  rfl

@[simp]
theorem toOrdinal_toNimber (a : Nimber) : ∗(Nimber.toOrdinal a) = a :=
  rfl

theorem lt_wf : @WellFounded Nimber (· < ·) :=
  Ordinal.lt_wf

instance : WellFoundedLT Nimber :=
  Ordinal.wellFoundedLT

instance : ConditionallyCompleteLinearOrderBot Nimber :=
  WellFoundedLT.conditionallyCompleteLinearOrderBot _

@[simp]
theorem bot_eq_zero : ⊥ = 0 :=
  rfl

@[simp]
theorem toOrdinal_zero : toOrdinal 0 = 0 :=
  rfl

@[simp]
theorem toOrdinal_one : toOrdinal 1 = 1 :=
  rfl

@[simp]
theorem toOrdinal_eq_zero {a} : toOrdinal a = 0 ↔ a = 0 :=
  Iff.rfl

@[simp]
theorem toOrdinal_eq_one {a} : toOrdinal a = 1 ↔ a = 1 :=
  Iff.rfl

@[simp]
theorem toOrdinal_max (a b : Nimber) : toOrdinal (max a b) = max (toOrdinal a) (toOrdinal b) :=
  rfl

@[simp]
theorem toOrdinal_min (a b : Nimber) : toOrdinal (min a b) = min (toOrdinal a) (toOrdinal b) :=
  rfl

theorem succ_def (a : Nimber) : succ a = ∗(toOrdinal a + 1) :=
  rfl

/-- A recursor for `Nimber`. Use as `induction x`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
protected def rec {β : Nimber → Sort*} (h : ∀ a, β (∗a)) : ∀ a, β a := fun a =>
  h (toOrdinal a)

/-- `Ordinal.induction` but for `Nimber`. -/
theorem induction {p : Nimber → Prop} : ∀ (i) (_ : ∀ j, (∀ k, k < j → p k) → p j), p i :=
  Ordinal.induction

protected theorem le_zero {a : Nimber} : a ≤ 0 ↔ a = 0 :=
  Ordinal.le_zero

protected theorem not_lt_zero (a : Nimber) : ¬ a < 0 :=
  Ordinal.not_lt_zero a

protected theorem pos_iff_ne_zero {a : Nimber} : 0 < a ↔ a ≠ 0 :=
  Ordinal.pos_iff_ne_zero

theorem lt_one_iff_zero {a : Nimber} : a < 1 ↔ a = 0 :=
  Ordinal.lt_one_iff_zero

theorem one_le_iff_ne_zero {a : Nimber} : 1 ≤ a ↔ a ≠ 0 :=
  Ordinal.one_le_iff_ne_zero

theorem eq_nat_of_le_nat {a : Nimber} {b : ℕ} (h : a ≤ ∗b) : ∃ c : ℕ, a = ∗c :=
  Ordinal.lt_omega0.1 (h.trans_lt (nat_lt_omega0 b))

instance small_Iio (a : Nimber.{u}) : Small.{u} (Set.Iio a) := Ordinal.small_Iio a
instance small_Iic (a : Nimber.{u}) : Small.{u} (Set.Iic a) := Ordinal.small_Iic a
instance small_Ico (a b : Nimber.{u}) : Small.{u} (Set.Ico a b) := Ordinal.small_Ico a b
instance small_Icc (a b : Nimber.{u}) : Small.{u} (Set.Icc a b) := Ordinal.small_Icc a b
instance small_Ioo (a b : Nimber.{u}) : Small.{u} (Set.Ioo a b) := Ordinal.small_Ioo a b
instance small_Ioc (a b : Nimber.{u}) : Small.{u} (Set.Ioc a b) := Ordinal.small_Ioc a b

theorem not_bddAbove_compl_of_small (s : Set Nimber.{u}) [Small.{u} s] : ¬ BddAbove sᶜ :=
  Ordinal.not_bddAbove_compl_of_small s

end Nimber

theorem not_small_nimber : ¬ Small.{u} Nimber.{max u v} :=
  not_small_ordinal

instance Nimber.uncountable : Uncountable Nimber :=
  Ordinal.uncountable

open Nimber

namespace Ordinal

@[simp]
theorem toNimber_symm_eq : toNimber.symm = Nimber.toOrdinal :=
  rfl

@[simp]
theorem toNimber_toOrdinal (a : Ordinal) : Nimber.toOrdinal (∗a) = a :=
  rfl

@[simp]
theorem toNimber_zero : ∗0 = 0 :=
  rfl

@[simp]
theorem toNimber_one : ∗1 = 1 :=
  rfl

@[simp]
theorem toNimber_eq_zero {a} : ∗a = 0 ↔ a = 0 :=
  Iff.rfl

@[simp]
theorem toNimber_eq_one {a} : ∗a = 1 ↔ a = 1 :=
  Iff.rfl

@[simp]
theorem toNimber_max (a b : Ordinal) : ∗(max a b) = max (∗a) (∗b) :=
  rfl

@[simp]
theorem toNimber_min (a b : Ordinal) : ∗(min a b) = min (∗a) (∗b) :=
  rfl

end Ordinal

/-! ### Nimber addition -/

namespace Nimber

variable {a b c : Nimber.{u}}

/-- Nimber addition is recursively defined so that `a + b` is the smallest nimber not equal to
`a' + b` or `a + b'` for `a' < a` and `b' < b`. -/
-- We write the binders like this so that the termination checker works.
protected def add (a b : Nimber.{u}) : Nimber.{u} :=
  sInf {x | (∃ a', ∃ (_ : a' < a), Nimber.add a' b = x) ∨
    ∃ b', ∃ (_ : b' < b), Nimber.add a b' = x}ᶜ
termination_by (a, b)

instance : Add Nimber :=
  ⟨Nimber.add⟩

theorem add_def (a b : Nimber) :
    a + b = sInf {x | (∃ a' < a, a' + b = x) ∨ ∃ b' < b, a + b' = x}ᶜ := by
  change Nimber.add a b = _
  rw [Nimber.add]
  simp_rw [exists_prop]
  rfl

/-- The set in the definition of `Nimber.add` is nonempty. -/
private theorem add_nonempty (a b : Nimber.{u}) :
    {x | (∃ a' < a, a' + b = x) ∨ ∃ b' < b, a + b' = x}ᶜ.Nonempty :=
  nonempty_of_not_bddAbove <| not_bddAbove_compl_of_small
    ((· + b) '' Set.Iio a ∪ (a + ·) '' Set.Iio b)

theorem exists_of_lt_add (h : c < a + b) : (∃ a' < a, a' + b = c) ∨ ∃ b' < b, a + b' = c := by
  rw [add_def] at h
  have := notMem_of_lt_csInf' h
  rwa [Set.mem_compl_iff, not_not] at this

theorem add_le_of_forall_ne (h₁ : ∀ a' < a, a' + b ≠ c) (h₂ : ∀ b' < b, a + b' ≠ c) :
    a + b ≤ c := by
  by_contra! h
  have := exists_of_lt_add h
  tauto

private theorem add_ne_of_lt (a b : Nimber) :
    (∀ a' < a, a' + b ≠ a + b) ∧ ∀ b' < b, a + b' ≠ a + b := by
  have H := csInf_mem (add_nonempty a b)
  rw [← add_def] at H
  simpa using H

instance : IsLeftCancelAdd Nimber := by
  constructor
  intro a b c h
  apply le_antisymm <;>
  apply le_of_not_gt
  · exact fun hc => (add_ne_of_lt a b).2 c hc h.symm
  · exact fun hb => (add_ne_of_lt a c).2 b hb h

instance : IsRightCancelAdd Nimber := by
  constructor
  intro a b c h
  apply le_antisymm <;>
  apply le_of_not_gt
  · exact fun hc => (add_ne_of_lt b a).1 c hc h.symm
  · exact fun ha => (add_ne_of_lt c a).1 b ha h

protected theorem add_comm (a b : Nimber) : a + b = b + a := by
  rw [add_def, add_def]
  simp_rw [or_comm]
  congr! 7 <;>
    (rw [and_congr_right_iff]; intro; rw [Nimber.add_comm])
termination_by (a, b)

theorem add_eq_zero {a b : Nimber} : a + b = 0 ↔ a = b := by
  constructor <;>
    intro hab
  · obtain h | rfl | h := lt_trichotomy a b
    · have ha : a + a = 0 := add_eq_zero.2 rfl
      rwa [← ha, add_right_inj, eq_comm] at hab
    · rfl
    · have hb : b + b = 0 := add_eq_zero.2 rfl
      rwa [← hb, add_left_inj] at hab
  · rw [← Nimber.le_zero]
    apply add_le_of_forall_ne <;>
    simp_rw [ne_eq] <;>
    intro x hx
    · rw [add_eq_zero, ← hab]
      exact hx.ne
    · rw [add_eq_zero, hab]
      exact hx.ne'
termination_by (a, b)

theorem add_ne_zero_iff : a + b ≠ 0 ↔ a ≠ b :=
  add_eq_zero.not

@[simp]
theorem add_self (a : Nimber) : a + a = 0 :=
  add_eq_zero.2 rfl

protected theorem add_assoc (a b c : Nimber) : a + b + c = a + (b + c) := by
  apply le_antisymm <;>
    apply add_le_of_forall_ne <;>
    intro x hx <;>
    try obtain ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩ := exists_of_lt_add hx
  on_goal 1 => rw [Nimber.add_assoc y, add_ne_add_left]
  on_goal 2 => rw [Nimber.add_assoc _ y, add_ne_add_right, add_ne_add_left]
  on_goal 3 => rw [Nimber.add_assoc _ _ x, add_ne_add_right, add_ne_add_right]
  on_goal 4 => rw [← Nimber.add_assoc x, add_ne_add_left, add_ne_add_left]
  on_goal 5 => rw [← Nimber.add_assoc _ y, add_ne_add_left, add_ne_add_right]
  on_goal 6 => rw [← Nimber.add_assoc _ _ y, add_ne_add_right]
  all_goals apply ne_of_lt; assumption
termination_by (a, b, c)

protected theorem add_zero (a : Nimber) : a + 0 = a := by
  apply le_antisymm
  · apply add_le_of_forall_ne
    · intro a' ha
      rw [Nimber.add_zero]
      exact ha.ne
    · intro _ h
      exact (Nimber.not_lt_zero _ h).elim
  · by_contra! h
    replace h := h -- needed to remind `termination_by`
    have := Nimber.add_zero (a + 0)
    rw [add_left_inj] at this
    exact this.not_lt h
termination_by a

protected theorem zero_add (a : Nimber) : 0 + a = a := by
  rw [Nimber.add_comm, Nimber.add_zero]

instance : Neg Nimber :=
  ⟨id⟩

@[simp]
protected theorem neg_eq (a : Nimber) : -a = a :=
  rfl

instance : AddCommGroupWithOne Nimber where
  add_assoc := Nimber.add_assoc
  add_zero := Nimber.add_zero
  zero_add := Nimber.zero_add
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel := add_self
  add_comm := Nimber.add_comm

@[simp]
theorem add_cancel_right (a b : Nimber) : a + b + b = a := by
  rw [add_assoc, add_self, add_zero]

@[simp]
theorem add_cancel_left (a b : Nimber) : a + (a + b) = b := by
  rw [← add_assoc, add_self, zero_add]

theorem add_trichotomy {a b c : Nimber} (h : a + b + c ≠ 0) :
    b + c < a ∨ c + a < b ∨ a + b < c := by
  rw [← Nimber.pos_iff_ne_zero] at h
  obtain ⟨x, hx, hx'⟩ | ⟨x, hx, hx'⟩ := exists_of_lt_add h <;>
  rw [add_eq_zero] at hx'
  · obtain ⟨x, hx, hx'⟩ | ⟨x, hx, hx'⟩ := exists_of_lt_add (hx' ▸ hx)
    · rw [← hx', add_comm, add_cancel_right]
      exact Or.inl hx
    · rw [← hx', add_comm a, add_cancel_right]
      exact Or.inr <| Or.inl hx
  · rw [← hx'] at hx
    exact Or.inr <| Or.inr hx

theorem lt_add_cases {a b c : Nimber} (h : a < b + c) : a + c < b ∨ a + b < c := by
  obtain ha | hb | hc := add_trichotomy <| add_assoc a b c ▸ add_ne_zero_iff.2 h.ne
  exacts [(h.asymm ha).elim, Or.inl <| add_comm c a ▸ hb, Or.inr hc]

/-- Nimber addition of naturals corresponds to the bitwise XOR operation. -/
theorem add_nat (a b : ℕ) : ∗a + ∗b = ∗(a ^^^ b) := by
  apply le_antisymm
  · apply add_le_of_forall_ne
    all_goals
      intro c hc
      obtain ⟨c, rfl⟩ := eq_nat_of_le_nat hc.le
      rw [OrderIso.lt_iff_lt] at hc
      replace hc := Nat.cast_lt.1 hc
      rw [add_nat]
      simpa using hc.ne
  · apply le_of_not_gt
    intro hc
    obtain ⟨c, hc'⟩ := eq_nat_of_le_nat hc.le
    rw [hc', OrderIso.lt_iff_lt, Nat.cast_lt] at hc
    obtain h | h := Nat.lt_xor_cases hc
    · apply h.ne
      simpa [Nat.xor_comm, Nat.xor_cancel_left, ← hc'] using add_nat (c ^^^ b) b
    · apply h.ne
      simpa [Nat.xor_comm, Nat.xor_cancel_left, ← hc'] using add_nat a (c ^^^ a)

end Nimber
