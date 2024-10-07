/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Algebra.CharP.Two
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Tactic.Abel

/-!
# Nimbers

The goal of this file is to define the field of nimbers, constructed as ordinals endowed with new
arithmetical operations. The nim sum `a + b` is recursively defined as the least ordinal not equal
to any `a' + b` or `a + b'` for `a' < a` and `b' < b`. The nim product `a * b` is likewise
recursively defined as the least ordinal not equal to any `a' * b + a * b' + a' * b'` for `a' < a`
and `b' < b`.

Nim addition arises within the context of impartial games. By the Sprague-Grundy theorem, each
impartial game is equivalent to some game of nim. If `x ≈ nim o₁` and `y ≈ nim o₂`, then
`x + y ≈ nim (o₁ + o₂)`, where the ordinals are summed together as nimbers. Unfortunately, the
nim product admits no such characterization.

## Implementation notes

The nimbers inherit the order from the ordinals - this makes working with minimum excluded values
much more convenient. However, the fact that nimbers are of characteristic 2 prevents the order from
interacting with the arithmetic in any nice way.

To reduce API duplication, we opt not to implement operations on `Nimber` on `Ordinal`. The order
isomorphisms `Ordinal.toNimber` and `Nimber.toOrdinal` allow us to cast between them whenever
needed.

## Todo

- Define nim division and prove nimbers are a field.
- Show the nimbers are algebraically closed.
-/

universe u v

open Function Order

noncomputable section

/-! ### Basic casts between `Ordinal` and `Nimber` -/

/-- A type synonym for ordinals with natural addition and multiplication. -/
def Nimber : Type _ :=
  Ordinal deriving Zero, Inhabited, One, Nontrivial, WellFoundedRelation

instance Nimber.linearOrder : LinearOrder Nimber := {Ordinal.linearOrder with}
instance Nimber.succOrder : SuccOrder Nimber := {Ordinal.instSuccOrder with}
instance Nimber.orderBot : OrderBot Nimber := {Ordinal.orderBot with}
instance Nimber.noMaxOrder : NoMaxOrder Nimber := {Ordinal.noMaxOrder with}
instance Nimber.zeroLEOneClass : ZeroLEOneClass Nimber := {Ordinal.zeroLEOneClass with}
instance Nimber.NeZero.one : NeZero (1 : Nimber) := Ordinal.NeZero.one

/-- The identity function between `Ordinal` and `Nimber`. -/
@[match_pattern]
def Ordinal.toNimber : Ordinal ≃o Nimber :=
  OrderIso.refl _

/-- The identity function between `Nimber` and `Ordinal`. -/
@[match_pattern]
def Nimber.toOrdinal : Nimber ≃o Ordinal :=
  OrderIso.refl _

namespace Nimber

open Ordinal

@[simp]
theorem toOrdinal_symm_eq : Nimber.toOrdinal.symm = Ordinal.toNimber :=
  rfl

@[simp]
theorem toOrdinal_toNimber (a : Nimber) :
    Ordinal.toNimber (Nimber.toOrdinal a) = a := rfl

theorem lt_wf : @WellFounded Nimber (· < ·) :=
  Ordinal.lt_wf

instance : WellFoundedLT Nimber :=
  Ordinal.wellFoundedLT

instance : IsWellOrder Nimber (· < ·) where

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

theorem succ_def (a : Nimber) : succ a = toNimber (toOrdinal a + 1) :=
  rfl

/-- A recursor for `Nimber`. Use as `induction x`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
protected def rec {β : Nimber → Sort*} (h : ∀ a, β (toNimber a)) : ∀ a, β a := fun a =>
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

namespace Ordinal

@[simp]
theorem toNimber_symm_eq : toNimber.symm = Nimber.toOrdinal :=
  rfl

@[simp]
theorem toNimber_toOrdinal (a : Ordinal) :  Nimber.toOrdinal (toNimber a) = a :=
  rfl

@[simp]
theorem toNimber_zero : toNimber 0 = 0 :=
  rfl

@[simp]
theorem toNimber_one : toNimber 1 = 1 :=
  rfl

@[simp]
theorem toNimber_eq_zero {a} : toNimber a = 0 ↔ a = 0 :=
  Iff.rfl

@[simp]
theorem toNimber_eq_one {a} : toNimber a = 1 ↔ a = 1 :=
  Iff.rfl

@[simp]
theorem toNimber_max (a b : Ordinal) :
    toNimber (max a b) = max (toNimber a) (toNimber b) :=
  rfl

@[simp]
theorem toNimber_min (a b : Ordinal) :
    toNimber (min a b) = min (toNimber a) (toNimber b) :=
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
  have := not_mem_of_lt_csInf' h
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
  apply le_of_not_lt
  · exact fun hc => (add_ne_of_lt a b).2 c hc h.symm
  · exact fun hb => (add_ne_of_lt a c).2 b hb h

instance : IsRightCancelAdd Nimber := by
  constructor
  intro a b c h
  apply le_antisymm <;>
  apply le_of_not_lt
  · exact fun hc => (add_ne_of_lt a b).1 c hc h.symm
  · exact fun ha => (add_ne_of_lt c b).1 a ha h

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
  · -- by_contra! doesn't work for whatever reason.
    by_contra h
    replace h := lt_of_not_le h
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

instance : CharP Nimber 2 := by
  apply CharTwo.mk one_ne_zero
  rw [← one_add_one_eq_two, add_self]

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

private theorem two_zsmul (x : Nimber) : (2 : ℤ) • x = 0 := by
  rw [_root_.two_zsmul]
  exact add_self x

private theorem add_eq_iff_eq_add : a + b = c ↔ a = c + b :=
  sub_eq_iff_eq_add

/-! ### Nimber multiplication -/

/-- Nimber multiplication is recursively defined so that `a * b` is the smallest nimber not equal to
`a' * b + a * b' + a' * b'` for `a' < a` and `b' < b`. -/
-- We write the binders like this so that the termination checker works.
protected def mul (a b : Nimber.{u}) : Nimber.{u} :=
  sInf {x | ∃ a', ∃ (_ : a' < a), ∃ b', ∃ (_ : b' < b),
    Nimber.mul a' b + Nimber.mul a b' + Nimber.mul a' b' = x}ᶜ
termination_by (a, b)

instance : Mul Nimber :=
  ⟨Nimber.mul⟩

theorem mul_def (a b : Nimber) :
    a * b = sInf {x | ∃ a' < a, ∃ b' < b, a' * b + a * b' + a' * b' = x}ᶜ := by
  change Nimber.mul a b = _
  rw [Nimber.mul]
  simp_rw [exists_prop]
  rfl

/-- The set in the definition of `Nimber.mul` is nonempty. -/
private theorem mul_nonempty (a b : Nimber.{u}) :
    {x | ∃ a' < a, ∃ b' < b, a' * b + a * b' + a' * b' = x}ᶜ.Nonempty := by
  convert nonempty_of_not_bddAbove <| not_bddAbove_compl_of_small
    ((fun x ↦ x.1 * b + a * x.2 + x.1 * x.2) '' Set.Iio a ×ˢ Set.Iio b)
  ext
  simp_rw [Set.mem_setOf_eq, Set.mem_image, Set.mem_prod, Set.mem_Iio, Prod.exists]
  tauto

theorem exists_of_lt_mul (h : c < a * b) : ∃ a' < a, ∃ b' < b, a' * b + a * b' + a' * b' = c := by
  rw [mul_def] at h
  have := not_mem_of_lt_csInf' h
  rwa [Set.not_mem_compl_iff] at this

theorem mul_le_of_forall_ne (h : ∀ a' < a, ∀ b' < b, a' * b + a * b' + a' * b' ≠ c) :
    a * b ≤ c := by
  by_contra! h'
  have := exists_of_lt_mul h'
  tauto

instance : MulZeroClass Nimber where
  mul_zero a := by
    rw [← Nimber.le_zero]
    exact mul_le_of_forall_ne fun _ _ _ h ↦ (Nimber.not_lt_zero _ h).elim
  zero_mul a := by
    rw [← Nimber.le_zero]
    exact mul_le_of_forall_ne fun _ h ↦ (Nimber.not_lt_zero _ h).elim

private theorem mul_ne_of_lt : ∀ a' < a, ∀ b' < b, a' * b + a * b' + a' * b' ≠ a * b := by
  have H := csInf_mem (mul_nonempty a b)
  rw [← mul_def] at H
  simpa using H

instance : NoZeroDivisors Nimber where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} h := by
    by_contra! hab
    iterate 2 rw [← Nimber.pos_iff_ne_zero] at hab
    apply (mul_ne_of_lt _ hab.1 _ hab.2).symm
    simpa only [zero_add, mul_zero, zero_mul]

protected theorem mul_comm (a b : Nimber) : a * b = b * a := by
  apply le_antisymm <;>
    apply mul_le_of_forall_ne <;>
    intro x hx y hy
  on_goal 1 => rw [add_comm (x * _), Nimber.mul_comm a, Nimber.mul_comm x, Nimber.mul_comm x]
  on_goal 2 => rw [add_comm (x * _), ← Nimber.mul_comm y, ← Nimber.mul_comm a, ← Nimber.mul_comm y]
  all_goals exact mul_ne_of_lt y hy x hx
termination_by (a, b)

protected theorem mul_add (a b c : Nimber) : a * (b + c) = a * b + a * c := by
  apply le_antisymm
  · apply mul_le_of_forall_ne
    intro a' ha x hx
    obtain (⟨b', h, rfl⟩ | ⟨c', h, rfl⟩) := exists_of_lt_add hx <;>
    rw [Nimber.mul_add a', Nimber.mul_add a, Nimber.mul_add a']
    on_goal 1 => rw [← add_ne_add_left (a * c)]
    on_goal 2 => rw [← add_ne_add_left (a * b)]
    all_goals
      abel_nf
      simp only [two_zsmul, zero_add]
      rw [← add_assoc]
      exact mul_ne_of_lt _ ha _ h
  · apply add_le_of_forall_ne <;>
      intro x' hx' <;>
      obtain ⟨x, hx, y, hy, rfl⟩ := exists_of_lt_mul hx'
    · obtain h | h | h := lt_trichotomy (y + c) (b + c)
      · have H := mul_ne_of_lt _ hx _ h
        rw [Nimber.mul_add x, Nimber.mul_add a, Nimber.mul_add x] at H
        abel_nf at H ⊢
        simpa only [two_zsmul, zero_add] using H
      · exact (hy.ne <| add_left_injective _ h).elim
      · obtain ⟨z, hz, hz'⟩ | ⟨c', hc, hc'⟩ := exists_of_lt_add h
        · exact ((hz.trans hy).ne <| add_left_injective _ hz').elim
        · have := add_eq_iff_eq_add.1 hc'
          have H := mul_ne_of_lt _ hx _ hc
          rw [← hc', Nimber.mul_add a y c', ← add_ne_add_left (a * y), ← add_ne_add_left (a * c),
            ← add_ne_add_left (a * c'), ← add_eq_iff_eq_add.2 hc', Nimber.mul_add x,
            Nimber.mul_add x]
          abel_nf at H ⊢
          simpa only [two_zsmul, add_zero, zero_add] using H
    · obtain h | h | h := lt_trichotomy (b + y) (b + c)
      · have H := mul_ne_of_lt _ hx _ h
        rw [Nimber.mul_add x, Nimber.mul_add a, Nimber.mul_add x] at H
        abel_nf at H ⊢
        simpa only [two_zsmul, zero_add] using H
      · exact (hy.ne <| add_right_injective _ h).elim
      · obtain ⟨b', hb, hb'⟩ | ⟨z, hz, hz'⟩ := exists_of_lt_add h
        · have H := mul_ne_of_lt _ hx _ hb
          have hb'' := add_eq_iff_eq_add.2 (add_comm b c ▸ hb')
          rw [← hb', Nimber.mul_add a b', ← add_ne_add_left (a * y), ← add_ne_add_left (a * b),
            ← add_ne_add_left (a * b'), ← hb'', Nimber.mul_add x, Nimber.mul_add x]
          abel_nf at H ⊢
          simpa only [two_zsmul, add_zero, zero_add] using H
        · exact ((hz.trans hy).ne <| add_right_injective _ hz').elim
termination_by (a, b, c)

protected theorem add_mul (a b c : Nimber) : (a + b) * c = a * c + b * c := by
  rw [Nimber.mul_comm, Nimber.mul_add, Nimber.mul_comm, Nimber.mul_comm b]

protected theorem mul_assoc (a b c : Nimber) : a * b * c = a * (b * c) := by
  apply le_antisymm <;>
    apply mul_le_of_forall_ne <;>
    intro x hx y hy
  · obtain ⟨a', ha, b', hb, rfl⟩ := exists_of_lt_mul hx
    have H : (a + a') * ((b + b') * (c + y)) ≠ 0 := by
      apply mul_ne_zero _ (mul_ne_zero _ _)
      all_goals
        rw [add_ne_zero_iff]
        apply ne_of_gt
        assumption
    simp only [Nimber.add_mul, Nimber.mul_add] at H ⊢
    iterate 7 rw [Nimber.mul_assoc]
    rw [← add_ne_add_left (a * (b * c))]
    abel_nf at H ⊢
    simpa only [two_zsmul, zero_add] using H
  · obtain ⟨b', hb, c', hc, rfl⟩ := exists_of_lt_mul hy
    have H : (a + x) * (b + b') * (c + c') ≠ 0 := by
      apply mul_ne_zero (mul_ne_zero _ _)
      all_goals
        rw [add_ne_zero_iff]
        apply ne_of_gt
        assumption
    simp only [Nimber.add_mul, Nimber.mul_add] at H ⊢
    iterate 7 rw [← Nimber.mul_assoc]
    rw [← add_ne_add_left (a * b * c)]
    abel_nf at H ⊢
    simpa only [two_zsmul, zero_add] using H
termination_by (a, b, c)

instance : IsCancelMulZero Nimber where
  mul_left_cancel_of_ne_zero ha h := by
    rw [← add_eq_zero, ← Nimber.mul_add, mul_eq_zero] at h
    exact add_eq_zero.1 (h.resolve_left ha)
  mul_right_cancel_of_ne_zero ha h := by
    rw [← add_eq_zero, ← Nimber.add_mul, mul_eq_zero] at h
    exact add_eq_zero.1 (h.resolve_right ha)

protected theorem one_mul (a : Nimber) : 1 * a = a := by
  apply le_antisymm
  · apply mul_le_of_forall_ne
    intro x hx y hy
    rw [Nimber.lt_one_iff_zero] at hx
    rw [hx, Nimber.one_mul, zero_mul, zero_mul, add_zero, zero_add]
    exact hy.ne
  · -- by_contra! doesn't work for whatever reason.
    by_contra h
    replace h := lt_of_not_le h
    exact (mul_left_cancel₀ one_ne_zero <| Nimber.one_mul _).not_lt h
termination_by a

protected theorem mul_one (a : Nimber) : a * 1 = a := by
  rw [Nimber.mul_comm, Nimber.one_mul]

instance : CommRing Nimber where
  left_distrib := Nimber.mul_add
  right_distrib := Nimber.add_mul
  zero_mul := zero_mul
  mul_zero := mul_zero
  mul_assoc := Nimber.mul_assoc
  mul_comm := Nimber.mul_comm
  one_mul := Nimber.one_mul
  mul_one := Nimber.mul_one
  __ : AddCommGroupWithOne Nimber := inferInstance

instance : IsDomain Nimber where
instance : CancelMonoidWithZero Nimber where

end Nimber
