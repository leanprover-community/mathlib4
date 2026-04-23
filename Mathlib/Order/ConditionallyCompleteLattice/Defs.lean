/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Order.Bounds.Basic
public import Mathlib.Order.SetNotation
public import Mathlib.Order.WellFounded

/-!
# Definitions of conditionally complete lattices

A conditionally complete lattice is a lattice in which every non-empty bounded subset `s`
has a least upper bound and a greatest lower bound, denoted below by `sSup s` and `sInf s`.
Typical examples are `ℝ`, `ℕ`, and `ℤ` with their usual orders.

The theory is very comparable to the theory of complete lattices, except that suitable
boundedness and nonemptiness assumptions have to be added to most statements.
We express these using the `BddAbove` and `BddBelow` predicates, which we use to prove
most useful properties of `sSup` and `sInf` in conditionally complete lattices.

To differentiate the statements between complete lattices and conditionally complete
lattices, we prefix `sInf` and `sSup` in the statements by `c`, giving `csInf` and `csSup`.
For instance, `sInf_le` is a statement in complete lattices ensuring `sInf s ≤ x`,
while `csInf_le` is the same statement in conditionally complete lattices
with an additional assumption that `s` is bounded below.
-/

@[expose] public section

open Set

variable {α β γ : Type*} {ι : Sort*}

/-- A conditionally complete lattice is a lattice in which
every nonempty subset which is bounded above has a supremum, and
every nonempty subset which is bounded below has an infimum.
Typical examples are real numbers or natural numbers.

To differentiate the statements from the corresponding statements in (unconditional)
complete lattices, we prefix `sInf` and `sSup` by a `c` everywhere. The same statements should
hold in both worlds, sometimes with additional assumptions of nonemptiness or
boundedness. -/
class ConditionallyCompleteLattice (α : Type*) extends Lattice α, OrderSupSet α, OrderInfSet α where
  /-- Every nonempty subset which is bounded above has a least upper bound. -/
  exists_isLUB_cond : ∀ s : Set α, s.Nonempty → BddAbove s → ∃ a, IsLUB s a
  /-- Every nonempty subset which is bounded below has a greatest lower bound. -/
  exists_isGLB_cond : ∀ s : Set α, s.Nonempty → BddBelow s → ∃ a, IsGLB s a

attribute [to_dual self (reorder := 3 4, 5 6)] ConditionallyCompleteLattice.mk
attribute [to_dual existing] ConditionallyCompleteLattice.toOrderSupSet
attribute [to_dual existing] ConditionallyCompleteLattice.exists_isLUB_cond

/-- A conditionally complete linear order is a linear order in which
every nonempty subset which is bounded above has a supremum, and
every nonempty subset which is bounded below has an infimum.
Typical examples are real numbers or natural numbers.

To differentiate the statements from the corresponding statements in (unconditional)
complete linear orders, we prefix `sInf` and `sSup` by a `c` everywhere. The same statements should
hold in both worlds, sometimes with additional assumptions of nonemptiness or
boundedness. -/
class ConditionallyCompleteLinearOrder (α : Type*)
    extends ConditionallyCompleteLattice α, Ord α where
  /-- A `ConditionallyCompleteLinearOrder` is total. -/
  le_total (a b : α) : a ≤ b ∨ b ≤ a
  /-- In a `ConditionallyCompleteLinearOrder`, we assume the order relations are all decidable. -/
  toDecidableLE : DecidableLE α
  /-- In a `ConditionallyCompleteLinearOrder`, we assume the order relations are all decidable. -/
  toDecidableEq : DecidableEq α := @decidableEqOfDecidableLE _ _ toDecidableLE
  /-- In a `ConditionallyCompleteLinearOrder`, we assume the order relations are all decidable. -/
  toDecidableLT : DecidableLT α := @decidableLTOfDecidableLE _ _ toDecidableLE
  /-- If a set is not bounded above, its supremum is by convention `sSup ∅`. -/
  csSup_of_not_bddAbove : ∀ s, ¬BddAbove s → sSup s = sSup (∅ : Set α)
  /-- If a set is not bounded below, its infimum is by convention `sInf ∅`. -/
  csInf_of_not_bddBelow : ∀ s, ¬BddBelow s → sInf s = sInf (∅ : Set α)
  compare a b := compareOfLessAndEq a b
  /-- Comparison via `compare` is equal to the canonical comparison given decidable `<` and `=`. -/
  compare_eq_compareOfLessAndEq : ∀ a b, compare a b = compareOfLessAndEq a b := by
    compareOfLessAndEq_rfl

/-- A conditionally complete linear order with `Bot` is a linear order with least element, in which
every nonempty subset which is bounded above has a supremum, and every nonempty subset (necessarily
bounded below) has an infimum.  A typical example is the natural numbers.

To differentiate the statements from the corresponding statements in (unconditional)
complete linear orders, we prefix `sInf` and `sSup` by a `c` everywhere. The same statements should
hold in both worlds, sometimes with additional assumptions of nonemptiness or
boundedness. -/
class ConditionallyCompleteLinearOrderBot (α : Type*) extends ConditionallyCompleteLinearOrder α,
    OrderBot α where

-- see Note [lower instance priority]
attribute [instance 100] ConditionallyCompleteLinearOrderBot.toOrderBot

/-- Create a `ConditionallyCompleteLattice` from a `PartialOrder` and `sup` function
that returns the least upper bound of a nonempty set which is bounded above. Usually this
constructor provides poor definitional equalities.  If other fields are known explicitly, they
should be provided; for example, if `inf` is known explicitly, construct the
`ConditionallyCompleteLattice` instance as
```
instance : ConditionallyCompleteLattice my_T where
  inf := better_inf
  le_inf := ...
  inf_le_right := ...
  inf_le_left := ...
  -- don't care to fix sup, sInf
  __ := conditionallyCompleteLatticeOfsSup my_T ...
```
-/
@[to_dual (attr := implicit_reducible) (reorder := 4 5)
/-- Create a `ConditionallyCompleteLattice` from a `PartialOrder` and `sInf` function
that returns the greatest lower bound of a nonempty set which is bounded below. Usually this
constructor provides poor definitional equalities.  If other fields are known explicitly, they
should be provided; for example, if `inf` is known explicitly, construct the
`ConditionallyCompleteLattice` instance as
```
instance : ConditionallyCompleteLattice my_T :=
  inf := better_inf
  le_inf := ...
  inf_le_right := ...
  inf_le_left := ...
  -- don't care to fix sup, sSup
  __ := conditionallyCompleteLatticeOfsInf my_T ...
```
-/]
def conditionallyCompleteLatticeOfsSup (α : Type*) [H1 : PartialOrder α] [H2 : OrderSupSet α]
    (bddAbove_pair : ∀ a b : α, BddAbove ({a, b} : Set α))
    (bddBelow_pair : ∀ a b : α, BddBelow ({a, b} : Set α))
    (isLUB_sSup : ∀ s : Set α, BddAbove s → s.Nonempty → IsLUB s (sSup s)) :
    ConditionallyCompleteLattice α where
  toLattice := Lattice.ofIsLUBofIsGLB (fun a b ↦ sSup {a, b}) (fun a b ↦ sSup (lowerBounds {a, b}))
    (fun a b ↦ isLUB_sSup {a, b} (bddAbove_pair a b) (insert_nonempty _ _))
    (fun a b ↦ isLUB_lowerBounds.mp <| isLUB_sSup (lowerBounds {a, b})
      (insert_nonempty _ _).bddAbove_lowerBounds (bddBelow_pair a b))
  toOrderSupSet := H2
  toOrderInfSet := .ofOrderSupSet
  exists_isLUB_cond _ hn hb := ⟨_, isLUB_sSup _ hb hn⟩
  exists_isGLB_cond s hn hb :=
    ⟨sSup (lowerBounds s), isLUB_lowerBounds.mp (isLUB_sSup _ hn.bddAbove_lowerBounds hb)⟩

/-- A version of `conditionallyCompleteLatticeOfsSup` when we already know that `α` is a lattice.

This should only be used when it is both hard and unnecessary to provide `sInf` explicitly. -/
@[to_dual (attr := implicit_reducible)
/-- A version of `conditionallyCompleteLatticeOfsInf` when we already know that `α` is a lattice.

This should only be used when it is both hard and unnecessary to provide `sSup` explicitly. -/]
def conditionallyCompleteLatticeOfLatticeOfsSup (α : Type*) [H1 : Lattice α] [OrderSupSet α]
    (isLUB_sSup : ∀ s : Set α, BddAbove s → s.Nonempty → IsLUB s (sSup s)) :
    ConditionallyCompleteLattice α :=
  { H1,
    conditionallyCompleteLatticeOfsSup α
      (fun a b => ⟨a ⊔ b, forall_insert_of_forall (forall_eq.mpr le_sup_right) le_sup_left⟩)
      (fun a b => ⟨a ⊓ b, forall_insert_of_forall (forall_eq.mpr inf_le_right) inf_le_left⟩)
      isLUB_sSup with }

open scoped Classical in
/-- A well-founded linear order is conditionally complete, with a bottom element. -/
noncomputable abbrev WellFoundedLT.conditionallyCompleteLinearOrderBot (α : Type*)
    [i₁ : LinearOrder α] [i₂ : OrderBot α] [h : WellFoundedLT α] :
    ConditionallyCompleteLinearOrderBot α where
  __ := i₁
  __ := i₂
  __ := LinearOrder.toLattice
  __ :=
    letI : OrderInfSet α := .choose ⊥
    conditionallyCompleteLatticeOfLatticeOfsInf _ fun s _ hn ↦ isGLB_sInf_of_isGLB
      (IsLeast.isGLB ⟨h.wf.min_mem s hn, fun _ hx ↦ h.wf.min_le hx⟩)
  csSup_of_not_bddAbove _ H :=
    (dif_neg (fun ⟨_, hx⟩ ↦ H (isGLB_upperBounds.mp hx).bddAbove)).trans sSup_empty.symm
  csInf_of_not_bddBelow s H := (H (OrderBot.bddBelow s)).elim
