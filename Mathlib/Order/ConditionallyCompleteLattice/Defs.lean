/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.SetNotation
import Mathlib.Order.WellFounded

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
class ConditionallyCompleteLattice (α : Type*) extends Lattice α, SupSet α, InfSet α where
  /-- `a ≤ sSup s` for all `a ∈ s`. -/
  le_csSup : ∀ s a, BddAbove s → a ∈ s → a ≤ sSup s
  /-- `sSup s ≤ a` for all `a ∈ upperBounds s`. -/
  csSup_le : ∀ s a, Set.Nonempty s → a ∈ upperBounds s → sSup s ≤ a
  /-- `sInf s ≤ a` for all `a ∈ s`. -/
  csInf_le : ∀ s a, BddBelow s → a ∈ s → sInf s ≤ a
  /-- `a ≤ sInf s` for all `a ∈ lowerBounds s`. -/
  le_csInf : ∀ s a, Set.Nonempty s → a ∈ lowerBounds s → a ≤ sInf s

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
  /-- The supremum of the empty set is special-cased to `⊥` -/
  csSup_empty : sSup ∅ = ⊥

-- see Note [lower instance priority]
attribute [instance 100] ConditionallyCompleteLinearOrderBot.toOrderBot

open scoped Classical in
/-- A well founded linear order is conditionally complete, with a bottom element. -/
noncomputable abbrev WellFoundedLT.conditionallyCompleteLinearOrderBot (α : Type*)
    [i₁ : LinearOrder α] [i₂ : OrderBot α] [h : WellFoundedLT α] :
    ConditionallyCompleteLinearOrderBot α :=
  { i₁, i₂, LinearOrder.toLattice with
    sInf := fun s => if hs : s.Nonempty then h.wf.min s hs else ⊥
    csInf_le := fun s a _ has => by
      have s_ne : s.Nonempty := ⟨a, has⟩
      simpa [s_ne] using not_lt.1 (h.wf.not_lt_min s s_ne has)
    le_csInf := fun s a hs has => by
      simp only [hs, dif_pos]
      exact has (h.wf.min_mem s hs)
    sSup := fun s => if hs : (upperBounds s).Nonempty then h.wf.min _ hs else ⊥
    le_csSup := fun s a hs has => by
      have h's : (upperBounds s).Nonempty := hs
      simp only [h's, dif_pos]
      exact h.wf.min_mem _ h's has
    csSup_le := fun s a _ has => by
      have h's : (upperBounds s).Nonempty := ⟨a, has⟩
      simp only [h's, dif_pos]
      simpa using h.wf.not_lt_min _ h's has
    csSup_empty := by simpa using eq_bot_iff.2 (not_lt.1 <| h.wf.not_lt_min _ _ <| mem_univ ⊥)
    csSup_of_not_bddAbove := by
      intro s H
      have B : ¬((upperBounds s).Nonempty) := H
      simp only [B, dite_false, upperBounds_empty, univ_nonempty, dite_true]
      exact le_antisymm bot_le (WellFounded.min_le _ (mem_univ _))
    csInf_of_not_bddBelow := fun s H ↦ (H (OrderBot.bddBelow s)).elim }

/-- Create a `ConditionallyCompleteLattice` from a `PartialOrder` and `sup` function
that returns the least upper bound of a nonempty set which is bounded above. Usually this
constructor provides poor definitional equalities.  If other fields are known explicitly, they
should be provided; for example, if `inf` is known explicitly, construct the
`ConditionallyCompleteLattice` instance as
```
instance : ConditionallyCompleteLattice my_T :=
  { inf := better_inf,
    le_inf := ...,
    inf_le_right := ...,
    inf_le_left := ...
    -- don't care to fix sup, sInf
    ..conditionallyCompleteLatticeOfsSup my_T _ }
```
-/
def conditionallyCompleteLatticeOfsSup (α : Type*) [H1 : PartialOrder α] [H2 : SupSet α]
    (bddAbove_pair : ∀ a b : α, BddAbove ({a, b} : Set α))
    (bddBelow_pair : ∀ a b : α, BddBelow ({a, b} : Set α))
    (isLUB_sSup : ∀ s : Set α, BddAbove s → s.Nonempty → IsLUB s (sSup s)) :
    ConditionallyCompleteLattice α :=
  { H1, H2 with
    sup := fun a b => sSup {a, b}
    le_sup_left := fun a b =>
      (isLUB_sSup {a, b} (bddAbove_pair a b) (insert_nonempty _ _)).1 (mem_insert _ _)
    le_sup_right := fun a b =>
      (isLUB_sSup {a, b} (bddAbove_pair a b) (insert_nonempty _ _)).1
        (mem_insert_of_mem _ (mem_singleton _))
    sup_le := fun a b _ hac hbc =>
      (isLUB_sSup {a, b} (bddAbove_pair a b) (insert_nonempty _ _)).2
        (forall_insert_of_forall (forall_eq.mpr hbc) hac)
    inf := fun a b => sSup (lowerBounds {a, b})
    inf_le_left := fun a b =>
      (isLUB_sSup (lowerBounds {a, b}) (Nonempty.bddAbove_lowerBounds ⟨a, mem_insert _ _⟩)
            (bddBelow_pair a b)).2
        fun _ hc => hc <| mem_insert _ _
    inf_le_right := fun a b =>
      (isLUB_sSup (lowerBounds {a, b}) (Nonempty.bddAbove_lowerBounds ⟨a, mem_insert _ _⟩)
            (bddBelow_pair a b)).2
        fun _ hc => hc <| mem_insert_of_mem _ (mem_singleton _)
    le_inf := fun c a b hca hcb =>
      (isLUB_sSup (lowerBounds {a, b}) (Nonempty.bddAbove_lowerBounds ⟨a, mem_insert _ _⟩)
            ⟨c, forall_insert_of_forall (forall_eq.mpr hcb) hca⟩).1
        (forall_insert_of_forall (forall_eq.mpr hcb) hca)
    sInf := fun s => sSup (lowerBounds s)
    csSup_le := fun s a hs ha => (isLUB_sSup s ⟨a, ha⟩ hs).2 ha
    le_csSup := fun s a hs ha => (isLUB_sSup s hs ⟨a, ha⟩).1 ha
    csInf_le := fun s a hs ha =>
      (isLUB_sSup (lowerBounds s) (Nonempty.bddAbove_lowerBounds ⟨a, ha⟩) hs).2 fun _ hb => hb ha
    le_csInf := fun s a hs ha =>
      (isLUB_sSup (lowerBounds s) hs.bddAbove_lowerBounds ⟨a, ha⟩).1 ha }

/-- Create a `ConditionallyCompleteLattice` from a `PartialOrder` and `inf` function
that returns the greatest lower bound of a nonempty set which is bounded below. Usually this
constructor provides poor definitional equalities.  If other fields are known explicitly, they
should be provided; for example, if `inf` is known explicitly, construct the
`ConditionallyCompleteLattice` instance as
```
instance : ConditionallyCompleteLattice my_T :=
  { inf := better_inf,
    le_inf := ...,
    inf_le_right := ...,
    inf_le_left := ...
    -- don't care to fix sup, sSup
    ..conditionallyCompleteLatticeOfsInf my_T _ }
```
-/
def conditionallyCompleteLatticeOfsInf (α : Type*) [H1 : PartialOrder α] [H2 : InfSet α]
    (bddAbove_pair : ∀ a b : α, BddAbove ({a, b} : Set α))
    (bddBelow_pair : ∀ a b : α, BddBelow ({a, b} : Set α))
    (isGLB_sInf : ∀ s : Set α, BddBelow s → s.Nonempty → IsGLB s (sInf s)) :
    ConditionallyCompleteLattice α :=
  { H1, H2 with
    inf := fun a b => sInf {a, b}
    inf_le_left := fun a b =>
      (isGLB_sInf {a, b} (bddBelow_pair a b) (insert_nonempty _ _)).1 (mem_insert _ _)
    inf_le_right := fun a b =>
      (isGLB_sInf {a, b} (bddBelow_pair a b) (insert_nonempty _ _)).1
        (mem_insert_of_mem _ (mem_singleton _))
    le_inf := fun _ a b hca hcb =>
      (isGLB_sInf {a, b} (bddBelow_pair a b) (insert_nonempty _ _)).2
        (forall_insert_of_forall (forall_eq.mpr hcb) hca)
    sup := fun a b => sInf (upperBounds {a, b})
    le_sup_left := fun a b =>
      (isGLB_sInf (upperBounds {a, b}) (Nonempty.bddBelow_upperBounds ⟨a, mem_insert _ _⟩)
            (bddAbove_pair a b)).2
        fun _ hc => hc <| mem_insert _ _
    le_sup_right := fun a b =>
      (isGLB_sInf (upperBounds {a, b}) (Nonempty.bddBelow_upperBounds ⟨a, mem_insert _ _⟩)
            (bddAbove_pair a b)).2
        fun _ hc => hc <| mem_insert_of_mem _ (mem_singleton _)
    sup_le := fun a b c hac hbc =>
      (isGLB_sInf (upperBounds {a, b}) (Nonempty.bddBelow_upperBounds ⟨a, mem_insert _ _⟩)
            ⟨c, forall_insert_of_forall (forall_eq.mpr hbc) hac⟩).1
        (forall_insert_of_forall (forall_eq.mpr hbc) hac)
    sSup := fun s => sInf (upperBounds s)
    le_csInf := fun s a hs ha => (isGLB_sInf s ⟨a, ha⟩ hs).2 ha
    csInf_le := fun s a hs ha => (isGLB_sInf s hs ⟨a, ha⟩).1 ha
    le_csSup := fun s a hs ha =>
      (isGLB_sInf (upperBounds s) (Nonempty.bddBelow_upperBounds ⟨a, ha⟩) hs).2 fun _ hb => hb ha
    csSup_le := fun s a hs ha =>
      (isGLB_sInf (upperBounds s) hs.bddBelow_upperBounds ⟨a, ha⟩).1 ha }

/-- A version of `conditionallyCompleteLatticeOfsSup` when we already know that `α` is a lattice.

This should only be used when it is both hard and unnecessary to provide `inf` explicitly. -/
def conditionallyCompleteLatticeOfLatticeOfsSup (α : Type*) [H1 : Lattice α] [SupSet α]
    (isLUB_sSup : ∀ s : Set α, BddAbove s → s.Nonempty → IsLUB s (sSup s)) :
    ConditionallyCompleteLattice α :=
  { H1,
    conditionallyCompleteLatticeOfsSup α
      (fun a b => ⟨a ⊔ b, forall_insert_of_forall (forall_eq.mpr le_sup_right) le_sup_left⟩)
      (fun a b => ⟨a ⊓ b, forall_insert_of_forall (forall_eq.mpr inf_le_right) inf_le_left⟩)
      isLUB_sSup with }

/-- A version of `conditionallyCompleteLatticeOfsInf` when we already know that `α` is a lattice.

This should only be used when it is both hard and unnecessary to provide `sup` explicitly. -/
def conditionallyCompleteLatticeOfLatticeOfsInf (α : Type*) [H1 : Lattice α] [InfSet α]
    (isGLB_sInf : ∀ s : Set α, BddBelow s → s.Nonempty → IsGLB s (sInf s)) :
    ConditionallyCompleteLattice α :=
  { H1,
    conditionallyCompleteLatticeOfsInf α
      (fun a b => ⟨a ⊔ b, forall_insert_of_forall (forall_eq.mpr le_sup_right) le_sup_left⟩)
      (fun a b => ⟨a ⊓ b, forall_insert_of_forall (forall_eq.mpr inf_le_right) inf_le_left⟩)
      isGLB_sInf with }
