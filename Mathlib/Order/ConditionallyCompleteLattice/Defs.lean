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

/-- A conditionally complete semilattice is a semilattice in which every nonempty subset which is
  bounded above has a least upper bound.

To differentiate the statements from the corresponding statements in (unconditional)
complete lattices, we prefix `sSup` by a `c` everywhere. The same statements should
hold in both worlds, sometimes with additional assumptions of nonemptiness or
boundedness. -/
class ConditionallyCompleteSemilatticeSup (α : Type*) extends SemilatticeSup α, SupSet α where
  /-- Every nonempty subset which is bounded above has a least upper bound. -/
  isLUB_csSup : ∀ s : Set α, s.Nonempty → BddAbove s → IsLUB s (sSup s)
  /-- If the lattice has a bottom element, then `sSup ∅` is the bottom element. -/
  csSup_empty : ∀ ⦃x⦄, IsBot x -> sSup ∅ = x

/-- A conditionally complete semilattice is a semilattice in which every nonempty subset which is
bounded below has a greatest lower bound.

To differentiate the statements from the corresponding statements in (unconditional)
complete lattices, we prefix `sInf` by a `c` everywhere. The same statements should
hold in both worlds, sometimes with additional assumptions of nonemptiness or
boundedness. -/
@[to_dual existing]
class ConditionallyCompleteSemilatticeInf (α : Type*) extends SemilatticeInf α, InfSet α where
  /-- Every nonempty subset which is bounded below has a greatest lower bound. -/
  isGLB_csInf : ∀ s : Set α, s.Nonempty → BddBelow s → IsGLB s (sInf s)
  /-- If the lattice has a top element, then `sInf ∅` is the top element. -/
  csInf_empty : ∀ ⦃x⦄, IsTop x -> sInf ∅ = x

attribute [to_dual existing] ConditionallyCompleteSemilatticeInf.isGLB_csInf
  ConditionallyCompleteSemilatticeInf.toSemilatticeInf
  ConditionallyCompleteSemilatticeInf.toInfSet

@[to_dual]
instance OrderDual.instConditionallyCompleteSemilatticeSup (α)
    [h : ConditionallyCompleteSemilatticeInf α] : ConditionallyCompleteSemilatticeSup αᵒᵈ where
  sSup := sInf (α := α)
  isLUB_csSup := h.isGLB_csInf (α := α)
  csSup_empty := h.csInf_empty (α := α)

@[to_dual]
theorem isGLB_csInf [ConditionallyCompleteSemilatticeInf α] {s : Set α} (hn : s.Nonempty)
    (hb : BddBelow s := by bddDefault) : IsGLB s (sInf s) :=
  ConditionallyCompleteSemilatticeInf.isGLB_csInf s hn hb

@[to_dual, simp]
theorem csSup_empty [ConditionallyCompleteSemilatticeSup α] {x : α} (h : IsBot x) : sSup ∅ = x :=
  ConditionallyCompleteSemilatticeSup.csSup_empty h

/-- A conditionally complete lattice is a lattice in which
every nonempty subset which is bounded above has a supremum, and
every nonempty subset which is bounded below has an infimum.
Typical examples are real numbers or natural numbers.

To differentiate the statements from the corresponding statements in (unconditional)
complete lattices, we prefix `sInf` and `sSup` by a `c` everywhere. The same statements should
hold in both worlds, sometimes with additional assumptions of nonemptiness or
boundedness. -/
class ConditionallyCompleteLattice (α : Type*) extends
  ConditionallyCompleteSemilatticeSup α, ConditionallyCompleteSemilatticeInf α

attribute [to_dual existing] ConditionallyCompleteLattice.toConditionallyCompleteSemilatticeInf

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

/-- Create a `ConditionallyCompleteSemilatticeInf` from a `PartialOrder` and `sInf` function
that returns the greatest lower bound of a nonempty set which is bounded below. Usually this
constructor provides poor definitional equalities.  If other fields are known explicitly, they
should be provided. -/
@[to_dual (attr := implicit_reducible)
/-- Create a `ConditionallyCompleteSemilatticeSup` from a `PartialOrder` and `sSup` function
that returns the least upper bound of a nonempty set which is bounded above. Usually this
constructor provides poor definitional equalities.  If other fields are known explicitly, they
should be provided. -/]
def conditionallyCompleteSemilatticeInfOfsInf (α : Type*) [H1 : PartialOrder α] [H2 : InfSet α]
    (bddBelow_pair : ∀ a b : α, BddBelow ({a, b} : Set α))
    (isGLB_sInf : ∀ s : Set α, BddBelow s → s.Nonempty → IsGLB s (sInf s))
    (csInf_empty : ∀ ⦃x : α⦄, IsTop x -> sInf ∅ = x):
    ConditionallyCompleteSemilatticeInf α where
  __ := H2
  __ := SemilatticeInf.ofIsGLB (fun a b ↦ sInf {a, b})
    (fun a b ↦ isGLB_sInf {a, b} (bddBelow_pair a b) (insert_nonempty _ _))
  isGLB_csInf _ hn hb := isGLB_sInf _ hb hn
  csInf_empty := csInf_empty

/-- Create a `ConditionallyCompleteSemilatticeInfBot` from a `PartialOrder`, `OrderBot` and `sInf`
function that returns the greatest lower bound of a nonempty set. Usually this constructor provides
poor definitional equalities.  If other fields are known explicitly, they should be provided. -/
@[to_dual (attr := implicit_reducible)
/-- Create a `ConditionallyCompleteSemilatticeSupTop` from a `PartialOrder`, `OrderTop` and `sSup`
function that returns the least upper bound of a nonempty set. Usually this constructor provides
poor definitional equalities.  If other fields are known explicitly, they should be provided. -/]
def conditionallyCompleteSemilatticeInfOfsInfTop (α : Type*) [PartialOrder α] [H1 : InfSet α]
    [H2 : OrderTop α] (sInf_empty : sInf ∅ = (⊤ : α))
    (isGLB_sInf : ∀ s : Set α, s.Nonempty → IsGLB s (sInf s)) :
    ConditionallyCompleteSemilatticeInf α where
  __ := H1
  __ := H2
  __ := SemilatticeInf.ofIsGLB (fun a b ↦ sInf {a, b})
    (fun a b ↦ isGLB_sInf {a, b} (insert_nonempty _ _))
  isGLB_csInf _ hn _ := isGLB_sInf _ hn
  csInf_empty _ hx := hx.eq_top ▸ sInf_empty

/-- Create a `ConditionallyCompleteLattice` from a `PartialOrder` and `sSup` function
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
@[to_dual (attr := implicit_reducible)
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
def conditionallyCompleteLatticeOfsSup (α : Type*) [H1 : PartialOrder α] [H2 : SupSet α]
    (bddAbove_pair : ∀ a b : α, BddAbove ({a, b} : Set α))
    (bddBelow_pair : ∀ a b : α, BddBelow ({a, b} : Set α))
    (isLUB_sSup : ∀ s : Set α, BddAbove s → s.Nonempty → IsLUB s (sSup s))
    (csSup_empty : ∀ ⦃x : α⦄, IsBot x -> sSup ∅ = x) :
    ConditionallyCompleteLattice α where
  __ := Lattice.ofIsLUBofIsGLB (fun a b ↦ sSup {a, b}) (fun a b ↦ sSup (lowerBounds {a, b}))
    (fun a b ↦ isLUB_sSup {a, b} (bddAbove_pair a b) (insert_nonempty _ _))
    (fun a b ↦ isLUB_lowerBounds.mp <| isLUB_sSup (lowerBounds {a, b})
      (insert_nonempty _ _).bddAbove_lowerBounds (bddBelow_pair a b))
  __ := H2
  sInf s := sSup (lowerBounds s)
  isLUB_csSup _ hn hb := isLUB_sSup _ hb hn
  isGLB_csInf _ hn hb := isLUB_lowerBounds.mp (isLUB_sSup _ hn.bddAbove_lowerBounds hb)
  csSup_empty := csSup_empty
  csInf_empty x hx := by
    rw [lowerBounds_empty]
    exact isLUB_sSup univ ⟨x, fun ⦃a⦄ a_1 ↦ hx a⟩ ⟨x, mem_univ x⟩ |>.isLeast_iff_eq.mp
      ⟨fun ⦃a⦄ a_1 ↦ hx a, fun y hy ↦ hy <| mem_univ x⟩

/-- A version of `conditionallyCompleteLatticeOfsSup` when we already know that `α` is a lattice.

This should only be used when it is both hard and unnecessary to provide `sInf` explicitly. -/
@[to_dual (attr := implicit_reducible)
/-- A version of `conditionallyCompleteLatticeOfsInf` when we already know that `α` is a lattice.

This should only be used when it is both hard and unnecessary to provide `sSup` explicitly. -/]
def conditionallyCompleteLatticeOfLatticeOfsSup (α : Type*) [H1 : Lattice α] [SupSet α]
    (isLUB_sSup : ∀ s : Set α, BddAbove s → s.Nonempty → IsLUB s (sSup s))
    (csSup_empty : ∀ ⦃x : α⦄, IsBot x -> sSup ∅ = x) : ConditionallyCompleteLattice α :=
  {__ := H1,
   __ := conditionallyCompleteLatticeOfsSup α
    (fun a b => ⟨a ⊔ b, forall_insert_of_forall (forall_eq.mpr le_sup_right) le_sup_left⟩)
    (fun a b => ⟨a ⊓ b, forall_insert_of_forall (forall_eq.mpr inf_le_right) inf_le_left⟩)
    isLUB_sSup csSup_empty}

open scoped Classical in
/-- A well-founded linear order is conditionally complete, with a bottom element. -/
noncomputable abbrev WellFoundedLT.conditionallyCompleteLinearOrderBot (α : Type*)
    [i₁ : LinearOrder α] [i₂ : OrderBot α] [h : WellFoundedLT α] :
    ConditionallyCompleteLinearOrderBot α where
  __ := i₁
  __ := i₂
  __ := LinearOrder.toLattice
  __ :=
    letI : InfSet α := ⟨fun s => if hs : s.Nonempty then h.wf.min s hs else ⊥⟩
    conditionallyCompleteLatticeOfLatticeOfsInf _ fun s _ hn ↦ by
      simp only [dif_pos hn]
      exact IsLeast.isGLB ⟨h.wf.min_mem s hn, fun _ hx ↦ h.wf.min_le hx⟩
  csSup_empty := by simp [sSup, bot_unique (WellFounded.min_le _ (mem_univ _))]
  csSup_of_not_bddAbove s H := by
    rw [BddAbove] at H
    simp [sSup, H, bot_unique (WellFounded.min_le _ (mem_univ _))]
  csInf_of_not_bddBelow s H := (H (OrderBot.bddBelow s)).elim
