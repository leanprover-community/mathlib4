/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.WellFounded
import Mathlib.Data.Set.Image
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Data.Set.Lattice

/-!
# Theory of conditionally complete lattices.

A conditionally complete lattice is a lattice in which every non-empty bounded subset `s`
has a least upper bound and a greatest lower bound, denoted below by `sSup s` and `sInf s`.
Typical examples are `ℝ`, `ℕ`, and `ℤ` with their usual orders.

The theory is very comparable to the theory of complete lattices, except that suitable
boundedness and nonemptiness assumptions have to be added to most statements.
We introduce two predicates `BddAbove` and `BddBelow` to express this boundedness, prove
their basic properties, and then go on to prove most useful properties of `sSup` and `sInf`
in conditionally complete lattices.

To differentiate the statements between complete lattices and conditionally complete
lattices, we prefix `sInf` and `sSup` in the statements by `c`, giving `csInf` and `csSup`.
For instance, `sInf_le` is a statement in complete lattices ensuring `sInf s ≤ x`,
while `csInf_le` is the same statement in conditionally complete lattices
with an additional assumption that `s` is bounded below.
-/

-- Guard against import creep
assert_not_exists Multiset


open Function OrderDual Set

variable {α β γ : Type*} {ι : Sort*}

section

/-!
Extension of `sSup` and `sInf` from a preorder `α` to `WithTop α` and `WithBot α`
-/

variable [Preorder α]

open Classical in
noncomputable instance WithTop.instSupSet [SupSet α] :
    SupSet (WithTop α) :=
  ⟨fun S =>
    if ⊤ ∈ S then ⊤ else if BddAbove ((fun (a : α) ↦ ↑a) ⁻¹' S : Set α) then
      ↑(sSup ((fun (a : α) ↦ (a : WithTop α)) ⁻¹' S : Set α)) else ⊤⟩

open Classical in
noncomputable instance WithTop.instInfSet [InfSet α] : InfSet (WithTop α) :=
  ⟨fun S => if S ⊆ {⊤} ∨ ¬BddBelow S then ⊤ else ↑(sInf ((fun (a : α) ↦ ↑a) ⁻¹' S : Set α))⟩

noncomputable instance WithBot.instSupSet [SupSet α] : SupSet (WithBot α) :=
  ⟨(WithTop.instInfSet (α := αᵒᵈ)).sInf⟩

noncomputable instance WithBot.instInfSet [InfSet α] :
    InfSet (WithBot α) :=
  ⟨(WithTop.instSupSet (α := αᵒᵈ)).sSup⟩

theorem WithTop.sSup_eq [SupSet α] {s : Set (WithTop α)} (hs : ⊤ ∉ s)
    (hs' : BddAbove ((↑) ⁻¹' s : Set α)) : sSup s = ↑(sSup ((↑) ⁻¹' s) : α) :=
  (if_neg hs).trans <| if_pos hs'

theorem WithTop.sInf_eq [InfSet α] {s : Set (WithTop α)} (hs : ¬s ⊆ {⊤}) (h's : BddBelow s) :
    sInf s = ↑(sInf ((↑) ⁻¹' s) : α) :=
  if_neg <| by simp [hs, h's]

theorem WithBot.sInf_eq [InfSet α] {s : Set (WithBot α)} (hs : ⊥ ∉ s)
    (hs' : BddBelow ((↑) ⁻¹' s : Set α)) : sInf s = ↑(sInf ((↑) ⁻¹' s) : α) :=
  (if_neg hs).trans <| if_pos hs'

theorem WithBot.sSup_eq [SupSet α] {s : Set (WithBot α)} (hs : ¬s ⊆ {⊥}) (h's : BddAbove s) :
    sSup s = ↑(sSup ((↑) ⁻¹' s) : α) :=
  WithTop.sInf_eq (α := αᵒᵈ) hs h's

@[simp]
theorem WithTop.sInf_empty [InfSet α] : sInf (∅ : Set (WithTop α)) = ⊤ :=
  if_pos <| by simp

@[simp]
theorem WithTop.iInf_empty [IsEmpty ι] [InfSet α] (f : ι → WithTop α) :
    ⨅ i, f i = ⊤ := by rw [iInf, range_eq_empty, WithTop.sInf_empty]

theorem WithTop.coe_sInf' [InfSet α] {s : Set α} (hs : s.Nonempty) (h's : BddBelow s) :
    ↑(sInf s) = (sInf ((fun (a : α) ↦ ↑a) '' s) : WithTop α) := by
  classical
  obtain ⟨x, hx⟩ := hs
  change _ = ite _ _ _
  split_ifs with h
  · rcases h with h1 | h2
    · cases h1 (mem_image_of_mem _ hx)
    · exact (h2 (Monotone.map_bddBelow coe_mono h's)).elim
  · rw [preimage_image_eq]
    exact Option.some_injective _

@[norm_cast]
theorem WithTop.coe_iInf [Nonempty ι] [InfSet α] {f : ι → α} (hf : BddBelow (range f)) :
    ↑(⨅ i, f i) = (⨅ i, f i : WithTop α) := by
  rw [iInf, iInf, WithTop.coe_sInf' (range_nonempty f) hf, ← range_comp, Function.comp_def]

theorem WithTop.coe_sSup' [SupSet α] {s : Set α} (hs : BddAbove s) :
    ↑(sSup s) = (sSup ((fun (a : α) ↦ ↑a) '' s) : WithTop α) := by
  classical
  change _ = ite _ _ _
  rw [if_neg, preimage_image_eq, if_pos hs]
  · exact Option.some_injective _
  · rintro ⟨x, _, ⟨⟩⟩

@[norm_cast]
theorem WithTop.coe_iSup [SupSet α] (f : ι → α) (h : BddAbove (Set.range f)) :
    ↑(⨆ i, f i) = (⨆ i, f i : WithTop α) := by
  rw [iSup, iSup, WithTop.coe_sSup' h, ← range_comp, Function.comp_def]

@[simp]
theorem WithBot.sSup_empty [SupSet α] : sSup (∅ : Set (WithBot α)) = ⊥ :=
  WithTop.sInf_empty (α := αᵒᵈ)

@[deprecated (since := "2024-06-10")] alias WithBot.csSup_empty := WithBot.sSup_empty

@[simp]
theorem WithBot.ciSup_empty [IsEmpty ι] [SupSet α] (f : ι → WithBot α) :
    ⨆ i, f i = ⊥ :=
  WithTop.iInf_empty (α := αᵒᵈ) _

@[norm_cast]
theorem WithBot.coe_sSup' [SupSet α] {s : Set α} (hs : s.Nonempty) (h's : BddAbove s) :
    ↑(sSup s) = (sSup ((fun (a : α) ↦ ↑a) '' s) : WithBot α) :=
  WithTop.coe_sInf' (α := αᵒᵈ) hs h's

@[norm_cast]
theorem WithBot.coe_iSup [Nonempty ι] [SupSet α] {f : ι → α} (hf : BddAbove (range f)) :
    ↑(⨆ i, f i) = (⨆ i, f i : WithBot α) :=
  WithTop.coe_iInf (α := αᵒᵈ) hf

@[norm_cast]
theorem WithBot.coe_sInf' [InfSet α] {s : Set α} (hs : BddBelow s) :
    ↑(sInf s) = (sInf ((fun (a : α) ↦ ↑a) '' s) : WithBot α) :=
  WithTop.coe_sSup' (α := αᵒᵈ) hs

@[norm_cast]
theorem WithBot.coe_iInf [InfSet α] (f : ι → α) (h : BddBelow (Set.range f)) :
    ↑(⨅ i, f i) = (⨅ i, f i : WithBot α) :=
  WithTop.coe_iSup (α := αᵒᵈ) _ h

end

/-- A conditionally complete lattice is a lattice in which
every nonempty subset which is bounded above has a supremum, and
every nonempty subset which is bounded below has an infimum.
Typical examples are real numbers or natural numbers.

To differentiate the statements from the corresponding statements in (unconditional)
complete lattices, we prefix sInf and subₛ by a c everywhere. The same statements should
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

-- Porting note: mathlib3 used `renaming`
/-- A conditionally complete linear order is a linear order in which
every nonempty subset which is bounded above has a supremum, and
every nonempty subset which is bounded below has an infimum.
Typical examples are real numbers or natural numbers.

To differentiate the statements from the corresponding statements in (unconditional)
complete linear orders, we prefix sInf and sSup by a c everywhere. The same statements should
hold in both worlds, sometimes with additional assumptions of nonemptiness or
boundedness. -/
class ConditionallyCompleteLinearOrder (α : Type*) extends ConditionallyCompleteLattice α where
  /-- A `ConditionallyCompleteLinearOrder` is total. -/
  le_total (a b : α) : a ≤ b ∨ b ≤ a
  /-- In a `ConditionallyCompleteLinearOrder`, we assume the order relations are all decidable. -/
  decidableLE : DecidableRel (· ≤ · : α → α → Prop)
  /-- In a `ConditionallyCompleteLinearOrder`, we assume the order relations are all decidable. -/
  decidableEq : DecidableEq α := @decidableEqOfDecidableLE _ _ decidableLE
  /-- In a `ConditionallyCompleteLinearOrder`, we assume the order relations are all decidable. -/
  decidableLT : DecidableRel (· < · : α → α → Prop) :=
    @decidableLTOfDecidableLE _ _ decidableLE
  /-- If a set is not bounded above, its supremum is by convention `sSup ∅`. -/
  csSup_of_not_bddAbove : ∀ s, ¬BddAbove s → sSup s = sSup (∅ : Set α)
  /-- If a set is not bounded below, its infimum is by convention `sInf ∅`. -/
  csInf_of_not_bddBelow : ∀ s, ¬BddBelow s → sInf s = sInf (∅ : Set α)

instance ConditionallyCompleteLinearOrder.toLinearOrder [ConditionallyCompleteLinearOrder α] :
    LinearOrder α :=
  { ‹ConditionallyCompleteLinearOrder α› with
    max := Sup.sup, min := Inf.inf,
    min_def := fun a b ↦ by
      by_cases hab : a = b
      · simp [hab]
      · rcases ConditionallyCompleteLinearOrder.le_total a b with (h₁ | h₂)
        · simp [h₁]
        · simp [show ¬(a ≤ b) from fun h => hab (le_antisymm h h₂), h₂]
    max_def := fun a b ↦ by
      by_cases hab : a = b
      · simp [hab]
      · rcases ConditionallyCompleteLinearOrder.le_total a b with (h₁ | h₂)
        · simp [h₁]
        · simp [show ¬(a ≤ b) from fun h => hab (le_antisymm h h₂), h₂] }

/-- A conditionally complete linear order with `Bot` is a linear order with least element, in which
every nonempty subset which is bounded above has a supremum, and every nonempty subset (necessarily
bounded below) has an infimum.  A typical example is the natural numbers.

To differentiate the statements from the corresponding statements in (unconditional)
complete linear orders, we prefix `sInf` and `sSup` by a c everywhere. The same statements should
hold in both worlds, sometimes with additional assumptions of nonemptiness or
boundedness. -/
class ConditionallyCompleteLinearOrderBot (α : Type*) extends ConditionallyCompleteLinearOrder α,
  Bot α where
  /-- `⊥` is the least element -/
  bot_le : ∀ x : α, ⊥ ≤ x
  /-- The supremum of the empty set is `⊥` -/
  csSup_empty : sSup ∅ = ⊥

-- see Note [lower instance priority]
instance (priority := 100) ConditionallyCompleteLinearOrderBot.toOrderBot
    [h : ConditionallyCompleteLinearOrderBot α] : OrderBot α :=
  { h with }

-- see Note [lower instance priority]
/-- A complete lattice is a conditionally complete lattice, as there are no restrictions
on the properties of sInf and sSup in a complete lattice. -/
instance (priority := 100) CompleteLattice.toConditionallyCompleteLattice [CompleteLattice α] :
    ConditionallyCompleteLattice α :=
  { ‹CompleteLattice α› with
    le_csSup := by intros; apply le_sSup; assumption
    csSup_le := by intros; apply sSup_le; assumption
    csInf_le := by intros; apply sInf_le; assumption
    le_csInf := by intros; apply le_sInf; assumption }

-- see Note [lower instance priority]
instance (priority := 100) CompleteLinearOrder.toConditionallyCompleteLinearOrderBot {α : Type*}
    [h : CompleteLinearOrder α] : ConditionallyCompleteLinearOrderBot α :=
  { CompleteLattice.toConditionallyCompleteLattice, h with
    csSup_empty := sSup_empty
    csSup_of_not_bddAbove := fun s H ↦ (H (OrderTop.bddAbove s)).elim
    csInf_of_not_bddBelow := fun s H ↦ (H (OrderBot.bddBelow s)).elim }

open scoped Classical in
/-- A well founded linear order is conditionally complete, with a bottom element. -/
noncomputable abbrev IsWellOrder.conditionallyCompleteLinearOrderBot (α : Type*)
  [i₁ : _root_.LinearOrder α] [i₂ : OrderBot α] [h : IsWellOrder α (· < ·)] :
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

namespace OrderDual

instance instConditionallyCompleteLattice (α : Type*) [ConditionallyCompleteLattice α] :
    ConditionallyCompleteLattice αᵒᵈ :=
  { OrderDual.instInf α, OrderDual.instSup α, OrderDual.instLattice α with
    le_csSup := ConditionallyCompleteLattice.csInf_le (α := α)
    csSup_le := ConditionallyCompleteLattice.le_csInf (α := α)
    le_csInf := ConditionallyCompleteLattice.csSup_le (α := α)
    csInf_le := ConditionallyCompleteLattice.le_csSup (α := α) }

instance (α : Type*) [ConditionallyCompleteLinearOrder α] : ConditionallyCompleteLinearOrder αᵒᵈ :=
  { OrderDual.instConditionallyCompleteLattice α, OrderDual.instLinearOrder α with
    csSup_of_not_bddAbove := ConditionallyCompleteLinearOrder.csInf_of_not_bddBelow (α := α)
    csInf_of_not_bddBelow := ConditionallyCompleteLinearOrder.csSup_of_not_bddAbove (α := α) }

end OrderDual

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

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice α] {s t : Set α} {a b : α}

theorem le_csSup (h₁ : BddAbove s) (h₂ : a ∈ s) : a ≤ sSup s :=
  ConditionallyCompleteLattice.le_csSup s a h₁ h₂

theorem csSup_le (h₁ : s.Nonempty) (h₂ : ∀ b ∈ s, b ≤ a) : sSup s ≤ a :=
  ConditionallyCompleteLattice.csSup_le s a h₁ h₂

theorem csInf_le (h₁ : BddBelow s) (h₂ : a ∈ s) : sInf s ≤ a :=
  ConditionallyCompleteLattice.csInf_le s a h₁ h₂

theorem le_csInf (h₁ : s.Nonempty) (h₂ : ∀ b ∈ s, a ≤ b) : a ≤ sInf s :=
  ConditionallyCompleteLattice.le_csInf s a h₁ h₂

theorem le_csSup_of_le (hs : BddAbove s) (hb : b ∈ s) (h : a ≤ b) : a ≤ sSup s :=
  le_trans h (le_csSup hs hb)

theorem csInf_le_of_le (hs : BddBelow s) (hb : b ∈ s) (h : b ≤ a) : sInf s ≤ a :=
  le_trans (csInf_le hs hb) h

theorem csSup_le_csSup (ht : BddAbove t) (hs : s.Nonempty) (h : s ⊆ t) : sSup s ≤ sSup t :=
  csSup_le hs fun _ ha => le_csSup ht (h ha)

theorem csInf_le_csInf (ht : BddBelow t) (hs : s.Nonempty) (h : s ⊆ t) : sInf t ≤ sInf s :=
  le_csInf hs fun _ ha => csInf_le ht (h ha)

theorem le_csSup_iff (h : BddAbove s) (hs : s.Nonempty) :
    a ≤ sSup s ↔ ∀ b, b ∈ upperBounds s → a ≤ b :=
  ⟨fun h _ hb => le_trans h (csSup_le hs hb), fun hb => hb _ fun _ => le_csSup h⟩

theorem csInf_le_iff (h : BddBelow s) (hs : s.Nonempty) : sInf s ≤ a ↔ ∀ b ∈ lowerBounds s, b ≤ a :=
  ⟨fun h _ hb => le_trans (le_csInf hs hb) h, fun hb => hb _ fun _ => csInf_le h⟩

theorem isLUB_csSup (ne : s.Nonempty) (H : BddAbove s) : IsLUB s (sSup s) :=
  ⟨fun _ => le_csSup H, fun _ => csSup_le ne⟩

theorem isLUB_ciSup [Nonempty ι] {f : ι → α} (H : BddAbove (range f)) :
    IsLUB (range f) (⨆ i, f i) :=
  isLUB_csSup (range_nonempty f) H

theorem isLUB_ciSup_set {f : β → α} {s : Set β} (H : BddAbove (f '' s)) (Hne : s.Nonempty) :
    IsLUB (f '' s) (⨆ i : s, f i) := by
  rw [← sSup_image']
  exact isLUB_csSup (Hne.image _) H

theorem isGLB_csInf (ne : s.Nonempty) (H : BddBelow s) : IsGLB s (sInf s) :=
  ⟨fun _ => csInf_le H, fun _ => le_csInf ne⟩

theorem isGLB_ciInf [Nonempty ι] {f : ι → α} (H : BddBelow (range f)) :
    IsGLB (range f) (⨅ i, f i) :=
  isGLB_csInf (range_nonempty f) H

theorem isGLB_ciInf_set {f : β → α} {s : Set β} (H : BddBelow (f '' s)) (Hne : s.Nonempty) :
    IsGLB (f '' s) (⨅ i : s, f i) :=
  isLUB_ciSup_set (α := αᵒᵈ) H Hne

theorem ciSup_le_iff [Nonempty ι] {f : ι → α} {a : α} (hf : BddAbove (range f)) :
    iSup f ≤ a ↔ ∀ i, f i ≤ a :=
  (isLUB_le_iff <| isLUB_ciSup hf).trans forall_mem_range

theorem le_ciInf_iff [Nonempty ι] {f : ι → α} {a : α} (hf : BddBelow (range f)) :
    a ≤ iInf f ↔ ∀ i, a ≤ f i :=
  (le_isGLB_iff <| isGLB_ciInf hf).trans forall_mem_range

theorem ciSup_set_le_iff {ι : Type*} {s : Set ι} {f : ι → α} {a : α} (hs : s.Nonempty)
    (hf : BddAbove (f '' s)) : ⨆ i : s, f i ≤ a ↔ ∀ i ∈ s, f i ≤ a :=
  (isLUB_le_iff <| isLUB_ciSup_set hf hs).trans forall_mem_image

theorem le_ciInf_set_iff {ι : Type*} {s : Set ι} {f : ι → α} {a : α} (hs : s.Nonempty)
    (hf : BddBelow (f '' s)) : (a ≤ ⨅ i : s, f i) ↔ ∀ i ∈ s, a ≤ f i :=
  (le_isGLB_iff <| isGLB_ciInf_set hf hs).trans forall_mem_image

theorem IsLUB.csSup_eq (H : IsLUB s a) (ne : s.Nonempty) : sSup s = a :=
  (isLUB_csSup ne ⟨a, H.1⟩).unique H

theorem IsLUB.ciSup_eq [Nonempty ι] {f : ι → α} (H : IsLUB (range f) a) : ⨆ i, f i = a :=
  H.csSup_eq (range_nonempty f)

theorem IsLUB.ciSup_set_eq {s : Set β} {f : β → α} (H : IsLUB (f '' s) a) (Hne : s.Nonempty) :
    ⨆ i : s, f i = a :=
  IsLUB.csSup_eq (image_eq_range f s ▸ H) (image_eq_range f s ▸ Hne.image f)

/-- A greatest element of a set is the supremum of this set. -/
theorem IsGreatest.csSup_eq (H : IsGreatest s a) : sSup s = a :=
  H.isLUB.csSup_eq H.nonempty

theorem IsGreatest.csSup_mem (H : IsGreatest s a) : sSup s ∈ s :=
  H.csSup_eq.symm ▸ H.1

theorem IsGLB.csInf_eq (H : IsGLB s a) (ne : s.Nonempty) : sInf s = a :=
  (isGLB_csInf ne ⟨a, H.1⟩).unique H

theorem IsGLB.ciInf_eq [Nonempty ι] {f : ι → α} (H : IsGLB (range f) a) : ⨅ i, f i = a :=
  H.csInf_eq (range_nonempty f)

theorem IsGLB.ciInf_set_eq {s : Set β} {f : β → α} (H : IsGLB (f '' s) a) (Hne : s.Nonempty) :
    ⨅ i : s, f i = a :=
  IsGLB.csInf_eq (image_eq_range f s ▸ H) (image_eq_range f s ▸ Hne.image f)

/-- A least element of a set is the infimum of this set. -/
theorem IsLeast.csInf_eq (H : IsLeast s a) : sInf s = a :=
  H.isGLB.csInf_eq H.nonempty

theorem IsLeast.csInf_mem (H : IsLeast s a) : sInf s ∈ s :=
  H.csInf_eq.symm ▸ H.1

theorem subset_Icc_csInf_csSup (hb : BddBelow s) (ha : BddAbove s) : s ⊆ Icc (sInf s) (sSup s) :=
  fun _ hx => ⟨csInf_le hb hx, le_csSup ha hx⟩

theorem csSup_le_iff (hb : BddAbove s) (hs : s.Nonempty) : sSup s ≤ a ↔ ∀ b ∈ s, b ≤ a :=
  isLUB_le_iff (isLUB_csSup hs hb)

theorem le_csInf_iff (hb : BddBelow s) (hs : s.Nonempty) : a ≤ sInf s ↔ ∀ b ∈ s, a ≤ b :=
  le_isGLB_iff (isGLB_csInf hs hb)

theorem csSup_lower_bounds_eq_csInf {s : Set α} (h : BddBelow s) (hs : s.Nonempty) :
    sSup (lowerBounds s) = sInf s :=
  (isLUB_csSup h <| hs.mono fun _ hx _ hy => hy hx).unique (isGLB_csInf hs h).isLUB

theorem csInf_upper_bounds_eq_csSup {s : Set α} (h : BddAbove s) (hs : s.Nonempty) :
    sInf (upperBounds s) = sSup s :=
  (isGLB_csInf h <| hs.mono fun _ hx _ hy => hy hx).unique (isLUB_csSup hs h).isGLB

theorem not_mem_of_lt_csInf {x : α} {s : Set α} (h : x < sInf s) (hs : BddBelow s) : x ∉ s :=
  fun hx => lt_irrefl _ (h.trans_le (csInf_le hs hx))

theorem not_mem_of_csSup_lt {x : α} {s : Set α} (h : sSup s < x) (hs : BddAbove s) : x ∉ s :=
  not_mem_of_lt_csInf (α := αᵒᵈ) h hs

/-- Introduction rule to prove that `b` is the supremum of `s`: it suffices to check that `b`
is larger than all elements of `s`, and that this is not the case of any `w<b`.
See `sSup_eq_of_forall_le_of_forall_lt_exists_gt` for a version in complete lattices. -/
theorem csSup_eq_of_forall_le_of_forall_lt_exists_gt (hs : s.Nonempty) (H : ∀ a ∈ s, a ≤ b)
    (H' : ∀ w, w < b → ∃ a ∈ s, w < a) : sSup s = b :=
  (eq_of_le_of_not_lt (csSup_le hs H)) fun hb =>
    let ⟨_, ha, ha'⟩ := H' _ hb
    lt_irrefl _ <| ha'.trans_le <| le_csSup ⟨b, H⟩ ha

/-- Introduction rule to prove that `b` is the infimum of `s`: it suffices to check that `b`
is smaller than all elements of `s`, and that this is not the case of any `w>b`.
See `sInf_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in complete lattices. -/
theorem csInf_eq_of_forall_ge_of_forall_gt_exists_lt :
    s.Nonempty → (∀ a ∈ s, b ≤ a) → (∀ w, b < w → ∃ a ∈ s, a < w) → sInf s = b :=
  csSup_eq_of_forall_le_of_forall_lt_exists_gt (α := αᵒᵈ)

/-- `b < sSup s` when there is an element `a` in `s` with `b < a`, when `s` is bounded above.
This is essentially an iff, except that the assumptions for the two implications are
slightly different (one needs boundedness above for one direction, nonemptiness and linear
order for the other one), so we formulate separately the two implications, contrary to
the `CompleteLattice` case. -/
theorem lt_csSup_of_lt (hs : BddAbove s) (ha : a ∈ s) (h : b < a) : b < sSup s :=
  lt_of_lt_of_le h (le_csSup hs ha)

/-- `sInf s < b` when there is an element `a` in `s` with `a < b`, when `s` is bounded below.
This is essentially an iff, except that the assumptions for the two implications are
slightly different (one needs boundedness below for one direction, nonemptiness and linear
order for the other one), so we formulate separately the two implications, contrary to
the `CompleteLattice` case. -/
theorem csInf_lt_of_lt : BddBelow s → a ∈ s → a < b → sInf s < b :=
  lt_csSup_of_lt (α := αᵒᵈ)

/-- If all elements of a nonempty set `s` are less than or equal to all elements
of a nonempty set `t`, then there exists an element between these sets. -/
theorem exists_between_of_forall_le (sne : s.Nonempty) (tne : t.Nonempty)
    (hst : ∀ x ∈ s, ∀ y ∈ t, x ≤ y) : (upperBounds s ∩ lowerBounds t).Nonempty :=
  ⟨sInf t, fun x hx => le_csInf tne <| hst x hx, fun _ hy => csInf_le (sne.mono hst) hy⟩

/-- The supremum of a singleton is the element of the singleton-/
@[simp]
theorem csSup_singleton (a : α) : sSup {a} = a :=
  isGreatest_singleton.csSup_eq

/-- The infimum of a singleton is the element of the singleton-/
@[simp]
theorem csInf_singleton (a : α) : sInf {a} = a :=
  isLeast_singleton.csInf_eq

@[simp]
theorem csSup_pair (a b : α) : sSup {a, b} = a ⊔ b :=
  (@isLUB_pair _ _ a b).csSup_eq (insert_nonempty _ _)

@[simp]
theorem csInf_pair (a b : α) : sInf {a, b} = a ⊓ b :=
  (@isGLB_pair _ _ a b).csInf_eq (insert_nonempty _ _)

/-- If a set is bounded below and above, and nonempty, its infimum is less than or equal to
its supremum. -/
theorem csInf_le_csSup (hb : BddBelow s) (ha : BddAbove s) (ne : s.Nonempty) : sInf s ≤ sSup s :=
  isGLB_le_isLUB (isGLB_csInf ne hb) (isLUB_csSup ne ha) ne

/-- The `sSup` of a union of two sets is the max of the suprema of each subset, under the
assumptions that all sets are bounded above and nonempty. -/
theorem csSup_union (hs : BddAbove s) (sne : s.Nonempty) (ht : BddAbove t) (tne : t.Nonempty) :
    sSup (s ∪ t) = sSup s ⊔ sSup t :=
  ((isLUB_csSup sne hs).union (isLUB_csSup tne ht)).csSup_eq sne.inl

/-- The `sInf` of a union of two sets is the min of the infima of each subset, under the assumptions
that all sets are bounded below and nonempty. -/
theorem csInf_union (hs : BddBelow s) (sne : s.Nonempty) (ht : BddBelow t) (tne : t.Nonempty) :
    sInf (s ∪ t) = sInf s ⊓ sInf t :=
  csSup_union (α := αᵒᵈ) hs sne ht tne

/-- The supremum of an intersection of two sets is bounded by the minimum of the suprema of each
set, if all sets are bounded above and nonempty. -/
theorem csSup_inter_le (hs : BddAbove s) (ht : BddAbove t) (hst : (s ∩ t).Nonempty) :
    sSup (s ∩ t) ≤ sSup s ⊓ sSup t :=
  (csSup_le hst) fun _ hx => le_inf (le_csSup hs hx.1) (le_csSup ht hx.2)

/-- The infimum of an intersection of two sets is bounded below by the maximum of the
infima of each set, if all sets are bounded below and nonempty. -/
theorem le_csInf_inter :
    BddBelow s → BddBelow t → (s ∩ t).Nonempty → sInf s ⊔ sInf t ≤ sInf (s ∩ t) :=
  csSup_inter_le (α := αᵒᵈ)

/-- The supremum of `insert a s` is the maximum of `a` and the supremum of `s`, if `s` is
nonempty and bounded above. -/
theorem csSup_insert (hs : BddAbove s) (sne : s.Nonempty) : sSup (insert a s) = a ⊔ sSup s :=
  ((isLUB_csSup sne hs).insert a).csSup_eq (insert_nonempty a s)

/-- The infimum of `insert a s` is the minimum of `a` and the infimum of `s`, if `s` is
nonempty and bounded below. -/
theorem csInf_insert (hs : BddBelow s) (sne : s.Nonempty) : sInf (insert a s) = a ⊓ sInf s :=
  csSup_insert (α := αᵒᵈ) hs sne

@[simp]
theorem csInf_Icc (h : a ≤ b) : sInf (Icc a b) = a :=
  (isGLB_Icc h).csInf_eq (nonempty_Icc.2 h)

@[simp]
theorem csInf_Ici : sInf (Ici a) = a :=
  isLeast_Ici.csInf_eq

@[simp]
theorem csInf_Ico (h : a < b) : sInf (Ico a b) = a :=
  (isGLB_Ico h).csInf_eq (nonempty_Ico.2 h)

@[simp]
theorem csInf_Ioc [DenselyOrdered α] (h : a < b) : sInf (Ioc a b) = a :=
  (isGLB_Ioc h).csInf_eq (nonempty_Ioc.2 h)

@[simp]
theorem csInf_Ioi [NoMaxOrder α] [DenselyOrdered α] : sInf (Ioi a) = a :=
  csInf_eq_of_forall_ge_of_forall_gt_exists_lt nonempty_Ioi (fun _ => le_of_lt) fun w hw => by
    simpa using exists_between hw

@[simp]
theorem csInf_Ioo [DenselyOrdered α] (h : a < b) : sInf (Ioo a b) = a :=
  (isGLB_Ioo h).csInf_eq (nonempty_Ioo.2 h)

@[simp]
theorem csSup_Icc (h : a ≤ b) : sSup (Icc a b) = b :=
  (isLUB_Icc h).csSup_eq (nonempty_Icc.2 h)

@[simp]
theorem csSup_Ico [DenselyOrdered α] (h : a < b) : sSup (Ico a b) = b :=
  (isLUB_Ico h).csSup_eq (nonempty_Ico.2 h)

@[simp]
theorem csSup_Iic : sSup (Iic a) = a :=
  isGreatest_Iic.csSup_eq

@[simp]
theorem csSup_Iio [NoMinOrder α] [DenselyOrdered α] : sSup (Iio a) = a :=
  csSup_eq_of_forall_le_of_forall_lt_exists_gt nonempty_Iio (fun _ => le_of_lt) fun w hw => by
    simpa [and_comm] using exists_between hw

@[simp]
theorem csSup_Ioc (h : a < b) : sSup (Ioc a b) = b :=
  (isLUB_Ioc h).csSup_eq (nonempty_Ioc.2 h)

@[simp]
theorem csSup_Ioo [DenselyOrdered α] (h : a < b) : sSup (Ioo a b) = b :=
  (isLUB_Ioo h).csSup_eq (nonempty_Ioo.2 h)

/-- The indexed supremum of a function is bounded above by a uniform bound-/
theorem ciSup_le [Nonempty ι] {f : ι → α} {c : α} (H : ∀ x, f x ≤ c) : iSup f ≤ c :=
  csSup_le (range_nonempty f) (by rwa [forall_mem_range])

/-- The indexed supremum of a function is bounded below by the value taken at one point-/
theorem le_ciSup {f : ι → α} (H : BddAbove (range f)) (c : ι) : f c ≤ iSup f :=
  le_csSup H (mem_range_self _)

theorem le_ciSup_of_le {f : ι → α} (H : BddAbove (range f)) (c : ι) (h : a ≤ f c) : a ≤ iSup f :=
  le_trans h (le_ciSup H c)

/-- The indexed supremum of two functions are comparable if the functions are pointwise comparable-/
theorem ciSup_mono {f g : ι → α} (B : BddAbove (range g)) (H : ∀ x, f x ≤ g x) :
    iSup f ≤ iSup g := by
  cases isEmpty_or_nonempty ι
  · rw [iSup_of_empty', iSup_of_empty']
  · exact ciSup_le fun x => le_ciSup_of_le B x (H x)

theorem le_ciSup_set {f : β → α} {s : Set β} (H : BddAbove (f '' s)) {c : β} (hc : c ∈ s) :
    f c ≤ ⨆ i : s, f i :=
  (le_csSup H <| mem_image_of_mem f hc).trans_eq sSup_image'

/-- The indexed infimum of two functions are comparable if the functions are pointwise comparable-/
theorem ciInf_mono {f g : ι → α} (B : BddBelow (range f)) (H : ∀ x, f x ≤ g x) : iInf f ≤ iInf g :=
  ciSup_mono (α := αᵒᵈ) B H

/-- The indexed minimum of a function is bounded below by a uniform lower bound-/
theorem le_ciInf [Nonempty ι] {f : ι → α} {c : α} (H : ∀ x, c ≤ f x) : c ≤ iInf f :=
  ciSup_le (α := αᵒᵈ) H

/-- The indexed infimum of a function is bounded above by the value taken at one point-/
theorem ciInf_le {f : ι → α} (H : BddBelow (range f)) (c : ι) : iInf f ≤ f c :=
  le_ciSup (α := αᵒᵈ) H c

theorem ciInf_le_of_le {f : ι → α} (H : BddBelow (range f)) (c : ι) (h : f c ≤ a) : iInf f ≤ a :=
  le_ciSup_of_le (α := αᵒᵈ) H c h

theorem ciInf_set_le {f : β → α} {s : Set β} (H : BddBelow (f '' s)) {c : β} (hc : c ∈ s) :
    ⨅ i : s, f i ≤ f c :=
  le_ciSup_set (α := αᵒᵈ) H hc

@[simp]
theorem ciSup_const [hι : Nonempty ι] {a : α} : ⨆ _ : ι, a = a := by
  rw [iSup, range_const, csSup_singleton]

@[simp]
theorem ciInf_const [Nonempty ι] {a : α} : ⨅ _ : ι, a = a :=
  ciSup_const (α := αᵒᵈ)

@[simp]
theorem ciSup_unique [Unique ι] {s : ι → α} : ⨆ i, s i = s default := by
  have : ∀ i, s i = s default := fun i => congr_arg s (Unique.eq_default i)
  simp only [this, ciSup_const]

@[simp]
theorem ciInf_unique [Unique ι] {s : ι → α} : ⨅ i, s i = s default :=
  ciSup_unique (α := αᵒᵈ)

theorem ciSup_subsingleton [Subsingleton ι] (i : ι) (s : ι → α) : ⨆ i, s i = s i :=
  @ciSup_unique α ι _ ⟨⟨i⟩, fun j => Subsingleton.elim j i⟩ _

theorem ciInf_subsingleton [Subsingleton ι] (i : ι) (s : ι → α) : ⨅ i, s i = s i :=
  @ciInf_unique α ι _ ⟨⟨i⟩, fun j => Subsingleton.elim j i⟩ _

@[simp]
theorem ciSup_pos {p : Prop} {f : p → α} (hp : p) : ⨆ h : p, f h = f hp :=
  ciSup_subsingleton hp f

@[simp]
theorem ciInf_pos {p : Prop} {f : p → α} (hp : p) : ⨅ h : p, f h = f hp :=
  ciSup_pos (α := αᵒᵈ) hp

lemma ciSup_neg {p : Prop} {f : p → α} (hp : ¬ p) :
    ⨆ (h : p), f h = sSup (∅ : Set α) := by
  rw [iSup]
  congr
  rwa [range_eq_empty_iff, isEmpty_Prop]

lemma ciInf_neg {p : Prop} {f : p → α} (hp : ¬ p) :
    ⨅ (h : p), f h = sInf (∅ : Set α) :=
  ciSup_neg (α := αᵒᵈ) hp

lemma ciSup_eq_ite {p : Prop} [Decidable p] {f : p → α} :
    (⨆ h : p, f h) = if h : p then f h else sSup (∅ : Set α) := by
  by_cases H : p <;> simp [ciSup_neg, H]

lemma ciInf_eq_ite {p : Prop} [Decidable p] {f : p → α} :
    (⨅ h : p, f h) = if h : p then f h else sInf (∅ : Set α) :=
  ciSup_eq_ite (α := αᵒᵈ)

theorem cbiSup_eq_of_forall {p : ι → Prop} {f : Subtype p → α} (hp : ∀ i, p i) :
    ⨆ (i) (h : p i), f ⟨i, h⟩ = iSup f := by
  simp only [hp, ciSup_unique]
  simp only [iSup]
  congr
  apply Subset.antisymm
  · rintro - ⟨i, rfl⟩
    simp [hp i]
  · rintro - ⟨i, rfl⟩
    simp

theorem cbiInf_eq_of_forall {p : ι → Prop} {f : Subtype p → α} (hp : ∀ i, p i) :
    ⨅ (i) (h : p i), f ⟨i, h⟩ = iInf f :=
  cbiSup_eq_of_forall (α := αᵒᵈ) hp

/-- Introduction rule to prove that `b` is the supremum of `f`: it suffices to check that `b`
is larger than `f i` for all `i`, and that this is not the case of any `w<b`.
See `iSup_eq_of_forall_le_of_forall_lt_exists_gt` for a version in complete lattices. -/
theorem ciSup_eq_of_forall_le_of_forall_lt_exists_gt [Nonempty ι] {f : ι → α} (h₁ : ∀ i, f i ≤ b)
    (h₂ : ∀ w, w < b → ∃ i, w < f i) : ⨆ i : ι, f i = b :=
  csSup_eq_of_forall_le_of_forall_lt_exists_gt (range_nonempty f) (forall_mem_range.mpr h₁)
    fun w hw => exists_range_iff.mpr <| h₂ w hw

-- Porting note: in mathlib3 `by exact` is not needed
/-- Introduction rule to prove that `b` is the infimum of `f`: it suffices to check that `b`
is smaller than `f i` for all `i`, and that this is not the case of any `w>b`.
See `iInf_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in complete lattices. -/
theorem ciInf_eq_of_forall_ge_of_forall_gt_exists_lt [Nonempty ι] {f : ι → α} (h₁ : ∀ i, b ≤ f i)
    (h₂ : ∀ w, b < w → ∃ i, f i < w) : ⨅ i : ι, f i = b := by
  exact ciSup_eq_of_forall_le_of_forall_lt_exists_gt (α := αᵒᵈ) (f := ‹_›) ‹_› ‹_›

/-- **Nested intervals lemma**: if `f` is a monotone sequence, `g` is an antitone sequence, and
`f n ≤ g n` for all `n`, then `⨆ n, f n` belongs to all the intervals `[f n, g n]`. -/
theorem Monotone.ciSup_mem_iInter_Icc_of_antitone [SemilatticeSup β] {f g : β → α} (hf : Monotone f)
    (hg : Antitone g) (h : f ≤ g) : (⨆ n, f n) ∈ ⋂ n, Icc (f n) (g n) := by
  refine mem_iInter.2 fun n => ?_
  haveI : Nonempty β := ⟨n⟩
  have : ∀ m, f m ≤ g n := fun m => hf.forall_le_of_antitone hg h m n
  exact ⟨le_ciSup ⟨g <| n, forall_mem_range.2 this⟩ _, ciSup_le this⟩

/-- Nested intervals lemma: if `[f n, g n]` is an antitone sequence of nonempty
closed intervals, then `⨆ n, f n` belongs to all the intervals `[f n, g n]`. -/
theorem ciSup_mem_iInter_Icc_of_antitone_Icc [SemilatticeSup β] {f g : β → α}
    (h : Antitone fun n => Icc (f n) (g n)) (h' : ∀ n, f n ≤ g n) :
    (⨆ n, f n) ∈ ⋂ n, Icc (f n) (g n) :=
  Monotone.ciSup_mem_iInter_Icc_of_antitone
    (fun _ n hmn => ((Icc_subset_Icc_iff (h' n)).1 (h hmn)).1)
    (fun _ n hmn => ((Icc_subset_Icc_iff (h' n)).1 (h hmn)).2) h'

/-- Introduction rule to prove that `b` is the supremum of `s`: it suffices to check that
1) `b` is an upper bound
2) every other upper bound `b'` satisfies `b ≤ b'`. -/
theorem csSup_eq_of_is_forall_le_of_forall_le_imp_ge (hs : s.Nonempty) (h_is_ub : ∀ a ∈ s, a ≤ b)
    (h_b_le_ub : ∀ ub, (∀ a ∈ s, a ≤ ub) → b ≤ ub) : sSup s = b :=
  (csSup_le hs h_is_ub).antisymm ((h_b_le_ub _) fun _ => le_csSup ⟨b, h_is_ub⟩)

lemma Set.Iic_ciInf [Nonempty ι] {f : ι → α} (hf : BddBelow (range f)) :
    Iic (⨅ i, f i) = ⋂ i, Iic (f i) := by
  apply Subset.antisymm
  · rintro x hx - ⟨i, rfl⟩
    exact hx.trans (ciInf_le hf _)
  · rintro x hx
    apply le_ciInf
    simpa using hx

lemma Set.Ici_ciSup [Nonempty ι] {f : ι → α} (hf : BddAbove (range f)) :
    Ici (⨆ i, f i) = ⋂ i, Ici (f i) :=
  Iic_ciInf (α := αᵒᵈ) hf

lemma sup_eq_top_of_top_mem [OrderTop α] (h : ⊤ ∈ s) : sSup s = ⊤ :=
  top_unique <| le_csSup (OrderTop.bddAbove s) h

lemma inf_eq_bot_of_bot_mem [OrderBot α] (h : ⊥ ∈ s) : sInf s = ⊥ :=
  bot_unique <| csInf_le (OrderBot.bddBelow s) h

theorem ciSup_subtype [Nonempty ι] {p : ι → Prop} [Nonempty (Subtype p)] {f : Subtype p → α}
    (hf : BddAbove (Set.range f)) (hf' : sSup ∅ ≤ iSup f) :
    iSup f = ⨆ (i) (h : p i), f ⟨i, h⟩ := by
  classical
  refine le_antisymm (ciSup_le ?_) ?_
  · intro ⟨i, h⟩
    have : f ⟨i, h⟩ = (fun i : ι ↦ ⨆ (h : p i), f ⟨i, h⟩) i := by simp [h]
    rw [this]
    refine le_ciSup (f := (fun i : ι ↦ ⨆ (h : p i), f ⟨i, h⟩)) ?_ i
    simp_rw [ciSup_eq_ite]
    refine (hf.union (bddAbove_singleton (a := sSup ∅))).mono ?_
    intro
    simp only [Set.mem_range, Set.union_singleton, Set.mem_insert_iff, Subtype.exists,
      forall_exists_index]
    intro b hb
    split_ifs at hb
    · exact Or.inr ⟨_, _, hb⟩
    · simp_all
  · refine ciSup_le fun i ↦ ?_
    simp_rw [ciSup_eq_ite]
    split_ifs
    · exact le_ciSup hf ?_
    · exact hf'

theorem ciInf_subtype [Nonempty ι] {p : ι → Prop} [Nonempty (Subtype p)] {f : Subtype p → α}
    (hf : BddBelow (Set.range f)) (hf' : iInf f ≤ sInf ∅) :
    iInf f = ⨅ (i) (h : p i), f ⟨i, h⟩ :=
  ciSup_subtype (α := αᵒᵈ) hf hf'

theorem ciSup_subtype' [Nonempty ι] {p : ι → Prop} [Nonempty (Subtype p)] {f : ∀ i, p i → α}
    (hf : BddAbove (Set.range (fun i : Subtype p ↦ f i i.prop)))
    (hf' : sSup ∅ ≤ ⨆ (i : Subtype p), f i i.prop) :
    ⨆ (i) (h), f i h = ⨆ x : Subtype p, f x x.property :=
  (ciSup_subtype (f := fun x => f x.val x.property) hf hf').symm

theorem ciInf_subtype' [Nonempty ι] {p : ι → Prop} [Nonempty (Subtype p)] {f : ∀ i, p i → α}
    (hf : BddBelow (Set.range (fun i : Subtype p ↦ f i i.prop)))
    (hf' : ⨅ (i : Subtype p), f i i.prop ≤ sInf ∅) :
    ⨅ (i) (h), f i h = ⨅ x : Subtype p, f x x.property :=
  (ciInf_subtype (f := fun x => f x.val x.property) hf hf').symm

theorem ciSup_subtype'' {ι} [Nonempty ι] {s : Set ι} (hs : s.Nonempty) {f : ι → α}
    (hf : BddAbove (Set.range fun i : s ↦ f i)) (hf' : sSup ∅ ≤ ⨆ i : s, f i) :
    ⨆ i : s, f i = ⨆ (t : ι) (_ : t ∈ s), f t :=
  haveI : Nonempty s := Set.Nonempty.to_subtype hs
  ciSup_subtype hf hf'

theorem ciInf_subtype'' {ι} [Nonempty ι] {s : Set ι} (hs : s.Nonempty) {f : ι → α}
    (hf : BddBelow (Set.range fun i : s ↦ f i)) (hf' : ⨅ i : s, f i ≤ sInf ∅) :
    ⨅ i : s, f i = ⨅ (t : ι) (_ : t ∈ s), f t :=
  haveI : Nonempty s := Set.Nonempty.to_subtype hs
  ciInf_subtype hf hf'

theorem csSup_image [Nonempty β] {s : Set β} (hs : s.Nonempty) {f : β → α}
    (hf : BddAbove (Set.range fun i : s ↦ f i)) (hf' : sSup ∅ ≤ ⨆ i : s, f i) :
    sSup (f '' s) = ⨆ a ∈ s, f a := by
  rw [← ciSup_subtype'' hs hf hf', iSup, Set.image_eq_range]

theorem csInf_image [Nonempty β] {s : Set β} (hs : s.Nonempty) {f : β → α}
    (hf : BddBelow (Set.range fun i : s ↦ f i)) (hf' : ⨅ i : s, f i ≤ sInf ∅) :
    sInf (f '' s) = ⨅ a ∈ s, f a :=
  csSup_image (α := αᵒᵈ) hs hf hf'

lemma ciSup_image {α ι ι' : Type*} [ConditionallyCompleteLattice α] [Nonempty ι] [Nonempty ι']
    {s : Set ι} (hs : s.Nonempty) {f : ι → ι'} {g : ι' → α}
    (hf : BddAbove (Set.range fun i : s ↦ g (f i))) (hg' : sSup ∅ ≤ ⨆ i : s, g (f i)) :
    ⨆ i ∈ (f '' s), g i = ⨆ x ∈ s, g (f x) := by
  have hg : BddAbove (Set.range fun i : f '' s ↦ g i) := by
    simpa [bddAbove_def] using hf
  have hf' : sSup ∅ ≤ ⨆ i : f '' s, g i := by
    refine hg'.trans ?_
    have : Nonempty s := Set.Nonempty.to_subtype hs
    refine ciSup_le ?_
    intro ⟨i, h⟩
    obtain ⟨t, ht⟩ : ∃ t : f '' s, g t = g (f (Subtype.mk i h)) := by
      have : f i ∈ f '' s := Set.mem_image_of_mem _ h
      exact ⟨⟨f i, this⟩, by simp [this]⟩
    rw [← ht]
    refine le_ciSup_set ?_ t.prop
    simpa [bddAbove_def] using hf
  rw [← csSup_image (by simpa using hs) hg hf', ← csSup_image hs hf hg', ← Set.image_comp, comp_def]

lemma ciInf_image {α ι ι' : Type*} [ConditionallyCompleteLattice α] [Nonempty ι] [Nonempty ι']
    {s : Set ι} (hs : s.Nonempty) {f : ι → ι'} {g : ι' → α}
    (hf : BddBelow (Set.range fun i : s ↦ g (f i))) (hg' : ⨅ i : s, g (f i) ≤ sInf ∅) :
    ⨅ i ∈ (f '' s), g i = ⨅ x ∈ s, g (f x) :=
  ciSup_image (α := αᵒᵈ) hs hf hg'

end ConditionallyCompleteLattice

instance Pi.conditionallyCompleteLattice {ι : Type*} {α : ι → Type*}
    [∀ i, ConditionallyCompleteLattice (α i)] : ConditionallyCompleteLattice (∀ i, α i) :=
  { Pi.instLattice, Pi.supSet, Pi.infSet with
    le_csSup := fun s f ⟨g, hg⟩ hf i =>
      le_csSup ⟨g i, Set.forall_mem_range.2 fun ⟨f', hf'⟩ => hg hf' i⟩ ⟨⟨f, hf⟩, rfl⟩
    csSup_le := fun s f hs hf i =>
      (csSup_le (by haveI := hs.to_subtype; apply range_nonempty)) fun b ⟨⟨g, hg⟩, hb⟩ =>
        hb ▸ hf hg i
    csInf_le := fun s f ⟨g, hg⟩ hf i =>
      csInf_le ⟨g i, Set.forall_mem_range.2 fun ⟨f', hf'⟩ => hg hf' i⟩ ⟨⟨f, hf⟩, rfl⟩
    le_csInf := fun s f hs hf i =>
      (le_csInf (by haveI := hs.to_subtype; apply range_nonempty)) fun b ⟨⟨g, hg⟩, hb⟩ =>
        hb ▸ hf hg i }

section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder α] {s t : Set α} {a b : α}

/-- When `b < sSup s`, there is an element `a` in `s` with `b < a`, if `s` is nonempty and the order
is a linear order. -/
theorem exists_lt_of_lt_csSup (hs : s.Nonempty) (hb : b < sSup s) : ∃ a ∈ s, b < a := by
  contrapose! hb
  exact csSup_le hs hb

/-- Indexed version of the above lemma `exists_lt_of_lt_csSup`.
When `b < iSup f`, there is an element `i` such that `b < f i`.
-/
theorem exists_lt_of_lt_ciSup [Nonempty ι] {f : ι → α} (h : b < iSup f) : ∃ i, b < f i :=
  let ⟨_, ⟨i, rfl⟩, h⟩ := exists_lt_of_lt_csSup (range_nonempty f) h
  ⟨i, h⟩

/-- When `sInf s < b`, there is an element `a` in `s` with `a < b`, if `s` is nonempty and the order
is a linear order. -/
theorem exists_lt_of_csInf_lt (hs : s.Nonempty) (hb : sInf s < b) : ∃ a ∈ s, a < b :=
  exists_lt_of_lt_csSup (α := αᵒᵈ) hs hb

/-- Indexed version of the above lemma `exists_lt_of_csInf_lt`
When `iInf f < a`, there is an element `i` such that `f i < a`.
-/
theorem exists_lt_of_ciInf_lt [Nonempty ι] {f : ι → α} (h : iInf f < a) : ∃ i, f i < a :=
  exists_lt_of_lt_ciSup (α := αᵒᵈ) h

theorem csSup_of_not_bddAbove {s : Set α} (hs : ¬BddAbove s) : sSup s = sSup ∅ :=
  ConditionallyCompleteLinearOrder.csSup_of_not_bddAbove s hs

theorem csSup_eq_univ_of_not_bddAbove {s : Set α} (hs : ¬BddAbove s) : sSup s = sSup univ := by
  rw [csSup_of_not_bddAbove hs, csSup_of_not_bddAbove (s := univ)]
  contrapose! hs
  exact hs.mono (subset_univ _)

theorem csInf_of_not_bddBelow {s : Set α} (hs : ¬BddBelow s) : sInf s = sInf ∅ :=
  ConditionallyCompleteLinearOrder.csInf_of_not_bddBelow s hs

theorem csInf_eq_univ_of_not_bddBelow {s : Set α} (hs : ¬BddBelow s) : sInf s = sInf univ :=
  csSup_eq_univ_of_not_bddAbove (α := αᵒᵈ) hs

/-- When every element of a set `s` is bounded by an element of a set `t`, and conversely, then
`s` and `t` have the same supremum. This holds even when the sets may be empty or unbounded. -/
theorem csSup_eq_csSup_of_forall_exists_le {s t : Set α}
    (hs : ∀ x ∈ s, ∃ y ∈ t, x ≤ y) (ht : ∀ y ∈ t, ∃ x ∈ s, y ≤ x) :
    sSup s = sSup t := by
  rcases eq_empty_or_nonempty s with rfl|s_ne
  · have : t = ∅ := eq_empty_of_forall_not_mem (fun y yt ↦ by simpa using ht y yt)
    rw [this]
  rcases eq_empty_or_nonempty t with rfl|t_ne
  · have : s = ∅ := eq_empty_of_forall_not_mem (fun x xs ↦ by simpa using hs x xs)
    rw [this]
  by_cases B : BddAbove s ∨ BddAbove t
  · have Bs : BddAbove s := by
      rcases B with hB|⟨b, hb⟩
      · exact hB
      · refine ⟨b, fun x hx ↦ ?_⟩
        rcases hs x hx with ⟨y, hy, hxy⟩
        exact hxy.trans (hb hy)
    have Bt : BddAbove t := by
      rcases B with ⟨b, hb⟩|hB
      · refine ⟨b, fun y hy ↦ ?_⟩
        rcases ht y hy with ⟨x, hx, hyx⟩
        exact hyx.trans (hb hx)
      · exact hB
    apply le_antisymm
    · apply csSup_le s_ne (fun x hx ↦ ?_)
      rcases hs x hx with ⟨y, yt, hxy⟩
      exact hxy.trans (le_csSup Bt yt)
    · apply csSup_le t_ne (fun y hy ↦ ?_)
      rcases ht y hy with ⟨x, xs, hyx⟩
      exact hyx.trans (le_csSup Bs xs)
  · simp [csSup_of_not_bddAbove, (not_or.1 B).1, (not_or.1 B).2]

/-- When every element of a set `s` is bounded by an element of a set `t`, and conversely, then
`s` and `t` have the same infimum. This holds even when the sets may be empty or unbounded. -/
theorem csInf_eq_csInf_of_forall_exists_le {s t : Set α}
    (hs : ∀ x ∈ s, ∃ y ∈ t, y ≤ x) (ht : ∀ y ∈ t, ∃ x ∈ s, x ≤ y) :
    sInf s = sInf t :=
  csSup_eq_csSup_of_forall_exists_le (α := αᵒᵈ) hs ht

lemma sSup_iUnion_Iic (f : ι → α) : sSup (⋃ (i : ι), Iic (f i)) = ⨆ i, f i := by
  apply csSup_eq_csSup_of_forall_exists_le
  · rintro x ⟨-, ⟨i, rfl⟩, hi⟩
    exact ⟨f i, mem_range_self _, hi⟩
  · rintro x ⟨i, rfl⟩
    exact ⟨f i, mem_iUnion_of_mem i le_rfl, le_rfl⟩

lemma sInf_iUnion_Ici (f : ι → α) : sInf (⋃ (i : ι), Ici (f i)) = ⨅ i, f i :=
  sSup_iUnion_Iic (α := αᵒᵈ) f

theorem cbiSup_eq_of_not_forall {p : ι → Prop} {f : Subtype p → α} (hp : ¬ (∀ i, p i)) :
    ⨆ (i) (h : p i), f ⟨i, h⟩ = iSup f ⊔ sSup ∅ := by
  classical
  rcases not_forall.1 hp with ⟨i₀, hi₀⟩
  have : Nonempty ι := ⟨i₀⟩
  simp only [ciSup_eq_ite]
  by_cases H : BddAbove (range f)
  · have B : BddAbove (range fun i ↦ if h : p i then f ⟨i, h⟩ else sSup ∅) := by
      rcases H with ⟨c, hc⟩
      refine ⟨c ⊔ sSup ∅, ?_⟩
      rintro - ⟨i, rfl⟩
      by_cases hi : p i
      · simp only [hi, dite_true, le_sup_iff, hc (mem_range_self _), true_or]
      · simp only [hi, dite_false, le_sup_right]
    apply le_antisymm
    · apply ciSup_le (fun i ↦ ?_)
      by_cases hi : p i
      · simp only [hi, dite_true, le_sup_iff]
        left
        exact le_ciSup H _
      · simp [hi]
    · apply sup_le
      · rcases isEmpty_or_nonempty (Subtype p) with hp|hp
        · rw [iSup_of_empty']
          convert le_ciSup B i₀
          simp [hi₀]
        · apply ciSup_le
          rintro ⟨i, hi⟩
          convert le_ciSup B i
          simp [hi]
      · convert le_ciSup B i₀
        simp [hi₀]
  · have : iSup f = sSup (∅ : Set α) := csSup_of_not_bddAbove H
    simp only [this, le_refl, sup_of_le_left]
    apply csSup_of_not_bddAbove
    contrapose! H
    apply H.mono
    rintro - ⟨i, rfl⟩
    convert mem_range_self i.1
    simp [i.2]

theorem cbiInf_eq_of_not_forall {p : ι → Prop} {f : Subtype p → α} (hp : ¬ (∀ i, p i)) :
    ⨅ (i) (h : p i), f ⟨i, h⟩ = iInf f ⊓ sInf ∅ :=
  cbiSup_eq_of_not_forall (α := αᵒᵈ) hp

open Function

variable [IsWellOrder α (· < ·)]

theorem sInf_eq_argmin_on (hs : s.Nonempty) : sInf s = argminOn id wellFounded_lt s hs :=
  IsLeast.csInf_eq ⟨argminOn_mem _ _ _ _, fun _ ha => argminOn_le id _ _ ha⟩

theorem isLeast_csInf (hs : s.Nonempty) : IsLeast s (sInf s) := by
  rw [sInf_eq_argmin_on hs]
  exact ⟨argminOn_mem _ _ _ _, fun a ha => argminOn_le id _ _ ha⟩

theorem le_csInf_iff' (hs : s.Nonempty) : b ≤ sInf s ↔ b ∈ lowerBounds s :=
  le_isGLB_iff (isLeast_csInf hs).isGLB

theorem csInf_mem (hs : s.Nonempty) : sInf s ∈ s :=
  (isLeast_csInf hs).1

theorem ciInf_mem [Nonempty ι] (f : ι → α) : iInf f ∈ range f :=
  csInf_mem (range_nonempty f)

theorem MonotoneOn.map_csInf {β : Type*} [ConditionallyCompleteLattice β] {f : α → β}
    (hf : MonotoneOn f s) (hs : s.Nonempty) : f (sInf s) = sInf (f '' s) :=
  (hf.map_isLeast (isLeast_csInf hs)).csInf_eq.symm

theorem Monotone.map_csInf {β : Type*} [ConditionallyCompleteLattice β] {f : α → β}
    (hf : Monotone f) (hs : s.Nonempty) : f (sInf s) = sInf (f '' s) :=
  (hf.map_isLeast (isLeast_csInf hs)).csInf_eq.symm

end ConditionallyCompleteLinearOrder

/-!
### Lemmas about a conditionally complete linear order with bottom element

In this case we have `Sup ∅ = ⊥`, so we can drop some `Nonempty`/`Set.Nonempty` assumptions.
-/


section ConditionallyCompleteLinearOrderBot

@[simp]
theorem csInf_univ [ConditionallyCompleteLinearOrder α] [OrderBot α] : sInf (univ : Set α) = ⊥ :=
  isLeast_univ.csInf_eq

variable [ConditionallyCompleteLinearOrderBot α] {s : Set α} {f : ι → α} {a : α}

@[simp]
theorem csSup_empty : (sSup ∅ : α) = ⊥ :=
  ConditionallyCompleteLinearOrderBot.csSup_empty

@[simp]
theorem ciSup_of_empty [IsEmpty ι] (f : ι → α) : ⨆ i, f i = ⊥ := by
  rw [iSup_of_empty', csSup_empty]

theorem ciSup_false (f : False → α) : ⨆ i, f i = ⊥ :=
  ciSup_of_empty f

theorem isLUB_csSup' {s : Set α} (hs : BddAbove s) : IsLUB s (sSup s) := by
  rcases eq_empty_or_nonempty s with (rfl | hne)
  · simp only [csSup_empty, isLUB_empty]
  · exact isLUB_csSup hne hs

theorem csSup_le_iff' {s : Set α} (hs : BddAbove s) {a : α} : sSup s ≤ a ↔ ∀ x ∈ s, x ≤ a :=
  isLUB_le_iff (isLUB_csSup' hs)

theorem csSup_le' {s : Set α} {a : α} (h : a ∈ upperBounds s) : sSup s ≤ a :=
  (csSup_le_iff' ⟨a, h⟩).2 h

theorem le_csSup_iff' {s : Set α} {a : α} (h : BddAbove s) :
    a ≤ sSup s ↔ ∀ b, b ∈ upperBounds s → a ≤ b :=
  ⟨fun h _ hb => le_trans h (csSup_le' hb), fun hb => hb _ fun _ => le_csSup h⟩

theorem le_ciSup_iff' {s : ι → α} {a : α} (h : BddAbove (range s)) :
    a ≤ iSup s ↔ ∀ b, (∀ i, s i ≤ b) → a ≤ b := by simp [iSup, h, le_csSup_iff', upperBounds]

theorem le_csInf_iff'' {s : Set α} {a : α} (ne : s.Nonempty) :
    a ≤ sInf s ↔ ∀ b : α, b ∈ s → a ≤ b :=
  le_csInf_iff (OrderBot.bddBelow _) ne

theorem le_ciInf_iff' [Nonempty ι] {f : ι → α} {a : α} : a ≤ iInf f ↔ ∀ i, a ≤ f i :=
  le_ciInf_iff (OrderBot.bddBelow _)

theorem csInf_le' (h : a ∈ s) : sInf s ≤ a := csInf_le (OrderBot.bddBelow _) h

theorem ciInf_le' (f : ι → α) (i : ι) : iInf f ≤ f i := ciInf_le (OrderBot.bddBelow _) _

lemma ciInf_le_of_le' (c : ι) : f c ≤ a → iInf f ≤ a := ciInf_le_of_le (OrderBot.bddBelow _) _

theorem exists_lt_of_lt_csSup' {s : Set α} {a : α} (h : a < sSup s) : ∃ b ∈ s, a < b := by
  contrapose! h
  exact csSup_le' h

theorem ciSup_le_iff' {f : ι → α} (h : BddAbove (range f)) {a : α} :
    ⨆ i, f i ≤ a ↔ ∀ i, f i ≤ a :=
  (csSup_le_iff' h).trans forall_mem_range

theorem ciSup_le' {f : ι → α} {a : α} (h : ∀ i, f i ≤ a) : ⨆ i, f i ≤ a :=
  csSup_le' <| forall_mem_range.2 h

theorem exists_lt_of_lt_ciSup' {f : ι → α} {a : α} (h : a < ⨆ i, f i) : ∃ i, a < f i := by
  contrapose! h
  exact ciSup_le' h

theorem ciSup_mono' {ι'} {f : ι → α} {g : ι' → α} (hg : BddAbove (range g))
    (h : ∀ i, ∃ i', f i ≤ g i') : iSup f ≤ iSup g :=
  ciSup_le' fun i => Exists.elim (h i) (le_ciSup_of_le hg)

theorem csInf_le_csInf' {s t : Set α} (h₁ : t.Nonempty) (h₂ : t ⊆ s) : sInf s ≤ sInf t :=
  csInf_le_csInf (OrderBot.bddBelow s) h₁ h₂

lemma ciSup_or' (p q : Prop) (f : p ∨ q → α) :
    ⨆ (h : p ∨ q), f h = (⨆ h : p, f (.inl h)) ⊔ ⨆ h : q, f (.inr h) := by
  by_cases hp : p <;> by_cases hq : q
  · simp [hp, hq]
  · simp [hp, hq]
  · simp [hp, hq]
  · simp [hp, hq]

end ConditionallyCompleteLinearOrderBot

namespace WithTop

variable [ConditionallyCompleteLinearOrderBot α]

/-- The `sSup` of a non-empty set is its least upper bound for a conditionally
complete lattice with a top. -/
theorem isLUB_sSup' {β : Type*} [ConditionallyCompleteLattice β] {s : Set (WithTop β)}
    (hs : s.Nonempty) : IsLUB s (sSup s) := by
  classical
  constructor
  · show ite _ _ _ ∈ _
    split_ifs with h₁ h₂
    · intro _ _
      exact le_top
    · rintro (⟨⟩ | a) ha
      · contradiction
      apply coe_le_coe.2
      exact le_csSup h₂ ha
    · intro _ _
      exact le_top
  · show ite _ _ _ ∈ _
    split_ifs with h₁ h₂
    · rintro (⟨⟩ | a) ha
      · exact le_rfl
      · exact False.elim (not_top_le_coe a (ha h₁))
    · rintro (⟨⟩ | b) hb
      · exact le_top
      refine coe_le_coe.2 (csSup_le ?_ ?_)
      · rcases hs with ⟨⟨⟩ | b, hb⟩
        · exact absurd hb h₁
        · exact ⟨b, hb⟩
      · intro a ha
        exact coe_le_coe.1 (hb ha)
    · rintro (⟨⟩ | b) hb
      · exact le_rfl
      · exfalso
        apply h₂
        use b
        intro a ha
        exact coe_le_coe.1 (hb ha)

-- Porting note: in mathlib3 `dsimp only [sSup]` was not needed, we used `show IsLUB ∅ (ite _ _ _)`
theorem isLUB_sSup (s : Set (WithTop α)) : IsLUB s (sSup s) := by
  rcases s.eq_empty_or_nonempty with hs | hs
  · rw [hs]
    dsimp only [sSup]
    show IsLUB ∅ _
    split_ifs with h₁ h₂
    · cases h₁
    · rw [preimage_empty, csSup_empty]
      exact isLUB_empty
    · exfalso
      apply h₂
      use ⊥
      rintro a ⟨⟩
  exact isLUB_sSup' hs

/-- The `sInf` of a bounded-below set is its greatest lower bound for a conditionally
complete lattice with a top. -/
theorem isGLB_sInf' {β : Type*} [ConditionallyCompleteLattice β] {s : Set (WithTop β)}
    (hs : BddBelow s) : IsGLB s (sInf s) := by
  classical
  constructor
  · show ite _ _ _ ∈ _
    simp only [hs, not_true_eq_false, or_false]
    split_ifs with h
    · intro a ha
      exact top_le_iff.2 (Set.mem_singleton_iff.1 (h ha))
    · rintro (⟨⟩ | a) ha
      · exact le_top
      refine coe_le_coe.2 (csInf_le ?_ ha)
      rcases hs with ⟨⟨⟩ | b, hb⟩
      · exfalso
        apply h
        intro c hc
        rw [mem_singleton_iff, ← top_le_iff]
        exact hb hc
      use b
      intro c hc
      exact coe_le_coe.1 (hb hc)
  · show ite _ _ _ ∈ _
    simp only [hs, not_true_eq_false, or_false]
    split_ifs with h
    · intro _ _
      exact le_top
    · rintro (⟨⟩ | a) ha
      · exfalso
        apply h
        intro b hb
        exact Set.mem_singleton_iff.2 (top_le_iff.1 (ha hb))
      · refine coe_le_coe.2 (le_csInf ?_ ?_)
        · classical
            contrapose! h
            rintro (⟨⟩ | a) ha
            · exact mem_singleton ⊤
            · exact (not_nonempty_iff_eq_empty.2 h ⟨a, ha⟩).elim
        · intro b hb
          rw [← coe_le_coe]
          exact ha hb

theorem isGLB_sInf (s : Set (WithTop α)) : IsGLB s (sInf s) := by
  by_cases hs : BddBelow s
  · exact isGLB_sInf' hs
  · exfalso
    apply hs
    use ⊥
    intro _ _
    exact bot_le

noncomputable instance : CompleteLinearOrder (WithTop α) where
  __ := linearOrder
  __ := LinearOrder.toBiheytingAlgebra
  le_sSup s := (isLUB_sSup s).1
  sSup_le s := (isLUB_sSup s).2
  le_sInf s := (isGLB_sInf s).2
  sInf_le s := (isGLB_sInf s).1

/-- A version of `WithTop.coe_sSup'` with a more convenient but less general statement. -/
@[norm_cast]
theorem coe_sSup {s : Set α} (hb : BddAbove s) : ↑(sSup s) = (⨆ a ∈ s, ↑a : WithTop α) := by
  rw [coe_sSup' hb, sSup_image]

/-- A version of `WithTop.coe_sInf'` with a more convenient but less general statement. -/
@[norm_cast]
theorem coe_sInf {s : Set α} (hs : s.Nonempty) (h's : BddBelow s) :
    ↑(sInf s) = (⨅ a ∈ s, ↑a : WithTop α) := by
  rw [coe_sInf' hs h's, sInf_image]

end WithTop

namespace Monotone

variable [Preorder α] [ConditionallyCompleteLattice β] {f : α → β} (h_mono : Monotone f)

/-! A monotone function into a conditionally complete lattice preserves the ordering properties of
`sSup` and `sInf`. -/


theorem le_csSup_image {s : Set α} {c : α} (hcs : c ∈ s) (h_bdd : BddAbove s) :
    f c ≤ sSup (f '' s) :=
  le_csSup (map_bddAbove h_mono h_bdd) (mem_image_of_mem f hcs)

theorem csSup_image_le {s : Set α} (hs : s.Nonempty) {B : α} (hB : B ∈ upperBounds s) :
    sSup (f '' s) ≤ f B :=
  csSup_le (Nonempty.image f hs) (h_mono.mem_upperBounds_image hB)

-- Porting note: in mathlib3 `f'` is not needed
theorem csInf_image_le {s : Set α} {c : α} (hcs : c ∈ s) (h_bdd : BddBelow s) :
    sInf (f '' s) ≤ f c := by
  let f' : αᵒᵈ → βᵒᵈ := f
  exact le_csSup_image (α := αᵒᵈ) (β := βᵒᵈ)
    (show Monotone f' from fun x y hxy => h_mono hxy) hcs h_bdd

-- Porting note: in mathlib3 `f'` is not needed
theorem le_csInf_image {s : Set α} (hs : s.Nonempty) {B : α} (hB : B ∈ lowerBounds s) :
    f B ≤ sInf (f '' s) := by
  let f' : αᵒᵈ → βᵒᵈ := f
  exact csSup_image_le (α := αᵒᵈ) (β := βᵒᵈ)
    (show Monotone f' from fun x y hxy => h_mono hxy) hs hB

end Monotone

namespace GaloisConnection

variable [ConditionallyCompleteLattice α] [ConditionallyCompleteLattice β] [Nonempty ι] {l : α → β}
  {u : β → α}

theorem l_csSup (gc : GaloisConnection l u) {s : Set α} (hne : s.Nonempty) (hbdd : BddAbove s) :
    l (sSup s) = ⨆ x : s, l x :=
  Eq.symm <| IsLUB.ciSup_set_eq (gc.isLUB_l_image <| isLUB_csSup hne hbdd) hne

theorem l_csSup' (gc : GaloisConnection l u) {s : Set α} (hne : s.Nonempty) (hbdd : BddAbove s) :
    l (sSup s) = sSup (l '' s) := by rw [gc.l_csSup hne hbdd, sSup_image']

theorem l_ciSup (gc : GaloisConnection l u) {f : ι → α} (hf : BddAbove (range f)) :
    l (⨆ i, f i) = ⨆ i, l (f i) := by rw [iSup, gc.l_csSup (range_nonempty _) hf, iSup_range']

theorem l_ciSup_set (gc : GaloisConnection l u) {s : Set γ} {f : γ → α} (hf : BddAbove (f '' s))
    (hne : s.Nonempty) : l (⨆ i : s, f i) = ⨆ i : s, l (f i) := by
  haveI := hne.to_subtype
  rw [image_eq_range] at hf
  exact gc.l_ciSup hf

theorem u_csInf (gc : GaloisConnection l u) {s : Set β} (hne : s.Nonempty) (hbdd : BddBelow s) :
    u (sInf s) = ⨅ x : s, u x :=
  gc.dual.l_csSup hne hbdd

theorem u_csInf' (gc : GaloisConnection l u) {s : Set β} (hne : s.Nonempty) (hbdd : BddBelow s) :
    u (sInf s) = sInf (u '' s) :=
  gc.dual.l_csSup' hne hbdd

theorem u_ciInf (gc : GaloisConnection l u) {f : ι → β} (hf : BddBelow (range f)) :
    u (⨅ i, f i) = ⨅ i, u (f i) :=
  gc.dual.l_ciSup hf

theorem u_ciInf_set (gc : GaloisConnection l u) {s : Set γ} {f : γ → β} (hf : BddBelow (f '' s))
    (hne : s.Nonempty) : u (⨅ i : s, f i) = ⨅ i : s, u (f i) :=
  gc.dual.l_ciSup_set hf hne

end GaloisConnection

namespace OrderIso

variable [ConditionallyCompleteLattice α] [ConditionallyCompleteLattice β] [Nonempty ι]

theorem map_csSup (e : α ≃o β) {s : Set α} (hne : s.Nonempty) (hbdd : BddAbove s) :
    e (sSup s) = ⨆ x : s, e x :=
  e.to_galoisConnection.l_csSup hne hbdd

theorem map_csSup' (e : α ≃o β) {s : Set α} (hne : s.Nonempty) (hbdd : BddAbove s) :
    e (sSup s) = sSup (e '' s) :=
  e.to_galoisConnection.l_csSup' hne hbdd

theorem map_ciSup (e : α ≃o β) {f : ι → α} (hf : BddAbove (range f)) :
    e (⨆ i, f i) = ⨆ i, e (f i) :=
  e.to_galoisConnection.l_ciSup hf

theorem map_ciSup_set (e : α ≃o β) {s : Set γ} {f : γ → α} (hf : BddAbove (f '' s))
    (hne : s.Nonempty) : e (⨆ i : s, f i) = ⨆ i : s, e (f i) :=
  e.to_galoisConnection.l_ciSup_set hf hne

theorem map_csInf (e : α ≃o β) {s : Set α} (hne : s.Nonempty) (hbdd : BddBelow s) :
    e (sInf s) = ⨅ x : s, e x :=
  e.dual.map_csSup hne hbdd

theorem map_csInf' (e : α ≃o β) {s : Set α} (hne : s.Nonempty) (hbdd : BddBelow s) :
    e (sInf s) = sInf (e '' s) :=
  e.dual.map_csSup' hne hbdd

theorem map_ciInf (e : α ≃o β) {f : ι → α} (hf : BddBelow (range f)) :
    e (⨅ i, f i) = ⨅ i, e (f i) :=
  e.dual.map_ciSup hf

theorem map_ciInf_set (e : α ≃o β) {s : Set γ} {f : γ → α} (hf : BddBelow (f '' s))
    (hne : s.Nonempty) : e (⨅ i : s, f i) = ⨅ i : s, e (f i) :=
  e.dual.map_ciSup_set hf hne

end OrderIso

/-!
### Supremum/infimum of `Set.image2`

A collection of lemmas showing what happens to the suprema/infima of `s` and `t` when mapped under
a binary function whose partial evaluations are lower/upper adjoints of Galois connections.
-/


section

variable [ConditionallyCompleteLattice α] [ConditionallyCompleteLattice β]
  [ConditionallyCompleteLattice γ] {f : α → β → γ} {s : Set α} {t : Set β}

variable {l u : α → β → γ} {l₁ u₁ : β → γ → α} {l₂ u₂ : α → γ → β}

theorem csSup_image2_eq_csSup_csSup (h₁ : ∀ b, GaloisConnection (swap l b) (u₁ b))
    (h₂ : ∀ a, GaloisConnection (l a) (u₂ a)) (hs₀ : s.Nonempty) (hs₁ : BddAbove s)
    (ht₀ : t.Nonempty) (ht₁ : BddAbove t) : sSup (image2 l s t) = l (sSup s) (sSup t) := by
  refine eq_of_forall_ge_iff fun c => ?_
  rw [csSup_le_iff (hs₁.image2 (fun _ => (h₁ _).monotone_l) (fun _ => (h₂ _).monotone_l) ht₁)
      (hs₀.image2 ht₀),
    forall_image2_iff, forall₂_swap, (h₂ _).le_iff_le, csSup_le_iff ht₁ ht₀]
  simp_rw [← (h₂ _).le_iff_le, (h₁ _).le_iff_le, csSup_le_iff hs₁ hs₀]

theorem csSup_image2_eq_csSup_csInf (h₁ : ∀ b, GaloisConnection (swap l b) (u₁ b))
    (h₂ : ∀ a, GaloisConnection (l a ∘ ofDual) (toDual ∘ u₂ a)) :
    s.Nonempty → BddAbove s → t.Nonempty → BddBelow t → sSup (image2 l s t) = l (sSup s) (sInf t) :=
  csSup_image2_eq_csSup_csSup (β := βᵒᵈ) h₁ h₂

theorem csSup_image2_eq_csInf_csSup (h₁ : ∀ b, GaloisConnection (swap l b ∘ ofDual) (toDual ∘ u₁ b))
    (h₂ : ∀ a, GaloisConnection (l a) (u₂ a)) :
    s.Nonempty → BddBelow s → t.Nonempty → BddAbove t → sSup (image2 l s t) = l (sInf s) (sSup t) :=
  csSup_image2_eq_csSup_csSup (α := αᵒᵈ) h₁ h₂

theorem csSup_image2_eq_csInf_csInf (h₁ : ∀ b, GaloisConnection (swap l b ∘ ofDual) (toDual ∘ u₁ b))
    (h₂ : ∀ a, GaloisConnection (l a ∘ ofDual) (toDual ∘ u₂ a)) :
    s.Nonempty → BddBelow s → t.Nonempty → BddBelow t → sSup (image2 l s t) = l (sInf s) (sInf t) :=
  csSup_image2_eq_csSup_csSup (α := αᵒᵈ) (β := βᵒᵈ) h₁ h₂

theorem csInf_image2_eq_csInf_csInf (h₁ : ∀ b, GaloisConnection (l₁ b) (swap u b))
    (h₂ : ∀ a, GaloisConnection (l₂ a) (u a)) :
    s.Nonempty → BddBelow s → t.Nonempty → BddBelow t → sInf (image2 u s t) = u (sInf s) (sInf t) :=
  csSup_image2_eq_csSup_csSup (α := αᵒᵈ) (β := βᵒᵈ) (γ := γᵒᵈ) (u₁ := l₁) (u₂ := l₂)
    (fun _ => (h₁ _).dual) fun _ => (h₂ _).dual

theorem csInf_image2_eq_csInf_csSup (h₁ : ∀ b, GaloisConnection (l₁ b) (swap u b))
    (h₂ : ∀ a, GaloisConnection (toDual ∘ l₂ a) (u a ∘ ofDual)) :
    s.Nonempty → BddBelow s → t.Nonempty → BddAbove t → sInf (image2 u s t) = u (sInf s) (sSup t) :=
  csInf_image2_eq_csInf_csInf (β := βᵒᵈ) h₁ h₂

theorem csInf_image2_eq_csSup_csInf (h₁ : ∀ b, GaloisConnection (toDual ∘ l₁ b) (swap u b ∘ ofDual))
    (h₂ : ∀ a, GaloisConnection (l₂ a) (u a)) :
    s.Nonempty → BddAbove s → t.Nonempty → BddBelow t → sInf (image2 u s t) = u (sSup s) (sInf t) :=
  csInf_image2_eq_csInf_csInf (α := αᵒᵈ) h₁ h₂

theorem csInf_image2_eq_csSup_csSup (h₁ : ∀ b, GaloisConnection (toDual ∘ l₁ b) (swap u b ∘ ofDual))
    (h₂ : ∀ a, GaloisConnection (toDual ∘ l₂ a) (u a ∘ ofDual)) :
    s.Nonempty → BddAbove s → t.Nonempty → BddAbove t → sInf (image2 u s t) = u (sSup s) (sSup t) :=
  csInf_image2_eq_csInf_csInf (α := αᵒᵈ) (β := βᵒᵈ) h₁ h₂

end

section WithTopBot

/-!
### Complete lattice structure on `WithTop (WithBot α)`

If `α` is a `ConditionallyCompleteLattice`, then we show that `WithTop α` and `WithBot α`
also inherit the structure of conditionally complete lattices. Furthermore, we show
that `WithTop (WithBot α)` and `WithBot (WithTop α)` naturally inherit the structure of a
complete lattice. Note that for `α` a conditionally complete lattice, `sSup` and `sInf` both return
junk values for sets which are empty or unbounded. The extension of `sSup` to `WithTop α` fixes
the unboundedness problem and the extension to `WithBot α` fixes the problem with
the empty set.

This result can be used to show that the extended reals `[-∞, ∞]` are a complete linear order.
-/


/-- Adding a top element to a conditionally complete lattice
gives a conditionally complete lattice -/
noncomputable instance WithTop.conditionallyCompleteLattice {α : Type*}
    [ConditionallyCompleteLattice α] : ConditionallyCompleteLattice (WithTop α) :=
  { lattice, instSupSet, instInfSet with
    le_csSup := fun _ a _ haS => (WithTop.isLUB_sSup' ⟨a, haS⟩).1 haS
    csSup_le := fun _ _ hS haS => (WithTop.isLUB_sSup' hS).2 haS
    csInf_le := fun _ _ hS haS => (WithTop.isGLB_sInf' hS).1 haS
    le_csInf := fun _ a _ haS => (WithTop.isGLB_sInf' ⟨a, haS⟩).2 haS }

/-- Adding a bottom element to a conditionally complete lattice
gives a conditionally complete lattice -/
noncomputable instance WithBot.conditionallyCompleteLattice {α : Type*}
    [ConditionallyCompleteLattice α] : ConditionallyCompleteLattice (WithBot α) :=
  { WithBot.lattice with
    le_csSup := (WithTop.conditionallyCompleteLattice (α := αᵒᵈ)).csInf_le
    csSup_le := (WithTop.conditionallyCompleteLattice (α := αᵒᵈ)).le_csInf
    csInf_le := (WithTop.conditionallyCompleteLattice (α := αᵒᵈ)).le_csSup
    le_csInf := (WithTop.conditionallyCompleteLattice (α := αᵒᵈ)).csSup_le }

open Classical in
-- Porting note: `convert @bot_le (WithTop (WithBot α)) _ _ a` was `convert bot_le`
noncomputable instance WithTop.WithBot.completeLattice {α : Type*}
    [ConditionallyCompleteLattice α] : CompleteLattice (WithTop (WithBot α)) :=
  { instInfSet, instSupSet, boundedOrder, lattice with
    le_sSup := fun S a haS => (WithTop.isLUB_sSup' ⟨a, haS⟩).1 haS
    sSup_le := fun S a ha => by
      rcases S.eq_empty_or_nonempty with h | h
      · show ite _ _ _ ≤ a
        split_ifs with h₁ h₂
        · rw [h] at h₁
          cases h₁
        · convert bot_le (a := a)
          -- Porting note: previous proof relied on convert unfolding
          -- the definition of ⊥
          apply congr_arg
          simp only [h, preimage_empty, WithBot.sSup_empty]
        · exfalso
          apply h₂
          use ⊥
          rw [h]
          rintro b ⟨⟩
      · exact (WithTop.isLUB_sSup' h).2 ha
    sInf_le := fun S a haS =>
      show ite _ _ _ ≤ a by
        simp only [OrderBot.bddBelow, not_true_eq_false, or_false]
        split_ifs with h₁
        · cases' a with a
          · exact le_rfl
          cases h₁ haS
        · cases a
          · exact le_top
          · apply WithTop.coe_le_coe.2
            refine csInf_le ?_ haS
            use ⊥
            intro b _
            exact bot_le
    le_sInf := fun S a haS => (WithTop.isGLB_sInf' ⟨a, haS⟩).2 haS }

noncomputable instance WithTop.WithBot.completeLinearOrder {α : Type*}
    [ConditionallyCompleteLinearOrder α] : CompleteLinearOrder (WithTop (WithBot α)) :=
  -- FIXME: Spread notation doesn't work
  { completeLattice, linearOrder, LinearOrder.toBiheytingAlgebra with }

noncomputable instance WithBot.WithTop.completeLattice {α : Type*}
    [ConditionallyCompleteLattice α] : CompleteLattice (WithBot (WithTop α)) :=
  { instInfSet, instSupSet, instBoundedOrder, lattice with
    le_sSup := (WithTop.WithBot.completeLattice (α := αᵒᵈ)).sInf_le
    sSup_le := (WithTop.WithBot.completeLattice (α := αᵒᵈ)).le_sInf
    sInf_le := (WithTop.WithBot.completeLattice (α := αᵒᵈ)).le_sSup
    le_sInf := (WithTop.WithBot.completeLattice (α := αᵒᵈ)).sSup_le }

noncomputable instance WithBot.WithTop.completeLinearOrder {α : Type*}
    [ConditionallyCompleteLinearOrder α] : CompleteLinearOrder (WithBot (WithTop α)) :=
  { completeLattice, linearOrder, LinearOrder.toBiheytingAlgebra with }

namespace WithTop
variable [ConditionallyCompleteLinearOrderBot α] {f : ι → α}

lemma iSup_coe_eq_top : ⨆ x, (f x : WithTop α) = ⊤ ↔ ¬BddAbove (range f) := by
  rw [iSup_eq_top, not_bddAbove_iff]
  refine ⟨fun hf r => ?_, fun hf a ha => ?_⟩
  · rcases hf r (WithTop.coe_lt_top r) with ⟨i, hi⟩
    exact ⟨f i, ⟨i, rfl⟩, WithTop.coe_lt_coe.mp hi⟩
  · rcases hf (a.untop ha.ne) with ⟨-, ⟨i, rfl⟩, hi⟩
    exact ⟨i, by simpa only [WithTop.coe_untop _ ha.ne] using WithTop.coe_lt_coe.mpr hi⟩

lemma iSup_coe_lt_top : ⨆ x, (f x : WithTop α) < ⊤ ↔ BddAbove (range f) :=
  lt_top_iff_ne_top.trans iSup_coe_eq_top.not_left

lemma iInf_coe_eq_top : ⨅ x, (f x : WithTop α) = ⊤ ↔ IsEmpty ι := by simp [isEmpty_iff]

lemma iInf_coe_lt_top : ⨅ i, (f i : WithTop α) < ⊤ ↔ Nonempty ι := by
  rw [lt_top_iff_ne_top, Ne, iInf_coe_eq_top, not_isEmpty_iff]

end WithTop
end WithTopBot
