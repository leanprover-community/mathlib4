/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module order.conditionally_complete_lattice.basic
! leanprover-community/mathlib commit 207cfac9fcd06138865b5d04f7091e46d9320432
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Bounds.Basic
import Mathbin.Order.WellFounded
import Mathbin.Data.Set.Intervals.Basic
import Mathbin.Data.Set.Lattice

/-!
# Theory of conditionally complete lattices.

A conditionally complete lattice is a lattice in which every non-empty bounded subset `s`
has a least upper bound and a greatest lower bound, denoted below by `Sup s` and `Inf s`.
Typical examples are `ℝ`, `ℕ`, and `ℤ` with their usual orders.

The theory is very comparable to the theory of complete lattices, except that suitable
boundedness and nonemptiness assumptions have to be added to most statements.
We introduce two predicates `bdd_above` and `bdd_below` to express this boundedness, prove
their basic properties, and then go on to prove most useful properties of `Sup` and `Inf`
in conditionally complete lattices.

To differentiate the statements between complete lattices and conditionally complete
lattices, we prefix `Inf` and `Sup` in the statements by `c`, giving `cInf` and `cSup`.
For instance, `Inf_le` is a statement in complete lattices ensuring `Inf s ≤ x`,
while `cInf_le` is the same statement in conditionally complete lattices
with an additional assumption that `s` is bounded below.
-/


open Function OrderDual Set

variable {α β γ : Type _} {ι : Sort _}

section

/-!
Extension of Sup and Inf from a preorder `α` to `with_top α` and `with_bot α`
-/


open Classical

noncomputable instance {α : Type _} [Preorder α] [SupSet α] : SupSet (WithTop α) :=
  ⟨fun S =>
    if ⊤ ∈ S then ⊤ else if BddAbove (coe ⁻¹' S : Set α) then ↑(supₛ (coe ⁻¹' S : Set α)) else ⊤⟩

noncomputable instance {α : Type _} [InfSet α] : InfSet (WithTop α) :=
  ⟨fun S => if S ⊆ {⊤} then ⊤ else ↑(infₛ (coe ⁻¹' S : Set α))⟩

noncomputable instance {α : Type _} [SupSet α] : SupSet (WithBot α) :=
  ⟨(@WithTop.hasInf αᵒᵈ _).inf⟩

noncomputable instance {α : Type _} [Preorder α] [InfSet α] : InfSet (WithBot α) :=
  ⟨(@WithTop.hasSup αᵒᵈ _ _).sup⟩

@[simp]
theorem WithTop.cInf_empty {α : Type _} [InfSet α] : infₛ (∅ : Set (WithTop α)) = ⊤ :=
  if_pos <| Set.empty_subset _
#align with_top.cInf_empty WithTop.cInf_empty

@[simp]
theorem WithTop.cinfi_empty {α : Type _} [IsEmpty ι] [InfSet α] (f : ι → WithTop α) :
    (⨅ i, f i) = ⊤ := by rw [infi, range_eq_empty, WithTop.cInf_empty]
#align with_top.cinfi_empty WithTop.cinfi_empty

theorem WithTop.coe_Inf' [InfSet α] {s : Set α} (hs : s.Nonempty) :
    ↑(infₛ s) = (infₛ (coe '' s) : WithTop α) := by
  obtain ⟨x, hx⟩ := hs
  change _ = ite _ _ _
  split_ifs
  · cases h (mem_image_of_mem _ hx)
  · rw [preimage_image_eq]
    exact Option.some_injective _
#align with_top.coe_Inf' WithTop.coe_Inf'

@[norm_cast]
theorem WithTop.coe_infi [Nonempty ι] [InfSet α] (f : ι → α) :
    ↑(⨅ i, f i) = (⨅ i, f i : WithTop α) := by
  rw [infi, infi, WithTop.coe_Inf' (range_nonempty f), range_comp]
#align with_top.coe_infi WithTop.coe_infi

theorem WithTop.coe_Sup' [Preorder α] [SupSet α] {s : Set α} (hs : BddAbove s) :
    ↑(supₛ s) = (supₛ (coe '' s) : WithTop α) := by
  change _ = ite _ _ _
  rw [if_neg, preimage_image_eq, if_pos hs]
  · exact Option.some_injective _
  · rintro ⟨x, h, ⟨⟩⟩
#align with_top.coe_Sup' WithTop.coe_Sup'

@[norm_cast]
theorem WithTop.coe_supr [Preorder α] [SupSet α] (f : ι → α) (h : BddAbove (Set.range f)) :
    ↑(⨆ i, f i) = (⨆ i, f i : WithTop α) := by rw [supᵢ, supᵢ, WithTop.coe_Sup' h, range_comp]
#align with_top.coe_supr WithTop.coe_supr

@[simp]
theorem WithBot.cSup_empty {α : Type _} [SupSet α] : supₛ (∅ : Set (WithBot α)) = ⊥ :=
  if_pos <| Set.empty_subset _
#align with_bot.cSup_empty WithBot.cSup_empty

@[simp]
theorem WithBot.csupr_empty {α : Type _} [IsEmpty ι] [SupSet α] (f : ι → WithBot α) :
    (⨆ i, f i) = ⊥ :=
  @WithTop.cinfi_empty _ αᵒᵈ _ _ _
#align with_bot.csupr_empty WithBot.csupr_empty

@[norm_cast]
theorem WithBot.coe_Sup' [SupSet α] {s : Set α} (hs : s.Nonempty) :
    ↑(supₛ s) = (supₛ (coe '' s) : WithBot α) :=
  @WithTop.coe_Inf' αᵒᵈ _ _ hs
#align with_bot.coe_Sup' WithBot.coe_Sup'

@[norm_cast]
theorem WithBot.coe_supr [Nonempty ι] [SupSet α] (f : ι → α) :
    ↑(⨆ i, f i) = (⨆ i, f i : WithBot α) :=
  @WithTop.coe_infi αᵒᵈ _ _ _ _
#align with_bot.coe_supr WithBot.coe_supr

@[norm_cast]
theorem WithBot.coe_Inf' [Preorder α] [InfSet α] {s : Set α} (hs : BddBelow s) :
    ↑(infₛ s) = (infₛ (coe '' s) : WithBot α) :=
  @WithTop.coe_Sup' αᵒᵈ _ _ _ hs
#align with_bot.coe_Inf' WithBot.coe_Inf'

@[norm_cast]
theorem WithBot.coe_infi [Preorder α] [InfSet α] (f : ι → α) (h : BddBelow (Set.range f)) :
    ↑(⨅ i, f i) = (⨅ i, f i : WithBot α) :=
  @WithTop.coe_supr αᵒᵈ _ _ _ _ h
#align with_bot.coe_infi WithBot.coe_infi

end

-- section
/-- A conditionally complete lattice is a lattice in which
every nonempty subset which is bounded above has a supremum, and
every nonempty subset which is bounded below has an infimum.
Typical examples are real numbers or natural numbers.

To differentiate the statements from the corresponding statements in (unconditional)
complete lattices, we prefix Inf and Sup by a c everywhere. The same statements should
hold in both worlds, sometimes with additional assumptions of nonemptiness or
boundedness.-/
class ConditionallyCompleteLattice (α : Type _) extends Lattice α, SupSet α, InfSet α where
  le_cSup : ∀ s a, BddAbove s → a ∈ s → a ≤ Sup s
  cSup_le : ∀ s a, Set.Nonempty s → a ∈ upperBounds s → Sup s ≤ a
  cInf_le : ∀ s a, BddBelow s → a ∈ s → Inf s ≤ a
  le_cInf : ∀ s a, Set.Nonempty s → a ∈ lowerBounds s → a ≤ Inf s
#align conditionally_complete_lattice ConditionallyCompleteLattice

/- ./././Mathport/Syntax/Translate/Command.lean:407:11: unsupported: advanced extends in structure -/
/-- A conditionally complete linear order is a linear order in which
every nonempty subset which is bounded above has a supremum, and
every nonempty subset which is bounded below has an infimum.
Typical examples are real numbers or natural numbers.

To differentiate the statements from the corresponding statements in (unconditional)
complete linear orders, we prefix Inf and Sup by a c everywhere. The same statements should
hold in both worlds, sometimes with additional assumptions of nonemptiness or
boundedness.-/
class ConditionallyCompleteLinearOrder (α : Type _) extends ConditionallyCompleteLattice α,
  "./././Mathport/Syntax/Translate/Command.lean:407:11: unsupported: advanced extends in structure"
#align conditionally_complete_linear_order ConditionallyCompleteLinearOrder

/-- A conditionally complete linear order with `bot` is a linear order with least element, in which
every nonempty subset which is bounded above has a supremum, and every nonempty subset (necessarily
bounded below) has an infimum.  A typical example is the natural numbers.

To differentiate the statements from the corresponding statements in (unconditional)
complete linear orders, we prefix Inf and Sup by a c everywhere. The same statements should
hold in both worlds, sometimes with additional assumptions of nonemptiness or
boundedness.-/
class ConditionallyCompleteLinearOrderBot (α : Type _) extends ConditionallyCompleteLinearOrder α,
  Bot α where
  bot_le : ∀ x : α, ⊥ ≤ x
  cSup_empty : Sup ∅ = ⊥
#align conditionally_complete_linear_order_bot ConditionallyCompleteLinearOrderBot

-- see Note [lower instance priority]
instance (priority := 100) ConditionallyCompleteLinearOrderBot.toOrderBot
    [h : ConditionallyCompleteLinearOrderBot α] : OrderBot α :=
  { h with }
#align
  conditionally_complete_linear_order_bot.to_order_bot ConditionallyCompleteLinearOrderBot.toOrderBot

-- see Note [lower instance priority]
/-- A complete lattice is a conditionally complete lattice, as there are no restrictions
on the properties of Inf and Sup in a complete lattice.-/
instance (priority := 100) CompleteLattice.toConditionallyCompleteLattice [CompleteLattice α] :
    ConditionallyCompleteLattice α :=
  { ‹CompleteLattice α› with
    le_cSup := by intros <;> apply le_supₛ <;> assumption
    cSup_le := by intros <;> apply supₛ_le <;> assumption
    cInf_le := by intros <;> apply infₛ_le <;> assumption
    le_cInf := by intros <;> apply le_infₛ <;> assumption }
#align
  complete_lattice.to_conditionally_complete_lattice CompleteLattice.toConditionallyCompleteLattice

-- see Note [lower instance priority]
instance (priority := 100) CompleteLinearOrder.toConditionallyCompleteLinearOrderBot {α : Type _}
    [CompleteLinearOrder α] : ConditionallyCompleteLinearOrderBot α :=
  { CompleteLattice.toConditionallyCompleteLattice, ‹CompleteLinearOrder α› with
    cSup_empty := supₛ_empty }
#align
  complete_linear_order.to_conditionally_complete_linear_order_bot CompleteLinearOrder.toConditionallyCompleteLinearOrderBot

section

open Classical

/-- A well founded linear order is conditionally complete, with a bottom element. -/
@[reducible]
noncomputable def IsWellOrder.conditionallyCompleteLinearOrderBot (α : Type _) [i₁ : LinearOrder α]
    [i₂ : OrderBot α] [h : IsWellOrder α (· < ·)] : ConditionallyCompleteLinearOrderBot α :=
  { i₁, i₂, LinearOrder.toLattice with
    inf := fun s => if hs : s.Nonempty then h.wf.min s hs else ⊥
    cInf_le := fun s a hs has => by 
      have s_ne : s.nonempty := ⟨a, has⟩
      simpa [s_ne] using not_lt.1 (h.wf.not_lt_min s s_ne has)
    le_cInf := fun s a hs has => by 
      simp only [hs, dif_pos]
      exact has (h.wf.min_mem s hs)
    sup := fun s => if hs : (upperBounds s).Nonempty then h.wf.min _ hs else ⊥
    le_cSup := fun s a hs has => by
      have h's : (upperBounds s).Nonempty := hs
      simp only [h's, dif_pos]
      exact h.wf.min_mem _ h's has
    cSup_le := fun s a hs has => by
      have h's : (upperBounds s).Nonempty := ⟨a, has⟩
      simp only [h's, dif_pos]
      simpa using h.wf.not_lt_min _ h's has
    cSup_empty := by simpa using eq_bot_iff.2 (not_lt.1 <| h.wf.not_lt_min _ _ <| mem_univ ⊥) }
#align
  is_well_order.conditionally_complete_linear_order_bot IsWellOrder.conditionallyCompleteLinearOrderBot

end

section OrderDual

instance (α : Type _) [ConditionallyCompleteLattice α] : ConditionallyCompleteLattice αᵒᵈ :=
  { OrderDual.hasInf α, OrderDual.hasSup α, OrderDual.lattice α with
    le_cSup := @ConditionallyCompleteLattice.cInf_le α _
    cSup_le := @ConditionallyCompleteLattice.le_cInf α _
    le_cInf := @ConditionallyCompleteLattice.cSup_le α _
    cInf_le := @ConditionallyCompleteLattice.le_cSup α _ }

instance (α : Type _) [ConditionallyCompleteLinearOrder α] : ConditionallyCompleteLinearOrder αᵒᵈ :=
  { OrderDual.conditionallyCompleteLattice α, OrderDual.linearOrder α with }

end OrderDual

/-- Create a `conditionally_complete_lattice` from a `partial_order` and `Sup` function
that returns the least upper bound of a nonempty set which is bounded above. Usually this
constructor provides poor definitional equalities.  If other fields are known explicitly, they
should be provided; for example, if `inf` is known explicitly, construct the
`conditionally_complete_lattice` instance as
```
instance : conditionally_complete_lattice my_T :=
{ inf := better_inf,
  le_inf := ...,
  inf_le_right := ...,
  inf_le_left := ...
  -- don't care to fix sup, Inf
  ..conditionally_complete_lattice_of_Sup my_T _ }
```
-/
def conditionallyCompleteLatticeOfSup (α : Type _) [H1 : PartialOrder α] [H2 : SupSet α]
    (bdd_above_pair : ∀ a b : α, BddAbove ({a, b} : Set α))
    (bdd_below_pair : ∀ a b : α, BddBelow ({a, b} : Set α))
    (is_lub_Sup : ∀ s : Set α, BddAbove s → s.Nonempty → IsLUB s (supₛ s)) :
    ConditionallyCompleteLattice α :=
  { H1, H2 with 
    sup := fun a b => supₛ {a, b}
    le_sup_left := fun a b =>
      (is_lub_Sup {a, b} (bdd_above_pair a b) (insert_nonempty _ _)).1 (mem_insert _ _)
    le_sup_right := fun a b =>
      (is_lub_Sup {a, b} (bdd_above_pair a b) (insert_nonempty _ _)).1
        (mem_insert_of_mem _ (mem_singleton _))
    sup_le := fun a b c hac hbc =>
      (is_lub_Sup {a, b} (bdd_above_pair a b) (insert_nonempty _ _)).2
        (forall_insert_of_forall (forall_eq.mpr hbc) hac)
    inf := fun a b => supₛ (lowerBounds {a, b})
    inf_le_left := fun a b =>
      (is_lub_Sup (lowerBounds {a, b}) (Nonempty.bddAbove_lowerBounds ⟨a, mem_insert _ _⟩)
            (bdd_below_pair a b)).2
        fun c hc => hc <| mem_insert _ _
    inf_le_right := fun a b =>
      (is_lub_Sup (lowerBounds {a, b}) (Nonempty.bddAbove_lowerBounds ⟨a, mem_insert _ _⟩)
            (bdd_below_pair a b)).2
        fun c hc => hc <| mem_insert_of_mem _ (mem_singleton _)
    le_inf := fun c a b hca hcb =>
      (is_lub_Sup (lowerBounds {a, b}) (Nonempty.bddAbove_lowerBounds ⟨a, mem_insert _ _⟩)
            ⟨c, forall_insert_of_forall (forall_eq.mpr hcb) hca⟩).1
        (forall_insert_of_forall (forall_eq.mpr hcb) hca)
    inf := fun s => supₛ (lowerBounds s)
    cSup_le := fun s a hs ha => (is_lub_Sup s ⟨a, ha⟩ hs).2 ha
    le_cSup := fun s a hs ha => (is_lub_Sup s hs ⟨a, ha⟩).1 ha
    cInf_le := fun s a hs ha =>
      (is_lub_Sup (lowerBounds s) (Nonempty.bddAbove_lowerBounds ⟨a, ha⟩) hs).2 fun b hb => hb ha
    le_cInf := fun s a hs ha =>
      (is_lub_Sup (lowerBounds s) hs.bdd_above_lower_bounds ⟨a, ha⟩).1 ha }
#align conditionally_complete_lattice_of_Sup conditionallyCompleteLatticeOfSup

/-- Create a `conditionally_complete_lattice_of_Inf` from a `partial_order` and `Inf` function
that returns the greatest lower bound of a nonempty set which is bounded below. Usually this
constructor provides poor definitional equalities.  If other fields are known explicitly, they
should be provided; for example, if `inf` is known explicitly, construct the
`conditionally_complete_lattice` instance as
```
instance : conditionally_complete_lattice my_T :=
{ inf := better_inf,
  le_inf := ...,
  inf_le_right := ...,
  inf_le_left := ...
  -- don't care to fix sup, Sup
  ..conditionally_complete_lattice_of_Inf my_T _ }
```
-/
def conditionallyCompleteLatticeOfInf (α : Type _) [H1 : PartialOrder α] [H2 : InfSet α]
    (bdd_above_pair : ∀ a b : α, BddAbove ({a, b} : Set α))
    (bdd_below_pair : ∀ a b : α, BddBelow ({a, b} : Set α))
    (is_glb_Inf : ∀ s : Set α, BddBelow s → s.Nonempty → IsGLB s (infₛ s)) :
    ConditionallyCompleteLattice α :=
  { H1, H2 with 
    inf := fun a b => infₛ {a, b}
    inf_le_left := fun a b =>
      (is_glb_Inf {a, b} (bdd_below_pair a b) (insert_nonempty _ _)).1 (mem_insert _ _)
    inf_le_right := fun a b =>
      (is_glb_Inf {a, b} (bdd_below_pair a b) (insert_nonempty _ _)).1
        (mem_insert_of_mem _ (mem_singleton _))
    le_inf := fun c a b hca hcb =>
      (is_glb_Inf {a, b} (bdd_below_pair a b) (insert_nonempty _ _)).2
        (forall_insert_of_forall (forall_eq.mpr hcb) hca)
    sup := fun a b => infₛ (upperBounds {a, b})
    le_sup_left := fun a b =>
      (is_glb_Inf (upperBounds {a, b}) (Nonempty.bddBelow_upperBounds ⟨a, mem_insert _ _⟩)
            (bdd_above_pair a b)).2
        fun c hc => hc <| mem_insert _ _
    le_sup_right := fun a b =>
      (is_glb_Inf (upperBounds {a, b}) (Nonempty.bddBelow_upperBounds ⟨a, mem_insert _ _⟩)
            (bdd_above_pair a b)).2
        fun c hc => hc <| mem_insert_of_mem _ (mem_singleton _)
    sup_le := fun a b c hac hbc =>
      (is_glb_Inf (upperBounds {a, b}) (Nonempty.bddBelow_upperBounds ⟨a, mem_insert _ _⟩)
            ⟨c, forall_insert_of_forall (forall_eq.mpr hbc) hac⟩).1
        (forall_insert_of_forall (forall_eq.mpr hbc) hac)
    sup := fun s => infₛ (upperBounds s)
    le_cInf := fun s a hs ha => (is_glb_Inf s ⟨a, ha⟩ hs).2 ha
    cInf_le := fun s a hs ha => (is_glb_Inf s hs ⟨a, ha⟩).1 ha
    le_cSup := fun s a hs ha =>
      (is_glb_Inf (upperBounds s) (Nonempty.bddBelow_upperBounds ⟨a, ha⟩) hs).2 fun b hb => hb ha
    cSup_le := fun s a hs ha =>
      (is_glb_Inf (upperBounds s) hs.bdd_below_upper_bounds ⟨a, ha⟩).1 ha }
#align conditionally_complete_lattice_of_Inf conditionallyCompleteLatticeOfInf

/-- A version of `conditionally_complete_lattice_of_Sup` when we already know that `α` is a lattice.

This should only be used when it is both hard and unnecessary to provide `Inf` explicitly. -/
def conditionallyCompleteLatticeOfLatticeOfSup (α : Type _) [H1 : Lattice α] [H2 : SupSet α]
    (is_lub_Sup : ∀ s : Set α, BddAbove s → s.Nonempty → IsLUB s (supₛ s)) :
    ConditionallyCompleteLattice α :=
  { H1,
    conditionallyCompleteLatticeOfSup α
      (fun a b => ⟨a ⊔ b, forall_insert_of_forall (forall_eq.mpr le_sup_right) le_sup_left⟩)
      (fun a b => ⟨a ⊓ b, forall_insert_of_forall (forall_eq.mpr inf_le_right) inf_le_left⟩)
      is_lub_Sup with }
#align conditionally_complete_lattice_of_lattice_of_Sup conditionallyCompleteLatticeOfLatticeOfSup

/-- A version of `conditionally_complete_lattice_of_Inf` when we already know that `α` is a lattice.

This should only be used when it is both hard and unnecessary to provide `Sup` explicitly. -/
def conditionallyCompleteLatticeOfLatticeOfInf (α : Type _) [H1 : Lattice α] [H2 : InfSet α]
    (is_glb_Inf : ∀ s : Set α, BddBelow s → s.Nonempty → IsGLB s (infₛ s)) :
    ConditionallyCompleteLattice α :=
  { H1,
    conditionallyCompleteLatticeOfInf α
      (fun a b => ⟨a ⊔ b, forall_insert_of_forall (forall_eq.mpr le_sup_right) le_sup_left⟩)
      (fun a b => ⟨a ⊓ b, forall_insert_of_forall (forall_eq.mpr inf_le_right) inf_le_left⟩)
      is_glb_Inf with }
#align conditionally_complete_lattice_of_lattice_of_Inf conditionallyCompleteLatticeOfLatticeOfInf

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice α] {s t : Set α} {a b : α}

theorem le_cSup (h₁ : BddAbove s) (h₂ : a ∈ s) : a ≤ supₛ s :=
  ConditionallyCompleteLattice.le_cSup s a h₁ h₂
#align le_cSup le_cSup

theorem cSup_le (h₁ : s.Nonempty) (h₂ : ∀ b ∈ s, b ≤ a) : supₛ s ≤ a :=
  ConditionallyCompleteLattice.cSup_le s a h₁ h₂
#align cSup_le cSup_le

theorem cInf_le (h₁ : BddBelow s) (h₂ : a ∈ s) : infₛ s ≤ a :=
  ConditionallyCompleteLattice.cInf_le s a h₁ h₂
#align cInf_le cInf_le

theorem le_cInf (h₁ : s.Nonempty) (h₂ : ∀ b ∈ s, a ≤ b) : a ≤ infₛ s :=
  ConditionallyCompleteLattice.le_cInf s a h₁ h₂
#align le_cInf le_cInf

theorem le_cSup_of_le (hs : BddAbove s) (hb : b ∈ s) (h : a ≤ b) : a ≤ supₛ s :=
  le_trans h (le_cSup hs hb)
#align le_cSup_of_le le_cSup_of_le

theorem cInf_le_of_le (hs : BddBelow s) (hb : b ∈ s) (h : b ≤ a) : infₛ s ≤ a :=
  le_trans (cInf_le hs hb) h
#align cInf_le_of_le cInf_le_of_le

theorem cSup_le_cSup (ht : BddAbove t) (hs : s.Nonempty) (h : s ⊆ t) : supₛ s ≤ supₛ t :=
  cSup_le hs fun a ha => le_cSup ht (h ha)
#align cSup_le_cSup cSup_le_cSup

theorem cInf_le_cInf (ht : BddBelow t) (hs : s.Nonempty) (h : s ⊆ t) : infₛ t ≤ infₛ s :=
  le_cInf hs fun a ha => cInf_le ht (h ha)
#align cInf_le_cInf cInf_le_cInf

theorem le_cSup_iff (h : BddAbove s) (hs : s.Nonempty) :
    a ≤ supₛ s ↔ ∀ b, b ∈ upperBounds s → a ≤ b :=
  ⟨fun h b hb => le_trans h (cSup_le hs hb), fun hb => hb _ fun x => le_cSup h⟩
#align le_cSup_iff le_cSup_iff

theorem cInf_le_iff (h : BddBelow s) (hs : s.Nonempty) : infₛ s ≤ a ↔ ∀ b ∈ lowerBounds s, b ≤ a :=
  ⟨fun h b hb => le_trans (le_cInf hs hb) h, fun hb => hb _ fun x => cInf_le h⟩
#align cInf_le_iff cInf_le_iff

theorem is_lub_cSup (ne : s.Nonempty) (H : BddAbove s) : IsLUB s (supₛ s) :=
  ⟨fun x => le_cSup H, fun x => cSup_le Ne⟩
#align is_lub_cSup is_lub_cSup

theorem is_lub_csupr [Nonempty ι] {f : ι → α} (H : BddAbove (range f)) :
    IsLUB (range f) (⨆ i, f i) :=
  is_lub_cSup (range_nonempty f) H
#align is_lub_csupr is_lub_csupr

theorem is_lub_csupr_set {f : β → α} {s : Set β} (H : BddAbove (f '' s)) (Hne : s.Nonempty) :
    IsLUB (f '' s) (⨆ i : s, f i) := by 
  rw [← supₛ_image']
  exact is_lub_cSup (Hne.image _) H
#align is_lub_csupr_set is_lub_csupr_set

theorem is_glb_cInf (ne : s.Nonempty) (H : BddBelow s) : IsGLB s (infₛ s) :=
  ⟨fun x => cInf_le H, fun x => le_cInf Ne⟩
#align is_glb_cInf is_glb_cInf

theorem is_glb_cinfi [Nonempty ι] {f : ι → α} (H : BddBelow (range f)) :
    IsGLB (range f) (⨅ i, f i) :=
  is_glb_cInf (range_nonempty f) H
#align is_glb_cinfi is_glb_cinfi

theorem is_glb_cinfi_set {f : β → α} {s : Set β} (H : BddBelow (f '' s)) (Hne : s.Nonempty) :
    IsGLB (f '' s) (⨅ i : s, f i) :=
  @is_lub_csupr_set αᵒᵈ _ _ _ _ H Hne
#align is_glb_cinfi_set is_glb_cinfi_set

theorem csupr_le_iff [Nonempty ι] {f : ι → α} {a : α} (hf : BddAbove (range f)) :
    supᵢ f ≤ a ↔ ∀ i, f i ≤ a :=
  (isLUB_le_iff <| is_lub_csupr hf).trans forall_range_iff
#align csupr_le_iff csupr_le_iff

theorem le_cinfi_iff [Nonempty ι] {f : ι → α} {a : α} (hf : BddBelow (range f)) :
    a ≤ infi f ↔ ∀ i, a ≤ f i :=
  (le_isGLB_iff <| is_glb_cinfi hf).trans forall_range_iff
#align le_cinfi_iff le_cinfi_iff

theorem csupr_set_le_iff {ι : Type _} {s : Set ι} {f : ι → α} {a : α} (hs : s.Nonempty)
    (hf : BddAbove (f '' s)) : (⨆ i : s, f i) ≤ a ↔ ∀ i ∈ s, f i ≤ a :=
  (isLUB_le_iff <| is_lub_csupr_set hf hs).trans ball_image_iff
#align csupr_set_le_iff csupr_set_le_iff

theorem le_cinfi_set_iff {ι : Type _} {s : Set ι} {f : ι → α} {a : α} (hs : s.Nonempty)
    (hf : BddBelow (f '' s)) : (a ≤ ⨅ i : s, f i) ↔ ∀ i ∈ s, a ≤ f i :=
  (le_isGLB_iff <| is_glb_cinfi_set hf hs).trans ball_image_iff
#align le_cinfi_set_iff le_cinfi_set_iff

theorem IsLUB.cSup_eq (H : IsLUB s a) (ne : s.Nonempty) : supₛ s = a :=
  (is_lub_cSup Ne ⟨a, H.1⟩).unique H
#align is_lub.cSup_eq IsLUB.cSup_eq

theorem IsLUB.csupr_eq [Nonempty ι] {f : ι → α} (H : IsLUB (range f) a) : (⨆ i, f i) = a :=
  H.cSup_eq (range_nonempty f)
#align is_lub.csupr_eq IsLUB.csupr_eq

theorem IsLUB.csupr_set_eq {s : Set β} {f : β → α} (H : IsLUB (f '' s) a) (Hne : s.Nonempty) :
    (⨆ i : s, f i) = a :=
  IsLUB.cSup_eq (image_eq_range f s ▸ H) (image_eq_range f s ▸ Hne.image f)
#align is_lub.csupr_set_eq IsLUB.csupr_set_eq

/-- A greatest element of a set is the supremum of this set. -/
theorem IsGreatest.cSup_eq (H : IsGreatest s a) : supₛ s = a :=
  H.IsLub.cSup_eq H.Nonempty
#align is_greatest.cSup_eq IsGreatest.cSup_eq

theorem IsGreatest.Sup_mem (H : IsGreatest s a) : supₛ s ∈ s :=
  H.cSup_eq.symm ▸ H.1
#align is_greatest.Sup_mem IsGreatest.Sup_mem

theorem IsGLB.cInf_eq (H : IsGLB s a) (ne : s.Nonempty) : infₛ s = a :=
  (is_glb_cInf Ne ⟨a, H.1⟩).unique H
#align is_glb.cInf_eq IsGLB.cInf_eq

theorem IsGLB.cinfi_eq [Nonempty ι] {f : ι → α} (H : IsGLB (range f) a) : (⨅ i, f i) = a :=
  H.cInf_eq (range_nonempty f)
#align is_glb.cinfi_eq IsGLB.cinfi_eq

theorem IsGLB.cinfi_set_eq {s : Set β} {f : β → α} (H : IsGLB (f '' s) a) (Hne : s.Nonempty) :
    (⨅ i : s, f i) = a :=
  IsGLB.cInf_eq (image_eq_range f s ▸ H) (image_eq_range f s ▸ Hne.image f)
#align is_glb.cinfi_set_eq IsGLB.cinfi_set_eq

/-- A least element of a set is the infimum of this set. -/
theorem IsLeast.cInf_eq (H : IsLeast s a) : infₛ s = a :=
  H.IsGlb.cInf_eq H.Nonempty
#align is_least.cInf_eq IsLeast.cInf_eq

theorem IsLeast.Inf_mem (H : IsLeast s a) : infₛ s ∈ s :=
  H.cInf_eq.symm ▸ H.1
#align is_least.Inf_mem IsLeast.Inf_mem

theorem subset_Icc_cInf_cSup (hb : BddBelow s) (ha : BddAbove s) : s ⊆ Icc (infₛ s) (supₛ s) :=
  fun x hx => ⟨cInf_le hb hx, le_cSup ha hx⟩
#align subset_Icc_cInf_cSup subset_Icc_cInf_cSup

theorem cSup_le_iff (hb : BddAbove s) (hs : s.Nonempty) : supₛ s ≤ a ↔ ∀ b ∈ s, b ≤ a :=
  isLUB_le_iff (is_lub_cSup hs hb)
#align cSup_le_iff cSup_le_iff

theorem le_cInf_iff (hb : BddBelow s) (hs : s.Nonempty) : a ≤ infₛ s ↔ ∀ b ∈ s, a ≤ b :=
  le_isGLB_iff (is_glb_cInf hs hb)
#align le_cInf_iff le_cInf_iff

theorem cSup_lower_bounds_eq_cInf {s : Set α} (h : BddBelow s) (hs : s.Nonempty) :
    supₛ (lowerBounds s) = infₛ s :=
  (is_lub_cSup h <| hs.mono fun x hx y hy => hy hx).unique (is_glb_cInf hs h).IsLub
#align cSup_lower_bounds_eq_cInf cSup_lower_bounds_eq_cInf

theorem cInf_upper_bounds_eq_cSup {s : Set α} (h : BddAbove s) (hs : s.Nonempty) :
    infₛ (upperBounds s) = supₛ s :=
  (is_glb_cInf h <| hs.mono fun x hx y hy => hy hx).unique (is_lub_cSup hs h).IsGlb
#align cInf_upper_bounds_eq_cSup cInf_upper_bounds_eq_cSup

theorem not_mem_of_lt_cInf {x : α} {s : Set α} (h : x < infₛ s) (hs : BddBelow s) : x ∉ s :=
  fun hx => lt_irrefl _ (h.trans_le (cInf_le hs hx))
#align not_mem_of_lt_cInf not_mem_of_lt_cInf

theorem not_mem_of_cSup_lt {x : α} {s : Set α} (h : supₛ s < x) (hs : BddAbove s) : x ∉ s :=
  @not_mem_of_lt_cInf αᵒᵈ _ x s h hs
#align not_mem_of_cSup_lt not_mem_of_cSup_lt

/-- Introduction rule to prove that `b` is the supremum of `s`: it suffices to check that `b`
is larger than all elements of `s`, and that this is not the case of any `w<b`.
See `Sup_eq_of_forall_le_of_forall_lt_exists_gt` for a version in complete lattices. -/
theorem cSup_eq_of_forall_le_of_forall_lt_exists_gt (hs : s.Nonempty) (H : ∀ a ∈ s, a ≤ b)
    (H' : ∀ w, w < b → ∃ a ∈ s, w < a) : supₛ s = b :=
  (eq_of_le_of_not_lt (cSup_le hs H)) fun hb =>
    let ⟨a, ha, ha'⟩ := H' _ hb
    lt_irrefl _ <| ha'.trans_le <| le_cSup ⟨b, H⟩ ha
#align cSup_eq_of_forall_le_of_forall_lt_exists_gt cSup_eq_of_forall_le_of_forall_lt_exists_gt

/-- Introduction rule to prove that `b` is the infimum of `s`: it suffices to check that `b`
is smaller than all elements of `s`, and that this is not the case of any `w>b`.
See `Inf_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in complete lattices. -/
theorem cInf_eq_of_forall_ge_of_forall_gt_exists_lt :
    s.Nonempty → (∀ a ∈ s, b ≤ a) → (∀ w, b < w → ∃ a ∈ s, a < w) → infₛ s = b :=
  @cSup_eq_of_forall_le_of_forall_lt_exists_gt αᵒᵈ _ _ _
#align cInf_eq_of_forall_ge_of_forall_gt_exists_lt cInf_eq_of_forall_ge_of_forall_gt_exists_lt

/-- b < Sup s when there is an element a in s with b < a, when s is bounded above.
This is essentially an iff, except that the assumptions for the two implications are
slightly different (one needs boundedness above for one direction, nonemptiness and linear
order for the other one), so we formulate separately the two implications, contrary to
the complete_lattice case.-/
theorem lt_cSup_of_lt (hs : BddAbove s) (ha : a ∈ s) (h : b < a) : b < supₛ s :=
  lt_of_lt_of_le h (le_cSup hs ha)
#align lt_cSup_of_lt lt_cSup_of_lt

/-- Inf s < b when there is an element a in s with a < b, when s is bounded below.
This is essentially an iff, except that the assumptions for the two implications are
slightly different (one needs boundedness below for one direction, nonemptiness and linear
order for the other one), so we formulate separately the two implications, contrary to
the complete_lattice case.-/
theorem cInf_lt_of_lt : BddBelow s → a ∈ s → a < b → infₛ s < b :=
  @lt_cSup_of_lt αᵒᵈ _ _ _ _
#align cInf_lt_of_lt cInf_lt_of_lt

/-- If all elements of a nonempty set `s` are less than or equal to all elements
of a nonempty set `t`, then there exists an element between these sets. -/
theorem exists_between_of_forall_le (sne : s.Nonempty) (tne : t.Nonempty)
    (hst : ∀ x ∈ s, ∀ y ∈ t, x ≤ y) : (upperBounds s ∩ lowerBounds t).Nonempty :=
  ⟨infₛ t, fun x hx => le_cInf tne <| hst x hx, fun y hy => cInf_le (sne.mono hst) hy⟩
#align exists_between_of_forall_le exists_between_of_forall_le

/-- The supremum of a singleton is the element of the singleton-/
@[simp]
theorem cSup_singleton (a : α) : supₛ {a} = a :=
  isGreatest_singleton.cSup_eq
#align cSup_singleton cSup_singleton

/-- The infimum of a singleton is the element of the singleton-/
@[simp]
theorem cInf_singleton (a : α) : infₛ {a} = a :=
  isLeast_singleton.cInf_eq
#align cInf_singleton cInf_singleton

@[simp]
theorem cSup_pair (a b : α) : supₛ {a, b} = a ⊔ b :=
  (@isLUB_pair _ _ a b).cSup_eq (insert_nonempty _ _)
#align cSup_pair cSup_pair

@[simp]
theorem cInf_pair (a b : α) : infₛ {a, b} = a ⊓ b :=
  (@isGLB_pair _ _ a b).cInf_eq (insert_nonempty _ _)
#align cInf_pair cInf_pair

/-- If a set is bounded below and above, and nonempty, its infimum is less than or equal to
its supremum.-/
theorem cInf_le_cSup (hb : BddBelow s) (ha : BddAbove s) (ne : s.Nonempty) : infₛ s ≤ supₛ s :=
  isGLB_le_isLUB (is_glb_cInf Ne hb) (is_lub_cSup Ne ha) Ne
#align cInf_le_cSup cInf_le_cSup

/-- The sup of a union of two sets is the max of the suprema of each subset, under the assumptions
that all sets are bounded above and nonempty.-/
theorem cSup_union (hs : BddAbove s) (sne : s.Nonempty) (ht : BddAbove t) (tne : t.Nonempty) :
    supₛ (s ∪ t) = supₛ s ⊔ supₛ t :=
  ((is_lub_cSup sne hs).union (is_lub_cSup tne ht)).cSup_eq sne.inl
#align cSup_union cSup_union

/-- The inf of a union of two sets is the min of the infima of each subset, under the assumptions
that all sets are bounded below and nonempty.-/
theorem cInf_union (hs : BddBelow s) (sne : s.Nonempty) (ht : BddBelow t) (tne : t.Nonempty) :
    infₛ (s ∪ t) = infₛ s ⊓ infₛ t :=
  @cSup_union αᵒᵈ _ _ _ hs sne ht tne
#align cInf_union cInf_union

/-- The supremum of an intersection of two sets is bounded by the minimum of the suprema of each
set, if all sets are bounded above and nonempty.-/
theorem cSup_inter_le (hs : BddAbove s) (ht : BddAbove t) (hst : (s ∩ t).Nonempty) :
    supₛ (s ∩ t) ≤ supₛ s ⊓ supₛ t :=
  (cSup_le hst) fun x hx => le_inf (le_cSup hs hx.1) (le_cSup ht hx.2)
#align cSup_inter_le cSup_inter_le

/-- The infimum of an intersection of two sets is bounded below by the maximum of the
infima of each set, if all sets are bounded below and nonempty.-/
theorem le_cInf_inter :
    BddBelow s → BddBelow t → (s ∩ t).Nonempty → infₛ s ⊔ infₛ t ≤ infₛ (s ∩ t) :=
  @cSup_inter_le αᵒᵈ _ _ _
#align le_cInf_inter le_cInf_inter

/-- The supremum of insert a s is the maximum of a and the supremum of s, if s is
nonempty and bounded above.-/
theorem cSup_insert (hs : BddAbove s) (sne : s.Nonempty) : supₛ (insert a s) = a ⊔ supₛ s :=
  ((is_lub_cSup sne hs).insert a).cSup_eq (insert_nonempty a s)
#align cSup_insert cSup_insert

/-- The infimum of insert a s is the minimum of a and the infimum of s, if s is
nonempty and bounded below.-/
theorem cInf_insert (hs : BddBelow s) (sne : s.Nonempty) : infₛ (insert a s) = a ⊓ infₛ s :=
  @cSup_insert αᵒᵈ _ _ _ hs sne
#align cInf_insert cInf_insert

@[simp]
theorem cInf_Icc (h : a ≤ b) : infₛ (Icc a b) = a :=
  (isGLB_Icc h).cInf_eq (nonempty_Icc.2 h)
#align cInf_Icc cInf_Icc

@[simp]
theorem cInf_Ici : infₛ (Ici a) = a :=
  isLeast_Ici.cInf_eq
#align cInf_Ici cInf_Ici

@[simp]
theorem cInf_Ico (h : a < b) : infₛ (Ico a b) = a :=
  (isGLB_Ico h).cInf_eq (nonempty_Ico.2 h)
#align cInf_Ico cInf_Ico

@[simp]
theorem cInf_Ioc [DenselyOrdered α] (h : a < b) : infₛ (Ioc a b) = a :=
  (isGLB_Ioc h).cInf_eq (nonempty_Ioc.2 h)
#align cInf_Ioc cInf_Ioc

@[simp]
theorem cInf_Ioi [NoMaxOrder α] [DenselyOrdered α] : infₛ (Ioi a) = a :=
  cInf_eq_of_forall_ge_of_forall_gt_exists_lt nonempty_Ioi (fun _ => le_of_lt) fun w hw => by
    simpa using exists_between hw
#align cInf_Ioi cInf_Ioi

@[simp]
theorem cInf_Ioo [DenselyOrdered α] (h : a < b) : infₛ (Ioo a b) = a :=
  (isGLB_Ioo h).cInf_eq (nonempty_Ioo.2 h)
#align cInf_Ioo cInf_Ioo

@[simp]
theorem cSup_Icc (h : a ≤ b) : supₛ (Icc a b) = b :=
  (isLUB_Icc h).cSup_eq (nonempty_Icc.2 h)
#align cSup_Icc cSup_Icc

@[simp]
theorem cSup_Ico [DenselyOrdered α] (h : a < b) : supₛ (Ico a b) = b :=
  (isLUB_Ico h).cSup_eq (nonempty_Ico.2 h)
#align cSup_Ico cSup_Ico

@[simp]
theorem cSup_Iic : supₛ (Iic a) = a :=
  isGreatest_Iic.cSup_eq
#align cSup_Iic cSup_Iic

@[simp]
theorem cSup_Iio [NoMinOrder α] [DenselyOrdered α] : supₛ (Iio a) = a :=
  cSup_eq_of_forall_le_of_forall_lt_exists_gt nonempty_Iio (fun _ => le_of_lt) fun w hw => by
    simpa [and_comm'] using exists_between hw
#align cSup_Iio cSup_Iio

@[simp]
theorem cSup_Ioc (h : a < b) : supₛ (Ioc a b) = b :=
  (isLUB_Ioc h).cSup_eq (nonempty_Ioc.2 h)
#align cSup_Ioc cSup_Ioc

@[simp]
theorem cSup_Ioo [DenselyOrdered α] (h : a < b) : supₛ (Ioo a b) = b :=
  (isLUB_Ioo h).cSup_eq (nonempty_Ioo.2 h)
#align cSup_Ioo cSup_Ioo

/-- The indexed supremum of a function is bounded above by a uniform bound-/
theorem csupr_le [Nonempty ι] {f : ι → α} {c : α} (H : ∀ x, f x ≤ c) : supᵢ f ≤ c :=
  cSup_le (range_nonempty f) (by rwa [forall_range_iff])
#align csupr_le csupr_le

/-- The indexed supremum of a function is bounded below by the value taken at one point-/
theorem le_csupr {f : ι → α} (H : BddAbove (range f)) (c : ι) : f c ≤ supᵢ f :=
  le_cSup H (mem_range_self _)
#align le_csupr le_csupr

theorem le_csupr_of_le {f : ι → α} (H : BddAbove (range f)) (c : ι) (h : a ≤ f c) : a ≤ supᵢ f :=
  le_trans h (le_csupr H c)
#align le_csupr_of_le le_csupr_of_le

/-- The indexed supremum of two functions are comparable if the functions are pointwise comparable-/
theorem csupr_mono {f g : ι → α} (B : BddAbove (range g)) (H : ∀ x, f x ≤ g x) : supᵢ f ≤ supᵢ g :=
  by 
  cases isEmpty_or_nonempty ι
  · rw [supᵢ_of_empty', supᵢ_of_empty']
  · exact csupr_le fun x => le_csupr_of_le B x (H x)
#align csupr_mono csupr_mono

theorem le_csupr_set {f : β → α} {s : Set β} (H : BddAbove (f '' s)) {c : β} (hc : c ∈ s) :
    f c ≤ ⨆ i : s, f i :=
  (le_cSup H <| mem_image_of_mem f hc).trans_eq supₛ_image'
#align le_csupr_set le_csupr_set

/-- The indexed infimum of two functions are comparable if the functions are pointwise comparable-/
theorem cinfi_mono {f g : ι → α} (B : BddBelow (range f)) (H : ∀ x, f x ≤ g x) : infi f ≤ infi g :=
  @csupr_mono αᵒᵈ _ _ _ _ B H
#align cinfi_mono cinfi_mono

/-- The indexed minimum of a function is bounded below by a uniform lower bound-/
theorem le_cinfi [Nonempty ι] {f : ι → α} {c : α} (H : ∀ x, c ≤ f x) : c ≤ infi f :=
  @csupr_le αᵒᵈ _ _ _ _ _ H
#align le_cinfi le_cinfi

/-- The indexed infimum of a function is bounded above by the value taken at one point-/
theorem cinfi_le {f : ι → α} (H : BddBelow (range f)) (c : ι) : infi f ≤ f c :=
  @le_csupr αᵒᵈ _ _ _ H c
#align cinfi_le cinfi_le

theorem cinfi_le_of_le {f : ι → α} (H : BddBelow (range f)) (c : ι) (h : f c ≤ a) : infi f ≤ a :=
  @le_csupr_of_le αᵒᵈ _ _ _ _ H c h
#align cinfi_le_of_le cinfi_le_of_le

theorem cinfi_set_le {f : β → α} {s : Set β} (H : BddBelow (f '' s)) {c : β} (hc : c ∈ s) :
    (⨅ i : s, f i) ≤ f c :=
  @le_csupr_set αᵒᵈ _ _ _ _ H _ hc
#align cinfi_set_le cinfi_set_le

@[simp]
theorem csupr_const [hι : Nonempty ι] {a : α} : (⨆ b : ι, a) = a := by
  rw [supᵢ, range_const, cSup_singleton]
#align csupr_const csupr_const

@[simp]
theorem cinfi_const [hι : Nonempty ι] {a : α} : (⨅ b : ι, a) = a :=
  @csupr_const αᵒᵈ _ _ _ _
#align cinfi_const cinfi_const

@[simp]
theorem supr_unique [Unique ι] {s : ι → α} : (⨆ i, s i) = s default := by
  have : ∀ i, s i = s default := fun i => congr_arg s (Unique.eq_default i)
  simp only [this, csupr_const]
#align supr_unique supr_unique

@[simp]
theorem infi_unique [Unique ι] {s : ι → α} : (⨅ i, s i) = s default :=
  @supr_unique αᵒᵈ _ _ _ _
#align infi_unique infi_unique

@[simp]
theorem csupr_pos {p : Prop} {f : p → α} (hp : p) : (⨆ h : p, f h) = f hp :=
  haveI := uniqueProp hp
  supr_unique
#align csupr_pos csupr_pos

@[simp]
theorem cinfi_pos {p : Prop} {f : p → α} (hp : p) : (⨅ h : p, f h) = f hp :=
  @csupr_pos αᵒᵈ _ _ _ hp
#align cinfi_pos cinfi_pos

/-- Introduction rule to prove that `b` is the supremum of `f`: it suffices to check that `b`
is larger than `f i` for all `i`, and that this is not the case of any `w<b`.
See `supr_eq_of_forall_le_of_forall_lt_exists_gt` for a version in complete lattices. -/
theorem csupr_eq_of_forall_le_of_forall_lt_exists_gt [Nonempty ι] {f : ι → α} (h₁ : ∀ i, f i ≤ b)
    (h₂ : ∀ w, w < b → ∃ i, w < f i) : (⨆ i : ι, f i) = b :=
  cSup_eq_of_forall_le_of_forall_lt_exists_gt (range_nonempty f) (forall_range_iff.mpr h₁)
    fun w hw => exists_range_iff.mpr <| h₂ w hw
#align csupr_eq_of_forall_le_of_forall_lt_exists_gt csupr_eq_of_forall_le_of_forall_lt_exists_gt

/-- Introduction rule to prove that `b` is the infimum of `f`: it suffices to check that `b`
is smaller than `f i` for all `i`, and that this is not the case of any `w>b`.
See `infi_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in complete lattices. -/
theorem cinfi_eq_of_forall_ge_of_forall_gt_exists_lt [Nonempty ι] {f : ι → α} (h₁ : ∀ i, b ≤ f i)
    (h₂ : ∀ w, b < w → ∃ i, f i < w) : (⨅ i : ι, f i) = b :=
  @csupr_eq_of_forall_le_of_forall_lt_exists_gt αᵒᵈ _ _ _ _ ‹_› ‹_› ‹_›
#align cinfi_eq_of_forall_ge_of_forall_gt_exists_lt cinfi_eq_of_forall_ge_of_forall_gt_exists_lt

/-- Nested intervals lemma: if `f` is a monotone sequence, `g` is an antitone sequence, and
`f n ≤ g n` for all `n`, then `⨆ n, f n` belongs to all the intervals `[f n, g n]`. -/
theorem Monotone.csupr_mem_Inter_Icc_of_antitone [SemilatticeSup β] {f g : β → α} (hf : Monotone f)
    (hg : Antitone g) (h : f ≤ g) : (⨆ n, f n) ∈ ⋂ n, Icc (f n) (g n) := by
  refine' mem_Inter.2 fun n => _
  haveI : Nonempty β := ⟨n⟩
  have : ∀ m, f m ≤ g n := fun m => hf.forall_le_of_antitone hg h m n
  exact ⟨le_csupr ⟨g <| n, forall_range_iff.2 this⟩ _, csupr_le this⟩
#align monotone.csupr_mem_Inter_Icc_of_antitone Monotone.csupr_mem_Inter_Icc_of_antitone

/-- Nested intervals lemma: if `[f n, g n]` is an antitone sequence of nonempty
closed intervals, then `⨆ n, f n` belongs to all the intervals `[f n, g n]`. -/
theorem csupr_mem_Inter_Icc_of_antitone_Icc [SemilatticeSup β] {f g : β → α}
    (h : Antitone fun n => Icc (f n) (g n)) (h' : ∀ n, f n ≤ g n) :
    (⨆ n, f n) ∈ ⋂ n, Icc (f n) (g n) :=
  Monotone.csupr_mem_Inter_Icc_of_antitone
    (fun m n hmn => ((Icc_subset_Icc_iff (h' n)).1 (h hmn)).1)
    (fun m n hmn => ((Icc_subset_Icc_iff (h' n)).1 (h hmn)).2) h'
#align csupr_mem_Inter_Icc_of_antitone_Icc csupr_mem_Inter_Icc_of_antitone_Icc

/-- Introduction rule to prove that b is the supremum of s: it suffices to check that
1) b is an upper bound
2) every other upper bound b' satisfies b ≤ b'.-/
theorem cSup_eq_of_is_forall_le_of_forall_le_imp_ge (hs : s.Nonempty) (h_is_ub : ∀ a ∈ s, a ≤ b)
    (h_b_le_ub : ∀ ub, (∀ a ∈ s, a ≤ ub) → b ≤ ub) : supₛ s = b :=
  (cSup_le hs h_is_ub).antisymm ((h_b_le_ub _) fun a => le_cSup ⟨b, h_is_ub⟩)
#align cSup_eq_of_is_forall_le_of_forall_le_imp_ge cSup_eq_of_is_forall_le_of_forall_le_imp_ge

end ConditionallyCompleteLattice

instance Pi.conditionallyCompleteLattice {ι : Type _} {α : ∀ i : ι, Type _}
    [∀ i, ConditionallyCompleteLattice (α i)] : ConditionallyCompleteLattice (∀ i, α i) :=
  { Pi.lattice, Pi.SupSet, Pi.InfSet with
    le_cSup := fun s f ⟨g, hg⟩ hf i =>
      le_cSup ⟨g i, Set.forall_range_iff.2 fun ⟨f', hf'⟩ => hg hf' i⟩ ⟨⟨f, hf⟩, rfl⟩
    cSup_le := fun s f hs hf i =>
      (cSup_le (by haveI := hs.to_subtype <;> apply range_nonempty)) fun b ⟨⟨g, hg⟩, hb⟩ =>
        hb ▸ hf hg i
    cInf_le := fun s f ⟨g, hg⟩ hf i =>
      cInf_le ⟨g i, Set.forall_range_iff.2 fun ⟨f', hf'⟩ => hg hf' i⟩ ⟨⟨f, hf⟩, rfl⟩
    le_cInf := fun s f hs hf i =>
      (le_cInf (by haveI := hs.to_subtype <;> apply range_nonempty)) fun b ⟨⟨g, hg⟩, hb⟩ =>
        hb ▸ hf hg i }
#align pi.conditionally_complete_lattice Pi.conditionallyCompleteLattice

section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder α] {s t : Set α} {a b : α}

/-- When b < Sup s, there is an element a in s with b < a, if s is nonempty and the order is
a linear order. -/
theorem exists_lt_of_lt_cSup (hs : s.Nonempty) (hb : b < supₛ s) : ∃ a ∈ s, b < a := by
  contrapose! hb
  exact cSup_le hs hb
#align exists_lt_of_lt_cSup exists_lt_of_lt_cSup

/-- Indexed version of the above lemma `exists_lt_of_lt_cSup`.
When `b < supr f`, there is an element `i` such that `b < f i`.
-/
theorem exists_lt_of_lt_csupr [Nonempty ι] {f : ι → α} (h : b < supᵢ f) : ∃ i, b < f i :=
  let ⟨_, ⟨i, rfl⟩, h⟩ := exists_lt_of_lt_cSup (range_nonempty f) h
  ⟨i, h⟩
#align exists_lt_of_lt_csupr exists_lt_of_lt_csupr

/-- When Inf s < b, there is an element a in s with a < b, if s is nonempty and the order is
a linear order.-/
theorem exists_lt_of_cInf_lt (hs : s.Nonempty) (hb : infₛ s < b) : ∃ a ∈ s, a < b :=
  @exists_lt_of_lt_cSup αᵒᵈ _ _ _ hs hb
#align exists_lt_of_cInf_lt exists_lt_of_cInf_lt

/-- Indexed version of the above lemma `exists_lt_of_cInf_lt`
When `infi f < a`, there is an element `i` such that `f i < a`.
-/
theorem exists_lt_of_cinfi_lt [Nonempty ι] {f : ι → α} (h : infi f < a) : ∃ i, f i < a :=
  @exists_lt_of_lt_csupr αᵒᵈ _ _ _ _ _ h
#align exists_lt_of_cinfi_lt exists_lt_of_cinfi_lt

open Function

variable [IsWellOrder α (· < ·)]

theorem Inf_eq_argmin_on (hs : s.Nonempty) :
    infₛ s = argminOn id (@IsWellFounded.wf α (· < ·) _) s hs :=
  IsLeast.cInf_eq ⟨argminOn_mem _ _ _ _, fun a ha => argminOn_le id _ _ ha⟩
#align Inf_eq_argmin_on Inf_eq_argmin_on

theorem is_least_Inf (hs : s.Nonempty) : IsLeast s (infₛ s) := by
  rw [Inf_eq_argmin_on hs]
  exact ⟨argmin_on_mem _ _ _ _, fun a ha => argmin_on_le id _ _ ha⟩
#align is_least_Inf is_least_Inf

theorem le_cInf_iff' (hs : s.Nonempty) : b ≤ infₛ s ↔ b ∈ lowerBounds s :=
  le_isGLB_iff (is_least_Inf hs).IsGlb
#align le_cInf_iff' le_cInf_iff'

theorem Inf_mem (hs : s.Nonempty) : infₛ s ∈ s :=
  (is_least_Inf hs).1
#align Inf_mem Inf_mem

theorem infi_mem [Nonempty ι] (f : ι → α) : infi f ∈ range f :=
  Inf_mem (range_nonempty f)
#align infi_mem infi_mem

theorem MonotoneOn.map_Inf {β : Type _} [ConditionallyCompleteLattice β] {f : α → β}
    (hf : MonotoneOn f s) (hs : s.Nonempty) : f (infₛ s) = infₛ (f '' s) :=
  (hf.map_is_least (is_least_Inf hs)).cInf_eq.symm
#align monotone_on.map_Inf MonotoneOn.map_Inf

theorem Monotone.map_Inf {β : Type _} [ConditionallyCompleteLattice β] {f : α → β} (hf : Monotone f)
    (hs : s.Nonempty) : f (infₛ s) = infₛ (f '' s) :=
  (hf.map_is_least (is_least_Inf hs)).cInf_eq.symm
#align monotone.map_Inf Monotone.map_Inf

end ConditionallyCompleteLinearOrder

/-!
### Lemmas about a conditionally complete linear order with bottom element

In this case we have `Sup ∅ = ⊥`, so we can drop some `nonempty`/`set.nonempty` assumptions.
-/


section ConditionallyCompleteLinearOrderBot

variable [ConditionallyCompleteLinearOrderBot α]

@[simp]
theorem cSup_empty : (supₛ ∅ : α) = ⊥ :=
  ConditionallyCompleteLinearOrderBot.cSup_empty
#align cSup_empty cSup_empty

@[simp]
theorem csupr_of_empty [IsEmpty ι] (f : ι → α) : (⨆ i, f i) = ⊥ := by
  rw [supᵢ_of_empty', cSup_empty]
#align csupr_of_empty csupr_of_empty

@[simp]
theorem csupr_false (f : False → α) : (⨆ i, f i) = ⊥ :=
  csupr_of_empty f
#align csupr_false csupr_false

@[simp]
theorem cInf_univ : infₛ (univ : Set α) = ⊥ :=
  isLeast_univ.cInf_eq
#align cInf_univ cInf_univ

theorem is_lub_cSup' {s : Set α} (hs : BddAbove s) : IsLUB s (supₛ s) := by
  rcases eq_empty_or_nonempty s with (rfl | hne)
  · simp only [cSup_empty, isLUB_empty]
  · exact is_lub_cSup hne hs
#align is_lub_cSup' is_lub_cSup'

theorem cSup_le_iff' {s : Set α} (hs : BddAbove s) {a : α} : supₛ s ≤ a ↔ ∀ x ∈ s, x ≤ a :=
  isLUB_le_iff (is_lub_cSup' hs)
#align cSup_le_iff' cSup_le_iff'

theorem cSup_le' {s : Set α} {a : α} (h : a ∈ upperBounds s) : supₛ s ≤ a :=
  (cSup_le_iff' ⟨a, h⟩).2 h
#align cSup_le' cSup_le'

theorem le_cSup_iff' {s : Set α} {a : α} (h : BddAbove s) :
    a ≤ supₛ s ↔ ∀ b, b ∈ upperBounds s → a ≤ b :=
  ⟨fun h b hb => le_trans h (cSup_le' hb), fun hb => hb _ fun x => le_cSup h⟩
#align le_cSup_iff' le_cSup_iff'

theorem le_csupr_iff' {s : ι → α} {a : α} (h : BddAbove (range s)) :
    a ≤ supᵢ s ↔ ∀ b, (∀ i, s i ≤ b) → a ≤ b := by simp [supᵢ, h, le_cSup_iff', upperBounds]
#align le_csupr_iff' le_csupr_iff'

theorem le_cInf_iff'' {s : Set α} {a : α} (ne : s.Nonempty) : a ≤ infₛ s ↔ ∀ b : α, b ∈ s → a ≤ b :=
  le_cInf_iff ⟨⊥, fun a _ => bot_le⟩ Ne
#align le_cInf_iff'' le_cInf_iff''

theorem le_cinfi_iff' [Nonempty ι] {f : ι → α} {a : α} : a ≤ infi f ↔ ∀ i, a ≤ f i :=
  le_cinfi_iff ⟨⊥, fun a _ => bot_le⟩
#align le_cinfi_iff' le_cinfi_iff'

theorem cInf_le' {s : Set α} {a : α} (h : a ∈ s) : infₛ s ≤ a :=
  cInf_le ⟨⊥, fun a _ => bot_le⟩ h
#align cInf_le' cInf_le'

theorem cinfi_le' (f : ι → α) (i : ι) : infi f ≤ f i :=
  cinfi_le ⟨⊥, fun a _ => bot_le⟩ _
#align cinfi_le' cinfi_le'

theorem exists_lt_of_lt_cSup' {s : Set α} {a : α} (h : a < supₛ s) : ∃ b ∈ s, a < b := by
  contrapose! h
  exact cSup_le' h
#align exists_lt_of_lt_cSup' exists_lt_of_lt_cSup'

theorem csupr_le_iff' {f : ι → α} (h : BddAbove (range f)) {a : α} :
    (⨆ i, f i) ≤ a ↔ ∀ i, f i ≤ a :=
  (cSup_le_iff' h).trans forall_range_iff
#align csupr_le_iff' csupr_le_iff'

theorem csupr_le' {f : ι → α} {a : α} (h : ∀ i, f i ≤ a) : (⨆ i, f i) ≤ a :=
  cSup_le' <| forall_range_iff.2 h
#align csupr_le' csupr_le'

theorem exists_lt_of_lt_csupr' {f : ι → α} {a : α} (h : a < ⨆ i, f i) : ∃ i, a < f i := by
  contrapose! h
  exact csupr_le' h
#align exists_lt_of_lt_csupr' exists_lt_of_lt_csupr'

theorem csupr_mono' {ι'} {f : ι → α} {g : ι' → α} (hg : BddAbove (range g))
    (h : ∀ i, ∃ i', f i ≤ g i') : supᵢ f ≤ supᵢ g :=
  csupr_le' fun i => Exists.elim (h i) (le_csupr_of_le hg)
#align csupr_mono' csupr_mono'

theorem cInf_le_cInf' {s t : Set α} (h₁ : t.Nonempty) (h₂ : t ⊆ s) : infₛ s ≤ infₛ t :=
  cInf_le_cInf (OrderBot.bddBelow s) h₁ h₂
#align cInf_le_cInf' cInf_le_cInf'

end ConditionallyCompleteLinearOrderBot

namespace WithTop

open Classical

variable [ConditionallyCompleteLinearOrderBot α]

/-- The Sup of a non-empty set is its least upper bound for a conditionally
complete lattice with a top. -/
theorem is_lub_Sup' {β : Type _} [ConditionallyCompleteLattice β] {s : Set (WithTop β)}
    (hs : s.Nonempty) : IsLUB s (supₛ s) := by
  constructor
  · show ite _ _ _ ∈ _
    split_ifs
    · intro _ _
      exact le_top
    · rintro (⟨⟩ | a) ha
      · contradiction
      apply some_le_some.2
      exact le_cSup h_1 ha
    · intro _ _
      exact le_top
  · show ite _ _ _ ∈ _
    split_ifs
    · rintro (⟨⟩ | a) ha
      · exact le_rfl
      · exact False.elim (not_top_le_coe a (ha h))
    · rintro (⟨⟩ | b) hb
      · exact le_top
      refine' some_le_some.2 (cSup_le _ _)
      · rcases hs with ⟨⟨⟩ | b, hb⟩
        · exact absurd hb h
        · exact ⟨b, hb⟩
      · intro a ha
        exact some_le_some.1 (hb ha)
    · rintro (⟨⟩ | b) hb
      · exact le_rfl
      · exfalso
        apply h_1
        use b
        intro a ha
        exact some_le_some.1 (hb ha)
#align with_top.is_lub_Sup' WithTop.is_lub_Sup'

theorem is_lub_Sup (s : Set (WithTop α)) : IsLUB s (supₛ s) := by
  cases' s.eq_empty_or_nonempty with hs hs
  · rw [hs]
    show IsLUB ∅ (ite _ _ _)
    split_ifs
    · cases h
    · rw [preimage_empty, cSup_empty]
      exact isLUB_empty
    · exfalso
      apply h_1
      use ⊥
      rintro a ⟨⟩
  exact is_lub_Sup' hs
#align with_top.is_lub_Sup WithTop.is_lub_Sup

/-- The Inf of a bounded-below set is its greatest lower bound for a conditionally
complete lattice with a top. -/
theorem is_glb_Inf' {β : Type _} [ConditionallyCompleteLattice β] {s : Set (WithTop β)}
    (hs : BddBelow s) : IsGLB s (infₛ s) := by
  constructor
  · show ite _ _ _ ∈ _
    split_ifs
    · intro a ha
      exact top_le_iff.2 (Set.mem_singleton_iff.1 (h ha))
    · rintro (⟨⟩ | a) ha
      · exact le_top
      refine' some_le_some.2 (cInf_le _ ha)
      rcases hs with ⟨⟨⟩ | b, hb⟩
      · exfalso
        apply h
        intro c hc
        rw [mem_singleton_iff, ← top_le_iff]
        exact hb hc
      use b
      intro c hc
      exact some_le_some.1 (hb hc)
  · show ite _ _ _ ∈ _
    split_ifs
    · intro _ _
      exact le_top
    · rintro (⟨⟩ | a) ha
      · exfalso
        apply h
        intro b hb
        exact Set.mem_singleton_iff.2 (top_le_iff.1 (ha hb))
      · refine' some_le_some.2 (le_cInf _ _)
        ·
          classical 
            contrapose! h
            rintro (⟨⟩ | a) ha
            · exact mem_singleton ⊤
            · exact (h ⟨a, ha⟩).elim
        · intro b hb
          rw [← some_le_some]
          exact ha hb
#align with_top.is_glb_Inf' WithTop.is_glb_Inf'

theorem is_glb_Inf (s : Set (WithTop α)) : IsGLB s (infₛ s) := by
  by_cases hs : BddBelow s
  · exact is_glb_Inf' hs
  · exfalso
    apply hs
    use ⊥
    intro _ _
    exact bot_le
#align with_top.is_glb_Inf WithTop.is_glb_Inf

noncomputable instance : CompleteLinearOrder (WithTop α) :=
  { WithTop.linearOrder, WithTop.lattice, WithTop.orderTop, WithTop.orderBot with
    sup := supₛ
    le_Sup := fun s => (is_lub_Sup s).1
    Sup_le := fun s => (is_lub_Sup s).2
    inf := infₛ
    le_Inf := fun s => (is_glb_Inf s).2
    Inf_le := fun s => (is_glb_Inf s).1 }

/-- A version of `with_top.coe_Sup'` with a more convenient but less general statement. -/
@[norm_cast]
theorem coe_Sup {s : Set α} (hb : BddAbove s) : ↑(supₛ s) = (⨆ a ∈ s, ↑a : WithTop α) := by
  rw [coe_Sup' hb, supₛ_image]
#align with_top.coe_Sup WithTop.coe_Sup

/-- A version of `with_top.coe_Inf'` with a more convenient but less general statement. -/
@[norm_cast]
theorem coe_Inf {s : Set α} (hs : s.Nonempty) : ↑(infₛ s) = (⨅ a ∈ s, ↑a : WithTop α) := by
  rw [coe_Inf' hs, infₛ_image]
#align with_top.coe_Inf WithTop.coe_Inf

end WithTop

namespace Monotone

variable [Preorder α] [ConditionallyCompleteLattice β] {f : α → β} (h_mono : Monotone f)

/-! A monotone function into a conditionally complete lattice preserves the ordering properties of
`Sup` and `Inf`. -/


theorem le_cSup_image {s : Set α} {c : α} (hcs : c ∈ s) (h_bdd : BddAbove s) :
    f c ≤ supₛ (f '' s) :=
  le_cSup (map_bddAbove h_mono h_bdd) (mem_image_of_mem f hcs)
#align monotone.le_cSup_image Monotone.le_cSup_image

theorem cSup_image_le {s : Set α} (hs : s.Nonempty) {B : α} (hB : B ∈ upperBounds s) :
    supₛ (f '' s) ≤ f B :=
  cSup_le (Nonempty.image f hs) (h_mono.mem_upper_bounds_image hB)
#align monotone.cSup_image_le Monotone.cSup_image_le

theorem cInf_image_le {s : Set α} {c : α} (hcs : c ∈ s) (h_bdd : BddBelow s) :
    infₛ (f '' s) ≤ f c :=
  @le_cSup_image αᵒᵈ βᵒᵈ _ _ _ (fun x y hxy => h_mono hxy) _ _ hcs h_bdd
#align monotone.cInf_image_le Monotone.cInf_image_le

theorem le_cInf_image {s : Set α} (hs : s.Nonempty) {B : α} (hB : B ∈ lowerBounds s) :
    f B ≤ infₛ (f '' s) :=
  @cSup_image_le αᵒᵈ βᵒᵈ _ _ _ (fun x y hxy => h_mono hxy) _ hs _ hB
#align monotone.le_cInf_image Monotone.le_cInf_image

end Monotone

namespace GaloisConnection

variable [ConditionallyCompleteLattice α] [ConditionallyCompleteLattice β] [Nonempty ι] {l : α → β}
  {u : β → α}

theorem l_cSup (gc : GaloisConnection l u) {s : Set α} (hne : s.Nonempty) (hbdd : BddAbove s) :
    l (supₛ s) = ⨆ x : s, l x :=
  Eq.symm <| IsLUB.csupr_set_eq (gc.is_lub_l_image <| is_lub_cSup hne hbdd) hne
#align galois_connection.l_cSup GaloisConnection.l_cSup

theorem l_cSup' (gc : GaloisConnection l u) {s : Set α} (hne : s.Nonempty) (hbdd : BddAbove s) :
    l (supₛ s) = supₛ (l '' s) := by rw [gc.l_cSup hne hbdd, supₛ_image']
#align galois_connection.l_cSup' GaloisConnection.l_cSup'

theorem l_csupr (gc : GaloisConnection l u) {f : ι → α} (hf : BddAbove (range f)) :
    l (⨆ i, f i) = ⨆ i, l (f i) := by rw [supᵢ, gc.l_cSup (range_nonempty _) hf, supᵢ_range']
#align galois_connection.l_csupr GaloisConnection.l_csupr

theorem l_csupr_set (gc : GaloisConnection l u) {s : Set γ} {f : γ → α} (hf : BddAbove (f '' s))
    (hne : s.Nonempty) : l (⨆ i : s, f i) = ⨆ i : s, l (f i) := by
  haveI := hne.to_subtype
  rw [image_eq_range] at hf
  exact gc.l_csupr hf
#align galois_connection.l_csupr_set GaloisConnection.l_csupr_set

theorem u_cInf (gc : GaloisConnection l u) {s : Set β} (hne : s.Nonempty) (hbdd : BddBelow s) :
    u (infₛ s) = ⨅ x : s, u x :=
  gc.dual.l_cSup hne hbdd
#align galois_connection.u_cInf GaloisConnection.u_cInf

theorem u_cInf' (gc : GaloisConnection l u) {s : Set β} (hne : s.Nonempty) (hbdd : BddBelow s) :
    u (infₛ s) = infₛ (u '' s) :=
  gc.dual.l_cSup' hne hbdd
#align galois_connection.u_cInf' GaloisConnection.u_cInf'

theorem u_cinfi (gc : GaloisConnection l u) {f : ι → β} (hf : BddBelow (range f)) :
    u (⨅ i, f i) = ⨅ i, u (f i) :=
  gc.dual.l_csupr hf
#align galois_connection.u_cinfi GaloisConnection.u_cinfi

theorem u_cinfi_set (gc : GaloisConnection l u) {s : Set γ} {f : γ → β} (hf : BddBelow (f '' s))
    (hne : s.Nonempty) : u (⨅ i : s, f i) = ⨅ i : s, u (f i) :=
  gc.dual.l_csupr_set hf hne
#align galois_connection.u_cinfi_set GaloisConnection.u_cinfi_set

end GaloisConnection

namespace OrderIso

variable [ConditionallyCompleteLattice α] [ConditionallyCompleteLattice β] [Nonempty ι]

theorem map_cSup (e : α ≃o β) {s : Set α} (hne : s.Nonempty) (hbdd : BddAbove s) :
    e (supₛ s) = ⨆ x : s, e x :=
  e.to_galois_connection.l_cSup hne hbdd
#align order_iso.map_cSup OrderIso.map_cSup

theorem map_cSup' (e : α ≃o β) {s : Set α} (hne : s.Nonempty) (hbdd : BddAbove s) :
    e (supₛ s) = supₛ (e '' s) :=
  e.to_galois_connection.l_cSup' hne hbdd
#align order_iso.map_cSup' OrderIso.map_cSup'

theorem map_csupr (e : α ≃o β) {f : ι → α} (hf : BddAbove (range f)) :
    e (⨆ i, f i) = ⨆ i, e (f i) :=
  e.to_galois_connection.l_csupr hf
#align order_iso.map_csupr OrderIso.map_csupr

theorem map_csupr_set (e : α ≃o β) {s : Set γ} {f : γ → α} (hf : BddAbove (f '' s))
    (hne : s.Nonempty) : e (⨆ i : s, f i) = ⨆ i : s, e (f i) :=
  e.to_galois_connection.l_csupr_set hf hne
#align order_iso.map_csupr_set OrderIso.map_csupr_set

theorem map_cInf (e : α ≃o β) {s : Set α} (hne : s.Nonempty) (hbdd : BddBelow s) :
    e (infₛ s) = ⨅ x : s, e x :=
  e.dual.map_cSup hne hbdd
#align order_iso.map_cInf OrderIso.map_cInf

theorem map_cInf' (e : α ≃o β) {s : Set α} (hne : s.Nonempty) (hbdd : BddBelow s) :
    e (infₛ s) = infₛ (e '' s) :=
  e.dual.map_cSup' hne hbdd
#align order_iso.map_cInf' OrderIso.map_cInf'

theorem map_cinfi (e : α ≃o β) {f : ι → α} (hf : BddBelow (range f)) :
    e (⨅ i, f i) = ⨅ i, e (f i) :=
  e.dual.map_csupr hf
#align order_iso.map_cinfi OrderIso.map_cinfi

theorem map_cinfi_set (e : α ≃o β) {s : Set γ} {f : γ → α} (hf : BddBelow (f '' s))
    (hne : s.Nonempty) : e (⨅ i : s, f i) = ⨅ i : s, e (f i) :=
  e.dual.map_csupr_set hf hne
#align order_iso.map_cinfi_set OrderIso.map_cinfi_set

end OrderIso

/-!
### Supremum/infimum of `set.image2`

A collection of lemmas showing what happens to the suprema/infima of `s` and `t` when mapped under
a binary function whose partial evaluations are lower/upper adjoints of Galois connections.
-/


section

variable [ConditionallyCompleteLattice α] [ConditionallyCompleteLattice β]
  [ConditionallyCompleteLattice γ] {f : α → β → γ} {s : Set α} {t : Set β}

variable {l u : α → β → γ} {l₁ u₁ : β → γ → α} {l₂ u₂ : α → γ → β}

theorem cSup_image2_eq_cSup_cSup (h₁ : ∀ b, GaloisConnection (swap l b) (u₁ b))
    (h₂ : ∀ a, GaloisConnection (l a) (u₂ a)) (hs₀ : s.Nonempty) (hs₁ : BddAbove s)
    (ht₀ : t.Nonempty) (ht₁ : BddAbove t) : supₛ (image2 l s t) = l (supₛ s) (supₛ t) := by
  refine' eq_of_forall_ge_iff fun c => _
  rw [cSup_le_iff (hs₁.image2 (fun _ => (h₁ _).monotone_l) (fun _ => (h₂ _).monotone_l) ht₁)
      (hs₀.image2 ht₀),
    forall_image2_iff, forall₂_swap, (h₂ _).le_iff_le, cSup_le_iff ht₁ ht₀]
  simp_rw [← (h₂ _).le_iff_le, (h₁ _).le_iff_le, cSup_le_iff hs₁ hs₀]
#align cSup_image2_eq_cSup_cSup cSup_image2_eq_cSup_cSup

theorem cSup_image2_eq_cSup_cInf (h₁ : ∀ b, GaloisConnection (swap l b) (u₁ b))
    (h₂ : ∀ a, GaloisConnection (l a ∘ of_dual) (to_dual ∘ u₂ a)) :
    s.Nonempty → BddAbove s → t.Nonempty → BddBelow t → supₛ (image2 l s t) = l (supₛ s) (infₛ t) :=
  @cSup_image2_eq_cSup_cSup _ βᵒᵈ _ _ _ _ _ _ _ _ _ h₁ h₂
#align cSup_image2_eq_cSup_cInf cSup_image2_eq_cSup_cInf

theorem cSup_image2_eq_cInf_cSup (h₁ : ∀ b, GaloisConnection (swap l b ∘ of_dual) (to_dual ∘ u₁ b))
    (h₂ : ∀ a, GaloisConnection (l a) (u₂ a)) :
    s.Nonempty → BddBelow s → t.Nonempty → BddAbove t → supₛ (image2 l s t) = l (infₛ s) (supₛ t) :=
  @cSup_image2_eq_cSup_cSup αᵒᵈ _ _ _ _ _ _ _ _ _ _ h₁ h₂
#align cSup_image2_eq_cInf_cSup cSup_image2_eq_cInf_cSup

theorem cSup_image2_eq_cInf_cInf (h₁ : ∀ b, GaloisConnection (swap l b ∘ of_dual) (to_dual ∘ u₁ b))
    (h₂ : ∀ a, GaloisConnection (l a ∘ of_dual) (to_dual ∘ u₂ a)) :
    s.Nonempty → BddBelow s → t.Nonempty → BddBelow t → supₛ (image2 l s t) = l (infₛ s) (infₛ t) :=
  @cSup_image2_eq_cSup_cSup αᵒᵈ βᵒᵈ _ _ _ _ _ _ _ _ _ h₁ h₂
#align cSup_image2_eq_cInf_cInf cSup_image2_eq_cInf_cInf

theorem cInf_image2_eq_cInf_cInf (h₁ : ∀ b, GaloisConnection (l₁ b) (swap u b))
    (h₂ : ∀ a, GaloisConnection (l₂ a) (u a)) :
    s.Nonempty → BddBelow s → t.Nonempty → BddBelow t → infₛ (image2 u s t) = u (infₛ s) (infₛ t) :=
  @cSup_image2_eq_cSup_cSup αᵒᵈ βᵒᵈ γᵒᵈ _ _ _ _ _ _ l₁ l₂ (fun _ => (h₁ _).dual) fun _ =>
    (h₂ _).dual
#align cInf_image2_eq_cInf_cInf cInf_image2_eq_cInf_cInf

theorem cInf_image2_eq_cInf_cSup (h₁ : ∀ b, GaloisConnection (l₁ b) (swap u b))
    (h₂ : ∀ a, GaloisConnection (to_dual ∘ l₂ a) (u a ∘ of_dual)) :
    s.Nonempty → BddBelow s → t.Nonempty → BddAbove t → infₛ (image2 u s t) = u (infₛ s) (supₛ t) :=
  @cInf_image2_eq_cInf_cInf _ βᵒᵈ _ _ _ _ _ _ _ _ _ h₁ h₂
#align cInf_image2_eq_cInf_cSup cInf_image2_eq_cInf_cSup

theorem cInf_image2_eq_cSup_cInf (h₁ : ∀ b, GaloisConnection (to_dual ∘ l₁ b) (swap u b ∘ of_dual))
    (h₂ : ∀ a, GaloisConnection (l₂ a) (u a)) :
    s.Nonempty → BddAbove s → t.Nonempty → BddBelow t → infₛ (image2 u s t) = u (supₛ s) (infₛ t) :=
  @cInf_image2_eq_cInf_cInf αᵒᵈ _ _ _ _ _ _ _ _ _ _ h₁ h₂
#align cInf_image2_eq_cSup_cInf cInf_image2_eq_cSup_cInf

theorem cInf_image2_eq_cSup_cSup (h₁ : ∀ b, GaloisConnection (to_dual ∘ l₁ b) (swap u b ∘ of_dual))
    (h₂ : ∀ a, GaloisConnection (to_dual ∘ l₂ a) (u a ∘ of_dual)) :
    s.Nonempty → BddAbove s → t.Nonempty → BddAbove t → infₛ (image2 u s t) = u (supₛ s) (supₛ t) :=
  @cInf_image2_eq_cInf_cInf αᵒᵈ βᵒᵈ _ _ _ _ _ _ _ _ _ h₁ h₂
#align cInf_image2_eq_cSup_cSup cInf_image2_eq_cSup_cSup

end

section WithTopBot

/-!
### Complete lattice structure on `with_top (with_bot α)`

If `α` is a `conditionally_complete_lattice`, then we show that `with_top α` and `with_bot α`
also inherit the structure of conditionally complete lattices. Furthermore, we show
that `with_top (with_bot α)` and `with_bot (with_top α)` naturally inherit the structure of a
complete lattice. Note that for `α` a conditionally complete lattice, `Sup` and `Inf` both return
junk values for sets which are empty or unbounded. The extension of `Sup` to `with_top α` fixes
the unboundedness problem and the extension to `with_bot α` fixes the problem with
the empty set.

This result can be used to show that the extended reals `[-∞, ∞]` are a complete linear order.
-/


open Classical

/-- Adding a top element to a conditionally complete lattice
gives a conditionally complete lattice -/
noncomputable instance WithTop.conditionallyCompleteLattice {α : Type _}
    [ConditionallyCompleteLattice α] : ConditionallyCompleteLattice (WithTop α) :=
  { WithTop.lattice, WithTop.hasSup, WithTop.hasInf with
    le_cSup := fun S a hS haS => (WithTop.is_lub_Sup' ⟨a, haS⟩).1 haS
    cSup_le := fun S a hS haS => (WithTop.is_lub_Sup' hS).2 haS
    cInf_le := fun S a hS haS => (WithTop.is_glb_Inf' hS).1 haS
    le_cInf := fun S a hS haS => (WithTop.is_glb_Inf' ⟨a, haS⟩).2 haS }
#align with_top.conditionally_complete_lattice WithTop.conditionallyCompleteLattice

/-- Adding a bottom element to a conditionally complete lattice
gives a conditionally complete lattice -/
noncomputable instance WithBot.conditionallyCompleteLattice {α : Type _}
    [ConditionallyCompleteLattice α] : ConditionallyCompleteLattice (WithBot α) :=
  { WithBot.lattice, WithBot.hasSup, WithBot.hasInf with
    le_cSup := (@WithTop.conditionallyCompleteLattice αᵒᵈ _).cInf_le
    cSup_le := (@WithTop.conditionallyCompleteLattice αᵒᵈ _).le_cInf
    cInf_le := (@WithTop.conditionallyCompleteLattice αᵒᵈ _).le_cSup
    le_cInf := (@WithTop.conditionallyCompleteLattice αᵒᵈ _).cSup_le }
#align with_bot.conditionally_complete_lattice WithBot.conditionallyCompleteLattice

noncomputable instance WithTop.WithBot.completeLattice {α : Type _}
    [ConditionallyCompleteLattice α] : CompleteLattice (WithTop (WithBot α)) :=
  { WithTop.hasInf, WithTop.hasSup, WithTop.boundedOrder, WithTop.lattice with
    le_Sup := fun S a haS => (WithTop.is_lub_Sup' ⟨a, haS⟩).1 haS
    Sup_le := fun S a ha => by 
      cases' S.eq_empty_or_nonempty with h
      · show ite _ _ _ ≤ a
        split_ifs
        · rw [h] at h_1
          cases h_1
        · convert bot_le
          convert WithBot.cSup_empty
          rw [h]
          rfl
        · exfalso
          apply h_2
          use ⊥
          rw [h]
          rintro b ⟨⟩
      · refine' (WithTop.is_lub_Sup' h).2 ha
    Inf_le := fun S a haS =>
      show ite _ _ _ ≤ a by 
        split_ifs
        · cases' a with a
          exact le_rfl
          cases h haS <;> tauto
        · cases a
          · exact le_top
          · apply WithTop.some_le_some.2
            refine' cInf_le _ haS
            use ⊥
            intro b hb
            exact bot_le
    le_Inf := fun S a haS => (WithTop.is_glb_Inf' ⟨a, haS⟩).2 haS }
#align with_top.with_bot.complete_lattice WithTop.WithBot.completeLattice

noncomputable instance WithTop.WithBot.completeLinearOrder {α : Type _}
    [ConditionallyCompleteLinearOrder α] : CompleteLinearOrder (WithTop (WithBot α)) :=
  { WithTop.WithBot.completeLattice, WithTop.linearOrder with }
#align with_top.with_bot.complete_linear_order WithTop.WithBot.completeLinearOrder

noncomputable instance WithBot.WithTop.completeLattice {α : Type _}
    [ConditionallyCompleteLattice α] : CompleteLattice (WithBot (WithTop α)) :=
  { WithBot.hasInf, WithBot.hasSup, WithBot.boundedOrder, WithBot.lattice with
    le_Sup := (@WithTop.WithBot.completeLattice αᵒᵈ _).Inf_le
    Sup_le := (@WithTop.WithBot.completeLattice αᵒᵈ _).le_Inf
    Inf_le := (@WithTop.WithBot.completeLattice αᵒᵈ _).le_Sup
    le_Inf := (@WithTop.WithBot.completeLattice αᵒᵈ _).Sup_le }
#align with_bot.with_top.complete_lattice WithBot.WithTop.completeLattice

noncomputable instance WithBot.WithTop.completeLinearOrder {α : Type _}
    [ConditionallyCompleteLinearOrder α] : CompleteLinearOrder (WithBot (WithTop α)) :=
  { WithBot.WithTop.completeLattice, WithBot.linearOrder with }
#align with_bot.with_top.complete_linear_order WithBot.WithTop.completeLinearOrder

theorem WithTop.supr_coe_eq_top {ι : Sort _} {α : Type _} [ConditionallyCompleteLinearOrderBot α]
    (f : ι → α) : (⨆ x, (f x : WithTop α)) = ⊤ ↔ ¬BddAbove (Set.range f) := by
  rw [supᵢ_eq_top, not_bddAbove_iff]
  refine' ⟨fun hf r => _, fun hf a ha => _⟩
  · rcases hf r (WithTop.coe_lt_top r) with ⟨i, hi⟩
    exact ⟨f i, ⟨i, rfl⟩, with_top.coe_lt_coe.mp hi⟩
  · rcases hf (a.untop ha.ne) with ⟨-, ⟨i, rfl⟩, hi⟩
    exact ⟨i, by simpa only [WithTop.coe_untop _ ha.ne] using with_top.coe_lt_coe.mpr hi⟩
#align with_top.supr_coe_eq_top WithTop.supr_coe_eq_top

theorem WithTop.supr_coe_lt_top {ι : Sort _} {α : Type _} [ConditionallyCompleteLinearOrderBot α]
    (f : ι → α) : (⨆ x, (f x : WithTop α)) < ⊤ ↔ BddAbove (Set.range f) :=
  lt_top_iff_ne_top.trans <| (WithTop.supr_coe_eq_top f).Not.trans not_not
#align with_top.supr_coe_lt_top WithTop.supr_coe_lt_top

end WithTopBot

-- Guard against import creep
assert_not_exists multiset

