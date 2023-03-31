/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module order.conditionally_complete_lattice.basic
! leanprover-community/mathlib commit 207cfac9fcd06138865b5d04f7091e46d9320432
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.WellFounded
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Data.Set.Lattice

/-!
# Theory of conditionally complete lattices.

A conditionally complete lattice is a lattice in which every non-empty bounded subset `s`
has a least upper bound and a greatest lower bound, denoted below by `supₛ s` and `infₛ s`.
Typical examples are `ℝ`, `ℕ`, and `ℤ` with their usual orders.

The theory is very comparable to the theory of complete lattices, except that suitable
boundedness and nonemptiness assumptions have to be added to most statements.
We introduce two predicates `BddAbove` and `BddBelow` to express this boundedness, prove
their basic properties, and then go on to prove most useful properties of `supₛ` and `infₛ`
in conditionally complete lattices.

To differentiate the statements between complete lattices and conditionally complete
lattices, we prefix `infₛ` and `supₛ` in the statements by `c`, giving `cinfₛ` and `csupₛ`.
For instance, `infₛ_le` is a statement in complete lattices ensuring `infₛ s ≤ x`,
while `cinfₛ_le` is the same statement in conditionally complete lattices
with an additional assumption that `s` is bounded below.
-/


open Function OrderDual Set

variable {α β γ : Type _} {ι : Sort _}

section

/-!
Extension of `supₛ` and `infₛ` from a preorder `α` to `WithTop α` and `WithBot α`
-/


open Classical

noncomputable instance {α : Type _} [Preorder α] [SupSet α] : SupSet (WithTop α) :=
  ⟨fun S =>
    if ⊤ ∈ S then ⊤ else if BddAbove ((fun (a : α) ↦ ↑a) ⁻¹' S : Set α) then
      ↑(supₛ ((fun (a : α) ↦ (a : WithTop α)) ⁻¹' S : Set α)) else ⊤⟩

noncomputable instance {α : Type _} [InfSet α] : InfSet (WithTop α) :=
  ⟨fun S => if S ⊆ {⊤} then ⊤ else ↑(infₛ ((fun (a : α) ↦ ↑a) ⁻¹' S : Set α))⟩

noncomputable instance {α : Type _} [SupSet α] : SupSet (WithBot α) :=
  ⟨(@instInfSetWithTop αᵒᵈ _).infₛ⟩

noncomputable instance {α : Type _} [Preorder α] [InfSet α] : InfSet (WithBot α) :=
  ⟨(@instSupSetWithTop αᵒᵈ _).supₛ⟩

@[simp]
theorem WithTop.infₛ_empty {α : Type _} [InfSet α] : infₛ (∅ : Set (WithTop α)) = ⊤ :=
  if_pos <| Set.empty_subset _
#align with_top.cInf_empty WithTop.infₛ_empty

@[simp]
theorem WithTop.infᵢ_empty {α : Type _} [IsEmpty ι] [InfSet α] (f : ι → WithTop α) :
    (⨅ i, f i) = ⊤ := by rw [infᵢ, range_eq_empty, WithTop.infₛ_empty]
#align with_top.cinfi_empty WithTop.infᵢ_empty

theorem WithTop.coe_infₛ' [InfSet α] {s : Set α} (hs : s.Nonempty) :
    ↑(infₛ s) = (infₛ ((fun (a : α) ↦ ↑a) '' s) : WithTop α) := by
  obtain ⟨x, hx⟩ := hs
  change _ = ite _ _ _
  split_ifs with h
  · cases h (mem_image_of_mem _ hx)
  · rw [preimage_image_eq]
    exact Option.some_injective _
#align with_top.coe_Inf' WithTop.coe_infₛ'

-- Porting note: the mathlib3 proof uses `range_comp` in the opposite direction and
-- does not need `rfl`.
@[norm_cast]
theorem WithTop.coe_infᵢ [Nonempty ι] [InfSet α] (f : ι → α) :
    ↑(⨅ i, f i) = (⨅ i, f i : WithTop α) := by
  rw [infᵢ, infᵢ, WithTop.coe_infₛ' (range_nonempty f), ← range_comp]; rfl
#align with_top.coe_infi WithTop.coe_infᵢ

theorem WithTop.coe_supₛ' [Preorder α] [SupSet α] {s : Set α} (hs : BddAbove s) :
    ↑(supₛ s) = (supₛ ((fun (a : α) ↦ ↑a) '' s) : WithTop α) := by
  change _ = ite _ _ _
  rw [if_neg, preimage_image_eq, if_pos hs]
  · exact Option.some_injective _
  · rintro ⟨x, _, ⟨⟩⟩
#align with_top.coe_Sup' WithTop.coe_supₛ'

-- Porting note: the mathlib3 proof uses `range_comp` in the opposite direction and
-- does not need `rfl`.
@[norm_cast]
theorem WithTop.coe_supᵢ [Preorder α] [SupSet α] (f : ι → α) (h : BddAbove (Set.range f)) :
    ↑(⨆ i, f i) = (⨆ i, f i : WithTop α) := by
    rw [supᵢ, supᵢ, WithTop.coe_supₛ' h, ← range_comp]; rfl
#align with_top.coe_supr WithTop.coe_supᵢ

@[simp]
theorem WithBot.supₛ_empty {α : Type _} [SupSet α] : supₛ (∅ : Set (WithBot α)) = ⊥ :=
  if_pos <| Set.empty_subset _
#align with_bot.cSup_empty WithBot.supₛ_empty

@[simp]
theorem WithBot.supᵢ_empty {α : Type _} [IsEmpty ι] [SupSet α] (f : ι → WithBot α) :
    (⨆ i, f i) = ⊥ :=
  @WithTop.infᵢ_empty _ αᵒᵈ _ _ _
#align with_bot.csupr_empty WithBot.supᵢ_empty

@[norm_cast]
theorem WithBot.coe_supₛ' [SupSet α] {s : Set α} (hs : s.Nonempty) :
    ↑(supₛ s) = (supₛ ((fun (a : α) ↦ ↑a) '' s) : WithBot α) :=
  @WithTop.coe_infₛ' αᵒᵈ _ _ hs
#align with_bot.coe_Sup' WithBot.coe_supₛ'

@[norm_cast]
theorem WithBot.coe_supᵢ [Nonempty ι] [SupSet α] (f : ι → α) :
    ↑(⨆ i, f i) = (⨆ i, f i : WithBot α) :=
  @WithTop.coe_infᵢ αᵒᵈ _ _ _ _
#align with_bot.coe_supr WithBot.coe_supᵢ

@[norm_cast]
theorem WithBot.coe_infₛ' [Preorder α] [InfSet α] {s : Set α} (hs : BddBelow s) :
    ↑(infₛ s) = (infₛ ((fun (a : α) ↦ ↑a) '' s) : WithBot α) :=
  @WithTop.coe_supₛ' αᵒᵈ _ _ _ hs
#align with_bot.coe_Inf' WithBot.coe_infₛ'

@[norm_cast]
theorem WithBot.coe_infᵢ [Preorder α] [InfSet α] (f : ι → α) (h : BddBelow (Set.range f)) :
    ↑(⨅ i, f i) = (⨅ i, f i : WithBot α) :=
  @WithTop.coe_supᵢ αᵒᵈ _ _ _ _ h
#align with_bot.coe_infi WithBot.coe_infᵢ

end

/-- A conditionally complete lattice is a lattice in which
every nonempty subset which is bounded above has a supremum, and
every nonempty subset which is bounded below has an infimum.
Typical examples are real numbers or natural numbers.

To differentiate the statements from the corresponding statements in (unconditional)
complete lattices, we prefix infₛ and subₛ by a c everywhere. The same statements should
hold in both worlds, sometimes with additional assumptions of nonemptiness or
boundedness.-/
class ConditionallyCompleteLattice (α : Type _) extends Lattice α, SupSet α, InfSet α where
  /-- `a ≤ supₛ s` for all `a ∈ s`. -/
  le_csupₛ : ∀ s a, BddAbove s → a ∈ s → a ≤ supₛ s
  /-- `supₛ s ≤ a` for all `a ∈ upperBounds s`. -/
  csupₛ_le : ∀ s a, Set.Nonempty s → a ∈ upperBounds s → supₛ s ≤ a
  /-- `infₛ s ≤ a` for all `a ∈ s`. -/
  cinfₛ_le : ∀ s a, BddBelow s → a ∈ s → infₛ s ≤ a
  /-- `a ≤ infₛ s` for all `a ∈ lowerBounds s`. -/
  le_cinfₛ : ∀ s a, Set.Nonempty s → a ∈ lowerBounds s → a ≤ infₛ s
#align conditionally_complete_lattice ConditionallyCompleteLattice

-- Porting note: mathlib3 used `renaming`
/-- A conditionally complete linear order is a linear order in which
every nonempty subset which is bounded above has a supremum, and
every nonempty subset which is bounded below has an infimum.
Typical examples are real numbers or natural numbers.

To differentiate the statements from the corresponding statements in (unconditional)
complete linear orders, we prefix infₛ and supₛ by a c everywhere. The same statements should
hold in both worlds, sometimes with additional assumptions of nonemptiness or
boundedness.-/
class ConditionallyCompleteLinearOrder (α : Type _) extends ConditionallyCompleteLattice α where
  /-- A `ConditionallyCompleteLinearOrder` is total. -/
  le_total (a b : α) : a ≤ b ∨ b ≤ a
  /-- In a `ConditionallyCompleteLinearOrder`, we assume the order relations are all decidable. -/
  decidable_le : DecidableRel (. ≤ . : α → α → Prop)
  /-- In a `ConditionallyCompleteLinearOrder`, we assume the order relations are all decidable. -/
  decidable_eq : DecidableEq α := @decidableEq_of_decidableLE _ _ decidable_le
  /-- In a `ConditionallyCompleteLinearOrder`, we assume the order relations are all decidable. -/
  decidable_lt : DecidableRel (. < . : α → α → Prop) :=
    @decidableLT_of_decidableLE _ _ decidable_le
#align conditionally_complete_linear_order ConditionallyCompleteLinearOrder

instance (α : Type _) [ConditionallyCompleteLinearOrder α] : LinearOrder α :=
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
complete linear orders, we prefix `infₛ` and `supₛ` by a c everywhere. The same statements should
hold in both worlds, sometimes with additional assumptions of nonemptiness or
boundedness.-/
class ConditionallyCompleteLinearOrderBot (α : Type _) extends ConditionallyCompleteLinearOrder α,
  Bot α where
  /-- `⊥` is the least element -/
  bot_le : ∀ x : α, ⊥ ≤ x
  /-- The supremum of the empty set is `⊥` -/
  csupₛ_empty : supₛ ∅ = ⊥
#align conditionally_complete_linear_order_bot ConditionallyCompleteLinearOrderBot

-- see Note [lower instance priority]
instance (priority := 100) ConditionallyCompleteLinearOrderBot.toOrderBot
    [h : ConditionallyCompleteLinearOrderBot α] : OrderBot α :=
  { h with }
#align conditionally_complete_linear_order_bot.to_order_bot ConditionallyCompleteLinearOrderBot.toOrderBot

-- see Note [lower instance priority]
/-- A complete lattice is a conditionally complete lattice, as there are no restrictions
on the properties of infₛ and supₛ in a complete lattice.-/
instance (priority := 100) CompleteLattice.toConditionallyCompleteLattice [CompleteLattice α] :
    ConditionallyCompleteLattice α :=
  { ‹CompleteLattice α› with
    le_csupₛ := by intros; apply le_supₛ; assumption
    csupₛ_le := by intros; apply supₛ_le; assumption
    cinfₛ_le := by intros; apply infₛ_le; assumption
    le_cinfₛ := by intros; apply le_infₛ; assumption }
#align complete_lattice.to_conditionally_complete_lattice CompleteLattice.toConditionallyCompleteLattice

-- see Note [lower instance priority]
instance (priority := 100) CompleteLinearOrder.toConditionallyCompleteLinearOrderBot {α : Type _}
    [h : CompleteLinearOrder α] : ConditionallyCompleteLinearOrderBot α :=
  { CompleteLattice.toConditionallyCompleteLattice, h with csupₛ_empty := supₛ_empty }
#align complete_linear_order.to_conditionally_complete_linear_order_bot CompleteLinearOrder.toConditionallyCompleteLinearOrderBot

section

open Classical

/-- A well founded linear order is conditionally complete, with a bottom element. -/
@[reducible]
noncomputable def IsWellOrder.conditionallyCompleteLinearOrderBot (α : Type _)
  [i₁ : _root_.LinearOrder α] [i₂ : OrderBot α] [h : IsWellOrder α (· < ·)] :
    ConditionallyCompleteLinearOrderBot α :=
  { i₁, i₂, LinearOrder.toLattice with
    infₛ := fun s => if hs : s.Nonempty then h.wf.min s hs else ⊥
    cinfₛ_le := fun s a _ has => by
      have s_ne : s.Nonempty := ⟨a, has⟩
      simpa [s_ne] using not_lt.1 (h.wf.not_lt_min s s_ne has)
    le_cinfₛ := fun s a hs has => by
      simp only [hs, dif_pos]
      exact has (h.wf.min_mem s hs)
    supₛ := fun s => if hs : (upperBounds s).Nonempty then h.wf.min _ hs else ⊥
    le_csupₛ := fun s a hs has => by
      have h's : (upperBounds s).Nonempty := hs
      simp only [h's, dif_pos]
      exact h.wf.min_mem _ h's has
    csupₛ_le := fun s a _ has => by
      have h's : (upperBounds s).Nonempty := ⟨a, has⟩
      simp only [h's, dif_pos]
      simpa using h.wf.not_lt_min _ h's has
    csupₛ_empty := by simpa using eq_bot_iff.2 (not_lt.1 <| h.wf.not_lt_min _ _ <| mem_univ ⊥) }
#align is_well_order.conditionally_complete_linear_order_bot IsWellOrder.conditionallyCompleteLinearOrderBot

end

section OrderDual

instance (α : Type _) [ConditionallyCompleteLattice α] : ConditionallyCompleteLattice αᵒᵈ :=
  { instInfOrderDual α, instSupOrderDual α, OrderDual.lattice α with
    le_csupₛ := @ConditionallyCompleteLattice.cinfₛ_le α _
    csupₛ_le := @ConditionallyCompleteLattice.le_cinfₛ α _
    le_cinfₛ := @ConditionallyCompleteLattice.csupₛ_le α _
    cinfₛ_le := @ConditionallyCompleteLattice.le_csupₛ α _ }

instance (α : Type _) [ConditionallyCompleteLinearOrder α] : ConditionallyCompleteLinearOrder αᵒᵈ :=
  { instConditionallyCompleteLatticeOrderDual α, OrderDual.linearOrder α with }

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
  -- don't care to fix sup, infₛ
  ..conditionallyCompleteLatticeOfSupₛ my_T _ }
```
-/
def conditionallyCompleteLatticeOfSupₛ (α : Type _) [H1 : PartialOrder α] [H2 : SupSet α]
    (bddAbove_pair : ∀ a b : α, BddAbove ({a, b} : Set α))
    (bddBelow_pair : ∀ a b : α, BddBelow ({a, b} : Set α))
    (isLUB_supₛ : ∀ s : Set α, BddAbove s → s.Nonempty → IsLUB s (supₛ s)) :
    ConditionallyCompleteLattice α :=
  { H1, H2 with
    sup := fun a b => supₛ {a, b}
    le_sup_left := fun a b =>
      (isLUB_supₛ {a, b} (bddAbove_pair a b) (insert_nonempty _ _)).1 (mem_insert _ _)
    le_sup_right := fun a b =>
      (isLUB_supₛ {a, b} (bddAbove_pair a b) (insert_nonempty _ _)).1
        (mem_insert_of_mem _ (mem_singleton _))
    sup_le := fun a b _ hac hbc =>
      (isLUB_supₛ {a, b} (bddAbove_pair a b) (insert_nonempty _ _)).2
        (forall_insert_of_forall (forall_eq.mpr hbc) hac)
    inf := fun a b => supₛ (lowerBounds {a, b})
    inf_le_left := fun a b =>
      (isLUB_supₛ (lowerBounds {a, b}) (Nonempty.bddAbove_lowerBounds ⟨a, mem_insert _ _⟩)
            (bddBelow_pair a b)).2
        fun _ hc => hc <| mem_insert _ _
    inf_le_right := fun a b =>
      (isLUB_supₛ (lowerBounds {a, b}) (Nonempty.bddAbove_lowerBounds ⟨a, mem_insert _ _⟩)
            (bddBelow_pair a b)).2
        fun _ hc => hc <| mem_insert_of_mem _ (mem_singleton _)
    le_inf := fun c a b hca hcb =>
      (isLUB_supₛ (lowerBounds {a, b}) (Nonempty.bddAbove_lowerBounds ⟨a, mem_insert _ _⟩)
            ⟨c, forall_insert_of_forall (forall_eq.mpr hcb) hca⟩).1
        (forall_insert_of_forall (forall_eq.mpr hcb) hca)
    infₛ := fun s => supₛ (lowerBounds s)
    csupₛ_le := fun s a hs ha => (isLUB_supₛ s ⟨a, ha⟩ hs).2 ha
    le_csupₛ := fun s a hs ha => (isLUB_supₛ s hs ⟨a, ha⟩).1 ha
    cinfₛ_le := fun s a hs ha =>
      (isLUB_supₛ (lowerBounds s) (Nonempty.bddAbove_lowerBounds ⟨a, ha⟩) hs).2 fun _ hb => hb ha
    le_cinfₛ := fun s a hs ha =>
      (isLUB_supₛ (lowerBounds s) hs.bddAbove_lowerBounds ⟨a, ha⟩).1 ha }
#align conditionally_complete_lattice_of_Sup conditionallyCompleteLatticeOfSupₛ

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
  -- don't care to fix sup, supₛ
  ..conditionallyCompleteLatticeOfInfₛ my_T _ }
```
-/
def conditionallyCompleteLatticeOfInfₛ (α : Type _) [H1 : PartialOrder α] [H2 : InfSet α]
    (bddAbove_pair : ∀ a b : α, BddAbove ({a, b} : Set α))
    (bddBelow_pair : ∀ a b : α, BddBelow ({a, b} : Set α))
    (isGLB_infₛ : ∀ s : Set α, BddBelow s → s.Nonempty → IsGLB s (infₛ s)) :
    ConditionallyCompleteLattice α :=
  { H1, H2 with
    inf := fun a b => infₛ {a, b}
    inf_le_left := fun a b =>
      (isGLB_infₛ {a, b} (bddBelow_pair a b) (insert_nonempty _ _)).1 (mem_insert _ _)
    inf_le_right := fun a b =>
      (isGLB_infₛ {a, b} (bddBelow_pair a b) (insert_nonempty _ _)).1
        (mem_insert_of_mem _ (mem_singleton _))
    le_inf := fun _ a b hca hcb =>
      (isGLB_infₛ {a, b} (bddBelow_pair a b) (insert_nonempty _ _)).2
        (forall_insert_of_forall (forall_eq.mpr hcb) hca)
    sup := fun a b => infₛ (upperBounds {a, b})
    le_sup_left := fun a b =>
      (isGLB_infₛ (upperBounds {a, b}) (Nonempty.bddBelow_upperBounds ⟨a, mem_insert _ _⟩)
            (bddAbove_pair a b)).2
        fun _ hc => hc <| mem_insert _ _
    le_sup_right := fun a b =>
      (isGLB_infₛ (upperBounds {a, b}) (Nonempty.bddBelow_upperBounds ⟨a, mem_insert _ _⟩)
            (bddAbove_pair a b)).2
        fun _ hc => hc <| mem_insert_of_mem _ (mem_singleton _)
    sup_le := fun a b c hac hbc =>
      (isGLB_infₛ (upperBounds {a, b}) (Nonempty.bddBelow_upperBounds ⟨a, mem_insert _ _⟩)
            ⟨c, forall_insert_of_forall (forall_eq.mpr hbc) hac⟩).1
        (forall_insert_of_forall (forall_eq.mpr hbc) hac)
    supₛ := fun s => infₛ (upperBounds s)
    le_cinfₛ := fun s a hs ha => (isGLB_infₛ s ⟨a, ha⟩ hs).2 ha
    cinfₛ_le := fun s a hs ha => (isGLB_infₛ s hs ⟨a, ha⟩).1 ha
    le_csupₛ := fun s a hs ha =>
      (isGLB_infₛ (upperBounds s) (Nonempty.bddBelow_upperBounds ⟨a, ha⟩) hs).2 fun _ hb => hb ha
    csupₛ_le := fun s a hs ha =>
      (isGLB_infₛ (upperBounds s) hs.bddBelow_upperBounds ⟨a, ha⟩).1 ha }
#align conditionally_complete_lattice_of_Inf conditionallyCompleteLatticeOfInfₛ

/-- A version of `conditionallyCompleteLatticeOfSupₛ` when we already know that `α` is a lattice.

This should only be used when it is both hard and unnecessary to provide `inf` explicitly. -/
def conditionallyCompleteLatticeOfLatticeOfSupₛ (α : Type _) [H1 : Lattice α] [SupSet α]
    (isLUB_supₛ : ∀ s : Set α, BddAbove s → s.Nonempty → IsLUB s (supₛ s)) :
    ConditionallyCompleteLattice α :=
  { H1,
    conditionallyCompleteLatticeOfSupₛ α
      (fun a b => ⟨a ⊔ b, forall_insert_of_forall (forall_eq.mpr le_sup_right) le_sup_left⟩)
      (fun a b => ⟨a ⊓ b, forall_insert_of_forall (forall_eq.mpr inf_le_right) inf_le_left⟩)
      isLUB_supₛ with }
#align conditionally_complete_lattice_of_lattice_of_Sup conditionallyCompleteLatticeOfLatticeOfSupₛ

/-- A version of `conditionallyCompleteLatticeOfInfₛ` when we already know that `α` is a lattice.

This should only be used when it is both hard and unnecessary to provide `sup` explicitly. -/
def conditionallyCompleteLatticeOfLatticeOfInfₛ (α : Type _) [H1 : Lattice α] [InfSet α]
    (isGLB_infₛ : ∀ s : Set α, BddBelow s → s.Nonempty → IsGLB s (infₛ s)) :
    ConditionallyCompleteLattice α :=
  { H1,
    conditionallyCompleteLatticeOfInfₛ α
      (fun a b => ⟨a ⊔ b, forall_insert_of_forall (forall_eq.mpr le_sup_right) le_sup_left⟩)
      (fun a b => ⟨a ⊓ b, forall_insert_of_forall (forall_eq.mpr inf_le_right) inf_le_left⟩)
      isGLB_infₛ with }
#align conditionally_complete_lattice_of_lattice_of_Inf conditionallyCompleteLatticeOfLatticeOfInfₛ

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice α] {s t : Set α} {a b : α}

theorem le_csupₛ (h₁ : BddAbove s) (h₂ : a ∈ s) : a ≤ supₛ s :=
  ConditionallyCompleteLattice.le_csupₛ s a h₁ h₂
#align le_cSup le_csupₛ

theorem csupₛ_le (h₁ : s.Nonempty) (h₂ : ∀ b ∈ s, b ≤ a) : supₛ s ≤ a :=
  ConditionallyCompleteLattice.csupₛ_le s a h₁ h₂
#align cSup_le csupₛ_le

theorem cinfₛ_le (h₁ : BddBelow s) (h₂ : a ∈ s) : infₛ s ≤ a :=
  ConditionallyCompleteLattice.cinfₛ_le s a h₁ h₂
#align cInf_le cinfₛ_le

theorem le_cinfₛ (h₁ : s.Nonempty) (h₂ : ∀ b ∈ s, a ≤ b) : a ≤ infₛ s :=
  ConditionallyCompleteLattice.le_cinfₛ s a h₁ h₂
#align le_cInf le_cinfₛ

theorem le_csupₛ_of_le (hs : BddAbove s) (hb : b ∈ s) (h : a ≤ b) : a ≤ supₛ s :=
  le_trans h (le_csupₛ hs hb)
#align le_cSup_of_le le_csupₛ_of_le

theorem cinfₛ_le_of_le (hs : BddBelow s) (hb : b ∈ s) (h : b ≤ a) : infₛ s ≤ a :=
  le_trans (cinfₛ_le hs hb) h
#align cInf_le_of_le cinfₛ_le_of_le

theorem csupₛ_le_csupₛ (ht : BddAbove t) (hs : s.Nonempty) (h : s ⊆ t) : supₛ s ≤ supₛ t :=
  csupₛ_le hs fun _ ha => le_csupₛ ht (h ha)
#align cSup_le_cSup csupₛ_le_csupₛ

theorem cinfₛ_le_cinfₛ (ht : BddBelow t) (hs : s.Nonempty) (h : s ⊆ t) : infₛ t ≤ infₛ s :=
  le_cinfₛ hs fun _ ha => cinfₛ_le ht (h ha)
#align cInf_le_cInf cinfₛ_le_cinfₛ

theorem le_csupₛ_iff (h : BddAbove s) (hs : s.Nonempty) :
    a ≤ supₛ s ↔ ∀ b, b ∈ upperBounds s → a ≤ b :=
  ⟨fun h _ hb => le_trans h (csupₛ_le hs hb), fun hb => hb _ fun _ => le_csupₛ h⟩
#align le_cSup_iff le_csupₛ_iff

theorem cinfₛ_le_iff (h : BddBelow s) (hs : s.Nonempty) : infₛ s ≤ a ↔ ∀ b ∈ lowerBounds s, b ≤ a :=
  ⟨fun h _ hb => le_trans (le_cinfₛ hs hb) h, fun hb => hb _ fun _ => cinfₛ_le h⟩
#align cInf_le_iff cinfₛ_le_iff

theorem isLUB_csupₛ (ne : s.Nonempty) (H : BddAbove s) : IsLUB s (supₛ s) :=
  ⟨fun _ => le_csupₛ H, fun _ => csupₛ_le ne⟩
#align is_lub_cSup isLUB_csupₛ

theorem isLUB_csupᵢ [Nonempty ι] {f : ι → α} (H : BddAbove (range f)) :
    IsLUB (range f) (⨆ i, f i) :=
  isLUB_csupₛ (range_nonempty f) H
#align is_lub_csupr isLUB_csupᵢ

theorem isLUB_csupᵢ_set {f : β → α} {s : Set β} (H : BddAbove (f '' s)) (Hne : s.Nonempty) :
    IsLUB (f '' s) (⨆ i : s, f i) := by
  rw [← supₛ_image']
  exact isLUB_csupₛ (Hne.image _) H
#align is_lub_csupr_set isLUB_csupᵢ_set

theorem isGLB_cinfₛ (ne : s.Nonempty) (H : BddBelow s) : IsGLB s (infₛ s) :=
  ⟨fun _ => cinfₛ_le H, fun _ => le_cinfₛ ne⟩
#align is_glb_cInf isGLB_cinfₛ

theorem isGLB_cinfᵢ [Nonempty ι] {f : ι → α} (H : BddBelow (range f)) :
    IsGLB (range f) (⨅ i, f i) :=
  isGLB_cinfₛ (range_nonempty f) H
#align is_glb_cinfi isGLB_cinfᵢ

theorem isGLB_cinfᵢ_set {f : β → α} {s : Set β} (H : BddBelow (f '' s)) (Hne : s.Nonempty) :
    IsGLB (f '' s) (⨅ i : s, f i) :=
  @isLUB_csupᵢ_set αᵒᵈ _ _ _ _ H Hne
#align is_glb_cinfi_set isGLB_cinfᵢ_set

theorem csupᵢ_le_iff [Nonempty ι] {f : ι → α} {a : α} (hf : BddAbove (range f)) :
    supᵢ f ≤ a ↔ ∀ i, f i ≤ a :=
  (isLUB_le_iff <| isLUB_csupᵢ hf).trans forall_range_iff
#align csupr_le_iff csupᵢ_le_iff

theorem le_cinfᵢ_iff [Nonempty ι] {f : ι → α} {a : α} (hf : BddBelow (range f)) :
    a ≤ infᵢ f ↔ ∀ i, a ≤ f i :=
  (le_isGLB_iff <| isGLB_cinfᵢ hf).trans forall_range_iff
#align le_cinfi_iff le_cinfᵢ_iff

theorem csupᵢ_set_le_iff {ι : Type _} {s : Set ι} {f : ι → α} {a : α} (hs : s.Nonempty)
    (hf : BddAbove (f '' s)) : (⨆ i : s, f i) ≤ a ↔ ∀ i ∈ s, f i ≤ a :=
  (isLUB_le_iff <| isLUB_csupᵢ_set hf hs).trans ball_image_iff
#align csupr_set_le_iff csupᵢ_set_le_iff

theorem le_cinfᵢ_set_iff {ι : Type _} {s : Set ι} {f : ι → α} {a : α} (hs : s.Nonempty)
    (hf : BddBelow (f '' s)) : (a ≤ ⨅ i : s, f i) ↔ ∀ i ∈ s, a ≤ f i :=
  (le_isGLB_iff <| isGLB_cinfᵢ_set hf hs).trans ball_image_iff
#align le_cinfi_set_iff le_cinfᵢ_set_iff

theorem IsLUB.csupₛ_eq (H : IsLUB s a) (ne : s.Nonempty) : supₛ s = a :=
  (isLUB_csupₛ ne ⟨a, H.1⟩).unique H
#align is_lub.cSup_eq IsLUB.csupₛ_eq

theorem IsLUB.csupᵢ_eq [Nonempty ι] {f : ι → α} (H : IsLUB (range f) a) : (⨆ i, f i) = a :=
  H.csupₛ_eq (range_nonempty f)
#align is_lub.csupr_eq IsLUB.csupᵢ_eq

theorem IsLUB.csupᵢ_set_eq {s : Set β} {f : β → α} (H : IsLUB (f '' s) a) (Hne : s.Nonempty) :
    (⨆ i : s, f i) = a :=
  IsLUB.csupₛ_eq (image_eq_range f s ▸ H) (image_eq_range f s ▸ Hne.image f)
#align is_lub.csupr_set_eq IsLUB.csupᵢ_set_eq

/-- A greatest element of a set is the supremum of this set. -/
theorem IsGreatest.csupₛ_eq (H : IsGreatest s a) : supₛ s = a :=
  H.isLUB.csupₛ_eq H.nonempty
#align is_greatest.cSup_eq IsGreatest.csupₛ_eq

theorem IsGreatest.csupₛ_mem (H : IsGreatest s a) : supₛ s ∈ s :=
  H.csupₛ_eq.symm ▸ H.1
#align is_greatest.Sup_mem IsGreatest.csupₛ_mem

theorem IsGLB.cinfₛ_eq (H : IsGLB s a) (ne : s.Nonempty) : infₛ s = a :=
  (isGLB_cinfₛ ne ⟨a, H.1⟩).unique H
#align is_glb.cInf_eq IsGLB.cinfₛ_eq

theorem IsGLB.cinfᵢ_eq [Nonempty ι] {f : ι → α} (H : IsGLB (range f) a) : (⨅ i, f i) = a :=
  H.cinfₛ_eq (range_nonempty f)
#align is_glb.cinfi_eq IsGLB.cinfᵢ_eq

theorem IsGLB.cinfᵢ_set_eq {s : Set β} {f : β → α} (H : IsGLB (f '' s) a) (Hne : s.Nonempty) :
    (⨅ i : s, f i) = a :=
  IsGLB.cinfₛ_eq (image_eq_range f s ▸ H) (image_eq_range f s ▸ Hne.image f)
#align is_glb.cinfi_set_eq IsGLB.cinfᵢ_set_eq

/-- A least element of a set is the infimum of this set. -/
theorem IsLeast.cinfₛ_eq (H : IsLeast s a) : infₛ s = a :=
  H.isGLB.cinfₛ_eq H.nonempty
#align is_least.cInf_eq IsLeast.cinfₛ_eq

theorem IsLeast.cinfₛ_mem (H : IsLeast s a) : infₛ s ∈ s :=
  H.cinfₛ_eq.symm ▸ H.1
#align is_least.Inf_mem IsLeast.cinfₛ_mem

theorem subset_Icc_cinfₛ_csupₛ (hb : BddBelow s) (ha : BddAbove s) : s ⊆ Icc (infₛ s) (supₛ s) :=
  fun _ hx => ⟨cinfₛ_le hb hx, le_csupₛ ha hx⟩
#align subset_Icc_cInf_cSup subset_Icc_cinfₛ_csupₛ

theorem csupₛ_le_iff (hb : BddAbove s) (hs : s.Nonempty) : supₛ s ≤ a ↔ ∀ b ∈ s, b ≤ a :=
  isLUB_le_iff (isLUB_csupₛ hs hb)
#align cSup_le_iff csupₛ_le_iff

theorem le_cinfₛ_iff (hb : BddBelow s) (hs : s.Nonempty) : a ≤ infₛ s ↔ ∀ b ∈ s, a ≤ b :=
  le_isGLB_iff (isGLB_cinfₛ hs hb)
#align le_cInf_iff le_cinfₛ_iff

theorem csupₛ_lower_bounds_eq_cinfₛ {s : Set α} (h : BddBelow s) (hs : s.Nonempty) :
    supₛ (lowerBounds s) = infₛ s :=
  (isLUB_csupₛ h <| hs.mono fun _ hx _ hy => hy hx).unique (isGLB_cinfₛ hs h).isLUB
#align cSup_lower_bounds_eq_cInf csupₛ_lower_bounds_eq_cinfₛ

theorem cinfₛ_upper_bounds_eq_csupₛ {s : Set α} (h : BddAbove s) (hs : s.Nonempty) :
    infₛ (upperBounds s) = supₛ s :=
  (isGLB_cinfₛ h <| hs.mono fun _ hx _ hy => hy hx).unique (isLUB_csupₛ hs h).isGLB
#align cInf_upper_bounds_eq_cSup cinfₛ_upper_bounds_eq_csupₛ

theorem not_mem_of_lt_cinfₛ {x : α} {s : Set α} (h : x < infₛ s) (hs : BddBelow s) : x ∉ s :=
  fun hx => lt_irrefl _ (h.trans_le (cinfₛ_le hs hx))
#align not_mem_of_lt_cInf not_mem_of_lt_cinfₛ

theorem not_mem_of_csupₛ_lt {x : α} {s : Set α} (h : supₛ s < x) (hs : BddAbove s) : x ∉ s :=
  @not_mem_of_lt_cinfₛ αᵒᵈ _ x s h hs
#align not_mem_of_cSup_lt not_mem_of_csupₛ_lt

/-- Introduction rule to prove that `b` is the supremum of `s`: it suffices to check that `b`
is larger than all elements of `s`, and that this is not the case of any `w<b`.
See `supₛ_eq_of_forall_le_of_forall_lt_exists_gt` for a version in complete lattices. -/
theorem csupₛ_eq_of_forall_le_of_forall_lt_exists_gt (hs : s.Nonempty) (H : ∀ a ∈ s, a ≤ b)
    (H' : ∀ w, w < b → ∃ a ∈ s, w < a) : supₛ s = b :=
  (eq_of_le_of_not_lt (csupₛ_le hs H)) fun hb =>
    let ⟨_, ha, ha'⟩ := H' _ hb
    lt_irrefl _ <| ha'.trans_le <| le_csupₛ ⟨b, H⟩ ha
#align cSup_eq_of_forall_le_of_forall_lt_exists_gt csupₛ_eq_of_forall_le_of_forall_lt_exists_gt

/-- Introduction rule to prove that `b` is the infimum of `s`: it suffices to check that `b`
is smaller than all elements of `s`, and that this is not the case of any `w>b`.
See `infₛ_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in complete lattices. -/
theorem cinfₛ_eq_of_forall_ge_of_forall_gt_exists_lt :
    s.Nonempty → (∀ a ∈ s, b ≤ a) → (∀ w, b < w → ∃ a ∈ s, a < w) → infₛ s = b :=
  @csupₛ_eq_of_forall_le_of_forall_lt_exists_gt αᵒᵈ _ _ _
#align cInf_eq_of_forall_ge_of_forall_gt_exists_lt cinfₛ_eq_of_forall_ge_of_forall_gt_exists_lt

/-- `b < supₛ s` when there is an element `a` in `s` with `b < a`, when `s` is bounded above.
This is essentially an iff, except that the assumptions for the two implications are
slightly different (one needs boundedness above for one direction, nonemptiness and linear
order for the other one), so we formulate separately the two implications, contrary to
the `CompleteLattice` case.-/
theorem lt_csupₛ_of_lt (hs : BddAbove s) (ha : a ∈ s) (h : b < a) : b < supₛ s :=
  lt_of_lt_of_le h (le_csupₛ hs ha)
#align lt_cSup_of_lt lt_csupₛ_of_lt

/-- `infₛ s < b` when there is an element `a` in `s` with `a < b`, when `s` is bounded below.
This is essentially an iff, except that the assumptions for the two implications are
slightly different (one needs boundedness below for one direction, nonemptiness and linear
order for the other one), so we formulate separately the two implications, contrary to
the `CompleteLattice` case.-/
theorem cinfₛ_lt_of_lt : BddBelow s → a ∈ s → a < b → infₛ s < b :=
  @lt_csupₛ_of_lt αᵒᵈ _ _ _ _
#align cInf_lt_of_lt cinfₛ_lt_of_lt

/-- If all elements of a nonempty set `s` are less than or equal to all elements
of a nonempty set `t`, then there exists an element between these sets. -/
theorem exists_between_of_forall_le (sne : s.Nonempty) (tne : t.Nonempty)
    (hst : ∀ x ∈ s, ∀ y ∈ t, x ≤ y) : (upperBounds s ∩ lowerBounds t).Nonempty :=
  ⟨infₛ t, fun x hx => le_cinfₛ tne <| hst x hx, fun _ hy => cinfₛ_le (sne.mono hst) hy⟩
#align exists_between_of_forall_le exists_between_of_forall_le

/-- The supremum of a singleton is the element of the singleton-/
@[simp]
theorem csupₛ_singleton (a : α) : supₛ {a} = a :=
  isGreatest_singleton.csupₛ_eq
#align cSup_singleton csupₛ_singleton

/-- The infimum of a singleton is the element of the singleton-/
@[simp]
theorem cinfₛ_singleton (a : α) : infₛ {a} = a :=
  isLeast_singleton.cinfₛ_eq
#align cInf_singleton cinfₛ_singleton

@[simp]
theorem csupₛ_pair (a b : α) : supₛ {a, b} = a ⊔ b :=
  (@isLUB_pair _ _ a b).csupₛ_eq (insert_nonempty _ _)
#align cSup_pair csupₛ_pair

@[simp]
theorem cinfₛ_pair (a b : α) : infₛ {a, b} = a ⊓ b :=
  (@isGLB_pair _ _ a b).cinfₛ_eq (insert_nonempty _ _)
#align cInf_pair cinfₛ_pair

/-- If a set is bounded below and above, and nonempty, its infimum is less than or equal to
its supremum.-/
theorem cinfₛ_le_csupₛ (hb : BddBelow s) (ha : BddAbove s) (ne : s.Nonempty) : infₛ s ≤ supₛ s :=
  isGLB_le_isLUB (isGLB_cinfₛ ne hb) (isLUB_csupₛ ne ha) ne
#align cInf_le_cSup cinfₛ_le_csupₛ

/-- The `supₛ` of a union of two sets is the max of the suprema of each subset, under the
assumptions that all sets are bounded above and nonempty.-/
theorem csupₛ_union (hs : BddAbove s) (sne : s.Nonempty) (ht : BddAbove t) (tne : t.Nonempty) :
    supₛ (s ∪ t) = supₛ s ⊔ supₛ t :=
  ((isLUB_csupₛ sne hs).union (isLUB_csupₛ tne ht)).csupₛ_eq sne.inl
#align cSup_union csupₛ_union

/-- The `infₛ` of a union of two sets is the min of the infima of each subset, under the assumptions
that all sets are bounded below and nonempty.-/
theorem cinfₛ_union (hs : BddBelow s) (sne : s.Nonempty) (ht : BddBelow t) (tne : t.Nonempty) :
    infₛ (s ∪ t) = infₛ s ⊓ infₛ t :=
  @csupₛ_union αᵒᵈ _ _ _ hs sne ht tne
#align cInf_union cinfₛ_union

/-- The supremum of an intersection of two sets is bounded by the minimum of the suprema of each
set, if all sets are bounded above and nonempty.-/
theorem csupₛ_inter_le (hs : BddAbove s) (ht : BddAbove t) (hst : (s ∩ t).Nonempty) :
    supₛ (s ∩ t) ≤ supₛ s ⊓ supₛ t :=
  (csupₛ_le hst) fun _ hx => le_inf (le_csupₛ hs hx.1) (le_csupₛ ht hx.2)
#align cSup_inter_le csupₛ_inter_le

/-- The infimum of an intersection of two sets is bounded below by the maximum of the
infima of each set, if all sets are bounded below and nonempty.-/
theorem le_cinfₛ_inter :
    BddBelow s → BddBelow t → (s ∩ t).Nonempty → infₛ s ⊔ infₛ t ≤ infₛ (s ∩ t) :=
  @csupₛ_inter_le αᵒᵈ _ _ _
#align le_cInf_inter le_cinfₛ_inter

/-- The supremum of `insert a s` is the maximum of `a` and the supremum of `s`, if `s` is
nonempty and bounded above.-/
theorem csupₛ_insert (hs : BddAbove s) (sne : s.Nonempty) : supₛ (insert a s) = a ⊔ supₛ s :=
  ((isLUB_csupₛ sne hs).insert a).csupₛ_eq (insert_nonempty a s)
#align cSup_insert csupₛ_insert

/-- The infimum of `insert a s` is the minimum of `a` and the infimum of `s`, if `s` is
nonempty and bounded below.-/
theorem cinfₛ_insert (hs : BddBelow s) (sne : s.Nonempty) : infₛ (insert a s) = a ⊓ infₛ s :=
  @csupₛ_insert αᵒᵈ _ _ _ hs sne
#align cInf_insert cinfₛ_insert

@[simp]
theorem cinfₛ_Icc (h : a ≤ b) : infₛ (Icc a b) = a :=
  (isGLB_Icc h).cinfₛ_eq (nonempty_Icc.2 h)
#align cInf_Icc cinfₛ_Icc

@[simp]
theorem cinfₛ_Ici : infₛ (Ici a) = a :=
  isLeast_Ici.cinfₛ_eq
#align cInf_Ici cinfₛ_Ici

@[simp]
theorem cinfₛ_Ico (h : a < b) : infₛ (Ico a b) = a :=
  (isGLB_Ico h).cinfₛ_eq (nonempty_Ico.2 h)
#align cInf_Ico cinfₛ_Ico

@[simp]
theorem cinfₛ_Ioc [DenselyOrdered α] (h : a < b) : infₛ (Ioc a b) = a :=
  (isGLB_Ioc h).cinfₛ_eq (nonempty_Ioc.2 h)
#align cInf_Ioc cinfₛ_Ioc

@[simp]
theorem cinfₛ_Ioi [NoMaxOrder α] [DenselyOrdered α] : infₛ (Ioi a) = a :=
  cinfₛ_eq_of_forall_ge_of_forall_gt_exists_lt nonempty_Ioi (fun _ => le_of_lt) fun w hw => by
    simpa using exists_between hw
#align cInf_Ioi cinfₛ_Ioi

@[simp]
theorem cinfₛ_Ioo [DenselyOrdered α] (h : a < b) : infₛ (Ioo a b) = a :=
  (isGLB_Ioo h).cinfₛ_eq (nonempty_Ioo.2 h)
#align cInf_Ioo cinfₛ_Ioo

@[simp]
theorem csupₛ_Icc (h : a ≤ b) : supₛ (Icc a b) = b :=
  (isLUB_Icc h).csupₛ_eq (nonempty_Icc.2 h)
#align cSup_Icc csupₛ_Icc

@[simp]
theorem csupₛ_Ico [DenselyOrdered α] (h : a < b) : supₛ (Ico a b) = b :=
  (isLUB_Ico h).csupₛ_eq (nonempty_Ico.2 h)
#align cSup_Ico csupₛ_Ico

@[simp]
theorem csupₛ_Iic : supₛ (Iic a) = a :=
  isGreatest_Iic.csupₛ_eq
#align cSup_Iic csupₛ_Iic

@[simp]
theorem csupₛ_Iio [NoMinOrder α] [DenselyOrdered α] : supₛ (Iio a) = a :=
  csupₛ_eq_of_forall_le_of_forall_lt_exists_gt nonempty_Iio (fun _ => le_of_lt) fun w hw => by
    simpa [and_comm] using exists_between hw
#align cSup_Iio csupₛ_Iio

@[simp]
theorem csupₛ_Ioc (h : a < b) : supₛ (Ioc a b) = b :=
  (isLUB_Ioc h).csupₛ_eq (nonempty_Ioc.2 h)
#align cSup_Ioc csupₛ_Ioc

@[simp]
theorem csupₛ_Ioo [DenselyOrdered α] (h : a < b) : supₛ (Ioo a b) = b :=
  (isLUB_Ioo h).csupₛ_eq (nonempty_Ioo.2 h)
#align cSup_Ioo csupₛ_Ioo

/-- The indexed supremum of a function is bounded above by a uniform bound-/
theorem csupᵢ_le [Nonempty ι] {f : ι → α} {c : α} (H : ∀ x, f x ≤ c) : supᵢ f ≤ c :=
  csupₛ_le (range_nonempty f) (by rwa [forall_range_iff])
#align csupr_le csupᵢ_le

/-- The indexed supremum of a function is bounded below by the value taken at one point-/
theorem le_csupᵢ {f : ι → α} (H : BddAbove (range f)) (c : ι) : f c ≤ supᵢ f :=
  le_csupₛ H (mem_range_self _)
#align le_csupr le_csupᵢ

theorem le_csupᵢ_of_le {f : ι → α} (H : BddAbove (range f)) (c : ι) (h : a ≤ f c) : a ≤ supᵢ f :=
  le_trans h (le_csupᵢ H c)
#align le_csupr_of_le le_csupᵢ_of_le

/-- The indexed supremum of two functions are comparable if the functions are pointwise comparable-/
theorem csupᵢ_mono {f g : ι → α} (B : BddAbove (range g)) (H : ∀ x, f x ≤ g x) :
    supᵢ f ≤ supᵢ g := by
  cases isEmpty_or_nonempty ι
  · rw [supᵢ_of_empty', supᵢ_of_empty']
  · exact csupᵢ_le fun x => le_csupᵢ_of_le B x (H x)
#align csupr_mono csupᵢ_mono

theorem le_csupᵢ_set {f : β → α} {s : Set β} (H : BddAbove (f '' s)) {c : β} (hc : c ∈ s) :
    f c ≤ ⨆ i : s, f i :=
  (le_csupₛ H <| mem_image_of_mem f hc).trans_eq supₛ_image'
#align le_csupr_set le_csupᵢ_set

/-- The indexed infimum of two functions are comparable if the functions are pointwise comparable-/
theorem cinfᵢ_mono {f g : ι → α} (B : BddBelow (range f)) (H : ∀ x, f x ≤ g x) : infᵢ f ≤ infᵢ g :=
  @csupᵢ_mono αᵒᵈ _ _ _ _ B H
#align cinfi_mono cinfᵢ_mono

/-- The indexed minimum of a function is bounded below by a uniform lower bound-/
theorem le_cinfᵢ [Nonempty ι] {f : ι → α} {c : α} (H : ∀ x, c ≤ f x) : c ≤ infᵢ f :=
  @csupᵢ_le αᵒᵈ _ _ _ _ _ H
#align le_cinfi le_cinfᵢ

/-- The indexed infimum of a function is bounded above by the value taken at one point-/
theorem cinfᵢ_le {f : ι → α} (H : BddBelow (range f)) (c : ι) : infᵢ f ≤ f c :=
  @le_csupᵢ αᵒᵈ _ _ _ H c
#align cinfi_le cinfᵢ_le

theorem cinfᵢ_le_of_le {f : ι → α} (H : BddBelow (range f)) (c : ι) (h : f c ≤ a) : infᵢ f ≤ a :=
  @le_csupᵢ_of_le αᵒᵈ _ _ _ _ H c h
#align cinfi_le_of_le cinfᵢ_le_of_le

theorem cinfᵢ_set_le {f : β → α} {s : Set β} (H : BddBelow (f '' s)) {c : β} (hc : c ∈ s) :
    (⨅ i : s, f i) ≤ f c :=
  @le_csupᵢ_set αᵒᵈ _ _ _ _ H _ hc
#align cinfi_set_le cinfᵢ_set_le

@[simp]
theorem csupᵢ_const [hι : Nonempty ι] {a : α} : (⨆ _b : ι, a) = a := by
  rw [supᵢ, range_const, csupₛ_singleton]
#align csupr_const csupᵢ_const

@[simp]
theorem cinfᵢ_const [Nonempty ι] {a : α} : (⨅ _b : ι, a) = a :=
  @csupᵢ_const αᵒᵈ _ _ _ _
#align cinfi_const cinfᵢ_const

@[simp]
theorem csupᵢ_unique [Unique ι] {s : ι → α} : (⨆ i, s i) = s default := by
  have : ∀ i, s i = s default := fun i => congr_arg s (Unique.eq_default i)
  simp only [this, csupᵢ_const]
#align supr_unique csupᵢ_unique

@[simp]
theorem cinfᵢ_unique [Unique ι] {s : ι → α} : (⨅ i, s i) = s default :=
  @csupᵢ_unique αᵒᵈ _ _ _ _
#align infi_unique cinfᵢ_unique

-- porting note: new lemma
theorem csupᵢ_subsingleton [Subsingleton ι] (i : ι) (s : ι → α) : (⨆ i, s i) = s i :=
  @csupᵢ_unique α ι _ ⟨⟨i⟩, fun j => Subsingleton.elim j i⟩ _

-- porting note: new lemma
theorem cinfᵢ_subsingleton [Subsingleton ι] (i : ι) (s : ι → α) : (⨅ i, s i) = s i :=
  @cinfᵢ_unique α ι _ ⟨⟨i⟩, fun j => Subsingleton.elim j i⟩ _

@[simp]
theorem csupᵢ_pos {p : Prop} {f : p → α} (hp : p) : (⨆ h : p, f h) = f hp :=
  csupᵢ_subsingleton hp f
#align csupr_pos csupᵢ_pos

@[simp]
theorem cinfᵢ_pos {p : Prop} {f : p → α} (hp : p) : (⨅ h : p, f h) = f hp :=
  @csupᵢ_pos αᵒᵈ _ _ _ hp
#align cinfi_pos cinfᵢ_pos

/-- Introduction rule to prove that `b` is the supremum of `f`: it suffices to check that `b`
is larger than `f i` for all `i`, and that this is not the case of any `w<b`.
See `supᵢ_eq_of_forall_le_of_forall_lt_exists_gt` for a version in complete lattices. -/
theorem csupᵢ_eq_of_forall_le_of_forall_lt_exists_gt [Nonempty ι] {f : ι → α} (h₁ : ∀ i, f i ≤ b)
    (h₂ : ∀ w, w < b → ∃ i, w < f i) : (⨆ i : ι, f i) = b :=
  csupₛ_eq_of_forall_le_of_forall_lt_exists_gt (range_nonempty f) (forall_range_iff.mpr h₁)
    fun w hw => exists_range_iff.mpr <| h₂ w hw
#align csupr_eq_of_forall_le_of_forall_lt_exists_gt csupᵢ_eq_of_forall_le_of_forall_lt_exists_gt

-- Porting note: in mathlib3 `by exact` is not needed
/-- Introduction rule to prove that `b` is the infimum of `f`: it suffices to check that `b`
is smaller than `f i` for all `i`, and that this is not the case of any `w>b`.
See `infᵢ_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in complete lattices. -/
theorem cinfᵢ_eq_of_forall_ge_of_forall_gt_exists_lt [Nonempty ι] {f : ι → α} (h₁ : ∀ i, b ≤ f i)
    (h₂ : ∀ w, b < w → ∃ i, f i < w) : (⨅ i : ι, f i) = b := by
  exact @csupᵢ_eq_of_forall_le_of_forall_lt_exists_gt αᵒᵈ _ _ _ _ ‹_› ‹_› ‹_›
#align cinfi_eq_of_forall_ge_of_forall_gt_exists_lt cinfᵢ_eq_of_forall_ge_of_forall_gt_exists_lt

/-- Nested intervals lemma: if `f` is a monotone sequence, `g` is an antitone sequence, and
`f n ≤ g n` for all `n`, then `⨆ n, f n` belongs to all the intervals `[f n, g n]`. -/
theorem Monotone.csupᵢ_mem_Inter_Icc_of_antitone [SemilatticeSup β] {f g : β → α} (hf : Monotone f)
    (hg : Antitone g) (h : f ≤ g) : (⨆ n, f n) ∈ ⋂ n, Icc (f n) (g n) := by
  refine' mem_interᵢ.2 fun n => _
  haveI : Nonempty β := ⟨n⟩
  have : ∀ m, f m ≤ g n := fun m => hf.forall_le_of_antitone hg h m n
  exact ⟨le_csupᵢ ⟨g <| n, forall_range_iff.2 this⟩ _, csupᵢ_le this⟩
#align monotone.csupr_mem_Inter_Icc_of_antitone Monotone.csupᵢ_mem_Inter_Icc_of_antitone

/-- Nested intervals lemma: if `[f n, g n]` is an antitone sequence of nonempty
closed intervals, then `⨆ n, f n` belongs to all the intervals `[f n, g n]`. -/
theorem csupᵢ_mem_Inter_Icc_of_antitone_Icc [SemilatticeSup β] {f g : β → α}
    (h : Antitone fun n => Icc (f n) (g n)) (h' : ∀ n, f n ≤ g n) :
    (⨆ n, f n) ∈ ⋂ n, Icc (f n) (g n) :=
  Monotone.csupᵢ_mem_Inter_Icc_of_antitone
    (fun _ n hmn => ((Icc_subset_Icc_iff (h' n)).1 (h hmn)).1)
    (fun _ n hmn => ((Icc_subset_Icc_iff (h' n)).1 (h hmn)).2) h'
#align csupr_mem_Inter_Icc_of_antitone_Icc csupᵢ_mem_Inter_Icc_of_antitone_Icc

/-- Introduction rule to prove that `b` is the supremum of `s`: it suffices to check that
1) `b` is an upper bound
2) every other upper bound `b'` satisfies `b ≤ b'`.-/
theorem csupₛ_eq_of_is_forall_le_of_forall_le_imp_ge (hs : s.Nonempty) (h_is_ub : ∀ a ∈ s, a ≤ b)
    (h_b_le_ub : ∀ ub, (∀ a ∈ s, a ≤ ub) → b ≤ ub) : supₛ s = b :=
  (csupₛ_le hs h_is_ub).antisymm ((h_b_le_ub _) fun _ => le_csupₛ ⟨b, h_is_ub⟩)
#align cSup_eq_of_is_forall_le_of_forall_le_imp_ge csupₛ_eq_of_is_forall_le_of_forall_le_imp_ge

end ConditionallyCompleteLattice

instance Pi.conditionallyCompleteLattice {ι : Type _} {α : ∀ _i : ι, Type _}
    [∀ i, ConditionallyCompleteLattice (α i)] : ConditionallyCompleteLattice (∀ i, α i) :=
  { Pi.lattice, Pi.supSet, Pi.infSet with
    le_csupₛ := fun s f ⟨g, hg⟩ hf i =>
      le_csupₛ ⟨g i, Set.forall_range_iff.2 fun ⟨f', hf'⟩ => hg hf' i⟩ ⟨⟨f, hf⟩, rfl⟩
    csupₛ_le := fun s f hs hf i =>
      (csupₛ_le (by haveI := hs.to_subtype; apply range_nonempty)) fun b ⟨⟨g, hg⟩, hb⟩ =>
        hb ▸ hf hg i
    cinfₛ_le := fun s f ⟨g, hg⟩ hf i =>
      cinfₛ_le ⟨g i, Set.forall_range_iff.2 fun ⟨f', hf'⟩ => hg hf' i⟩ ⟨⟨f, hf⟩, rfl⟩
    le_cinfₛ := fun s f hs hf i =>
      (le_cinfₛ (by haveI := hs.to_subtype; apply range_nonempty)) fun b ⟨⟨g, hg⟩, hb⟩ =>
        hb ▸ hf hg i }
#align pi.conditionally_complete_lattice Pi.conditionallyCompleteLattice

section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder α] {s t : Set α} {a b : α}

/-- When `b < supₛ s`, there is an element `a` in `s` with `b < a`, if `s` is nonempty and the order
is a linear order. -/
theorem exists_lt_of_lt_csupₛ (hs : s.Nonempty) (hb : b < supₛ s) : ∃ a ∈ s, b < a := by
  contrapose! hb
  exact csupₛ_le hs hb
#align exists_lt_of_lt_cSup exists_lt_of_lt_csupₛ

/-- Indexed version of the above lemma `exists_lt_of_lt_csupₛ`.
When `b < supᵢ f`, there is an element `i` such that `b < f i`.
-/
theorem exists_lt_of_lt_csupᵢ [Nonempty ι] {f : ι → α} (h : b < supᵢ f) : ∃ i, b < f i :=
  let ⟨_, ⟨i, rfl⟩, h⟩ := exists_lt_of_lt_csupₛ (range_nonempty f) h
  ⟨i, h⟩
#align exists_lt_of_lt_csupr exists_lt_of_lt_csupᵢ

/-- When `infₛ s < b`, there is an element `a` in `s` with `a < b`, if `s` is nonempty and the order
is a linear order.-/
theorem exists_lt_of_cinfₛ_lt (hs : s.Nonempty) (hb : infₛ s < b) : ∃ a ∈ s, a < b :=
  @exists_lt_of_lt_csupₛ αᵒᵈ _ _ _ hs hb
#align exists_lt_of_cInf_lt exists_lt_of_cinfₛ_lt

/-- Indexed version of the above lemma `exists_lt_of_cinfₛ_lt`
When `infᵢ f < a`, there is an element `i` such that `f i < a`.
-/
theorem exists_lt_of_cinfᵢ_lt [Nonempty ι] {f : ι → α} (h : infᵢ f < a) : ∃ i, f i < a :=
  @exists_lt_of_lt_csupᵢ αᵒᵈ _ _ _ _ _ h
#align exists_lt_of_cinfi_lt exists_lt_of_cinfᵢ_lt

open Function

variable [IsWellOrder α (· < ·)]

theorem infₛ_eq_argmin_on (hs : s.Nonempty) :
    infₛ s = argminOn id (@IsWellFounded.wf α (· < ·) _) s hs :=
  IsLeast.cinfₛ_eq ⟨argminOn_mem _ _ _ _, fun _ ha => argminOn_le id _ _ ha⟩
#align Inf_eq_argmin_on infₛ_eq_argmin_on

theorem isLeast_cinfₛ (hs : s.Nonempty) : IsLeast s (infₛ s) := by
  rw [infₛ_eq_argmin_on hs]
  exact ⟨argminOn_mem _ _ _ _, fun a ha => argminOn_le id _ _ ha⟩
#align is_least_Inf isLeast_cinfₛ

theorem le_cinfₛ_iff' (hs : s.Nonempty) : b ≤ infₛ s ↔ b ∈ lowerBounds s :=
  le_isGLB_iff (isLeast_cinfₛ hs).isGLB
#align le_cInf_iff' le_cinfₛ_iff'

theorem cinfₛ_mem (hs : s.Nonempty) : infₛ s ∈ s :=
  (isLeast_cinfₛ hs).1
#align Inf_mem cinfₛ_mem

theorem cinfᵢ_mem [Nonempty ι] (f : ι → α) : infᵢ f ∈ range f :=
  cinfₛ_mem (range_nonempty f)
#align infi_mem cinfᵢ_mem

theorem MonotoneOn.map_cinfₛ {β : Type _} [ConditionallyCompleteLattice β] {f : α → β}
    (hf : MonotoneOn f s) (hs : s.Nonempty) : f (infₛ s) = infₛ (f '' s) :=
  (hf.map_isLeast (isLeast_cinfₛ hs)).cinfₛ_eq.symm
#align monotone_on.map_Inf MonotoneOn.map_cinfₛ

theorem Monotone.map_cinfₛ {β : Type _} [ConditionallyCompleteLattice β] {f : α → β}
    (hf : Monotone f) (hs : s.Nonempty) : f (infₛ s) = infₛ (f '' s) :=
  (hf.map_isLeast (isLeast_cinfₛ hs)).cinfₛ_eq.symm
#align monotone.map_Inf Monotone.map_cinfₛ

end ConditionallyCompleteLinearOrder

/-!
### Lemmas about a conditionally complete linear order with bottom element

In this case we have `Sup ∅ = ⊥`, so we can drop some `Nonempty`/`Set.Nonempty` assumptions.
-/


section ConditionallyCompleteLinearOrderBot

variable [ConditionallyCompleteLinearOrderBot α]

@[simp]
theorem csupₛ_empty : (supₛ ∅ : α) = ⊥ :=
  ConditionallyCompleteLinearOrderBot.csupₛ_empty
#align cSup_empty csupₛ_empty

@[simp]
theorem csupᵢ_of_empty [IsEmpty ι] (f : ι → α) : (⨆ i, f i) = ⊥ := by
  rw [supᵢ_of_empty', csupₛ_empty]
#align csupr_of_empty csupᵢ_of_empty

theorem csupᵢ_false (f : False → α) : (⨆ i, f i) = ⊥ :=
  csupᵢ_of_empty f
#align csupr_false csupᵢ_false

@[simp]
theorem cinfₛ_univ : infₛ (univ : Set α) = ⊥ :=
  isLeast_univ.cinfₛ_eq
#align cInf_univ cinfₛ_univ

theorem isLUB_csupₛ' {s : Set α} (hs : BddAbove s) : IsLUB s (supₛ s) := by
  rcases eq_empty_or_nonempty s with (rfl | hne)
  · simp only [csupₛ_empty, isLUB_empty]
  · exact isLUB_csupₛ hne hs
#align is_lub_cSup' isLUB_csupₛ'

theorem csupₛ_le_iff' {s : Set α} (hs : BddAbove s) {a : α} : supₛ s ≤ a ↔ ∀ x ∈ s, x ≤ a :=
  isLUB_le_iff (isLUB_csupₛ' hs)
#align cSup_le_iff' csupₛ_le_iff'

theorem csupₛ_le' {s : Set α} {a : α} (h : a ∈ upperBounds s) : supₛ s ≤ a :=
  (csupₛ_le_iff' ⟨a, h⟩).2 h
#align cSup_le' csupₛ_le'

theorem le_csupₛ_iff' {s : Set α} {a : α} (h : BddAbove s) :
    a ≤ supₛ s ↔ ∀ b, b ∈ upperBounds s → a ≤ b :=
  ⟨fun h _ hb => le_trans h (csupₛ_le' hb), fun hb => hb _ fun _ => le_csupₛ h⟩
#align le_cSup_iff' le_csupₛ_iff'

theorem le_csupᵢ_iff' {s : ι → α} {a : α} (h : BddAbove (range s)) :
    a ≤ supᵢ s ↔ ∀ b, (∀ i, s i ≤ b) → a ≤ b := by simp [supᵢ, h, le_csupₛ_iff', upperBounds]
#align le_csupr_iff' le_csupᵢ_iff'

theorem le_cinfₛ_iff'' {s : Set α} {a : α} (ne : s.Nonempty) :
    a ≤ infₛ s ↔ ∀ b : α, b ∈ s → a ≤ b :=
  le_cinfₛ_iff ⟨⊥, fun _ _ => bot_le⟩ ne
#align le_cInf_iff'' le_cinfₛ_iff''

theorem le_cinfᵢ_iff' [Nonempty ι] {f : ι → α} {a : α} : a ≤ infᵢ f ↔ ∀ i, a ≤ f i :=
  le_cinfᵢ_iff ⟨⊥, fun _ _ => bot_le⟩
#align le_cinfi_iff' le_cinfᵢ_iff'

theorem cinfₛ_le' {s : Set α} {a : α} (h : a ∈ s) : infₛ s ≤ a :=
  cinfₛ_le ⟨⊥, fun _ _ => bot_le⟩ h
#align cInf_le' cinfₛ_le'

theorem cinfᵢ_le' (f : ι → α) (i : ι) : infᵢ f ≤ f i :=
  cinfᵢ_le ⟨⊥, fun _ _ => bot_le⟩ _
#align cinfi_le' cinfᵢ_le'

theorem exists_lt_of_lt_csupₛ' {s : Set α} {a : α} (h : a < supₛ s) : ∃ b ∈ s, a < b := by
  contrapose! h
  exact csupₛ_le' h
#align exists_lt_of_lt_cSup' exists_lt_of_lt_csupₛ'

theorem csupᵢ_le_iff' {f : ι → α} (h : BddAbove (range f)) {a : α} :
    (⨆ i, f i) ≤ a ↔ ∀ i, f i ≤ a :=
  (csupₛ_le_iff' h).trans forall_range_iff
#align csupr_le_iff' csupᵢ_le_iff'

theorem csupᵢ_le' {f : ι → α} {a : α} (h : ∀ i, f i ≤ a) : (⨆ i, f i) ≤ a :=
  csupₛ_le' <| forall_range_iff.2 h
#align csupr_le' csupᵢ_le'

theorem exists_lt_of_lt_csupᵢ' {f : ι → α} {a : α} (h : a < ⨆ i, f i) : ∃ i, a < f i := by
  contrapose! h
  exact csupᵢ_le' h
#align exists_lt_of_lt_csupr' exists_lt_of_lt_csupᵢ'

theorem csupᵢ_mono' {ι'} {f : ι → α} {g : ι' → α} (hg : BddAbove (range g))
    (h : ∀ i, ∃ i', f i ≤ g i') : supᵢ f ≤ supᵢ g :=
  csupᵢ_le' fun i => Exists.elim (h i) (le_csupᵢ_of_le hg)
#align csupr_mono' csupᵢ_mono'

theorem cinfₛ_le_cinfₛ' {s t : Set α} (h₁ : t.Nonempty) (h₂ : t ⊆ s) : infₛ s ≤ infₛ t :=
  cinfₛ_le_cinfₛ (OrderBot.bddBelow s) h₁ h₂
#align cInf_le_cInf' cinfₛ_le_cinfₛ'

end ConditionallyCompleteLinearOrderBot

namespace WithTop

open Classical

variable [ConditionallyCompleteLinearOrderBot α]

/-- The `supₛ` of a non-empty set is its least upper bound for a conditionally
complete lattice with a top. -/
theorem isLUB_supₛ' {β : Type _} [ConditionallyCompleteLattice β] {s : Set (WithTop β)}
    (hs : s.Nonempty) : IsLUB s (supₛ s) := by
  constructor
  · show ite _ _ _ ∈ _
    split_ifs with h₁ h₂
    · intro _ _
      exact le_top
    · rintro (⟨⟩ | a) ha
      · contradiction
      apply some_le_some.2
      exact le_csupₛ h₂ ha
    · intro _ _
      exact le_top
  · show ite _ _ _ ∈ _
    split_ifs with h₁ h₂
    · rintro (⟨⟩ | a) ha
      · exact le_rfl
      · exact False.elim (not_top_le_coe a (ha h₁))
    · rintro (⟨⟩ | b) hb
      · exact le_top
      refine' some_le_some.2 (csupₛ_le _ _)
      · rcases hs with ⟨⟨⟩ | b, hb⟩
        · exact absurd hb h₁
        · exact ⟨b, hb⟩
      · intro a ha
        exact some_le_some.1 (hb ha)
    · rintro (⟨⟩ | b) hb
      · exact le_rfl
      · exfalso
        apply h₂
        use b
        intro a ha
        exact some_le_some.1 (hb ha)
#align with_top.is_lub_Sup' WithTop.isLUB_supₛ'

-- Porting note: in mathlib3 `dsimp only [supₛ]` was not needed, we used `show IsLUB ∅ (ite _ _ _)`
theorem isLUB_supₛ (s : Set (WithTop α)) : IsLUB s (supₛ s) := by
  cases' s.eq_empty_or_nonempty with hs hs
  · rw [hs]
    dsimp only [supₛ]
    show IsLUB ∅ _
    split_ifs with h₁ h₂
    · cases h₁
    · rw [preimage_empty, csupₛ_empty]
      exact isLUB_empty
    · exfalso
      apply h₂
      use ⊥
      rintro a ⟨⟩
  exact isLUB_supₛ' hs
#align with_top.is_lub_Sup WithTop.isLUB_supₛ

/-- The `infₛ` of a bounded-below set is its greatest lower bound for a conditionally
complete lattice with a top. -/
theorem isGLB_infₛ' {β : Type _} [ConditionallyCompleteLattice β] {s : Set (WithTop β)}
    (hs : BddBelow s) : IsGLB s (infₛ s) := by
  constructor
  · show ite _ _ _ ∈ _
    split_ifs with h
    · intro a ha
      exact top_le_iff.2 (Set.mem_singleton_iff.1 (h ha))
    · rintro (⟨⟩ | a) ha
      · exact le_top
      refine' some_le_some.2 (cinfₛ_le _ ha)
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
    split_ifs with h
    · intro _ _
      exact le_top
    · rintro (⟨⟩ | a) ha
      · exfalso
        apply h
        intro b hb
        exact Set.mem_singleton_iff.2 (top_le_iff.1 (ha hb))
      · refine' some_le_some.2 (le_cinfₛ _ _)
        ·
          classical
            contrapose! h
            rintro (⟨⟩ | a) ha
            · exact mem_singleton ⊤
            · exact (h ⟨a, ha⟩).elim
        · intro b hb
          rw [← some_le_some]
          exact ha hb
#align with_top.is_glb_Inf' WithTop.isGLB_infₛ'

theorem isGLB_infₛ (s : Set (WithTop α)) : IsGLB s (infₛ s) := by
  by_cases hs : BddBelow s
  · exact isGLB_infₛ' hs
  · exfalso
    apply hs
    use ⊥
    intro _ _
    exact bot_le
#align with_top.is_glb_Inf WithTop.isGLB_infₛ

noncomputable instance : CompleteLinearOrder (WithTop α) :=
  { WithTop.linearOrder, WithTop.lattice, WithTop.orderTop, WithTop.orderBot with
    sup := Sup.sup
    le_supₛ := fun s => (isLUB_supₛ s).1
    supₛ_le := fun s => (isLUB_supₛ s).2
    inf := Inf.inf
    le_infₛ := fun s => (isGLB_infₛ s).2
    infₛ_le := fun s => (isGLB_infₛ s).1 }

/-- A version of `WithTop.coe_supₛ'` with a more convenient but less general statement. -/
@[norm_cast]
theorem coe_supₛ {s : Set α} (hb : BddAbove s) : ↑(supₛ s) = (⨆ a ∈ s, ↑a : WithTop α) := by
  rw [coe_supₛ' hb, supₛ_image]
#align with_top.coe_Sup WithTop.coe_supₛ

/-- A version of `WithTop.coe_infₛ'` with a more convenient but less general statement. -/
@[norm_cast]
theorem coe_infₛ {s : Set α} (hs : s.Nonempty) : ↑(infₛ s) = (⨅ a ∈ s, ↑a : WithTop α) := by
  rw [coe_infₛ' hs, infₛ_image]
#align with_top.coe_Inf WithTop.coe_infₛ

end WithTop

namespace Monotone

variable [Preorder α] [ConditionallyCompleteLattice β] {f : α → β} (h_mono : Monotone f)

/-! A monotone function into a conditionally complete lattice preserves the ordering properties of
`supₛ` and `infₛ`. -/


theorem le_csupₛ_image {s : Set α} {c : α} (hcs : c ∈ s) (h_bdd : BddAbove s) :
    f c ≤ supₛ (f '' s) :=
  le_csupₛ (map_bddAbove h_mono h_bdd) (mem_image_of_mem f hcs)
#align monotone.le_cSup_image Monotone.le_csupₛ_image

theorem csupₛ_image_le {s : Set α} (hs : s.Nonempty) {B : α} (hB : B ∈ upperBounds s) :
    supₛ (f '' s) ≤ f B :=
  csupₛ_le (Nonempty.image f hs) (h_mono.mem_upperBounds_image hB)
#align monotone.cSup_image_le Monotone.csupₛ_image_le

-- Porting note: in mathlib3 `f'` is not needed
theorem cinfₛ_image_le {s : Set α} {c : α} (hcs : c ∈ s) (h_bdd : BddBelow s) :
    infₛ (f '' s) ≤ f c := by
  let f' : αᵒᵈ → βᵒᵈ := f
  exact @le_csupₛ_image αᵒᵈ βᵒᵈ _ _ _
    (show Monotone f' from fun x y hxy => h_mono hxy) _ _ hcs h_bdd
#align monotone.cInf_image_le Monotone.cinfₛ_image_le

-- Porting note: in mathlib3 `f'` is not needed
theorem le_cinfₛ_image {s : Set α} (hs : s.Nonempty) {B : α} (hB : B ∈ lowerBounds s) :
    f B ≤ infₛ (f '' s) := by
  let f' : αᵒᵈ → βᵒᵈ := f
  exact @csupₛ_image_le αᵒᵈ βᵒᵈ _ _ _
    (show Monotone f' from fun x y hxy => h_mono hxy) _ hs _ hB
#align monotone.le_cInf_image Monotone.le_cinfₛ_image

end Monotone

namespace GaloisConnection

variable [ConditionallyCompleteLattice α] [ConditionallyCompleteLattice β] [Nonempty ι] {l : α → β}
  {u : β → α}

theorem l_csupₛ (gc : GaloisConnection l u) {s : Set α} (hne : s.Nonempty) (hbdd : BddAbove s) :
    l (supₛ s) = ⨆ x : s, l x :=
  Eq.symm <| IsLUB.csupᵢ_set_eq (gc.isLUB_l_image <| isLUB_csupₛ hne hbdd) hne
#align galois_connection.l_cSup GaloisConnection.l_csupₛ

theorem l_csupₛ' (gc : GaloisConnection l u) {s : Set α} (hne : s.Nonempty) (hbdd : BddAbove s) :
    l (supₛ s) = supₛ (l '' s) := by rw [gc.l_csupₛ hne hbdd, supₛ_image']
#align galois_connection.l_cSup' GaloisConnection.l_csupₛ'

theorem l_csupᵢ (gc : GaloisConnection l u) {f : ι → α} (hf : BddAbove (range f)) :
    l (⨆ i, f i) = ⨆ i, l (f i) := by rw [supᵢ, gc.l_csupₛ (range_nonempty _) hf, supᵢ_range']
#align galois_connection.l_csupr GaloisConnection.l_csupᵢ

theorem l_csupᵢ_set (gc : GaloisConnection l u) {s : Set γ} {f : γ → α} (hf : BddAbove (f '' s))
    (hne : s.Nonempty) : l (⨆ i : s, f i) = ⨆ i : s, l (f i) := by
  haveI := hne.to_subtype
  rw [image_eq_range] at hf
  exact gc.l_csupᵢ hf
#align galois_connection.l_csupr_set GaloisConnection.l_csupᵢ_set

theorem u_cinfₛ (gc : GaloisConnection l u) {s : Set β} (hne : s.Nonempty) (hbdd : BddBelow s) :
    u (infₛ s) = ⨅ x : s, u x :=
  gc.dual.l_csupₛ hne hbdd
#align galois_connection.u_cInf GaloisConnection.u_cinfₛ

theorem u_cinfₛ' (gc : GaloisConnection l u) {s : Set β} (hne : s.Nonempty) (hbdd : BddBelow s) :
    u (infₛ s) = infₛ (u '' s) :=
  gc.dual.l_csupₛ' hne hbdd
#align galois_connection.u_cInf' GaloisConnection.u_cinfₛ'

theorem u_cinfᵢ (gc : GaloisConnection l u) {f : ι → β} (hf : BddBelow (range f)) :
    u (⨅ i, f i) = ⨅ i, u (f i) :=
  gc.dual.l_csupᵢ hf
#align galois_connection.u_cinfi GaloisConnection.u_cinfᵢ

theorem u_cinfᵢ_set (gc : GaloisConnection l u) {s : Set γ} {f : γ → β} (hf : BddBelow (f '' s))
    (hne : s.Nonempty) : u (⨅ i : s, f i) = ⨅ i : s, u (f i) :=
  gc.dual.l_csupᵢ_set hf hne
#align galois_connection.u_cinfi_set GaloisConnection.u_cinfᵢ_set

end GaloisConnection

namespace OrderIso

variable [ConditionallyCompleteLattice α] [ConditionallyCompleteLattice β] [Nonempty ι]

theorem map_csupₛ (e : α ≃o β) {s : Set α} (hne : s.Nonempty) (hbdd : BddAbove s) :
    e (supₛ s) = ⨆ x : s, e x :=
  e.to_galoisConnection.l_csupₛ hne hbdd
#align order_iso.map_cSup OrderIso.map_csupₛ

theorem map_csupₛ' (e : α ≃o β) {s : Set α} (hne : s.Nonempty) (hbdd : BddAbove s) :
    e (supₛ s) = supₛ (e '' s) :=
  e.to_galoisConnection.l_csupₛ' hne hbdd
#align order_iso.map_cSup' OrderIso.map_csupₛ'

theorem map_csupᵢ (e : α ≃o β) {f : ι → α} (hf : BddAbove (range f)) :
    e (⨆ i, f i) = ⨆ i, e (f i) :=
  e.to_galoisConnection.l_csupᵢ hf
#align order_iso.map_csupr OrderIso.map_csupᵢ

theorem map_csupᵢ_set (e : α ≃o β) {s : Set γ} {f : γ → α} (hf : BddAbove (f '' s))
    (hne : s.Nonempty) : e (⨆ i : s, f i) = ⨆ i : s, e (f i) :=
  e.to_galoisConnection.l_csupᵢ_set hf hne
#align order_iso.map_csupr_set OrderIso.map_csupᵢ_set

theorem map_cinfₛ (e : α ≃o β) {s : Set α} (hne : s.Nonempty) (hbdd : BddBelow s) :
    e (infₛ s) = ⨅ x : s, e x :=
  e.dual.map_csupₛ hne hbdd
#align order_iso.map_cInf OrderIso.map_cinfₛ

theorem map_cinfₛ' (e : α ≃o β) {s : Set α} (hne : s.Nonempty) (hbdd : BddBelow s) :
    e (infₛ s) = infₛ (e '' s) :=
  e.dual.map_csupₛ' hne hbdd
#align order_iso.map_cInf' OrderIso.map_cinfₛ'

theorem map_cinfᵢ (e : α ≃o β) {f : ι → α} (hf : BddBelow (range f)) :
    e (⨅ i, f i) = ⨅ i, e (f i) :=
  e.dual.map_csupᵢ hf
#align order_iso.map_cinfi OrderIso.map_cinfᵢ

theorem map_cinfᵢ_set (e : α ≃o β) {s : Set γ} {f : γ → α} (hf : BddBelow (f '' s))
    (hne : s.Nonempty) : e (⨅ i : s, f i) = ⨅ i : s, e (f i) :=
  e.dual.map_csupᵢ_set hf hne
#align order_iso.map_cinfi_set OrderIso.map_cinfᵢ_set

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

theorem csupₛ_image2_eq_csupₛ_csupₛ (h₁ : ∀ b, GaloisConnection (swap l b) (u₁ b))
    (h₂ : ∀ a, GaloisConnection (l a) (u₂ a)) (hs₀ : s.Nonempty) (hs₁ : BddAbove s)
    (ht₀ : t.Nonempty) (ht₁ : BddAbove t) : supₛ (image2 l s t) = l (supₛ s) (supₛ t) := by
  refine' eq_of_forall_ge_iff fun c => _
  rw [csupₛ_le_iff (hs₁.image2 (fun _ => (h₁ _).monotone_l) (fun _ => (h₂ _).monotone_l) ht₁)
      (hs₀.image2 ht₀),
    forall_image2_iff, forall₂_swap, (h₂ _).le_iff_le, csupₛ_le_iff ht₁ ht₀]
  simp_rw [← (h₂ _).le_iff_le, (h₁ _).le_iff_le, csupₛ_le_iff hs₁ hs₀]
#align cSup_image2_eq_cSup_cSup csupₛ_image2_eq_csupₛ_csupₛ

theorem csupₛ_image2_eq_csupₛ_cinfₛ (h₁ : ∀ b, GaloisConnection (swap l b) (u₁ b))
    (h₂ : ∀ a, GaloisConnection (l a ∘ ofDual) (toDual ∘ u₂ a)) :
    s.Nonempty → BddAbove s → t.Nonempty → BddBelow t → supₛ (image2 l s t) = l (supₛ s) (infₛ t) :=
  @csupₛ_image2_eq_csupₛ_csupₛ _ βᵒᵈ _ _ _ _ _ _ _ _ _ h₁ h₂
#align cSup_image2_eq_cSup_cInf csupₛ_image2_eq_csupₛ_cinfₛ

theorem csupₛ_image2_eq_cinfₛ_csupₛ (h₁ : ∀ b, GaloisConnection (swap l b ∘ ofDual) (toDual ∘ u₁ b))
    (h₂ : ∀ a, GaloisConnection (l a) (u₂ a)) :
    s.Nonempty → BddBelow s → t.Nonempty → BddAbove t → supₛ (image2 l s t) = l (infₛ s) (supₛ t) :=
  @csupₛ_image2_eq_csupₛ_csupₛ αᵒᵈ _ _ _ _ _ _ _ _ _ _ h₁ h₂
#align cSup_image2_eq_cInf_cSup csupₛ_image2_eq_cinfₛ_csupₛ

theorem csupₛ_image2_eq_cinfₛ_cinfₛ (h₁ : ∀ b, GaloisConnection (swap l b ∘ ofDual) (toDual ∘ u₁ b))
    (h₂ : ∀ a, GaloisConnection (l a ∘ ofDual) (toDual ∘ u₂ a)) :
    s.Nonempty → BddBelow s → t.Nonempty → BddBelow t → supₛ (image2 l s t) = l (infₛ s) (infₛ t) :=
  @csupₛ_image2_eq_csupₛ_csupₛ αᵒᵈ βᵒᵈ _ _ _ _ _ _ _ _ _ h₁ h₂
#align cSup_image2_eq_cInf_cInf csupₛ_image2_eq_cinfₛ_cinfₛ

theorem cinfₛ_image2_eq_cinfₛ_cinfₛ (h₁ : ∀ b, GaloisConnection (l₁ b) (swap u b))
    (h₂ : ∀ a, GaloisConnection (l₂ a) (u a)) :
    s.Nonempty → BddBelow s → t.Nonempty → BddBelow t → infₛ (image2 u s t) = u (infₛ s) (infₛ t) :=
  @csupₛ_image2_eq_csupₛ_csupₛ αᵒᵈ βᵒᵈ γᵒᵈ _ _ _ _ _ _ l₁ l₂ (fun _ => (h₁ _).dual) fun _ =>
    (h₂ _).dual
#align cInf_image2_eq_cInf_cInf cinfₛ_image2_eq_cinfₛ_cinfₛ

theorem cinfₛ_image2_eq_cinfₛ_csupₛ (h₁ : ∀ b, GaloisConnection (l₁ b) (swap u b))
    (h₂ : ∀ a, GaloisConnection (toDual ∘ l₂ a) (u a ∘ ofDual)) :
    s.Nonempty → BddBelow s → t.Nonempty → BddAbove t → infₛ (image2 u s t) = u (infₛ s) (supₛ t) :=
  @cinfₛ_image2_eq_cinfₛ_cinfₛ _ βᵒᵈ _ _ _ _ _ _ _ _ _ h₁ h₂
#align cInf_image2_eq_cInf_cSup cinfₛ_image2_eq_cinfₛ_csupₛ

theorem cinfₛ_image2_eq_csupₛ_cinfₛ (h₁ : ∀ b, GaloisConnection (toDual ∘ l₁ b) (swap u b ∘ ofDual))
    (h₂ : ∀ a, GaloisConnection (l₂ a) (u a)) :
    s.Nonempty → BddAbove s → t.Nonempty → BddBelow t → infₛ (image2 u s t) = u (supₛ s) (infₛ t) :=
  @cinfₛ_image2_eq_cinfₛ_cinfₛ αᵒᵈ _ _ _ _ _ _ _ _ _ _ h₁ h₂
#align cInf_image2_eq_cSup_cInf cinfₛ_image2_eq_csupₛ_cinfₛ

theorem cinfₛ_image2_eq_csupₛ_csupₛ (h₁ : ∀ b, GaloisConnection (toDual ∘ l₁ b) (swap u b ∘ ofDual))
    (h₂ : ∀ a, GaloisConnection (toDual ∘ l₂ a) (u a ∘ ofDual)) :
    s.Nonempty → BddAbove s → t.Nonempty → BddAbove t → infₛ (image2 u s t) = u (supₛ s) (supₛ t) :=
  @cinfₛ_image2_eq_cinfₛ_cinfₛ αᵒᵈ βᵒᵈ _ _ _ _ _ _ _ _ _ h₁ h₂
#align cInf_image2_eq_cSup_cSup cinfₛ_image2_eq_csupₛ_csupₛ

end

section WithTopBot

/-!
### Complete lattice structure on `WithTop (WithBot α)`

If `α` is a `ConditionallyCompleteLattice`, then we show that `WithTop α` and `WithBot α`
also inherit the structure of conditionally complete lattices. Furthermore, we show
that `WithTop (WithBot α)` and `WithBot (WithTop α)` naturally inherit the structure of a
complete lattice. Note that for `α` a conditionally complete lattice, `supₛ` and `infₛ` both return
junk values for sets which are empty or unbounded. The extension of `supₛ` to `WithTop α` fixes
the unboundedness problem and the extension to `WithBot α` fixes the problem with
the empty set.

This result can be used to show that the extended reals `[-∞, ∞]` are a complete linear order.
-/


open Classical

/-- Adding a top element to a conditionally complete lattice
gives a conditionally complete lattice -/
noncomputable instance WithTop.conditionallyCompleteLattice {α : Type _}
    [ConditionallyCompleteLattice α] : ConditionallyCompleteLattice (WithTop α) :=
  { WithTop.lattice, instSupSetWithTop, instInfSetWithTop with
    le_csupₛ := fun _ a _ haS => (WithTop.isLUB_supₛ' ⟨a, haS⟩).1 haS
    csupₛ_le := fun _ _ hS haS => (WithTop.isLUB_supₛ' hS).2 haS
    cinfₛ_le := fun _ _ hS haS => (WithTop.isGLB_infₛ' hS).1 haS
    le_cinfₛ := fun _ a _ haS => (WithTop.isGLB_infₛ' ⟨a, haS⟩).2 haS }
#align with_top.conditionally_complete_lattice WithTop.conditionallyCompleteLattice

/-- Adding a bottom element to a conditionally complete lattice
gives a conditionally complete lattice -/
noncomputable instance WithBot.conditionallyCompleteLattice {α : Type _}
    [ConditionallyCompleteLattice α] : ConditionallyCompleteLattice (WithBot α) :=
  { WithBot.lattice with
    le_csupₛ := (@WithTop.conditionallyCompleteLattice αᵒᵈ _).cinfₛ_le
    csupₛ_le := (@WithTop.conditionallyCompleteLattice αᵒᵈ _).le_cinfₛ
    cinfₛ_le := (@WithTop.conditionallyCompleteLattice αᵒᵈ _).le_csupₛ
    le_cinfₛ := (@WithTop.conditionallyCompleteLattice αᵒᵈ _).csupₛ_le }
#align with_bot.conditionally_complete_lattice WithBot.conditionallyCompleteLattice

-- Poting note: `convert @bot_le (WithTop (WithBot α)) _ _ a` was `convert bot_le`
noncomputable instance WithTop.WithBot.completeLattice {α : Type _}
    [ConditionallyCompleteLattice α] : CompleteLattice (WithTop (WithBot α)) :=
  { instInfSetWithTop, instSupSetWithTop, WithTop.boundedOrder, WithTop.lattice with
    le_supₛ := fun S a haS => (WithTop.isLUB_supₛ' ⟨a, haS⟩).1 haS
    supₛ_le := fun S a ha => by
      cases' S.eq_empty_or_nonempty with h h
      · show ite _ _ _ ≤ a
        split_ifs with h₁ h₂
        · rw [h] at h₁
          cases h₁
        · convert @bot_le _ _ _ a
          -- porting note: previous proof relied on convert unfolding
          -- the definition of ⊥
          apply congr_arg
          simp only [h, preimage_empty, WithBot.supₛ_empty]
        · exfalso
          apply h₂
          use ⊥
          rw [h]
          rintro b ⟨⟩
      · refine' (WithTop.isLUB_supₛ' h).2 ha
    infₛ_le := fun S a haS =>
      show ite _ _ _ ≤ a by
        split_ifs with h₁
        · cases' a with a
          exact le_rfl
          cases h₁ haS
        · cases a
          · exact le_top
          · apply WithTop.some_le_some.2
            refine' cinfₛ_le _ haS
            use ⊥
            intro b _
            exact bot_le
    le_infₛ := fun S a haS => (WithTop.isGLB_infₛ' ⟨a, haS⟩).2 haS }
#align with_top.with_bot.complete_lattice WithTop.WithBot.completeLattice

noncomputable instance WithTop.WithBot.completeLinearOrder {α : Type _}
    [ConditionallyCompleteLinearOrder α] : CompleteLinearOrder (WithTop (WithBot α)) :=
  { WithTop.WithBot.completeLattice, WithTop.linearOrder with }
#align with_top.with_bot.complete_linear_order WithTop.WithBot.completeLinearOrder

noncomputable instance WithBot.WithTop.completeLattice {α : Type _}
    [ConditionallyCompleteLattice α] : CompleteLattice (WithBot (WithTop α)) :=
  { instInfSetWithBot, instSupSetWithBot, WithBot.instBoundedOrderWithBotLe, WithBot.lattice with
    le_supₛ := (@WithTop.WithBot.completeLattice αᵒᵈ _).infₛ_le
    supₛ_le := (@WithTop.WithBot.completeLattice αᵒᵈ _).le_infₛ
    infₛ_le := (@WithTop.WithBot.completeLattice αᵒᵈ _).le_supₛ
    le_infₛ := (@WithTop.WithBot.completeLattice αᵒᵈ _).supₛ_le }
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
    exact ⟨f i, ⟨i, rfl⟩, WithTop.coe_lt_coe.mp hi⟩
  · rcases hf (a.untop ha.ne) with ⟨-, ⟨i, rfl⟩, hi⟩
    exact ⟨i, by simpa only [WithTop.coe_untop _ ha.ne] using WithTop.coe_lt_coe.mpr hi⟩
#align with_top.supr_coe_eq_top WithTop.supr_coe_eq_top

theorem WithTop.supr_coe_lt_top {ι : Sort _} {α : Type _} [ConditionallyCompleteLinearOrderBot α]
    (f : ι → α) : (⨆ x, (f x : WithTop α)) < ⊤ ↔ BddAbove (Set.range f) :=
  lt_top_iff_ne_top.trans <| (WithTop.supr_coe_eq_top f).not.trans not_not
#align with_top.supr_coe_lt_top WithTop.supr_coe_lt_top

end WithTopBot

-- Guard against import creep
-- Porting note: `assert_not_exists` has not been ported yet.
--assert_not_exists multiset
