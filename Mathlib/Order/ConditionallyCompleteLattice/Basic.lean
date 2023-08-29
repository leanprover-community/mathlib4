/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.WellFounded
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Data.Set.Lattice

#align_import order.conditionally_complete_lattice.basic from "leanprover-community/mathlib"@"29cb56a7b35f72758b05a30490e1f10bd62c35c1"

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


open Function OrderDual Set

variable {α β γ : Type*} {ι : Sort*}

section

/-!
Extension of `sSup` and `sInf` from a preorder `α` to `WithTop α` and `WithBot α`
-/


open Classical

noncomputable instance WithTop.instSupSet {α : Type*} [Preorder α] [SupSet α] :
    SupSet (WithTop α) :=
  ⟨fun S =>
    if ⊤ ∈ S then ⊤ else if BddAbove ((fun (a : α) ↦ ↑a) ⁻¹' S : Set α) then
      ↑(sSup ((fun (a : α) ↦ (a : WithTop α)) ⁻¹' S : Set α)) else ⊤⟩

noncomputable instance WithTop.instInfSet {α : Type*} [InfSet α] : InfSet (WithTop α) :=
  ⟨fun S => if S ⊆ {⊤} then ⊤ else ↑(sInf ((fun (a : α) ↦ ↑a) ⁻¹' S : Set α))⟩

noncomputable instance WithBot.instSupSet {α : Type*} [SupSet α] : SupSet (WithBot α) :=
  ⟨(@WithTop.instInfSet αᵒᵈ _).sInf⟩

noncomputable instance WithBot.instInfSet {α : Type*} [Preorder α] [InfSet α] :
    InfSet (WithBot α) :=
  ⟨(@WithTop.instSupSet αᵒᵈ _).sSup⟩

theorem WithTop.sSup_eq [Preorder α] [SupSet α] {s : Set (WithTop α)} (hs : ⊤ ∉ s)
    (hs' : BddAbove ((↑) ⁻¹' s : Set α)) : sSup s = ↑(sSup ((↑) ⁻¹' s) : α) :=
  (if_neg hs).trans $ if_pos hs'
#align with_top.Sup_eq WithTop.sSup_eq

theorem WithTop.sInf_eq [InfSet α] {s : Set (WithTop α)} (hs : ¬s ⊆ {⊤}) :
    sInf s = ↑(sInf ((↑) ⁻¹' s) : α) :=
  if_neg hs
#align with_top.Inf_eq WithTop.sInf_eq

theorem WithBot.sInf_eq [Preorder α] [InfSet α] {s : Set (WithBot α)} (hs : ⊥ ∉ s)
    (hs' : BddBelow ((↑) ⁻¹' s : Set α)) : sInf s = ↑(sInf ((↑) ⁻¹' s) : α) :=
  (if_neg hs).trans $ if_pos hs'
#align with_bot.Inf_eq WithBot.sInf_eq

theorem WithBot.sSup_eq [SupSet α] {s : Set (WithBot α)} (hs : ¬s ⊆ {⊥}) :
    sSup s = ↑(sSup ((↑) ⁻¹' s) : α) :=
  if_neg hs
#align with_bot.Sup_eq WithBot.sSup_eq

@[simp]
theorem WithTop.sInf_empty {α : Type*} [InfSet α] : sInf (∅ : Set (WithTop α)) = ⊤ :=
  if_pos <| Set.empty_subset _
#align with_top.cInf_empty WithTop.sInf_empty

@[simp]
theorem WithTop.iInf_empty {α : Type*} [IsEmpty ι] [InfSet α] (f : ι → WithTop α) :
    ⨅ i, f i = ⊤ := by rw [iInf, range_eq_empty, WithTop.sInf_empty]
                       -- 🎉 no goals
#align with_top.cinfi_empty WithTop.iInf_empty

theorem WithTop.coe_sInf' [InfSet α] {s : Set α} (hs : s.Nonempty) :
    ↑(sInf s) = (sInf ((fun (a : α) ↦ ↑a) '' s) : WithTop α) := by
  obtain ⟨x, hx⟩ := hs
  -- ⊢ ↑(sInf s) = sInf ((fun a => ↑a) '' s)
  change _ = ite _ _ _
  -- ⊢ ↑(sInf s) = if (fun a => ↑a) '' s ⊆ {⊤} then ⊤ else ↑(sInf ((fun a => ↑a) ⁻¹ …
  split_ifs with h
  -- ⊢ ↑(sInf s) = ⊤
  · cases h (mem_image_of_mem _ hx)
    -- 🎉 no goals
  · rw [preimage_image_eq]
    -- ⊢ Injective fun a => ↑a
    exact Option.some_injective _
    -- 🎉 no goals
#align with_top.coe_Inf' WithTop.coe_sInf'

-- Porting note: the mathlib3 proof uses `range_comp` in the opposite direction and
-- does not need `rfl`.
@[norm_cast]
theorem WithTop.coe_iInf [Nonempty ι] [InfSet α] (f : ι → α) :
    ↑(⨅ i, f i) = (⨅ i, f i : WithTop α) := by
  rw [iInf, iInf, WithTop.coe_sInf' (range_nonempty f), ← range_comp]; rfl
  -- ⊢ sInf (range ((fun a => ↑a) ∘ f)) = sInf (range fun i => ↑(f i))
                                                                       -- 🎉 no goals
#align with_top.coe_infi WithTop.coe_iInf

theorem WithTop.coe_sSup' [Preorder α] [SupSet α] {s : Set α} (hs : BddAbove s) :
    ↑(sSup s) = (sSup ((fun (a : α) ↦ ↑a) '' s) : WithTop α) := by
  change _ = ite _ _ _
  -- ⊢ ↑(sSup s) = if ⊤ ∈ (fun a => ↑a) '' s then ⊤ else if BddAbove ((fun a => ↑a) …
  rw [if_neg, preimage_image_eq, if_pos hs]
  -- ⊢ Injective fun a => ↑a
  · exact Option.some_injective _
    -- 🎉 no goals
  · rintro ⟨x, _, ⟨⟩⟩
    -- 🎉 no goals
#align with_top.coe_Sup' WithTop.coe_sSup'

-- Porting note: the mathlib3 proof uses `range_comp` in the opposite direction and
-- does not need `rfl`.
@[norm_cast]
theorem WithTop.coe_iSup [Preorder α] [SupSet α] (f : ι → α) (h : BddAbove (Set.range f)) :
    ↑(⨆ i, f i) = (⨆ i, f i : WithTop α) := by
    rw [iSup, iSup, WithTop.coe_sSup' h, ← range_comp]; rfl
    -- ⊢ sSup (range ((fun a => ↑a) ∘ f)) = sSup (range fun i => ↑(f i))
                                                        -- 🎉 no goals
#align with_top.coe_supr WithTop.coe_iSup

@[simp]
theorem WithBot.csSup_empty {α : Type*} [SupSet α] : sSup (∅ : Set (WithBot α)) = ⊥ :=
  if_pos <| Set.empty_subset _
#align with_bot.cSup_empty WithBot.csSup_empty

@[simp]
theorem WithBot.ciSup_empty {α : Type*} [IsEmpty ι] [SupSet α] (f : ι → WithBot α) :
    ⨆ i, f i = ⊥ :=
  @WithTop.iInf_empty _ αᵒᵈ _ _ _
#align with_bot.csupr_empty WithBot.ciSup_empty

@[norm_cast]
theorem WithBot.coe_sSup' [SupSet α] {s : Set α} (hs : s.Nonempty) :
    ↑(sSup s) = (sSup ((fun (a : α) ↦ ↑a) '' s) : WithBot α) :=
  @WithTop.coe_sInf' αᵒᵈ _ _ hs
#align with_bot.coe_Sup' WithBot.coe_sSup'

@[norm_cast]
theorem WithBot.coe_iSup [Nonempty ι] [SupSet α] (f : ι → α) :
    ↑(⨆ i, f i) = (⨆ i, f i : WithBot α) :=
  @WithTop.coe_iInf αᵒᵈ _ _ _ _
#align with_bot.coe_supr WithBot.coe_iSup

@[norm_cast]
theorem WithBot.coe_sInf' [Preorder α] [InfSet α] {s : Set α} (hs : BddBelow s) :
    ↑(sInf s) = (sInf ((fun (a : α) ↦ ↑a) '' s) : WithBot α) :=
  @WithTop.coe_sSup' αᵒᵈ _ _ _ hs
#align with_bot.coe_Inf' WithBot.coe_sInf'

@[norm_cast]
theorem WithBot.coe_iInf [Preorder α] [InfSet α] (f : ι → α) (h : BddBelow (Set.range f)) :
    ↑(⨅ i, f i) = (⨅ i, f i : WithBot α) :=
  @WithTop.coe_iSup αᵒᵈ _ _ _ _ h
#align with_bot.coe_infi WithBot.coe_iInf

end

/-- A conditionally complete lattice is a lattice in which
every nonempty subset which is bounded above has a supremum, and
every nonempty subset which is bounded below has an infimum.
Typical examples are real numbers or natural numbers.

To differentiate the statements from the corresponding statements in (unconditional)
complete lattices, we prefix sInf and subₛ by a c everywhere. The same statements should
hold in both worlds, sometimes with additional assumptions of nonemptiness or
boundedness.-/
class ConditionallyCompleteLattice (α : Type*) extends Lattice α, SupSet α, InfSet α where
  /-- `a ≤ sSup s` for all `a ∈ s`. -/
  le_csSup : ∀ s a, BddAbove s → a ∈ s → a ≤ sSup s
  /-- `sSup s ≤ a` for all `a ∈ upperBounds s`. -/
  csSup_le : ∀ s a, Set.Nonempty s → a ∈ upperBounds s → sSup s ≤ a
  /-- `sInf s ≤ a` for all `a ∈ s`. -/
  csInf_le : ∀ s a, BddBelow s → a ∈ s → sInf s ≤ a
  /-- `a ≤ sInf s` for all `a ∈ lowerBounds s`. -/
  le_csInf : ∀ s a, Set.Nonempty s → a ∈ lowerBounds s → a ≤ sInf s
#align conditionally_complete_lattice ConditionallyCompleteLattice

-- Porting note: mathlib3 used `renaming`
/-- A conditionally complete linear order is a linear order in which
every nonempty subset which is bounded above has a supremum, and
every nonempty subset which is bounded below has an infimum.
Typical examples are real numbers or natural numbers.

To differentiate the statements from the corresponding statements in (unconditional)
complete linear orders, we prefix sInf and sSup by a c everywhere. The same statements should
hold in both worlds, sometimes with additional assumptions of nonemptiness or
boundedness.-/
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
  /-- If a set is not bounded above, its supremum is by convention `Sup univ`. -/
  csSup_of_not_bddAbove : ∀ s, ¬BddAbove s → sSup s = sSup (univ : Set α)
  /-- If a set is not bounded below, its infimum is by convention `Inf univ`. -/
  csInf_of_not_bddBelow : ∀ s, ¬BddBelow s → sInf s = sInf (univ : Set α)
#align conditionally_complete_linear_order ConditionallyCompleteLinearOrder

instance (α : Type*) [ConditionallyCompleteLinearOrder α] : LinearOrder α :=
  { ‹ConditionallyCompleteLinearOrder α› with
    max := Sup.sup, min := Inf.inf,
    min_def := fun a b ↦ by
      by_cases hab : a = b
      -- ⊢ min a b = if a ≤ b then a else b
      · simp [hab]
        -- 🎉 no goals
      · rcases ConditionallyCompleteLinearOrder.le_total a b with (h₁ | h₂)
        -- ⊢ min a b = if a ≤ b then a else b
        · simp [h₁]
          -- 🎉 no goals
        · simp [show ¬(a ≤ b) from fun h => hab (le_antisymm h h₂), h₂]
          -- 🎉 no goals
    max_def := fun a b ↦ by
      by_cases hab : a = b
      -- ⊢ max a b = if a ≤ b then b else a
      · simp [hab]
        -- 🎉 no goals
      · rcases ConditionallyCompleteLinearOrder.le_total a b with (h₁ | h₂)
        -- ⊢ max a b = if a ≤ b then b else a
        · simp [h₁]
          -- 🎉 no goals
        · simp [show ¬(a ≤ b) from fun h => hab (le_antisymm h h₂), h₂] }
          -- 🎉 no goals

/-- A conditionally complete linear order with `Bot` is a linear order with least element, in which
every nonempty subset which is bounded above has a supremum, and every nonempty subset (necessarily
bounded below) has an infimum.  A typical example is the natural numbers.

To differentiate the statements from the corresponding statements in (unconditional)
complete linear orders, we prefix `sInf` and `sSup` by a c everywhere. The same statements should
hold in both worlds, sometimes with additional assumptions of nonemptiness or
boundedness.-/
class ConditionallyCompleteLinearOrderBot (α : Type*) extends ConditionallyCompleteLinearOrder α,
  Bot α where
  /-- `⊥` is the least element -/
  bot_le : ∀ x : α, ⊥ ≤ x
  /-- The supremum of the empty set is `⊥` -/
  csSup_empty : sSup ∅ = ⊥
#align conditionally_complete_linear_order_bot ConditionallyCompleteLinearOrderBot

-- see Note [lower instance priority]
instance (priority := 100) ConditionallyCompleteLinearOrderBot.toOrderBot
    [h : ConditionallyCompleteLinearOrderBot α] : OrderBot α :=
  { h with }
#align conditionally_complete_linear_order_bot.to_order_bot ConditionallyCompleteLinearOrderBot.toOrderBot

-- see Note [lower instance priority]
/-- A complete lattice is a conditionally complete lattice, as there are no restrictions
on the properties of sInf and sSup in a complete lattice.-/
instance (priority := 100) CompleteLattice.toConditionallyCompleteLattice [CompleteLattice α] :
    ConditionallyCompleteLattice α :=
  { ‹CompleteLattice α› with
    le_csSup := by intros; apply le_sSup; assumption
                   -- ⊢ a✝² ≤ sSup s✝
                           -- ⊢ a✝² ∈ s✝
                                          -- 🎉 no goals
    csSup_le := by intros; apply sSup_le; assumption
                   -- ⊢ sSup s✝ ≤ a✝²
                           -- ⊢ ∀ (b : α), b ∈ s✝ → b ≤ a✝²
                                          -- 🎉 no goals
    csInf_le := by intros; apply sInf_le; assumption
                   -- ⊢ sInf s✝ ≤ a✝²
                           -- ⊢ a✝² ∈ s✝
                                          -- 🎉 no goals
    le_csInf := by intros; apply le_sInf; assumption }
                   -- ⊢ a✝² ≤ sInf s✝
                           -- ⊢ ∀ (b : α), b ∈ s✝ → a✝² ≤ b
                                          -- 🎉 no goals
#align complete_lattice.to_conditionally_complete_lattice CompleteLattice.toConditionallyCompleteLattice

-- see Note [lower instance priority]
instance (priority := 100) CompleteLinearOrder.toConditionallyCompleteLinearOrderBot {α : Type*}
    [h : CompleteLinearOrder α] : ConditionallyCompleteLinearOrderBot α :=
  { CompleteLattice.toConditionallyCompleteLattice, h with
    csSup_empty := sSup_empty
    csSup_of_not_bddAbove := fun s H ↦ (H (OrderTop.bddAbove s)).elim
    csInf_of_not_bddBelow := fun s H ↦ (H (OrderBot.bddBelow s)).elim }
#align complete_linear_order.to_conditionally_complete_linear_order_bot CompleteLinearOrder.toConditionallyCompleteLinearOrderBot

section

open Classical

/-- A well founded linear order is conditionally complete, with a bottom element. -/
@[reducible]
noncomputable def IsWellOrder.conditionallyCompleteLinearOrderBot (α : Type*)
  [i₁ : _root_.LinearOrder α] [i₂ : OrderBot α] [h : IsWellOrder α (· < ·)] :
    ConditionallyCompleteLinearOrderBot α :=
  { i₁, i₂, LinearOrder.toLattice with
    sInf := fun s => if hs : s.Nonempty then h.wf.min s hs else ⊥
    csInf_le := fun s a _ has => by
      have s_ne : s.Nonempty := ⟨a, has⟩
      -- ⊢ sInf s ≤ a
      simpa [s_ne] using not_lt.1 (h.wf.not_lt_min s s_ne has)
      -- 🎉 no goals
    le_csInf := fun s a hs has => by
      simp only [hs, dif_pos]
      -- ⊢ a ≤ WellFounded.min (_ : WellFounded fun x x_1 => x < x_1) s (_ : Set.Nonemp …
      exact has (h.wf.min_mem s hs)
      -- ⊢ a ≤ sSup s
      -- 🎉 no goals
      -- ⊢ a ≤ WellFounded.min (_ : WellFounded fun x x_1 => x < x_1) (upperBounds s) ( …
    sSup := fun s => if hs : (upperBounds s).Nonempty then h.wf.min _ hs else ⊥
      -- 🎉 no goals
    le_csSup := fun s a hs has => by
      have h's : (upperBounds s).Nonempty := hs
      -- ⊢ sSup s ≤ a
      simp only [h's, dif_pos]
      -- ⊢ WellFounded.min (_ : WellFounded fun x x_1 => x < x_1) (upperBounds s) (_ :  …
      exact h.wf.min_mem _ h's has
      -- 🎉 no goals
    csSup_le := fun s a _ has => by
      have h's : (upperBounds s).Nonempty := ⟨a, has⟩
      simp only [h's, dif_pos]
      simpa using h.wf.not_lt_min _ h's has
    csSup_empty := by simpa using eq_bot_iff.2 (not_lt.1 <| h.wf.not_lt_min _ _ <| mem_univ ⊥)
                      -- 🎉 no goals
    csSup_of_not_bddAbove := by
      -- ⊢ sSup s = sSup univ
      intro s H
      have A : ¬(BddAbove (univ : Set α)) := by
        contrapose! H; exact H.mono (subset_univ _)
      -- ⊢ sSup s = sSup univ
      have B : ¬((upperBounds s).Nonempty) := H
      -- ⊢ sSup s = sSup univ
      have C : ¬((upperBounds (univ : Set α)).Nonempty) := A
      -- 🎉 no goals
      simp [sSup, B, C]
    csInf_of_not_bddBelow := fun s H ↦ (H (OrderBot.bddBelow s)).elim }
#align is_well_order.conditionally_complete_linear_order_bot IsWellOrder.conditionallyCompleteLinearOrderBot

end

section OrderDual

instance instConditionallyCompleteLatticeOrderDual (α : Type*) [ConditionallyCompleteLattice α] :
    ConditionallyCompleteLattice αᵒᵈ :=
  { instInfOrderDual α, instSupOrderDual α, OrderDual.lattice α with
    le_csSup := @ConditionallyCompleteLattice.csInf_le α _
    csSup_le := @ConditionallyCompleteLattice.le_csInf α _
    le_csInf := @ConditionallyCompleteLattice.csSup_le α _
    csInf_le := @ConditionallyCompleteLattice.le_csSup α _ }

instance (α : Type*) [ConditionallyCompleteLinearOrder α] : ConditionallyCompleteLinearOrder αᵒᵈ :=
  { instConditionallyCompleteLatticeOrderDual α, OrderDual.instLinearOrder α with
    csSup_of_not_bddAbove := @ConditionallyCompleteLinearOrder.csInf_of_not_bddBelow α _
    csInf_of_not_bddBelow := @ConditionallyCompleteLinearOrder.csSup_of_not_bddAbove α _ }

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
#align conditionally_complete_lattice_of_Sup conditionallyCompleteLatticeOfsSup

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
#align conditionally_complete_lattice_of_Inf conditionallyCompleteLatticeOfsInf

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
#align conditionally_complete_lattice_of_lattice_of_Sup conditionallyCompleteLatticeOfLatticeOfsSup

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
#align conditionally_complete_lattice_of_lattice_of_Inf conditionallyCompleteLatticeOfLatticeOfsInf

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice α] {s t : Set α} {a b : α}

theorem le_csSup (h₁ : BddAbove s) (h₂ : a ∈ s) : a ≤ sSup s :=
  ConditionallyCompleteLattice.le_csSup s a h₁ h₂
#align le_cSup le_csSup

theorem csSup_le (h₁ : s.Nonempty) (h₂ : ∀ b ∈ s, b ≤ a) : sSup s ≤ a :=
  ConditionallyCompleteLattice.csSup_le s a h₁ h₂
#align cSup_le csSup_le

theorem csInf_le (h₁ : BddBelow s) (h₂ : a ∈ s) : sInf s ≤ a :=
  ConditionallyCompleteLattice.csInf_le s a h₁ h₂
#align cInf_le csInf_le

theorem le_csInf (h₁ : s.Nonempty) (h₂ : ∀ b ∈ s, a ≤ b) : a ≤ sInf s :=
  ConditionallyCompleteLattice.le_csInf s a h₁ h₂
#align le_cInf le_csInf

theorem le_csSup_of_le (hs : BddAbove s) (hb : b ∈ s) (h : a ≤ b) : a ≤ sSup s :=
  le_trans h (le_csSup hs hb)
#align le_cSup_of_le le_csSup_of_le

theorem csInf_le_of_le (hs : BddBelow s) (hb : b ∈ s) (h : b ≤ a) : sInf s ≤ a :=
  le_trans (csInf_le hs hb) h
#align cInf_le_of_le csInf_le_of_le

theorem csSup_le_csSup (ht : BddAbove t) (hs : s.Nonempty) (h : s ⊆ t) : sSup s ≤ sSup t :=
  csSup_le hs fun _ ha => le_csSup ht (h ha)
#align cSup_le_cSup csSup_le_csSup

theorem csInf_le_csInf (ht : BddBelow t) (hs : s.Nonempty) (h : s ⊆ t) : sInf t ≤ sInf s :=
  le_csInf hs fun _ ha => csInf_le ht (h ha)
#align cInf_le_cInf csInf_le_csInf

theorem le_csSup_iff (h : BddAbove s) (hs : s.Nonempty) :
    a ≤ sSup s ↔ ∀ b, b ∈ upperBounds s → a ≤ b :=
  ⟨fun h _ hb => le_trans h (csSup_le hs hb), fun hb => hb _ fun _ => le_csSup h⟩
#align le_cSup_iff le_csSup_iff

theorem csInf_le_iff (h : BddBelow s) (hs : s.Nonempty) : sInf s ≤ a ↔ ∀ b ∈ lowerBounds s, b ≤ a :=
  ⟨fun h _ hb => le_trans (le_csInf hs hb) h, fun hb => hb _ fun _ => csInf_le h⟩
#align cInf_le_iff csInf_le_iff

theorem isLUB_csSup (ne : s.Nonempty) (H : BddAbove s) : IsLUB s (sSup s) :=
  ⟨fun _ => le_csSup H, fun _ => csSup_le ne⟩
#align is_lub_cSup isLUB_csSup

theorem isLUB_ciSup [Nonempty ι] {f : ι → α} (H : BddAbove (range f)) :
    IsLUB (range f) (⨆ i, f i) :=
  isLUB_csSup (range_nonempty f) H
#align is_lub_csupr isLUB_ciSup

theorem isLUB_ciSup_set {f : β → α} {s : Set β} (H : BddAbove (f '' s)) (Hne : s.Nonempty) :
    IsLUB (f '' s) (⨆ i : s, f i) := by
  rw [← sSup_image']
  -- ⊢ IsLUB (f '' s) (sSup (f '' s))
  exact isLUB_csSup (Hne.image _) H
  -- 🎉 no goals
#align is_lub_csupr_set isLUB_ciSup_set

theorem isGLB_csInf (ne : s.Nonempty) (H : BddBelow s) : IsGLB s (sInf s) :=
  ⟨fun _ => csInf_le H, fun _ => le_csInf ne⟩
#align is_glb_cInf isGLB_csInf

theorem isGLB_ciInf [Nonempty ι] {f : ι → α} (H : BddBelow (range f)) :
    IsGLB (range f) (⨅ i, f i) :=
  isGLB_csInf (range_nonempty f) H
#align is_glb_cinfi isGLB_ciInf

theorem isGLB_ciInf_set {f : β → α} {s : Set β} (H : BddBelow (f '' s)) (Hne : s.Nonempty) :
    IsGLB (f '' s) (⨅ i : s, f i) :=
  @isLUB_ciSup_set αᵒᵈ _ _ _ _ H Hne
#align is_glb_cinfi_set isGLB_ciInf_set

theorem ciSup_le_iff [Nonempty ι] {f : ι → α} {a : α} (hf : BddAbove (range f)) :
    iSup f ≤ a ↔ ∀ i, f i ≤ a :=
  (isLUB_le_iff <| isLUB_ciSup hf).trans forall_range_iff
#align csupr_le_iff ciSup_le_iff

theorem le_ciInf_iff [Nonempty ι] {f : ι → α} {a : α} (hf : BddBelow (range f)) :
    a ≤ iInf f ↔ ∀ i, a ≤ f i :=
  (le_isGLB_iff <| isGLB_ciInf hf).trans forall_range_iff
#align le_cinfi_iff le_ciInf_iff

theorem ciSup_set_le_iff {ι : Type*} {s : Set ι} {f : ι → α} {a : α} (hs : s.Nonempty)
    (hf : BddAbove (f '' s)) : ⨆ i : s, f i ≤ a ↔ ∀ i ∈ s, f i ≤ a :=
  (isLUB_le_iff <| isLUB_ciSup_set hf hs).trans ball_image_iff
#align csupr_set_le_iff ciSup_set_le_iff

theorem le_ciInf_set_iff {ι : Type*} {s : Set ι} {f : ι → α} {a : α} (hs : s.Nonempty)
    (hf : BddBelow (f '' s)) : (a ≤ ⨅ i : s, f i) ↔ ∀ i ∈ s, a ≤ f i :=
  (le_isGLB_iff <| isGLB_ciInf_set hf hs).trans ball_image_iff
#align le_cinfi_set_iff le_ciInf_set_iff

theorem IsLUB.csSup_eq (H : IsLUB s a) (ne : s.Nonempty) : sSup s = a :=
  (isLUB_csSup ne ⟨a, H.1⟩).unique H
#align is_lub.cSup_eq IsLUB.csSup_eq

theorem IsLUB.ciSup_eq [Nonempty ι] {f : ι → α} (H : IsLUB (range f) a) : ⨆ i, f i = a :=
  H.csSup_eq (range_nonempty f)
#align is_lub.csupr_eq IsLUB.ciSup_eq

theorem IsLUB.ciSup_set_eq {s : Set β} {f : β → α} (H : IsLUB (f '' s) a) (Hne : s.Nonempty) :
    ⨆ i : s, f i = a :=
  IsLUB.csSup_eq (image_eq_range f s ▸ H) (image_eq_range f s ▸ Hne.image f)
#align is_lub.csupr_set_eq IsLUB.ciSup_set_eq

/-- A greatest element of a set is the supremum of this set. -/
theorem IsGreatest.csSup_eq (H : IsGreatest s a) : sSup s = a :=
  H.isLUB.csSup_eq H.nonempty
#align is_greatest.cSup_eq IsGreatest.csSup_eq

theorem IsGreatest.csSup_mem (H : IsGreatest s a) : sSup s ∈ s :=
  H.csSup_eq.symm ▸ H.1
#align is_greatest.Sup_mem IsGreatest.csSup_mem

theorem IsGLB.csInf_eq (H : IsGLB s a) (ne : s.Nonempty) : sInf s = a :=
  (isGLB_csInf ne ⟨a, H.1⟩).unique H
#align is_glb.cInf_eq IsGLB.csInf_eq

theorem IsGLB.ciInf_eq [Nonempty ι] {f : ι → α} (H : IsGLB (range f) a) : ⨅ i, f i = a :=
  H.csInf_eq (range_nonempty f)
#align is_glb.cinfi_eq IsGLB.ciInf_eq

theorem IsGLB.ciInf_set_eq {s : Set β} {f : β → α} (H : IsGLB (f '' s) a) (Hne : s.Nonempty) :
    ⨅ i : s, f i = a :=
  IsGLB.csInf_eq (image_eq_range f s ▸ H) (image_eq_range f s ▸ Hne.image f)
#align is_glb.cinfi_set_eq IsGLB.ciInf_set_eq

/-- A least element of a set is the infimum of this set. -/
theorem IsLeast.csInf_eq (H : IsLeast s a) : sInf s = a :=
  H.isGLB.csInf_eq H.nonempty
#align is_least.cInf_eq IsLeast.csInf_eq

theorem IsLeast.csInf_mem (H : IsLeast s a) : sInf s ∈ s :=
  H.csInf_eq.symm ▸ H.1
#align is_least.Inf_mem IsLeast.csInf_mem

theorem subset_Icc_csInf_csSup (hb : BddBelow s) (ha : BddAbove s) : s ⊆ Icc (sInf s) (sSup s) :=
  fun _ hx => ⟨csInf_le hb hx, le_csSup ha hx⟩
#align subset_Icc_cInf_cSup subset_Icc_csInf_csSup

theorem csSup_le_iff (hb : BddAbove s) (hs : s.Nonempty) : sSup s ≤ a ↔ ∀ b ∈ s, b ≤ a :=
  isLUB_le_iff (isLUB_csSup hs hb)
#align cSup_le_iff csSup_le_iff

theorem le_csInf_iff (hb : BddBelow s) (hs : s.Nonempty) : a ≤ sInf s ↔ ∀ b ∈ s, a ≤ b :=
  le_isGLB_iff (isGLB_csInf hs hb)
#align le_cInf_iff le_csInf_iff

theorem csSup_lower_bounds_eq_csInf {s : Set α} (h : BddBelow s) (hs : s.Nonempty) :
    sSup (lowerBounds s) = sInf s :=
  (isLUB_csSup h <| hs.mono fun _ hx _ hy => hy hx).unique (isGLB_csInf hs h).isLUB
#align cSup_lower_bounds_eq_cInf csSup_lower_bounds_eq_csInf

theorem csInf_upper_bounds_eq_csSup {s : Set α} (h : BddAbove s) (hs : s.Nonempty) :
    sInf (upperBounds s) = sSup s :=
  (isGLB_csInf h <| hs.mono fun _ hx _ hy => hy hx).unique (isLUB_csSup hs h).isGLB
#align cInf_upper_bounds_eq_cSup csInf_upper_bounds_eq_csSup

theorem not_mem_of_lt_csInf {x : α} {s : Set α} (h : x < sInf s) (hs : BddBelow s) : x ∉ s :=
  fun hx => lt_irrefl _ (h.trans_le (csInf_le hs hx))
#align not_mem_of_lt_cInf not_mem_of_lt_csInf

theorem not_mem_of_csSup_lt {x : α} {s : Set α} (h : sSup s < x) (hs : BddAbove s) : x ∉ s :=
  @not_mem_of_lt_csInf αᵒᵈ _ x s h hs
#align not_mem_of_cSup_lt not_mem_of_csSup_lt

/-- Introduction rule to prove that `b` is the supremum of `s`: it suffices to check that `b`
is larger than all elements of `s`, and that this is not the case of any `w<b`.
See `sSup_eq_of_forall_le_of_forall_lt_exists_gt` for a version in complete lattices. -/
theorem csSup_eq_of_forall_le_of_forall_lt_exists_gt (hs : s.Nonempty) (H : ∀ a ∈ s, a ≤ b)
    (H' : ∀ w, w < b → ∃ a ∈ s, w < a) : sSup s = b :=
  (eq_of_le_of_not_lt (csSup_le hs H)) fun hb =>
    let ⟨_, ha, ha'⟩ := H' _ hb
    lt_irrefl _ <| ha'.trans_le <| le_csSup ⟨b, H⟩ ha
#align cSup_eq_of_forall_le_of_forall_lt_exists_gt csSup_eq_of_forall_le_of_forall_lt_exists_gt

/-- Introduction rule to prove that `b` is the infimum of `s`: it suffices to check that `b`
is smaller than all elements of `s`, and that this is not the case of any `w>b`.
See `sInf_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in complete lattices. -/
theorem csInf_eq_of_forall_ge_of_forall_gt_exists_lt :
    s.Nonempty → (∀ a ∈ s, b ≤ a) → (∀ w, b < w → ∃ a ∈ s, a < w) → sInf s = b :=
  @csSup_eq_of_forall_le_of_forall_lt_exists_gt αᵒᵈ _ _ _
#align cInf_eq_of_forall_ge_of_forall_gt_exists_lt csInf_eq_of_forall_ge_of_forall_gt_exists_lt

/-- `b < sSup s` when there is an element `a` in `s` with `b < a`, when `s` is bounded above.
This is essentially an iff, except that the assumptions for the two implications are
slightly different (one needs boundedness above for one direction, nonemptiness and linear
order for the other one), so we formulate separately the two implications, contrary to
the `CompleteLattice` case.-/
theorem lt_csSup_of_lt (hs : BddAbove s) (ha : a ∈ s) (h : b < a) : b < sSup s :=
  lt_of_lt_of_le h (le_csSup hs ha)
#align lt_cSup_of_lt lt_csSup_of_lt

/-- `sInf s < b` when there is an element `a` in `s` with `a < b`, when `s` is bounded below.
This is essentially an iff, except that the assumptions for the two implications are
slightly different (one needs boundedness below for one direction, nonemptiness and linear
order for the other one), so we formulate separately the two implications, contrary to
the `CompleteLattice` case.-/
theorem csInf_lt_of_lt : BddBelow s → a ∈ s → a < b → sInf s < b :=
  @lt_csSup_of_lt αᵒᵈ _ _ _ _
#align cInf_lt_of_lt csInf_lt_of_lt

/-- If all elements of a nonempty set `s` are less than or equal to all elements
of a nonempty set `t`, then there exists an element between these sets. -/
theorem exists_between_of_forall_le (sne : s.Nonempty) (tne : t.Nonempty)
    (hst : ∀ x ∈ s, ∀ y ∈ t, x ≤ y) : (upperBounds s ∩ lowerBounds t).Nonempty :=
  ⟨sInf t, fun x hx => le_csInf tne <| hst x hx, fun _ hy => csInf_le (sne.mono hst) hy⟩
#align exists_between_of_forall_le exists_between_of_forall_le

/-- The supremum of a singleton is the element of the singleton-/
@[simp]
theorem csSup_singleton (a : α) : sSup {a} = a :=
  isGreatest_singleton.csSup_eq
#align cSup_singleton csSup_singleton

/-- The infimum of a singleton is the element of the singleton-/
@[simp]
theorem csInf_singleton (a : α) : sInf {a} = a :=
  isLeast_singleton.csInf_eq
#align cInf_singleton csInf_singleton

@[simp]
theorem csSup_pair (a b : α) : sSup {a, b} = a ⊔ b :=
  (@isLUB_pair _ _ a b).csSup_eq (insert_nonempty _ _)
#align cSup_pair csSup_pair

@[simp]
theorem csInf_pair (a b : α) : sInf {a, b} = a ⊓ b :=
  (@isGLB_pair _ _ a b).csInf_eq (insert_nonempty _ _)
#align cInf_pair csInf_pair

/-- If a set is bounded below and above, and nonempty, its infimum is less than or equal to
its supremum.-/
theorem csInf_le_csSup (hb : BddBelow s) (ha : BddAbove s) (ne : s.Nonempty) : sInf s ≤ sSup s :=
  isGLB_le_isLUB (isGLB_csInf ne hb) (isLUB_csSup ne ha) ne
#align cInf_le_cSup csInf_le_csSup

/-- The `sSup` of a union of two sets is the max of the suprema of each subset, under the
assumptions that all sets are bounded above and nonempty.-/
theorem csSup_union (hs : BddAbove s) (sne : s.Nonempty) (ht : BddAbove t) (tne : t.Nonempty) :
    sSup (s ∪ t) = sSup s ⊔ sSup t :=
  ((isLUB_csSup sne hs).union (isLUB_csSup tne ht)).csSup_eq sne.inl
#align cSup_union csSup_union

/-- The `sInf` of a union of two sets is the min of the infima of each subset, under the assumptions
that all sets are bounded below and nonempty.-/
theorem csInf_union (hs : BddBelow s) (sne : s.Nonempty) (ht : BddBelow t) (tne : t.Nonempty) :
    sInf (s ∪ t) = sInf s ⊓ sInf t :=
  @csSup_union αᵒᵈ _ _ _ hs sne ht tne
#align cInf_union csInf_union

/-- The supremum of an intersection of two sets is bounded by the minimum of the suprema of each
set, if all sets are bounded above and nonempty.-/
theorem csSup_inter_le (hs : BddAbove s) (ht : BddAbove t) (hst : (s ∩ t).Nonempty) :
    sSup (s ∩ t) ≤ sSup s ⊓ sSup t :=
  (csSup_le hst) fun _ hx => le_inf (le_csSup hs hx.1) (le_csSup ht hx.2)
#align cSup_inter_le csSup_inter_le

/-- The infimum of an intersection of two sets is bounded below by the maximum of the
infima of each set, if all sets are bounded below and nonempty.-/
theorem le_csInf_inter :
    BddBelow s → BddBelow t → (s ∩ t).Nonempty → sInf s ⊔ sInf t ≤ sInf (s ∩ t) :=
  @csSup_inter_le αᵒᵈ _ _ _
#align le_cInf_inter le_csInf_inter

/-- The supremum of `insert a s` is the maximum of `a` and the supremum of `s`, if `s` is
nonempty and bounded above.-/
theorem csSup_insert (hs : BddAbove s) (sne : s.Nonempty) : sSup (insert a s) = a ⊔ sSup s :=
  ((isLUB_csSup sne hs).insert a).csSup_eq (insert_nonempty a s)
#align cSup_insert csSup_insert

/-- The infimum of `insert a s` is the minimum of `a` and the infimum of `s`, if `s` is
nonempty and bounded below.-/
theorem csInf_insert (hs : BddBelow s) (sne : s.Nonempty) : sInf (insert a s) = a ⊓ sInf s :=
  @csSup_insert αᵒᵈ _ _ _ hs sne
#align cInf_insert csInf_insert

@[simp]
theorem csInf_Icc (h : a ≤ b) : sInf (Icc a b) = a :=
  (isGLB_Icc h).csInf_eq (nonempty_Icc.2 h)
#align cInf_Icc csInf_Icc

@[simp]
theorem csInf_Ici : sInf (Ici a) = a :=
  isLeast_Ici.csInf_eq
#align cInf_Ici csInf_Ici

@[simp]
theorem csInf_Ico (h : a < b) : sInf (Ico a b) = a :=
  (isGLB_Ico h).csInf_eq (nonempty_Ico.2 h)
#align cInf_Ico csInf_Ico

@[simp]
theorem csInf_Ioc [DenselyOrdered α] (h : a < b) : sInf (Ioc a b) = a :=
  (isGLB_Ioc h).csInf_eq (nonempty_Ioc.2 h)
#align cInf_Ioc csInf_Ioc

@[simp]
theorem csInf_Ioi [NoMaxOrder α] [DenselyOrdered α] : sInf (Ioi a) = a :=
  csInf_eq_of_forall_ge_of_forall_gt_exists_lt nonempty_Ioi (fun _ => le_of_lt) fun w hw => by
    simpa using exists_between hw
    -- 🎉 no goals
#align cInf_Ioi csInf_Ioi

@[simp]
theorem csInf_Ioo [DenselyOrdered α] (h : a < b) : sInf (Ioo a b) = a :=
  (isGLB_Ioo h).csInf_eq (nonempty_Ioo.2 h)
#align cInf_Ioo csInf_Ioo

@[simp]
theorem csSup_Icc (h : a ≤ b) : sSup (Icc a b) = b :=
  (isLUB_Icc h).csSup_eq (nonempty_Icc.2 h)
#align cSup_Icc csSup_Icc

@[simp]
theorem csSup_Ico [DenselyOrdered α] (h : a < b) : sSup (Ico a b) = b :=
  (isLUB_Ico h).csSup_eq (nonempty_Ico.2 h)
#align cSup_Ico csSup_Ico

@[simp]
theorem csSup_Iic : sSup (Iic a) = a :=
  isGreatest_Iic.csSup_eq
#align cSup_Iic csSup_Iic

@[simp]
theorem csSup_Iio [NoMinOrder α] [DenselyOrdered α] : sSup (Iio a) = a :=
  csSup_eq_of_forall_le_of_forall_lt_exists_gt nonempty_Iio (fun _ => le_of_lt) fun w hw => by
    simpa [and_comm] using exists_between hw
    -- 🎉 no goals
#align cSup_Iio csSup_Iio

@[simp]
theorem csSup_Ioc (h : a < b) : sSup (Ioc a b) = b :=
  (isLUB_Ioc h).csSup_eq (nonempty_Ioc.2 h)
#align cSup_Ioc csSup_Ioc

@[simp]
theorem csSup_Ioo [DenselyOrdered α] (h : a < b) : sSup (Ioo a b) = b :=
  (isLUB_Ioo h).csSup_eq (nonempty_Ioo.2 h)
#align cSup_Ioo csSup_Ioo

/-- The indexed supremum of a function is bounded above by a uniform bound-/
theorem ciSup_le [Nonempty ι] {f : ι → α} {c : α} (H : ∀ x, f x ≤ c) : iSup f ≤ c :=
  csSup_le (range_nonempty f) (by rwa [forall_range_iff])
                                  -- 🎉 no goals
#align csupr_le ciSup_le

/-- The indexed supremum of a function is bounded below by the value taken at one point-/
theorem le_ciSup {f : ι → α} (H : BddAbove (range f)) (c : ι) : f c ≤ iSup f :=
  le_csSup H (mem_range_self _)
#align le_csupr le_ciSup

theorem le_ciSup_of_le {f : ι → α} (H : BddAbove (range f)) (c : ι) (h : a ≤ f c) : a ≤ iSup f :=
  le_trans h (le_ciSup H c)
#align le_csupr_of_le le_ciSup_of_le

/-- The indexed supremum of two functions are comparable if the functions are pointwise comparable-/
theorem ciSup_mono {f g : ι → α} (B : BddAbove (range g)) (H : ∀ x, f x ≤ g x) :
    iSup f ≤ iSup g := by
  cases isEmpty_or_nonempty ι
  -- ⊢ iSup f ≤ iSup g
  · rw [iSup_of_empty', iSup_of_empty']
    -- 🎉 no goals
  · exact ciSup_le fun x => le_ciSup_of_le B x (H x)
    -- 🎉 no goals
#align csupr_mono ciSup_mono

theorem le_ciSup_set {f : β → α} {s : Set β} (H : BddAbove (f '' s)) {c : β} (hc : c ∈ s) :
    f c ≤ ⨆ i : s, f i :=
  (le_csSup H <| mem_image_of_mem f hc).trans_eq sSup_image'
#align le_csupr_set le_ciSup_set

/-- The indexed infimum of two functions are comparable if the functions are pointwise comparable-/
theorem ciInf_mono {f g : ι → α} (B : BddBelow (range f)) (H : ∀ x, f x ≤ g x) : iInf f ≤ iInf g :=
  @ciSup_mono αᵒᵈ _ _ _ _ B H
#align cinfi_mono ciInf_mono

/-- The indexed minimum of a function is bounded below by a uniform lower bound-/
theorem le_ciInf [Nonempty ι] {f : ι → α} {c : α} (H : ∀ x, c ≤ f x) : c ≤ iInf f :=
  @ciSup_le αᵒᵈ _ _ _ _ _ H
#align le_cinfi le_ciInf

/-- The indexed infimum of a function is bounded above by the value taken at one point-/
theorem ciInf_le {f : ι → α} (H : BddBelow (range f)) (c : ι) : iInf f ≤ f c :=
  @le_ciSup αᵒᵈ _ _ _ H c
#align cinfi_le ciInf_le

theorem ciInf_le_of_le {f : ι → α} (H : BddBelow (range f)) (c : ι) (h : f c ≤ a) : iInf f ≤ a :=
  @le_ciSup_of_le αᵒᵈ _ _ _ _ H c h
#align cinfi_le_of_le ciInf_le_of_le

theorem ciInf_set_le {f : β → α} {s : Set β} (H : BddBelow (f '' s)) {c : β} (hc : c ∈ s) :
    ⨅ i : s, f i ≤ f c :=
  @le_ciSup_set αᵒᵈ _ _ _ _ H _ hc
#align cinfi_set_le ciInf_set_le

@[simp]
theorem ciSup_const [hι : Nonempty ι] {a : α} : ⨆ _ : ι, a = a := by
  rw [iSup, range_const, csSup_singleton]
  -- 🎉 no goals
#align csupr_const ciSup_const

@[simp]
theorem ciInf_const [Nonempty ι] {a : α} : ⨅ _ : ι, a = a :=
  @ciSup_const αᵒᵈ _ _ _ _
#align cinfi_const ciInf_const

@[simp]
theorem ciSup_unique [Unique ι] {s : ι → α} : ⨆ i, s i = s default := by
  have : ∀ i, s i = s default := fun i => congr_arg s (Unique.eq_default i)
  -- ⊢ ⨆ (i : ι), s i = s default
  simp only [this, ciSup_const]
  -- 🎉 no goals
#align supr_unique ciSup_unique

@[simp]
theorem ciInf_unique [Unique ι] {s : ι → α} : ⨅ i, s i = s default :=
  @ciSup_unique αᵒᵈ _ _ _ _
#align infi_unique ciInf_unique

-- porting note: new lemma
theorem ciSup_subsingleton [Subsingleton ι] (i : ι) (s : ι → α) : ⨆ i, s i = s i :=
  @ciSup_unique α ι _ ⟨⟨i⟩, fun j => Subsingleton.elim j i⟩ _

-- porting note: new lemma
theorem ciInf_subsingleton [Subsingleton ι] (i : ι) (s : ι → α) : ⨅ i, s i = s i :=
  @ciInf_unique α ι _ ⟨⟨i⟩, fun j => Subsingleton.elim j i⟩ _

@[simp]
theorem ciSup_pos {p : Prop} {f : p → α} (hp : p) : ⨆ h : p, f h = f hp :=
  ciSup_subsingleton hp f
#align csupr_pos ciSup_pos

@[simp]
theorem ciInf_pos {p : Prop} {f : p → α} (hp : p) : ⨅ h : p, f h = f hp :=
  @ciSup_pos αᵒᵈ _ _ _ hp
#align cinfi_pos ciInf_pos

/-- Introduction rule to prove that `b` is the supremum of `f`: it suffices to check that `b`
is larger than `f i` for all `i`, and that this is not the case of any `w<b`.
See `iSup_eq_of_forall_le_of_forall_lt_exists_gt` for a version in complete lattices. -/
theorem ciSup_eq_of_forall_le_of_forall_lt_exists_gt [Nonempty ι] {f : ι → α} (h₁ : ∀ i, f i ≤ b)
    (h₂ : ∀ w, w < b → ∃ i, w < f i) : ⨆ i : ι, f i = b :=
  csSup_eq_of_forall_le_of_forall_lt_exists_gt (range_nonempty f) (forall_range_iff.mpr h₁)
    fun w hw => exists_range_iff.mpr <| h₂ w hw
#align csupr_eq_of_forall_le_of_forall_lt_exists_gt ciSup_eq_of_forall_le_of_forall_lt_exists_gt

-- Porting note: in mathlib3 `by exact` is not needed
/-- Introduction rule to prove that `b` is the infimum of `f`: it suffices to check that `b`
is smaller than `f i` for all `i`, and that this is not the case of any `w>b`.
See `iInf_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in complete lattices. -/
theorem ciInf_eq_of_forall_ge_of_forall_gt_exists_lt [Nonempty ι] {f : ι → α} (h₁ : ∀ i, b ≤ f i)
    (h₂ : ∀ w, b < w → ∃ i, f i < w) : ⨅ i : ι, f i = b := by
  exact @ciSup_eq_of_forall_le_of_forall_lt_exists_gt αᵒᵈ _ _ _ _ ‹_› ‹_› ‹_›
  -- 🎉 no goals
#align cinfi_eq_of_forall_ge_of_forall_gt_exists_lt ciInf_eq_of_forall_ge_of_forall_gt_exists_lt

/-- Nested intervals lemma: if `f` is a monotone sequence, `g` is an antitone sequence, and
`f n ≤ g n` for all `n`, then `⨆ n, f n` belongs to all the intervals `[f n, g n]`. -/
theorem Monotone.ciSup_mem_Inter_Icc_of_antitone [SemilatticeSup β] {f g : β → α} (hf : Monotone f)
    (hg : Antitone g) (h : f ≤ g) : (⨆ n, f n) ∈ ⋂ n, Icc (f n) (g n) := by
  refine' mem_iInter.2 fun n => _
  -- ⊢ ⨆ (n : β), f n ∈ Icc (f n) (g n)
  haveI : Nonempty β := ⟨n⟩
  -- ⊢ ⨆ (n : β), f n ∈ Icc (f n) (g n)
  have : ∀ m, f m ≤ g n := fun m => hf.forall_le_of_antitone hg h m n
  -- ⊢ ⨆ (n : β), f n ∈ Icc (f n) (g n)
  exact ⟨le_ciSup ⟨g <| n, forall_range_iff.2 this⟩ _, ciSup_le this⟩
  -- 🎉 no goals
#align monotone.csupr_mem_Inter_Icc_of_antitone Monotone.ciSup_mem_Inter_Icc_of_antitone

/-- Nested intervals lemma: if `[f n, g n]` is an antitone sequence of nonempty
closed intervals, then `⨆ n, f n` belongs to all the intervals `[f n, g n]`. -/
theorem ciSup_mem_Inter_Icc_of_antitone_Icc [SemilatticeSup β] {f g : β → α}
    (h : Antitone fun n => Icc (f n) (g n)) (h' : ∀ n, f n ≤ g n) :
    (⨆ n, f n) ∈ ⋂ n, Icc (f n) (g n) :=
  Monotone.ciSup_mem_Inter_Icc_of_antitone
    (fun _ n hmn => ((Icc_subset_Icc_iff (h' n)).1 (h hmn)).1)
    (fun _ n hmn => ((Icc_subset_Icc_iff (h' n)).1 (h hmn)).2) h'
#align csupr_mem_Inter_Icc_of_antitone_Icc ciSup_mem_Inter_Icc_of_antitone_Icc

/-- Introduction rule to prove that `b` is the supremum of `s`: it suffices to check that
1) `b` is an upper bound
2) every other upper bound `b'` satisfies `b ≤ b'`.-/
theorem csSup_eq_of_is_forall_le_of_forall_le_imp_ge (hs : s.Nonempty) (h_is_ub : ∀ a ∈ s, a ≤ b)
    (h_b_le_ub : ∀ ub, (∀ a ∈ s, a ≤ ub) → b ≤ ub) : sSup s = b :=
  (csSup_le hs h_is_ub).antisymm ((h_b_le_ub _) fun _ => le_csSup ⟨b, h_is_ub⟩)
#align cSup_eq_of_is_forall_le_of_forall_le_imp_ge csSup_eq_of_is_forall_le_of_forall_le_imp_ge

end ConditionallyCompleteLattice

instance Pi.conditionallyCompleteLattice {ι : Type*} {α : ∀ _i : ι, Type*}
    [∀ i, ConditionallyCompleteLattice (α i)] : ConditionallyCompleteLattice (∀ i, α i) :=
  { Pi.lattice, Pi.supSet, Pi.infSet with
    le_csSup := fun s f ⟨g, hg⟩ hf i =>
      le_csSup ⟨g i, Set.forall_range_iff.2 fun ⟨f', hf'⟩ => hg hf' i⟩ ⟨⟨f, hf⟩, rfl⟩
    csSup_le := fun s f hs hf i =>
      (csSup_le (by haveI := hs.to_subtype; apply range_nonempty)) fun b ⟨⟨g, hg⟩, hb⟩ =>
                    -- ⊢ Set.Nonempty (range fun f => ↑f i)
                                            -- 🎉 no goals
        hb ▸ hf hg i
    csInf_le := fun s f ⟨g, hg⟩ hf i =>
      csInf_le ⟨g i, Set.forall_range_iff.2 fun ⟨f', hf'⟩ => hg hf' i⟩ ⟨⟨f, hf⟩, rfl⟩
    le_csInf := fun s f hs hf i =>
      (le_csInf (by haveI := hs.to_subtype; apply range_nonempty)) fun b ⟨⟨g, hg⟩, hb⟩ =>
                    -- ⊢ Set.Nonempty (range fun f => ↑f i)
                                            -- 🎉 no goals
        hb ▸ hf hg i }
#align pi.conditionally_complete_lattice Pi.conditionallyCompleteLattice

section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder α] {s t : Set α} {a b : α}

/-- When `b < sSup s`, there is an element `a` in `s` with `b < a`, if `s` is nonempty and the order
is a linear order. -/
theorem exists_lt_of_lt_csSup (hs : s.Nonempty) (hb : b < sSup s) : ∃ a ∈ s, b < a := by
  contrapose! hb
  -- ⊢ sSup s ≤ b
  exact csSup_le hs hb
  -- 🎉 no goals
#align exists_lt_of_lt_cSup exists_lt_of_lt_csSup

/-- Indexed version of the above lemma `exists_lt_of_lt_csSup`.
When `b < iSup f`, there is an element `i` such that `b < f i`.
-/
theorem exists_lt_of_lt_ciSup [Nonempty ι] {f : ι → α} (h : b < iSup f) : ∃ i, b < f i :=
  let ⟨_, ⟨i, rfl⟩, h⟩ := exists_lt_of_lt_csSup (range_nonempty f) h
  ⟨i, h⟩
#align exists_lt_of_lt_csupr exists_lt_of_lt_ciSup

/-- When `sInf s < b`, there is an element `a` in `s` with `a < b`, if `s` is nonempty and the order
is a linear order.-/
theorem exists_lt_of_csInf_lt (hs : s.Nonempty) (hb : sInf s < b) : ∃ a ∈ s, a < b :=
  @exists_lt_of_lt_csSup αᵒᵈ _ _ _ hs hb
#align exists_lt_of_cInf_lt exists_lt_of_csInf_lt

/-- Indexed version of the above lemma `exists_lt_of_csInf_lt`
When `iInf f < a`, there is an element `i` such that `f i < a`.
-/
theorem exists_lt_of_ciInf_lt [Nonempty ι] {f : ι → α} (h : iInf f < a) : ∃ i, f i < a :=
  @exists_lt_of_lt_ciSup αᵒᵈ _ _ _ _ _ h
#align exists_lt_of_cinfi_lt exists_lt_of_ciInf_lt

theorem csSup_of_not_bddAbove {s : Set α} (hs : ¬BddAbove s) : sSup s = sSup univ :=
  ConditionallyCompleteLinearOrder.csSup_of_not_bddAbove s hs

theorem csInf_of_not_bddBelow {s : Set α} (hs : ¬BddBelow s) : sInf s = sInf univ :=
  ConditionallyCompleteLinearOrder.csInf_of_not_bddBelow s hs

/-- When every element of a set `s` is bounded by an element of a set `t`, and conversely, then
`s` and `t` have the same supremum. This holds even when the sets may be empty or unbounded. -/
theorem csSup_eq_csSup_of_forall_exists_le {s t : Set α}
    (hs : ∀ x ∈ s, ∃ y ∈ t, x ≤ y) (ht : ∀ y ∈ t, ∃ x ∈ s, y ≤ x) :
    sSup s = sSup t := by
  rcases eq_empty_or_nonempty s with rfl|s_ne
  -- ⊢ sSup ∅ = sSup t
  · have : t = ∅ := eq_empty_of_forall_not_mem (fun y yt ↦ by simpa using ht y yt)
    -- ⊢ sSup ∅ = sSup t
    rw [this]
    -- 🎉 no goals
  rcases eq_empty_or_nonempty t with rfl|t_ne
  -- ⊢ sSup s = sSup ∅
  · have : s = ∅ := eq_empty_of_forall_not_mem (fun x xs ↦ by simpa using hs x xs)
    -- ⊢ sSup s = sSup ∅
    rw [this]
    -- 🎉 no goals
  by_cases B : BddAbove s ∨ BddAbove t
  -- ⊢ sSup s = sSup t
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
    -- ⊢ sSup s ≤ sSup t
    · apply csSup_le s_ne (fun x hx ↦ ?_)
      -- ⊢ x ≤ sSup t
      rcases hs x hx with ⟨y, yt, hxy⟩
      -- ⊢ x ≤ sSup t
      exact hxy.trans (le_csSup Bt yt)
      -- 🎉 no goals
    · apply csSup_le t_ne (fun y hy ↦ ?_)
      -- ⊢ y ≤ sSup s
      rcases ht y hy with ⟨x, xs, hyx⟩
      -- ⊢ y ≤ sSup s
      exact hyx.trans (le_csSup Bs xs)
      -- 🎉 no goals
  · simp [csSup_of_not_bddAbove, (not_or.1 B).1, (not_or.1 B).2]
    -- 🎉 no goals

/-- When every element of a set `s` is bounded by an element of a set `t`, and conversely, then
`s` and `t` have the same supremum. This holds even when the sets may be empty or unbounded. -/
theorem csInf_eq_csInf_of_forall_exists_le {s t : Set α}
    (hs : ∀ x ∈ s, ∃ y ∈ t, y ≤ x) (ht : ∀ y ∈ t, ∃ x ∈ s, x ≤ y) :
    sInf s = sInf t :=
  @csSup_eq_csSup_of_forall_exists_le αᵒᵈ _ s t hs ht

open Function

variable [IsWellOrder α (· < ·)]

theorem sInf_eq_argmin_on (hs : s.Nonempty) :
    sInf s = argminOn id (@IsWellFounded.wf α (· < ·) _) s hs :=
  IsLeast.csInf_eq ⟨argminOn_mem _ _ _ _, fun _ ha => argminOn_le id _ _ ha⟩
#align Inf_eq_argmin_on sInf_eq_argmin_on

theorem isLeast_csInf (hs : s.Nonempty) : IsLeast s (sInf s) := by
  rw [sInf_eq_argmin_on hs]
  -- ⊢ IsLeast s (argminOn id (_ : WellFounded fun x x_1 => x < x_1) s hs)
  exact ⟨argminOn_mem _ _ _ _, fun a ha => argminOn_le id _ _ ha⟩
  -- 🎉 no goals
#align is_least_Inf isLeast_csInf

theorem le_csInf_iff' (hs : s.Nonempty) : b ≤ sInf s ↔ b ∈ lowerBounds s :=
  le_isGLB_iff (isLeast_csInf hs).isGLB
#align le_cInf_iff' le_csInf_iff'

theorem csInf_mem (hs : s.Nonempty) : sInf s ∈ s :=
  (isLeast_csInf hs).1
#align Inf_mem csInf_mem

theorem ciInf_mem [Nonempty ι] (f : ι → α) : iInf f ∈ range f :=
  csInf_mem (range_nonempty f)
#align infi_mem ciInf_mem

theorem MonotoneOn.map_csInf {β : Type*} [ConditionallyCompleteLattice β] {f : α → β}
    (hf : MonotoneOn f s) (hs : s.Nonempty) : f (sInf s) = sInf (f '' s) :=
  (hf.map_isLeast (isLeast_csInf hs)).csInf_eq.symm
#align monotone_on.map_Inf MonotoneOn.map_csInf

theorem Monotone.map_csInf {β : Type*} [ConditionallyCompleteLattice β] {f : α → β}
    (hf : Monotone f) (hs : s.Nonempty) : f (sInf s) = sInf (f '' s) :=
  (hf.map_isLeast (isLeast_csInf hs)).csInf_eq.symm
#align monotone.map_Inf Monotone.map_csInf

end ConditionallyCompleteLinearOrder

/-!
### Lemmas about a conditionally complete linear order with bottom element

In this case we have `Sup ∅ = ⊥`, so we can drop some `Nonempty`/`Set.Nonempty` assumptions.
-/


section ConditionallyCompleteLinearOrderBot

variable [ConditionallyCompleteLinearOrderBot α]

@[simp]
theorem csSup_empty : (sSup ∅ : α) = ⊥ :=
  ConditionallyCompleteLinearOrderBot.csSup_empty
#align cSup_empty csSup_empty

@[simp]
theorem ciSup_of_empty [IsEmpty ι] (f : ι → α) : ⨆ i, f i = ⊥ := by
  rw [iSup_of_empty', csSup_empty]
  -- 🎉 no goals
#align csupr_of_empty ciSup_of_empty

theorem ciSup_false (f : False → α) : ⨆ i, f i = ⊥ :=
  ciSup_of_empty f
#align csupr_false ciSup_false

@[simp]
theorem csInf_univ : sInf (univ : Set α) = ⊥ :=
  isLeast_univ.csInf_eq
#align cInf_univ csInf_univ

theorem isLUB_csSup' {s : Set α} (hs : BddAbove s) : IsLUB s (sSup s) := by
  rcases eq_empty_or_nonempty s with (rfl | hne)
  -- ⊢ IsLUB ∅ (sSup ∅)
  · simp only [csSup_empty, isLUB_empty]
    -- 🎉 no goals
  · exact isLUB_csSup hne hs
    -- 🎉 no goals
#align is_lub_cSup' isLUB_csSup'

theorem csSup_le_iff' {s : Set α} (hs : BddAbove s) {a : α} : sSup s ≤ a ↔ ∀ x ∈ s, x ≤ a :=
  isLUB_le_iff (isLUB_csSup' hs)
#align cSup_le_iff' csSup_le_iff'

theorem csSup_le' {s : Set α} {a : α} (h : a ∈ upperBounds s) : sSup s ≤ a :=
  (csSup_le_iff' ⟨a, h⟩).2 h
#align cSup_le' csSup_le'

theorem le_csSup_iff' {s : Set α} {a : α} (h : BddAbove s) :
    a ≤ sSup s ↔ ∀ b, b ∈ upperBounds s → a ≤ b :=
  ⟨fun h _ hb => le_trans h (csSup_le' hb), fun hb => hb _ fun _ => le_csSup h⟩
#align le_cSup_iff' le_csSup_iff'

theorem le_ciSup_iff' {s : ι → α} {a : α} (h : BddAbove (range s)) :
    a ≤ iSup s ↔ ∀ b, (∀ i, s i ≤ b) → a ≤ b := by simp [iSup, h, le_csSup_iff', upperBounds]
                                                   -- 🎉 no goals
#align le_csupr_iff' le_ciSup_iff'

theorem le_csInf_iff'' {s : Set α} {a : α} (ne : s.Nonempty) :
    a ≤ sInf s ↔ ∀ b : α, b ∈ s → a ≤ b :=
  le_csInf_iff ⟨⊥, fun _ _ => bot_le⟩ ne
#align le_cInf_iff'' le_csInf_iff''

theorem le_ciInf_iff' [Nonempty ι] {f : ι → α} {a : α} : a ≤ iInf f ↔ ∀ i, a ≤ f i :=
  le_ciInf_iff ⟨⊥, fun _ _ => bot_le⟩
#align le_cinfi_iff' le_ciInf_iff'

theorem csInf_le' {s : Set α} {a : α} (h : a ∈ s) : sInf s ≤ a :=
  csInf_le ⟨⊥, fun _ _ => bot_le⟩ h
#align cInf_le' csInf_le'

theorem ciInf_le' (f : ι → α) (i : ι) : iInf f ≤ f i :=
  ciInf_le ⟨⊥, fun _ _ => bot_le⟩ _
#align cinfi_le' ciInf_le'

theorem exists_lt_of_lt_csSup' {s : Set α} {a : α} (h : a < sSup s) : ∃ b ∈ s, a < b := by
  contrapose! h
  -- ⊢ sSup s ≤ a
  exact csSup_le' h
  -- 🎉 no goals
#align exists_lt_of_lt_cSup' exists_lt_of_lt_csSup'

theorem ciSup_le_iff' {f : ι → α} (h : BddAbove (range f)) {a : α} :
    ⨆ i, f i ≤ a ↔ ∀ i, f i ≤ a :=
  (csSup_le_iff' h).trans forall_range_iff
#align csupr_le_iff' ciSup_le_iff'

theorem ciSup_le' {f : ι → α} {a : α} (h : ∀ i, f i ≤ a) : ⨆ i, f i ≤ a :=
  csSup_le' <| forall_range_iff.2 h
#align csupr_le' ciSup_le'

theorem exists_lt_of_lt_ciSup' {f : ι → α} {a : α} (h : a < ⨆ i, f i) : ∃ i, a < f i := by
  contrapose! h
  -- ⊢ ⨆ (i : ι), f i ≤ a
  exact ciSup_le' h
  -- 🎉 no goals
#align exists_lt_of_lt_csupr' exists_lt_of_lt_ciSup'

theorem ciSup_mono' {ι'} {f : ι → α} {g : ι' → α} (hg : BddAbove (range g))
    (h : ∀ i, ∃ i', f i ≤ g i') : iSup f ≤ iSup g :=
  ciSup_le' fun i => Exists.elim (h i) (le_ciSup_of_le hg)
#align csupr_mono' ciSup_mono'

theorem csInf_le_csInf' {s t : Set α} (h₁ : t.Nonempty) (h₂ : t ⊆ s) : sInf s ≤ sInf t :=
  csInf_le_csInf (OrderBot.bddBelow s) h₁ h₂
#align cInf_le_cInf' csInf_le_csInf'

end ConditionallyCompleteLinearOrderBot

namespace WithTop

open Classical

variable [ConditionallyCompleteLinearOrderBot α]

/-- The `sSup` of a non-empty set is its least upper bound for a conditionally
complete lattice with a top. -/
theorem isLUB_sSup' {β : Type*} [ConditionallyCompleteLattice β] {s : Set (WithTop β)}
    (hs : s.Nonempty) : IsLUB s (sSup s) := by
  constructor
  -- ⊢ sSup s ∈ upperBounds s
  · show ite _ _ _ ∈ _
    -- ⊢ (if ⊤ ∈ s then ⊤ else if BddAbove ((fun a => ↑a) ⁻¹' s) then ↑(sSup ((fun a  …
    split_ifs with h₁ h₂
    · intro _ _
      -- ⊢ a✝¹ ≤ ⊤
      exact le_top
      -- 🎉 no goals
    · rintro (⟨⟩ | a) ha
      -- ⊢ none ≤ ↑(sSup ((fun a => ↑a) ⁻¹' s))
      · contradiction
        -- 🎉 no goals
      apply some_le_some.2
      -- ⊢ a ≤ sSup ((fun a => ↑a) ⁻¹' s)
      exact le_csSup h₂ ha
      -- 🎉 no goals
    · intro _ _
      -- ⊢ a✝¹ ≤ ⊤
      exact le_top
      -- 🎉 no goals
  · show ite _ _ _ ∈ _
    -- ⊢ (if ⊤ ∈ s then ⊤ else if BddAbove ((fun a => ↑a) ⁻¹' s) then ↑(sSup ((fun a  …
    split_ifs with h₁ h₂
    · rintro (⟨⟩ | a) ha
      -- ⊢ ⊤ ≤ none
      · exact le_rfl
        -- 🎉 no goals
      · exact False.elim (not_top_le_coe a (ha h₁))
        -- 🎉 no goals
    · rintro (⟨⟩ | b) hb
      -- ⊢ ↑(sSup ((fun a => ↑a) ⁻¹' s)) ≤ none
      · exact le_top
        -- 🎉 no goals
      refine' some_le_some.2 (csSup_le _ _)
      -- ⊢ Set.Nonempty ((fun a => ↑a) ⁻¹' s)
      · rcases hs with ⟨⟨⟩ | b, hb⟩
        -- ⊢ Set.Nonempty ((fun a => ↑a) ⁻¹' s)
        · exact absurd hb h₁
          -- 🎉 no goals
        · exact ⟨b, hb⟩
          -- 🎉 no goals
      · intro a ha
        -- ⊢ a ≤ b
        exact some_le_some.1 (hb ha)
        -- 🎉 no goals
    · rintro (⟨⟩ | b) hb
      -- ⊢ ⊤ ≤ none
      · exact le_rfl
        -- 🎉 no goals
      · exfalso
        -- ⊢ False
        apply h₂
        -- ⊢ BddAbove ((fun a => ↑a) ⁻¹' s)
        use b
        -- ⊢ b ∈ upperBounds ((fun a => ↑a) ⁻¹' s)
        intro a ha
        -- ⊢ a ≤ b
        exact some_le_some.1 (hb ha)
        -- 🎉 no goals
#align with_top.is_lub_Sup' WithTop.isLUB_sSup'

-- Porting note: in mathlib3 `dsimp only [sSup]` was not needed, we used `show IsLUB ∅ (ite _ _ _)`
theorem isLUB_sSup (s : Set (WithTop α)) : IsLUB s (sSup s) := by
  cases' s.eq_empty_or_nonempty with hs hs
  -- ⊢ IsLUB s (sSup s)
  · rw [hs]
    -- ⊢ IsLUB ∅ (sSup ∅)
    dsimp only [sSup]
    -- ⊢ IsLUB ∅ (if ⊤ ∈ ∅ then ⊤ else if BddAbove ((fun a => ↑a) ⁻¹' ∅) then ↑(sSup  …
    show IsLUB ∅ _
    -- ⊢ IsLUB ∅ (if ⊤ ∈ ∅ then ⊤ else if BddAbove ((fun a => ↑a) ⁻¹' ∅) then ↑(sSup  …
    split_ifs with h₁ h₂
    · cases h₁
      -- 🎉 no goals
    · rw [preimage_empty, csSup_empty]
      -- ⊢ IsLUB ∅ ↑⊥
      exact isLUB_empty
      -- 🎉 no goals
    · exfalso
      -- ⊢ False
      apply h₂
      -- ⊢ BddAbove ((fun a => ↑a) ⁻¹' ∅)
      use ⊥
      -- ⊢ ⊥ ∈ upperBounds ((fun a => ↑a) ⁻¹' ∅)
      rintro a ⟨⟩
      -- 🎉 no goals
  exact isLUB_sSup' hs
  -- 🎉 no goals
#align with_top.is_lub_Sup WithTop.isLUB_sSup

/-- The `sInf` of a bounded-below set is its greatest lower bound for a conditionally
complete lattice with a top. -/
theorem isGLB_sInf' {β : Type*} [ConditionallyCompleteLattice β] {s : Set (WithTop β)}
    (hs : BddBelow s) : IsGLB s (sInf s) := by
  constructor
  -- ⊢ sInf s ∈ lowerBounds s
  · show ite _ _ _ ∈ _
    -- ⊢ (if s ⊆ {⊤} then ⊤ else ↑(sInf ((fun a => ↑a) ⁻¹' s))) ∈ lowerBounds s
    split_ifs with h
    -- ⊢ ⊤ ∈ lowerBounds s
    · intro a ha
      -- ⊢ ⊤ ≤ a
      exact top_le_iff.2 (Set.mem_singleton_iff.1 (h ha))
      -- 🎉 no goals
    · rintro (⟨⟩ | a) ha
      -- ⊢ ↑(sInf ((fun a => ↑a) ⁻¹' s)) ≤ none
      · exact le_top
        -- 🎉 no goals
      refine' some_le_some.2 (csInf_le _ ha)
      -- ⊢ BddBelow ((fun a => ↑a) ⁻¹' s)
      rcases hs with ⟨⟨⟩ | b, hb⟩
      -- ⊢ BddBelow ((fun a => ↑a) ⁻¹' s)
      · exfalso
        -- ⊢ False
        apply h
        -- ⊢ s ⊆ {⊤}
        intro c hc
        -- ⊢ c ∈ {⊤}
        rw [mem_singleton_iff, ← top_le_iff]
        -- ⊢ ⊤ ≤ c
        exact hb hc
        -- 🎉 no goals
      use b
      -- ⊢ b ∈ lowerBounds ((fun a => ↑a) ⁻¹' s)
      intro c hc
      -- ⊢ b ≤ c
      exact some_le_some.1 (hb hc)
      -- 🎉 no goals
  · show ite _ _ _ ∈ _
    -- ⊢ (if s ⊆ {⊤} then ⊤ else ↑(sInf ((fun a => ↑a) ⁻¹' s))) ∈ upperBounds (lowerB …
    split_ifs with h
    -- ⊢ ⊤ ∈ upperBounds (lowerBounds s)
    · intro _ _
      -- ⊢ a✝¹ ≤ ⊤
      exact le_top
      -- 🎉 no goals
    · rintro (⟨⟩ | a) ha
      -- ⊢ none ≤ ↑(sInf ((fun a => ↑a) ⁻¹' s))
      · exfalso
        -- ⊢ False
        apply h
        -- ⊢ s ⊆ {⊤}
        intro b hb
        -- ⊢ b ∈ {⊤}
        exact Set.mem_singleton_iff.2 (top_le_iff.1 (ha hb))
        -- 🎉 no goals
      · refine' some_le_some.2 (le_csInf _ _)
        -- ⊢ Set.Nonempty ((fun a => ↑a) ⁻¹' s)
        · classical
            contrapose! h
            rintro (⟨⟩ | a) ha
            · exact mem_singleton ⊤
            · exact (h ⟨a, ha⟩).elim
        · intro b hb
          -- ⊢ a ≤ b
          rw [← some_le_some]
          -- ⊢ Option.some a ≤ Option.some b
          exact ha hb
          -- 🎉 no goals
#align with_top.is_glb_Inf' WithTop.isGLB_sInf'

theorem isGLB_sInf (s : Set (WithTop α)) : IsGLB s (sInf s) := by
  by_cases hs : BddBelow s
  -- ⊢ IsGLB s (sInf s)
  · exact isGLB_sInf' hs
    -- 🎉 no goals
  · exfalso
    -- ⊢ False
    apply hs
    -- ⊢ BddBelow s
    use ⊥
    -- ⊢ ⊥ ∈ lowerBounds s
    intro _ _
    -- ⊢ ⊥ ≤ a✝¹
    exact bot_le
    -- 🎉 no goals
#align with_top.is_glb_Inf WithTop.isGLB_sInf

noncomputable instance : CompleteLinearOrder (WithTop α) :=
  { WithTop.linearOrder, WithTop.lattice, WithTop.orderTop, WithTop.orderBot with
    sup := Sup.sup
    le_sSup := fun s => (isLUB_sSup s).1
    sSup_le := fun s => (isLUB_sSup s).2
    inf := Inf.inf
    le_sInf := fun s => (isGLB_sInf s).2
    sInf_le := fun s => (isGLB_sInf s).1 }

/-- A version of `WithTop.coe_sSup'` with a more convenient but less general statement. -/
@[norm_cast]
theorem coe_sSup {s : Set α} (hb : BddAbove s) : ↑(sSup s) = (⨆ a ∈ s, ↑a : WithTop α) := by
  rw [coe_sSup' hb, sSup_image]
  -- 🎉 no goals
#align with_top.coe_Sup WithTop.coe_sSup

/-- A version of `WithTop.coe_sInf'` with a more convenient but less general statement. -/
@[norm_cast]
theorem coe_sInf {s : Set α} (hs : s.Nonempty) : ↑(sInf s) = (⨅ a ∈ s, ↑a : WithTop α) := by
  rw [coe_sInf' hs, sInf_image]
  -- 🎉 no goals
#align with_top.coe_Inf WithTop.coe_sInf

end WithTop

namespace Monotone

variable [Preorder α] [ConditionallyCompleteLattice β] {f : α → β} (h_mono : Monotone f)

/-! A monotone function into a conditionally complete lattice preserves the ordering properties of
`sSup` and `sInf`. -/


theorem le_csSup_image {s : Set α} {c : α} (hcs : c ∈ s) (h_bdd : BddAbove s) :
    f c ≤ sSup (f '' s) :=
  le_csSup (map_bddAbove h_mono h_bdd) (mem_image_of_mem f hcs)
#align monotone.le_cSup_image Monotone.le_csSup_image

theorem csSup_image_le {s : Set α} (hs : s.Nonempty) {B : α} (hB : B ∈ upperBounds s) :
    sSup (f '' s) ≤ f B :=
  csSup_le (Nonempty.image f hs) (h_mono.mem_upperBounds_image hB)
#align monotone.cSup_image_le Monotone.csSup_image_le

-- Porting note: in mathlib3 `f'` is not needed
theorem csInf_image_le {s : Set α} {c : α} (hcs : c ∈ s) (h_bdd : BddBelow s) :
    sInf (f '' s) ≤ f c := by
  let f' : αᵒᵈ → βᵒᵈ := f
  -- ⊢ sInf (f '' s) ≤ f c
  exact @le_csSup_image αᵒᵈ βᵒᵈ _ _ _
    (show Monotone f' from fun x y hxy => h_mono hxy) _ _ hcs h_bdd
#align monotone.cInf_image_le Monotone.csInf_image_le

-- Porting note: in mathlib3 `f'` is not needed
theorem le_csInf_image {s : Set α} (hs : s.Nonempty) {B : α} (hB : B ∈ lowerBounds s) :
    f B ≤ sInf (f '' s) := by
  let f' : αᵒᵈ → βᵒᵈ := f
  -- ⊢ f B ≤ sInf (f '' s)
  exact @csSup_image_le αᵒᵈ βᵒᵈ _ _ _
    (show Monotone f' from fun x y hxy => h_mono hxy) _ hs _ hB
#align monotone.le_cInf_image Monotone.le_csInf_image

end Monotone

namespace GaloisConnection

variable [ConditionallyCompleteLattice α] [ConditionallyCompleteLattice β] [Nonempty ι] {l : α → β}
  {u : β → α}

theorem l_csSup (gc : GaloisConnection l u) {s : Set α} (hne : s.Nonempty) (hbdd : BddAbove s) :
    l (sSup s) = ⨆ x : s, l x :=
  Eq.symm <| IsLUB.ciSup_set_eq (gc.isLUB_l_image <| isLUB_csSup hne hbdd) hne
#align galois_connection.l_cSup GaloisConnection.l_csSup

theorem l_csSup' (gc : GaloisConnection l u) {s : Set α} (hne : s.Nonempty) (hbdd : BddAbove s) :
    l (sSup s) = sSup (l '' s) := by rw [gc.l_csSup hne hbdd, sSup_image']
                                     -- 🎉 no goals
#align galois_connection.l_cSup' GaloisConnection.l_csSup'

theorem l_ciSup (gc : GaloisConnection l u) {f : ι → α} (hf : BddAbove (range f)) :
    l (⨆ i, f i) = ⨆ i, l (f i) := by rw [iSup, gc.l_csSup (range_nonempty _) hf, iSup_range']
                                      -- 🎉 no goals
#align galois_connection.l_csupr GaloisConnection.l_ciSup

theorem l_ciSup_set (gc : GaloisConnection l u) {s : Set γ} {f : γ → α} (hf : BddAbove (f '' s))
    (hne : s.Nonempty) : l (⨆ i : s, f i) = ⨆ i : s, l (f i) := by
  haveI := hne.to_subtype
  -- ⊢ l (⨆ (i : ↑s), f ↑i) = ⨆ (i : ↑s), l (f ↑i)
  rw [image_eq_range] at hf
  -- ⊢ l (⨆ (i : ↑s), f ↑i) = ⨆ (i : ↑s), l (f ↑i)
  exact gc.l_ciSup hf
  -- 🎉 no goals
#align galois_connection.l_csupr_set GaloisConnection.l_ciSup_set

theorem u_csInf (gc : GaloisConnection l u) {s : Set β} (hne : s.Nonempty) (hbdd : BddBelow s) :
    u (sInf s) = ⨅ x : s, u x :=
  gc.dual.l_csSup hne hbdd
#align galois_connection.u_cInf GaloisConnection.u_csInf

theorem u_csInf' (gc : GaloisConnection l u) {s : Set β} (hne : s.Nonempty) (hbdd : BddBelow s) :
    u (sInf s) = sInf (u '' s) :=
  gc.dual.l_csSup' hne hbdd
#align galois_connection.u_cInf' GaloisConnection.u_csInf'

theorem u_ciInf (gc : GaloisConnection l u) {f : ι → β} (hf : BddBelow (range f)) :
    u (⨅ i, f i) = ⨅ i, u (f i) :=
  gc.dual.l_ciSup hf
#align galois_connection.u_cinfi GaloisConnection.u_ciInf

theorem u_ciInf_set (gc : GaloisConnection l u) {s : Set γ} {f : γ → β} (hf : BddBelow (f '' s))
    (hne : s.Nonempty) : u (⨅ i : s, f i) = ⨅ i : s, u (f i) :=
  gc.dual.l_ciSup_set hf hne
#align galois_connection.u_cinfi_set GaloisConnection.u_ciInf_set

end GaloisConnection

namespace OrderIso

variable [ConditionallyCompleteLattice α] [ConditionallyCompleteLattice β] [Nonempty ι]

theorem map_csSup (e : α ≃o β) {s : Set α} (hne : s.Nonempty) (hbdd : BddAbove s) :
    e (sSup s) = ⨆ x : s, e x :=
  e.to_galoisConnection.l_csSup hne hbdd
#align order_iso.map_cSup OrderIso.map_csSup

theorem map_csSup' (e : α ≃o β) {s : Set α} (hne : s.Nonempty) (hbdd : BddAbove s) :
    e (sSup s) = sSup (e '' s) :=
  e.to_galoisConnection.l_csSup' hne hbdd
#align order_iso.map_cSup' OrderIso.map_csSup'

theorem map_ciSup (e : α ≃o β) {f : ι → α} (hf : BddAbove (range f)) :
    e (⨆ i, f i) = ⨆ i, e (f i) :=
  e.to_galoisConnection.l_ciSup hf
#align order_iso.map_csupr OrderIso.map_ciSup

theorem map_ciSup_set (e : α ≃o β) {s : Set γ} {f : γ → α} (hf : BddAbove (f '' s))
    (hne : s.Nonempty) : e (⨆ i : s, f i) = ⨆ i : s, e (f i) :=
  e.to_galoisConnection.l_ciSup_set hf hne
#align order_iso.map_csupr_set OrderIso.map_ciSup_set

theorem map_csInf (e : α ≃o β) {s : Set α} (hne : s.Nonempty) (hbdd : BddBelow s) :
    e (sInf s) = ⨅ x : s, e x :=
  e.dual.map_csSup hne hbdd
#align order_iso.map_cInf OrderIso.map_csInf

theorem map_csInf' (e : α ≃o β) {s : Set α} (hne : s.Nonempty) (hbdd : BddBelow s) :
    e (sInf s) = sInf (e '' s) :=
  e.dual.map_csSup' hne hbdd
#align order_iso.map_cInf' OrderIso.map_csInf'

theorem map_ciInf (e : α ≃o β) {f : ι → α} (hf : BddBelow (range f)) :
    e (⨅ i, f i) = ⨅ i, e (f i) :=
  e.dual.map_ciSup hf
#align order_iso.map_cinfi OrderIso.map_ciInf

theorem map_ciInf_set (e : α ≃o β) {s : Set γ} {f : γ → α} (hf : BddBelow (f '' s))
    (hne : s.Nonempty) : e (⨅ i : s, f i) = ⨅ i : s, e (f i) :=
  e.dual.map_ciSup_set hf hne
#align order_iso.map_cinfi_set OrderIso.map_ciInf_set

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
  refine' eq_of_forall_ge_iff fun c => _
  -- ⊢ sSup (image2 l s t) ≤ c ↔ l (sSup s) (sSup t) ≤ c
  rw [csSup_le_iff (hs₁.image2 (fun _ => (h₁ _).monotone_l) (fun _ => (h₂ _).monotone_l) ht₁)
      (hs₀.image2 ht₀),
    forall_image2_iff, forall₂_swap, (h₂ _).le_iff_le, csSup_le_iff ht₁ ht₀]
  simp_rw [← (h₂ _).le_iff_le, (h₁ _).le_iff_le, csSup_le_iff hs₁ hs₀]
  -- 🎉 no goals
#align cSup_image2_eq_cSup_cSup csSup_image2_eq_csSup_csSup

theorem csSup_image2_eq_csSup_csInf (h₁ : ∀ b, GaloisConnection (swap l b) (u₁ b))
    (h₂ : ∀ a, GaloisConnection (l a ∘ ofDual) (toDual ∘ u₂ a)) :
    s.Nonempty → BddAbove s → t.Nonempty → BddBelow t → sSup (image2 l s t) = l (sSup s) (sInf t) :=
  @csSup_image2_eq_csSup_csSup _ βᵒᵈ _ _ _ _ _ _ _ _ _ h₁ h₂
#align cSup_image2_eq_cSup_cInf csSup_image2_eq_csSup_csInf

theorem csSup_image2_eq_csInf_csSup (h₁ : ∀ b, GaloisConnection (swap l b ∘ ofDual) (toDual ∘ u₁ b))
    (h₂ : ∀ a, GaloisConnection (l a) (u₂ a)) :
    s.Nonempty → BddBelow s → t.Nonempty → BddAbove t → sSup (image2 l s t) = l (sInf s) (sSup t) :=
  @csSup_image2_eq_csSup_csSup αᵒᵈ _ _ _ _ _ _ _ _ _ _ h₁ h₂
#align cSup_image2_eq_cInf_cSup csSup_image2_eq_csInf_csSup

theorem csSup_image2_eq_csInf_csInf (h₁ : ∀ b, GaloisConnection (swap l b ∘ ofDual) (toDual ∘ u₁ b))
    (h₂ : ∀ a, GaloisConnection (l a ∘ ofDual) (toDual ∘ u₂ a)) :
    s.Nonempty → BddBelow s → t.Nonempty → BddBelow t → sSup (image2 l s t) = l (sInf s) (sInf t) :=
  @csSup_image2_eq_csSup_csSup αᵒᵈ βᵒᵈ _ _ _ _ _ _ _ _ _ h₁ h₂
#align cSup_image2_eq_cInf_cInf csSup_image2_eq_csInf_csInf

theorem csInf_image2_eq_csInf_csInf (h₁ : ∀ b, GaloisConnection (l₁ b) (swap u b))
    (h₂ : ∀ a, GaloisConnection (l₂ a) (u a)) :
    s.Nonempty → BddBelow s → t.Nonempty → BddBelow t → sInf (image2 u s t) = u (sInf s) (sInf t) :=
  @csSup_image2_eq_csSup_csSup αᵒᵈ βᵒᵈ γᵒᵈ _ _ _ _ _ _ l₁ l₂ (fun _ => (h₁ _).dual) fun _ =>
    (h₂ _).dual
#align cInf_image2_eq_cInf_cInf csInf_image2_eq_csInf_csInf

theorem csInf_image2_eq_csInf_csSup (h₁ : ∀ b, GaloisConnection (l₁ b) (swap u b))
    (h₂ : ∀ a, GaloisConnection (toDual ∘ l₂ a) (u a ∘ ofDual)) :
    s.Nonempty → BddBelow s → t.Nonempty → BddAbove t → sInf (image2 u s t) = u (sInf s) (sSup t) :=
  @csInf_image2_eq_csInf_csInf _ βᵒᵈ _ _ _ _ _ _ _ _ _ h₁ h₂
#align cInf_image2_eq_cInf_cSup csInf_image2_eq_csInf_csSup

theorem csInf_image2_eq_csSup_csInf (h₁ : ∀ b, GaloisConnection (toDual ∘ l₁ b) (swap u b ∘ ofDual))
    (h₂ : ∀ a, GaloisConnection (l₂ a) (u a)) :
    s.Nonempty → BddAbove s → t.Nonempty → BddBelow t → sInf (image2 u s t) = u (sSup s) (sInf t) :=
  @csInf_image2_eq_csInf_csInf αᵒᵈ _ _ _ _ _ _ _ _ _ _ h₁ h₂
#align cInf_image2_eq_cSup_cInf csInf_image2_eq_csSup_csInf

theorem csInf_image2_eq_csSup_csSup (h₁ : ∀ b, GaloisConnection (toDual ∘ l₁ b) (swap u b ∘ ofDual))
    (h₂ : ∀ a, GaloisConnection (toDual ∘ l₂ a) (u a ∘ ofDual)) :
    s.Nonempty → BddAbove s → t.Nonempty → BddAbove t → sInf (image2 u s t) = u (sSup s) (sSup t) :=
  @csInf_image2_eq_csInf_csInf αᵒᵈ βᵒᵈ _ _ _ _ _ _ _ _ _ h₁ h₂
#align cInf_image2_eq_cSup_cSup csInf_image2_eq_csSup_csSup

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


open Classical

/-- Adding a top element to a conditionally complete lattice
gives a conditionally complete lattice -/
noncomputable instance WithTop.conditionallyCompleteLattice {α : Type*}
    [ConditionallyCompleteLattice α] : ConditionallyCompleteLattice (WithTop α) :=
  { lattice, instSupSet, instInfSet with
    le_csSup := fun _ a _ haS => (WithTop.isLUB_sSup' ⟨a, haS⟩).1 haS
    csSup_le := fun _ _ hS haS => (WithTop.isLUB_sSup' hS).2 haS
    csInf_le := fun _ _ hS haS => (WithTop.isGLB_sInf' hS).1 haS
    le_csInf := fun _ a _ haS => (WithTop.isGLB_sInf' ⟨a, haS⟩).2 haS }
#align with_top.conditionally_complete_lattice WithTop.conditionallyCompleteLattice

/-- Adding a bottom element to a conditionally complete lattice
gives a conditionally complete lattice -/
noncomputable instance WithBot.conditionallyCompleteLattice {α : Type*}
    [ConditionallyCompleteLattice α] : ConditionallyCompleteLattice (WithBot α) :=
  { WithBot.lattice with
    le_csSup := (@WithTop.conditionallyCompleteLattice αᵒᵈ _).csInf_le
    csSup_le := (@WithTop.conditionallyCompleteLattice αᵒᵈ _).le_csInf
    csInf_le := (@WithTop.conditionallyCompleteLattice αᵒᵈ _).le_csSup
    le_csInf := (@WithTop.conditionallyCompleteLattice αᵒᵈ _).csSup_le }
#align with_bot.conditionally_complete_lattice WithBot.conditionallyCompleteLattice

-- Porting note: `convert @bot_le (WithTop (WithBot α)) _ _ a` was `convert bot_le`
noncomputable instance WithTop.WithBot.completeLattice {α : Type*}
    [ConditionallyCompleteLattice α] : CompleteLattice (WithTop (WithBot α)) :=
  { instInfSet, instSupSet, boundedOrder, lattice with
    le_sSup := fun S a haS => (WithTop.isLUB_sSup' ⟨a, haS⟩).1 haS
    sSup_le := fun S a ha => by
      cases' S.eq_empty_or_nonempty with h h
      -- ⊢ sSup S ≤ a
      · show ite _ _ _ ≤ a
        -- ⊢ (if ⊤ ∈ S then ⊤ else if BddAbove ((fun a => ↑a) ⁻¹' S) then ↑(sSup ((fun a  …
        split_ifs with h₁ h₂
        · rw [h] at h₁
          -- ⊢ ⊤ ≤ a
          cases h₁
          -- 🎉 no goals
        · convert @bot_le _ _ _ a
          -- ⊢ ↑(sSup ((fun a => ↑a) ⁻¹' S)) = ⊥
          -- porting note: previous proof relied on convert unfolding
          -- the definition of ⊥
          apply congr_arg
          -- ⊢ sSup ((fun a => ↑a) ⁻¹' S) = ⊥
          simp only [h, preimage_empty, WithBot.csSup_empty]
          -- 🎉 no goals
        · exfalso
          -- ⊢ False
          apply h₂
          -- ⊢ BddAbove ((fun a => ↑a) ⁻¹' S)
          use ⊥
          -- ⊢ ⊥ ∈ upperBounds ((fun a => ↑a) ⁻¹' S)
          rw [h]
          -- ⊢ ⊥ ∈ upperBounds ((fun a => ↑a) ⁻¹' ∅)
          rintro b ⟨⟩
          -- 🎉 no goals
      · refine' (WithTop.isLUB_sSup' h).2 ha
        -- 🎉 no goals
    sInf_le := fun S a haS =>
      show ite _ _ _ ≤ a by
        split_ifs with h₁
        -- ⊢ ⊤ ≤ a
        · cases' a with a
          -- ⊢ ⊤ ≤ none
          exact le_rfl
          -- ⊢ ⊤ ≤ Option.some a
          cases h₁ haS
          -- 🎉 no goals
        · cases a
          -- ⊢ ↑(sInf ((fun a => ↑a) ⁻¹' S)) ≤ none
          · exact le_top
            -- 🎉 no goals
          · apply WithTop.some_le_some.2
            -- ⊢ sInf ((fun a => ↑a) ⁻¹' S) ≤ val✝
            refine' csInf_le _ haS
            -- ⊢ BddBelow ((fun a => ↑a) ⁻¹' S)
            use ⊥
            -- ⊢ ⊥ ∈ lowerBounds ((fun a => ↑a) ⁻¹' S)
            intro b _
            -- ⊢ ⊥ ≤ b
            exact bot_le
            -- 🎉 no goals
    le_sInf := fun S a haS => (WithTop.isGLB_sInf' ⟨a, haS⟩).2 haS }
#align with_top.with_bot.complete_lattice WithTop.WithBot.completeLattice

noncomputable instance WithTop.WithBot.completeLinearOrder {α : Type*}
    [ConditionallyCompleteLinearOrder α] : CompleteLinearOrder (WithTop (WithBot α)) :=
  { WithTop.WithBot.completeLattice, WithTop.linearOrder with }
#align with_top.with_bot.complete_linear_order WithTop.WithBot.completeLinearOrder

noncomputable instance WithBot.WithTop.completeLattice {α : Type*}
    [ConditionallyCompleteLattice α] : CompleteLattice (WithBot (WithTop α)) :=
  { instInfSet, instSupSet, instBoundedOrder, lattice with
    le_sSup := (@WithTop.WithBot.completeLattice αᵒᵈ _).sInf_le
    sSup_le := (@WithTop.WithBot.completeLattice αᵒᵈ _).le_sInf
    sInf_le := (@WithTop.WithBot.completeLattice αᵒᵈ _).le_sSup
    le_sInf := (@WithTop.WithBot.completeLattice αᵒᵈ _).sSup_le }
#align with_bot.with_top.complete_lattice WithBot.WithTop.completeLattice

noncomputable instance WithBot.WithTop.completeLinearOrder {α : Type*}
    [ConditionallyCompleteLinearOrder α] : CompleteLinearOrder (WithBot (WithTop α)) :=
  { WithBot.WithTop.completeLattice, WithBot.linearOrder with }
#align with_bot.with_top.complete_linear_order WithBot.WithTop.completeLinearOrder

theorem WithTop.iSup_coe_eq_top {ι : Sort*} {α : Type*} [ConditionallyCompleteLinearOrderBot α]
    (f : ι → α) : ⨆ x, (f x : WithTop α) = ⊤ ↔ ¬BddAbove (Set.range f) := by
  rw [iSup_eq_top, not_bddAbove_iff]
  -- ⊢ (∀ (b : WithTop α), b < ⊤ → ∃ i, b < ↑(f i)) ↔ ∀ (x : α), ∃ y, y ∈ range f ∧ …
  refine' ⟨fun hf r => _, fun hf a ha => _⟩
  -- ⊢ ∃ y, y ∈ range f ∧ r < y
  · rcases hf r (WithTop.coe_lt_top r) with ⟨i, hi⟩
    -- ⊢ ∃ y, y ∈ range f ∧ r < y
    exact ⟨f i, ⟨i, rfl⟩, WithTop.coe_lt_coe.mp hi⟩
    -- 🎉 no goals
  · rcases hf (a.untop ha.ne) with ⟨-, ⟨i, rfl⟩, hi⟩
    -- ⊢ ∃ i, a < ↑(f i)
    exact ⟨i, by simpa only [WithTop.coe_untop _ ha.ne] using WithTop.coe_lt_coe.mpr hi⟩
    -- 🎉 no goals
#align with_top.supr_coe_eq_top WithTop.iSup_coe_eq_top

theorem WithTop.iSup_coe_lt_top {ι : Sort*} {α : Type*} [ConditionallyCompleteLinearOrderBot α]
    (f : ι → α) : ⨆ x, (f x : WithTop α) < ⊤ ↔ BddAbove (Set.range f) :=
  lt_top_iff_ne_top.trans <| (WithTop.iSup_coe_eq_top f).not.trans not_not
#align with_top.supr_coe_lt_top WithTop.iSup_coe_lt_top

end WithTopBot

-- Guard against import creep
assert_not_exists Multiset
