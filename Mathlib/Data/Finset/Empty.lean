/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Multiset.ZeroCons

/-!
# Empty and nonempty finite sets

This file defines the empty finite set ∅ and a predicate for nonempty `Finset`s.

## Main declarations
* `Finset.Nonempty`: A finset is nonempty if it has elements. This is equivalent to saying `s ≠ ∅`.
* `Finset.empty`: Denoted by `∅`. The finset associated to any type consisting of no elements.

## Tags

finite sets, finset

-/

-- Assert that we define `Finset` without the material on `List.sublists`.
-- Note that we cannot use `List.sublists` itself as that is defined very early.
assert_not_exists List.sublistsLen Multiset.powerset CompleteLattice OrderedCommMonoid

open Multiset Subtype Function

universe u

variable {α : Type*} {β : Type*} {γ : Type*}

namespace Finset

/-! ### Nonempty -/


/-- The property `s.Nonempty` expresses the fact that the finset `s` is not empty. It should be used
in theorem assumptions instead of `∃ x, x ∈ s` or `s ≠ ∅` as it gives access to a nice API thanks
to the dot notation. -/
protected def Nonempty (s : Finset α) : Prop := ∃ x : α, x ∈ s

@[grind =]
theorem nonempty_def {s : Finset α} : s.Nonempty ↔ ∃ x, x ∈ s := Iff.rfl

instance decidableNonempty {s : Finset α} : Decidable s.Nonempty :=
  decidable_of_iff (∃ a ∈ s, true) <| by simp [Finset.Nonempty]

@[simp, norm_cast]
theorem coe_nonempty {s : Finset α} : (s : Set α).Nonempty ↔ s.Nonempty :=
  Iff.rfl

-- Not `@[simp]` since `nonempty_subtype` already is.
theorem nonempty_coe_sort {s : Finset α} : Nonempty (s : Type _) ↔ s.Nonempty :=
  nonempty_subtype

alias ⟨_, Nonempty.to_set⟩ := coe_nonempty

alias ⟨_, Nonempty.coe_sort⟩ := nonempty_coe_sort

theorem Nonempty.exists_mem {s : Finset α} (h : s.Nonempty) : ∃ x : α, x ∈ s :=
  h

@[gcongr] theorem Nonempty.mono {s t : Finset α} (hst : s ⊆ t) (hs : s.Nonempty) : t.Nonempty :=
  Set.Nonempty.mono hst hs

theorem Nonempty.forall_const {s : Finset α} (h : s.Nonempty) {p : Prop} : (∀ x ∈ s, p) ↔ p :=
  let ⟨x, hx⟩ := h
  ⟨fun h => h x hx, fun h _ _ => h⟩

theorem Nonempty.to_subtype {s : Finset α} : s.Nonempty → Nonempty s :=
  nonempty_coe_sort.2

theorem Nonempty.to_type {s : Finset α} : s.Nonempty → Nonempty α := fun ⟨x, _hx⟩ => ⟨x⟩

/-! ### empty -/


section Empty

variable {s : Finset α}

/-- The empty finset -/
protected def empty : Finset α :=
  ⟨0, nodup_zero⟩

instance : EmptyCollection (Finset α) :=
  ⟨Finset.empty⟩

instance inhabitedFinset : Inhabited (Finset α) :=
  ⟨∅⟩

@[simp]
theorem empty_val : (∅ : Finset α).1 = 0 :=
  rfl

@[simp, grind]
theorem notMem_empty (a : α) : a ∉ (∅ : Finset α) := by
  simp only [mem_def, empty_val, notMem_zero, not_false_iff]

@[deprecated (since := "2025-05-23")] alias not_mem_empty := notMem_empty

@[simp]
theorem not_nonempty_empty : ¬(∅ : Finset α).Nonempty := fun ⟨x, hx⟩ => notMem_empty x hx

@[simp]
theorem mk_zero : (⟨0, nodup_zero⟩ : Finset α) = ∅ :=
  rfl

theorem ne_empty_of_mem {a : α} {s : Finset α} (h : a ∈ s) : s ≠ ∅ := fun e =>
  notMem_empty a <| e ▸ h

theorem Nonempty.ne_empty {s : Finset α} (h : s.Nonempty) : s ≠ ∅ :=
  (Exists.elim h) fun _a => ne_empty_of_mem

@[simp]
theorem empty_subset (s : Finset α) : ∅ ⊆ s :=
  zero_subset _

theorem eq_empty_of_forall_notMem {s : Finset α} (H : ∀ x, x ∉ s) : s = ∅ :=
  eq_of_veq (eq_zero_of_forall_notMem H)

@[deprecated (since := "2025-05-23")] alias eq_empty_of_forall_not_mem := eq_empty_of_forall_notMem

theorem eq_empty_iff_forall_notMem {s : Finset α} : s = ∅ ↔ ∀ x, x ∉ s := by grind

@[deprecated (since := "2025-05-23")]
alias eq_empty_iff_forall_not_mem := eq_empty_iff_forall_notMem

@[simp]
theorem val_eq_zero {s : Finset α} : s.1 = 0 ↔ s = ∅ :=
  @val_inj _ s ∅

@[simp] lemma subset_empty : s ⊆ ∅ ↔ s = ∅ := subset_zero.trans val_eq_zero

@[simp]
theorem not_ssubset_empty (s : Finset α) : ¬s ⊂ ∅ := by grind

theorem nonempty_of_ne_empty {s : Finset α} (h : s ≠ ∅) : s.Nonempty :=
  exists_mem_of_ne_zero (mt val_eq_zero.1 h)

theorem nonempty_iff_ne_empty {s : Finset α} : s.Nonempty ↔ s ≠ ∅ :=
  ⟨Nonempty.ne_empty, nonempty_of_ne_empty⟩

@[simp]
theorem not_nonempty_iff_eq_empty {s : Finset α} : ¬s.Nonempty ↔ s = ∅ :=
  nonempty_iff_ne_empty.not.trans not_not

theorem eq_empty_or_nonempty (s : Finset α) : s = ∅ ∨ s.Nonempty :=
  by_cases Or.inl fun h => Or.inr (nonempty_of_ne_empty h)

@[simp, norm_cast]
theorem coe_empty : ((∅ : Finset α) : Set α) = ∅ := by grind

@[simp, norm_cast]
theorem coe_eq_empty {s : Finset α} : (s : Set α) = ∅ ↔ s = ∅ := by grind

@[simp]
theorem isEmpty_coe_sort {s : Finset α} : IsEmpty (s : Type _) ↔ s = ∅ := by
  simpa using @Set.isEmpty_coe_sort α s

instance instIsEmpty : IsEmpty (∅ : Finset α) :=
  isEmpty_coe_sort.2 rfl

/-- A `Finset` for an empty type is empty. -/
theorem eq_empty_of_isEmpty [IsEmpty α] (s : Finset α) : s = ∅ :=
  Finset.eq_empty_of_forall_notMem isEmptyElim

instance : OrderBot (Finset α) where
  bot := ∅
  bot_le := empty_subset

@[simp]
theorem bot_eq_empty : (⊥ : Finset α) = ∅ :=
  rfl

@[simp]
theorem empty_ssubset : ∅ ⊂ s ↔ s.Nonempty :=
  (@bot_lt_iff_ne_bot (Finset α) _ _ _).trans nonempty_iff_ne_empty.symm

alias ⟨_, Nonempty.empty_ssubset⟩ := empty_ssubset

-- useful rules for calculations with quantifiers
theorem exists_mem_empty_iff (p : α → Prop) : (∃ x, x ∈ (∅ : Finset α) ∧ p x) ↔ False := by
  grind

theorem forall_mem_empty_iff (p : α → Prop) : (∀ x, x ∈ (∅ : Finset α) → p x) ↔ True := by
  grind

end Empty
end Finset

namespace Mathlib.Meta
open Qq Lean Meta Finset

/-- Attempt to prove that a finset is nonempty using the `finsetNonempty` aesop rule-set.

You can add lemmas to the rule-set by tagging them with either:
* `aesop safe apply (rule_sets := [finsetNonempty])` if they are always a good idea to follow or
* `aesop unsafe apply (rule_sets := [finsetNonempty])` if they risk directing the search to a blind
  alley.

TODO: should some of the lemmas be `aesop safe simp` instead?
-/
def proveFinsetNonempty {u : Level} {α : Q(Type u)} (s : Q(Finset $α)) :
    MetaM (Option Q(Finset.Nonempty $s)) := do
  -- Aesop expects to operate on goals, so we're going to make a new goal.
  let goal ← Lean.Meta.mkFreshExprMVar q(Finset.Nonempty $s)
  let mvar := goal.mvarId!
  -- We want this to be fast, so use only the basic and `Finset.Nonempty`-specific rules.
  let rulesets ← Aesop.Frontend.getGlobalRuleSets #[`builtin, `finsetNonempty]
  let options : Aesop.Options' :=
    { terminal := true -- Fail if the new goal is not closed.
      generateScript := false
      useDefaultSimpSet := false -- Avoiding the whole simp set to speed up the tactic.
      warnOnNonterminal := false -- Don't show a warning on failure, simply return `none`.
      forwardMaxDepth? := none }
  let rules ← Aesop.mkLocalRuleSet rulesets options
  let (remainingGoals, _) ←
    try Aesop.search (options := options.toOptions) mvar (.some rules)
    catch _ => return none
  -- Fail if there are open goals remaining, this serves as an extra check for the
  -- Aesop configuration option `terminal := true`.
  if remainingGoals.size > 0 then return none
  Lean.getExprMVarAssignment? mvar

end Mathlib.Meta
