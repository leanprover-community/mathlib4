/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Multiset.Filter

/-!
# Filtering a finite set

## Main declarations

* `Finset.filter`: Given a decidable predicate `p : α → Prop`, `s.filter p` is
  the finset consisting of those elements in `s` satisfying the predicate `p`.

## Tags

finite sets, finset

-/

-- Assert that we define `Finset` without the material on `List.sublists`.
-- Note that we cannot use `List.sublists` itself as that is defined very early.
assert_not_exists List.sublistsLen Multiset.powerset CompleteLattice IsOrderedMonoid

open Multiset Subtype Function

universe u

variable {α : Type*} {β : Type*} {γ : Type*}

namespace Finset

-- TODO: these should be global attributes, but this will require fixing other files
attribute [local trans] Subset.trans Superset.trans

/-! ### filter -/

section Filter

variable (p q : α → Prop) [DecidablePred p] [DecidablePred q] {s t : Finset α}

/-- `Finset.filter p s` is the set of elements of `s` that satisfy `p`.

For example, one can use `s.filter (· ∈ t)` to get the intersection of `s` with `t : Set α`
as a `Finset α` (when a `DecidablePred (· ∈ t)` instance is available). -/
def filter (s : Finset α) : Finset α :=
  ⟨_, s.2.filter p⟩

end Finset.Filter

namespace Mathlib.Meta
open Lean Elab Term Meta Batteries.ExtendedBinder

/-- Return `true` if `expectedType?` is `some (Finset ?α)`, throws `throwUnsupportedSyntax` if it is
`some (Set ?α)`, and returns `false` otherwise. -/
def knownToBeFinsetNotSet (expectedType? : Option Expr) : TermElabM Bool :=
  -- As we want to reason about the expected type, we would like to wait for it to be available.
  -- However this means that if we fall back on `elabSetBuilder` we will have postponed.
  -- This is undesirable as we want set builder notation to quickly elaborate to a `Set` when no
  -- expected type is available.
  -- tryPostponeIfNoneOrMVar expectedType?
  match expectedType? with
  | some expectedType =>
    match_expr expectedType with
    -- If the expected type is known to be `Finset ?α`, return `true`.
    | Finset _ => pure true
    -- If the expected type is known to be `Set ?α`, give up.
    | Set _ => throwUnsupportedSyntax
    -- If the expected type is known to not be `Finset ?α` or `Set ?α`, return `false`.
    | _ => pure false
  -- If the expected type is not known, return `false`.
  | none => pure false

/-- Elaborate set builder notation for `Finset`.

`{x ∈ s | p x}` is elaborated as `Finset.filter (fun x ↦ p x) s` if either the expected type is
`Finset ?α` or the expected type is not `Set ?α` and `s` has expected type `Finset ?α`.

See also
* `Data.Set.Defs` for the `Set` builder notation elaborator that this elaborator partly overrides.
* `Data.Fintype.Basic` for the `Finset` builder notation elaborator handling syntax of the form
  `{x | p x}`, `{x : α | p x}`, `{x ∉ s | p x}`, `{x ≠ a | p x}`.
* `Order.LocallyFinite.Basic` for the `Finset` builder notation elaborator handling syntax of the
  form `{x ≤ a | p x}`, `{x ≥ a | p x}`, `{x < a | p x}`, `{x > a | p x}`.

TODO: Write a delaborator
-/
@[term_elab setBuilder]
def elabFinsetBuilderSep : TermElab
  | `({ $x:ident ∈ $s:term | $p }), expectedType? => do
    -- If the expected type is known to be `Set ?α`, give up. If it is not known to be `Set ?α` or
    -- `Finset ?α`, check the expected type of `s`.
    unless ← knownToBeFinsetNotSet expectedType? do
      let ty ← try whnfR (← inferType (← elabTerm s none)) catch _ => throwUnsupportedSyntax
      -- If the expected type of `s` is not known to be `Finset ?α`, give up.
      match_expr ty with
      | Finset _ => pure ()
      | _ => throwUnsupportedSyntax
    -- Finally, we can elaborate the syntax as a finset.
    -- TODO: Seems a bit wasteful to have computed the expected type but still use `expectedType?`.
    elabTerm (← `(Finset.filter (fun $x:ident ↦ $p) $s)) expectedType?
  | _, _ => throwUnsupportedSyntax

end Mathlib.Meta

namespace Finset
section Filter
variable (p q : α → Prop) [DecidablePred p] [DecidablePred q] {s t : Finset α}

@[simp]
theorem filter_val (s : Finset α) : (filter p s).1 = s.1.filter p :=
  rfl

@[simp]
theorem filter_subset (s : Finset α) : s.filter p ⊆ s :=
  Multiset.filter_subset _ _

variable {p}

@[simp, grind =]
theorem mem_filter {s : Finset α} {a : α} : a ∈ s.filter p ↔ a ∈ s ∧ p a :=
  Multiset.mem_filter

theorem mem_of_mem_filter {s : Finset α} (x : α) (h : x ∈ s.filter p) : x ∈ s :=
  Multiset.mem_of_mem_filter h

theorem filter_ssubset {s : Finset α} : s.filter p ⊂ s ↔ ∃ x ∈ s, ¬p x := by grind

variable (p)

theorem filter_filter (s : Finset α) : (s.filter p).filter q = s.filter fun a => p a ∧ q a := by
  grind

theorem filter_comm (s : Finset α) : (s.filter p).filter q = (s.filter q).filter p := by
  grind

-- We can replace an application of filter where the decidability is inferred in "the wrong way".
theorem filter_congr_decidable (s : Finset α) (p : α → Prop) (h : DecidablePred p)
    [DecidablePred p] : @filter α p h s = s.filter p := by congr

@[simp]
theorem filter_true {h} (s : Finset α) : @filter _ (fun _ => True) h s = s := by ext; simp

@[deprecated (since := "2025-08-24")] alias filter_True := filter_true

@[simp]
theorem filter_false {h} (s : Finset α) : @filter _ (fun _ => False) h s = ∅ := by ext; simp

@[deprecated (since := "2025-08-24")] alias filter_False := filter_false

variable {p q}

@[simp]
lemma filter_eq_self : s.filter p = s ↔ ∀ x ∈ s, p x := by simp [Finset.ext_iff]

@[simp]
theorem filter_eq_empty_iff : s.filter p = ∅ ↔ ∀ ⦃x⦄, x ∈ s → ¬p x := by simp [Finset.ext_iff]

theorem filter_nonempty_iff : (s.filter p).Nonempty ↔ ∃ a ∈ s, p a := by
  simp only [nonempty_iff_ne_empty, Ne, filter_eq_empty_iff, Classical.not_not, not_forall,
    exists_prop]

/-- If all elements of a `Finset` satisfy the predicate `p`, `s.filter p` is `s`. -/
theorem filter_true_of_mem (h : ∀ x ∈ s, p x) : s.filter p = s := filter_eq_self.2 h

/-- If all elements of a `Finset` fail to satisfy the predicate `p`, `s.filter p` is `∅`. -/
theorem filter_false_of_mem (h : ∀ x ∈ s, ¬p x) : s.filter p = ∅ := filter_eq_empty_iff.2 h

@[simp]
theorem filter_const (p : Prop) [Decidable p] (s : Finset α) :
    (s.filter fun _a => p) = if p then s else ∅ := by split_ifs <;> simp [*]

theorem filter_congr {s : Finset α} (H : ∀ x ∈ s, p x ↔ q x) : filter p s = filter q s :=
  eq_of_veq <| Multiset.filter_congr H

variable (p q)

@[simp]
theorem filter_empty : filter p ∅ = ∅ :=
  subset_empty.1 <| filter_subset _ _

@[gcongr]
theorem filter_subset_filter {s t : Finset α} (h : s ⊆ t) : s.filter p ⊆ t.filter p := fun _a ha =>
  mem_filter.2 ⟨h (mem_filter.1 ha).1, (mem_filter.1 ha).2⟩

theorem monotone_filter_left : Monotone (filter p) := fun _ _ => filter_subset_filter p

@[gcongr]
theorem monotone_filter_right (s : Finset α) ⦃p q : α → Prop⦄ [DecidablePred p] [DecidablePred q]
    (h : ∀ a ∈ s, p a → q a) : s.filter p ⊆ s.filter q := by simp +contextual [subset_iff, h]

@[simp, norm_cast]
theorem coe_filter (s : Finset α) : ↑(s.filter p) = ({ x ∈ ↑s | p x } : Set α) :=
  Set.ext fun _ => mem_filter

theorem subset_coe_filter_of_subset_forall (s : Finset α) {t : Set α} (h₁ : t ⊆ s)
    (h₂ : ∀ x ∈ t, p x) : t ⊆ s.filter p := fun x hx => (s.coe_filter p).symm ▸ ⟨h₁ hx, h₂ x hx⟩

theorem disjoint_filter_filter {s t : Finset α}
    {p q : α → Prop} [DecidablePred p] [DecidablePred q] :
    Disjoint s t → Disjoint (s.filter p) (t.filter q) :=
  Disjoint.mono (filter_subset _ _) (filter_subset _ _)

lemma _root_.Set.pairwiseDisjoint_filter [DecidableEq β] (f : α → β) (s : Set β) (t : Finset α) :
    s.PairwiseDisjoint fun x ↦ t.filter (f · = x) := by
  rintro i - j - h u hi hj x hx
  obtain ⟨-, rfl⟩ : x ∈ t ∧ f x = i := by simpa using hi hx
  obtain ⟨-, rfl⟩ : x ∈ t ∧ f x = j := by simpa using hj hx
  contradiction

theorem disjoint_filter_and_not_filter :
    Disjoint (s.filter (fun x ↦ p x ∧ ¬q x)) (s.filter (fun x ↦ q x ∧ ¬p x)) := by
  intro _ htp htq
  simp only [bot_eq_empty, le_eq_subset, subset_empty, ← not_nonempty_iff_eq_empty]
  rintro ⟨_, hx⟩
  exact (mem_filter.mp (htq hx)).2.2 (mem_filter.mp (htp hx)).2.1

variable {p q}

lemma filter_inj : s.filter p = t.filter p ↔ ∀ ⦃a⦄, p a → (a ∈ s ↔ a ∈ t) := by
  simp [Finset.ext_iff]

lemma filter_inj' : s.filter p = s.filter q ↔ ∀ ⦃a⦄, a ∈ s → (p a ↔ q a) := by
  simp [Finset.ext_iff]

end Filter

end Finset
