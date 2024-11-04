/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kyle Miller
-/
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Set.Operations
import Mathlib.Tactic.Set
import Mathlib.Util.AssertExists

/-!
# Finite sets

This file defines predicates for finite and infinite sets.

## Main definitions

* `Set.Finite : Set α → Prop`
* `Set.Infinite : Set α → Prop`
* `Set.toFinite` to prove `Set.Finite` for a `Set` from a `Finite` instance.

## Implementation

A finite set is defined to be a set whose coercion to a type has a `Finite` instance.

There are two components to finiteness constructions. The first is `Fintype` instances for each
construction. This gives a way to actually compute a `Finset` that represents the set, and these
may be accessed using `set.toFinset`. This gets the `Finset` in the correct form, since otherwise
`Finset.univ : Finset s` is a `Finset` for the subtype for `s`. The second component is
"constructors" for `Set.Finite` that give proofs that `Fintype` instances exist classically given
other `Set.Finite` proofs. Unlike the `Fintype` instances, these *do not* use any decidability
instances since they do not compute anything.

## Tags

finite sets
-/

assert_not_exists Finset
assert_not_exists OrderedRing
assert_not_exists MonoidWithZero

open Set Function

universe u v w x

variable {α : Type u} {β : Type v} {ι : Sort w} {γ : Type x}

namespace Set

/-- A set is finite if the corresponding `Subtype` is finite,
i.e., if there exists a natural `n : ℕ` and an equivalence `s ≃ Fin n`. -/
protected def Finite (s : Set α) : Prop := Finite s

-- The `protected` attribute does not take effect within the same namespace block.
end Set

namespace Set

theorem finite_coe_iff {s : Set α} : Finite s ↔ s.Finite := .rfl

/-- Constructor for `Set.Finite` using a `Finite` instance. -/
theorem toFinite (s : Set α) [Finite s] : s.Finite := ‹_›

/-- Projection of `Set.Finite` to its `Finite` instance.
This is intended to be used with dot notation.
See also `Set.Finite.Fintype` and `Set.Finite.nonempty_fintype`. -/
protected theorem Finite.to_subtype {s : Set α} (h : s.Finite) : Finite s := h

/-- A set is infinite if it is not finite.

This is protected so that it does not conflict with global `Infinite`. -/
protected def Infinite (s : Set α) : Prop :=
  ¬s.Finite

@[simp]
theorem not_infinite {s : Set α} : ¬s.Infinite ↔ s.Finite :=
  not_not

alias ⟨_, Finite.not_infinite⟩ := not_infinite

attribute [simp] Finite.not_infinite

/-- See also `finite_or_infinite`, `fintypeOrInfinite`. -/
protected theorem finite_or_infinite (s : Set α) : s.Finite ∨ s.Infinite :=
  em _

protected theorem infinite_or_finite (s : Set α) : s.Infinite ∨ s.Finite :=
  em' _

end Set

theorem Equiv.set_finite_iff {s : Set α} {t : Set β} (hst : s ≃ t) : s.Finite ↔ t.Finite := by
  simp_rw [← Set.finite_coe_iff, hst.finite_iff]

namespace Set

/-! ### Infinite sets -/

variable {s t : Set α}

theorem infinite_coe_iff {s : Set α} : Infinite s ↔ s.Infinite :=
  not_finite_iff_infinite.symm.trans finite_coe_iff.not

-- Porting note: something weird happened here
alias ⟨_, Infinite.to_subtype⟩ := infinite_coe_iff

end Set
