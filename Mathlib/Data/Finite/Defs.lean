/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Data.Set.CoeSort
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Util.AssertExists
public import Mathlib.Data.Nat.Notation

/-!
# Definition of the `Finite` typeclass

This file defines a typeclass `Finite` saying that `α : Sort*` is finite. A type is `Finite` if it
is equivalent to `Fin n` for some `n`. We also define `Infinite α` as a typeclass equivalent to
`¬Finite α`.

The `Finite` predicate has no computational relevance and, being `Prop`-valued, gets to enjoy proof
irrelevance -- it represents the mere fact that the type is finite.  While the `Finite` class also
represents finiteness of a type, a key difference is that a `Fintype` instance represents finiteness
in a computable way: it gives a concrete algorithm to produce a `Finset` whose elements enumerate
the terms of the given type. As such, one generally relies on congruence lemmas when rewriting
expressions involving `Fintype` instances.

Every `Fintype` instance automatically gives a `Finite` instance, see `Fintype.finite`, but not vice
versa. Every `Fintype` instance should be computable since they are meant for computation. If it's
not possible to write a computable `Fintype` instance, one should prefer writing a `Finite` instance
instead.

## Main definitions

* `Finite α` denotes that `α` is a finite type.
* `Infinite α` denotes that `α` is an infinite type.
* `Set.Finite : Set α → Prop`
* `Set.Infinite : Set α → Prop`
* `Set.toFinite` to prove `Set.Finite` for a `Set` from a `Finite` instance.

## Implementation notes

This file defines both the type-level `Finite` class and the set-level `Set.Finite` definition.

The definition of `Finite α` is not just `Nonempty (Fintype α)` since `Fintype` requires
that `α : Type*`, and the definition in this module allows for `α : Sort*`. This means
we can write the instance `Finite.prop`.

A finite set is defined to be a set whose coercion to a type has a `Finite` instance.

There are two components to finiteness constructions. The first is `Fintype` instances for each
construction. This gives a way to actually compute a `Finset` that represents the set, and these
may be accessed using `set.toFinset`. This gets the `Finset` in the correct form, since otherwise
`Finset.univ : Finset s` is a `Finset` for the subtype for `s`. The second component is
"constructors" for `Set.Finite` that give proofs that `Fintype` instances exist classically given
other `Set.Finite` proofs. Unlike the `Fintype` instances, these *do not* use any decidability
instances since they do not compute anything.

## Tags

finite, fintype, finite sets
-/

@[expose] public section

assert_not_exists Finset MonoidWithZero IsOrderedRing

universe u v

open Function

variable {α β : Sort*}

/-- A type is `Finite` if it is in bijective correspondence to some `Fin n`.

This is similar to `Fintype`, but `Finite` is a proposition rather than data.
A particular benefit to this is that `Finite` instances are definitionally equal to one another
(due to proof irrelevance) rather than being merely propositionally equal,
and, furthermore, `Finite` instances generally avoid the need for `Decidable` instances.
One other notable difference is that `Finite` allows there to be `Finite p` instances
for all `p : Prop`, which is not allowed by `Fintype` due to universe constraints.
An application of this is that `Finite (x ∈ s → β x)` follows from the general instance for pi
types, assuming `[∀ x, Finite (β x)]`.
Implementation note: this is a reason `Finite α` is not defined as `Nonempty (Fintype α)`.

Every `Fintype` instance provides a `Finite` instance via `Finite.of_fintype`.
Conversely, one can noncomputably create a `Fintype` instance from a `Finite` instance
via `Fintype.ofFinite`. In a proof one might write
```lean
  have := Fintype.ofFinite α
```
to obtain such an instance.

Do not write noncomputable `Fintype` instances; instead write `Finite` instances
and use this `Fintype.ofFinite` interface.
The `Fintype` instances should be relied upon to be computable for evaluation purposes.

Theorems should use `Finite` instead of `Fintype`, unless definitions in the theorem statement
require `Fintype`.
Definitions should prefer `Finite` as well, unless it is important that the definitions
are meant to be computable in the reduction or `#eval` sense.
-/
class inductive Finite (α : Sort*) : Prop
  | intro {n : ℕ} : α ≃ Fin n → Finite _

theorem finite_iff_exists_equiv_fin {α : Sort*} : Finite α ↔ ∃ n, Nonempty (α ≃ Fin n) :=
  ⟨fun ⟨e⟩ => ⟨_, ⟨e⟩⟩, fun ⟨_, ⟨e⟩⟩ => ⟨e⟩⟩

theorem Finite.exists_equiv_fin (α : Sort*) [h : Finite α] : ∃ n : ℕ, Nonempty (α ≃ Fin n) :=
  finite_iff_exists_equiv_fin.mp h

theorem Finite.of_equiv (α : Sort*) [h : Finite α] (f : α ≃ β) : Finite β :=
  let ⟨e⟩ := h; ⟨f.symm.trans e⟩

theorem Equiv.finite_iff (f : α ≃ β) : Finite α ↔ Finite β :=
  ⟨fun _ => Finite.of_equiv _ f, fun _ => Finite.of_equiv _ f.symm⟩

theorem Function.Bijective.finite_iff {f : α → β} (h : Bijective f) : Finite α ↔ Finite β :=
  (Equiv.ofBijective f h).finite_iff

theorem Finite.ofBijective [Finite α] {f : α → β} (h : Bijective f) : Finite β :=
  h.finite_iff.mp ‹_›

variable (α) in
theorem Finite.nonempty_decidableEq [Finite α] : Nonempty (DecidableEq α) :=
  let ⟨_n, ⟨e⟩⟩ := Finite.exists_equiv_fin α; ⟨e.decidableEq⟩

instance [Finite α] : Finite (PLift α) :=
  Finite.of_equiv α Equiv.plift.symm

instance {α : Type v} [Finite α] : Finite (ULift.{u} α) :=
  Finite.of_equiv α Equiv.ulift.symm

/-- A type is said to be infinite if it is not finite. Note that `Infinite α` is equivalent to
`IsEmpty (Fintype α)` or `IsEmpty (Finite α)`. -/
class Infinite (α : Sort*) : Prop where
  /-- assertion that `α` is `¬Finite` -/
  not_finite : ¬Finite α

@[simp, push]
theorem not_finite_iff_infinite : ¬Finite α ↔ Infinite α :=
  ⟨Infinite.mk, fun h => h.1⟩

@[simp, push]
theorem not_infinite_iff_finite : ¬Infinite α ↔ Finite α :=
  not_finite_iff_infinite.not_right.symm

theorem Equiv.infinite_iff (e : α ≃ β) : Infinite α ↔ Infinite β :=
  not_finite_iff_infinite.symm.trans <| e.finite_iff.not.trans not_finite_iff_infinite

instance [Infinite α] : Infinite (PLift α) :=
  Equiv.plift.infinite_iff.2 ‹_›

instance {α : Type v} [Infinite α] : Infinite (ULift.{u} α) :=
  Equiv.ulift.infinite_iff.2 ‹_›

theorem finite_or_infinite (α : Sort*) : Finite α ∨ Infinite α :=
  or_iff_not_imp_left.2 not_finite_iff_infinite.1

/-- `Infinite α` is not `Finite` -/
theorem not_finite (α : Sort*) [Infinite α] [Finite α] : False :=
  @Infinite.not_finite α ‹_› ‹_›

protected theorem Finite.false [Infinite α] (_ : Finite α) : False :=
  not_finite α

protected theorem Infinite.false [Finite α] (_ : Infinite α) : False :=
  @Infinite.not_finite α ‹_› ‹_›

alias ⟨Finite.of_not_infinite, Finite.not_infinite⟩ := not_infinite_iff_finite

instance Bool.instFinite : Finite Bool := .intro finTwoEquiv.symm
instance Prop.instFinite : Finite Prop := .of_equiv _ Equiv.propEquivBool.symm

section Set

/-!
### Finite sets
-/

variable {α : Type u} {β : Type v}

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

@[simp, push]
theorem not_finite {s : Set α} : ¬s.Finite ↔ s.Infinite := .rfl

@[simp, push]
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

alias ⟨_, Infinite.to_subtype⟩ := infinite_coe_iff

end Set

end Set
