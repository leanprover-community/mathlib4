/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.WellFounded

/-!
# Minimising arguments for functions taking values in ordered codomains

Given a type `β` carrying a well-founded `<` relation, and a function `f : α → β`, an argmin for `f`
is a value `a : α` whose value under `f` is minimal in the sense of `Function.not_lt_argmin`.

## Main definitions:
 * `Function.argmin`: an argmin of a function `f : α → β` where `β` carries a well-founded `<`
 * `Function.argminOn`: an argmin of a function `f : α → β` restricted to `s : Set α`, where `β`
   carries a well-founded `<`
 * `Finite.argmin`: a convenience variation of `Function.argmin` where `α` is finite and the
   well-founded assumption on `<` is dropped
 * `Finite.argminOn`: a convenience variation of `Function.argminOn` where `α` is finite and the
   well-founded assumption on `<` is dropped

-/

@[expose] public section

noncomputable section

variable {α β : Type*} (f : α → β)

namespace Function

section LT

variable [LT β] [WellFoundedLT β]

/-- Given a function `f : α → β` where `β` carries a well-founded `<`, this is an element of `α`
whose image under `f` is minimal in the sense of `Function.not_lt_argmin`.

See also `Finite.argmin`. -/
def argmin [Nonempty α] : α :=
  WellFounded.min (InvImage.wf f wellFounded_lt) Set.univ Set.univ_nonempty

theorem not_lt_argmin [Nonempty α] (a : α) : ¬f a < f (argmin f) :=
  WellFounded.not_lt_min (InvImage.wf f wellFounded_lt) _ _ (Set.mem_univ a)

/-- Given a function `f : α → β` where `β` carries a well-founded `<`, and a non-empty subset `s`
of `α`, this is an element of `s` whose image under `f` is minimal in the sense of
`Function.not_lt_argminOn`.

See also `Finite.argminOn`. -/
def argminOn (s : Set α) (hs : s.Nonempty) : α :=
  WellFounded.min (InvImage.wf f wellFounded_lt) s hs

@[simp]
theorem argminOn_mem (s : Set α) (hs : s.Nonempty) : argminOn f s hs ∈ s :=
  WellFounded.min_mem _ _ _

theorem not_lt_argminOn (s : Set α) {a : α} (ha : a ∈ s)
    (hs : s.Nonempty := Set.nonempty_of_mem ha) : ¬f a < f (argminOn f s hs) :=
  WellFounded.not_lt_min (InvImage.wf f wellFounded_lt) s hs ha

end LT

section LinearOrder

variable [LinearOrder β] [WellFoundedLT β]

theorem argmin_le (a : α) [Nonempty α] : f (argmin f) ≤ f a :=
  not_lt.mp <| not_lt_argmin f a

theorem argminOn_le (s : Set α) {a : α} (ha : a ∈ s) (hs : s.Nonempty := Set.nonempty_of_mem ha) :
    f (argminOn f s hs) ≤ f a :=
  not_lt.mp <| not_lt_argminOn f s ha hs

end LinearOrder

theorem sInf_eq_argmin_on [ConditionallyCompleteLinearOrder α] [WellFoundedLT α]
    {s : Set α} (hs : s.Nonempty) : sInf s = argminOn id s hs :=
  IsLeast.csInf_eq ⟨argminOn_mem _ _ _, fun _ ha => argminOn_le id _ ha⟩

end Function

namespace Finite

variable [Finite α]

section Preorder

variable [Preorder β]

/-- A convenience variation of `Function.argmin` where `α` is finite and the well-founded
assumption on `<` is dropped. -/
def argmin [Nonempty α] : α :=
  (Set.rangeFactorization f).argmin

theorem not_lt_argmin (a : α) :
    have : Nonempty α := ⟨a⟩
    ¬ f a < f (argmin f) := by
  have : Nonempty α := ⟨a⟩
  simpa [← Subtype.coe_lt_coe] using Function.not_lt_argmin (Set.rangeFactorization f) a

/-- A convenience variation of `Function.argminOn` where `α` is finite and the well-founded
assumption on `<` is dropped. -/
def argminOn (s : Set α) (hs : s.Nonempty) : α :=
  (Set.rangeFactorization f).argminOn s hs

@[simp]
theorem argminOn_mem (s : Set α) (hs : s.Nonempty) : argminOn f s hs ∈ s := by
  simp [argminOn]

theorem not_lt_argminOn (s : Set α) {a : α} (ha : a ∈ s)
    (hs : s.Nonempty := Set.nonempty_of_mem ha) : ¬f a < f (argminOn f s hs) :=
  (Set.rangeFactorization f).not_lt_argminOn s ha

end Preorder

section LinearOrder

variable [LinearOrder β]

theorem argmin_le (a : α) :
    have : Nonempty α := ⟨a⟩
    f (argmin f) ≤ f a :=
  not_lt.mp <| not_lt_argmin f a

theorem argminOn_le (s : Set α) {a : α} (ha : a ∈ s) (hs : s.Nonempty := Set.nonempty_of_mem ha) :
    f (argminOn f s hs) ≤ f a :=
  (Set.rangeFactorization f).argminOn_le s ha hs

end LinearOrder

end Finite

/-- A convenience variation of `Finite.argminOn` for finite (sub)sets of a not-necessarily-finite
ambient type. -/
abbrev Set.Finite.argminOn [Preorder β] (s : Set α) (hs₀ : s.Finite) (hs : s.Nonempty) : α :=
  have : Finite s := hs₀.to_subtype
  have : Nonempty s := Set.nonempty_coe_sort.mpr hs
  (_root_.Finite.argminOn (s.restrict f) Set.univ (by simp)).val
