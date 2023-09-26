/-
Copyright (c) 2023 Matthias Uschold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Uschold
-/
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Data.Real.ENNReal

universe u v
variable (M : Type u) (α : Type v) [Monoid M] [MulAction M α]

structure mean where
  μ : Set α  → ENNReal
  norm : μ Set.univ = 1
  fin_add : ∀ (X Y : Set α), Disjoint X Y
            → μ (X ∪ Y) = μ X + μ Y

@[coe]
instance : Coe (mean α) (Set α → ENNReal) where
  coe := mean.μ

structure invariant_mean extends mean α where
  invariance: ∀ (A: Set α), ∀ (g: M),
      μ ((λ (x:α) => g•x) '' A) = μ A

example (m : invariant_mean M α ) (A: Set α )
  : ENNReal
  := m.μ A

def amenable : Prop
  := Nonempty (invariant_mean M α)

noncomputable def invmean_of_amenable (h: amenable M α)
  : invariant_mean M α
  := Classical.choice h
