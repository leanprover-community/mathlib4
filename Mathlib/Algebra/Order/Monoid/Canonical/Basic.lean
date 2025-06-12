/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Extra lemmas about canonically ordered monoids
-/

namespace Finset
variable {ι α : Type*} [AddCommMonoid α] [LinearOrder α] [OrderBot α] [CanonicallyOrderedAdd α]
  {s : Finset ι} {f : ι → α}

@[simp] lemma sup_eq_zero : s.sup f = 0 ↔ ∀ i ∈ s, f i = 0 := by simp [← bot_eq_zero']
@[simp] lemma sup'_eq_zero (hs) : s.sup' hs f = 0 ↔ ∀ i ∈ s, f i = 0 := by simp [sup'_eq_sup]

end Finset
