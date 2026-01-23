/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Extra lemmas about canonically ordered monoids
-/

public section

namespace Finset
variable {ι α : Type*} [AddCommMonoid α] [LinearOrder α] [OrderBot α] [CanonicallyOrderedAdd α]
  {s : Finset ι} {f : ι → α}

@[simp] lemma sup_eq_zero : s.sup f = 0 ↔ ∀ i ∈ s, f i = 0 := by simp [← bot_eq_zero']
@[simp] lemma sup'_eq_zero (hs) : s.sup' hs f = 0 ↔ ∀ i ∈ s, f i = 0 := by simp [sup'_eq_sup]

end Finset

namespace Set
variable {α : Type*} [AddCommMonoid α] [PartialOrder α] [CanonicallyOrderedAdd α]
  [Sub α] [OrderedSub α] {β : Type*} {f : α → β} {k : α}

theorem range_add_eq_image_Ici : range (fun x ↦ f (x + k)) = f '' Ici k :=
  Set.ext fun x ↦ ⟨fun ⟨y, hfy⟩ ↦ ⟨y + k, self_le_add_left k y, hfy⟩,
    fun ⟨y, hy, hfy⟩ ↦ ⟨y - k, by simpa [tsub_add_cancel_of_le hy] using hfy⟩⟩

end Set
