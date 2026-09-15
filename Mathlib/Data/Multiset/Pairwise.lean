/-
Copyright (c) 2025 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Data.List.Pairwise
public import Mathlib.Data.Multiset.Basic

/-!
# Pairwise relations on a multiset

This file provides basic results about `Multiset.Pairwise` (definitions are in
`Mathlib/Data/Multiset/Defs.lean`).
-/

@[expose] public section

namespace Multiset

variable {α : Type*} {r : α → α → Prop} {s : Multiset α} [Std.Symm r]

theorem Pairwise.forall (hs : s.Pairwise r) : ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → a ≠ b → r a b :=
  have h : List.Pairwise r s.toList := by grind [pairwise_coe_iff, coe_toList]
  fun a ha b hb => List.Pairwise.forall h (by simp [ha]) (by simp [hb])

instance instDecidablePairwise [DecidableRel r] : Decidable (s.Pairwise r) :=
  s.recOnSubsingleton (fun l ↦ (inferInstance : Decidable (l.Pairwise r)))

end Multiset
