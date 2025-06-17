/-
Copyright (c) 2025 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Invariant.Defs

/-!
# Predicate for Galois Groups

Give an action of a group `G` on an extension of fields `L/K`, we introduce a predicate
`IsGaloisGroup G K L`.
-/

variable (G K L : Type*) [Group G] [Field K] [Field L] [Algebra K L] [MulSemiringAction G L]

/-- `G` is a Galois group for `L/K` if the action on `L` is faithful with fixed field `K`. -/
class IsGaloisGroup where
  faithful : FaithfulSMul G L
  commutes : SMulCommClass G K L
  isInvariant : Algebra.IsInvariant K L G

namespace IsGaloisGroup

instance [h : IsGaloisGroup G K L] : SMulCommClass G K L := h.commutes

instance [h : IsGaloisGroup G K L] : Algebra.IsInvariant K L G := h.isInvariant

theorem fixedPoints_eq_bot [IsGaloisGroup G K L] :
    FixedPoints.intermediateField G = (⊥ : IntermediateField K L) := by
  rw [eq_bot_iff]
  exact Algebra.IsInvariant.isInvariant

/-- If `G` is a Galois group for `L/K`, then `L/K` is a Galois extension. -/
theorem isGalois [Finite G] [IsGaloisGroup G K L] : IsGalois K L := by
  rw [← isGalois_iff_isGalois_bot, ← fixedPoints_eq_bot G]
  exact IsGalois.of_fixed_field L G

/-- If `L/K` is a Galois extension, then `L ≃ₐ[K] L` is a Galois group for `L/K`. -/
theorem of_isGalois [FiniteDimensional K L] [IsGalois K L] : IsGaloisGroup (L ≃ₐ[K] L) K L where
  faithful := inferInstance
  commutes := inferInstance
  isInvariant := ⟨fun x ↦ (IsGalois.mem_bot_iff_fixed x).mpr⟩

theorem card_eq_finrank [Finite G] [IsGaloisGroup G K L] : Nat.card G = Module.finrank K L := by
  have : Fintype G := Fintype.ofFinite G
  have : FaithfulSMul G L := IsGaloisGroup.faithful K
  rw [← IntermediateField.finrank_bot', ← fixedPoints_eq_bot G, Nat.card_eq_fintype_card]
  exact (FixedPoints.finrank_eq_card G L).symm

end IsGaloisGroup
