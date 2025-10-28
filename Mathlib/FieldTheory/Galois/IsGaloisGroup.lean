/-
Copyright (c) 2025 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Invariant.Defs

/-!
# Predicate for Galois Groups

Given an action of a group `G` on an extension of fields `L/K`, we introduce a predicate
`IsGaloisGroup G K L` saying that `G` acts faithfully on `L` with fixed field `K`. In particular,
we do not assume that `L` is an algebraic extension of `K`.
-/

variable (G H K L : Type*) [Group G] [Group H] [Field K] [Field L] [Algebra K L]
  [MulSemiringAction G L] [MulSemiringAction H L]

/-- `G` is a Galois group for `L/K` if the action on `L` is faithful with fixed field `K`.
In particular, we do not assume that `L` is an algebraic extension of `K`. -/
class IsGaloisGroup where
  faithful : FaithfulSMul G L
  commutes : SMulCommClass G K L
  isInvariant : Algebra.IsInvariant K L G

namespace IsGaloisGroup

attribute [instance low] commutes isInvariant

theorem fixedPoints_eq_bot [IsGaloisGroup G K L] :
    FixedPoints.intermediateField G = (⊥ : IntermediateField K L) := by
  rw [eq_bot_iff]
  exact Algebra.IsInvariant.isInvariant

/-- If `G` is a finite Galois group for `L/K`, then `L/K` is a Galois extension. -/
theorem isGalois [Finite G] [IsGaloisGroup G K L] : IsGalois K L := by
  rw [← isGalois_iff_isGalois_bot, ← fixedPoints_eq_bot G]
  exact IsGalois.of_fixed_field L G

/-- If `L/K` is a finite Galois extension, then `L ≃ₐ[K] L` is a Galois group for `L/K`. -/
instance of_isGalois [FiniteDimensional K L] [IsGalois K L] : IsGaloisGroup (L ≃ₐ[K] L) K L where
  faithful := inferInstance
  commutes := inferInstance
  isInvariant := ⟨fun x ↦ (IsGalois.mem_bot_iff_fixed x).mpr⟩

theorem card_eq_finrank [Finite G] [IsGaloisGroup G K L] : Nat.card G = Module.finrank K L := by
  have : Fintype G := Fintype.ofFinite G
  have : FaithfulSMul G L := faithful K
  rw [← IntermediateField.finrank_bot', ← fixedPoints_eq_bot G, Nat.card_eq_fintype_card]
  exact (FixedPoints.finrank_eq_card G L).symm

theorem finiteDimensional [Finite G] [IsGaloisGroup G K L] : FiniteDimensional K L :=
  FiniteDimensional.of_finrank_pos (card_eq_finrank G K L ▸ Nat.card_pos)

/-- If `G` is a finite Galois group for `L/K`, then `G` is isomorphic to `L ≃ₐ[K] L`. -/
@[simps!] noncomputable def mulEquivAlgEquiv [IsGaloisGroup G K L] [Finite G] : G ≃* (L ≃ₐ[K] L) :=
  MulEquiv.ofBijective (MulSemiringAction.toAlgAut G K L) (by
    have := isGalois G K L
    have := finiteDimensional G K L
    rw [Nat.bijective_iff_injective_and_card, card_eq_finrank G K L,
      Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank K L]
    exact ⟨fun _ _ ↦ (faithful K).eq_of_smul_eq_smul ∘ DFunLike.ext_iff.mp, rfl⟩)

/-- If `G` and `H` are finite Galois groups for `L/K`, then `G` is isomorphic to `H`. -/
noncomputable def mulEquivCongr [IsGaloisGroup G K L] [Finite G]
    [IsGaloisGroup H K L] [Finite H] : G ≃* H :=
  (mulEquivAlgEquiv G K L).trans (mulEquivAlgEquiv H K L).symm

@[simp]
theorem mulEquivCongr_apply_smul [IsGaloisGroup G K L] [Finite G] [IsGaloisGroup H K L] [Finite H]
    (g : G) (x : L) : mulEquivCongr G H K L g • x = g • x :=
  AlgEquiv.ext_iff.mp ((mulEquivAlgEquiv H K L).apply_symm_apply (mulEquivAlgEquiv G K L g)) x

end IsGaloisGroup
