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

theorem card_eq_finrank [IsGaloisGroup G K L] : Nat.card G = Module.finrank K L := by
  rcases fintypeOrInfinite G with _ | hG
  · have : FaithfulSMul G L := faithful K
    rw [← IntermediateField.finrank_bot', ← fixedPoints_eq_bot G, Nat.card_eq_fintype_card]
    exact (FixedPoints.finrank_eq_card G L).symm
  · rw [Nat.card_eq_zero_of_infinite, eq_comm]
    contrapose! hG
    rw [not_infinite_iff_finite]
    have : FiniteDimensional K L := FiniteDimensional.of_finrank_pos (Nat.zero_lt_of_ne_zero hG)
    exact Finite.of_injective (MulSemiringAction.toAlgAut G K L)
      (fun _ _ ↦ (faithful K).eq_of_smul_eq_smul ∘ DFunLike.ext_iff.mp)

theorem finiteDimensional [Finite G] [IsGaloisGroup G K L] : FiniteDimensional K L :=
  FiniteDimensional.of_finrank_pos (card_eq_finrank G K L ▸ Nat.card_pos)

/-- If `G` is a finite Galois group for `L/K`, then `G` is isomorphic to `L ≃ₐ[K] L`. -/
@[simps!] noncomputable def mulEquivAlgEquiv [IsGaloisGroup G K L] [Finite G] : G ≃* (L ≃ₐ[K] L) :=
  MulEquiv.ofBijective (MulSemiringAction.toAlgAut G K L) (by
    have := isGalois G K L
    have := finiteDimensional G K L
    rw [Nat.bijective_iff_injective_and_card, card_eq_finrank G K L,
      IsGalois.card_aut_eq_finrank K L]
    exact ⟨fun _ _ ↦ (faithful K).eq_of_smul_eq_smul ∘ DFunLike.ext_iff.mp, rfl⟩)

/-- If `G` and `H` are finite Galois groups for `L/K`, then `G` is isomorphic to `H`. -/
noncomputable def mulEquivCongr [IsGaloisGroup G K L] [Finite G]
    [IsGaloisGroup H K L] [Finite H] : G ≃* H :=
  (mulEquivAlgEquiv G K L).trans (mulEquivAlgEquiv H K L).symm

@[simp]
theorem mulEquivCongr_apply_smul [IsGaloisGroup G K L] [Finite G] [IsGaloisGroup H K L] [Finite H]
    (g : G) (x : L) : mulEquivCongr G H K L g • x = g • x :=
  AlgEquiv.ext_iff.mp ((mulEquivAlgEquiv H K L).apply_symm_apply (mulEquivAlgEquiv G K L g)) x

variable (H H' : Subgroup G) (F F' : IntermediateField K L)

instance to_subgroup [hGKL : IsGaloisGroup G K L] :
    IsGaloisGroup H (FixedPoints.intermediateField H : IntermediateField K L) L where
  faithful := have := hGKL.faithful; inferInstance
  commutes := ⟨fun g x y ↦ by simp_rw [IntermediateField.smul_def, smul_eq_mul, smul_mul', x.2 g]⟩
  isInvariant := ⟨fun x h ↦ ⟨⟨x, h⟩, rfl⟩⟩

theorem card_subgroup_eq_finrank_fixedpoints [IsGaloisGroup G K L] :
    Nat.card H = Module.finrank (FixedPoints.intermediateField H : IntermediateField K L) L :=
  card_eq_finrank H (FixedPoints.intermediateField H) L

instance to_intermediateField [Finite G] [hGKL : IsGaloisGroup G K L] :
    IsGaloisGroup (fixingSubgroup G (F : Set L)) F L where
  faithful := have := hGKL.faithful; inferInstance
  commutes := ⟨fun g x y ↦ by
    simp_rw [IntermediateField.smul_def, smul_eq_mul, smul_mul', Subgroup.smul_def, g.2 x]⟩
  isInvariant := ⟨fun x h ↦ ⟨⟨x, by
    have := hGKL.finiteDimensional
    have := hGKL.isGalois
    rw [← IsGalois.fixedField_fixingSubgroup F]
    exact fun ⟨g, hg⟩ ↦ (mulEquivCongr_apply_smul _ G K L g x).symm.trans
      (Subtype.forall.mp h _ (by simpa [mem_fixingSubgroup_iff] using hg))⟩, rfl⟩⟩

theorem card_fixingSubgroup_eq_finrank [Finite G] [IsGaloisGroup G K L] :
    Nat.card (fixingSubgroup G (F : Set L)) = Module.finrank F L :=
  card_eq_finrank (fixingSubgroup G (F : Set L)) F L

section GaloisCorrespondence

theorem fixingSubgroup_le_of_le (h : F ≤ F') :
    fixingSubgroup G (F' : Set L) ≤ fixingSubgroup G (F : Set L) :=
  fun _ hσ ⟨x, hx⟩ ↦ hσ ⟨x, h hx⟩

section SMulCommClass

variable [SMulCommClass G K L]

theorem fixingSubgroup_bot : fixingSubgroup G ((⊥ : IntermediateField K L) : Set L) = ⊤ := by
  simp [Subgroup.ext_iff, mem_fixingSubgroup_iff, IntermediateField.mem_bot]

theorem fixedPoints_bot :
    (FixedPoints.intermediateField (⊥ : Subgroup G) : IntermediateField K L) = ⊤ := by
  simp [IntermediateField.ext_iff]

theorem le_fixedPoints_iff_le_fixingSubgroup :
    F ≤ FixedPoints.intermediateField H ↔ H ≤ fixingSubgroup G (F : Set L) :=
  ⟨fun h g hg x ↦ h x.2 ⟨g, hg⟩, fun h x hx g ↦ h g.2 ⟨x, hx⟩⟩

theorem fixedPoints_le_of_le (h : H ≤ H') :
    FixedPoints.intermediateField H' ≤ (FixedPoints.intermediateField H : IntermediateField K L) :=
  fun _ hσ ⟨x, hx⟩ ↦ hσ ⟨x, h hx⟩

end SMulCommClass

section IsGaloisGroup

variable [hGKL : IsGaloisGroup G K L]

theorem fixingSubgroup_top : fixingSubgroup G ((⊤ : IntermediateField K L) : Set L) = ⊥ := by
  simp only [Subgroup.ext_iff, mem_fixingSubgroup_iff, Subgroup.mem_bot]
  exact fun x ↦ ⟨fun h ↦ hGKL.faithful.eq_of_smul_eq_smul (by simpa using h), fun h ↦ by simp [h]⟩

theorem fixedPoints_top :
    (FixedPoints.intermediateField (⊤ : Subgroup G) : IntermediateField K L) = ⊥ := by
  simp only [eq_bot_iff, SetLike.le_def, FixedPoints.mem_intermediateField_iff, Subtype.forall,
    Subgroup.mem_top, Subgroup.mk_smul, forall_const]
  exact hGKL.isInvariant.isInvariant

theorem fixingSubgroup_fixedPoints [Finite G] :
    fixingSubgroup G ((FixedPoints.intermediateField H : IntermediateField K L) : Set L) = H := by
  have : FiniteDimensional K L := hGKL.finiteDimensional
  refine (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
  · rw [← le_fixedPoints_iff_le_fixingSubgroup]
  · rw [hGKL.card_subgroup_eq_finrank_fixedpoints, hGKL.card_subgroup_eq_finrank_fixedpoints]
    apply IntermediateField.finrank_le_of_le_left
    rw [le_fixedPoints_iff_le_fixingSubgroup]

theorem fixedPoints_fixingSubgroup [Finite G] :
    FixedPoints.intermediateField (fixingSubgroup G (F : Set L)) = F := by
  have : FiniteDimensional K L := hGKL.finiteDimensional
  refine (IntermediateField.eq_of_le_of_finrank_eq' ?_ ?_).symm
  · rw [le_fixedPoints_iff_le_fixingSubgroup]
  · rw [← card_subgroup_eq_finrank_fixedpoints, card_fixingSubgroup_eq_finrank]

end IsGaloisGroup

end GaloisCorrespondence

end IsGaloisGroup
