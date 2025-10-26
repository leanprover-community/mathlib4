/-
Copyright (c) 2025 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Invariant.Basic

/-!
# Predicate for Galois Groups

Given an action of a group `G` on an extension of fields `L/K`, we introduce a predicate
`IsGaloisGroup G K L` saying that `G` acts faithfully on `L` with fixed field `K`. In particular,
we do not assume that `L` is an algebraic extension of `K`.
-/

section CommRing

variable (G A B : Type*) [Group G] [CommSemiring A] [Semiring B] [Algebra A B]
  [MulSemiringAction G B]

/-- `G` is a Galois group for `L/K` if the action on `L` is faithful with fixed field `K`.
In particular, we do not assume that `L` is an algebraic extension of `K`. -/
class IsGaloisGroup where
  faithful : FaithfulSMul G B
  commutes : SMulCommClass G A B
  isInvariant : Algebra.IsInvariant A B G

attribute [instance low] IsGaloisGroup.commutes IsGaloisGroup.isInvariant

end CommRing

section Field

variable (G A B K L : Type*) [Group G] [CommRing A] [CommRing B] [MulSemiringAction G B]
  [Algebra A B] [Field K] [Field L] [Algebra K L] [Algebra A K] [Algebra B L] [Algebra A L]
  [IsFractionRing A K] [IsFractionRing B L] [IsScalarTower A K L] [IsScalarTower A B L]
  [MulSemiringAction G L] [IsScalarTower G B L]

theorem IsGaloisGroup.toIsFractionRing [Finite G] [hGAB : IsGaloisGroup G A B] :
    IsGaloisGroup G K L := by
  have hc (a : A) : (algebraMap K L) (algebraMap A K a) = (algebraMap B L) (algebraMap A B a) := by
    simp only [← IsScalarTower.algebraMap_apply]
  refine ⟨⟨fun h ↦ ?_⟩, ⟨fun g x y ↦ ?_⟩, ⟨fun x h ↦ ?_⟩⟩
  · have := hGAB.faithful
    exact eq_of_smul_eq_smul fun y ↦ by simpa [← algebraMap.coe_smul] using h (algebraMap B L y)
  · obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) x
    obtain ⟨c, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := B) y
    simp_rw [Algebra.smul_def, smul_mul', map_div₀, smul_div₀', hc,
      ← algebraMap.coe_smul, smul_algebraMap]
  · have := hGAB.isInvariant.isIntegral
    have : Nontrivial A := (IsFractionRing.nontrivial_iff_nontrivial A K).mpr inferInstance
    have : Nontrivial B := (IsFractionRing.nontrivial_iff_nontrivial B L).mpr inferInstance
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := B) x
    have hy' : algebraMap B L y ≠ 0 := by simpa using nonZeroDivisors.ne_zero hy
    obtain ⟨b, a, ha, hb⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := A) y).exists_smul_eq_mul x hy
    rw [mul_comm, Algebra.smul_def, mul_comm] at hb
    replace ha : (algebraMap B L) (algebraMap A B a) ≠ 0 := by simpa [← hc]
    have hxy : algebraMap B L x / algebraMap B L y =
      algebraMap B L b / algebraMap B L (algebraMap A B a) := by
      rw [div_eq_div_iff hy' ha, ← map_mul, hb, map_mul]
    simp only [hxy, smul_div₀', ← algebraMap.coe_smul, smul_algebraMap, div_left_inj' ha,
      IsFractionRing.coe_inj] at h
    obtain ⟨b, rfl⟩ := hGAB.isInvariant.isInvariant b h
    use algebraMap A K b / algebraMap A K a
    simp only [map_div₀, hc]
    rw [div_eq_div_iff ha hy', ← map_mul, ← map_mul, hb]

end Field

variable (G H K L : Type*) [Group G] [Group H] [Field K] [Field L] [Algebra K L]
  [MulSemiringAction G L] [MulSemiringAction H L]

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

/-- If `L/K` is a finite Galois extension, then `Gal(L/K)` is a Galois group for `L/K`. -/
instance of_isGalois [FiniteDimensional K L] [IsGalois K L] : IsGaloisGroup Gal(L/K) K L where
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
    have : FiniteDimensional K L := FiniteDimensional.of_finrank_pos (Nat.zero_lt_of_ne_zero hG)
    exact Finite.of_injective (MulSemiringAction.toAlgAut G K L)
      (fun _ _ ↦ (faithful K).eq_of_smul_eq_smul ∘ DFunLike.ext_iff.mp)

theorem finiteDimensional [Finite G] [IsGaloisGroup G K L] : FiniteDimensional K L :=
  FiniteDimensional.of_finrank_pos (card_eq_finrank G K L ▸ Nat.card_pos)

/-- If `G` is a finite Galois group for `L/K`, then `G` is isomorphic to `Gal(L/K)`. -/
@[simps!] noncomputable def mulEquivAlgEquiv [IsGaloisGroup G K L] [Finite G] : G ≃* Gal(L/K) :=
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

end IsGaloisGroup
