/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.HeckeRing.Multiplication

/-!
# Hecke rings: the identity and the unital non-associative semiring

The identity double coset `(1 : HeckeCoset Δ H H)` gives the multiplicative identity of the
Hecke ring `𝕋 Δ H R`, following [Shimura][shimura1971], Chapter 3. This file proves that the
structure constants collapse to a single basis element on convolution by the identity, deduces
the unit laws `1 * f = f` and `f * 1 = f` of the convolution product of Hecke coset modules
(where the two identities live at the two different levels), and assembles the
`NonAssocSemiring (𝕋 Δ H R)` instance.

## Main results

* `HeckeCosetModule.one_def`: `(1 : 𝕋 Δ H R) = single R 1 1`.
* `HeckeCosetModule.one_mul'`, `HeckeCosetModule.mul_one'`: the identities of the diagonal
  Hecke rings are one-sided units for the convolution product of Hecke coset modules.
* the `NonAssocSemiring (𝕋 Δ H R)` instance.
-/

@[expose] public section

open DoubleCoset Finsupp
open scoped Pointwise

namespace HeckeCosetModule

variable {G : Type*} [Group G] {Δ : Submonoid G} {H₁ H₂ : Subgroup G} (R : Type*) [Semiring R]

/-- The multiplicity for right convolution by the identity double coset vanishes off the
diagonal. -/
lemma multiplicity_one_right_eq_zero [IsHeckeTriple Δ H₁ H₂] [IsHeckeTriple Δ H₂ H₂]
    (g : Δ) {A : HeckeCoset Δ H₁ H₂} (hA : A ≠ HeckeCoset.mk H₁ H₂ g) :
    multiplicity H₁ H₂ H₂ (g : G) ((1 : HeckeCoset Δ H₂ H₂).rep : G) (A.rep : G) = 0 := by
  by_contra h0
  obtain ⟨⟨p, hp⟩⟩ := (Nat.card_ne_zero.mp h0).1
  refine hA ?_
  rw [← A.mk_rep, ← HeckeCoset.mulMap_eq_of_mk_eq hp]
  exact HeckeCoset.mulMap_one_right g p

/-- The multiplicity for left convolution by the identity double coset vanishes off the
diagonal. -/
lemma multiplicity_one_left_eq_zero [IsHeckeTriple Δ H₁ H₁] [IsHeckeTriple Δ H₁ H₂]
    (g : Δ) {A : HeckeCoset Δ H₁ H₂} (hA : A ≠ HeckeCoset.mk H₁ H₂ g) :
    multiplicity H₁ H₁ H₂ ((1 : HeckeCoset Δ H₁ H₁).rep : G) (g : G) (A.rep : G) = 0 := by
  by_contra h0
  obtain ⟨⟨p, hp⟩⟩ := (Nat.card_ne_zero.mp h0).1
  refine hA ?_
  rw [← A.mk_rep, ← HeckeCoset.mulMap_eq_of_mk_eq hp]
  exact HeckeCoset.mulMap_one_left g p

/-- The structure constants for right convolution by the identity double coset collapse to
a single basis element. -/
lemma structureConstants_one_right [IsHeckeTriple Δ H₁ H₂] [IsHeckeTriple Δ H₂ H₂]
    (g : Δ) : structureConstants R H₁ H₂ H₂ g (1 : HeckeCoset Δ H₂ H₂).rep =
      single R (HeckeCoset.mk H₁ H₂ g) 1 := by
  classical
  ext A
  rw [structureConstants_apply, single_apply]
  split_ifs with h
  · rw [(HeckeCoset.multiplicity_mul_one g A.rep).mpr (h.trans A.mk_rep.symm), Nat.cast_one]
  · rw [multiplicity_one_right_eq_zero g fun hA ↦ h hA.symm, Nat.cast_zero]

/-- The structure constants for left convolution by the identity double coset collapse to
a single basis element. -/
lemma structureConstants_one_left [IsHeckeTriple Δ H₁ H₁] [IsHeckeTriple Δ H₁ H₂]
    (g : Δ) : structureConstants R H₁ H₁ H₂ (1 : HeckeCoset Δ H₁ H₁).rep g =
      single R (HeckeCoset.mk H₁ H₂ g) 1 := by
  classical
  ext A
  rw [structureConstants_apply, single_apply]
  split_ifs with h
  · rw [(HeckeCoset.multiplicity_one_mul g A.rep).mpr (h.trans A.mk_rep.symm), Nat.cast_one]
  · rw [multiplicity_one_left_eq_zero g fun hA ↦ h hA.symm, Nat.cast_zero]

/-- The multiplicative identity of the Hecke ring is the basis element of the identity double
coset. -/
noncomputable instance {H : Subgroup G} : One (𝕋 Δ H R) := ⟨single R 1 1⟩

theorem one_def {H : Subgroup G} : (1 : 𝕋 Δ H R) = single R 1 1 := rfl

/-- The identity of the Hecke ring at the left level is a left unit for the convolution
product of Hecke coset modules. -/
theorem one_mul' [IsHeckeTriple Δ H₁ H₁] [IsHeckeTriple Δ H₁ H₂]
    (f : HeckeCosetModule Δ H₁ H₂ R) : mul R (1 : 𝕋 Δ H₁ R) f = f := by
  classical
  rw [one_def, mul_eq_sum, single, Finsupp.sum_single_index (by simp)]
  have inner : ∀ (D₂ : HeckeCoset Δ H₁ H₂) (b₂ : R),
      (1 : R) • b₂ • structureConstants R H₁ H₁ H₂ (1 : HeckeCoset Δ H₁ H₁).rep D₂.rep =
        single R D₂ b₂ := fun D₂ b₂ ↦ by
    rw [one_smul, structureConstants_one_left, HeckeCoset.mk_rep, smul_single_one]
  simp only [inner]
  exact sum_single R f

/-- The identity of the Hecke ring at the right level is a right unit for the convolution
product of Hecke coset modules. -/
theorem mul_one' [IsHeckeTriple Δ H₁ H₂] [IsHeckeTriple Δ H₂ H₂]
    (f : HeckeCosetModule Δ H₁ H₂ R) : mul R f (1 : HeckeCosetModule Δ H₂ H₂ R) = f := by
  classical
  rw [one_def, mul_eq_sum, single]
  have inner : ∀ (D₁ : HeckeCoset Δ H₁ H₂) (b₁ : R),
      (Finsupp.single (1 : HeckeCoset Δ H₂ H₂) (1 : R)).sum
        (fun D₂ b₂ ↦ b₁ • b₂ • structureConstants R H₁ H₂ H₂ D₁.rep D₂.rep) =
        single R D₁ b₁ := fun D₁ b₁ ↦ by
    rw [Finsupp.sum_single_index (by simp), one_smul, structureConstants_one_right,
      HeckeCoset.mk_rep, smul_single_one]
  simp only [inner]
  exact sum_single R f

/-- The Hecke ring is a non-associative semiring: the identity double coset is a two-sided
identity. -/
noncomputable instance {H : Subgroup G} [IsHeckeTriple Δ H H] :
    NonAssocSemiring (𝕋 Δ H R) :=
  { (inferInstance : NonUnitalNonAssocSemiring (𝕋 Δ H R)),
    (inferInstance : One (𝕋 Δ H R)) with
    natCast := fun n ↦ single R 1 n
    natCast_zero := by rw [Nat.cast_zero, single, Finsupp.single_zero]; rfl
    natCast_succ := fun n ↦ by
      rw [Nat.cast_add, Nat.cast_one, single, Finsupp.single_add]
      rfl
    one_mul := fun f ↦ one_mul' R f
    mul_one := fun f ↦ mul_one' R f }

end HeckeCosetModule
