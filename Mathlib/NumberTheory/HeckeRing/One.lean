/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.HeckeRing.Multiplication

/-!
# Hecke rings: the identity and the unital non-associative semiring

The identity double coset `(1 : HeckeCoset P)` gives the multiplicative identity of the Hecke
ring `𝕋 P R`, following [Shimura][shimura1971], Chapter 3. This file proves that the structure
constants collapse to a single basis element on multiplication by the identity, deduces that
`single 1 1` is a two-sided unit, and assembles the `NonAssocSemiring (𝕋 P R)` instance.

## Main results

* `HeckeRing.one_def`: `(1 : 𝕋 P R) = single P R 1 1`.
* the `NonAssocSemiring (𝕋 P R)` instance.
-/

@[expose] public section

open DoubleCoset Finsupp
open scoped Pointwise

namespace HeckeRing

variable {G : Type*} [Group G] (P : HeckePair G) (R : Type*) [Semiring R]

attribute [local instance] HeckePair.doubleCosetSetoid

/-- The multiplicity for right multiplication by the identity double coset vanishes off the
diagonal. -/
lemma multiplicity_one_right_eq_zero (g : P.Δ) {A : HeckeCoset P} (hA : A ≠ ⟦g⟧) :
    multiplicity P.H P.H P.H (g : G) ((1 : HeckeCoset P).rep : G) (A.rep : G) = 0 := by
  by_contra h0
  obtain ⟨⟨p, hp⟩⟩ := (Nat.card_ne_zero.mp h0).1
  refine hA ?_
  rw [← A.mk_rep, ← P.mulMap_eq_of_mk_eq hp]
  exact P.mulMap_one_right g p

/-- The multiplicity for left multiplication by the identity double coset vanishes off the
diagonal. -/
lemma multiplicity_one_left_eq_zero (g : P.Δ) {A : HeckeCoset P} (hA : A ≠ ⟦g⟧) :
    multiplicity P.H P.H P.H ((1 : HeckeCoset P).rep : G) (g : G) (A.rep : G) = 0 := by
  by_contra h0
  obtain ⟨⟨p, hp⟩⟩ := (Nat.card_ne_zero.mp h0).1
  refine hA ?_
  rw [← A.mk_rep, ← P.mulMap_eq_of_mk_eq hp]
  exact P.mulMap_one_left g p

/-- The structure constants for right multiplication by the identity double coset collapse to
a single basis element. -/
lemma structureConstants_one_right (g : P.Δ) :
    structureConstants P R g (1 : HeckeCoset P).rep = single P R ⟦g⟧ 1 := by
  classical
  ext A
  rw [structureConstants_apply, single_apply]
  split_ifs with h
  · rw [(P.multiplicity_mul_one g A.rep).mpr (h.trans A.mk_rep.symm), Nat.cast_one]
  · rw [multiplicity_one_right_eq_zero P g fun hA ↦ h hA.symm, Nat.cast_zero]

/-- The structure constants for left multiplication by the identity double coset collapse to
a single basis element. -/
lemma structureConstants_one_left (g : P.Δ) :
    structureConstants P R (1 : HeckeCoset P).rep g = single P R ⟦g⟧ 1 := by
  classical
  ext A
  rw [structureConstants_apply, single_apply]
  split_ifs with h
  · rw [(P.multiplicity_one_mul g A.rep).mpr (h.trans A.mk_rep.symm), Nat.cast_one]
  · rw [multiplicity_one_left_eq_zero P g fun hA ↦ h hA.symm, Nat.cast_zero]

/-- The multiplicative identity of the Hecke ring is the basis element of the identity double
coset. -/
noncomputable instance : One (𝕋 P R) := ⟨single P R 1 1⟩

theorem one_def : (1 : 𝕋 P R) = single P R 1 1 := rfl

/-- The Hecke ring is a non-associative semiring: the identity double coset is a two-sided
identity. -/
noncomputable instance : NonAssocSemiring (𝕋 P R) :=
  { (inferInstance : NonUnitalNonAssocSemiring (𝕋 P R)), (inferInstance : One (𝕋 P R)) with
    natCast := fun n ↦ single P R 1 n
    natCast_zero := by rw [Nat.cast_zero, single, Finsupp.single_zero]; rfl
    natCast_succ := fun n ↦ by
      rw [Nat.cast_add, Nat.cast_one, single, Finsupp.single_add]
      rfl
    one_mul := fun f ↦ by
      classical
      rw [one_def, mul_def, single, Finsupp.sum_single_index (by simp)]
      have inner : ∀ (D₂ : HeckeCoset P) (b₂ : R),
          (1 : R) • b₂ • structureConstants P R (1 : HeckeCoset P).rep D₂.rep =
            single P R D₂ b₂ := fun D₂ b₂ ↦ by
        rw [one_smul, structureConstants_one_left, HeckeCoset.mk_rep, smul_single_one]
      simp only [inner]
      exact sum_single P R f
    mul_one := fun f ↦ by
      classical
      rw [one_def, mul_def, single]
      have inner : ∀ (D₁ : HeckeCoset P) (b₁ : R), (Finsupp.single (1 : HeckeCoset P) (1 : R)).sum
          (fun D₂ b₂ ↦ b₁ • b₂ • structureConstants P R D₁.rep D₂.rep) =
            single P R D₁ b₁ := fun D₁ b₁ ↦ by
        rw [Finsupp.sum_single_index (by simp), one_smul, structureConstants_one_right,
          HeckeCoset.mk_rep, smul_single_one]
      simp only [inner]
      exact sum_single P R f }

end HeckeRing
