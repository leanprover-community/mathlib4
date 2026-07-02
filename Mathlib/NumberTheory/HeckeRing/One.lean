/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.HeckeRing.Multiplication

/-!
# Hecke rings: the identity and the unital non-associative semiring

The identity double coset `HeckeCoset.one` gives the multiplicative identity of the Hecke ring
`𝕋 P R`, following Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*,
Ch. 3. This file proves that the structure-constant finsupp collapses to a single basis element on
multiplication by the identity, deduces that `tSingle (one) 1` is a two-sided unit, and assembles
the `NonAssocSemiring (𝕋 P R)` instance.

## Main results

* `HeckeRing.one_def`: `(1 : 𝕋 P R) = tSingle (HeckeCoset.one P) 1`.
* the `NonAssocSemiring (𝕋 P R)` instance.
-/

@[expose] public section

open Set DoubleCoset Subgroup Finsupp
open scoped Pointwise

namespace HeckeRing

variable {G : Type*} [Group G]

attribute [local instance] doubleCosetSetoid

variable (P : HeckePair G)

/-- If every pair maps to a single double coset `D_out` under `mulMap`, the multiplicity vanishes
on every other double coset. -/
lemma heckeMultiplicity_eq_zero_of_mulMap_unique (g₁ g₂ : P.Δ) (D_out A : HeckeCoset P)
    (hA : A ≠ D_out)
    (h : ∀ p : decompQuot P g₁ × decompQuot P g₂, mulMap P g₁ g₂ p = D_out) :
    heckeMultiplicity P g₁ g₂ (HeckeCoset.rep A) = 0 :=
  heckeMultiplicity_eq_zero_of_nmem_mulSupport P g₁ g₂ A (by
    rw [mulSupport]
    simp only [Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ, true_and,
      Prod.exists, not_exists]
    intro i j heq
    exact hA (heq ▸ h (i, j)))

/-- When the multiplicity is one on a single double coset and zero elsewhere, the
structure-constant finsupp is a single basis element. -/
lemma m_eq_single (g₁ g₂ : P.Δ) (D_out : HeckeCoset P)
    (h_one : heckeMultiplicity P g₁ g₂ (HeckeCoset.rep D_out) = 1)
    (h_zero : ∀ A, A ≠ D_out → heckeMultiplicity P g₁ g₂ (HeckeCoset.rep A) = 0) :
    m P g₁ g₂ = Finsupp.single D_out 1 := by
  ext A
  simp only [m, Finsupp.coe_mk, Finsupp.single_apply]
  split_ifs with h1
  · exact h1 ▸ h_one
  · exact h_zero A (ne_comm.mp h1)

/-- The off-diagonal multiplicity for right multiplication by `HeckeCoset.one` is zero. -/
lemma heckeMultiplicity_mul_one_eq_zero (g₁ : P.Δ) (A : HeckeCoset P)
    (h : A ≠ (⟦g₁⟧ : HeckeCoset P)) :
    heckeMultiplicity P g₁ (HeckeCoset.one P).rep (HeckeCoset.rep A) = 0 := by
  simp only [heckeMultiplicity, Nat.cast_eq_zero, Nat.card_eq_zero, isEmpty_subtype]
  left
  intro ⟨i, j⟩ heq
  refine h ?_
  rw [show A = ⟦HeckeCoset.rep A⟧ from (Quotient.out_eq A).symm]
  exact ((mulMap_mul_one_eq P g₁ i j).symm.trans
    (doubleCoset_eq_of_rightCoset_eq P g₁ (HeckeCoset.one P).rep (HeckeCoset.rep A)
      (i, j) heq)).symm

/-- Right multiplication by `HeckeCoset.one` acts as the identity on the structure constants. -/
lemma m_mul_one_eq_single (g₁ : P.Δ) :
    m P g₁ (HeckeCoset.one P).rep = Finsupp.single (⟦g₁⟧ : HeckeCoset P) 1 :=
  m_eq_single P g₁ (HeckeCoset.one P).rep (⟦g₁⟧ : HeckeCoset P)
    ((heckeMultiplicity_mul_one P g₁ (HeckeCoset.rep (⟦g₁⟧ : HeckeCoset P))).mp
      (Quotient.out_eq (⟦g₁⟧ : HeckeCoset P)).symm)
    (heckeMultiplicity_mul_one_eq_zero P g₁)

/-- The off-diagonal multiplicity for left multiplication by `HeckeCoset.one` is zero. -/
lemma heckeMultiplicity_one_mul_eq_zero (g₁ : P.Δ) (A : HeckeCoset P)
    (h : A ≠ (⟦g₁⟧ : HeckeCoset P)) :
    heckeMultiplicity P (HeckeCoset.one P).rep g₁ (HeckeCoset.rep A) = 0 := by
  simp only [heckeMultiplicity, Nat.cast_eq_zero, Nat.card_eq_zero, isEmpty_subtype]
  left
  intro ⟨i, j⟩ heq
  refine h ?_
  rw [show A = ⟦HeckeCoset.rep A⟧ from (Quotient.out_eq A).symm]
  exact ((mulMap_one_mul_eq P g₁ i j).symm.trans
    (doubleCoset_eq_of_rightCoset_eq P (HeckeCoset.one P).rep g₁ (HeckeCoset.rep A)
      (i, j) heq)).symm

/-- Left multiplication by `HeckeCoset.one` acts as the identity on the structure constants. -/
lemma m_one_mul_eq_single (g₁ : P.Δ) :
    m P (HeckeCoset.one P).rep g₁ = Finsupp.single (⟦g₁⟧ : HeckeCoset P) 1 :=
  m_eq_single P (HeckeCoset.one P).rep g₁ (⟦g₁⟧ : HeckeCoset P)
    ((heckeMultiplicity_one_mul P g₁ (HeckeCoset.rep (⟦g₁⟧ : HeckeCoset P))).mp
      (Quotient.out_eq (⟦g₁⟧ : HeckeCoset P)).symm)
    (heckeMultiplicity_one_mul_eq_zero P g₁)

variable (R : Type*) [CommRing R]

/-- Right multiplication by `HeckeCoset.one` on the cast structure constants. -/
lemma mCast_mul_one_eq_single (g₁ : P.Δ) :
    mCast P R g₁ (HeckeCoset.one P).rep = Finsupp.single (⟦g₁⟧ : HeckeCoset P) 1 := by
  unfold mCast
  rw [m_mul_one_eq_single]
  exact Finsupp.mapRange_single.trans (congrArg (Finsupp.single ⟦g₁⟧) Int.cast_one)

/-- Left multiplication by `HeckeCoset.one` on the cast structure constants. -/
lemma mCast_one_mul_eq_single (g₁ : P.Δ) :
    mCast P R (HeckeCoset.one P).rep g₁ = Finsupp.single (⟦g₁⟧ : HeckeCoset P) 1 := by
  unfold mCast
  rw [m_one_mul_eq_single]
  exact Finsupp.mapRange_single.trans (congrArg (Finsupp.single ⟦g₁⟧) Int.cast_one)

/-- `tSingle D b` is fixed by right multiplication by the identity basis element. -/
lemma mul_tSingle_one (D : HeckeCoset P) (b : R) :
    tSingle P R D b * tSingle P R (HeckeCoset.one P) 1 = tSingle P R D b := by
  rw [mul_single, mCast_mul_one_eq_single, HeckeCoset.mk_rep]
  simp only [one_smul]
  exact Finsupp.smul_single_one D b

/-- `tSingle D b` is fixed by left multiplication by the identity basis element. -/
lemma one_mul_tSingle (D : HeckeCoset P) (b : R) :
    tSingle P R (HeckeCoset.one P) 1 * tSingle P R D b = tSingle P R D b := by
  rw [mul_single, mCast_one_mul_eq_single, HeckeCoset.mk_rep]
  simp only [one_smul]
  exact Finsupp.smul_single_one D b

/-- The multiplicative identity of the Hecke ring is `tSingle (HeckeCoset.one P) 1`. -/
noncomputable instance : One (𝕋 P R) :=
  ⟨tSingle P R (HeckeCoset.one P) 1⟩

/-- The one element of the Hecke ring unfolds to `tSingle (HeckeCoset.one P) 1`. -/
theorem one_def : (1 : 𝕋 P R) = tSingle P R (HeckeCoset.one P) 1 := rfl

/-- The Hecke ring is a non-associative semiring: `HeckeCoset.one` is a two-sided identity. -/
noncomputable instance : NonAssocSemiring (𝕋 P R) :=
  { (inferInstance : NonUnitalNonAssocSemiring (𝕋 P R)) with
    natCast := fun n ↦ tSingle P R (HeckeCoset.one P) n
    natCast_zero := by simp only [Nat.cast_zero, single_zero]; rfl
    natCast_succ := fun _ ↦ by simp only [Nat.cast_add, Nat.cast_one, single_add]; rfl
    one_mul := fun f ↦ by
      simp only [one_def, mul_def, tSingle]
      simp only [Finsupp.sum_single_index, one_smul, zero_smul, Finsupp.sum_fun_zero]
      nth_rw 2 [← Finsupp.sum_single f]
      congr
      ext D z v
      have := one_mul_tSingle P R D z
      simp_rw [tSingle] at *
      rw [← this, mul_single, one_smul]
    mul_one := fun f ↦ by
      simp only [one_def, mul_def, zero_smul, smul_zero, sum_single_index, one_smul]
      nth_rw 2 [← Finsupp.sum_single f]
      congr
      ext D z v
      have := mul_tSingle_one P R D z
      simp_rw [tSingle] at this
      rw [← this, mul_single, one_smul] }

end HeckeRing
