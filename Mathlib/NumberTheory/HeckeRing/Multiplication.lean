/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.NumberTheory.HeckeRing.MultiplicitySupport

/-!
# Hecke rings: the convolution product

The convolution product on the Hecke ring `𝕋 P R` with coefficients in a commutative ring `R`,
following Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Ch. 3. On
basis elements the product is `[D₁] * [D₂] = ∑_d m(D₁, D₂, d) [d]`, where the structure constants
`m` are Shimura's integer multiplicities; for general coefficients they are cast into `R`.

## Main definitions

* `HeckeRing.m`: the integer structure-constant finsupp `∑_d heckeMultiplicity(g₁, g₂, d) [d]`.
* `HeckeRing.mCast`: `m` with its coefficients cast into `R`.
* `HeckeRing.tSingle`: the basis element `b • [D]`.

## Main results

* `HeckeRing.mul_def`: the product as a double `Finsupp.sum` over structure constants.
* `HeckeRing.mul_single`: the product of two basis elements.
* the `NonUnitalNonAssocSemiring (𝕋 P R)` instance.
-/

@[expose] public section

open Set DoubleCoset Subgroup Finsupp
open scoped Pointwise

namespace HeckeRing

variable {G : Type*} [Group G]

attribute [local instance] doubleCosetSetoid

variable (P : HeckePair G)

/-- The integer structure-constant finsupp: `m g₁ g₂` is the formal sum
`∑_d heckeMultiplicity g₁ g₂ d • [d]` encoding the product of two double cosets. -/
noncomputable def m (g₁ g₂ : P.Δ) : (HeckeCoset P) →₀ ℤ :=
  ⟨mulSupport P g₁ g₂,
    fun d ↦ heckeMultiplicity P g₁ g₂ (HeckeCoset.rep d),
    fun a ↦
      ⟨heckeMultiplicity_pos_of_mem_mulSupport P g₁ g₂ a,
        fun hm ↦ by
          by_contra hemp
          exact hm (heckeMultiplicity_eq_zero_of_nmem_mulSupport P g₁ g₂ a hemp)⟩⟩

variable (R : Type*) [CommRing R]

/-- The structure constants cast into the coefficient ring `R`. -/
noncomputable def mCast (g₁ g₂ : P.Δ) : (HeckeCoset P) →₀ R :=
  (m P g₁ g₂).mapRange (Int.cast) Int.cast_zero

/-- The convolution product on the Hecke ring, defined via the structure constants `mCast`. -/
noncomputable instance : Mul (𝕋 P R) where
  mul f g := Finsupp.sum f fun D₁ b₁ ↦
    g.sum fun D₂ b₂ ↦
      b₁ • b₂ • mCast P R (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)

/-- The convolution product unfolds as a double `Finsupp.sum` over structure constants. -/
lemma mul_def (f g : 𝕋 P R) : f * g = Finsupp.sum f
    (fun D₁ b₁ ↦ g.sum fun D₂ b₂ ↦
      b₁ • b₂ • mCast P R (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)) := rfl

/-- A basis element of the Hecke ring: `tSingle D b` is the formal sum `b • [D]`. -/
noncomputable abbrev tSingle (a : HeckeCoset P) (b : R) : 𝕋 P R :=
  Finsupp.single a b

/-- The product of two basis elements of the Hecke ring. -/
lemma mul_single (D₁ D₂ : HeckeCoset P) (a b : R) :
    tSingle P R D₁ a * tSingle P R D₂ b =
      a • b • mCast P R (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) := by
  rw [mul_def]
  simp [tSingle, Finsupp.sum_single_index]

/-- The Hecke ring is a non-unital non-associative semiring (distributivity and zero laws). -/
noncomputable instance :
    NonUnitalNonAssocSemiring (𝕋 P R) :=
  { (inferInstance : AddCommGroup (𝕋 P R)) with
    left_distrib := fun f g h ↦ by
      simp only [mul_def]
      refine Eq.trans (congr_arg (Finsupp.sum f)
        (funext₂ fun a₁ b₁ ↦ Finsupp.sum_add_index ?_ ?_)) ?_
      · intros; simp
      · intro D₁ _ a b
        simp_rw [← smul_assoc, smul_eq_mul]
        ring_nf
        rw [add_smul]
      · exact Finsupp.sum_add
    right_distrib := fun f g h ↦ by
      simp only [mul_def]
      refine Eq.trans (Finsupp.sum_add_index ?_ ?_) ?_
      · intros
        simp only [zero_smul, Finsupp.sum_fun_zero]
        rfl
      · intro D₁ _ a b
        refine Finsupp.ext fun t ↦ ?_
        change (Finsupp.sum h fun D₂ b₂ ↦ (a + b) • b₂ • mCast P R D₁.rep D₂.rep) t =
            ((Finsupp.sum h fun D₂ b₂ ↦ a • b₂ • mCast P R D₁.rep D₂.rep) +
              Finsupp.sum h fun D₂ b₂ ↦ b • b₂ • mCast P R D₁.rep D₂.rep) t
        rw [Finsupp.add_apply]
        simp only [Finsupp.sum, Finset.sum_apply', Finsupp.coe_smul, Pi.smul_apply,
          smul_eq_mul]
        simp_rw [add_mul]
        rw [Finset.sum_add_distrib]
      · rfl
    zero_mul := fun _ ↦ by simp only [mul_def]; exact Finsupp.sum_zero_index
    mul_zero := fun f ↦ by
      simp only [mul_def]
      exact Eq.trans (congr_arg (sum f) (funext₂ fun _ _ ↦ sum_zero_index)) (sum_fun_zero f) }

end HeckeRing
