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

The convolution product on the Hecke ring `𝕋 P R` with coefficients in a semiring `R`,
following [Shimura][shimura1971], Chapter 3. On basis elements the product is
`[D₁] * [D₂] = ∑_D m(D₁, D₂; D) [D]`, where the structure constants `m` are Shimura's
multiplicities cast into `R`.

## Main definitions

* `HeckeRing.structureConstants`: the formal sum `∑_D m(g₁, g₂; D) [D]` of the structure
  constants of a product of two double cosets.

## Main results

* `HeckeRing.single_mul_single`: the product of two basis elements.
* the `NonUnitalNonAssocSemiring (𝕋 P R)` instance.
-/

@[expose] public section

open DoubleCoset Finsupp
open scoped Pointwise

namespace HeckeRing

variable {G : Type*} [Group G] (P : HeckePair G) (R : Type*) [Semiring R]

attribute [local instance] HeckePair.doubleCosetSetoid

open Classical in
/-- The structure constants of the Hecke product: `structureConstants P R g₁ g₂` is the formal
sum `∑_D m(g₁, g₂; D) [D]` over double cosets, with Shimura's multiplicities cast into `R`. -/
noncomputable def structureConstants (g₁ g₂ : P.Δ) : 𝕋 P R :=
  Finsupp.onFinset (Finset.univ.image (P.mulMap g₁ g₂))
    (fun D ↦ (multiplicity P.H P.H P.H (g₁ : G) (g₂ : G) (D.rep : G) : R))
    (fun D hD ↦ (P.mem_image_mulMap_iff g₁ g₂ D).mpr fun h0 ↦ hD (by rw [h0, Nat.cast_zero]))

@[simp] lemma structureConstants_apply (g₁ g₂ : P.Δ) (D : HeckeCoset P) :
    structureConstants P R g₁ g₂ D =
      (multiplicity P.H P.H P.H (g₁ : G) (g₂ : G) (D.rep : G) : R) := rfl

noncomputable instance : Module R (𝕋 P R) := inferInstanceAs (Module R (HeckeCoset P →₀ R))

/-- The convolution product on the Hecke ring, defined via the structure constants. -/
noncomputable instance : Mul (𝕋 P R) where
  mul f g := f.sum fun D₁ b₁ ↦ g.sum fun D₂ b₂ ↦ b₁ • b₂ • structureConstants P R D₁.rep D₂.rep

lemma mul_def (f g : 𝕋 P R) : f * g =
    f.sum (fun D₁ b₁ ↦ g.sum fun D₂ b₂ ↦ b₁ • b₂ • structureConstants P R D₁.rep D₂.rep) := rfl

/-- A basis element of the Hecke ring: `single D b` is the formal sum `b • [D]`. As for
`Finsupp` itself, this is the type-correct way to produce elements of `𝕋 P R`. -/
noncomputable def single (D : HeckeCoset P) (b : R) : 𝕋 P R := Finsupp.single D b

lemma single_apply {D A : HeckeCoset P} {b : R} [Decidable (D = A)] :
    single P R D b A = if D = A then b else 0 :=
  Finsupp.single_apply

lemma smul_single_one (D : HeckeCoset P) (b : R) : b • single P R D 1 = single P R D b :=
  Finsupp.smul_single_one D b

lemma sum_single (f : 𝕋 P R) : f.sum (single P R) = f := Finsupp.sum_single f

/-- The product of two basis elements of the Hecke ring. -/
lemma single_mul_single (D₁ D₂ : HeckeCoset P) (a b : R) :
    single P R D₁ a * single P R D₂ b = a • b • structureConstants P R D₁.rep D₂.rep := by
  rw [mul_def]
  simp [single, Finsupp.sum_single_index]

/-- The Hecke ring is a non-unital non-associative semiring (distributivity and zero laws). -/
noncomputable instance : NonUnitalNonAssocSemiring (𝕋 P R) :=
  { (inferInstance : AddCommMonoid (𝕋 P R)), (inferInstance : Mul (𝕋 P R)) with
    left_distrib := fun f g h ↦ by
      classical
      simp only [mul_def]
      rw [← Finsupp.sum_add]
      exact Finsupp.sum_congr fun D₁ _ ↦ Finsupp.sum_add_index (fun _ _ ↦ by simp)
        (fun _ _ b b' ↦ by rw [add_smul, smul_add])
    right_distrib := fun f g h ↦ by
      classical
      simp only [mul_def]
      exact Finsupp.sum_add_index (fun _ _ ↦ by simp) fun _ _ b b' ↦ by
        rw [← Finsupp.sum_add]
        exact Finsupp.sum_congr fun D₂ _ ↦ by rw [add_smul]
    zero_mul := fun f ↦ by
      simp only [mul_def]
      exact Finsupp.sum_zero_index
    mul_zero := fun f ↦ by
      simp only [mul_def]
      exact (congrArg (Finsupp.sum f) (funext₂ fun _ _ ↦ Finsupp.sum_zero_index)).trans
        (Finsupp.sum_fun_zero f) }

end HeckeRing
