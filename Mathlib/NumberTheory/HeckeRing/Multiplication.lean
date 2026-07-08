/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.NumberTheory.HeckeRing.MultiplicitySupport

/-!
# Hecke rings: the convolution product

The convolution product
`HeckeCosetModule Δ H₁ H₂ R × HeckeCosetModule Δ H₂ H₃ R → HeckeCosetModule Δ H₁ H₃ R`
of Hecke coset modules with coefficients in a semiring `R`, following [Shimura][shimura1971],
Chapter 3. On basis elements the product is `[D₁] * [D₂] = ∑_D m(D₁, D₂; D) [D]`, where the
structure constants `m` are Shimura's multiplicities cast into `R`. On the diagonal
`H₁ = H₂ = H₃` this is the multiplication of the Hecke ring.

## Main definitions

* `HeckeCosetModule.structureConstants`: the formal sum `∑_D m(g₁, g₂; D) [D]` of the structure
  constants of a product of two double cosets.
* `HeckeCosetModule.mul`: the convolution product
  `HeckeCosetModule Δ H₁ H₂ R → HeckeCosetModule Δ H₂ H₃ R → HeckeCosetModule Δ H₁ H₃ R`.

## Main results

* `HeckeCosetModule.single_mul_single`: the product of two basis elements.
* the `NonUnitalNonAssocSemiring (𝕋 Δ H R)` instance.
-/

@[expose] public section

open DoubleCoset Finsupp
open scoped Pointwise

namespace HeckeCosetModule

variable {G : Type*} [Group G] {Δ : Submonoid G} {H₁ H₂ H₃ : Subgroup G}
  (R : Type*) [Semiring R]

open Classical in
/-- The structure constants of the Hecke product: `structureConstants H₁ H₂ H₃ R g₁ g₂` is the
formal sum `∑_D m(g₁, g₂; D) [D]` over mixed double cosets, with Shimura's multiplicities cast
into `R`. -/
noncomputable def structureConstants (H₁ H₂ H₃ : Subgroup G) [IsHeckeTriple Δ H₁ H₂]
    [IsHeckeTriple Δ H₂ H₃] (g₁ g₂ : Δ) : HeckeCosetModule Δ H₁ H₃ R :=
  Finsupp.onFinset (Finset.univ.image (HeckeCoset.mulMap H₁ H₂ H₃ g₁ g₂))
    (fun D ↦ (multiplicity H₁ H₂ H₃ (g₁ : G) (g₂ : G) (D.rep : G) : R))
    (fun D hD ↦ (HeckeCoset.mem_image_mulMap_iff g₁ g₂ D).mpr
      fun h0 ↦ hD (by rw [h0, Nat.cast_zero]))

@[simp] lemma structureConstants_apply [IsHeckeTriple Δ H₁ H₂] [IsHeckeTriple Δ H₂ H₃]
    (g₁ g₂ : Δ) (D : HeckeCoset Δ H₁ H₃) :
    structureConstants R H₁ H₂ H₃ g₁ g₂ D =
      (multiplicity H₁ H₂ H₃ (g₁ : G) (g₂ : G) (D.rep : G) : R) := rfl

noncomputable instance : Module R (HeckeCosetModule Δ H₁ H₂ R) :=
  inferInstanceAs (Module R (HeckeCoset Δ H₁ H₂ →₀ R))

/-- The convolution product of Hecke coset modules, defined via the structure constants. The
diagonal case is the multiplication of the Hecke ring; see the `Mul (𝕋 Δ H R)` instance. -/
noncomputable def mul [IsHeckeTriple Δ H₁ H₂] [IsHeckeTriple Δ H₂ H₃]
    (f : HeckeCosetModule Δ H₁ H₂ R) (g : HeckeCosetModule Δ H₂ H₃ R) :
    HeckeCosetModule Δ H₁ H₃ R :=
  f.sum fun D₁ b₁ ↦ g.sum fun D₂ b₂ ↦ b₁ • b₂ • structureConstants R H₁ H₂ H₃ D₁.rep D₂.rep

lemma mul_eq_sum [IsHeckeTriple Δ H₁ H₂] [IsHeckeTriple Δ H₂ H₃]
    (f : HeckeCosetModule Δ H₁ H₂ R) (g : HeckeCosetModule Δ H₂ H₃ R) : mul R f g =
      f.sum fun D₁ b₁ ↦ g.sum fun D₂ b₂ ↦ b₁ • b₂ • structureConstants R H₁ H₂ H₃ D₁.rep D₂.rep :=
  rfl

/-- The multiplication of the Hecke ring: the diagonal case of the convolution product
`HeckeCosetModule.mul`. -/
noncomputable instance {H : Subgroup G} [IsHeckeTriple Δ H H] : Mul (𝕋 Δ H R) where
  mul f g := mul R f g

lemma mul_def {H : Subgroup G} [IsHeckeTriple Δ H H] (f g : 𝕋 Δ H R) :
    f * g = mul R f g := rfl

/-- A basis element of the Hecke coset module: `single R D b` is the formal sum `b • [D]`. As
for `Finsupp` itself, this is the type-correct way to produce elements of
`HeckeCosetModule Δ H₁ H₂ R`. -/
noncomputable def single (D : HeckeCoset Δ H₁ H₂) (b : R) : HeckeCosetModule Δ H₁ H₂ R :=
  Finsupp.single D b

lemma single_apply {D A : HeckeCoset Δ H₁ H₂} {b : R} [Decidable (D = A)] :
    single R D b A = if D = A then b else 0 :=
  Finsupp.single_apply

lemma smul_single_one (D : HeckeCoset Δ H₁ H₂) (b : R) : b • single R D 1 = single R D b :=
  Finsupp.smul_single_one D b

lemma sum_single (f : HeckeCosetModule Δ H₁ H₂ R) : f.sum (single R) = f := Finsupp.sum_single f

/-- The convolution product of two basis elements. -/
lemma mul_single_single [IsHeckeTriple Δ H₁ H₂] [IsHeckeTriple Δ H₂ H₃]
    (D₁ : HeckeCoset Δ H₁ H₂) (D₂ : HeckeCoset Δ H₂ H₃) (a b : R) :
    mul R (single R D₁ a) (single R D₂ b) =
      a • b • structureConstants R H₁ H₂ H₃ D₁.rep D₂.rep := by
  rw [mul_eq_sum]
  simp [single, Finsupp.sum_single_index]

/-- The product of two basis elements of the Hecke ring. -/
lemma single_mul_single {H : Subgroup G} [IsHeckeTriple Δ H H]
    (D₁ D₂ : HeckeCoset Δ H H) (a b : R) :
    single R D₁ a * single R D₂ b = a • b • structureConstants R H H H D₁.rep D₂.rep :=
  mul_single_single R D₁ D₂ a b

/-- The convolution product distributes over addition on the right. -/
lemma mul_add [IsHeckeTriple Δ H₁ H₂] [IsHeckeTriple Δ H₂ H₃]
    (f : HeckeCosetModule Δ H₁ H₂ R) (g h : HeckeCosetModule Δ H₂ H₃ R) :
    mul R f (g + h) = mul R f g + mul R f h := by
  classical
  simp only [mul_eq_sum]
  rw [← Finsupp.sum_add]
  exact Finsupp.sum_congr fun D₁ _ ↦ Finsupp.sum_add_index (fun _ _ ↦ by simp)
    (fun _ _ b b' ↦ by rw [add_smul, smul_add])

/-- The convolution product distributes over addition on the left. -/
lemma add_mul [IsHeckeTriple Δ H₁ H₂] [IsHeckeTriple Δ H₂ H₃]
    (f g : HeckeCosetModule Δ H₁ H₂ R) (h : HeckeCosetModule Δ H₂ H₃ R) :
    mul R (f + g) h = mul R f h + mul R g h := by
  classical
  simp only [mul_eq_sum]
  exact Finsupp.sum_add_index (fun _ _ ↦ by simp) fun _ _ b b' ↦ by
    rw [← Finsupp.sum_add]
    exact Finsupp.sum_congr fun D₂ _ ↦ by rw [add_smul]

/-- The convolution product vanishes on the left zero. -/
lemma zero_mul [IsHeckeTriple Δ H₁ H₂] [IsHeckeTriple Δ H₂ H₃]
    (f : HeckeCosetModule Δ H₂ H₃ R) : mul R (0 : HeckeCosetModule Δ H₁ H₂ R) f = 0 := by
  simp only [mul_eq_sum]
  exact Finsupp.sum_zero_index

/-- The convolution product vanishes on the right zero. -/
lemma mul_zero [IsHeckeTriple Δ H₁ H₂] [IsHeckeTriple Δ H₂ H₃]
    (f : HeckeCosetModule Δ H₁ H₂ R) : mul R f (0 : HeckeCosetModule Δ H₂ H₃ R) = 0 := by
  simp only [mul_eq_sum]
  exact (congrArg (Finsupp.sum f) (funext₂ fun _ _ ↦ Finsupp.sum_zero_index)).trans
    (Finsupp.sum_fun_zero f)

/-- The Hecke ring is a non-unital non-associative semiring (distributivity and zero laws). -/
noncomputable instance {H : Subgroup G} [IsHeckeTriple Δ H H] :
    NonUnitalNonAssocSemiring (𝕋 Δ H R) :=
  { (inferInstance : AddCommMonoid (𝕋 Δ H R)), (inferInstance : Mul (𝕋 Δ H R)) with
    left_distrib := fun f g h ↦ mul_add R f g h
    right_distrib := fun f g h ↦ add_mul R f g h
    zero_mul := fun f ↦ zero_mul R f
    mul_zero := fun f ↦ mul_zero R f }

end HeckeCosetModule
