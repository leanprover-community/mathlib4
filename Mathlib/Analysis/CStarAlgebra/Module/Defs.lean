/-
Copyright (c) 2024 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Hilbert C⋆-modules

A Hilbert C⋆-module is a complex module `E` together with a right `A`-module structure, where `A`
is a C⋆-algebra, and with an `A`-valued inner product. This inner product satisfies the
Cauchy-Schwarz inequality, and induces a norm that makes `E` a normed vector space over `ℂ`.

## Main declarations

+ `CStarModule`: The class containing the Hilbert C⋆-module structure
+ `CStarModule.normedSpaceCore`: The proof that a Hilbert C⋆-module is a normed vector
  space. This can be used with `NormedAddCommGroup.ofCore` and `NormedSpace.ofCore` to create
  the relevant instances on a type of interest.
+ `CStarModule.inner_mul_inner_swap_le`: The statement that
  `⟪y, x⟫ * ⟪x, y⟫ ≤ ‖x‖ ^ 2 • ⟪y, y⟫`, which can be viewed as a version of the Cauchy-Schwarz
  inequality for Hilbert C⋆-modules.
+ `CStarModule.norm_inner_le`, which states that `‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖`, i.e. the
  Cauchy-Schwarz inequality.

## Implementation notes

The class `CStarModule A E` requires `E` to already have a `Norm E` instance on it, but
no other norm-related instances. We then include the fact that this norm agrees with the norm
induced by the inner product among the axioms of the class. Furthermore, instead of registering
`NormedAddCommGroup E` and `NormedSpace ℂ E` instances (which might already be present on the type,
and which would send the type class search algorithm on a chase for `A`), we provide a
`NormedSpace.Core` structure which enables downstream users of the class to easily register
these instances themselves on a particular type.

Although the `Norm` is passed as a parameter, it almost never coincides with the norm on the
underlying type, unless that it is a purpose built type, as with the *standard Hilbert C⋆-module*.
However, with generic types already equipped with a norm, the norm as a Hilbert C⋆-module almost
never coincides with the norm on the underlying type. The two notable exceptions to this are when
we view `A` as a C⋆-module over itself, or when `A := ℂ`.  For this reason we will later use the
type synonym `WithCStarModule`.

As an example of just how different the norm can be, consider `CStarModule`s `E` and `F` over `A`.
One would like to put a `CStarModule` structure on (a type synonym of) `E × F`, where the `A`-valued
inner product is given, for `x y : E × F`, `⟪x, y⟫_A := ⟪x.1, y.1⟫_A + ⟪x.2, y.2⟫_A`. The norm this
induces satisfies `‖x‖ ^ 2 = ‖⟪x.1, y.1⟫ + ⟪x.2, y.2⟫‖`, but this doesn't coincide with *any*
natural norm on `E × F` unless `A := ℂ`, in which case it is `WithLp 2 (E × F)` because `E × F` is
then an `InnerProductSpace` over `ℂ`.

## References

+ Erin Wittlich. *Formalizing Hilbert Modules in C⋆-algebras with the Lean Proof Assistant*,
  December 2022. Master's thesis, Southern Illinois University Edwardsville.
-/

open scoped ComplexOrder RightActions

/-- A *Hilbert C⋆-module* is a complex module `E` endowed with a right `A`-module structure
(where `A` is typically a C⋆-algebra) and an inner product `⟪x, y⟫_A` which satisfies the
following properties. -/
class CStarModule (A : outParam <| Type*) (E : Type*) [NonUnitalSemiring A] [StarRing A]
    [Module ℂ A] [AddCommGroup E] [Module ℂ E] [PartialOrder A] [SMul Aᵐᵒᵖ E] [Norm A] [Norm E]
    extends Inner A E where
  inner_add_right {x} {y} {z} : inner x (y + z) = inner x y + inner x z
  inner_self_nonneg {x} : 0 ≤ inner x x
  inner_self {x} : inner x x = 0 ↔ x = 0
  inner_op_smul_right {a : A} {x y : E} : inner x (y <• a) = inner x y * a
  inner_smul_right_complex {z : ℂ} {x} {y} : inner x (z • y) = z • inner x y
  star_inner x y : star (inner x y) = inner y x
  norm_eq_sqrt_norm_inner_self x : ‖x‖ = √‖inner x x‖

attribute [simp] CStarModule.inner_add_right CStarModule.star_inner
  CStarModule.inner_op_smul_right CStarModule.inner_smul_right_complex

@[deprecated (since := "2024-08-04")] alias CstarModule := CStarModule

namespace CStarModule

section general

variable {A E : Type*} [NonUnitalRing A] [StarRing A] [AddCommGroup E] [Module ℂ A]
  [Module ℂ E] [PartialOrder A] [SMul Aᵐᵒᵖ E] [Norm A] [Norm E] [CStarModule A E]

local notation "⟪" x ", " y "⟫" => inner (𝕜 := A) x y

@[simp]
lemma inner_add_left {x y z : E} : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫ := by
  rw [← star_star (r := ⟪x + y, z⟫)]
  simp only [inner_add_right, star_add, star_inner]

@[simp]
lemma inner_op_smul_left {a : A} {x y : E} : ⟪x <• a, y⟫ = star a * ⟪x, y⟫ := by
  rw [← star_inner]; simp

section StarModule

variable [StarModule ℂ A]

@[simp]
lemma inner_smul_left_complex {z : ℂ} {x y : E} : ⟪z • x, y⟫ = star z • ⟪x, y⟫ := by
  rw [← star_inner]
  simp

@[simp]
lemma inner_smul_left_real {z : ℝ} {x y : E} : ⟪z • x, y⟫ = z • ⟪x, y⟫ := by
  have h₁ : z • x = (z : ℂ) • x := by simp
  rw [h₁, ← star_inner, inner_smul_right_complex]
  simp

@[simp]
lemma inner_smul_right_real {z : ℝ} {x y : E} : ⟪x, z • y⟫ = z • ⟪x, y⟫ := by
  have h₁ : z • y = (z : ℂ) • y := by simp
  rw [h₁, ← star_inner, inner_smul_left_complex]
  simp

/-- The function `⟨x, y⟩ ↦ ⟪x, y⟫` bundled as a sesquilinear map. -/
def innerₛₗ : E →ₗ⋆[ℂ] E →ₗ[ℂ] A where
  toFun x := { toFun := fun y => ⟪x, y⟫
               map_add' := fun z y => by simp
               map_smul' := fun z y => by simp }
  map_add' z y := by ext; simp
  map_smul' z y := by ext; simp

lemma innerₛₗ_apply {x y : E} : innerₛₗ x y = ⟪x, y⟫ := rfl

@[simp] lemma inner_zero_right {x : E} : ⟪x, 0⟫ = 0 := by simp [← innerₛₗ_apply]
@[simp] lemma inner_zero_left {x : E} : ⟪0, x⟫ = 0 := by simp [← innerₛₗ_apply]
@[simp] lemma inner_neg_right {x y : E} : ⟪x, -y⟫ = -⟪x, y⟫ := by simp [← innerₛₗ_apply]
@[simp] lemma inner_neg_left {x y : E} : ⟪-x, y⟫ = -⟪x, y⟫ := by simp [← innerₛₗ_apply]
@[simp] lemma inner_sub_right {x y z : E} : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫ := by
  simp [← innerₛₗ_apply]
@[simp] lemma inner_sub_left {x y z : E} : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫ := by
  simp [← innerₛₗ_apply]

@[simp]
lemma inner_sum_right {ι : Type*} {s : Finset ι} {x : E} {y : ι → E} :
    ⟪x, ∑ i ∈ s, y i⟫ = ∑ i ∈ s, ⟪x, y i⟫ :=
  map_sum (innerₛₗ x) ..

@[simp]
lemma inner_sum_left {ι : Type*} {s : Finset ι} {x : ι → E} {y : E} :
    ⟪∑ i ∈ s, x i, y⟫ = ∑ i ∈ s, ⟪x i, y⟫ :=
  map_sum (innerₛₗ.flip y) ..

end StarModule

@[simp]
lemma isSelfAdjoint_inner_self {x : E} : IsSelfAdjoint ⟪x, x⟫ := star_inner _ _

end general

section norm

variable {A E : Type*} [NonUnitalNormedRing A] [StarRing A] [PartialOrder A]
  [AddCommGroup E] [NormedSpace ℂ A] [Module ℂ E] [SMul Aᵐᵒᵖ E] [Norm E] [CStarModule A E]

local notation "⟪" x ", " y "⟫" => inner (𝕜 := A) x y

/-- The norm associated with a Hilbert C⋆-module. It is not registered as a norm, since a type
might already have a norm defined on it. -/
noncomputable def norm (A : Type*) {E : Type*} [Norm A] [Inner A E] : Norm E where
  norm x := Real.sqrt ‖⟪x, x⟫_A‖

lemma norm_sq_eq {x : E} : ‖x‖ ^ 2 = ‖⟪x, x⟫‖ := by simp [norm_eq_sqrt_norm_inner_self]

section
include A

protected lemma norm_nonneg {x : E} : 0 ≤ ‖x‖ := by simp [norm_eq_sqrt_norm_inner_self]

protected lemma norm_pos {x : E} (hx : x ≠ 0) : 0 < ‖x‖ := by
  simp only [norm_eq_sqrt_norm_inner_self, Real.sqrt_pos, norm_pos_iff]
  intro H
  rw [inner_self] at H
  exact hx H

variable [StarModule ℂ A]

protected lemma norm_zero : ‖(0 : E)‖ = 0 := by simp [norm_eq_sqrt_norm_inner_self]

lemma norm_zero_iff (x : E) : ‖x‖ = 0 ↔ x = 0 :=
  ⟨fun h => by simpa [norm_eq_sqrt_norm_inner_self, inner_self] using h,
    fun h => by simp [norm, h, norm_eq_sqrt_norm_inner_self]⟩

end

variable [CStarRing A] [StarOrderedRing A] [StarModule ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]

/-- The C⋆-algebra-valued Cauchy-Schwarz inequality for Hilbert C⋆-modules. -/
lemma inner_mul_inner_swap_le [CompleteSpace A] {x y : E} : ⟪y, x⟫ * ⟪x, y⟫ ≤ ‖x‖ ^ 2 • ⟪y, y⟫ := by
  rcases eq_or_ne x 0 with h|h
  · simp [h, CStarModule.norm_zero (E := E)]
  · have h₁ : ∀ (a : A),
        (0 : A) ≤ ‖x‖ ^ 2 • (star a * a) - ‖x‖ ^ 2 • (⟪y, x⟫ * a)
                  - ‖x‖ ^ 2 • (star a * ⟪x, y⟫) + ‖x‖ ^ 2 • (‖x‖ ^ 2 • ⟪y, y⟫) := fun a => by
      calc (0 : A) ≤ ⟪x <• a - ‖x‖ ^ 2 • y, x <• a - ‖x‖ ^ 2 • y⟫_A := by
                      exact inner_self_nonneg
            _ = star a * ⟪x, x⟫ * a - ‖x‖ ^ 2 • (⟪y, x⟫ * a)
                  - ‖x‖ ^ 2 • (star a * ⟪x, y⟫) + ‖x‖ ^ 2 • (‖x‖ ^ 2 • ⟪y, y⟫) := by
                      simp only [inner_sub_right, inner_op_smul_right, inner_sub_left,
                        inner_op_smul_left, inner_smul_left_real, sub_mul, smul_mul_assoc,
                        inner_smul_right_real, smul_sub]
                      abel
            _ ≤ ‖x‖ ^ 2 • (star a * a) - ‖x‖ ^ 2 • (⟪y, x⟫ * a)
                  - ‖x‖ ^ 2 • (star a * ⟪x, y⟫) + ‖x‖ ^ 2 • (‖x‖ ^ 2 • ⟪y, y⟫) := by
                      gcongr
                      calc _ ≤ ‖⟪x, x⟫_A‖ • (star a * a) := CStarRing.conjugate_le_norm_smul
                        _ = (Real.sqrt ‖⟪x, x⟫_A‖) ^ 2 • (star a * a) := by
                                  congr
                                  have : 0 ≤ ‖⟪x, x⟫_A‖ := by positivity
                                  rw [Real.sq_sqrt this]
                        _ = ‖x‖ ^ 2 • (star a * a) := by rw [← norm_eq_sqrt_norm_inner_self]
    specialize h₁ ⟪x, y⟫
    simp only [star_inner, sub_self, zero_sub, le_neg_add_iff_add_le, add_zero] at h₁
    rwa [smul_le_smul_iff_of_pos_left (pow_pos (CStarModule.norm_pos h) _)] at h₁

variable (E) in
/-- The Cauchy-Schwarz inequality for Hilbert C⋆-modules. -/
lemma norm_inner_le [CompleteSpace A] {x y : E} : ‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖ := by
  have := calc ‖⟪x, y⟫‖ ^ 2 = ‖⟪y, x⟫ * ⟪x, y⟫‖ := by
                rw [← star_inner x, CStarRing.norm_star_mul_self, pow_two]
    _ ≤ ‖‖x‖^ 2 • ⟪y, y⟫‖ := by
                refine CStarRing.norm_le_norm_of_nonneg_of_le ?_ inner_mul_inner_swap_le
                rw [← star_inner x]
                exact star_mul_self_nonneg ⟪x, y⟫_A
    _ = ‖x‖ ^ 2 * ‖⟪y, y⟫‖ := by simp [norm_smul]
    _ = ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
                simp only [norm_eq_sqrt_norm_inner_self, norm_nonneg, Real.sq_sqrt]
    _ = (‖x‖ * ‖y‖) ^ 2 := by simp only [mul_pow]
  refine (pow_le_pow_iff_left (R := ℝ) (norm_nonneg ⟪x, y⟫_A) ?_ (by norm_num)).mp this
  exact mul_nonneg CStarModule.norm_nonneg CStarModule.norm_nonneg

protected lemma norm_triangle [CompleteSpace A] (x y : E) : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := by
  have h : ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := by
    calc _ ≤ ‖⟪x, x⟫ + ⟪y, x⟫‖ + ‖⟪x, y⟫‖ + ‖⟪y, y⟫‖ := by
          simp only [norm_eq_sqrt_norm_inner_self, inner_add_right, inner_add_left, ← add_assoc,
            norm_nonneg, Real.sq_sqrt]
          exact norm_add₃_le _ _ _
      _ ≤ ‖⟪x, x⟫‖ + ‖⟪y, x⟫‖ + ‖⟪x, y⟫‖ + ‖⟪y, y⟫‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ‖⟪x, x⟫‖ + ‖y‖ * ‖x‖ + ‖x‖ * ‖y‖ + ‖⟪y, y⟫‖ := by gcongr <;> exact norm_inner_le E
      _ = ‖x‖ ^ 2 + ‖y‖ * ‖x‖ + ‖x‖ * ‖y‖ + ‖y‖ ^ 2 := by
          simp [norm_eq_sqrt_norm_inner_self]
      _ = (‖x‖ + ‖y‖) ^ 2 := by simp only [add_pow_two, add_left_inj]; ring
  refine (pow_le_pow_iff_left CStarModule.norm_nonneg ?_ (by norm_num)).mp h
  exact add_nonneg CStarModule.norm_nonneg CStarModule.norm_nonneg

/-- This allows us to get `NormedAddCommGroup` and `NormedSpace` instances on `E` via
`NormedAddCommGroup.ofCore` and `NormedSpace.ofCore`. -/
lemma normedSpaceCore [CompleteSpace A] : NormedSpace.Core ℂ E where
  norm_nonneg x := CStarModule.norm_nonneg
  norm_eq_zero_iff x := norm_zero_iff x
  norm_smul c x := by simp [norm_eq_sqrt_norm_inner_self, norm_smul, ← mul_assoc]
  norm_triangle x y := CStarModule.norm_triangle x y

/-- This is not listed as an instance because we often want to replace the topology, uniformity
and bornology instead of inheriting them from the norm. -/
abbrev normedAddCommGroup [CompleteSpace A] : NormedAddCommGroup E :=
  NormedAddCommGroup.ofCore CStarModule.normedSpaceCore

lemma norm_eq_csSup [CompleteSpace A] (v : E) :
    ‖v‖ = sSup { ‖⟪w, v⟫_A‖ | (w : E) (_ : ‖w‖ ≤ 1) } := by
  let instNACG : NormedAddCommGroup E := NormedAddCommGroup.ofCore normedSpaceCore
  let instNS : NormedSpace ℂ E := .ofCore normedSpaceCore
  refine Eq.symm <| IsGreatest.csSup_eq ⟨⟨‖v‖⁻¹ • v, ?_, ?_⟩, ?_⟩
  · simpa only [norm_smul, norm_inv, norm_norm] using inv_mul_le_one_of_le le_rfl (by positivity)
  · simp [norm_smul, ← norm_sq_eq, pow_two, ← mul_assoc]
  · rintro - ⟨w, hw, rfl⟩
    calc _ ≤ ‖w‖ * ‖v‖ := norm_inner_le E
      _ ≤ 1 * ‖v‖ := by gcongr
      _ = ‖v‖ := by simp

end norm

section NormedAddCommGroup

/- Note: one generally creates a `CStarModule` instance for a type `E` first before getting the
`NormedAddCommGroup` and `NormedSpace` instances via `CStarModule.normedSpaceCore`, especially by
using `NormedAddCommGroup.ofCoreReplaceAll` and `NormedSpace.ofCore`. See
`Analysis.CStarAlgebra.Module.Constructions` for examples. -/
variable {A E : Type*} [NonUnitalNormedRing A] [StarRing A] [CStarRing A] [PartialOrder A]
  [StarOrderedRing A] [NormedSpace ℂ A] [SMul Aᵐᵒᵖ E] [CompleteSpace A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [StarModule ℂ A] [CStarModule A E] [IsScalarTower ℂ A A]
  [SMulCommClass ℂ A A]

/-- The function `⟨x, y⟩ ↦ ⟪x, y⟫` bundled as a continuous sesquilinear map. -/
noncomputable def innerSL : E →L⋆[ℂ] E →L[ℂ] A :=
  LinearMap.mkContinuous₂ (innerₛₗ : E →ₗ⋆[ℂ] E →ₗ[ℂ] A) 1 <| fun x y => by
    simp [innerₛₗ_apply, norm_inner_le E]

lemma innerSL_apply {x y : E} : innerSL x y = ⟪x, y⟫_A := rfl

@[continuity, fun_prop]
lemma continuous_inner : Continuous (fun x : E × E => ⟪x.1, x.2⟫_A) := by
  simp_rw [← innerSL_apply]
  fun_prop

end NormedAddCommGroup

end CStarModule
