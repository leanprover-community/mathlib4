/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Data.Finsupp.Pointwise
--import Mathlib.Data.Finset.Lattice.Basic

/-!
# Lemmas about bilinear maps with a basis over each argument
-/

open Module

namespace LinearMap

variable {ι₁ ι₂ : Type*}
variable {R R₂ S S₂ M N P Rₗ : Type*}
variable {Mₗ Nₗ Pₗ : Type*}

-- Could weaken [CommSemiring Rₗ] to [SMulCommClass Rₗ Rₗ Pₗ], but might impact performance
variable [Semiring R] [Semiring S] [Semiring R₂] [Semiring S₂] [CommSemiring Rₗ]

section AddCommMonoid

variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
variable [AddCommMonoid Mₗ] [AddCommMonoid Nₗ] [AddCommMonoid Pₗ]
variable [Module R M] [Module S N] [Module R₂ P] [Module S₂ P]
variable [Module Rₗ Mₗ] [Module Rₗ Nₗ] [Module Rₗ Pₗ]
variable [SMulCommClass S₂ R₂ P]
variable {ρ₁₂ : R →+* R₂} {σ₁₂ : S →+* S₂}
variable (b₁ : Basis ι₁ R M) (b₂ : Basis ι₂ S N) (b₁' : Basis ι₁ Rₗ Mₗ) (b₂' : Basis ι₂ Rₗ Nₗ)

/-- Two bilinear maps are equal when they are equal on all basis vectors. -/
theorem ext_basis {B B' : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P} (h : ∀ i j, B (b₁ i) (b₂ j) = B' (b₁ i) (b₂ j)) :
    B = B' :=
  b₁.ext fun i => b₂.ext fun j => h i j

/-- Write out `B x y` as a sum over `B (b i) (b j)` if `b` is a basis.

Version for semi-bilinear maps, see `sum_repr_mul_repr_mul` for the bilinear version. -/
theorem sum_repr_mul_repr_mulₛₗ {B : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P} (x y) :
    ((b₁.repr x).sum fun i xi => (b₂.repr y).sum fun j yj => ρ₁₂ xi • σ₁₂ yj • B (b₁ i) (b₂ j)) =
      B x y := by
  conv_rhs => rw [← b₁.linearCombination_repr x, ← b₂.linearCombination_repr y]
  simp_rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum₂, map_sum, LinearMap.map_smulₛₗ₂,
    LinearMap.map_smulₛₗ]

variable {ι : Type*}

open Finsupp in
theorem BilinearMap.map_finsuppSum (B : Mₗ →ₗ[Rₗ] Nₗ →ₗ[Rₗ] Pₗ) (f₁ : ι →₀ R) (g₁ : ι → R → Mₗ)
    (f₂ : ι →₀ R) (g₂ : ι → R → Nₗ) : B (f₁.sum g₁) (f₂.sum g₂) =
      f₁.sum (fun i r => f₂.sum (fun i₂ r₂ => B (g₁ i r) (g₂ i₂ r₂))) := by
  rw [Finsupp.sum, LinearMap.map_sum₂, Finsupp.sum]
  simp_rw [map_sum]
  rw [Finsupp.sum]
  simp_rw [Finsupp.sum]

variable [DecidableEq ι]

open Finsupp in
theorem apply_linearCombination (B : Mₗ →ₗ[Rₗ] Nₗ →ₗ[Rₗ] Pₗ) {g₁ : ι → Mₗ} (l₁ : ι →₀ Rₗ)
    {g₂ : ι → Nₗ} (l₂ : ι →₀ Rₗ) :
    B (linearCombination Rₗ g₁ l₁) (linearCombination Rₗ g₂ l₂) =
      linearCombination Rₗ (fun i => B (g₁ i) (g₂ i)) (l₂ * l₁) := by
  simp_rw [linearCombination_apply]
  simp_rw [BilinearMap.map_finsuppSum]
  simp_rw [map_smul]
  --rw [Finsupp.sum]
  have hs : support (l₂ * l₁) ⊆ l₂.support ∩ l₁.support := support_mul
  rw [Finsupp.sum_of_support_subset (l₂ * l₁) hs (fun i a => a • (B (g₁ i) (g₂ i)))
    (fun _ _=> zero_smul Rₗ _)]
  simp_all only [smul_apply, Finsupp.mul_apply]
  simp only [←smul_eq_mul]
  simp only [smul_assoc]


  sorry

  --, map_finsuppSum, polar_smul_left, polar_smul_right, map_smul,
--    mul_smul,


/-- Write out `B x y` as a sum over `B (b i) (b j)` if `b` is a basis.

Version for bilinear maps, see `sum_repr_mul_repr_mulₛₗ` for the semi-bilinear version. -/
theorem sum_repr_mul_repr_mul {B : Mₗ →ₗ[Rₗ] Nₗ →ₗ[Rₗ] Pₗ} (x y) :
    ((b₁'.repr x).sum fun i xi => (b₂'.repr y).sum fun j yj => xi • yj • B (b₁' i) (b₂' j)) =
      B x y := by
  conv_rhs => rw [← b₁'.linearCombination_repr x, ← b₂'.linearCombination_repr y]
  simp_rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum₂, map_sum, LinearMap.map_smul₂,
    LinearMap.map_smul]

end AddCommMonoid

end LinearMap
