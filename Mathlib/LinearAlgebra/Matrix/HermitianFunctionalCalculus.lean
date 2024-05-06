/-
Copyright (c) 2024 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Jireh Loreaux
-/

import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.Analysis.NormedSpace.Star.ContinuousFunctionalCalculus.Restrict
import Mathlib.Analysis.NormedSpace.Star.ContinuousFunctionalCalculus
import Mathlib.Analysis.NormedSpace.Star.Spectrum
import Mathlib.Topology.ContinuousFunction.UniqueCFC
import Mathlib.Analysis.NormedSpace.Star.Matrix

/-
This file defines an instance of the continuous functional calculus for Hermitian matrices over an
RCLike field 𝕜.

## Tags

spectral theorem, diagonalization theorem, continuous functional calculus
-/

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]

open scoped BigOperators
namespace IsHermitian
section DecidableEq

variable [DecidableEq n]

variable {A : Matrix n n 𝕜} (hA : IsHermitian A)

/-To do:

1) Somehow make this natural map defined in terms of the diagonal into a *-alg hom,
so I have to learn how to specify all of this data.

2) Use the resulting * algebra hom as the φ in the instance of the CFC.

-/

theorem eigenvalue_mem_toEuclideanLin_spectrum_RCLike (i : n) :
    (RCLike.ofReal ∘ hA.eigenvalues) i ∈ spectrum 𝕜 (toEuclideanLin A) :=
  LinearMap.IsSymmetric.hasEigenvalue_eigenvalues _ _ _ |>.mem_spectrum

theorem range_thm_RCLike : Set.range
    (fun (i : n) ↦ (RCLike.ofReal ∘ hA.eigenvalues) i) ⊆ (spectrum 𝕜 (toEuclideanLin A)) := by
   rw [Set.range_subset_iff]
   apply eigenvalue_mem_toEuclideanLin_spectrum_RCLike

noncomputable def LinearAlgEquiv : AlgEquiv (R := 𝕜)
    (A := (EuclideanSpace 𝕜 n) →ₗ[𝕜] (EuclideanSpace 𝕜 n))
    (B := (EuclideanSpace 𝕜 n) →L[𝕜] (EuclideanSpace 𝕜 n)) where
         toFun := LinearMap.toContinuousLinearMap
         invFun := ContinuousLinearMap.toLinearMap
         left_inv := congr_fun rfl
         right_inv := congr_fun rfl
         map_mul' := by exact fun x y ↦ rfl
         map_add' := by exact fun x y ↦ rfl
         commutes' := by exact fun r ↦ rfl

theorem spec_EuclideanCLM_eq_spec : spectrum 𝕜 (toEuclideanCLM (𝕜:= 𝕜) A) = spectrum 𝕜 A :=
    AlgEquiv.spectrum_eq _ A

theorem spec_EuclideanCLM_eq_spec_toEuclideanLin : spectrum 𝕜 (toEuclideanCLM (𝕜:= 𝕜) A)
    = spectrum 𝕜 (toEuclideanLin A) := by
refine AlgEquiv.spectrum_eq (LinearAlgEquiv) (toEuclideanLin A)

theorem spec_toEuclideanLin_eq_spec_EuclideanCLM : spectrum 𝕜 (toEuclideanLin A) = spectrum 𝕜 A
    := by
simp only [spec_EuclideanCLM_eq_spec.symm, spec_EuclideanCLM_eq_spec_toEuclideanLin]

noncomputable def f : n → spectrum 𝕜 A := by
apply Set.codRestrict fun (i : n) ↦ (RCLike.ofReal ∘ hA.eigenvalues) i
exact spec_toEuclideanLin_eq_spec_EuclideanCLM (𝕜 := 𝕜) (n:= n) (A := A)
      ▸ eigenvalue_mem_toEuclideanLin_spectrum_RCLike (hA := hA)


#exit
def φ₀ : C(spectrum ℝ A, ℝ) →  Matrix n n 𝕜 :=
  fun f => (eigenvectorUnitary hA : Matrix n n 𝕜) *
  diagonal (RCLike.ofReal (K := 𝕜) ∘ f.1 ∘ (f1 hA))
      * star (eigenvectorUnitary hA : Matrix n n 𝕜)

def φ : StarAlgHom ℝ C(spectrum ℝ A, ℝ) (Matrix n n 𝕜) where
  toFun := fun f => (eigenvectorUnitary hA : Matrix n n 𝕜) *
  diagonal (RCLike.ofReal (K := 𝕜) ∘ f.1 ∘ hA.eigenvalues)
      * star (eigenvectorUnitary hA : Matrix n n 𝕜)
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry
  commutes' := sorry
  map_star' := fun
    | .mk toFun continuous_toFun => sorry



instance instContinuousFunctionalCalculus :
    ContinuousFunctionalCalculus 𝕜 (IsHermitian : Matrix n n 𝕜 → Prop) where
exists_cfc_of_predicate

sorry

-/

--
