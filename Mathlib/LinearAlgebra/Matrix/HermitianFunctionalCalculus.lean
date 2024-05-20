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
import Mathlib.Algebra.Star.StarAlgHom

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

/-The following needs a name change-/
theorem range_thm_RCLike : Set.range
    (fun (i : n) ↦ (RCLike.ofReal ∘ hA.eigenvalues) i) ⊆ (spectrum 𝕜 (toEuclideanLin A)) := by
    rw [Set.range_subset_iff]
    apply eigenvalue_mem_toEuclideanLin_spectrum_RCLike

def AlgEquivFiniteDimNormedLinearCLM.{v} (E : Type v) [NormedAddCommGroup E]
    [NormedSpace 𝕜 E][FiniteDimensional 𝕜 E] :
    AlgEquiv (R := 𝕜) (A := E →ₗ[𝕜] E) (B := E →L[𝕜] E) :=
    {LinearMap.toContinuousLinearMap with
    map_mul' := fun _ _ ↦ rfl
    commutes' := fun _ ↦ rfl}

theorem spec_toEuclideanLin_eq_spec : spectrum 𝕜 (toEuclideanLin A) = spectrum 𝕜 A
    := AlgEquiv.spectrum_eq ((AlgEquiv.trans ((toEuclideanCLM : Matrix n n 𝕜 ≃⋆ₐ[𝕜]
    EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n) : Matrix n n 𝕜 ≃ₐ[𝕜]
    EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n))
    (AlgEquivFiniteDimNormedLinearCLM (EuclideanSpace 𝕜 n)).symm) _

theorem eigenvalue_mem_real : ∀ (i : n), (hA.eigenvalues) i ∈ spectrum ℝ A := by
    intro i
    apply spectrum.of_algebraMap_mem (S := 𝕜) (R := ℝ) (A := Matrix n n 𝕜)
    rw [←spec_toEuclideanLin_eq_spec]
    apply hA.eigenvalue_mem_toEuclideanLin_spectrum_RCLike i

noncomputable def φ : StarAlgHom ℝ C(spectrum ℝ A, ℝ) (Matrix n n 𝕜) where
  toFun := fun g => (eigenvectorUnitary hA : Matrix n n 𝕜) *
    diagonal (RCLike.ofReal ∘ g ∘ (fun i ↦ ⟨hA.eigenvalues i, hA.eigenvalue_mem_real i⟩))
    * star (eigenvectorUnitary hA : Matrix n n 𝕜)
  map_one' := by simp [Pi.one_def (f := fun _ : n ↦ 𝕜)]
  map_mul' f g := by
    have {a b c d e f : Matrix n n 𝕜} : (a * b * c) * (d * e * f) = a * (b * (c * d) * e) * f := by
      simp only [mul_assoc]
    simp only [this, ContinuousMap.coe_mul, SetLike.coe_mem, unitary.star_mul_self_of_mem, mul_one,
      diagonal_mul_diagonal, Function.comp_apply]
    congr! with i
    simp
  map_zero' := by simp [Pi.zero_def (f := fun _ : n ↦ 𝕜)]
  map_add' f g := by
    simp only [ContinuousMap.coe_add, ← add_mul, ← mul_add, diagonal_add, Function.comp_apply]
    congr! with i
    simp
  commutes' r := by
    simp only [Function.comp, algebraMap_apply, smul_eq_mul, mul_one]
    rw [IsScalarTower.algebraMap_apply ℝ 𝕜 _ r, RCLike.algebraMap_eq_ofReal,
      ← mul_one (algebraMap _ _ _), ← unitary.coe_mul_star_self hA.eigenvectorUnitary,
      ← Algebra.left_comm, unitary.coe_star, mul_assoc]
    congr!
  map_star' f := by
    simp only [star_trivial, StarMul.star_mul, star_star, star_eq_conjTranspose (diagonal _),
      diagonal_conjTranspose, mul_assoc]
    congr!
    ext
    simp

--spectrum of a matrix is a finite set, so C(σ(A), ℝ) might be finite-dimensional.
--If this is the case, then Continuous.closedEmbedding might work...but I don't think
--so, since the continuous functions will then only be Locally Compact...
--But LinearMap.closedEmbedding_of_injective might work, in this case.
--Otherwise, the best might be closedEmbedding_of_continuous_injective_closed.
--equivFnOfDiscrete gives that the continuous functions are the same as all functions
--if the domain is discrete
--Pi.discreteTopology gets that the product of discrete spaces is discrete. Can this
--be used to get that the spectrum has the discrete topology?
--finite_of_compact_of_discrete : a compact discrete space is finite
--Is the spectrum of any Hermitian matrix necessarily Hausdorff? If so, then the
--topology on the spectrum must be discrete. Maybe this isn't needed, though,
--because the dimension can only be less if there are fewer open sets. Check this.
--finiteDimensional_finsupp
-- linearEquivFunOnFinite

--variable [CompactSpace (spectrum ℝ A)]
--isCompact_iff_compactSpace
-- Matrix.IsHermitian.eigenvalues (map to the reals) Is map with finite domain finite?

--#synth ContinuousSMul ℝ C(spectrum ℝ A, ℝ)
--#synth CompactSpace (spectrum ℝ A)

theorem eigenvalues_eq_spectrum {a : Matrix n n 𝕜} (ha : IsHermitian A) : (spectrum ℝ a) = Set.range (ha.eigenvalues) := by
    sorry --simp? [toLin, Module.End.hasEigenvalue_iff_mem_spectrum]

theorem finite_spectrum {a : Matrix n n 𝕜} (ha : IsHermitian a) : (spectrum ℝ a).Finite := by
   have H := Set.finite_range (ha.eigenvalues)
   exact (ha.eigenvalues_eq_spectrum).symm ▸ H

theorem compact_spectrum {a : Matrix n n 𝕜} (ha : IsHermitian a) : CompactSpace (spectrum ℝ a) := by
   convert Finite.compactSpace (X := spectrum ℝ a)
   refine Set.finite_coe_iff.mpr ?_
   apply finite_spectrum
   assumption

instance instContinuousFunctionalCalculus :
    ContinuousFunctionalCalculus ℝ (IsHermitian : Matrix n n 𝕜 → Prop) where
exists_cfc_of_predicate := by
    intro a ha
    use (φ ha)
    constructor
    · have h0 : FiniteDimensional ℝ C(spectrum ℝ a, ℝ) := by sorry
      have hφ : LinearMap.ker ha.φ = ⊥ := by sorry
      have H := ha.compact_spectrum
      apply LinearMap.closedEmbedding_of_injective (𝕜 := ℝ) (E := C(spectrum ℝ a, ℝ))
                (F := Matrix n n 𝕜) (f := ha.φ) hφ
    · sorry--probably an easy lemma saying that *-homs preserve Hermitian elements...



--theorem spec_EuclideanCLM_eq_spec : spectrum 𝕜 (toEuclideanCLM (𝕜:= 𝕜) A) = spectrum 𝕜 A :=
--    AlgEquiv.spectrum_eq _ A

--theorem spec_EuclideanCLM_eq_spec_toEuclideanLin : spectrum 𝕜 (toEuclideanCLM (𝕜:= 𝕜) A)
--    = spectrum 𝕜 (toEuclideanLin A) := AlgEquiv.spectrum_eq (LinearAlgEquiv) _

--#check Matrix.coe_toEuclideanCLM_eq_toEuclideanLin
--the above might be useful when refactoring all of this

--noncomputable def f1 : n → spectrum ℝ A := by
--apply Set.codRestrict (fun (i : n) ↦ hA.eigenvalues i)
--apply eigenvalue_mem_real

--noncomputable def f2 : n → spectrum ℝ A := Set.codRestrict (fun (i : n) ↦ hA.eigenvalues i) (spectrum ℝ A) (hA.eigenvalue_mem_real)

--noncomputable def f : n → spectrum ℝ A := by
--apply Set.codRestrict fun (i : n) ↦ (RCLike.ofReal ∘ hA.eigenvalues) i
--have H := spec_toEuclideanLin_eq_spec (𝕜 := 𝕜) (n := n)
--      ▸ eigenvalue_mem_toEuclideanLin_spectrum_RCLike hA
--intro i
--apply spectrum.of_algebraMap_mem 𝕜
--refine H i

--noncomputable def φ₀ : C(spectrum ℝ A, ℝ) →  Matrix n n 𝕜 :=
--  fun g => (eigenvectorUnitary hA : Matrix n n 𝕜) * diagonal (RCLike.ofReal ∘ g ∘ f hA)
--      * star (eigenvectorUnitary hA : Matrix n n 𝕜)

--noncomputable def φ1 : C(spectrum ℝ A, ℝ) →  Matrix n n 𝕜 :=
--fun g => (eigenvectorUnitary hA : Matrix n n 𝕜) * diagonal (RCLike.ofReal ∘ g ∘ Set.codRestrict (fun (i : n) ↦ hA.eigenvalues i) (spectrum ℝ A) (hA.eigenvalue_mem_real))
--      * star (eigenvectorUnitary hA : Matrix n n 𝕜)
--
