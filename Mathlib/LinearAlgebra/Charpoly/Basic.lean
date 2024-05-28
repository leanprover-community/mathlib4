/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.FieldTheory.Minpoly.Field

#align_import linear_algebra.charpoly.basic from "leanprover-community/mathlib"@"d3e8e0a0237c10c2627bf52c246b15ff8e7df4c0"

/-!

# Characteristic polynomial

We define the characteristic polynomial of `f : M →ₗ[R] M`, where `M` is a finite and
free `R`-module. The proof that `f.charpoly` is the characteristic polynomial of the matrix of `f`
in any basis is in `LinearAlgebra/Charpoly/ToMatrix`.

## Main definition

* `LinearMap.charpoly f` : the characteristic polynomial of `f : M →ₗ[R] M`.

-/


universe u v w

variable {R : Type u} {M : Type v} [CommRing R] [Nontrivial R]
variable [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] (f : M →ₗ[R] M)

open Matrix Polynomial

noncomputable section

open Module.Free Polynomial Matrix

namespace LinearMap

section Basic

/-- The characteristic polynomial of `f : M →ₗ[R] M`. -/
def charpoly : R[X] :=
  (toMatrix (chooseBasis R M) (chooseBasis R M) f).charpoly
#align linear_map.charpoly LinearMap.charpoly

theorem charpoly_def : f.charpoly = (toMatrix (chooseBasis R M) (chooseBasis R M) f).charpoly :=
  rfl
#align linear_map.charpoly_def LinearMap.charpoly_def

end Basic

section Coeff

theorem charpoly_monic : f.charpoly.Monic :=
  Matrix.charpoly_monic _
#align linear_map.charpoly_monic LinearMap.charpoly_monic

open FiniteDimensional in
lemma charpoly_natDegree [StrongRankCondition R] : natDegree (charpoly f) = finrank R M := by
  rw [charpoly, Matrix.charpoly_natDegree_eq_dim, finrank_eq_card_chooseBasisIndex]

end Coeff

section CayleyHamilton

/-- The **Cayley-Hamilton Theorem**, that the characteristic polynomial of a linear map, applied
to the linear map itself, is zero.

See `Matrix.aeval_self_charpoly` for the equivalent statement about matrices. -/
theorem aeval_self_charpoly : aeval f f.charpoly = 0 := by
  apply (LinearEquiv.map_eq_zero_iff (algEquivMatrix (chooseBasis R M)).toLinearEquiv).1
  rw [AlgEquiv.toLinearEquiv_apply, ← AlgEquiv.coe_algHom, ← Polynomial.aeval_algHom_apply _ _ _,
    charpoly_def]
  exact Matrix.aeval_self_charpoly _
#align linear_map.aeval_self_charpoly LinearMap.aeval_self_charpoly

theorem isIntegral : IsIntegral R f :=
  ⟨f.charpoly, ⟨charpoly_monic f, aeval_self_charpoly f⟩⟩
#align linear_map.is_integral LinearMap.isIntegral

theorem minpoly_dvd_charpoly {K : Type u} {M : Type v} [Field K] [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] (f : M →ₗ[K] M) : minpoly K f ∣ f.charpoly :=
  minpoly.dvd _ _ (aeval_self_charpoly f)
#align linear_map.minpoly_dvd_charpoly LinearMap.minpoly_dvd_charpoly

/-- Any endomorphism polynomial `p` is equivalent under evaluation to `p %ₘ f.charpoly`; that is,
`p` is equivalent to a polynomial with degree less than the dimension of the module. -/
theorem aeval_eq_aeval_mod_charpoly (p : R[X]) : aeval f p = aeval f (p %ₘ f.charpoly) :=
  (aeval_modByMonic_eq_self_of_root f.charpoly_monic f.aeval_self_charpoly).symm
#align linear_map.aeval_eq_aeval_mod_charpoly LinearMap.aeval_eq_aeval_mod_charpoly

/-- Any endomorphism power can be computed as the sum of endomorphism powers less than the
dimension of the module. -/
theorem pow_eq_aeval_mod_charpoly (k : ℕ) : f ^ k = aeval f (X ^ k %ₘ f.charpoly) := by
  rw [← aeval_eq_aeval_mod_charpoly, map_pow, aeval_X]
#align linear_map.pow_eq_aeval_mod_charpoly LinearMap.pow_eq_aeval_mod_charpoly

variable {f}

theorem minpoly_coeff_zero_of_injective (hf : Function.Injective f) :
    (minpoly R f).coeff 0 ≠ 0 := by
  intro h
  obtain ⟨P, hP⟩ := X_dvd_iff.2 h
  have hdegP : P.degree < (minpoly R f).degree := by
    rw [hP, mul_comm]
    refine degree_lt_degree_mul_X fun h => ?_
    rw [h, mul_zero] at hP
    exact minpoly.ne_zero (isIntegral f) hP
  have hPmonic : P.Monic := by
    suffices (minpoly R f).Monic by
      rwa [Monic.def, hP, mul_comm, leadingCoeff_mul_X, ← Monic.def] at this
    exact minpoly.monic (isIntegral f)
  have hzero : aeval f (minpoly R f) = 0 := minpoly.aeval _ _
  simp only [hP, mul_eq_comp, ext_iff, hf, aeval_X, map_eq_zero_iff, coe_comp, AlgHom.map_mul,
    zero_apply, Function.comp_apply] at hzero
  exact not_le.2 hdegP (minpoly.min _ _ hPmonic (ext hzero))
#align linear_map.minpoly_coeff_zero_of_injective LinearMap.minpoly_coeff_zero_of_injective

end CayleyHamilton

end LinearMap
