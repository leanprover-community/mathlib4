/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang, Wanyi He, Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.Submodule.Pointwise

/-!
# Categorical constructions for `IsSMulRegular`
-/

@[expose] public section

universe u v w

variable {R : Type u} [CommRing R] (M : ModuleCat.{v} R)

open CategoryTheory Abelian Pointwise

lemma LinearMap.exact_lsmul_mkQ_smul_top (M : Type v) [AddCommGroup M] [Module R M] (r : R) :
    Function.Exact (LinearMap.lsmul _ M r) (r • (⊤ : Submodule R M)).mkQ := by
  intro x
  simp [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_smul_pointwise_iff_exists]

@[deprecated (since := "2026-04-13")]
alias LinearMap.exact_smul_id_smul_top_mkQ := LinearMap.exact_lsmul_mkQ_smul_top

namespace ModuleCat

/-- The short (exact) complex `M → M → M⧸xM` obtain from the scalar multiple of `x : R` on `M`. -/
@[simps!]
def smulShortComplex (r : R) : ShortComplex (ModuleCat R) :=
  ModuleCat.shortComplexOfCompEqZero (LinearMap.lsmul _ M r) (r • (⊤ : Submodule R M)).mkQ
    (LinearMap.exact_lsmul_mkQ_smul_top M r).linearMap_comp_eq_zero

@[simp]
lemma smulShortComplex_f_eq_smul_id (r : R) : (M.smulShortComplex r).f = r • 𝟙 M := rfl

lemma smulShortComplex_exact (r : R) : (smulShortComplex M r).Exact :=
  ModuleCat.shortComplex_exact _ (LinearMap.exact_lsmul_mkQ_smul_top M r)

instance smulShortComplex_g_epi (r : R) : Epi (smulShortComplex M r).g := by
  simpa [smulShortComplex, ModuleCat.epi_iff_surjective] using Submodule.mkQ_surjective _

end ModuleCat

variable {M} in
lemma IsSMulRegular.smulShortComplex_shortExact {r : R} (reg : IsSMulRegular M r) :
    (ModuleCat.smulShortComplex M r).ShortExact where
  exact := ModuleCat.smulShortComplex_exact M r
  mono_f := by simpa [ModuleCat.smulShortComplex, ModuleCat.mono_iff_injective] using reg
