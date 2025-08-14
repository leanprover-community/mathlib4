/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang, Wanyi He, Nailin Guan
-/
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.QuotSMulTop

/-!
# Categorical constructions for `IsSMulRegular`
-/

universe u v w

variable {R : Type u} [CommRing R] (M : ModuleCat.{v} R)

open CategoryTheory Ideal Pointwise

lemma LinearMap.exact_smul_id_smul_top_mkQ (M : Type v) [AddCommGroup M] [Module R M] (r : R) :
    Function.Exact (r • LinearMap.id : M →ₗ[R] M) (r • (⊤ : Submodule R M)).mkQ := by
  intro x
  simp [Submodule.mem_smul_pointwise_iff_exists,
    Submodule.mem_smul_pointwise_iff_exists]

namespace ModuleCat

/-- The short (exact) complex `M → M → M⧸xM` obtain from the scalar multiple of `x : R` on `M`. -/
@[simps]
def smulShortComplex (r : R) :
    ShortComplex (ModuleCat R) where
  X₁ := M
  X₂ := M
  X₃ := ModuleCat.of R (QuotSMulTop r M)
  f := ModuleCat.ofHom (r • LinearMap.id)
  g := ModuleCat.ofHom (r • (⊤ : Submodule R M)).mkQ
  zero := by
    ext x
    exact (LinearMap.exact_smul_id_smul_top_mkQ M r).apply_apply_eq_zero x

lemma smulShortComplex_exact (r : R) : (smulShortComplex M r).Exact := by
  simp [smulShortComplex, ShortComplex.ShortExact.moduleCat_exact_iff_function_exact,
    LinearMap.exact_smul_id_smul_top_mkQ]

instance smulShortComplex_g_epi (r : R) : Epi (smulShortComplex M r).g := by
  simpa [smulShortComplex, ModuleCat.epi_iff_surjective] using Submodule.mkQ_surjective _

end ModuleCat

variable {M} in
lemma IsSMulRegular.smulShortComplex_shortExact {r : R} (reg : IsSMulRegular M r) :
    (ModuleCat.smulShortComplex M r).ShortExact where
  exact := ModuleCat.smulShortComplex_exact M r
  mono_f := by simpa [ModuleCat.smulShortComplex, ModuleCat.mono_iff_injective] using reg
