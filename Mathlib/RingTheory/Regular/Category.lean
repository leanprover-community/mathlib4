/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang, Wanyi He, Nailin Guan
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Categorical constructions for `IsSMulRegular`
-/

@[expose] public section

universe u v w

variable {R : Type u} [CommRing R] (M : ModuleCat.{v} R)

open CategoryTheory Abelian Pointwise

lemma LinearMap.exact_lsmul_smul_top_mkQ (M : Type v) [AddCommGroup M] [Module R M] (r : R) :
    Function.Exact (LinearMap.lsmul _ M r) (r • (⊤ : Submodule R M)).mkQ := by
  intro x
  simp [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_smul_pointwise_iff_exists]

@[deprecated (since := "2026-04-13")]
alias LinearMap.exact_smul_id_smul_top_mkQ := LinearMap.exact_lsmul_smul_top_mkQ

namespace ModuleCat

/-- The short (exact) complex `M → M → M⧸xM` obtain from the scalar multiple of `x : R` on `M`. -/
@[simps!]
def smulShortComplex (r : R) : ShortComplex (ModuleCat R) :=
  ModuleCat.shortComplexOfCompEqZero (LinearMap.lsmul _ M r) (r • (⊤ : Submodule R M)).mkQ
    (LinearMap.exact_lsmul_smul_top_mkQ M r).linearMap_comp_eq_zero

lemma smulShortComplex_f_eq_smul_id (r : R) : (M.smulShortComplex r).f = r • 𝟙 M := rfl

lemma smulShortComplex_f_hom_eq_smul_id (r : R) :
    (M.smulShortComplex r).f.hom = r • LinearMap.id := rfl

lemma smulShortComplex_exact (r : R) : (smulShortComplex M r).Exact :=
  ModuleCat.shortComplex_exact _ (LinearMap.exact_lsmul_smul_top_mkQ M r)

instance smulShortComplex_g_epi (r : R) : Epi (smulShortComplex M r).g := by
  simpa [smulShortComplex, ModuleCat.epi_iff_surjective] using Submodule.mkQ_surjective _

end ModuleCat

variable {M} in
lemma IsSMulRegular.smulShortComplex_shortExact {r : R} (reg : IsSMulRegular M r) :
    (ModuleCat.smulShortComplex M r).ShortExact where
  exact := ModuleCat.smulShortComplex_exact M r
  mono_f := by simpa [ModuleCat.smulShortComplex, ModuleCat.mono_iff_injective] using reg

namespace CategoryTheory.Abelian

variable [Small.{v} R] {M N : ModuleCat.{v} R}

set_option backward.isDefEq.respectTransparency false in
lemma Ext.smul_id_postcomp_eq_zero_of_mem_ann {r : R} (mem_ann : r ∈ Module.annihilator R N)
    (n : ℕ) : AddCommGrpCat.ofHom ((Ext.mk₀ (r • (𝟙 M))).postcomp N (add_zero n)) = 0 := by
  ext h
  have : r • (𝟙 N) = 0 := ModuleCat.hom_ext (LinearMap.ext (Module.mem_annihilator.mp mem_ann ·))
  have smul_eq : r • h = (Ext.mk₀ (r • (𝟙 N))).comp h (zero_add n) := by simp [Ext.mk₀_smul]
  simp [Ext.mk₀_smul, this, smul_eq]

lemma Ext.smulShortComplex_f_postcomp_eq_zero_of_mem_ann {r : R}
    (mem_ann : r ∈ Module.annihilator R N) (n : ℕ) :
    AddCommGrpCat.ofHom ((Ext.mk₀ (M.smulShortComplex r).f).postcomp N (add_zero n)) = 0 := by
  simpa [M.smulShortComplex_f_eq_smul_id] using Ext.smul_id_postcomp_eq_zero_of_mem_ann mem_ann n

end CategoryTheory.Abelian
