/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/

import Mathlib.Algebra.Order.Module.HahnEmbedding
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Real.Embedding
import Mathlib.GroupTheory.Divisible
import Mathlib.GroupTheory.DivisibleCompletion
import Mathlib.Algebra.Module.LinearMap.Rat

/-!

# Hahn embedding theorem

In this file, we prove the Hahn embedding theorem: every linearly ordered abelian group
can be embedded as an ordered subgroup of `Lex (HahnSeries Ω ℝ)`, where Ω is the top-less
Archimedean classes of the group. The theorem is stated as
`exists_orderAddMonoidHom_hahnSeries_real_injective`.

-/

variable (M : Type*) [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

section Module
variable [Module ℚ M] [PosSMulMono ℚ M]

instance : Nonempty (HahnEmbeddingSeed ℚ M ℝ) := by
  have grades (A : ArchimedeanClass M) : ∃ G : Submodule ℚ M, IsArchimedeanGrade ℚ A G := by
    apply IsModularLattice.exists_disjoint_and_sup_eq
    apply ArchimedeanSubgroup.submodule_antitone
    apply UpperSet.Ici_le_Ioi
  choose g hg using grades
  choose f hf using fun A ↦ (hg A).archimedean.exists_orderAddMonoidHom_real_injective
  refine ⟨g, fun A ↦ (f A).toRatLinearMap, hg, fun A ↦ ?_⟩
  apply Monotone.strictMono_of_injective
  · simpa using (f A).monotone'
  · simpa using hf A

theorem exists_linearMap_hahnSeries_real_strictMono :
    ∃ f : M →ₗ[ℚ] Lex (HahnSeries (ArchimedeanClass₀ M) ℝ), StrictMono f := by
  apply exists_linearMap_hahnSeries_strictMono

end Module

theorem exists_orderAddMonoidHom_hahnSeries_real_injective :
    ∃ f : M →+o Lex (HahnSeries (ArchimedeanClass₀ M) ℝ), Function.Injective f := by
  let f₁ := DivisibleCompletion.orderAddMonoidHom M
  have hf₁ : Function.Injective f₁ := DivisibleCompletion.addMonoidHom_injective M
  obtain ⟨g, hg⟩ := exists_linearMap_hahnSeries_real_strictMono (DivisibleCompletion M)
  let f₂ := OrderAddMonoidHom.mk g.toAddMonoidHom hg.monotone
  have hf₂ : Function.Injective f₂ := hg.injective
  let f₃ : Lex (HahnSeries (ArchimedeanClass₀ (DivisibleCompletion M)) ℝ) →+o
      Lex (HahnSeries (ArchimedeanClass₀ M) ℝ) :=
    HahnSeries.embDomainOrderAddMonoidHom (DivisibleCompletion.archimedeanClass₀OrderIso M).symm
  have hf₃ : Function.Injective f₃ := HahnSeries.embDomainOrderAddMonoidHom_injective _
  exact ⟨f₃.comp (f₂.comp f₁), hf₃.comp (hf₂.comp hf₁)⟩
