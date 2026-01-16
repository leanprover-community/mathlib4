/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Algebra.Order.Module.HahnEmbedding
public import Mathlib.Algebra.Module.LinearMap.Rat
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Data.Real.Embedding
public import Mathlib.GroupTheory.DivisibleHull

/-!

# Hahn embedding theorem

In this file, we prove the Hahn embedding theorem: every linearly ordered abelian group
can be embedded as an ordered subgroup of `Lex ℝ⟦Ω⟧`, where `Ω` is the type of finite
Archimedean classes of the group. The theorem is stated as `hahnEmbedding_isOrderedAddMonoid`.

## References

* [A. H. Clifford, *Note on Hahn’s theorem on ordered Abelian groups.*][clifford1954]

-/

@[expose] public section

open ArchimedeanClass HahnSeries

variable (M : Type*) [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

section Module
variable [Module ℚ M] [IsOrderedModule ℚ M]

instance : Nonempty (HahnEmbedding.Seed ℚ M ℝ) := by
  obtain ⟨strata⟩ : Nonempty (HahnEmbedding.ArchimedeanStrata ℚ M) := inferInstance
  choose f hf using fun c ↦ Archimedean.exists_orderAddMonoidHom_real_injective (strata.stratum c)
  refine ⟨strata, fun c ↦ (f c).toRatLinearMap, fun c ↦ ?_⟩
  apply Monotone.strictMono_of_injective
  · simpa using OrderHomClass.monotone (f c)
  · simpa using hf c

theorem hahnEmbedding_isOrderedModule_rat :
    ∃ f : M →ₗ[ℚ] Lex ℝ⟦FiniteArchimedeanClass M⟧, StrictMono f ∧
      ∀ a, .mk a = FiniteArchimedeanClass.withTopOrderIso M (ofLex (f a)).orderTop := by
  apply hahnEmbedding_isOrderedModule

end Module

/--
**Hahn embedding theorem**

For a linearly ordered additive group `M`, there exists an injective `OrderAddMonoidHom` from `M` to
`Lex ℝ⟦FiniteArchimedeanClass M⟧` that sends each `a : M` to an element of the `a`-Archimedean class
of the Hahn series.
-/
theorem hahnEmbedding_isOrderedAddMonoid :
    ∃ f : M →+o Lex ℝ⟦FiniteArchimedeanClass M⟧, Function.Injective f ∧
      ∀ a, .mk a = FiniteArchimedeanClass.withTopOrderIso M (ofLex (f a)).orderTop := by
  /-
  The desired embedding is the composition of three functions:

      Group type                                    `ArchimedeanClass` / `HahnSeries.orderTop` type

      `M`                                           `ArchimedeanClass M`
  `f₁` ↓+o                                           ↓o~
      `D-Hull M`                                    `ArchimedeanClass (D-Hull M)`
  `f₂` ↓+o                                           ↓o~
      `Lex ℝ⟦F-A-Class (D-Hull M)⟧`                 `WithTop (F-A-Class (D-Hull M))`
  `f₃` ↓+o(~)                                        ↓o~
      `Lex ℝ⟦F-A-Class M⟧`                          `WithTop (F-A-Class M)`
  -/
  let f₁ := DivisibleHull.coeOrderAddMonoidHom M
  have hf₁ : Function.Injective f₁ := DivisibleHull.coe_injective
  have hf₁class (a : M) : mk a = (DivisibleHull.archimedeanClassOrderIso M).symm (mk (f₁ a)) := by
    simp [f₁]
  obtain ⟨f₂', hf₂', hf₂class'⟩ := hahnEmbedding_isOrderedModule_rat (DivisibleHull M)
  let f₂ := OrderAddMonoidHom.mk f₂'.toAddMonoidHom hf₂'.monotone
  have hf₂ : Function.Injective f₂ := hf₂'.injective
  have hf₂class (a : DivisibleHull M) :
      mk a = (FiniteArchimedeanClass.withTopOrderIso (DivisibleHull M)) (ofLex (f₂ a)).orderTop :=
    hf₂class' a
  let f₃ : Lex ℝ⟦FiniteArchimedeanClass (DivisibleHull M)⟧ →+o Lex ℝ⟦FiniteArchimedeanClass M⟧ :=
    HahnSeries.embDomainOrderAddMonoidHom
    (FiniteArchimedeanClass.congrOrderIso (DivisibleHull.archimedeanClassOrderIso M).symm)
  have hf₃ : Function.Injective f₃ := HahnSeries.embDomainOrderAddMonoidHom_injective _
  have hf₃class (a : Lex ℝ⟦FiniteArchimedeanClass (DivisibleHull M)⟧) :
      (ofLex a).orderTop = OrderIso.withTopCongr
      ((FiniteArchimedeanClass.congrOrderIso (DivisibleHull.archimedeanClassOrderIso M)))
      (ofLex (f₃ a)).orderTop := by
    rw [← OrderIso.symm_apply_eq]
    simp [f₃, ← OrderIso.withTopCongr_symm]
  refine ⟨f₃.comp (f₂.comp f₁), hf₃.comp (hf₂.comp hf₁), ?_⟩
  intro a
  simp_rw [hf₁class, hf₂class, hf₃class, OrderAddMonoidHom.comp_apply]
  cases (ofLex (f₃ (f₂ (f₁ a)))).orderTop with
  | top => simp
  | coe x => simp [-DivisibleHull.archimedeanClassOrderIso_apply]
