/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Module.Presentation.Basic
import Mathlib.Algebra.Module.FinitePresentation

/-!
# Characterization of finitely presented modules

A module is finitely presented (in the sense of `Module.FinitePresentation`) iff
it admits a presentation with finitely many generators and relations.

-/

universe w₀ w₁ v u

namespace Module

variable {A : Type u} [Ring A] {M : Type v} [AddCommGroup M] [Module A M]

-- to be moved
lemma _root_.Submodule.FG.exists_generators {N : Submodule A M} (hN : N.FG) :
    ∃ (G : Type w₀) (_ : Finite G) (g : G → M), Submodule.span A (Set.range g) = N := by
  rw [Submodule.fg_iff_exists_fin_generating_family] at hN
  obtain ⟨n, f, h⟩ := hN
  refine ⟨ULift (Fin n), inferInstance, f ∘ ULift.down, ?_⟩
  convert h
  ext x
  simp only [Set.mem_range, Function.comp_apply, ULift.exists]

namespace Presentation

variable (pres : Presentation A M)

lemma finite [Finite pres.G] :
    Module.Finite A M :=
  Finite.of_surjective _ pres.surjective_π

lemma finitePresentation [Finite pres.G] [Finite pres.R] :
    Module.FinitePresentation A M :=
  Module.finitePresentation_of_surjective _ pres.surjective_π (by
    rw [pres.ker_π]
    exact Submodule.fg_span (Set.finite_range _))

end Presentation

lemma finitePresentation_iff_exists_presentation :
    Module.FinitePresentation A M ↔
      ∃ (pres : Presentation.{w₀, w₁} A M), Finite pres.G ∧ Finite pres.R := by
  constructor
  · intro
    have h₁ : Module.Finite A M := inferInstance
    rw [finite_def] at h₁
    obtain ⟨G : Type w₀, _, var, hG⟩ := h₁.exists_generators
    obtain ⟨R : Type w₁, _, relation, hR⟩ :=
      (Module.FinitePresentation.fg_ker (Finsupp.linearCombination A var) (by
        rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination, hG])).exists_generators
    refine
     ⟨{ G := G
        R := R
        relation := relation
        var := var
        linearCombination_var_relation := fun r ↦ by
          rw [Submodule.ext_iff] at hR
          exact (hR _).1 (Submodule.subset_span ⟨_, rfl⟩)
        toIsPresentation := by
          rw [Relations.Solution.isPresentation_iff]
          exact ⟨hG, hR.symm⟩ },
        inferInstance, inferInstance⟩
  · rintro ⟨pres, _, _⟩
    exact pres.finitePresentation

end Module
