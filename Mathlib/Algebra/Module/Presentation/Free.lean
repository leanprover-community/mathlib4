/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.Algebra.Module.Presentation.Basic
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.Logic.UnivLE

/-!
# Presentation of free modules

A module is free iff it admits a presentation with generators but no relation,
see `Module.free_iff_exists_presentation`.

-/

universe w w₀ w₁ v u

namespace Module

variable {A : Type u} [Ring A] (relations : Relations.{w₀, w₁} A)
  (M : Type v) [AddCommGroup M] [Module A M]

namespace Relations

variable [IsEmpty relations.R]

/-- If `relations : Relations A` involved no relation, then it has an obvious
solution in the module `relations.G →₀ A`. -/
@[simps]
noncomputable def solutionFinsupp : relations.Solution (relations.G →₀ A) where
  var g := Finsupp.single g 1
  linearCombination_var_relation r := by exfalso; exact IsEmpty.false r

/-- If `relations : Relations A` involves no relations (`[IsEmpty relations.R]`),
then the free module `relations.G →₀ A` satisfies the universal property of the
corresponding module defined by generators (and relations). -/
noncomputable def solutionFinsupp.isPresentationCore :
    Solution.IsPresentationCore.{w} relations.solutionFinsupp where
  desc s := Finsupp.linearCombination _ s.var
  postcomp_desc := by aesop
  postcomp_injective h := by ext; apply Solution.congr_var h

lemma solutionFinsupp_isPresentation :
    relations.solutionFinsupp.IsPresentation :=
  (solutionFinsupp.isPresentationCore relations).isPresentation

section

variable {M} {relations} {solution : relations.Solution M}
    (h : solution.IsPresentation)

include h

lemma Solution.IsPresentation.free  :
    Module.Free A M :=
  Free.of_equiv ((solutionFinsupp_isPresentation relations).uniq h)

/-- The basis of a module that is given by a presentation involving no relation. -/
noncomputable def Solution.IsPresentation.basis :
    Basis relations.G A M :=
  .ofRepr ((solutionFinsupp_isPresentation relations).uniq h).symm

@[simp]
lemma Solution.IsPresentation.basis_apply (i : relations.G) :
    h.basis i = solution.var i :=
  uniq_var _ _ _

end

end Relations

variable (A)

/-- The presentation of the `A`-module `G →₀ A` with generators indexed by `G`,
and no relation. (Note that there is an auxiliary universe parameter `w₁` for the
empty type `R`.) -/
@[simps! G R var]
noncomputable def presentationFinsupp (G : Type w₀) :
    Presentation.{w₀, w₁} A (G →₀ A) where
  G := G
  R := PEmpty.{w₁ + 1}
  relation := by rintro ⟨⟩
  toSolution := Relations.solutionFinsupp _
  toIsPresentation := by exact Relations.solutionFinsupp_isPresentation _

lemma free_iff_exists_presentation :
    Free A M ↔ ∃ (p : Presentation.{v, w₁} A M), IsEmpty p.R := by
  constructor
  · rw [free_def.{_, _, v}]
    rintro ⟨G, ⟨⟨e⟩⟩⟩
    exact ⟨(presentationFinsupp A G).ofLinearEquiv e.symm,
      by dsimp; infer_instance⟩
  · rintro ⟨p, h⟩
    exact p.toIsPresentation.free

end Module

namespace Basis

variable {A : Type u} [Ring A] {M : Type v} [AddCommGroup M] [Module A M] {ι : Type w}
  (b : Basis ι A M)

/-- The presentation of a module given by a basis. -/
@[simps!]
noncomputable def presentation : Module.Presentation A M :=
  (Module.presentationFinsupp.{w, w} A ι).ofLinearEquiv b.repr.symm

instance : IsEmpty (b.presentation.R) := by dsimp; infer_instance

end Basis
