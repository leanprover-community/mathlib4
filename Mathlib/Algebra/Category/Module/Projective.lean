/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Scott Morrison

! This file was ported from Lean 3 source module algebra.category.Module.projective
! leanprover-community/mathlib commit 201a3f4a0e59b5f836fe8a6c1a462ee674327211
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Category.Module.EpiMono
import Mathbin.Algebra.Module.Projective
import Mathbin.CategoryTheory.Preadditive.Projective
import Mathbin.LinearAlgebra.FinsuppVectorSpace

/-!
# The category of `R`-modules has enough projectives.
-/


universe v u

open CategoryTheory

open CategoryTheory.Limits

open LinearMap

open ModuleCat

/-- The categorical notion of projective object agrees with the explicit module-theoretic notion. -/
theorem IsProjective.iff_projective {R : Type u} [Ring R] {P : Type max u v} [AddCommGroup P]
    [Module R P] : Module.Projective R P ↔ Projective (ModuleCat.of R P) :=
  by
  refine' ⟨fun h => _, fun h => _⟩
  · letI : Module.Projective R ↥(ModuleCat.of R P) := h
    exact
      ⟨fun E X f e epi =>
        Module.projective_lifting_property _ _ ((ModuleCat.epi_iff_surjective _).mp epi)⟩
  · refine' Module.Projective.of_lifting_property _
    intro E X mE mX sE sX f g s
    haveI : epi (↟f) := (ModuleCat.epi_iff_surjective (↟f)).mpr s
    letI : projective (ModuleCat.of R P) := h
    exact ⟨projective.factor_thru (↟g) (↟f), projective.factor_thru_comp (↟g) (↟f)⟩
#align is_projective.iff_projective IsProjective.iff_projective

namespace ModuleCat

variable {R : Type u} [Ring R] {M : ModuleCat.{max u v} R}

-- We transport the corresponding result from `module.projective`.
/-- Modules that have a basis are projective. -/
theorem projective_of_free {ι : Type _} (b : Basis ι R M) : Projective M :=
  Projective.of_iso (ModuleCat.ofSelfIso _)
    (IsProjective.iff_projective.mp (Module.Projective.of_basis b))
#align Module.projective_of_free ModuleCat.projective_of_free

/-- The category of modules has enough projectives, since every module is a quotient of a free
    module. -/
instance moduleCat_enoughProjectives : EnoughProjectives (ModuleCat.{max u v} R)
    where presentation M :=
    ⟨{  p := ModuleCat.of R (M →₀ R)
        Projective := projective_of_free Finsupp.basisSingleOne
        f := Finsupp.basisSingleOne.constr ℕ id
        Epi :=
          (epi_iff_range_eq_top _).mpr
            (range_eq_top.2 fun m => ⟨Finsupp.single m (1 : R), by simp [Basis.constr]⟩) }⟩
#align Module.Module_enough_projectives ModuleCat.moduleCat_enoughProjectives

end ModuleCat

