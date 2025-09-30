/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Kim Morrison
-/
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Group.Shrink
import Mathlib.Algebra.Module.Projective
import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-!
# The category of `R`-modules has enough projectives.
-/

universe v u w

open CategoryTheory Module ModuleCat

variable {R : Type u} [Ring R] (P : ModuleCat.{v} R)

instance ModuleCat.projective_of_categoryTheory_projective [Module.Projective R P] :
    CategoryTheory.Projective P := by
  refine ⟨fun E X epi => ?_⟩
  obtain ⟨f, h⟩ := Module.projective_lifting_property X.hom E.hom
    ((ModuleCat.epi_iff_surjective _).mp epi)
  exact ⟨ofHom f, hom_ext h⟩

instance ModuleCat.projective_of_module_projective [Small.{v} R] [Projective P] :
    Module.Projective R P := by
  refine Module.Projective.of_lifting_property ?_
  intro _ _ _ _ _ _ f g s
  have : Epi (↟f) := (ModuleCat.epi_iff_surjective (↟f)).mpr s
  exact ⟨(Projective.factorThru (↟g) (↟f)).hom,
    ModuleCat.hom_ext_iff.mp <| Projective.factorThru_comp (↟g) (↟f)⟩

/-- The categorical notion of projective object agrees with the explicit module-theoretic notion. -/
theorem IsProjective.iff_projective [Small.{v} R] (P : Type v) [AddCommGroup P] [Module R P] :
    Module.Projective R P ↔ Projective (of R P) :=
  ⟨fun _ => (of R P).projective_of_categoryTheory_projective,
    fun _ => (of R P).projective_of_module_projective⟩

namespace ModuleCat

variable {M : ModuleCat.{v} R}

-- We transport the corresponding result from `Module.Projective`.
/-- Modules that have a basis are projective. -/
theorem projective_of_free {ι : Type w} (b : Basis ι R M) : Projective M :=
  have : Module.Projective R M := Module.Projective.of_basis b
  M.projective_of_categoryTheory_projective

/-- The category of modules has enough projectives, since every module is a quotient of a free
  module. -/
instance enoughProjectives [Small.{v} R] : EnoughProjectives (ModuleCat.{v} R) where
  presentation M :=
    let e : Basis M R (M →₀ Shrink.{v} R) := ⟨Finsupp.mapRange.linearEquiv (Shrink.linearEquiv R R)⟩
    ⟨{p := ModuleCat.of R (M →₀ Shrink.{v} R)
      projective := projective_of_free e
      f := ofHom <| e.constr ℕ _root_.id
      epi := by
        rw [epi_iff_range_eq_top, LinearMap.range_eq_top]
        refine fun m ↦ ⟨Finsupp.single m 1, ?_⟩
        simp [e, Basis.constr_apply] }⟩

end ModuleCat
