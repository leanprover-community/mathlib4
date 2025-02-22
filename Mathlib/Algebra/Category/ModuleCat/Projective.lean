/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Kim Morrison
-/
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Module.Projective
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# The category of `R`-modules has enough projectives.
-/

universe v u u'

open CategoryTheory

open CategoryTheory.Limits

open LinearMap

open ModuleCat

open scoped Module

/-- The categorical notion of projective object agrees with the explicit module-theoretic notion. -/
theorem IsProjective.iff_projective {R : Type u} [Ring R] {P : Type max u v} [AddCommGroup P]
    [Module R P] : Module.Projective R P ↔ Projective (ModuleCat.of R P) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · letI : Module.Projective R (ModuleCat.of R P) := h
    refine ⟨fun E X epi => ?_⟩
    obtain ⟨f, h⟩ := Module.projective_lifting_property X.hom E.hom
      ((ModuleCat.epi_iff_surjective _).mp epi)
    exact ⟨ofHom f, hom_ext h⟩
  · refine Module.Projective.of_lifting_property.{u,v} ?_
    intro E X mE mX sE sX f g s
    haveI : Epi (↟f) := (ModuleCat.epi_iff_surjective (↟f)).mpr s
    letI : Projective (ModuleCat.of R P) := h
    exact ⟨(Projective.factorThru (↟g) (↟f)).hom,
      ModuleCat.hom_ext_iff.mp <| Projective.factorThru_comp (↟g) (↟f)⟩

namespace ModuleCat

variable {R : Type u} [Ring R] {M : ModuleCat.{max u v} R}

-- We transport the corresponding result from `Module.Projective`.
/-- Modules that have a basis are projective. -/
theorem projective_of_free {ι : Type u'} (b : Basis ι R M) : Projective M :=
  Projective.of_iso (ModuleCat.ofSelfIso M)
    (IsProjective.iff_projective.{v,u}.mp (Module.Projective.of_basis b))

/-- The category of modules has enough projectives, since every module is a quotient of a free
    module. -/
instance moduleCat_enoughProjectives : EnoughProjectives (ModuleCat.{max u v} R) where
  presentation M :=
    ⟨{  p := ModuleCat.of R (M →₀ R)
        projective :=
          projective_of_free.{v,u} (ι := M) (M := ModuleCat.of R (M →₀ R)) <|
            Finsupp.basisSingleOne
        f := ofHom <| Finsupp.basisSingleOne.constr ℕ _root_.id
        epi := (epi_iff_range_eq_top _).mpr
            (range_eq_top.2 fun m => ⟨Finsupp.single m (1 : R), by
              simp [Finsupp.linearCombination_single, Basis.constr] ⟩)}⟩

end ModuleCat
