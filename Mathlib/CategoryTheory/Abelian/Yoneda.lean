/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Preadditive.Yoneda.Projective
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Generator.Preadditive
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# Yoneda!
In this file we give a sufficient criterion for a restriction of the functor
`preadditiveCoyonedaObj G` to be full: this is the case if `C` is an abelian category and `G : C`
is a projective separator such that every object in the relevant subcategory is a quotient of `G`.
-/

open CategoryTheory Opposite Limits

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace CategoryTheory.Abelian

section

theorem preadditiveCoyonedaObj_map_surjective {G : C} [Projective G] (hG : IsSeparator G) {X : C}
    (p : G ⟶ X) [Epi p] {Y : C} :
    Function.Surjective ((preadditiveCoyonedaObj G).map : (X ⟶ Y) → _) := by
  rw [← Functor.coe_mapAddHom, ← AddCommGrp.hom_ofHom (preadditiveCoyonedaObj G).mapAddHom,
    ← AddCommGrp.epi_iff_surjective]
  let φ := preadditiveCoyonedaObj G
  let cm : ShortComplex C := ⟨kernel.ι p, p, by simp⟩
  have : cm.Exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)
  have : cm.op.Exact := this.op
  let top := cm.op.map (preadditiveYoneda.obj Y)
  let bot := cm.op.map (φ.op ⋙ preadditiveYoneda.obj (φ.obj Y))
  let map : top ⟶ bot := cm.op.mapNatTrans (preadditiveYonedaMap _ _)
  have mono : Mono cm.op.f := by simp [cm]; infer_instance
  have preserveEpimorphisms : φ.PreservesEpimorphisms :=
    (Projective.projective_iff_preservesEpimorphisms_preadditiveCoyonedaObj _).1 inferInstance
  have preservesHomology : φ.PreservesHomology := by
    apply Functor.preservesHomology_of_preservesEpis_and_kernels
  have preservesFiniteColimits : PreservesFiniteColimits φ := by
    apply Functor.preservesFiniteColimits_of_preservesHomology
  have preservesFiniteLimits : PreservesFiniteLimits φ.op :=
    preservesFiniteLimits_op _
  refine ShortComplex.epi_of_mono_of_epi_of_mono map ?_ ?_ ?_ ?_
  · exact this.map_of_mono_of_preservesKernel _ mono inferInstance
  · simp only [bot, ShortComplex.map_f]
    infer_instance
  · simp +zetaDelta [AddCommGrp.epi_iff_surjective, Functor.coe_mapAddHom]
    exact fun f => ⟨f (𝟙 G), by aesop_cat⟩
  · simp +zetaDelta [AddCommGrp.mono_iff_injective, Functor.coe_mapAddHom]
    have : (preadditiveCoyonedaObj G).Faithful := by
      rwa [← isSeparator_iff_faithful_preadditiveCoyonedaObj]
    exact Functor.map_injective _

end

theorem full_preadditiveCoyonedaObj {G : C} [Projective G] (hG : IsSeparator G)
    (hG₂ : ∀ X, ∃ (p : G ⟶ X), Epi p) : (preadditiveCoyonedaObj G).Full where
  map_surjective {X Y} := by
    obtain ⟨p, _⟩ := hG₂ X
    exact preadditiveCoyonedaObj_map_surjective hG p

end CategoryTheory.Abelian
