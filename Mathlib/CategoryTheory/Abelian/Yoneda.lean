/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
public import Mathlib.CategoryTheory.Abelian.Projective.Basic
public import Mathlib.CategoryTheory.Generator.Preadditive
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites

/-!
# Fullness of restrictions of `preadditiveCoyonedaObj`

In this file we give a sufficient criterion for a restriction of the functor
`preadditiveCoyonedaObj G` to be full: this is the case if `C` is an abelian category and `G : C`
is a projective separator such that every object in the relevant subcategory is a quotient of `G`.
-/
set_option backward.defeqAttrib.useBackward true

public section

open CategoryTheory Opposite Limits

universe v v' u u'

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace CategoryTheory.Abelian

section

attribute [local instance] preservesFiniteLimits_op

set_option backward.isDefEq.respectTransparency false in
theorem preadditiveCoyonedaObj_map_surjective {G : C} [Projective G] (hG : IsSeparator G) {X : C}
    (p : G ⟶ X) [Epi p] {Y : C} :
    Function.Surjective ((preadditiveCoyonedaObj G).map : (X ⟶ Y) → _) := by
  rw [← Functor.coe_mapAddHom, ← AddCommGrpCat.hom_ofHom (preadditiveCoyonedaObj G).mapAddHom,
    ← AddCommGrpCat.epi_iff_surjective]
  let cm : ShortComplex C := ⟨kernel.ι p, p, by simp⟩
  have exact : cm.Exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)
  have mono : Mono cm.op.f := by dsimp [cm]; infer_instance
  let φ := preadditiveCoyonedaObj G
  have faithful : φ.Faithful := by rwa [← isSeparator_iff_faithful_preadditiveCoyonedaObj]
  apply ShortComplex.epi_of_mono_of_epi_of_mono (cm.op.mapNatTrans (preadditiveYonedaMap _ _))
  · exact exact.op.map_of_mono_of_preservesKernel _ mono inferInstance
  · simp only [ShortComplex.map_f]
    infer_instance
  · suffices φ.map.Surjective by simpa [AddCommGrpCat.epi_iff_surjective, Functor.coe_mapAddHom]
    exact fun f => ⟨f (𝟙 G), by cat_disch⟩
  · simp [AddCommGrpCat.mono_iff_injective, Functor.coe_mapAddHom, Functor.map_injective]

end

variable {D : Type u'} [Category.{v'} D] (F : D ⥤ C)

theorem full_comp_preadditiveCoyonedaObj [F.Full] {G : C} [Projective G] (hG : IsSeparator G)
    (hG₂ : ∀ X, ∃ (p : G ⟶ F.obj X), Epi p) : (F ⋙ preadditiveCoyonedaObj G).Full where
  map_surjective {X Y} f := by
    obtain ⟨p, _⟩ := hG₂ X
    obtain ⟨f, rfl⟩ := preadditiveCoyonedaObj_map_surjective hG p f
    obtain ⟨f, rfl⟩ := F.map_surjective f
    exact ⟨f, rfl⟩

end CategoryTheory.Abelian
