/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Scott Morrison, Jakob von Raumer

! This file was ported from Lean 3 source module category_theory.abelian.projective
! leanprover-community/mathlib commit f0c8bf9245297a541f468be517f1bde6195105e9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Homology.QuasiIso
import Mathbin.CategoryTheory.Preadditive.ProjectiveResolution
import Mathbin.CategoryTheory.Preadditive.Yoneda.Limits
import Mathbin.CategoryTheory.Preadditive.Yoneda.Projective

/-!
# Abelian categories with enough projectives have projective resolutions

When `C` is abelian `projective.d f` and `f` are exact.
Hence, starting from an epimorphism `P ⟶ X`, where `P` is projective,
we can apply `projective.d` repeatedly to obtain a projective resolution of `X`.
-/


noncomputable section

open CategoryTheory

open CategoryTheory.Limits

open Opposite

universe v u v' u'

namespace CategoryTheory

open CategoryTheory.Projective

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- When `C` is abelian, `projective.d f` and `f` are exact.
-/
theorem exact_d_f [EnoughProjectives C] {X Y : C} (f : X ⟶ Y) : Exact (d f) f :=
  (Abelian.exact_iff _ _).2 <|
    ⟨by simp, zero_of_epi_comp (π _) <| by rw [← category.assoc, cokernel.condition]⟩
#align category_theory.exact_d_f CategoryTheory.exact_d_f

/-- The preadditive Co-Yoneda functor on `P` preserves colimits if `P` is projective. -/
def preservesFiniteColimitsPreadditiveCoyonedaObjOfProjective (P : C) [hP : Projective P] :
    PreservesFiniteColimits (preadditiveCoyonedaObj (op P)) :=
  by
  letI := (projective_iff_preserves_epimorphisms_preadditive_coyoneda_obj' P).mp hP
  apply functor.preserves_finite_colimits_of_preserves_epis_and_kernels
#align category_theory.preserves_finite_colimits_preadditive_coyoneda_obj_of_projective CategoryTheory.preservesFiniteColimitsPreadditiveCoyonedaObjOfProjective

/-- An object is projective if its preadditive Co-Yoneda functor preserves finite colimits. -/
theorem projective_of_preservesFiniteColimits_preadditiveCoyonedaObj (P : C)
    [hP : PreservesFiniteColimits (preadditiveCoyonedaObj (op P))] : Projective P :=
  by
  rw [projective_iff_preserves_epimorphisms_preadditive_coyoneda_obj']
  infer_instance
#align category_theory.projective_of_preserves_finite_colimits_preadditive_coyoneda_obj CategoryTheory.projective_of_preservesFiniteColimits_preadditiveCoyonedaObj

namespace ProjectiveResolution

/-!
Our goal is to define `ProjectiveResolution.of Z : ProjectiveResolution Z`.
The `0`-th object in this resolution will just be `projective.over Z`,
i.e. an arbitrarily chosen projective object with a map to `Z`.
After that, we build the `n+1`-st object as `projective.syzygies`
applied to the previously constructed morphism,
and the map to the `n`-th object as `projective.d`.
-/


variable [EnoughProjectives C]

/-- Auxiliary definition for `ProjectiveResolution.of`. -/
@[simps]
def ofComplex (Z : C) : ChainComplex C ℕ :=
  ChainComplex.mk' (Projective.over Z) (Projective.syzygies (Projective.π Z))
    (Projective.d (Projective.π Z)) fun ⟨X, Y, f⟩ =>
    ⟨Projective.syzygies f, Projective.d f, (exact_d_f f).w⟩
#align category_theory.ProjectiveResolution.of_complex CategoryTheory.ProjectiveResolution.ofComplex

/-- In any abelian category with enough projectives,
`ProjectiveResolution.of Z` constructs a projective resolution of the object `Z`.
-/
irreducible_def of (Z : C) : ProjectiveResolution Z :=
  { complex := ofComplex Z
    π :=
      ChainComplex.mkHom _ _ (Projective.π Z) 0
        (by
          simp
          exact (exact_d_f (projective.π Z)).w.symm)
        fun n _ => ⟨0, by ext⟩
    Projective := by rintro (_ | _ | _ | n) <;> apply projective.projective_over
    exact₀ := by simpa using exact_d_f (projective.π Z)
    exact := by
      rintro (_ | n) <;>
        · simp
          apply exact_d_f
    Epi := Projective.π_epi Z }
#align category_theory.ProjectiveResolution.of CategoryTheory.ProjectiveResolution.of

instance (priority := 100) (Z : C) : HasProjectiveResolution Z where out := ⟨of Z⟩

instance (priority := 100) : HasProjectiveResolutions C where out Z := by infer_instance

end ProjectiveResolution

end CategoryTheory

namespace HomologicalComplex.Hom

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- If `X` is a chain complex of projective objects and we have a quasi-isomorphism `f : X ⟶ Y[0]`,
then `X` is a projective resolution of `Y.` -/
def toSingle₀ProjectiveResolution {X : ChainComplex C ℕ} {Y : C}
    (f : X ⟶ (ChainComplex.single₀ C).obj Y) [QuasiIso f] (H : ∀ n, Projective (X.pt n)) :
    ProjectiveResolution Y where
  complex := X
  π := f
  Projective := H
  exact₀ := f.to_single₀_exact_d_f_at_zero
  exact := f.to_single₀_exact_at_succ
  Epi := f.to_single₀_epi_at_zero
#align homological_complex.hom.to_single₀_ProjectiveResolution HomologicalComplex.Hom.toSingle₀ProjectiveResolution

end HomologicalComplex.Hom

