/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Scott Morrison, Jakob von Raumer

! This file was ported from Lean 3 source module category_theory.abelian.projective
! leanprover-community/mathlib commit f0c8bf9245297a541f468be517f1bde6195105e9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Preadditive.ProjectiveResolution
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
import Mathlib.CategoryTheory.Preadditive.Yoneda.Projective

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
    ⟨by simp, zero_of_epi_comp (π _) <| by rw [← Category.assoc, cokernel.condition]⟩
#align category_theory.exact_d_f CategoryTheory.exact_d_f

/-- The preadditive Co-Yoneda functor on `P` preserves colimits if `P` is projective. -/
def preservesFiniteColimitsPreadditiveCoyonedaObjOfProjective (P : C) [hP : Projective P] :
    PreservesFiniteColimits (preadditiveCoyonedaObj (op P)) := by
  haveI := (projective_iff_preservesEpimorphisms_preadditiveCoyoneda_obj' P).mp hP
  -- porting note: this next instance wasn't necessary in Lean 3
  haveI := @Functor.preservesEpimorphisms_of_preserves_of_reflects _ _ _ _ _ _ _ _ this _
  apply Functor.preservesFiniteColimitsOfPreservesEpisAndKernels
#align category_theory.preserves_finite_colimits_preadditive_coyoneda_obj_of_projective CategoryTheory.preservesFiniteColimitsPreadditiveCoyonedaObjOfProjective

/-- An object is projective if its preadditive Co-Yoneda functor preserves finite colimits. -/
theorem projective_of_preservesFiniteColimits_preadditiveCoyonedaObj (P : C)
    [hP : PreservesFiniteColimits (preadditiveCoyonedaObj (op P))] : Projective P := by
  rw [projective_iff_preservesEpimorphisms_preadditiveCoyoneda_obj']
  -- porting note: this next line wasn't necessary in Lean 3
  dsimp only [preadditiveCoyoneda]
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

-- Porting note: compilation of CategoryTheory.ProjectiveResolution.ofComplex took 4.95s
-- (was much faster in lean 3)
/-- Auxiliary definition for `ProjectiveResolution.of`. -/
@[simps!]
def ofComplex (Z : C) : ChainComplex C ℕ :=
  ChainComplex.mk' (Projective.over Z) (Projective.syzygies (Projective.π Z))
    (Projective.d (Projective.π Z)) fun ⟨_, _, f⟩ =>
    ⟨Projective.syzygies f, Projective.d f, (exact_d_f f).w⟩
set_option linter.uppercaseLean3 false in
#align category_theory.ProjectiveResolution.of_complex CategoryTheory.ProjectiveResolution.ofComplex

-- Porting note: the π in `of` was very, very slow. To assist,
-- implicit arguments were filled in and this particular proof was broken
-- out into a separate result
theorem ofComplex_sq_10_comm (Z : C) :
    0 ≫ HomologicalComplex.d ((ChainComplex.single₀ C).obj Z) 1 0 =
    HomologicalComplex.d (ofComplex Z) 1 0 ≫ Projective.π Z := by
  simp only [ofComplex_X, ChainComplex.single₀_obj_X_0, ChainComplex.single₀_obj_X_succ,
    ComplexShape.down_Rel, not_true, ChainComplex.single₀_obj_X_d, comp_zero, ofComplex_d,
    eqToHom_refl, Category.id_comp, dite_eq_ite, ite_true]
  exact (exact_d_f (Projective.π Z)).w.symm

-- Porting note: the `exact` in `of` was very, very slow. To assist,
-- the whole proof was broken out into a separate result
theorem exact_ofComplex (Z : C) (n : ℕ) :
    Exact (HomologicalComplex.d (ofComplex Z) (n + 2) (n + 1))
    (HomologicalComplex.d (ofComplex Z) (n + 1) n) :=
  match n with
-- Porting note: used to be simp; apply exact_d_f on both branches
    | 0 => by simp; apply exact_d_f
    | m+1 => by
      simp only [ofComplex_X, ComplexShape.down_Rel, ofComplex_d, eqToHom_refl,
        Category.id_comp, dite_eq_ite, not_true, ite_true]
      erw [if_pos (c := m + 1 + 1 + 1 = m + 2 + 1) rfl]
      apply exact_d_f

/-- In any abelian category with enough projectives,
`ProjectiveResolution.of Z` constructs a projective resolution of the object `Z`.
-/
irreducible_def of (Z : C) : ProjectiveResolution Z :=
  { complex := ofComplex Z
    π := ChainComplex.mkHom (ofComplex Z) ((ChainComplex.single₀ C).obj Z) (Projective.π Z) 0
           (ofComplex_sq_10_comm Z) (fun n _ ↦ ⟨0, by
           -- Porting note: broken ext
            apply HasZeroObject.to_zero_ext ⟩)
    projective := by rintro (_ | _ | _ | n) <;> apply Projective.projective_over
    exact₀ := by simpa using exact_d_f (Projective.π Z)
    exact := exact_ofComplex Z
    epi := Projective.π_epi Z }
set_option linter.uppercaseLean3 false in
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
    -- porting note: autoporter incorrectly went for `X.pt` at the end there
    (f : X ⟶ (ChainComplex.single₀ C).obj Y) [QuasiIso f] (H : ∀ n, Projective (X.X n)) :
    ProjectiveResolution Y where
  complex := X
  π := f
  projective := H
  -- porting note: Lean 3 used dot notation `f.to_single₀_exact_d_f_at_zero` etc
  exact₀ := HomologicalComplex.Hom.to_single₀_exact_d_f_at_zero f
  exact := HomologicalComplex.Hom.to_single₀_exact_at_succ f
  epi := HomologicalComplex.Hom.to_single₀_epi_at_zero f
set_option linter.uppercaseLean3 false in
#align homological_complex.hom.to_single₀_ProjectiveResolution HomologicalComplex.Hom.toSingle₀ProjectiveResolution

end HomologicalComplex.Hom
