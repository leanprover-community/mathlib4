/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebra.homology.differential_object
! leanprover-community/mathlib commit b535c2d5d996acd9b0554b76395d9c920e186f4f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Homology.HomologicalComplex
import Mathbin.CategoryTheory.DifferentialObject

/-!
# Homological complexes are differential graded objects.

We verify that a `homological_complex` indexed by an `add_comm_group` is
essentially the same thing as a differential graded object.

This equivalence is probably not particularly useful in practice;
it's here to check that definitions match up as expected.
-/


open CategoryTheory

open CategoryTheory.Limits

open scoped Classical

noncomputable section

namespace HomologicalComplex

variable {β : Type _} [AddCommGroup β] {b : β}

variable {V : Type _} [Category V] [HasZeroMorphisms V]

/-- Since `eq_to_hom` only preserves the fact that `X.X i = X.X j` but not `i = j`, this definition
is used to aid the simplifier. -/
abbrev CategoryTheory.DifferentialObject.xEqToHom
    (X : DifferentialObject (GradedObjectWithShift b V)) {i j : β} (h : i = j) : X.pt i ⟶ X.pt j :=
  eqToHom (congr_arg X.pt h)
#align category_theory.differential_object.X_eq_to_hom CategoryTheory.DifferentialObject.xEqToHom

@[simp]
theorem CategoryTheory.DifferentialObject.xEqToHom_refl
    (X : DifferentialObject (GradedObjectWithShift b V)) (i : β) : X.xEqToHom (refl i) = 𝟙 _ :=
  rfl
#align category_theory.differential_object.X_eq_to_hom_refl CategoryTheory.DifferentialObject.xEqToHom_refl

@[simp, reassoc]
theorem eq_to_hom_d (X : DifferentialObject (GradedObjectWithShift b V)) {x y : β} (h : x = y) :
    X.xEqToHom h ≫ X.d y = X.d x ≫ X.xEqToHom (by cases h; rfl) := by cases h; dsimp; simp
#align homological_complex.eq_to_hom_d HomologicalComplex.eq_to_hom_d

@[simp, reassoc]
theorem d_eqToHom (X : HomologicalComplex V (ComplexShape.up' b)) {x y z : β} (h : y = z) :
    X.d x y ≫ eqToHom (congr_arg X.pt h) = X.d x z := by cases h; simp
#align homological_complex.d_eq_to_hom HomologicalComplex.d_eqToHom

@[simp, reassoc]
theorem eq_to_hom_f' {X Y : DifferentialObject (GradedObjectWithShift b V)} (f : X ⟶ Y) {x y : β}
    (h : x = y) : X.xEqToHom h ≫ f.f y = f.f x ≫ Y.xEqToHom h := by cases h; simp
#align homological_complex.eq_to_hom_f' HomologicalComplex.eq_to_hom_f'

variable (b V)

attribute [local reducible] graded_object.has_shift

/-- The functor from differential graded objects to homological complexes.
-/
@[simps]
def dgoToHomologicalComplex :
    DifferentialObject (GradedObjectWithShift b V) ⥤ HomologicalComplex V (ComplexShape.up' b)
    where
  obj X :=
    { pt := fun i => X.pt i
      d := fun i j =>
        if h : i + b = j then X.d i ≫ X.xEqToHom (show i + (1 : ℤ) • b = j by simp [h]) else 0
      shape' := fun i j w => by dsimp at w ; convert dif_neg w
      d_comp_d' := fun i j k hij hjk => by
        dsimp at hij hjk ; substs hij hjk
        have : X.d i ≫ X.d _ = _ := (congr_fun X.d_squared i : _)
        reassoc! this
        simp [this] }
  map X Y f :=
    { f := f.f
      comm' := fun i j h => by
        dsimp at h ⊢
        subst h
        have : f.f i ≫ Y.d i = X.d i ≫ f.f (i + 1 • b) := (congr_fun f.comm i).symm
        reassoc! this
        simp only [category.comp_id, eq_to_hom_refl, dif_pos rfl, this, category.assoc,
          eq_to_hom_f'] }
#align homological_complex.dgo_to_homological_complex HomologicalComplex.dgoToHomologicalComplex

/-- The functor from homological complexes to differential graded objects.
-/
@[simps]
def homologicalComplexToDgo :
    HomologicalComplex V (ComplexShape.up' b) ⥤ DifferentialObject (GradedObjectWithShift b V)
    where
  obj X :=
    { pt := fun i => X.pt i
      d := fun i => X.d i (i + 1 • b)
      d_squared' := by ext i; dsimp; simp }
  map X Y f :=
    { f := f.f
      comm' := by ext i; dsimp; simp }
#align homological_complex.homological_complex_to_dgo HomologicalComplex.homologicalComplexToDgo

/-- The unit isomorphism for `dgo_equiv_homological_complex`.
-/
@[simps]
def dgoEquivHomologicalComplexUnitIso :
    𝟭 (DifferentialObject (GradedObjectWithShift b V)) ≅
      dgoToHomologicalComplex b V ⋙ homologicalComplexToDgo b V :=
  NatIso.ofComponents
    (fun X =>
      { Hom := { f := fun i => 𝟙 (X.pt i) }
        inv := { f := fun i => 𝟙 (X.pt i) } })
    (by tidy)
#align homological_complex.dgo_equiv_homological_complex_unit_iso HomologicalComplex.dgoEquivHomologicalComplexUnitIso

/-- The counit isomorphism for `dgo_equiv_homological_complex`.
-/
@[simps]
def dgoEquivHomologicalComplexCounitIso :
    homologicalComplexToDgo b V ⋙ dgoToHomologicalComplex b V ≅
      𝟭 (HomologicalComplex V (ComplexShape.up' b)) :=
  NatIso.ofComponents
    (fun X =>
      { Hom :=
          { f := fun i => 𝟙 (X.pt i)
            comm' := fun i j h => by
              dsimp at h ⊢; subst h
              delta homological_complex_to_dgo
              simp }
        inv :=
          { f := fun i => 𝟙 (X.pt i)
            comm' := fun i j h => by
              dsimp at h ⊢; subst h
              delta homological_complex_to_dgo
              simp } })
    (by tidy)
#align homological_complex.dgo_equiv_homological_complex_counit_iso HomologicalComplex.dgoEquivHomologicalComplexCounitIso

/-- The category of differential graded objects in `V` is equivalent
to the category of homological complexes in `V`.
-/
@[simps]
def dgoEquivHomologicalComplex :
    DifferentialObject (GradedObjectWithShift b V) ≌ HomologicalComplex V (ComplexShape.up' b)
    where
  Functor := dgoToHomologicalComplex b V
  inverse := homologicalComplexToDgo b V
  unitIso := dgoEquivHomologicalComplexUnitIso b V
  counitIso := dgoEquivHomologicalComplexCounitIso b V
#align homological_complex.dgo_equiv_homological_complex HomologicalComplex.dgoEquivHomologicalComplex

end HomologicalComplex

