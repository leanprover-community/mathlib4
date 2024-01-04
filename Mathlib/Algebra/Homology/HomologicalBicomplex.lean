/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Joël Riou
-/
import Mathlib.Algebra.Homology.HomologicalComplex

#align_import algebra.homology.flip from "leanprover-community/mathlib"@"ff511590476ef357b6132a45816adc120d5d7b1d"

/-!
# Bicomplexes

Given a category `C` with zero morphisms and two complex shapes
`c₁ : ComplexShape I₁` and `c₂ : ComplexShape I₂`, we define
the type of bicomplexes `HomologicalComplex₂ C c₁ c₂` as an
abbreviation for `HomologicalComplex (HomologicalComplex C c₂) c₁`.
In particular, if `K : HomologicalComplex₂ C c₁ c₂`, then
for each `i₁ : I₁`, `K.X i₁` is a column of `K`.

In this file, we obtain the equivalence of categories
`HomologicalComplex₂.flipEquivalence : HomologicalComplex₂ C c₁ c₂ ≌ HomologicalComplex₂ C c₂ c₁`
which is obtained by exchanging the horizontal and vertical directions.

-/


open CategoryTheory Limits

variable (C : Type*) [Category C] [HasZeroMorphisms C]
  {I₁ I₂ : Type*} (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂)

/-- Given a category `C` and two complex shapes `c₁` and `c₂` on types `I₁` and `I₂`,
the associated type of bicomplexes `HomologicalComplex₂ C c₁ c₂` is
`K : HomologicalComplex (HomologicalComplex C c₂) c₁`. Then, the object in
position `⟨i₁, i₂⟩` can be obtained as `(K.X i₁).X i₂`. -/
abbrev HomologicalComplex₂ :=
  HomologicalComplex (HomologicalComplex C c₂) c₁

namespace HomologicalComplex₂

open HomologicalComplex

variable {C c₁ c₂}

/-- The graded object indexed by `I₁ × I₂` induced by a bicomplex. -/
def toGradedObject (K : HomologicalComplex₂ C c₁ c₂) :
    GradedObject (I₁ × I₂) C :=
  fun ⟨i₁, i₂⟩ => (K.X i₁).X i₂

lemma shape_f (K : HomologicalComplex₂ C c₁ c₂) (i₁ i₁' : I₁) (h : ¬ c₁.Rel i₁ i₁') (i₂ : I₂) :
    (K.d i₁ i₁').f i₂ = 0 := by
  rw [K.shape _ _ h, zero_f]

@[reassoc (attr := simp)]
lemma d_f_comp_d_f (K : HomologicalComplex₂ C c₁ c₂)
    (i₁ i₁' i₁'' : I₁) (i₂ : I₂) :
    (K.d i₁ i₁').f i₂ ≫ (K.d i₁' i₁'').f i₂ = 0 := by
  rw [← comp_f, d_comp_d, zero_f]

@[reassoc]
lemma d_comm (K : HomologicalComplex₂ C c₁ c₂) (i₁ i₁' : I₁) (i₂ i₂' : I₂) :
    (K.d i₁ i₁').f i₂ ≫ (K.X i₁').d i₂ i₂' = (K.X i₁).d i₂ i₂' ≫ (K.d i₁ i₁').f i₂' := by
  simp

@[reassoc (attr := simp)]
lemma comm_f {K L : HomologicalComplex₂ C c₁ c₂} (f : K ⟶ L) (i₁ i₁' : I₁) (i₂ : I₂) :
    (f.f i₁).f i₂ ≫ (L.d i₁ i₁').f i₂ = (K.d i₁ i₁').f i₂ ≫ (f.f i₁').f i₂ :=
  congr_hom (f.comm i₁ i₁') i₂

/-- Flip a complex of complexes over the diagonal,
exchanging the horizontal and vertical directions.
-/
@[simps]
def flip (K : HomologicalComplex₂ C c₁ c₂) : HomologicalComplex₂ C c₂ c₁ where
  X i :=
    { X := fun j => (K.X j).X i
      d := fun j j' => (K.d j j').f i
      shape := fun j j' w => K.shape_f _ _ w i }
  d i i' := { f := fun j => (K.X j).d i i' }
  shape i i' w := by
    ext j
    exact (K.X j).shape i i' w
#align homological_complex.flip_obj HomologicalComplex₂.flip

variable (C c₁ c₂)

/-- Flipping a complex of complexes over the diagonal, as a functor. -/
@[simps]
def flipFunctor :
    HomologicalComplex₂ C c₁ c₂ ⥤ HomologicalComplex₂ C c₂ c₁ where
  obj K := K.flip
  map {K L} f :=
    { f := fun i =>
        { f := fun j => (f.f j).f i
          comm' := by intros; simp }
      comm' := by intros; ext; simp }
#align homological_complex.flip HomologicalComplex₂.flipFunctor

/-- Auxiliary definition for `HomologicalComplex₂.flipEquivalence`. -/
@[simps!]
def flipEquivalenceUnitIso :
    𝟭 (HomologicalComplex₂ C c₁ c₂) ≅ flipFunctor C c₁ c₂ ⋙ flipFunctor C c₂ c₁ :=
  NatIso.ofComponents (fun K => HomologicalComplex.Hom.isoOfComponents (fun i₁ =>
    HomologicalComplex.Hom.isoOfComponents (fun i₂ => Iso.refl _)
    (by aesop_cat)) (by aesop_cat)) (by aesop_cat)
#align homological_complex.flip_equivalence_unit_iso HomologicalComplex₂.flipEquivalenceUnitIso

/-- Auxiliary definition for `HomologicalComplex₂.flipEquivalence`. -/
@[simps!]
def flipEquivalenceCounitIso :
    flipFunctor C c₂ c₁ ⋙ flipFunctor C c₁ c₂ ≅ 𝟭 (HomologicalComplex₂ C c₂ c₁) :=
  NatIso.ofComponents (fun K => HomologicalComplex.Hom.isoOfComponents (fun i₂ =>
    HomologicalComplex.Hom.isoOfComponents (fun i₁ => Iso.refl _)
    (by aesop_cat)) (by aesop_cat)) (by aesop_cat)
#align homological_complex.flip_equivalence_counit_iso HomologicalComplex₂.flipEquivalenceCounitIso

/-- Flipping a complex of complexes over the diagonal, as an equivalence of categories. -/
@[simps]
def flipEquivalence :
    HomologicalComplex₂ C c₁ c₂ ≌ HomologicalComplex₂ C c₂ c₁ where
  functor := flipFunctor C c₁ c₂
  inverse := flipFunctor C c₂ c₁
  unitIso := flipEquivalenceUnitIso C c₁ c₂
  counitIso := flipEquivalenceCounitIso C c₁ c₂
#align homological_complex.flip_equivalence HomologicalComplex₂.flipEquivalence

end HomologicalComplex₂
