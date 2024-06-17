/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.Algebra.Homology.Localization

/-! # The derived category of an abelian category

In this file, we construct the derived category `DerivedCategory C` of an
abelian category `C`. It is equipped with a triangulated structure.

The derived category is defined here as the localization of cochain complexes
indexed by `ℤ` with respect to quasi-isomorphisms: it is a type synonym of
`HomologicalComplexUpToQuasiIso C (ComplexShape.up ℤ)`. Then, we have a
localization functor `DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C`.
It was already shown in the file `Algebra.Homology.Localization` that the induced
functor `DerivedCategory.Qh : HomotopyCategory C (ComplexShape.up ℤ) ⥤ DerivedCategory C`
is a localization functor with respect to the class of morphisms
`HomotopyCategory.quasiIso C (ComplexShape.up ℤ)`. In the lemma
`HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W` we obtain that this class of morphisms
consists of morphisms whose cone belongs to the triangulated subcategory
`HomotopyCategory.subcategoryAcyclic C` of acyclic complexes. Then, the triangulated
structure on `DerivedCategory C` is deduced from the triangulated structure
on the homotopy category (see file `Algebra.Homology.HomotopyCategory.Triangulated`)
using the localization theorem for triangulated categories which was obtained
in the file `CategoryTheory.Localization.Triangulated`.

## Implementation notes

If `C : Type u` and `Category.{v} C`, the constructed localized category of cochain
complexes with respect to quasi-isomorphisms has morphisms in `Type (max u v)`.
However, in certain circumstances, it shall be possible to prove that they are `v`-small
(when `C` is a Grothendieck abelian category (e.g. the category of modules over a ring),
it should be so by a theorem of Hovey.).

Then, when working with derived categories in mathlib, the user should add the variable
`[HasDerivedCategory.{w} C]` which is the assumption that there is a chosen derived
category with morphisms in `Type w`. When derived categories are used in order to
prove statements which do not involve derived categories, the `HasDerivedCategory.{max u v}`
instance should be obtained at the beginning of the proof, using the term
`HasDerivedCategory.standard C`.

## TODO (@joelriou)

- construct the distinguished triangle associated to a short exact sequence
of cochain complexes, and compare the associated connecting homomorphism
with the one defined in `Algebra.Homology.HomologySequence`.
- refactor the definition of Ext groups using morphisms in the derived category
(which may be shrunk to the universe `v` at least when `C` has enough projectives
or enough injectives).

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*][verdier1996]
* [Mark Hovey, *Model category structures on chain complexes of sheaves*][hovey-2001]

-/

universe w v u

open CategoryTheory Limits

variable (C : Type u) [Category.{v} C] [Abelian C]

namespace HomotopyCategory

/-- The triangulated subcategory of `HomotopyCategory C (ComplexShape.up ℤ)` consisting
of acyclic complexes. -/
def subcategoryAcyclic : Triangulated.Subcategory (HomotopyCategory C (ComplexShape.up ℤ)) :=
  (homologyFunctor C (ComplexShape.up ℤ) 0).homologicalKernel

instance : ClosedUnderIsomorphisms (subcategoryAcyclic C).P := by
  dsimp [subcategoryAcyclic]
  infer_instance

variable {C}

lemma mem_subcategoryAcyclic_iff (X : HomotopyCategory C (ComplexShape.up ℤ)) :
    (subcategoryAcyclic C).P X ↔ ∀ (n : ℤ), IsZero ((homologyFunctor _ _ n).obj X) :=
  Functor.mem_homologicalKernel_iff _ X

lemma quotient_obj_mem_subcategoryAcyclic_iff_exactAt (K : CochainComplex C ℤ) :
    (subcategoryAcyclic C).P ((quotient _ _).obj K) ↔ ∀ (n : ℤ), K.ExactAt n := by
  rw [mem_subcategoryAcyclic_iff]
  refine forall_congr' (fun n => ?_)
  simp only [HomologicalComplex.exactAt_iff_isZero_homology]
  exact ((homologyFunctorFactors C (ComplexShape.up ℤ) n).app K).isZero_iff

variable (C)

lemma quasiIso_eq_subcategoryAcyclic_W :
    quasiIso C (ComplexShape.up ℤ) = (subcategoryAcyclic C).W := by
  ext K L f
  exact ((homologyFunctor C (ComplexShape.up ℤ) 0).mem_homologicalKernel_W_iff f).symm

end HomotopyCategory

/-- The assumption that a localized category for
`(HomologicalComplex.quasiIso C (ComplexShape.up ℤ))` has been chosen, and that the morphisms
in this chosen category are in `Type w`. -/
abbrev HasDerivedCategory := MorphismProperty.HasLocalization.{w}
  (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))

/-- The derived category obtained using the constructed localized category of cochain complexes
with respect to quasi-isomorphisms. This should be used only while proving statements
which do not involve the derived category. -/
def HasDerivedCategory.standard : HasDerivedCategory.{max u v} C :=
  MorphismProperty.HasLocalization.standard _

variable [HasDerivedCategory.{w} C]

/-- The derived category of an abelian category. -/
def DerivedCategory : Type (max u v) := HomologicalComplexUpToQuasiIso C (ComplexShape.up ℤ)

namespace DerivedCategory

instance : Category.{w} (DerivedCategory C) := by
  dsimp [DerivedCategory]
  infer_instance

variable {C}

/-- The localization functor `CochainComplex C ℤ ⥤ DerivedCategory C`. -/
def Q : CochainComplex C ℤ ⥤ DerivedCategory C := HomologicalComplexUpToQuasiIso.Q

instance : (Q (C := C)).IsLocalization
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) := by
  dsimp only [Q, DerivedCategory]
  infer_instance

/-- The localization functor `HomotopyCategory C (ComplexShape.up ℤ) ⥤ DerivedCategory C`. -/
def Qh : HomotopyCategory C (ComplexShape.up ℤ) ⥤ DerivedCategory C :=
  HomologicalComplexUpToQuasiIso.Qh

variable (C)

/-- The natural isomorphism `HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙ Qh ≅ Q`. -/
def quotientCompQhIso : HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙ Qh ≅ Q :=
  HomologicalComplexUpToQuasiIso.quotientCompQhIso C (ComplexShape.up ℤ)

instance : Qh.IsLocalization (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) := by
  dsimp [Qh, DerivedCategory]
  infer_instance

instance : Qh.IsLocalization (HomotopyCategory.subcategoryAcyclic C).W := by
  rw [← HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W]
  infer_instance

noncomputable instance : Preadditive (DerivedCategory C) :=
  Localization.preadditive Qh (HomotopyCategory.subcategoryAcyclic C).W

instance : (Qh (C := C)).Additive :=
  Localization.functor_additive Qh (HomotopyCategory.subcategoryAcyclic C).W

instance : (Q (C := C)).Additive :=
  Functor.additive_of_iso (quotientCompQhIso C)

noncomputable instance : HasZeroObject (DerivedCategory C) :=
  Q.hasZeroObject_of_additive

noncomputable instance : HasShift (DerivedCategory C) ℤ :=
  HasShift.localized Qh (HomotopyCategory.subcategoryAcyclic C).W ℤ

noncomputable instance : (Qh (C := C)).CommShift ℤ :=
  Functor.CommShift.localized Qh (HomotopyCategory.subcategoryAcyclic C).W ℤ

instance (n : ℤ) : (shiftFunctor (DerivedCategory C) n).Additive := by
  rw [Localization.functor_additive_iff
    Qh (HomotopyCategory.subcategoryAcyclic C).W]
  exact Functor.additive_of_iso (Qh.commShiftIso n)

noncomputable instance : Pretriangulated (DerivedCategory C) :=
  Triangulated.Localization.pretriangulated
    Qh (HomotopyCategory.subcategoryAcyclic C).W

instance : (Qh (C := C)).IsTriangulated :=
  Triangulated.Localization.isTriangulated_functor
    Qh (HomotopyCategory.subcategoryAcyclic C).W

noncomputable instance : IsTriangulated (DerivedCategory C) :=
  Triangulated.Localization.isTriangulated
    Qh (HomotopyCategory.subcategoryAcyclic C).W

instance : (Qh (C := C)).mapArrow.EssSurj :=
  Localization.essSurj_mapArrow _ (HomotopyCategory.subcategoryAcyclic C).W

instance {D : Type*} [Category D] : ((whiskeringLeft _ _ D).obj (Qh (C := C))).Full :=
  inferInstanceAs
    (Localization.whiskeringLeftFunctor' _ (HomotopyCategory.quasiIso _ _) D).Full

instance {D : Type*} [Category D] : ((whiskeringLeft _ _ D).obj (Qh (C := C))).Faithful :=
  inferInstanceAs
    (Localization.whiskeringLeftFunctor' _ (HomotopyCategory.quasiIso _ _) D).Faithful

end DerivedCategory
