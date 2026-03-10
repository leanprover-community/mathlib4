/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated

/-! # The derived category of an abelian category

In this file, we construct the derived category `DerivedCategory C` of an
abelian category `C`. It is equipped with a triangulated structure.

The derived category is defined here as the localization of cochain complexes
indexed by `ℤ` with respect to quasi-isomorphisms: it is a type synonym of
`HomologicalComplexUpToQuasiIso C (ComplexShape.up ℤ)`. Then, we have a
localization functor `DerivedCategory.Q : CochainComplex C ℤ ⥤ DerivedCategory C`.
It was already shown in the file `Mathlib/Algebra/Homology/Localization.lean` that the induced
functor `DerivedCategory.Qh : HomotopyCategory C (ComplexShape.up ℤ) ⥤ DerivedCategory C`
is a localization functor with respect to the class of morphisms
`HomotopyCategory.quasiIso C (ComplexShape.up ℤ)`. In the file
`HomotopyCategory.Acyclic`, it was shown that this class of quasiisomorphisms
consists of morphisms whose cone belongs to the triangulated subcategory
`HomotopyCategory.subcategoryAcyclic C` of acyclic complexes. Then, the triangulated
structure on `DerivedCategory C` is deduced from the triangulated structure
on the homotopy category (see file `Mathlib/Algebra/Homology/HomotopyCategory/Triangulated.lean`)
using the localization theorem for triangulated categories which was obtained
in the file `Mathlib/CategoryTheory/Localization/Triangulated.lean`.

## Implementation notes

If `C : Type u` and `Category.{v} C`, the constructed localized category of cochain
complexes with respect to quasi-isomorphisms has morphisms in `Type (max u v)`.
However, in certain circumstances, it shall be possible to prove that they are `v`-small
(when `C` is a Grothendieck abelian category (e.g. the category of modules over a ring),
it should be so by a theorem of Hovey).

Then, when working with derived categories in mathlib, the user should add the variable
`[HasDerivedCategory.{w} C]` which is the assumption that there is a chosen derived
category with morphisms in `Type w`. When derived categories are used in order to
prove statements which do not involve derived categories, the `HasDerivedCategory.{max u v}`
instance should be obtained at the beginning of the proof, using the term
`HasDerivedCategory.standard C`.

## TODO (@joelriou)

- construct the distinguished triangle associated to a short exact sequence
  of cochain complexes (done), and compare the associated connecting homomorphism
  with the one defined in `Algebra.Homology.HomologySequence`.

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*][verdier1996]
* [Mark Hovey, *Model category structures on chain complexes of sheaves*][hovey-2001]

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

universe w v u

open CategoryTheory Limits Pretriangulated

variable (C : Type u) [Category.{v} C] [Abelian C]

/-- The assumption that a localized category for
`(HomologicalComplex.quasiIso C (ComplexShape.up ℤ))` has been chosen, and that the morphisms
in this chosen category are in `Type w`. -/
abbrev HasDerivedCategory := MorphismProperty.HasLocalization.{w}
  (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))

/-- The derived category obtained using the constructed localized category of cochain complexes
with respect to quasi-isomorphisms. This should be used only while proving statements
which do not involve the derived category. -/
@[instance_reducible]
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

set_option backward.isDefEq.respectTransparency false in
instance : (Q (C := C)).IsLocalization
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) := by
  dsimp only [Q, DerivedCategory]
  infer_instance

instance {K L : CochainComplex C ℤ} (f : K ⟶ L) [QuasiIso f] :
    IsIso (Q.map f) :=
  Localization.inverts Q (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) _
    (inferInstanceAs% (QuasiIso f))

/-- The localization functor `HomotopyCategory C (ComplexShape.up ℤ) ⥤ DerivedCategory C`. -/
def Qh : HomotopyCategory C (ComplexShape.up ℤ) ⥤ DerivedCategory C :=
  HomologicalComplexUpToQuasiIso.Qh

variable (C)

/-- The natural isomorphism `HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙ Qh ≅ Q`. -/
def quotientCompQhIso : HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙ Qh ≅ Q :=
  HomologicalComplexUpToQuasiIso.quotientCompQhIso C (ComplexShape.up ℤ)

set_option backward.isDefEq.respectTransparency false in
instance : Qh.IsLocalization (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) := by
  dsimp [Qh, DerivedCategory]
  infer_instance

instance : Qh.IsLocalization (HomotopyCategory.subcategoryAcyclic C).trW := by
  rw [← HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W]
  infer_instance

noncomputable instance : Preadditive (DerivedCategory C) :=
  Localization.preadditive Qh (HomotopyCategory.subcategoryAcyclic C).trW

instance : (Qh (C := C)).Additive :=
  Localization.functor_additive Qh (HomotopyCategory.subcategoryAcyclic C).trW

instance : (Q (C := C)).Additive :=
  Functor.additive_of_iso (quotientCompQhIso C)

noncomputable instance : HasZeroObject (DerivedCategory C) :=
  Q.hasZeroObject_of_additive

noncomputable instance : HasShift (DerivedCategory C) ℤ :=
  HasShift.localized Qh (HomotopyCategory.subcategoryAcyclic C).trW ℤ

noncomputable instance : (Qh (C := C)).CommShift ℤ :=
  Functor.CommShift.localized Qh (HomotopyCategory.subcategoryAcyclic C).trW ℤ

noncomputable instance : (Q (C := C)).CommShift ℤ :=
  Functor.CommShift.ofIso (quotientCompQhIso C) ℤ

instance : NatTrans.CommShift (quotientCompQhIso C).hom ℤ :=
  Functor.CommShift.ofIso_compatibility (quotientCompQhIso C) ℤ

instance (n : ℤ) : (shiftFunctor (DerivedCategory C) n).Additive := by
  rw [Localization.functor_additive_iff
    Qh (HomotopyCategory.subcategoryAcyclic C).trW]
  exact Functor.additive_of_iso (Qh.commShiftIso n)

noncomputable instance : Pretriangulated (DerivedCategory C) :=
  Triangulated.Localization.pretriangulated
    Qh (HomotopyCategory.subcategoryAcyclic C).trW

instance : (Qh (C := C)).IsTriangulated :=
  Triangulated.Localization.isTriangulated_functor
    Qh (HomotopyCategory.subcategoryAcyclic C).trW

noncomputable instance : IsTriangulated (DerivedCategory C) :=
  Triangulated.Localization.isTriangulated
    Qh (HomotopyCategory.subcategoryAcyclic C).trW

instance : (Qh (C := C)).mapArrow.EssSurj :=
  Localization.essSurj_mapArrow _ (HomotopyCategory.subcategoryAcyclic C).trW

instance {D : Type*} [Category* D] : ((Functor.whiskeringLeft _ _ D).obj (Qh (C := C))).Full :=
  inferInstanceAs
    (Localization.whiskeringLeftFunctor' _ (HomotopyCategory.quasiIso _ _) D).Full

instance {D : Type*} [Category* D] : ((Functor.whiskeringLeft _ _ D).obj (Qh (C := C))).Faithful :=
  inferInstanceAs
    (Localization.whiskeringLeftFunctor' _ (HomotopyCategory.quasiIso _ _) D).Faithful

instance : (Qh : _ ⥤ DerivedCategory C).EssSurj :=
  Localization.essSurj _ (HomotopyCategory.quasiIso _ _)

instance : (Q : _ ⥤ DerivedCategory C).EssSurj :=
  Localization.essSurj _ (HomologicalComplex.quasiIso _ _)

variable {C} in
lemma mem_distTriang_iff (T : Triangle (DerivedCategory C)) :
    (T ∈ distTriang (DerivedCategory C)) ↔ ∃ (X Y : CochainComplex C ℤ) (f : X ⟶ Y),
      Nonempty (T ≅ Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f)) := by
  constructor
  · rintro ⟨T', e, ⟨X, Y, f, ⟨e'⟩⟩⟩
    refine ⟨_, _, f, ⟨?_⟩⟩
    exact e ≪≫ Qh.mapTriangle.mapIso e' ≪≫
      (Functor.mapTriangleCompIso (HomotopyCategory.quotient C _) Qh).symm.app _ ≪≫
      (Functor.mapTriangleIso (quotientCompQhIso C)).app _
  · rintro ⟨X, Y, f, ⟨e⟩⟩
    refine isomorphic_distinguished _ (Qh.map_distinguished _ ?_) _
      (e ≪≫ (Functor.mapTriangleIso (quotientCompQhIso C)).symm.app _ ≪≫
      (Functor.mapTriangleCompIso (HomotopyCategory.quotient C _) Qh).app _)
    exact ⟨_, _, f, ⟨Iso.refl _⟩⟩

/-- The single functors `C ⥤ DerivedCategory C` for all `n : ℤ` along with
their compatibilities with shifts. -/
noncomputable def singleFunctors : SingleFunctors C (DerivedCategory C) ℤ :=
  (HomotopyCategory.singleFunctors C).postcomp Qh

/-- The shift functor `C ⥤ DerivedCategory C` which sends `X : C` to the
single cochain complex with `X` sitting in degree `n : ℤ`. -/
noncomputable abbrev singleFunctor (n : ℤ) := (singleFunctors C).functor n

instance (n : ℤ) : (singleFunctor C n).Additive := by
  dsimp [singleFunctor, singleFunctors]
  infer_instance

-- The object level definitional equality underlying `singleFunctorsPostcompQhIso`.
@[simp] theorem Qh_obj_singleFunctors_obj (n : ℤ) (X : C) :
    Qh.obj (((HomotopyCategory.singleFunctors C).functor n).obj X) = (singleFunctor C n).obj X := by
  rfl

/-- The isomorphism
`DerivedCategory.singleFunctors C ≅ (HomotopyCategory.singleFunctors C).postcomp Qh` given
by the definition of `DerivedCategory.singleFunctors`. -/
noncomputable def singleFunctorsPostcompQhIso :
    singleFunctors C ≅ (HomotopyCategory.singleFunctors C).postcomp Qh :=
  Iso.refl _

/-- The isomorphism
`DerivedCategory.singleFunctors C ≅ (CochainComplex.singleFunctors C).postcomp Q`. -/
noncomputable def singleFunctorsPostcompQIso :
    singleFunctors C ≅ (CochainComplex.singleFunctors C).postcomp Q :=
  (SingleFunctors.postcompFunctor C ℤ (Qh : _ ⥤ DerivedCategory C)).mapIso
    (HomotopyCategory.singleFunctorsPostcompQuotientIso C) ≪≫
      (CochainComplex.singleFunctors C).postcompPostcompIso (HomotopyCategory.quotient _ _) Qh ≪≫
      SingleFunctors.postcompIsoOfIso
        (CochainComplex.singleFunctors C) (quotientCompQhIso C)

lemma singleFunctorsPostcompQIso_hom_hom (n : ℤ) :
    (singleFunctorsPostcompQIso C).hom.hom n = 𝟙 _ := by
  ext X
  dsimp [singleFunctorsPostcompQIso, HomotopyCategory.singleFunctorsPostcompQuotientIso,
    quotientCompQhIso, HomologicalComplexUpToQuasiIso.quotientCompQhIso]
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  erw [Category.id_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma singleFunctorsPostcompQIso_inv_hom (n : ℤ) :
    (singleFunctorsPostcompQIso C).inv.hom n = 𝟙 _ := by
  ext X
  simp [singleFunctorsPostcompQIso, HomotopyCategory.singleFunctorsPostcompQuotientIso]
  rfl

/-- The isomorphism `singleFunctor C n ≅ CochainComplex.singleFunctor C n ⋙ Q`. -/
noncomputable def singleFunctorIsoCompQ (n : ℤ) :
    singleFunctor C n ≅ CochainComplex.singleFunctor C n ⋙ Q := Iso.refl _

lemma isIso_Q_map_iff_quasiIso {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    IsIso (Q.map φ) ↔ QuasiIso φ := by
  apply HomologicalComplexUpToQuasiIso.isIso_Q_map_iff_mem_quasiIso

lemma Q_map_eq_of_homotopy {K L : CochainComplex C ℤ} {f g : K ⟶ L} (h : Homotopy f g) :
    DerivedCategory.Q.map f = DerivedCategory.Q.map g :=
  HomologicalComplexUpToQuasiIso.Q_map_eq_of_homotopy h

end DerivedCategory
