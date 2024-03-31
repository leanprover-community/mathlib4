/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.Algebra.Homology.Localization

/-! # The derived category of an abelian category

In this file, we construct the derived category `DerivedCategory C` of an
abelian category `C`. If is equipped with a triangulated structure.

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

- define the induced homological functor `DerivedCategory C ⥤ C`.
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

open CategoryTheory Category Limits Pretriangulated ZeroObject

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
def DerivedCategory := HomologicalComplexUpToQuasiIso C (ComplexShape.up ℤ)

namespace DerivedCategory

instance : Category (DerivedCategory C) := by
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

variable (C) in
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

instance shiftFunctor_additive (n : ℤ) : (shiftFunctor (DerivedCategory C) n).Additive := by
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

noncomputable instance (n : ℤ) :
  Localization.Lifting Qh (HomotopyCategory.subcategoryAcyclic C).W
    (shiftFunctor (HomotopyCategory C (ComplexShape.up ℤ)) n ⋙ Qh)
    (shiftFunctor (DerivedCategory C) n) := ⟨(Qh.commShiftIso n).symm⟩

instance : EssSurj (Qh : _ ⥤ DerivedCategory C).mapArrow :=
  Triangulated.Localization.essSurj_mapArrow
    Qh (HomotopyCategory.subcategoryAcyclic C).W

instance : EssSurj (Q : _ ⥤ DerivedCategory C).mapArrow where
  mem_essImage φ := by
    obtain ⟨⟨K⟩, ⟨L⟩, f, ⟨e⟩⟩ :
        ∃ (K L : HomotopyCategory C (ComplexShape.up ℤ)) (f : K ⟶ L),
          Nonempty (Arrow.mk (Qh.map f) ≅ φ) := ⟨_, _, _, ⟨Qh.mapArrow.objObjPreimageIso φ⟩⟩
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_surjective f
    exact ⟨Arrow.mk f, ⟨e⟩⟩

instance : (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).HasLeftCalculusOfFractions := by
  rw [HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W]
  infer_instance

instance : (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).HasRightCalculusOfFractions := by
  rw [HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W]
  infer_instance

instance : EssSurj (Qh : _ ⥤ DerivedCategory C) :=
  Localization.essSurj _ (HomotopyCategory.quasiIso _ _)

instance : EssSurj (Q : _ ⥤ DerivedCategory C) :=
  Localization.essSurj _ (HomologicalComplex.quasiIso _ _)

noncomputable instance : (Q : CochainComplex C ℤ ⥤ _).CommShift ℤ :=
  Functor.CommShift.ofIso (quotientCompQhIso C) ℤ

instance : NatTrans.CommShift (quotientCompQhIso C).hom ℤ :=
  Functor.CommShift.ofIso_compatibility (quotientCompQhIso C) ℤ

lemma mem_distTriang_iff (T : Triangle (DerivedCategory C)) :
    (T ∈ distTriang (DerivedCategory C)) ↔ ∃ (X Y : CochainComplex C ℤ) (f : X ⟶ Y),
      Nonempty (T ≅ Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f)) := by
  constructor
  · rintro ⟨T', e, ⟨X, Y, f, ⟨e'⟩⟩⟩
    refine' ⟨_, _, f, ⟨_⟩⟩
    exact e ≪≫ Qh.mapTriangle.mapIso e' ≪≫
      (Functor.mapTriangleCompIso (HomotopyCategory.quotient C _) Qh).symm.app _ ≪≫
      (Functor.mapTriangleIso (quotientCompQhIso C)).app _
  · rintro ⟨X, Y, f, ⟨e⟩⟩
    refine' isomorphic_distinguished _ (Qh.map_distinguished _ _) _
      (e ≪≫ (Functor.mapTriangleIso (quotientCompQhIso C)).symm.app _ ≪≫
      (Functor.mapTriangleCompIso (HomotopyCategory.quotient C _) Qh).app _)
    exact ⟨_, _, f, ⟨Iso.refl _⟩⟩

lemma induction_Q_obj (P : DerivedCategory C → Prop)
    (hP₁ : ∀ (X : CochainComplex C ℤ), P (Q.obj X))
    (hP₂ : ∀ ⦃X Y : DerivedCategory C⦄ (_ : X ≅ Y), P X → P Y)
    (X : DerivedCategory C) : P X :=
  hP₂ (Q.objObjPreimageIso X) (hP₁ _)

variable (C)

noncomputable def singleFunctors : SingleFunctors C (DerivedCategory C) ℤ :=
  (HomotopyCategory.singleFunctors C).postComp Qh

noncomputable abbrev singleFunctor (n : ℤ) := (singleFunctors C).functor n

instance (n : ℤ) : (singleFunctor C n).Additive := by
  dsimp [singleFunctor, singleFunctors]
  infer_instance

noncomputable def singleFunctorsPostCompQhIso :
    singleFunctors C ≅ (HomotopyCategory.singleFunctors C).postComp Qh :=
  Iso.refl _

noncomputable def singleFunctorsPostCompQIso :
    singleFunctors C ≅ (CochainComplex.singleFunctors C).postComp Q :=
  (SingleFunctors.postCompFunctor C ℤ (Qh : _ ⥤ DerivedCategory C)).mapIso (HomotopyCategory.singleFunctorsPostCompQuotientIso C)
    ≪≫ (CochainComplex.singleFunctors C).postCompPostCompIso (HomotopyCategory.quotient _ _) Qh ≪≫
      SingleFunctors.postCompIsoOfIso
        (CochainComplex.singleFunctors C) (quotientCompQhIso C)

/-noncomputable def singleFunctor (n : ℤ) : C ⥤ DerivedCategory C :=
  HomologicalComplex.single _ _ n ⋙ Q

instance (n : ℤ) : (singleFunctor C n).Additive := by
  dsimp only [singleFunctor]
  infer_instance

noncomputable def singleFunctorShiftIso (n a a' : ℤ) (ha' : n + a = a') :
    singleFunctor C a' ⋙ shiftFunctor _ n ≅ singleFunctor C a :=
  Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (Q.commShiftIso n).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (CochainComplex.singleShiftIso C n a a' ha') Q

variable {C}

lemma singleFunctorShiftIso_hom_app (n a a' : ℤ) (ha' : n + a = a') (X : C) :
    (singleFunctorShiftIso C n a a' ha').hom.app X =
      (Q.commShiftIso n).inv.app ((HomologicalComplex.single C (ComplexShape.up ℤ) a').obj X) ≫
        Q.map ((CochainComplex.singleShiftIso C n a a' ha').hom.app X) := by
  dsimp [singleFunctorShiftIso]
  erw [id_comp, id_comp]

lemma singleFunctorShiftIso_inv_app (n a a' : ℤ) (ha' : n + a = a') (X : C) :
    (singleFunctorShiftIso C n a a' ha').inv.app X =
      Q.map ((CochainComplex.singleShiftIso C n a a' ha').inv.app X) ≫
      (Q.commShiftIso n).hom.app ((HomologicalComplex.single C (ComplexShape.up ℤ) a').obj X) := by
  dsimp [singleFunctorShiftIso]
  erw [comp_id, comp_id]-/


noncomputable def homologyFunctor (n : ℤ) : DerivedCategory C ⥤ C :=
  HomologicalComplexUpToQuasiIso.homologyFunctor C (ComplexShape.up ℤ) n

noncomputable def homologyFunctorFactors (n : ℤ) : Q ⋙ homologyFunctor C n ≅
    HomologicalComplex.homologyFunctor _ _ n :=
  HomologicalComplexUpToQuasiIso.homologyFunctorFactors C (ComplexShape.up ℤ) n

noncomputable def homologyFunctorFactorsh (n : ℤ) : Qh ⋙ homologyFunctor C n ≅
    HomotopyCategory.homologyFunctor _ _ n :=
  HomologicalComplexUpToQuasiIso.homologyFunctorFactorsh C (ComplexShape.up ℤ) n


noncomputable def singleFunctorCompHomologyFunctorIso (n : ℤ) :
    singleFunctor C n ⋙ homologyFunctor C n ≅ 𝟭 C :=
  isoWhiskerRight ((SingleFunctors.evaluation _ _ n).mapIso (singleFunctorsPostCompQIso C)) _ ≪≫ Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (homologyFunctorFactors C n) ≪≫
      HomologicalComplex.homologyFunctorSingleIso _ _ _

instance (n : ℤ) : (homologyFunctor C n).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_fac_of_essSurj _ _ _
    (homologyFunctorFactorsh C n)

-- could be better to have `IsHomological` extend `PreservesZeroMorphisms` so that
-- we do not have to prove both statement separately
instance (n : ℤ) : (homologyFunctor C n).IsHomological :=
  Functor.isHomological_of_localization Qh
    (homologyFunctor C n) _ (homologyFunctorFactorsh C n)

noncomputable instance :
    (homologyFunctor C 0).ShiftSequence ℤ :=
  Functor.ShiftSequence.induced (homologyFunctorFactorsh C 0) ℤ
    (homologyFunctor C) (homologyFunctorFactorsh C)
      ⟨⟨(inferInstance :
          Full (Localization.whiskeringLeftFunctor' Qh (HomotopyCategory.quasiIso _ _) C))⟩,
        (inferInstance :
          Faithful (Localization.whiskeringLeftFunctor' Qh (HomotopyCategory.quasiIso _ _) C))⟩

variable {C}

lemma isIso_Qh_map_iff {X Y : HomotopyCategory C (ComplexShape.up ℤ)} (f : X ⟶ Y) :
    IsIso (Qh.map f) ↔ HomotopyCategory.quasiIso C _ f := by
  constructor
  · intro hf
    rw [HomotopyCategory.mem_quasiIso_iff]
    intro n
    rw [← NatIso.isIso_map_iff (homologyFunctorFactorsh C n) f]
    dsimp
    infer_instance
  · intro hf
    exact Localization.inverts Qh (HomotopyCategory.quasiIso _ _) _ hf

lemma isIso_Q_map_iff_quasiIso {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    IsIso (Q.map φ) ↔ QuasiIso φ := by
  apply HomologicalComplexUpToQuasiIso.isIso_Q_map_iff_mem_quasiIso

lemma isIso_Q_map_iff {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    IsIso (Q.map φ) ↔
      ∀ (n : ℤ), IsIso ((HomologicalComplex.homologyFunctor C _ n).map φ) := by
  simp only [isIso_Q_map_iff_quasiIso, quasiIso_iff,
    quasiIsoAt_iff_isIso_homologyMap]
  rfl

lemma isIso_Q_map_iff' {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    IsIso (Q.map φ) ↔ HomologicalComplex.quasiIso _ _ φ := by
  rw [isIso_Q_map_iff_quasiIso]
  rfl

instance {K L : CochainComplex C ℤ} (φ : K ⟶ L) [QuasiIso φ] : IsIso (Q.map φ) := by
  simpa only [isIso_Q_map_iff_quasiIso]

lemma isIso_iff {K L : DerivedCategory C} (f : K ⟶ L) :
    IsIso f ↔ ∀ (n : ℤ), IsIso ((homologyFunctor C n).map f) := by
  constructor
  · intro hf n
    infer_instance
  · intro hf
    let g := (Functor.mapArrow Qh).objPreimage (Arrow.mk f)
    refine' ((MorphismProperty.RespectsIso.isomorphisms (DerivedCategory C)).arrow_iso_iff
      ((Functor.mapArrow Qh).objObjPreimageIso (Arrow.mk f))).1 _
    change IsIso (Qh.map g.hom)
    rw [isIso_Qh_map_iff, HomotopyCategory.mem_quasiIso_iff]
    intro n
    have e : Arrow.mk ((homologyFunctor C n).map f) ≅
        Arrow.mk ((HomotopyCategory.homologyFunctor _ _ n).map g.hom) :=
      ((homologyFunctor C n).mapArrow.mapIso
        (((Functor.mapArrow Qh).objObjPreimageIso (Arrow.mk f)).symm)) ≪≫
        ((Functor.mapArrowFunctor _ _).mapIso (homologyFunctorFactorsh C n)).app (Arrow.mk g.hom)
    exact ((MorphismProperty.RespectsIso.isomorphisms C).arrow_iso_iff e).1 (hf n)

lemma isZero_iff (K : DerivedCategory C) :
    IsZero K ↔ ∀ (n : ℤ), IsZero ((homologyFunctor C n).obj K) := by
  constructor
  · intro hK n
    rw [IsZero.iff_id_eq_zero, ← ((homologyFunctor C n).map_id K),
      (IsZero.iff_id_eq_zero K).1 hK, Functor.map_zero]
  · intro hK
    have : IsIso (0 : K ⟶ 0) := by
      rw [isIso_iff]
      intro n
      refine' ⟨0, _, _⟩
      · apply (hK n).eq_of_src
      · rw [zero_comp, ← (homologyFunctor C n).map_id, id_zero,
          Functor.map_zero]
    exact IsZero.of_iso (isZero_zero _) (asIso (0 : K ⟶ 0))

section

variable {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact)

lemma isIso_Q_map_fromOfShortComplex :
    IsIso (Q.map (CochainComplex.mappingCone.fromOfShortComplex S)) := by
  rw [isIso_Q_map_iff]
  exact CochainComplex.mappingCone.isIso_homologyMap_fromOfShortComplex hS

noncomputable def triangleOfSESδ :
  Q.obj (S.X₃) ⟶ (Q.obj S.X₁)⟦(1 : ℤ)⟧ :=
    have := isIso_Q_map_fromOfShortComplex hS
    inv (Q.map (CochainComplex.mappingCone.fromOfShortComplex S)) ≫
      Q.map (CochainComplex.mappingCone.triangle S.f).mor₃ ≫
      (Q.commShiftIso (1 : ℤ)).hom.app S.X₁

noncomputable def triangleOfSES : Triangle (DerivedCategory C) :=
  Triangle.mk (Q.map S.f) (Q.map S.g) (triangleOfSESδ hS)

noncomputable def triangleOfSESIso :
    Q.mapTriangle.obj (CochainComplex.mappingCone.triangle S.f) ≅ triangleOfSES hS := by
  have := isIso_Q_map_fromOfShortComplex hS
  refine' Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    (asIso (Q.map (CochainComplex.mappingCone.fromOfShortComplex S))) _ _ _
  · dsimp [triangleOfSES]
    simp only [comp_id, id_comp]
  · dsimp [triangleOfSES, CochainComplex.mappingCone.fromOfShortComplex, asIso]
    rw [id_comp, ← Q.map_comp, CochainComplex.mappingCone.inr_desc]
  · dsimp [triangleOfSES, triangleOfSESδ]
    rw [CategoryTheory.Functor.map_id, comp_id, IsIso.hom_inv_id_assoc]

lemma triangleOfSES_distinguished :
    triangleOfSES hS ∈ distTriang (DerivedCategory C) := by
  rw [mem_distTriang_iff]
  exact ⟨_, _, S.f, ⟨(triangleOfSESIso hS).symm⟩⟩

namespace HomologySequence

variable (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _)
  (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁)

noncomputable def δ : (homologyFunctor C n₀).obj T.obj₃ ⟶ (homologyFunctor C n₁).obj T.obj₁ :=
  (homologyFunctor C 0).shiftMap T.mor₃ n₀ n₁ (by rw [add_comm 1, h])

lemma comp_δ : (homologyFunctor C n₀).map T.mor₂ ≫ δ T n₀ n₁ h = 0 :=
  (homologyFunctor C 0).comp_homologySequenceδ _ hT _ _ h

lemma δ_comp : δ T n₀ n₁ h ≫ (homologyFunctor C n₁).map T.mor₁ = 0 :=
  (homologyFunctor C 0).homologySequenceδ_comp _ hT _ _ h

lemma exact₂ :
  (ShortComplex.mk ((homologyFunctor C n₀).map T.mor₁) ((homologyFunctor C n₀).map T.mor₂)
    (by simp only [← Functor.map_comp, comp_distTriang_mor_zero₁₂ _ hT,
      Functor.map_zero])).Exact :=
  (homologyFunctor C 0).homologySequence_exact₂ _ hT _

lemma exact₃ :
  (ShortComplex.mk _ _ (comp_δ T hT n₀ n₁ h)).Exact :=
  (homologyFunctor C 0).homologySequence_exact₃ _ hT _ _ h

lemma exact₁ :
  (ShortComplex.mk _ _ (δ_comp T hT n₀ n₁ h)).Exact :=
  (homologyFunctor C 0).homologySequence_exact₁ _ hT _ _ h

lemma epi_homologyMap_mor₁_iff :
    Epi ((homologyFunctor C n₀).map T.mor₁) ↔ (homologyFunctor C n₀).map T.mor₂ = 0 :=
  (homologyFunctor C 0).homologySequence_epi_shift_map_mor₁_iff _ hT _

lemma mono_homologyMap_mor₁_iff :
    Mono ((homologyFunctor C n₁).map T.mor₁) ↔ δ T n₀ n₁ h  = 0 :=
  (homologyFunctor C 0).homologySequence_mono_shift_map_mor₁_iff _ hT _ _ h

lemma isIso_homologyMap_mor₁_iff :
    IsIso ((homologyFunctor C n₁).map T.mor₁) ↔
      δ T n₀ n₁ h  = 0 ∧ (homologyFunctor C n₁).map T.mor₂ = 0 :=
  (homologyFunctor C 0).homologySequence_isIso_shift_map_mor₁_iff _ hT _ _ h

lemma isIso_homologyMap_mor₂_iff :
    IsIso ((homologyFunctor C n₀).map T.mor₂) ↔
      δ T n₀ n₁ h  = 0 ∧ (homologyFunctor C n₀).map T.mor₁ = 0 :=
  (homologyFunctor C 0).homologySequence_isIso_shift_map_mor₂_iff _ hT _ _ h

end HomologySequence

end

lemma right_fac (X Y : CochainComplex C ℤ) (f : Q.obj X ⟶ Q.obj Y) :
    ∃ (X' : CochainComplex C ℤ) (s : X' ⟶ X) (hs : IsIso (Q.map s)) (g : X' ⟶ Y),
      f = inv (Q.map s) ≫ Q.map g := by
  have ⟨φ, hφ⟩ := Localization.exists_rightFraction Qh (HomotopyCategory.quasiIso C _) f
  obtain ⟨X', s, hs, g, rfl⟩ := φ.cases
  obtain ⟨X', rfl⟩ := HomotopyCategory.quotient_obj_surjective X'
  obtain ⟨s, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective s
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g
  rw [← isIso_Qh_map_iff] at hs
  exact ⟨X', s, hs, g, hφ⟩

lemma left_fac (X Y : CochainComplex C ℤ) (f : Q.obj X ⟶ Q.obj Y) :
    ∃ (Y' : CochainComplex C ℤ) (g : X ⟶ Y') (s : Y ⟶ Y') (hs : IsIso (Q.map s)),
      f = Q.map g ≫ inv (Q.map s) := by
  have ⟨φ, hφ⟩ := Localization.exists_leftFraction Qh (HomotopyCategory.quasiIso C _) f
  obtain ⟨X', g, s, hs, rfl⟩ := φ.cases
  obtain ⟨X', rfl⟩ := HomotopyCategory.quotient_obj_surjective X'
  obtain ⟨s, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective s
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g
  rw [← isIso_Qh_map_iff] at hs
  exact ⟨X', g, s, hs, hφ⟩

end DerivedCategory
