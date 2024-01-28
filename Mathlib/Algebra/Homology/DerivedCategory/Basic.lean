import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.Algebra.Homology.HomotopyCategory.Cylinder
import Mathlib.Algebra.Homology.Localization
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Localization.Composition
import Mathlib.CategoryTheory.Localization.HasLocalization

open CategoryTheory Category Limits Pretriangulated ZeroObject Preadditive

universe w v u

variable (C : Type u) [Category.{v} C] [Abelian C]

namespace HomotopyCategory

def subcategoryAcyclic :
    Triangulated.Subcategory (HomotopyCategory C (ComplexShape.up ℤ)) :=
  Functor.homologicalKernel (homologyFunctor C (ComplexShape.up ℤ) 0)

instance : (subcategoryAcyclic C).set.RespectsIso := by
  dsimp only [subcategoryAcyclic]
  infer_instance

variable {C}

lemma mem_subcategoryAcyclic_iff (X : HomotopyCategory C (ComplexShape.up ℤ)) :
    X ∈ (subcategoryAcyclic C).set ↔ ∀ (n : ℤ), IsZero ((homologyFunctor _ _ n).obj X) :=
  Functor.mem_homologicalKernel_iff _ X

lemma mem_subcategoryAcyclic_iff_exactAt (K : CochainComplex C ℤ) :
    (quotient _ _).obj K ∈ (subcategoryAcyclic C).set ↔ ∀ (n : ℤ), K.ExactAt n := by
  rw [mem_subcategoryAcyclic_iff]
  refine forall_congr' (fun n => ?_)
  simp only [HomologicalComplex.exactAt_iff_isZero_homology]
  exact ((homologyFunctorFactors C (ComplexShape.up ℤ) n).app K).isZero_iff

variable (C)

lemma qis_eq_subcategoryAcyclic_W :
    qis C (ComplexShape.up ℤ) = (subcategoryAcyclic C).W := by
  ext K L f
  erw [← Functor.IsHomological.W_eq_homologicalKernelW]
  rw [Functor.IsHomological.mem_W_iff]
  rfl

/-def qis : MorphismProperty (HomotopyCategory C (ComplexShape.up ℤ)) := (subcategoryAcyclic C).W

instance : (qis C).IsMultiplicative := by
  dsimp [qis]
  infer_instance


lemma mem_qis_iff' {X Y : CochainComplex C ℤ} (f : X ⟶ Y) :
    qis C ((quotient _ _).map f) ↔
    ∀ (n : ℤ), IsIso ((HomologicalComplex.homologyFunctor _ _ n).map f) := by
  simp only [mem_qis_iff,
    ← fun n => NatIso.isIso_map_iff (homologyFunctorFactors C (ComplexShape.up ℤ) n) f]
  rfl-/

end HomotopyCategory

abbrev HasDerivedCategory := MorphismProperty.HasLocalization.{w}
  (HomologicalComplex.qis C (ComplexShape.up ℤ))

variable [HasDerivedCategory.{w} C]

def DerivedCategory := HomologicalComplexUpToQis C (ComplexShape.up ℤ)

namespace DerivedCategory

instance : Category (DerivedCategory C) := by
  dsimp only [DerivedCategory]
  infer_instance

variable {C}

def Q : CochainComplex C ℤ ⥤ DerivedCategory C := HomologicalComplexUpToQis.Q

instance : (Q : _ ⥤ DerivedCategory C).IsLocalization
    (HomologicalComplex.qis C (ComplexShape.up ℤ)) := by
  dsimp only [Q, DerivedCategory]
  infer_instance

def Qh : HomotopyCategory C (ComplexShape.up ℤ) ⥤ DerivedCategory C :=
    HomologicalComplexUpToQis.Qh

variable (C)

def quotientCompQhIso : HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙ Qh ≅ Q :=
    HomologicalComplexUpToQis.quotientCompQhIso C (ComplexShape.up ℤ)

instance : Qh.IsLocalization (HomotopyCategory.qis C (ComplexShape.up ℤ)) := by
  dsimp [Qh, DerivedCategory]
  infer_instance

instance : Qh.IsLocalization (HomotopyCategory.subcategoryAcyclic C).W := by
  rw [← HomotopyCategory.qis_eq_subcategoryAcyclic_W]
  infer_instance

end DerivedCategory

namespace DerivedCategory

instance : HasFiniteProducts (DerivedCategory C) :=
  Localization.hasFiniteProducts Qh (HomotopyCategory.subcategoryAcyclic C).W

noncomputable instance : PreservesFiniteProducts (Qh : _ ⥤ DerivedCategory C) :=
  Localization.preservesFiniteProducts Qh (HomotopyCategory.subcategoryAcyclic C).W

noncomputable instance : Preadditive (DerivedCategory C) :=
  Localization.preadditive Qh (HomotopyCategory.subcategoryAcyclic C).W

instance : (Qh : _ ⥤ DerivedCategory C).Additive :=
  Functor.additive_of_preserves_finite_products _

instance : (Q : _ ⥤ DerivedCategory C).Additive :=
  Functor.additive_of_iso (quotientCompQhIso C)

noncomputable instance : HasZeroObject (DerivedCategory C) :=
  hasZeroObject_of_additive_functor Qh

noncomputable instance : HasShift (DerivedCategory C) ℤ :=
  HasShift.localized Qh (HomotopyCategory.subcategoryAcyclic C).W ℤ

noncomputable instance : (Qh : _ ⥤ DerivedCategory C).CommShift ℤ :=
  Functor.CommShift.localized Qh (HomotopyCategory.subcategoryAcyclic C).W ℤ

noncomputable instance (n : ℤ) :
  Localization.Lifting Qh (HomotopyCategory.subcategoryAcyclic C).W
    (shiftFunctor (HomotopyCategory C (ComplexShape.up ℤ)) n ⋙ Qh)
    (shiftFunctor (DerivedCategory C) n) := ⟨(Qh.commShiftIso n).symm⟩

instance (n : ℤ) : (shiftFunctor (DerivedCategory C) n).Additive := by
  rw [← Localization.functor_additive_iff
    Qh (HomotopyCategory.subcategoryAcyclic C).W
    (shiftFunctor (HomotopyCategory C (ComplexShape.up ℤ)) n ⋙ Qh)
    (shiftFunctor (DerivedCategory C) n)]
  infer_instance

noncomputable instance : Pretriangulated (DerivedCategory C) :=
  Triangulated.Localization.pretriangulated
    Qh (HomotopyCategory.subcategoryAcyclic C).W

instance : (Qh : _ ⥤ DerivedCategory C).IsTriangulated :=
  Triangulated.Localization.isTriangulated_functor
    Qh (HomotopyCategory.subcategoryAcyclic C).W

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

noncomputable instance : IsTriangulated (DerivedCategory C) :=
  Triangulated.Localization.isTriangulated
    Qh (HomotopyCategory.subcategoryAcyclic C).W

variable {C}

instance : (HomotopyCategory.qis C (ComplexShape.up ℤ)).HasLeftCalculusOfFractions := by
  rw [HomotopyCategory.qis_eq_subcategoryAcyclic_W]
  infer_instance

instance : (HomotopyCategory.qis C (ComplexShape.up ℤ)).HasRightCalculusOfFractions := by
  rw [HomotopyCategory.qis_eq_subcategoryAcyclic_W]
  infer_instance

instance : EssSurj (Qh : _ ⥤ DerivedCategory C) :=
  Localization.essSurj _ (HomotopyCategory.qis _ _)

instance : EssSurj (Q : _ ⥤ DerivedCategory C) :=
  Localization.essSurj _ (HomologicalComplex.qis _ _)

noncomputable instance : (Q : CochainComplex C ℤ ⥤ _).CommShift ℤ :=
  Functor.CommShift.ofIso (quotientCompQhIso C) ℤ

instance : NatTrans.CommShift (quotientCompQhIso C).hom ℤ :=
  Functor.CommShift.ofIso_compatibility (quotientCompQhIso C) ℤ

/-@[reassoc]
lemma Q_commShiftIso_hom_app (X : CochainComplex C ℤ) (n : ℤ) :
    (Q.commShiftIso n).hom.app X =
      Qh.map (((HomotopyCategory.quotient C _).commShiftIso n).hom.app X) ≫
        (Qh.commShiftIso n).hom.app ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj X) :=
  by apply Functor.commShiftIso_comp_hom_app

@[reassoc]
lemma Q_commShiftIso_inv_app (X : CochainComplex C ℤ) (n : ℤ) :
    (Q.commShiftIso n).inv.app X =
      (Qh.commShiftIso n).inv.app ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj X) ≫
      Qh.map (((HomotopyCategory.quotient C _).commShiftIso n).inv.app X) :=
  by apply Functor.commShiftIso_comp_inv_app

@[reassoc]
lemma Qh_commShiftIso_hom_app (X : CochainComplex C ℤ) (n : ℤ) :
    Qh.map (((HomotopyCategory.quotient C _).commShiftIso n).hom.app X) =
      (Q.commShiftIso n).hom.app X ≫
        (Qh.commShiftIso n).inv.app ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj X) := by
  simp only [Q_commShiftIso_hom_app, Functor.comp_obj, assoc, Iso.hom_inv_id_app, comp_id]

@[reassoc]
lemma Qh_commShiftIso_inv_app (X : CochainComplex C ℤ) (n : ℤ) :
    (Qh.commShiftIso n).inv.app ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj X) =
      (Q.commShiftIso n).inv.app X ≫
      Qh.map (((HomotopyCategory.quotient C _).commShiftIso n).hom.app X) := by
  simp only [Q_commShiftIso_inv_app, assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    Functor.comp_obj, Paths.of_obj, CategoryTheory.Functor.map_id, comp_id]-/

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
      (e ≪≫ (Functor.mapTriangleIso (quotientCompQhIso C)).symm.app _ ≪≫ (Functor.mapTriangleCompIso (HomotopyCategory.quotient C _) Qh).app _)
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
  HomologicalComplexUpToQis.homologyFunctor C (ComplexShape.up ℤ) n

noncomputable def homologyFunctorFactors (n : ℤ) : Q ⋙ homologyFunctor C n ≅
    HomologicalComplex.homologyFunctor _ _ n :=
  HomologicalComplexUpToQis.homologyFunctorFactors C (ComplexShape.up ℤ) n

noncomputable def homologyFunctorFactorsh (n : ℤ) : Qh ⋙ homologyFunctor C n ≅
    HomotopyCategory.homologyFunctor _ _ n :=
  HomologicalComplexUpToQis.homologyFunctorFactorsh C (ComplexShape.up ℤ) n


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
          Full (Localization.whiskeringLeftFunctor' Qh (HomotopyCategory.qis _ _) C))⟩,
        (inferInstance :
          Faithful (Localization.whiskeringLeftFunctor' Qh (HomotopyCategory.qis _ _) C))⟩

variable {C}

lemma isIso_Qh_map_iff {X Y : HomotopyCategory C (ComplexShape.up ℤ)} (f : X ⟶ Y) :
    IsIso (Qh.map f) ↔ HomotopyCategory.qis C _ f := by
  constructor
  · intro hf
    rw [HomotopyCategory.mem_qis_iff]
    intro n
    rw [← NatIso.isIso_map_iff (homologyFunctorFactorsh C n) f]
    dsimp
    infer_instance
  · intro hf
    exact Localization.inverts Qh (HomotopyCategory.qis _ _) _ hf

lemma isIso_Q_map_iff_quasiIso {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    IsIso (Q.map φ) ↔ QuasiIso φ := by
  apply HomologicalComplexUpToQis.isIso_Q_map_iff_mem_qis

lemma isIso_Q_map_iff {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    IsIso (Q.map φ) ↔
      ∀ (n : ℤ), IsIso ((HomologicalComplex.homologyFunctor C _ n).map φ) := by
  simp only [isIso_Q_map_iff_quasiIso, quasiIso_iff,
    quasiIsoAt_iff_isIso_homologyMap]
  rfl

lemma isIso_Q_map_iff' {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    IsIso (Q.map φ) ↔ HomologicalComplex.qis _ _ φ := by
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
    rw [isIso_Qh_map_iff, HomotopyCategory.mem_qis_iff]
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
  (homologyFunctor C 0).comp_homology_sequence_δ _ hT _ _ h

lemma δ_comp : δ T n₀ n₁ h ≫ (homologyFunctor C n₁).map T.mor₁ = 0 :=
  (homologyFunctor C 0).homology_sequence_δ_comp _ hT _ _ h

lemma exact₂ :
  (ShortComplex.mk ((homologyFunctor C n₀).map T.mor₁) ((homologyFunctor C n₀).map T.mor₂)
    (by simp only [← Functor.map_comp, comp_distTriang_mor_zero₁₂ _ hT,
      Functor.map_zero])).Exact :=
  (homologyFunctor C 0).homology_sequence_exact₂ _ hT _

lemma exact₃ :
  (ShortComplex.mk _ _ (comp_δ T hT n₀ n₁ h)).Exact :=
  (homologyFunctor C 0).homology_sequence_exact₃ _ hT _ _ h

lemma exact₁ :
  (ShortComplex.mk _ _ (δ_comp T hT n₀ n₁ h)).Exact :=
  (homologyFunctor C 0).homology_sequence_exact₁ _ hT _ _ h

lemma epi_homologyMap_mor₁_iff :
    Epi ((homologyFunctor C n₀).map T.mor₁) ↔ (homologyFunctor C n₀).map T.mor₂ = 0 :=
  (homologyFunctor C 0).homology_sequence_epi_shift_map_mor₁_iff _ hT _

lemma mono_homologyMap_mor₁_iff :
    Mono ((homologyFunctor C n₁).map T.mor₁) ↔ δ T n₀ n₁ h  = 0 :=
  (homologyFunctor C 0).homology_sequence_mono_shift_map_mor₁_iff _ hT _ _ h

lemma isIso_homologyMap_mor₁_iff :
    IsIso ((homologyFunctor C n₁).map T.mor₁) ↔
      δ T n₀ n₁ h  = 0 ∧ (homologyFunctor C n₁).map T.mor₂ = 0 :=
  (homologyFunctor C 0).homology_sequence_isIso_shift_map_mor₁_iff _ hT _ _ h

end HomologySequence

end

lemma right_fac (X Y : CochainComplex C ℤ) (f : Q.obj X ⟶ Q.obj Y) :
    ∃ (X' : CochainComplex C ℤ) (s : X' ⟶ X) (hs : IsIso (Q.map s)) (g : X' ⟶ Y),
      f = inv (Q.map s) ≫ Q.map g := by
  have ⟨φ, hφ⟩ := Localization.exists_rightFraction Qh (HomotopyCategory.qis C _) f
  obtain ⟨X', s, hs, g, rfl⟩ := φ.cases
  obtain ⟨X', rfl⟩ := HomotopyCategory.quotient_obj_surjective X'
  obtain ⟨s, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective s
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g
  rw [← isIso_Qh_map_iff] at hs
  exact ⟨X', s, hs, g, hφ⟩

lemma left_fac (X Y : CochainComplex C ℤ) (f : Q.obj X ⟶ Q.obj Y) :
    ∃ (Y' : CochainComplex C ℤ) (g : X ⟶ Y') (s : Y ⟶ Y') (hs : IsIso (Q.map s)),
      f = Q.map g ≫ inv (Q.map s) := by
  have ⟨φ, hφ⟩ := Localization.exists_leftFraction Qh (HomotopyCategory.qis C _) f
  obtain ⟨X', g, s, hs, rfl⟩ := φ.cases
  obtain ⟨X', rfl⟩ := HomotopyCategory.quotient_obj_surjective X'
  obtain ⟨s, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective s
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g
  rw [← isIso_Qh_map_iff] at hs
  exact ⟨X', g, s, hs, hφ⟩

end DerivedCategory
