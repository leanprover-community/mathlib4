import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.Algebra.Homology.HomotopyCategory.Cylinder
import Mathlib.CategoryTheory.Localization.Composition
import Mathlib.CategoryTheory.Localization.HasLocalization

open CategoryTheory Category Limits Pretriangulated ZeroObject Preadditive

universe w v u

variable (C : Type u) [Category.{v} C] [Abelian C]

namespace HomotopyCategory

def subcategoryAcyclic :
    Triangulated.Subcategory (HomotopyCategory C (ComplexShape.up ℤ)) :=
  Functor.homologicalKernel (newHomologyFunctor C (ComplexShape.up ℤ) 0)

lemma mem_subCategoryAcyclic_iff (X : HomotopyCategory C (ComplexShape.up ℤ)) :
    X ∈ (subcategoryAcyclic C).set ↔ ∀ (n : ℤ), IsZero ((newHomologyFunctor _ _ n).obj X) :=
  Functor.mem_homologicalKernel_iff _ X

def qis : MorphismProperty (HomotopyCategory C (ComplexShape.up ℤ)) := (subcategoryAcyclic C).W

lemma mem_qis_iff {X Y : HomotopyCategory C (ComplexShape.up ℤ)} (f : X ⟶ Y) :
    qis _ f ↔ ∀ (n : ℤ), IsIso ((newHomologyFunctor _ _ n).map f) := by
  dsimp only [qis, subcategoryAcyclic]
  rw [← Functor.IsHomological.W_eq_homologicalKernelW]
  apply Functor.IsHomological.mem_W_iff

lemma mem_qis_iff' {X Y : CochainComplex C ℤ} (f : X ⟶ Y) :
    qis C ((quotient _ _).map f) ↔
    ∀ (n : ℤ), IsIso ((HomologicalComplex.newHomologyFunctor _ _ n).map f) := by
  simp only [mem_qis_iff,
    ← fun n => NatIso.isIso_map_iff (newHomologyFunctorFactors C (ComplexShape.up ℤ) n) f]
  rfl

end HomotopyCategory

abbrev HasDerivedCategory := MorphismProperty.HasLocalization.{w} (HomotopyCategory.qis C)

variable [HasDerivedCategory.{w} C]

def DerivedCategory := (HomotopyCategory.qis C).Localization'

namespace DerivedCategory

instance : Category (DerivedCategory C) := by
  dsimp only [DerivedCategory]
  infer_instance

noncomputable instance : Preadditive (DerivedCategory C) := by
  dsimp only [DerivedCategory, HomotopyCategory.qis]
  infer_instance

instance : HasZeroObject (DerivedCategory C) := by
  dsimp only [DerivedCategory, HomotopyCategory.qis]
  infer_instance

noncomputable instance : HasShift (DerivedCategory C) ℤ := by
  dsimp only [DerivedCategory, HomotopyCategory.qis]
  infer_instance

instance (n : ℤ) : (shiftFunctor (DerivedCategory C) n).Additive := by
  dsimp only [DerivedCategory, HomotopyCategory.qis]
  infer_instance

noncomputable instance : Pretriangulated (DerivedCategory C) := by
  dsimp only [DerivedCategory, HomotopyCategory.qis]
  infer_instance

noncomputable instance : IsTriangulated (DerivedCategory C) := by
  dsimp only [DerivedCategory, HomotopyCategory.qis]
  infer_instance

variable {C}

def Qh : HomotopyCategory C (ComplexShape.up ℤ) ⥤ DerivedCategory C :=
  MorphismProperty.Q' _

instance : Qh.IsLocalization (HomotopyCategory.qis C) := by
  dsimp only [Qh, DerivedCategory]
  infer_instance

instance : (HomotopyCategory.qis C).HasLeftCalculusOfFractions := by
  dsimp only [HomotopyCategory.qis]
  infer_instance

instance : (HomotopyCategory.qis C).HasRightCalculusOfFractions := by
  dsimp only [HomotopyCategory.qis]
  infer_instance

noncomputable instance : (Qh : _ ⥤ DerivedCategory C).CommShift ℤ := by
  dsimp only [Qh, DerivedCategory]
  infer_instance

instance : (Qh : _ ⥤ DerivedCategory C).IsTriangulated := by
  dsimp only [Qh, DerivedCategory, HomotopyCategory.qis]
  infer_instance

instance : EssSurj (Functor.mapArrow (Qh : _ ⥤ DerivedCategory C)) := by
  dsimp only [Qh, DerivedCategory, HomotopyCategory.qis]
  infer_instance

instance : EssSurj (Qh : _ ⥤ DerivedCategory C) :=
  Localization.essSurj _ (HomotopyCategory.qis _)

def Q : CochainComplex C ℤ ⥤ DerivedCategory C :=
  (HomotopyCategory.quotient _ _ ) ⋙ Qh

instance : EssSurj (Q : _ ⥤ DerivedCategory C) := by
  dsimp only [Q]
  infer_instance

instance : (Q : CochainComplex C ℤ ⥤ _).Additive := by
  dsimp only [Q]
  infer_instance

noncomputable instance : (Q : CochainComplex C ℤ ⥤ _).CommShift ℤ := by
  dsimp only [Q]
  infer_instance

@[reassoc]
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
    Functor.comp_obj, Paths.of_obj, CategoryTheory.Functor.map_id, comp_id]

lemma mem_distTriang_iff (T : Triangle (DerivedCategory C)) :
    (T ∈ distTriang (DerivedCategory C)) ↔ ∃ (X Y : CochainComplex C ℤ) (f : X ⟶ Y),
      Nonempty (T ≅ Q.mapTriangle.obj (CochainComplex.MappingCone.triangle f)) := by
  constructor
  . rintro ⟨T', e, ⟨X, Y, f, ⟨e'⟩⟩⟩
    exact ⟨_, _, f, ⟨e ≪≫ Qh.mapTriangle.mapIso e' ≪≫
      (Functor.mapTriangleCompIso (HomotopyCategory.quotient C _) Qh).symm.app _⟩⟩
  . rintro ⟨X, Y, f, ⟨e⟩⟩
    refine' isomorphic_distinguished _ (Qh.map_distinguished _ _) _
      (e ≪≫ (Functor.mapTriangleCompIso (HomotopyCategory.quotient C _) Qh).app _)
    exact ⟨_, _, f, ⟨Iso.refl _⟩⟩

lemma induction_Q_obj (P : DerivedCategory C → Prop)
    (hP₁ : ∀ (X : CochainComplex C ℤ), P (Q.obj X))
    (hP₂ : ∀ ⦃X Y : DerivedCategory C⦄ (_ : X ≅ Y), P X → P Y)
    (X : DerivedCategory C) : P X :=
  hP₂ (Q.objObjPreimageIso X) (hP₁ _)

variable (C)

-- this should be moved (and generalized)
instance : (HomologicalComplex.single C (ComplexShape.up ℤ) n).Additive where

noncomputable def singleFunctor (n : ℤ) : C ⥤ DerivedCategory C :=
  HomologicalComplex.single _ _ n ⋙ Q

instance (n : ℤ) : (singleFunctor C n).Additive := by
  dsimp only [singleFunctor]
  infer_instance

noncomputable def singleFunctorShiftIso (n a a' : ℤ) (ha' : n + a = a') :
    singleFunctor C a' ⋙ shiftFunctor _ n ≅ singleFunctor C a :=
  Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (Q.commShiftIso n).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (CochainComplex.singleShiftIso C n a a' ha') Q

lemma homologyFunctor_inverts_qis (n : ℤ) :
    (HomotopyCategory.qis C).IsInvertedBy
      (HomotopyCategory.newHomologyFunctor C _ n) := fun X Y f hf => by
  rw [HomotopyCategory.mem_qis_iff] at hf
  exact hf n

noncomputable def homologyFunctor (n : ℤ) : DerivedCategory C ⥤ C :=
  Localization.lift _ (homologyFunctor_inverts_qis C n) Qh

noncomputable def homologyFunctorFactorsh (n : ℤ) : Qh ⋙ homologyFunctor C n ≅
  HomotopyCategory.newHomologyFunctor C _ n := Localization.fac _ _ _

attribute [irreducible] homologyFunctor homologyFunctorFactorsh

noncomputable def homologyFunctorFactors (n : ℤ) : Q ⋙ homologyFunctor C n ≅
    HomologicalComplex.newHomologyFunctor _ _ n :=
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (homologyFunctorFactorsh C n) ≪≫
    HomotopyCategory.newHomologyFunctorFactors _ _ _

noncomputable def singleFunctorCompHomologyFunctorIso (n : ℤ) :
    singleFunctor C n ⋙ homologyFunctor C n ≅ 𝟭 C :=
  Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (homologyFunctorFactors C n) ≪≫
    HomologicalComplex.singleCompHomologyFunctorIso C (ComplexShape.up ℤ) n

instance : (homologyFunctor C n).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_fac_of_essSurj _ _ _
    (homologyFunctorFactorsh C n)

-- could be better to have `IsHomological` extend `PreservesZeroMorphisms` so that
-- we do not have to prove both statement separately
instance : (homologyFunctor C n).IsHomological :=
  Functor.isHomological_of_localization Qh
    (homologyFunctor C n) _ (homologyFunctorFactorsh C n)

noncomputable instance :
    (homologyFunctor C 0).ShiftSequence ℤ :=
  Functor.ShiftSequence.induced (homologyFunctorFactorsh C 0) ℤ
    (homologyFunctor C) (homologyFunctorFactorsh C)
      ⟨⟨(inferInstance :
          Full (Localization.whiskeringLeftFunctor' Qh (HomotopyCategory.qis C) C))⟩,
        (inferInstance :
          Faithful (Localization.whiskeringLeftFunctor' Qh (HomotopyCategory.qis C) C))⟩

variable {C}

lemma isIso_Qh_map_iff {X Y : HomotopyCategory C (ComplexShape.up ℤ)} (f : X ⟶ Y) :
    IsIso (Qh.map f) ↔ HomotopyCategory.qis C f := by
  constructor
  . intro hf
    rw [HomotopyCategory.mem_qis_iff]
    intro n
    rw [← NatIso.isIso_map_iff (homologyFunctorFactorsh C n) f]
    dsimp
    infer_instance
  . intro hf
    exact Localization.inverts Qh (HomotopyCategory.qis C) _ hf

lemma isIso_Q_map_iff {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    IsIso (Q.map φ) ↔
      ∀ (n : ℤ), IsIso ((HomologicalComplex.newHomologyFunctor C _ n).map φ) := by
  dsimp only [Q, Functor.comp]
  rw [← HomotopyCategory.mem_qis_iff', isIso_Qh_map_iff]

lemma isIso_Q_map_iff' {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    IsIso (Q.map φ) ↔ HomologicalComplex.qis _ _ φ :=
  isIso_Q_map_iff φ

instance : Q.IsLocalization (HomologicalComplex.qis C (ComplexShape.up ℤ)) := by
  refine' Functor.IsLocalization.comp (HomotopyCategory.quotient _ _)
    (HomologicalComplex.homotopyEquivalences _ _) Qh (HomotopyCategory.qis C) _ _ _ _
  . intro X Y f hf
    exact (isIso_Q_map_iff f).2 hf
  . apply HomologicalComplex.homotopyEquivalences_subset_qis
  . rintro ⟨K : CochainComplex C ℤ⟩ ⟨L : CochainComplex C ℤ⟩ f hf
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective f
    apply MorphismProperty.map_mem_map
    simpa only [HomotopyCategory.mem_qis_iff'] using hf

lemma isIso_iff {K L : DerivedCategory C} (f : K ⟶ L) :
    IsIso f ↔ ∀ (n : ℤ), IsIso ((homologyFunctor C n).map f) := by
  constructor
  . intro hf n
    infer_instance
  . intro hf
    let g := (Functor.mapArrow Qh).objPreimage (Arrow.mk f)
    refine' ((MorphismProperty.RespectsIso.isomorphisms (DerivedCategory C)).arrow_iso_iff
      ((Functor.mapArrow Qh).objObjPreimageIso (Arrow.mk f))).1 _
    change IsIso (Qh.map g.hom)
    rw [isIso_Qh_map_iff, HomotopyCategory.mem_qis_iff]
    intro n
    have e : Arrow.mk ((homologyFunctor C n).map f) ≅
        Arrow.mk ((HomotopyCategory.newHomologyFunctor _ _ n).map g.hom) :=
      ((homologyFunctor C n).mapArrow.mapIso
        (((Functor.mapArrow Qh).objObjPreimageIso (Arrow.mk f)).symm)) ≪≫
        ((Functor.mapArrowFunctor _ _).mapIso (homologyFunctorFactorsh C n)).app (Arrow.mk g.hom)
    exact ((MorphismProperty.RespectsIso.isomorphisms C).arrow_iso_iff e).1 (hf n)

lemma isZero_iff (K : DerivedCategory C) :
    IsZero K ↔ ∀ (n : ℤ), IsZero ((homologyFunctor C n).obj K) := by
  constructor
  . intro hK n
    rw [IsZero.iff_id_eq_zero, ← ((homologyFunctor C n).map_id K),
      (IsZero.iff_id_eq_zero K).1 hK, Functor.map_zero]
  . intro hK
    have : IsIso (0 : K ⟶ 0) := by
      rw [isIso_iff]
      intro n
      refine' ⟨0, _, _⟩
      . apply (hK n).eq_of_src
      . rw [zero_comp, ← (homologyFunctor C n).map_id, id_zero,
          Functor.map_zero]
    exact IsZero.of_iso (isZero_zero _) (asIso (0 : K ⟶ 0))

section

variable {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact)

lemma isIso_Q_map_fromOfShortComplex :
    IsIso (Q.map (CochainComplex.MappingCone.fromOfShortComplex S)) := by
  rw [isIso_Q_map_iff]
  exact CochainComplex.MappingCone.isIso_homologyMap_fromOfShortComplex hS

noncomputable def triangleOfSESδ :
  Q.obj (S.X₃) ⟶ (Q.obj S.X₁)⟦(1 : ℤ)⟧ :=
    have := isIso_Q_map_fromOfShortComplex hS
    inv (Q.map (CochainComplex.MappingCone.fromOfShortComplex S)) ≫
      Q.map (CochainComplex.MappingCone.triangleδ S.f) ≫
      (Q.commShiftIso (1 : ℤ)).hom.app S.X₁

noncomputable def triangleOfSES : Triangle (DerivedCategory C) :=
  Triangle.mk (Q.map S.f) (Q.map S.g) (triangleOfSESδ hS)

noncomputable def triangleOfSESIso :
    Q.mapTriangle.obj (CochainComplex.MappingCone.triangle S.f) ≅ triangleOfSES hS := by
  have := isIso_Q_map_fromOfShortComplex hS
  refine' Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    (asIso (Q.map (CochainComplex.MappingCone.fromOfShortComplex S))) _ _ _
  . dsimp [triangleOfSES]
    simp only [comp_id, id_comp]
  . dsimp [triangleOfSES, CochainComplex.MappingCone.fromOfShortComplex, asIso]
    rw [id_comp, ← Q.map_comp, CochainComplex.MappingCone.inr_desc]
  . dsimp [triangleOfSES, triangleOfSESδ]
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
    (by simp only [← Functor.map_comp, comp_dist_triangle_mor_zero₁₂ _ hT,
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
  dsimp only [Q, Functor.comp] at f
  obtain ⟨X', g', s', hs', fac⟩ :=
    MorphismProperty.HasRightCalculusOfFractions.fac Qh (HomotopyCategory.qis C) f
  rw [← isIso_Qh_map_iff] at hs'
  obtain ⟨X', rfl⟩ := HomotopyCategory.quotient_obj_surjective X'
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g'
  obtain ⟨s, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective s'
  exact ⟨X', s, hs', g, fac⟩

lemma left_fac (X Y : CochainComplex C ℤ) (f : Q.obj X ⟶ Q.obj Y) :
    ∃ (Y' : CochainComplex C ℤ) (g : X ⟶ Y') (s : Y ⟶ Y') (hs : IsIso (Q.map s)),
      f = Q.map g ≫ inv (Q.map s) := by
  dsimp only [Q, Functor.comp] at f
  obtain ⟨X', g', s', hs', fac⟩ :=
    MorphismProperty.HasLeftCalculusOfFractions.fac Qh (HomotopyCategory.qis C) f
  rw [← isIso_Qh_map_iff] at hs'
  obtain ⟨X', rfl⟩ := HomotopyCategory.quotient_obj_surjective X'
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g'
  obtain ⟨s, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective s'
  exact ⟨X', g, s, hs', fac⟩

end DerivedCategory
