import Mathlib.Algebra.Homology.HomotopyCategory.Plus
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Shift.SingleFunctorsLift

open CategoryTheory Category Triangulated Limits

variable {C : Type*} [Category C] [Abelian C]
  [HasDerivedCategory C]

namespace HomotopyCategory

namespace Plus

variable (C)

abbrev subcategoryAcyclic :
    Triangulated.Subcategory (HomotopyCategory.Plus C) :=
  (HomotopyCategory.subcategoryAcyclic C).inverseImage (HomotopyCategory.Plus.ι C)

lemma qis_eq_subcategoryAcyclic_W :
    HomotopyCategory.Plus.qis C = (subcategoryAcyclic C).W := by
  ext K L f
  obtain ⟨M, g, h, mem⟩ := CategoryTheory.Pretriangulated.distinguished_cocone_triangle f
  have mem' := (HomotopyCategory.Plus.ι C).map_distinguished _ mem
  erw [(subcategoryAcyclic C).mem_W_iff_of_distinguished _ mem,
    ← (HomotopyCategory.subcategoryAcyclic C).mem_W_iff_of_distinguished _ mem',
    ← HomotopyCategory.qis_eq_subcategoryAcyclic_W]
  rfl

end Plus

end HomotopyCategory

namespace DerivedCategory

open TStructure

namespace Plus

def Qh : HomotopyCategory.Plus C ⥤ Plus C :=
  t.plus.lift (HomotopyCategory.Plus.ι _ ⋙ DerivedCategory.Qh) (by
    rintro ⟨⟨X⟩, n, h⟩
    dsimp at h
    have : (DerivedCategory.Q.obj X).IsGE n := inferInstance
    refine' ⟨n, ⟨_⟩⟩
    dsimp [t]
    change (DerivedCategory.Q.obj X).IsGE n
    infer_instance)

noncomputable instance : (Qh : _ ⥤ Plus C).CommShift ℤ := by
  dsimp only [Qh]
  infer_instance

instance : (Qh : _ ⥤ Plus C).IsTriangulated := by
  dsimp only [Qh]
  infer_instance

lemma Qh_map_bijective_of_isKInjective (K L : HomotopyCategory.Plus C)
    (_ : CochainComplex.IsKInjective L.1.as) : Function.Bijective (Qh.map : (K ⟶ L) → _) :=
  CochainComplex.Qh_map_bijective_of_isKInjective K.1 L.1.as

variable (C)

lemma Qh_inverts : (HomotopyCategory.Plus.qis C).IsInvertedBy Plus.Qh := by
  intro X Y f hf
  have : IsIso (ι.map (Qh.map f)) :=
    Localization.inverts DerivedCategory.Qh (HomotopyCategory.qis C _) _ hf
  exact isIso_of_reflects_iso (Qh.map f) ι

namespace QhIsLocalization

noncomputable abbrev Loc := (HomotopyCategory.Plus.subcategoryAcyclic C).W.Localization

variable {C}

noncomputable abbrev LocQ : HomotopyCategory.Plus C ⥤ Loc C :=
  (HomotopyCategory.Plus.subcategoryAcyclic C).W.Q

lemma locQ_obj_surjective (X : Loc C) : ∃ (K : HomotopyCategory.Plus C), X = LocQ.obj K := ⟨_, rfl⟩

variable (C)

lemma Qh_inverts' : (HomotopyCategory.Plus.subcategoryAcyclic C).W.IsInvertedBy Plus.Qh := by
  rw [← HomotopyCategory.Plus.qis_eq_subcategoryAcyclic_W]
  apply Plus.Qh_inverts

noncomputable def π : Loc C ⥤ DerivedCategory.Plus C :=
  Localization.lift _ (Qh_inverts' C) LocQ

noncomputable def fac : LocQ ⋙ π C ≅ Qh :=
  Localization.fac _ _ _

variable {C}

noncomputable def QhObjIso (K : HomotopyCategory C (ComplexShape.up ℤ))
    (hK : K ∈ (HomotopyCategory.subcategoryPlus C).set) :
    Plus.ι.obj ((π C).obj (LocQ.obj ⟨K, hK⟩)) ≅ DerivedCategory.Qh.obj K :=
  Plus.ι.mapIso ((fac C).app ⟨K, hK⟩)

lemma ι_π_LocQ_map_eq {K L : HomotopyCategory C (ComplexShape.up ℤ)}
    (f : K ⟶ L)
    (hK : K ∈ (HomotopyCategory.subcategoryPlus C).set)
    (hL : L ∈ (HomotopyCategory.subcategoryPlus C).set) :
    ι.map ((π C).map (LocQ.map (f : ⟨K, hK⟩ ⟶ ⟨L, hL⟩))) = (QhObjIso K hK).hom ≫
      DerivedCategory.Qh.map f ≫ (QhObjIso L hL).inv:= by
  dsimp [QhObjIso]
  have eq := Plus.ι.congr_map ((fac C).hom.naturality (f : ⟨K, hK⟩ ⟶ ⟨L, hL⟩))
  dsimp at eq
  simp only [Functor.map_comp] at eq
  erw [← reassoc_of% eq]
  rw [← Functor.map_comp, ← Functor.map_comp, Iso.hom_inv_id_app]
  erw [comp_id]

-- see Verdier II 2.3.5 (a), which should be formalized more generally
lemma right_localizing {K K' : HomotopyCategory C (ComplexShape.up ℤ)} (φ : K ⟶ K')
    (hK : K ∈ (HomotopyCategory.subcategoryPlus C).set)
    (hφ : IsIso (DerivedCategory.Qh.map φ)) :
    ∃ (K'' : HomotopyCategory C (ComplexShape.up ℤ))
    (hK'' : K'' ∈ (HomotopyCategory.subcategoryPlus C).set) (f : K' ⟶ K''),
    IsIso (DerivedCategory.Qh.map f) := by
  obtain ⟨K : CochainComplex C ℤ⟩ := K
  obtain ⟨n, (hn : K.IsStrictlyGE n)⟩ := hK
  obtain ⟨K' : CochainComplex C ℤ⟩ := K'
  have : K'.IsGE n := by
    have hK : K.IsGE n := inferInstance
    rw [← isGE_Q_obj_iff] at hK ⊢
    have e : Q.obj K ≅ Q.obj K' := asIso (DerivedCategory.Qh.map φ)
    exact isGE_of_iso e n
  refine' ⟨(HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj (K'.truncGE n), _,
    (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (K'.truncGEπ n), _⟩
  · refine' ⟨n, _⟩
    dsimp [HomotopyCategory.quotient, Quotient.functor]
    infer_instance
  · change IsIso (DerivedCategory.Q.map _)
    rw [isIso_Q_map_iff_quasiIso, K'.quasiIso_truncGEπ_iff n]
    infer_instance

-- it would be better to formalize right-localizing subcategories...
noncomputable instance : Full (π C) := Functor.fullOfSurjective _ (fun K L => by
  obtain ⟨⟨K, hK⟩, rfl⟩ := locQ_obj_surjective K
  obtain ⟨⟨L, hL⟩, rfl⟩ := locQ_obj_surjective L
  intro φ
  obtain ⟨ψ, hψ⟩ : ∃ (ψ : DerivedCategory.Qh.obj K ⟶ DerivedCategory.Qh.obj L),
    ψ = (QhObjIso K hK).inv ≫ DerivedCategory.Plus.ι.map φ ≫ (QhObjIso L hL).hom := ⟨_, rfl⟩
  have hψ' : DerivedCategory.Plus.ι.map φ =
    (QhObjIso K hK).hom ≫ ψ ≫ (QhObjIso L hL).inv := by simp [hψ]
  obtain ⟨γ, hγ⟩ :=  Localization.exists_leftFraction DerivedCategory.Qh (HomotopyCategory.qis C _) ψ
  obtain ⟨K', g, s, hs, rfl⟩ := γ.cases
  dsimp only [MorphismProperty.LeftFraction.map] at hγ
  rw [← isIso_Qh_map_iff] at hs
  obtain ⟨K'', hK'', f, _⟩ := right_localizing s hL hs
  let α' : K ⟶ K'' := g ≫ f
  let α : (⟨K, hK⟩ : HomotopyCategory.Plus C) ⟶ ⟨K'', hK''⟩ := α'
  let β' : L ⟶ K'' := s ≫ f
  let β : (⟨L, hL⟩ : HomotopyCategory.Plus C) ⟶ ⟨K'', hK''⟩ := β'
  let e := Localization.isoOfHom LocQ (HomotopyCategory.Plus.subcategoryAcyclic C).W β (by
    rw [← HomotopyCategory.Plus.qis_eq_subcategoryAcyclic_W]
    dsimp [HomotopyCategory.Plus.qis, MorphismProperty.inverseImage, HomotopyCategory.Plus.ι, Subcategory.ι]
    rw [← isIso_Qh_map_iff, Functor.map_comp]
    infer_instance)
  refine' ⟨LocQ.map α ≫ e.inv, _⟩
  erw [← cancel_mono ((π C).mapIso e).hom, ← Functor.map_comp, assoc, e.inv_hom_id, comp_id]
  apply DerivedCategory.Plus.ι.map_injective
  rw [Functor.map_comp, hψ', hγ]
  dsimp only
  dsimp
  simp only [assoc]
  rw [ι_π_LocQ_map_eq (g ≫ f) hK hK'', Functor.map_comp, assoc]
  congr 2
  rw [ι_π_LocQ_map_eq (s ≫ f) hL hK'', Iso.inv_hom_id_assoc,
    Functor.map_comp, assoc, IsIso.inv_hom_id_assoc])

instance : (π C ⋙ Plus.ι).Additive := by
  have : Localization.Lifting LocQ (Subcategory.W (HomotopyCategory.Plus.subcategoryAcyclic C))
    (Qh ⋙ ι) (π C ⋙ ι) := ⟨isoWhiskerRight (fac C) ι⟩
  rw [← Localization.functor_additive_iff LocQ
    (HomotopyCategory.Plus.subcategoryAcyclic C).W
    (Qh ⋙ Plus.ι)
    (π C ⋙ Plus.ι)]
  infer_instance

instance : Faithful (π C ⋙ Plus.ι) := by
  suffices ∀ {K L : HomotopyCategory.Plus C} (φ : K ⟶ L)
      (_ : (LocQ ⋙ π C ⋙ Plus.ι).map φ = 0), LocQ.map φ = 0 by
    refine' ⟨fun {K L} f₁ f₂ h => _⟩
    obtain ⟨f, rfl⟩ : ∃ f, f₁ = f + f₂ := ⟨f₁-f₂, by simp⟩
    simp only [add_left_eq_self, Functor.map_add] at h ⊢
    obtain ⟨φ, hφ⟩ := Localization.exists_leftFraction LocQ
      (HomotopyCategory.Plus.subcategoryAcyclic C).W f
    have := this φ.f (by
      have : LocQ.map φ.f = f ≫ (Localization.isoOfHom LocQ (Subcategory.W (HomotopyCategory.Plus.subcategoryAcyclic C)) φ.s φ.hs).hom := by
        simp [hφ]
      dsimp at h ⊢
      rw [this]
      simp [h])
    rw [hφ, MorphismProperty.LeftFraction.map_eq, this, zero_comp]
  intro K L φ hφ
  dsimp at hφ
  rw [ι_π_LocQ_map_eq φ K.2 L.2, ← cancel_mono (QhObjIso L.1 L.2).hom,
    ← cancel_epi (QhObjIso K.1 K.2).inv, assoc, assoc, zero_comp, comp_zero,
    Iso.inv_hom_id, comp_id, Iso.inv_hom_id_assoc, ← DerivedCategory.Qh.map_zero,
    MorphismProperty.map_eq_iff_postcomp DerivedCategory.Qh
    (HomotopyCategory.subcategoryAcyclic C).W] at hφ
  simp only [zero_comp] at hφ
  obtain ⟨L', s, hs, eq⟩ := hφ
  have : IsIso (DerivedCategory.Qh.map s) := by
    rw [isIso_Qh_map_iff, HomotopyCategory.qis_eq_subcategoryAcyclic_W]
    exact hs
  obtain ⟨L'', hL'', t, ht⟩ := right_localizing s L.2 inferInstance
  rw [← LocQ.map_zero, MorphismProperty.map_eq_iff_postcomp LocQ
      (HomotopyCategory.Plus.subcategoryAcyclic C).W]
  refine' ⟨⟨L'', hL''⟩, (s ≫ t : L.1 ⟶ L''), _, _⟩
  · rw [← HomotopyCategory.Plus.qis_eq_subcategoryAcyclic_W]
    dsimp [HomotopyCategory.Plus.qis, MorphismProperty.inverseImage, HomotopyCategory.Plus.ι, Subcategory.ι]
    rw [← isIso_Qh_map_iff, Functor.map_comp]
    infer_instance
  · erw [zero_comp, reassoc_of% eq, zero_comp]

instance : Faithful (π C) where
  map_injective h := by
    apply (π C ⋙ Plus.ι).map_injective
    dsimp
    rw [h]

instance : EssSurj (π C) where
  mem_essImage := by
    rintro ⟨K, n, hn⟩
    obtain ⟨L, ⟨e⟩⟩ : ∃ (L : CochainComplex C ℤ), Nonempty (Q.obj L ≅ K) :=
      ⟨_, ⟨Q.objObjPreimageIso K⟩⟩
    have : IsIso (Q.map (L.truncGEπ n)) := by
      rw [isIso_Q_map_iff_quasiIso, CochainComplex.quasiIso_truncGEπ_iff, ← isGE_Q_obj_iff]
      have : K.IsGE n := hn.mem
      exact isGE_of_iso e.symm n
    let L' : Loc C := LocQ.obj
      ⟨(HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj (L.truncGE n), n, by
        dsimp [HomotopyCategory.quotient, Quotient.functor]
        infer_instance⟩
    exact ⟨L', ⟨(fac C).app _ ≪≫ (Plus.ι).preimageIso ((asIso (Q.map (L.truncGEπ n))).symm ≪≫ e)⟩⟩

noncomputable instance : IsEquivalence (π C) := Equivalence.ofFullyFaithfullyEssSurj _

noncomputable instance : Pretriangulated (Loc C) := inferInstance

end QhIsLocalization

instance : Qh.IsLocalization (HomotopyCategory.Plus.qis C) := by
  rw [HomotopyCategory.Plus.qis_eq_subcategoryAcyclic_W]
  exact Functor.IsLocalization.of_equivalence_target
    (HomotopyCategory.Plus.subcategoryAcyclic C).W.Q (HomotopyCategory.Plus.subcategoryAcyclic C).W Qh
    (QhIsLocalization.π C).asEquivalence (Localization.fac _ _ _)

noncomputable def singleFunctors : SingleFunctors C (Plus C) ℤ :=
  SingleFunctors.lift (DerivedCategory.singleFunctors C) Plus.ι
      (fun n => t.plus.lift (DerivedCategory.singleFunctor C n) (fun X => by
        refine' ⟨n, _⟩
        constructor
        change ((singleFunctor C n).obj X).IsGE n
        infer_instance))
      (fun n => Iso.refl _)

noncomputable abbrev singleFunctor (n : ℤ) : C ⥤ Plus C := (singleFunctors C).functor n

noncomputable def homologyFunctor (n : ℤ) : Plus C ⥤ C :=
    Plus.ι ⋙ DerivedCategory.homologyFunctor C n

end Plus

end DerivedCategory
