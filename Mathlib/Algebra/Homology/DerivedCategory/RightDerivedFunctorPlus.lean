import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.Algebra.Homology.HomotopyCategory.Devissage
import Mathlib.CategoryTheory.Functor.Derived.RightDerivedComposition

open CategoryTheory Category Limits

def HomotopyCategory.Plus.mk {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] (K : CochainComplex C ℤ) (hK : ∃ n, K.IsStrictlyGE n):
    HomotopyCategory.Plus C :=
  ⟨(HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K, hK.choose, hK.choose_spec⟩

namespace CochainComplex

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]

open ComplexShape

lemma isIso_πStupidTrunc_f (K : CochainComplex C ℤ) (n i : ℤ) (hi : i ≤ n) :
    IsIso ((K.πStupidTrunc (embeddingUpIntLE n)).f i) := by
  have ⟨k, hk⟩ := Int.eq_add_ofNat_of_le hi
  exact HomologicalComplex.isIso_πStupidTrunc_f K _ (i := k) (by dsimp; omega)

lemma isIso_ιStupidTrunc_f (K : CochainComplex C ℤ) (n i : ℤ) (hi : n ≤ i) :
    IsIso ((K.ιStupidTrunc (embeddingUpIntGE n)).f i) := by
  have ⟨k, hk⟩ := Int.eq_add_ofNat_of_le hi
  exact HomologicalComplex.isIso_ιStupidTrunc_f K _ (i := k) (by dsimp; omega)

end CochainComplex

namespace CategoryTheory

namespace Functor

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]

variable (F : C ⥤ D) [F.Additive]

variable [EnoughInjectives C]

noncomputable def rightDerivedFunctorPlus :
    DerivedCategory.Plus C ⥤ DerivedCategory.Plus D :=
  (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerived DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso C)

noncomputable def rightDerivedFunctorPlusUnit :
    F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ F.rightDerivedFunctorPlus :=
  (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso C)

instance :
    F.rightDerivedFunctorPlus.IsRightDerivedFunctor
      F.rightDerivedFunctorPlusUnit (HomotopyCategory.Plus.quasiIso C) := by
  dsimp only [rightDerivedFunctorPlus, rightDerivedFunctorPlusUnit]
  infer_instance

instance (X : HomotopyCategory.Plus (Injectives C)) :
    IsIso  (F.rightDerivedFunctorPlusUnit.app
      ((Injectives.ι C).mapHomotopyCategoryPlus.obj X)) := by
  dsimp only [rightDerivedFunctorPlus, rightDerivedFunctorPlusUnit]
  infer_instance

noncomputable instance : F.rightDerivedFunctorPlus.CommShift ℤ :=
  IsRightDerivedFunctor.commShift F.rightDerivedFunctorPlus F.rightDerivedFunctorPlusUnit
    (HomotopyCategory.Plus.quasiIso C) ℤ

noncomputable instance : NatTrans.CommShift F.rightDerivedFunctorPlusUnit ℤ := by
  infer_instance

instance : F.rightDerivedFunctorPlus.IsTriangulated :=
  LocalizerMorphism.isTriangulated_of_isRightDerivedFunctor
    (Φ := (Injectives.localizerMorphism C))
    (hF := MorphismProperty.isomorphisms_isInvertedBy _)
    (α := F.rightDerivedFunctorPlusUnit)

section

open DerivedCategory.Plus.TStructure

instance : F.rightDerivedFunctorPlus.RightTExact t t where
  objGE X n hX := by
    obtain ⟨K, hK, ⟨e⟩⟩ : ∃ (K : CochainComplex C ℤ) (hK : K.IsStrictlyGE n),
        Nonempty (X ≅ DerivedCategory.Plus.Qh.obj ⟨⟨K⟩, n, hK⟩) := by
      have : (DerivedCategory.Plus.ι.obj X).IsGE n := hX.1
      obtain ⟨Y, _, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE
        (DerivedCategory.Plus.ι.obj X) n
      refine' ⟨Y, inferInstance, ⟨DerivedCategory.Plus.ι.preimageIso e⟩⟩
    let r := Injectives.rightResolution_localizerMorphism K n
    have e' : (DerivedCategory.Plus.ι.obj (DerivedCategory.Plus.Qh.obj
        ((mapHomotopyCategoryPlus F).obj
          ((mapHomotopyCategoryPlus (Injectives.ι C)).obj r.X₁)))) ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex _).obj (K.injectiveResolution n)) :=
      (DerivedCategory.Plus.QhCompιIsoιCompQh D).app _ ≪≫
        (DerivedCategory.quotientCompQhIso D).app _
    have : t.IsGE ((mapHomotopyCategoryPlus F ⋙ DerivedCategory.Plus.Qh).obj
        ((mapHomotopyCategoryPlus (Injectives.ι C)).obj r.X₁)) n := by
      rw [← DerivedCategory.Plus.isGE_ι_obj_iff]
      exact DerivedCategory.TStructure.t.isGE_of_iso e'.symm n
    have : IsIso (DerivedCategory.Plus.Qh.map r.w) := Localization.inverts _ _ _ r.hw
    have : t.IsGE ((rightDerivedFunctorPlus F).obj (DerivedCategory.Plus.Qh.obj
      ((Injectives.localizerMorphism C).functor.obj r.X₁))) n :=
      t.isGE_of_iso (asIso (F.rightDerivedFunctorPlusUnit.app
        ((Injectives.ι C).mapHomotopyCategoryPlus.obj r.X₁))) n
    apply (t.isGE_of_iso (F.rightDerivedFunctorPlus.mapIso
      (e ≪≫ asIso (DerivedCategory.Plus.Qh.map r.w)).symm))

instance (K : DerivedCategory.Plus C) (n : ℤ) [t.IsGE K n] :
    t.IsGE (F.rightDerivedFunctorPlus.obj K) n :=
  F.rightDerivedFunctorPlus.isGE_obj t t K n

lemma isIso_rightDerivedFunctorPlusUnit_app_of_bounded
    (K : CochainComplex C ℤ) (a b : ℤ) [ha : K.IsStrictlyGE a] [K.IsStrictlyLE b]
    (hK : ∀ (i : ℤ) (_ : a ≤ i) (_ : i ≤ b),
      IsIso (F.rightDerivedFunctorPlusUnit.app
        ((HomotopyCategory.Plus.singleFunctor C 0).obj (K.X i)))) :
    IsIso (F.rightDerivedFunctorPlusUnit.app
      ⟨(HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K, a, ha⟩) := by
  let S := (Triangulated.Subcategory.ofNatTrans (F.rightDerivedFunctorPlusUnit)).map (HomotopyCategory.Plus.ι C)
  suffices S.P ((HomotopyCategory.quotient _ _).obj K) by
    change (Triangulated.Subcategory.ofNatTrans (F.rightDerivedFunctorPlusUnit)).P _
    rw [← Triangulated.Subcategory.mem_map_iff _ (HomotopyCategory.Plus.ι C)]
    exact this
  apply HomotopyCategory.mem_subcategory_of_strictly_bounded _ _ a b
  intro i ha hb
  replace hK := hK i ha hb
  change (Triangulated.Subcategory.ofNatTrans (F.rightDerivedFunctorPlusUnit)).P _ at hK
  simpa only [← Triangulated.Subcategory.mem_map_iff _ (HomotopyCategory.Plus.ι C)] using hK

/-lemma isIso_rightDerivedFunctorPlusUnit_app
    (K : CochainComplex C ℤ) (a : ℤ) [ha : K.IsStrictlyGE a]
    (hK : ∀ (i : ℤ) (_ : a ≤ i),
      IsIso (F.rightDerivedFunctorPlusUnit.app
        ((HomotopyCategory.Plus.singleFunctor C 0).obj (K.X i)))) :
    IsIso (F.rightDerivedFunctorPlusUnit.app
      (HomotopyCategory.Plus.mk K ⟨a, inferInstance⟩)) := by
  rw [DerivedCategory.Plus.isIso_iff]
  intro n
  let e₁ := ComplexShape.embeddingUpIntLE (n + 1)
  let e₂ := ComplexShape.embeddingUpIntGE (n + 2)
  let K' := HomotopyCategory.Plus.mk K ⟨a, inferInstance⟩
  let L' := HomotopyCategory.Plus.mk (K.stupidTrunc e₁) ⟨a, inferInstance⟩
  let M' := HomotopyCategory.Plus.mk (K.stupidTrunc e₂) ⟨a, inferInstance⟩
  let T := CochainComplex.trianglehOfDegreewiseSplit _
      (K.shortComplexStupidTruncSplitting
        (ComplexShape.Embedding.embeddingUpInt_areComplementary (n + 1) (n + 2) (by omega)))
  have hT : T ∈ distTriang _ := by
    apply HomotopyCategory.trianglehOfDegreewiseSplit_distinguished
  let T' : Pretriangulated.Triangle (HomotopyCategory.Plus C) :=
    { obj₁ := M'
      obj₂ := K'
      obj₃ := L'
      mor₁ := (HomotopyCategory.Plus.ι _).preimage T.mor₁
      mor₂ := (HomotopyCategory.Plus.ι _).preimage T.mor₂
      mor₃ := (HomotopyCategory.Plus.ι _).preimage (T.mor₃ ≫
        ((HomotopyCategory.Plus.ι C).commShiftIso (1 : ℤ)).inv.app M') }
  have hT' : T' ∈ distTriang _ := by
    rw [← (HomotopyCategory.Plus.ι C).map_distinguished_iff]
    refine Pretriangulated.isomorphic_distinguished _ hT _
      (Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) ?_)
    dsimp
    simp only [image_preimage, assoc, Iso.inv_hom_id_app, comp_obj, map_id, comp_id, id_comp]
    apply comp_id
  let φ : K' ⟶ L' := (HomotopyCategory.quotient C _).map (K.πStupidTrunc e₁)
  have : IsIso (F.rightDerivedFunctorPlusUnit.app L') := by
    apply isIso_rightDerivedFunctorPlusUnit_app_of_bounded _ _ a (n + 1)
    intro i hi hi'
    exact (NatTrans.isIso_app_iff_of_iso _
      (Functor.mapIso _ (asIso' (K.isIso_πStupidTrunc_f (n + 1) i hi')))).1 (hK i hi)

  have h₁ : IsIso ((DerivedCategory.Plus.homologyFunctor D n).map
      ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).map φ)) := by
    sorry
  have h₂ : IsIso ((DerivedCategory.Plus.homologyFunctor D n).map
    ((DerivedCategory.Plus.Qh ⋙ F.rightDerivedFunctorPlus).map φ)) := sorry

  have e'' : Arrow.mk ((DerivedCategory.Plus.homologyFunctor D n).map
    ((F.rightDerivedFunctorPlusUnit).app K')) ≅
      Arrow.mk ((DerivedCategory.Plus.homologyFunctor D n).map
        ((F.rightDerivedFunctorPlusUnit).app L')) := Arrow.isoMk (asIso' h₁) (asIso' h₂) (by
      dsimp
      simp only [← Functor.map_comp]
      congr 1
      exact F.rightDerivedFunctorPlusUnit.naturality φ)
  apply ((MorphismProperty.RespectsIso.isomorphisms D).arrow_mk_iso_iff e'').2
  change IsIso _
  infer_instance-/

end

noncomputable def rightDerived' (n : ℕ) : C ⥤ D :=
  DerivedCategory.Plus.singleFunctor C 0 ⋙ F.rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.homologyFunctor D n

instance (n : ℕ) : (F.rightDerived' n).Additive := by
  dsimp [rightDerived']
  infer_instance

section
variable (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) {S : ShortComplex C} (hS : S.ShortExact)

open DerivedCategory.Plus.TStructure

noncomputable def rightDerivedδ :
    (F.rightDerived' n₀).obj S.X₃ ⟶ (F.rightDerived' n₁).obj S.X₁ :=
  (DerivedCategory.Plus.homologyFunctor D 0).homologySequenceδ
    (F.rightDerivedFunctorPlus.mapTriangle.obj (t.heartShortExactTriangle _ hS)) n₀ n₁ (by omega)

lemma rightDerived_exact₂ :
    (ShortComplex.mk ((F.rightDerived' n₀).map S.f)
      ((F.rightDerived' n₀).map S.g)
      (by rw [← Functor.map_comp, S.zero, Functor.map_zero])).Exact :=
  (DerivedCategory.Plus.homologyFunctor D 0).homologySequence_exact₂ _
    (F.rightDerivedFunctorPlus.map_distinguished _
      (t.heartShortExactTriangle_distinguished _ hS)) _

@[reassoc (attr := simp)]
lemma rightDerivedδ_comp :
    F.rightDerivedδ n₀ n₁ h hS ≫ (F.rightDerived' n₁).map S.f = 0 :=
  (DerivedCategory.Plus.homologyFunctor D 0).homologySequenceδ_comp
    _ (F.rightDerivedFunctorPlus.map_distinguished _
      (t.heartShortExactTriangle_distinguished _ hS)) _ _ _

@[reassoc (attr := simp)]
lemma comp_rightDerivedδ :
    (F.rightDerived' n₀).map S.g ≫ F.rightDerivedδ n₀ n₁ h hS = 0 :=
  (DerivedCategory.Plus.homologyFunctor D 0).comp_homologySequenceδ
    _ (F.rightDerivedFunctorPlus.map_distinguished _
      (t.heartShortExactTriangle_distinguished _ hS)) _ _ _

lemma rightDerived_exact₁ :
    (ShortComplex.mk (F.rightDerivedδ n₀ n₁ h hS) ((F.rightDerived' n₁).map S.f)
      (by simp)).Exact :=
  (DerivedCategory.Plus.homologyFunctor D 0).homologySequence_exact₁ _
    (F.rightDerivedFunctorPlus.map_distinguished _
      (t.heartShortExactTriangle_distinguished _ hS)) _ _ _

lemma rightDerived_exact₃ :
    (ShortComplex.mk ((F.rightDerived' n₀).map S.g) (F.rightDerivedδ n₀ n₁ h hS)
      (by simp)).Exact :=
  (DerivedCategory.Plus.homologyFunctor D 0).homologySequence_exact₃ _
    (F.rightDerivedFunctorPlus.map_distinguished _
      (t.heartShortExactTriangle_distinguished _ hS)) _ _ _

end

section

variable {F}
variable {G : D ⥤ E} [G.Additive] {H : C ⥤ E} [H.Additive] [EnoughInjectives D]
  (e : F ⋙ G ≅ H)

noncomputable def rightDerivedFunctorPlusCompNatTrans :
    H.rightDerivedFunctorPlus ⟶ F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus :=
  Functor.natTransOfIsRightDerivedFunctorComp
    (mapHomotopyCategoryPlusCompIso e).symm DerivedCategory.Plus.Qh DerivedCategory.Plus.Qh
    DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C)
    F.rightDerivedFunctorPlusUnit G.rightDerivedFunctorPlusUnit H.rightDerivedFunctorPlusUnit

lemma isIso_rightDerivedFunctorPlusCompNatTrans_app (K : HomotopyCategory.Plus C)
    (_ : IsIso (F.rightDerivedFunctorPlusUnit.app K))
    (_ : IsIso (G.rightDerivedFunctorPlusUnit.app (F.mapHomotopyCategoryPlus.obj K)))
    (_ : IsIso (H.rightDerivedFunctorPlusUnit.app K)) :
    IsIso ((rightDerivedFunctorPlusCompNatTrans e).app (DerivedCategory.Plus.Qh.obj K)) :=
  isIso_natTransOfIsRightDerivedFunctorComp_app
    (mapHomotopyCategoryPlusCompIso e).symm DerivedCategory.Plus.Qh DerivedCategory.Plus.Qh
    DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C)
    F.rightDerivedFunctorPlusUnit G.rightDerivedFunctorPlusUnit H.rightDerivedFunctorPlusUnit K

lemma isIso_rightDerivedFunctorPlusCompNatTrans'
    (h : ∀ (K : HomotopyCategory.Plus (Injectives C)),
      IsIso (G.rightDerivedFunctorPlusUnit.app
        ((Injectives.ι C ⋙ F).mapHomotopyCategoryPlus.obj K))) :
    IsIso (rightDerivedFunctorPlusCompNatTrans e) := by
  suffices ∀ K, IsIso ((rightDerivedFunctorPlusCompNatTrans e).app K) from
    NatIso.isIso_of_isIso_app _
  intro K
  suffices ∃ (L : DerivedCategory.Plus C) (_ : K ≅ L),
      IsIso ((rightDerivedFunctorPlusCompNatTrans e).app L) by
    obtain ⟨L, e', _⟩ := this
    have : IsIso (H.rightDerivedFunctorPlus.map e'.inv ≫
        (rightDerivedFunctorPlusCompNatTrans e).app K) := by
      rw [(rightDerivedFunctorPlusCompNatTrans e).naturality e'.inv]
      infer_instance
    simpa only [isIso_comp_left_iff] using this
  obtain ⟨M, ⟨e'⟩⟩ : ∃ (M : HomotopyCategory.Plus (Injectives C)),
    Nonempty (((Injectives.ι C).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).obj M ≅ K) :=
      ⟨_, ⟨Functor.objObjPreimageIso _ _⟩⟩
  refine' ⟨((Injectives.ι C).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).obj M,
    e'.symm, _⟩
  apply isIso_rightDerivedFunctorPlusCompNatTrans_app
  · infer_instance
  · apply h
  · infer_instance

/-instance isIso_rightDerivedFunctorPlusCompNatTrans
    [hFG : ∀ (I : Injectives C), IsIso (G.rightDerivedFunctorPlusUnit.app
        ((HomotopyCategory.Plus.singleFunctor D 0).obj (F.obj ((Injectives.ι C).obj I))))] :
    IsIso (rightDerivedFunctorPlusCompNatTrans e) := by
  apply isIso_rightDerivedFunctorPlusCompNatTrans'
  rintro ⟨⟨K⟩, n, hK⟩
  exact G.isIso_rightDerivedFunctorPlusUnit_app
    (((Injectives.ι C ⋙ F).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) n
    (fun i _ => hFG _)-/

end

end Functor

end CategoryTheory
