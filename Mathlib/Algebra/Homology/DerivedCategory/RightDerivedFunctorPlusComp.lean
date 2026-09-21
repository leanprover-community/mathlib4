/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.Algebra.Homology.HomotopyCategory.Devissage
public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedComposition
public import Mathlib.CategoryTheory.Triangulated.TStructure.Homology

/-!
# ...

-/

@[expose] public section

open CategoryTheory Category Limits

namespace CategoryTheory.Functor

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [EnoughInjectives C]
  {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} [F.Additive] [G.Additive] [H.Additive]
  (e : F ⋙ G ≅ H)

section

variable (F) in
lemma isIso_rightDerivedFunctorPlusUnith_app_of_bounded
    (K : CochainComplex C ℤ) (a b : ℤ) [ha : K.IsStrictlyGE a] [K.IsStrictlyLE b]
    (hK : ∀ (i : ℤ) (_ : a ≤ i) (_ : i ≤ b),
      IsIso (F.rightDerivedFunctorPlusUnith.app
        ((HomotopyCategory.Plus.singleFunctor C 0).obj (K.X i)))) :
    IsIso (F.rightDerivedFunctorPlusUnith.app
      ⟨(HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K, by
        simp only [HomotopyCategory.plus_quotient_obj_iff]
        exact ⟨a, ha⟩⟩) := by
  let S := (ObjectProperty.ofNatTrans F.rightDerivedFunctorPlusUnith).map
    (HomotopyCategory.Plus.ι C)
  have : (ObjectProperty.ofNatTrans F.rightDerivedFunctorPlusUnith).IsTriangulated := by
    infer_instance
  suffices S ((HomotopyCategory.quotient _ _).obj K) by
    dsimp only [S] at this
    change (ObjectProperty.ofNatTrans (F.rightDerivedFunctorPlusUnith)) _
    rw [← ObjectProperty.prop_map_obj_iff (ObjectProperty.ofNatTrans
      (F.rightDerivedFunctorPlusUnith)) (HomotopyCategory.Plus.ι C)]
    exact this
  apply HomotopyCategory.mem_subcategory_of_strictly_bounded _ _ a b
  intro i ha hb
  replace hK := hK i ha hb
  change (ObjectProperty.ofNatTrans F.rightDerivedFunctorPlusUnith) _ at hK
  simp only [← ObjectProperty.prop_map_obj_iff (ObjectProperty.ofNatTrans
    F.rightDerivedFunctorPlusUnith) (HomotopyCategory.Plus.ι C)] at hK
  exact hK

variable (F) in
open DerivedCategory.Plus.TStructure in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma isIso_rightDerivedFunctorPlusUnith_app
    (K : CochainComplex C ℤ) (a : ℤ) [ha : K.IsStrictlyGE a]
    (hK : ∀ (i : ℤ) (_ : a ≤ i),
      IsIso (F.rightDerivedFunctorPlusUnith.app
        ((HomotopyCategory.Plus.singleFunctor C 0).obj (K.X i)))) :
    IsIso (F.rightDerivedFunctorPlusUnith.app
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
      mor₁ := (HomotopyCategory.Plus.fullyFaithfulι _).preimage T.mor₁
      mor₂ := (HomotopyCategory.Plus.fullyFaithfulι _).preimage T.mor₂
      mor₃ := (HomotopyCategory.Plus.fullyFaithfulι _).preimage (T.mor₃ ≫
        ((HomotopyCategory.Plus.ι C).commShiftIso (1 : ℤ)).inv.app M') }
  have hT' : T' ∈ distTriang _ := by
    rw [← (HomotopyCategory.Plus.ι C).map_distinguished_iff]
    refine Pretriangulated.isomorphic_distinguished _ hT _
      (Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by aesop) (by aesop) ?_)
    dsimp [T']
    simp only [map_id, comp_id, id_comp]
    change (_ ≫ _) ≫ _ = _
    rw [assoc, Iso.inv_hom_id_app]
    apply comp_id
  have : IsIso (F.rightDerivedFunctorPlusUnith.app L') := by
    apply isIso_rightDerivedFunctorPlusUnith_app_of_bounded _ _ a (n + 1)
    intro i hi hi'
    exact (NatTrans.isIso_app_iff_of_iso _
      (Functor.mapIso _ (Iso.ofIsIso (K.isIso_πStupidTrunc_f (n + 1) i hi')))).1 (hK i hi)
  have : (DerivedCategory.Plus.Qh.obj M').IsGE (n + 2) := by
    rw [← DerivedCategory.Plus.isGE_ι_obj_iff]
    apply DerivedCategory.TStructure.t.isGE_of_iso
      ((DerivedCategory.quotientCompQhIso C).symm.app (K.stupidTrunc e₂)) (n + 2)
  have : (DerivedCategory.Plus.Qh.obj (F.mapHomotopyCategoryPlus.obj M')).IsGE (n + 2) := by
    rw [← DerivedCategory.Plus.isGE_ι_obj_iff]
    exact DerivedCategory.TStructure.t.isGE_of_iso
      (show DerivedCategory.Q.obj ((F.mapHomologicalComplex _).obj (K.stupidTrunc e₂)) ≅ _ from
        (DerivedCategory.quotientCompQhIso D).symm.app _) _
  have h₁ : IsIso ((DerivedCategory.Plus.homologyFunctor D n).map
      ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).map T'.mor₂)) :=
    t.isIso_homologyFunctor_map_mor₂_of_isGE _
      ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).map_distinguished _ hT')
      n (n + 2) (by omega) (by dsimp; infer_instance)
  have h₂ : IsIso ((DerivedCategory.Plus.homologyFunctor D n).map
    ((DerivedCategory.Plus.Qh ⋙ F.rightDerivedFunctorPlus).map T'.mor₂)) :=
    t.isIso_homologyFunctor_map_mor₂_of_isGE _
      ((DerivedCategory.Plus.Qh ⋙ F.rightDerivedFunctorPlus).map_distinguished _ hT')
      n (n + 2) (by omega) (by dsimp; infer_instance)
  have e'' : Arrow.mk ((DerivedCategory.Plus.homologyFunctor D n).map
    ((F.rightDerivedFunctorPlusUnith).app K')) ≅
      Arrow.mk ((DerivedCategory.Plus.homologyFunctor D n).map
        ((F.rightDerivedFunctorPlusUnith).app L')) :=
      Arrow.isoMk (@asIso _ _ _ _ _ h₁) (@asIso _ _ _ _ _ h₂) (by
        dsimp
        simp only [← Functor.map_comp]
        congr 1
        exact F.rightDerivedFunctorPlusUnith.naturality T'.mor₂)
  apply ((MorphismProperty.isomorphisms D).arrow_mk_iso_iff e'').2
  change IsIso _
  infer_instance

end


variable [EnoughInjectives D]
noncomputable def rightDerivedFunctorPlusCompNatTrans :
    H.rightDerivedFunctorPlus ⟶ F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus :=
  Functor.natTransOfIsRightDerivedFunctorComp
    (mapHomotopyCategoryPlusCompIso e) DerivedCategory.Plus.Qh DerivedCategory.Plus.Qh
    DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C)
    F.rightDerivedFunctorPlusUnith G.rightDerivedFunctorPlusUnith H.rightDerivedFunctorPlusUnith

lemma isIso_rightDerivedFunctorPlusCompNatTrans_app (K : HomotopyCategory.Plus C)
    (_ : IsIso (F.rightDerivedFunctorPlusUnith.app K))
    (_ : IsIso (G.rightDerivedFunctorPlusUnith.app (F.mapHomotopyCategoryPlus.obj K)))
    (_ : IsIso (H.rightDerivedFunctorPlusUnith.app K)) :
    IsIso ((rightDerivedFunctorPlusCompNatTrans e).app (DerivedCategory.Plus.Qh.obj K)) :=
  isIso_natTransOfIsRightDerivedFunctorComp_app
    (mapHomotopyCategoryPlusCompIso e) DerivedCategory.Plus.Qh DerivedCategory.Plus.Qh
    DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C)
    F.rightDerivedFunctorPlusUnith G.rightDerivedFunctorPlusUnith H.rightDerivedFunctorPlusUnith K

/-- isIso_rightDerivedFunctorPlusCompNatTrans' -/
lemma isIso_rightDerivedFunctorPlusCompNatTrans'
    (h : ∀ (K : HomotopyCategory.Plus (InjectiveObject C)),
      IsIso (G.rightDerivedFunctorPlusUnith.app
        ((InjectiveObject.ι C ⋙ F).mapHomotopyCategoryPlus.obj K))) :
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
  obtain ⟨M, ⟨e'⟩⟩ : ∃ (M : HomotopyCategory.Plus (InjectiveObject C)),
    Nonempty (((InjectiveObject.ι C).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh).obj M ≅ K) :=
      ⟨_, ⟨Functor.objObjPreimageIso _ _⟩⟩
  refine ⟨((InjectiveObject.ι C).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).obj M,
    e'.symm, ?_⟩
  apply isIso_rightDerivedFunctorPlusCompNatTrans_app
  · infer_instance
  · apply h
  · infer_instance

instance isIso_rightDerivedFunctorPlusCompNatTrans
    [hFG : ∀ (I : InjectiveObject C), IsIso (G.rightDerivedFunctorPlusUnith.app
        ((HomotopyCategory.Plus.singleFunctor D 0).obj (F.obj ((InjectiveObject.ι C).obj I))))] :
    IsIso (rightDerivedFunctorPlusCompNatTrans e) := by
  refine isIso_rightDerivedFunctorPlusCompNatTrans' _ (fun ⟨X, hX⟩ ↦ ?_)
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  simp only [HomotopyCategory.plus_quotient_obj_iff] at hX
  obtain ⟨n, hn⟩ := hX
  exact G.isIso_rightDerivedFunctorPlusUnith_app
    (((InjectiveObject.ι C ⋙ F).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) n
    (fun i _ => hFG _)

end CategoryTheory.Functor
