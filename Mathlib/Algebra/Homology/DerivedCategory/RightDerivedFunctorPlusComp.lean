/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

/-!
# ...

-/

@[expose] public section

open CategoryTheory Category Limits

namespace CategoryTheory.Functor

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [EnoughInjectives C] [EnoughInjectives D]
  {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} [F.Additive] [G.Additive] [H.Additive]
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

/-- isIso_rightDerivedFunctorPlusCompNatTrans' -/
lemma isIso_rightDerivedFunctorPlusCompNatTrans'
    (h : ∀ (K : HomotopyCategory.Plus (InjectiveObject C)),
      IsIso (G.rightDerivedFunctorPlusUnit.app
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
    [hFG : ∀ (I : InjectiveObject C), IsIso (G.rightDerivedFunctorPlusUnit.app
        ((HomotopyCategory.Plus.singleFunctor D 0).obj (F.obj ((InjectiveObject.ι C).obj I))))] :
    IsIso (rightDerivedFunctorPlusCompNatTrans e) := by
  refine isIso_rightDerivedFunctorPlusCompNatTrans' _ (fun ⟨X, hX⟩ ↦ ?_)
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  simp only [HomotopyCategory.plus_quotient_obj_iff] at hX
  obtain ⟨n, hn⟩ := hX
  exact G.isIso_rightDerivedFunctorPlusUnit_app
    (((InjectiveObject.ι C ⋙ F).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) n
    (fun i _ => hFG _)

end CategoryTheory.Functor
