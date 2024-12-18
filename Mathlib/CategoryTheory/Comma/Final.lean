/-
Copyright (c) 2024 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.IsConnected
import Mathlib.CategoryTheory.Grothendieck

/-!
# Finality of Projections in Comma Categories

We show that `fst L R` is final if `R` is and that `snd L R` is initial if `L` is.
As a corollary, we show that `Comma L R` with `L : A ⥤ T` and `R : B ⥤ T` is connected if `R` is
final and `A` is connected.

## References

* [M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006], Lemma 3.4.3
-/

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

namespace CategoryTheory

namespace Comma

open Limits Functor CostructuredArrow

section Small

variable {A : Type v₁} [Category.{v₁} A]
variable {B : Type v₁} [Category.{v₁} B]
variable {T : Type v₁} [Category.{v₁} T]
variable (L : A ⥤ T) (R : B ⥤ T)

private lemma final_fst_small [R.Final] : (fst L R).Final := by
  rw  [Functor.final_iff_isIso_colimit_pre]
  intro G
  let i : colimit G ≅ colimit (fst L R ⋙ G) :=
    colimitIsoColimitGrothendieck L G ≪≫
    (Final.colimitIso (Grothendieck.pre (functor L) R) (grothendieckProj L ⋙ G)).symm ≪≫
    HasColimit.isoOfNatIso (Iso.refl _) ≪≫
    Final.colimitIso (grothendieckPrecompFunctorEquivalence L R).functor (fst L R ⋙ G)
  convert i.isIso_inv
  apply colimit.hom_ext
  intro ⟨a, b, f⟩
  simp only [colimit.ι_pre, comp_obj, fst_obj, grothendieckPrecompFunctorEquivalence_functor,
    Iso.trans_inv, Iso.symm_inv, Category.assoc, i]
  change _ = colimit.ι (fst L R ⋙ G)
    ((grothendieckPrecompFunctorToComma L R).obj ⟨b, CostructuredArrow.mk f⟩) ≫ _
  simp

end Small

section NonSmall

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {T : Type u₃} [Category.{v₃} T]
variable (L : A ⥤ T) (R : B ⥤ T)

instance final_fst [R.Final] : (fst L R).Final := by
  let sA : A ≌ AsSmall.{max u₁ u₂ u₃ v₁ v₂ v₃} A := AsSmall.equiv
  let sB : B ≌ AsSmall.{max u₁ u₂ u₃ v₁ v₂ v₃} B := AsSmall.equiv
  let sT : T ≌ AsSmall.{max u₁ u₂ u₃ v₁ v₂ v₃} T := AsSmall.equiv
  let L' := sA.inverse ⋙ L ⋙ sT.functor
  let R' := sB.inverse ⋙ R ⋙ sT.functor
  let fC : Comma L R ⥤ Comma L' R' :=
    map (F₁ := sA.functor) (F := sT.functor) (F₂ := sB.functor)
      (isoWhiskerRight sA.unitIso (L ⋙ sT.functor)).hom
      (isoWhiskerRight sB.unitIso (R ⋙ sT.functor)).hom
  have : Final (fst L' R') := final_fst_small _ _
  apply final_of_natIso (F := (fC ⋙ fst L' R' ⋙ sA.inverse))
  exact (Functor.associator _ _ _).symm.trans (Iso.compInverseIso (mapFst _ _))

instance initial_snd [L.Initial] : (snd L R).Initial := by
  haveI : ((opFunctor L R).leftOp ⋙ fst R.op L.op).Final :=
    final_equivalence_comp (opEquiv L R).functor.leftOp (fst R.op L.op)
  haveI : (snd L R).op.Final := final_of_natIso (opFunctorCompFst _ _)
  apply initial_of_final_op

/-- `Comma L R` with `L : A ⥤ T` and `R : B ⥤ T` is connected if `R` is final and `A` is
connected. -/
instance isConnected_comma_of_final [IsConnected A] [R.Final] : IsConnected (Comma L R) := by
  rwa [Types.isConnected_iff_of_final (fst L R)]

/-- `Comma L R` with `L : A ⥤ T` and `R : B ⥤ T` is connected if `L` is initial and `B` is
connected. -/
instance isConnected_comma_of_initial [IsConnected B] [L.Initial] : IsConnected (Comma L R) := by
  sorry

end NonSmall

section Small

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{u₂} B]
variable {T : Type u₃} [Category.{v₃} T]
variable {L : A ⥤ T} {R : B ⥤ T}
variable {A' : Type u₄} [Category.{v₄} A']
variable {B' : Type u₅} [Category.{v₅} B']
variable {T' : Type u₆} [Category.{u₂} T']
variable {L' : A' ⥤ T'} {R' : B' ⥤ T'}
variable {F : A ⥤ A'} {G : B ⥤ B'} {H : T ⥤ T'}
variable (iL : F ⋙ L' ≅ L ⋙ H) (iR : G ⋙ R' ≅ R ⋙ H)
variable [IsFiltered B] [IsFiltered B']
variable [R.Final] [R'.Final] [F.Final] [G.Final]

lemma map_final : (Comma.map iL.hom iR.inv).Final := by
  haveI : IsFiltered T := IsFiltered.of_final R
  haveI : IsFiltered T' := IsFiltered.of_final R'
  haveI := final_of_natIso iR
  haveI : H.Final := final_of_final_comp R H
  fconstructor
  rintro ⟨i₂, j₂, u₂⟩
  let φ' : StructuredArrow i₂ F ⥤ StructuredArrow (L'.obj i₂) H :=
    StructuredArrow.map₂ (𝟙 _) iL.hom
  let ψ' : StructuredArrow j₂ G ⥤ StructuredArrow (L'.obj i₂) H :=
    StructuredArrow.map₂ u₂ iR.hom
  have : StructuredArrow ⟨i₂, j₂, u₂⟩ (map iL.hom iR.inv) ≌ Comma φ' ψ' := by
    sorry
  rw [isConnected_iff_of_equivalence this]
  haveI : (StructuredArrow.map₂ (R := G ⋙ R') (G := 𝟭 _) u₂ iR.hom).Final := by
    sorry
  have : ψ' ≅ StructuredArrow.post j₂ G R' ⋙ StructuredArrow.map₂ (G := 𝟭 _) u₂ iR.hom :=
    Iso.refl ψ'
  haveI := final_of_natIso this.symm
  infer_instance

#check StructuredArrow.final_map₂_id

end Small

end Comma

end CategoryTheory
