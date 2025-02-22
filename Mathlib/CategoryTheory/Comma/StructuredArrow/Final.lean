/-
Copyright (c) 2025 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import Mathlib.CategoryTheory.Comma.Final
import Mathlib.CategoryTheory.Filtered.OfColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.Limits.Preserves.Grothendieck
import Mathlib.CategoryTheory.Limits.Final

/-!
# Finality on Costructured Arrow categories

## References

* [M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006], Proposition 3.1.8(i)
-/

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

namespace Functor

open Limits Functor CostructuredArrow

section Small

variable {A : Type u₁} [SmallCategory A] {B : Type u₁} [SmallCategory B]
variable {T : Type u₁} [SmallCategory T]

attribute [local instance] Grothendieck.final_map

/-- The version of `final_of_final_CostructuredArrowtoOver` on small categories used to prove the
full statement. -/
private lemma final_of_final_CostructuredArrowtoOver_small (L : A ⥤ T) (R : B ⥤ T) [Final R]
    [∀ b : B, Final (CostructuredArrow.toOver L (R.obj b))] : Final L := by
  rw [final_iff_isIso_colimit_pre]
  intro G
  have : ∀ (b : B), Final ((whiskerLeft R (functorPre L (𝟭 T))).app b) := fun b =>
    inferInstanceAs (Final (CostructuredArrow.toOver L (R.obj b)))
  let i : colimit (L ⋙ G) ≅ colimit G :=
  calc colimit (L ⋙ G) ≅ colimit <| grothendieckProj L ⋙ L ⋙ G :=
          colimitIsoColimitGrothendieck L (L ⋙ G)
    _ ≅ colimit <| Grothendieck.pre (functor L) R ⋙ grothendieckProj L ⋙ L ⋙ G :=
          (Final.colimitIso (Grothendieck.pre (functor L) R) (grothendieckProj L ⋙ L ⋙ G)).symm
    _ ≅ colimit <| Grothendieck.map (whiskerLeft _ (functorPre L (𝟭 T))) ⋙
          grothendieckPrecompFunctorToComma (𝟭 T) R ⋙ Comma.fst (𝟭 T) R ⋙ G :=
            HasColimit.isoOfNatIso (NatIso.ofComponents (fun _ => Iso.refl _))
    _ ≅ colimit <| grothendieckPrecompFunctorToComma (𝟭 T) R ⋙ Comma.fst (𝟭 T) R ⋙ G :=
          Final.colimitIso _ _
    _ ≅ colimit <| Grothendieck.pre (functor (𝟭 T)) R ⋙ grothendieckProj (𝟭 T) ⋙ G :=
          HasColimit.isoOfNatIso (Iso.refl _)
    _ ≅ colimit <| grothendieckProj (𝟭 T) ⋙ G :=
          Final.colimitIso _ _
    _ ≅ colimit G := (colimitIsoColimitGrothendieck (𝟭 T) G).symm
  convert (Iso.isIso_hom i)
  simp only [Iso.instTransIso_trans, comp_obj, grothendieckProj_obj, Grothendieck.pre_obj_base,
    Grothendieck.pre_obj_fiber, Iso.trans_assoc, Iso.trans_hom, Iso.symm_hom, i]
  rw [← Iso.inv_comp_eq, Iso.eq_inv_comp]
  apply colimit.hom_ext (fun _ => by simp)

end Small

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₁} [Category.{v₂} B]
variable {T : Type u₁} [Category.{v₃} T]

/-- A functor `L : A ⥤ T` is final if there is a final functor `R : B ⥤ T` such that for all
`b : B`, the canonical functor `CostructuredArrow L (R.obj b) ⥤ Over (R.obj b)` is final. -/
private lemma final_of_final_CostructuredArrowtoOver (L : A ⥤ T) (R : B ⥤ T) [Final R]
    [hB : ∀ b : B, Final (CostructuredArrow.toOver L (R.obj b))] : Final L := by
  let sA : A ≌ AsSmall.{max u₁ u₂ u₃ v₁ v₂ v₃} A := AsSmall.equiv
  let sB : B ≌ AsSmall.{max u₁ u₂ u₃ v₁ v₂ v₃} B := AsSmall.equiv
  let sT : T ≌ AsSmall.{max u₁ u₂ u₃ v₁ v₂ v₃} T := AsSmall.equiv
  let L' := sA.inverse ⋙ L ⋙ sT.functor
  let R' := sB.inverse ⋙ R ⋙ sT.functor
  have : ∀ (b : AsSmall B), (CostructuredArrow.toOver L' (R'.obj b)).Final := fun b => by
    dsimp only [L', R', CostructuredArrow.toOver] at hB ⊢
    let x := (sB.inverse ⋙ R ⋙ sT.functor).obj b
    let F := pre sA.inverse (L ⋙ sT.functor) x ⋙ pre L _ x ⋙ pre sT.functor (𝟭 _) x
    have : (pre sT.functor (𝟭 _) x).IsEquivalence := Comma.isEquivalence_preLeft _ _ _
    have : (pre L (𝟭 T) (AsSmall.down.obj x)).Final := hB _
    have : (pre L sT.functor x).Final := by
      apply final_of_natIso (F := map₂ (S := L ⋙ sT.functor)  (F := 𝟭 _) (G := sT.inverse)
        (whiskerLeft L sT.unitIso.hom) (𝟙 _) ⋙ pre L (𝟭 T) (AsSmall.down.obj x) ⋙
        map₂ (F := 𝟭 _) (G := sT.functor) (𝟙 _) (𝟙 _))
      apply NatIso.ofComponents (fun x => by {
        apply eqToIso
        rcases x
        simp [pre, Comma.preLeft, map, map₂, Comma.map]
        congr
        simp
        change _ ≫ eqToHom (by { simp [sT, AsSmall.down, AsSmall.up]; congr }) = _
        apply eq_of_heq
        simp })
    apply final_of_natIso (F := F) (Iso.refl _)
  have := final_of_final_CostructuredArrowtoOver_small L' R'
  apply final_of_natIso (F := (sA.functor ⋙ L' ⋙ sT.inverse))
  exact (sA.functor.associator (sA.inverse ⋙ L ⋙ sT.functor) sT.inverse).symm ≪≫
    ((sA.functor.associator sA.inverse (L ⋙ sT.functor)).symm ≪≫
      isoWhiskerRight sA.unitIso.symm _ ≪≫ (L ⋙ sT.functor).leftUnitor).compInverseIso

end Functor

end CategoryTheory
