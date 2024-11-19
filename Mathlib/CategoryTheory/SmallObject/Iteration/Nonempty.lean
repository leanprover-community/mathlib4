/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.SmallObject.Iteration.ExtendToSucc
import Mathlib.CategoryTheory.SmallObject.Iteration.FunctorOfCocone
import Mathlib.CategoryTheory.SmallObject.Iteration.UniqueHom

/-!
# Existence of objects in the category of iterations of functors

Given a functor `Φ : C ⥤ C` and a natural transformation `ε : 𝟭 C ⟶ Φ`,
we shall show in this file that for any well ordered set `J`,
and `j : J`, the category `Functor.Iteration ε j` is nonempty.
As we already know from the main result in `SmallObject.Iteration.UniqueHom`
that such objects, if they exists, are unique up to a unique isomorphism,
we shall show the existence of a term in `Functor.Iteration ε j` by
transfinite induction.

-/

universe u

namespace CategoryTheory

open Category Limits

variable {C : Type*} [Category C] {Φ : C ⥤ C} {ε : 𝟭 C ⟶ Φ}
  {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J]

namespace Functor

namespace Iteration

variable (ε J) in
/-- The obvious term in `Iteration ε ⊥`: it is given by the identity functor. -/
def mkOfBot : Iteration ε (⊥ : J) where
  F := (Functor.const _).obj (𝟭 C)
  isoZero := Iso.refl _
  isoSucc _ h := by simp at h
  mapSucc'_eq _ h := by simp at h
  isColimit x hx h := by
    exfalso
    refine hx.not_isMin (by simpa using h)

/-- When `j : J` is not maximal, this is the extension as `Iteration ε (Order.succ j)`
of any `iter : Iteration ε j`. -/
noncomputable def mkOfSucc {j : J} (hj : ¬IsMax j) (iter : Iteration ε j) :
    Iteration ε (Order.succ j) where
  F := extendToSucc hj iter.F (whiskerLeft _ ε)
  isoZero := (extendToSuccObjIso hj iter.F (whiskerLeft _ ε) ⟨⊥, by simp⟩).trans iter.isoZero
  isoSucc i hi :=
    if hij : i < j then
      extendToSuccObjIso _ _ _ ⟨Order.succ i, Order.succ_le_of_lt hij⟩ ≪≫
        iter.isoSucc i hij ≪≫ (isoWhiskerRight (extendToSuccObjIso _ _ _ ⟨i, hij.le⟩).symm _)
    else
      have hij' : i = j := le_antisymm
        (by simpa only [Order.lt_succ_iff_of_not_isMax hj] using hi) (by simpa using hij)
      eqToIso (by subst hij'; rfl) ≪≫ extendToSuccObjSuccIso hj iter.F (whiskerLeft _ ε) ≪≫
        isoWhiskerRight ((extendToSuccObjIso hj iter.F (whiskerLeft _ ε) ⟨j, by simp⟩).symm.trans
            (eqToIso (by subst hij'; rfl))) _
  mapSucc'_eq i hi := by
    obtain hi' | rfl := ((Order.lt_succ_iff_of_not_isMax hj).mp hi).lt_or_eq
    · ext X
      have := iter.mapSucc_eq i hi'
      dsimp [mapSucc, mapSucc'] at this ⊢
      rw [extentToSucc_map _ _ _ _ _ _ (Order.succ_le_of_lt hi'), this, dif_pos hi']
      dsimp
      rw [assoc, assoc]
      erw [ε.naturality_assoc]
    · ext X
      dsimp [mapSucc']
      rw [dif_neg (gt_irrefl i), extendToSucc_map_le_succ]
      dsimp
      rw [id_comp, comp_id]
      erw [ε.naturality_assoc]
  isColimit i hi hij := by
    have hij' : i ≤ j := by
      obtain hij | rfl := hij.lt_or_eq
      · exact (Order.lt_succ_iff_of_not_isMax hj).1 hij
      · exfalso
        exact Order.not_isSuccLimit_succ_of_not_isMax hj hi
    refine (IsColimit.precomposeHomEquiv
      (isoWhiskerLeft (monotone_inclusion_lt_le_of_le hij').functor
        (extendToSuccRestrictionLEIso hj iter.F (whiskerLeft _ ε))).symm _).1
      (IsColimit.ofIsoColimit (iter.isColimit i hi hij')
      (Iso.symm (Cocones.ext (extendToSuccObjIso hj iter.F (whiskerLeft _ ε) ⟨i, hij'⟩)
      (fun ⟨k, hk⟩ ↦ ?_))))
    dsimp
    rw [assoc, extendToSuccObjIso_hom_naturality hj iter.F (whiskerLeft _ ε)]
    dsimp
    rw [Iso.inv_hom_id_assoc]

section

variable [WellFoundedLT J] {j : J} (hj : Order.IsSuccLimit j)
  (iter : ∀ (i : J) (_ : i < j), Iteration ε i)

namespace mkOfLimit

abbrev obj (i : J) (hi : i < j) : C ⥤ C := (iter i hi).F.obj ⟨i, by simp⟩

noncomputable def map (i₁ i₂ : J) (hi : i₁ ≤ i₂) (hi₂ : i₂ < j) :
    obj iter i₁ (lt_of_le_of_lt hi hi₂) ⟶ obj iter i₂ hi₂ :=
  ((iter i₁ (lt_of_le_of_lt hi hi₂)).iso ((iter i₂ hi₂).trunc hi)).hom.natTrans.app
    ⟨i₁, by simp⟩ ≫ (iter i₂ hi₂).F.map (homOfLE hi)

@[simp]
lemma map_id (i : J) (hi : i < j) :
    map iter i i (by rfl) hi = 𝟙 _ := by
  simp [map]

lemma map_comp (i₁ i₂ i₃ : J) (hi : i₁ ≤ i₂) (hi' : i₂ ≤ i₃) (hi₃ : i₃ < j) :
    map iter i₁ i₃ (hi.trans hi') hi₃ =
      map iter i₁ i₂ hi (lt_of_le_of_lt hi' hi₃) ≫
        map iter i₂ i₃ hi' hi₃ := by
  dsimp [map]
  rw [assoc, NatTrans.naturality_assoc]
  dsimp
  rw [← truncFunctor_map_natTrans_app _ hi i₁ (by rfl), truncFunctor_map_iso_hom,
    ← NatTrans.comp_app_assoc, ← natTrans_comp, ← Functor.map_comp]
  dsimp only [truncFunctor_obj, trunc_trunc]
  rw [iso_hom_comp_iso_hom, homOfLE_comp]

@[simps]
noncomputable def functor : Set.Iio j ⥤ C ⥤ C where
  obj i := obj iter i.1 i.2
  map f := map iter _ _ (leOfHom f) _
  map_id _ := map_id iter _ _
  map_comp _ _ := map_comp iter _ _ _ _ _ _

end mkOfLimit

section

open mkOfLimit

variable [HasColimit (functor iter)]

include hj iter in
noncomputable def mkOfLimit :
    Iteration ε j where
  F := Functor.ofCocone (colimit.cocone (functor iter))
  isoZero := by
    have := hj
    sorry
  isoSucc := sorry
  mapSucc'_eq := sorry
  isColimit := sorry

end
end

instance [WellFoundedLT J] [HasIterationOfShape C J] (j : J) : Nonempty (Iteration ε j) := by
  induction j using SuccOrder.limitRecOn with
  | hm i hi =>
      obtain rfl : i = ⊥ := by simpa using hi
      exact ⟨mkOfBot ε J⟩
  | hs i hi hi' => exact ⟨mkOfSucc hi hi'.some⟩
  | hl i hi hi' =>
      have := hasColimitOfShape_of_isSuccLimit C i hi
      exact ⟨mkOfLimit hi (fun a ha ↦ (hi' a ha).some)⟩

end Iteration

end Functor

end CategoryTheory
