/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.SmallObject.Iteration.Basic
import Mathlib.CategoryTheory.SmallObject.Iteration.ExtendToSucc
import Mathlib.CategoryTheory.SmallObject.Iteration.FunctorOfCocone

/-!
# Existence of the iteration of a successor structure

Given `Φ : SuccStruct C`, we show by transfinite induction
that for any element `j` in a well ordered set `J`,
the type `Φ.Iteration j` is nonempty.

-/

universe u

namespace CategoryTheory

namespace SmallObject

namespace SuccStruct

open Category Limits

variable {C : Type*} [Category C] (Φ : SuccStruct C)
  {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  [HasIterationOfShape C J]

namespace Iteration

variable (J) in
/-- The obvious term in `Iteration ε ⊥`: it is given by the identity functor. -/
def mkOfBot : Φ.Iteration (⊥ : J) where
  F := (Functor.const _).obj Φ.X₀
  obj_bot := rfl
  obj_succ _ h := by simp at h
  map_succ  _ h := by simp at h
  obj_limit x hx h := (hx.not_isMin (by simpa using h)).elim
  map_eq_ι _ _ h₁ _ h₂ := by
    obtain rfl := le_bot_iff.1 h₁
    simp at h₂

variable {Φ}

open Functor in
/-- When `j : J` is not maximal, this is the extension as `Φ.Iteration (Order.succ j)`
of any `iter : Φ.Iteration j`. -/
noncomputable def mkOfSucc {j : J} (hj : ¬IsMax j) (iter : Φ.Iteration j) :
    Φ.Iteration (Order.succ j) where
  F := extendToSucc hj iter.F (Φ.toSucc _)
  obj_bot := by rw [extendToSucc_obj_eq _ _ _ ⟨⊥, bot_le⟩, obj_bot]
  obj_succ i hi₁ := by
    have hi₂ := (Order.lt_succ_iff_of_not_isMax hj).1 hi₁
    rw [extendToSucc_obj_eq _ _ _ ⟨i, hi₂⟩]
    by_cases hi₃ : i < j
    · rw [extendToSucc_obj_eq _ _ _ ⟨Order.succ i, Order.succ_le_of_lt hi₃⟩, obj_succ _ _ hi₃]
    · obtain rfl : i = j := le_antisymm hi₂ (by simpa using hi₃)
      rw [extendToSucc_obj_succ_eq]
  map_succ i hi₁ := by
    rw [Order.lt_succ_iff_of_not_isMax hj] at hi₁
    by_cases hi₂ : i < j
    · simp [extendToSucc_map _ _ _ _ _ _ (Order.succ_le_of_lt hi₂), map_succ _ _ hi₂,
        extendToSuccObjIso, extendToSucc.objIso,
        Φ.congr_toSucc (extendToSucc_obj_eq hj iter.F (Φ.toSucc _) ⟨i, hi₂.le⟩)]
    · obtain rfl : j = i := le_antisymm (by simpa using hi₂) hi₁
      simp [extendToSucc_map_le_succ,
        Φ.congr_toSucc (extendToSucc_obj_eq hj iter.F (Φ.toSucc _) ⟨j, by simp⟩),
        extendToSuccObjIso, extendToSucc.objIso,
        extendToSuccObjSuccIso, extendToSucc.objSuccIso]
  obj_limit i hi hij := by
    rw [Order.IsSuccLimit.le_succ_iff hi] at hij
    rw [extendToSucc_obj_eq hj iter.F (Φ.toSucc _) ⟨i, hij⟩, obj_limit _ _ hi]
    congr 1
    fapply Functor.ext
    · rintro ⟨k, hk⟩
      exact (extendToSucc_obj_eq hj iter.F (Φ.toSucc _) ⟨k, _⟩).symm
    · rintro ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩ f
      simp [extendToSucc_map _ _ _ k₁ k₂ (leOfHom f) (hk₂.le.trans hij),
        extendToSuccObjIso, extendToSucc.objIso,
        extendToSuccObjSuccIso, extendToSucc.objSuccIso]
  map_eq_ι i hi hij k hk := by
    have hij' := (Order.IsSuccLimit.le_succ_iff hi).1 hij
    have : restrictionLT iter.F hij' =
        restrictionLT (extendToSucc hj iter.F (Φ.toSucc _)) hij := by
      fapply Functor.ext
      · rintro ⟨l, hl⟩
        exact (extendToSucc_obj_eq hj iter.F (Φ.toSucc _) ⟨l, _⟩).symm
      · rintro ⟨l₁, hl₁⟩ ⟨l₂, hl₂⟩ f
        simp [extendToSucc_map _ _ _ l₁ l₂ (leOfHom f) (hl₂.le.trans hij'),
          extendToSuccObjIso, extendToSucc.objIso]
    simp [extendToSucc_map _ _ _ _ _ _ hij', map_eq_ι _ i hi _ _ hk,
      congr_colimit_ι this hi, extendToSuccObjIso, extendToSucc.objIso]

lemma congr_obj {j₁ j₂ : J} (iter₁ : Φ.Iteration j₁) (iter₂ : Φ.Iteration j₂)
    (k : J) (h₁ : k ≤ j₁) (h₂ : k ≤ j₂) :
    iter₁.F.obj ⟨k, h₁⟩ = iter₂.F.obj ⟨k, h₂⟩ := by
  wlog h : j₁ ≤ j₂ generalizing j₁ j₂
  · exact (this iter₂ iter₁ h₂ h₁ (le_of_lt (by simpa using h))).symm
  rw [Subsingleton.elim iter₁ (iter₂.trunc h)]
  dsimp

lemma congr_map {j₁ j₂ : J} (iter₁ : Φ.Iteration j₁) (iter₂ : Φ.Iteration j₂)
    {k₁ k₂ : J} (h : k₁ ≤ k₂) (h₁ : k₂ ≤ j₁) (h₂ : k₂ ≤ j₂) :
    iter₁.F.map (homOfLE h : ⟨k₁, h.trans h₁⟩ ⟶ ⟨k₂, h₁⟩) =
      eqToHom (congr_obj iter₁ iter₂ k₁ (h.trans h₁) (h.trans h₂)) ≫
        iter₂.F.map (homOfLE h) ≫
        eqToHom (congr_obj iter₁ iter₂ k₂ h₁ h₂).symm := by
  wlog hj : j₁ ≤ j₂ generalizing j₁ j₂
  · simp [this iter₂ iter₁ h₂ h₁ ((not_le.1 hj).le)]
  exact Functor.congr_hom (congr_arg F (Subsingleton.elim iter₁ (iter₂.trunc hj)))
    (homOfLE h : ⟨k₁, _⟩ ⟶ ⟨k₂, _⟩)

/-- Given `iter₁ : Φ.Iteration j₁` and `iter₂ : Φ.Iteration j₂`, with `j₁ ≤ j₂`,
if `k₁ ≤ k₂` are elements such that `k₁ ≤ j₁` and `k₂ ≤ k₂`, then this
is the canonical map `iter₁.F.obj ⟨k₁, h₁⟩ ⟶ iter₂.F.obj ⟨k₂, h₂⟩`. -/
def mapObj {j₁ j₂ : J} (iter₁ : Φ.Iteration j₁) (iter₂ : Φ.Iteration j₂)
    {k₁ k₂ : J} (h₁₂ : k₁ ≤ k₂) (h₁ : k₁ ≤ j₁) (h₂ : k₂ ≤ j₂) (hj : j₁ ≤ j₂) :
    iter₁.F.obj ⟨k₁, h₁⟩ ⟶ iter₂.F.obj ⟨k₂, h₂⟩ :=
  eqToHom (congr_obj iter₁ iter₂ k₁ h₁ (h₁.trans hj)) ≫
    iter₂.F.map (homOfLE h₁₂)

lemma arrow_mk_mapObj {j₁ j₂ : J} (iter₁ : Φ.Iteration j₁) (iter₂ : Φ.Iteration j₂)
    {k₁ k₂ : J} (h₁₂ : k₁ ≤ k₂) (h₁ : k₁ ≤ j₁) (h₂ : k₂ ≤ j₂) (hj : j₁ ≤ j₂) :
    Arrow.mk (mapObj iter₁ iter₂ h₁₂ h₁ h₂ hj) =
      Arrow.mk (iter₂.F.map (homOfLE h₁₂ : ⟨k₁, h₁.trans hj⟩ ⟶ ⟨k₂, h₂⟩)) :=
  Arrow.ext (congr_obj iter₁ iter₂ k₁ h₁ (h₁.trans hj)) rfl (by simp [mapObj])

@[simp]
lemma mapObj_refl {j : J} (iter : Φ.Iteration j)
    {k l : J} (h : k ≤ l) (h' : l ≤ j) :
    mapObj iter iter h (h.trans h') h' (by rfl) = iter.F.map (homOfLE h) := by
  simp [mapObj]

@[reassoc (attr := simp)]
lemma mapObj_trans {j₁ j₂ j₃ : J} (iter₁ : Φ.Iteration j₁) (iter₂ : Φ.Iteration j₂)
    (iter₃ : Φ.Iteration j₃) {k₁ k₂ k₃ : J} (h₁₂ : k₁ ≤ k₂) (h₂₃ : k₂ ≤ k₃)
    (h₁ : k₁ ≤ j₁) (h₂ : k₂ ≤ j₂) (h₃ : k₃ ≤ j₃) (h₁₂' : j₁ ≤ j₂) (h₂₃' : j₂ ≤ j₃) :
    mapObj iter₁ iter₂ h₁₂ h₁ h₂ h₁₂' ≫ mapObj iter₂ iter₃ h₂₃ h₂ h₃ h₂₃' =
      mapObj iter₁ iter₃ (h₁₂.trans h₂₃) h₁ h₃ (h₁₂'.trans h₂₃') := by
  simp [mapObj, congr_map iter₂ iter₃ h₁₂ h₂ (h₂.trans h₂₃'), ← Functor.map_comp]

namespace mkOfLimit

open Functor

variable {j : J} (hj : Order.IsSuccLimit j) (iter : ∀ (i : J), i < j → Φ.Iteration i)

/-- Assuming `j : J` is a limit element and that we have `∀ (i : J), i < j → Φ.Iteration i`,
this is the inductive system `Set.Iio j ⥤ C` which sends `⟨i, _⟩` to
`(iter i _).F.obj ⟨i, _⟩`. -/
@[simps]
noncomputable def inductiveSystem : Set.Iio j ⥤ C where
  obj i := (iter i.1 i.2).F.obj ⟨i.1, by simp⟩
  map {i₁ i₂} f := mapObj (iter i₁.1 i₁.2) (iter i₂.1 i₂.2) (leOfHom f)
    (by simp) (by simp) (leOfHom f)

/-- The extension of `inductiveSystem iter` to a functor `Set.Iic j ⥤ C` which
sends the top element to the colimit of `inductiveSystem iter`. -/
noncomputable def functor : Set.Iic j ⥤ C :=
  letI := hasColimitsOfShape_of_isSuccLimit C j hj
  ofCocone (colimit.cocone (inductiveSystem iter))

lemma functor_obj (i : J) (hi : i < j) {k : J} (iter' : Φ.Iteration k) (hk : i ≤ k) :
    (functor hj iter).obj ⟨i, hi.le⟩ = iter'.F.obj ⟨i, hk⟩ := by
  dsimp only [functor]
  rw [ofCocone_obj_eq _ _ hi]
  apply congr_obj

lemma functor_obj_eq_colimit :
    letI := hasColimitsOfShape_of_isSuccLimit C j hj
    (functor hj iter).obj ⟨j, by simp⟩ = colimit (inductiveSystem iter) := by
  apply ofCocone_obj_eq_pt

lemma functor_map {i₁ i₂ : J} (h₁₂ : i₁ ≤ i₂) (hi₂ : i₂ < j)
    {k : J} (iter' : Φ.Iteration k) (hk : i₂ ≤ k) :
    (functor hj iter).map (homOfLE h₁₂ : ⟨i₁, h₁₂.trans hi₂.le⟩ ⟶ ⟨i₂, hi₂.le⟩) =
      eqToHom (functor_obj hj iter i₁ (lt_of_le_of_lt h₁₂ hi₂) iter' (h₁₂.trans hk)) ≫
        iter'.F.map (homOfLE h₁₂) ≫
        eqToHom (functor_obj hj iter i₂ hi₂ iter' hk).symm := by
  simp [functor, ofCocone_map _ _ _ _ hi₂, congr_map (iter i₂ hi₂) iter' _ _ hk,
    ofCoconeObjIso, ofCocone.objIso, mapObj]

lemma restrictionLT_functor_of_lt {i : J} (hij : i < j) {k : J} (iter' : Φ.Iteration k)
    (hk : i ≤ k) :
    restrictionLT (functor hj iter) hij.le = restrictionLT iter'.F hk := by
  fapply Functor.ext
  · rintro ⟨l, hl⟩
    exact functor_obj hj _ _ (hl.trans hij) iter' _
  · rintro ⟨l₁, h₁⟩ ⟨l₂, h₂⟩ f
    exact functor_map hj _ _ (h₂.trans hij) _ _

lemma restrictionLT_functor :
    restrictionLT (functor hj iter) (le_refl j) = inductiveSystem iter := by
  fapply Functor.ext
  · rintro ⟨l, hl⟩
    exact functor_obj hj _ _ hl _ _
  · rintro ⟨l₁, h₁⟩ ⟨l₂, h₂⟩ f
    simp [functor_map _ _ _ h₂ (iter l₂ h₂) (by rfl), mapObj]

lemma functor_map_to_top (i : J) (hij : i < j) :
    letI := hasColimitsOfShape_of_isSuccLimit C j hj
    (functor hj iter).map (homOfLE hij.le : ⟨i, hij.le⟩ ⟶ ⟨j, by simp⟩) =
      eqToHom (functor_obj _ _ _ hij _ _) ≫ colimit.ι (inductiveSystem iter) ⟨i, hij⟩ ≫
          eqToHom (functor_obj_eq_colimit hj iter).symm := by
  simp [functor, ofCocone_map_to_top _ _ hij, ofCoconeObjIso, ofCocone.objIso,
    ofCoconeObjIsoPt, ofCocone.objIsoPt]

end mkOfLimit

open mkOfLimit in
/-- When `j` is a limit element, this is the element in `Φ.Iteration j`
that is constructed from elements in `Φ.Iteration i` for all `i < j`. -/
noncomputable def mkOfLimit {j : J} (hj : Order.IsSuccLimit j)
    (iter : ∀ (i : J), i < j → Φ.Iteration i) :
    Φ.Iteration j where
  F := functor hj iter
  obj_bot := functor_obj hj iter ⊥ (Order.IsSuccLimit.bot_lt hj) (mkOfBot Φ J) (by rfl)
  obj_succ i hi₁ := by
    have hi₂ := (Order.IsSuccLimit.succ_lt_iff hj).2 hi₁
    rw [functor_obj hj iter (Order.succ i) hi₂ (iter (Order.succ i) hi₂) (by rfl),
      functor_obj hj iter i hi₁ (iter (Order.succ i) hi₂) (Order.le_succ i),
      obj_succ _ _ (Order.lt_succ_of_le_of_not_isMax (by rfl) (not_isMax_of_lt hi₁))]
  map_succ i hi₁ := by
    have hi₂ := (Order.IsSuccLimit.succ_lt_iff hj).2 hi₁
    simp [functor_map hj iter (Order.le_succ i) hi₂ (iter _ hi₂) (by rfl),
      map_succ _ _ (Order.lt_succ_of_le_of_not_isMax (by rfl) (not_isMax_of_lt hi₁)),
      Φ.congr_toSucc (functor_obj hj iter i hi₁ (iter _ hi₂) (Order.le_succ i))]
  obj_limit i hi hij := by
    obtain hij | rfl := hij.lt_or_eq
    · rw [functor_obj hj iter i hij (iter _ hij) (by rfl), obj_limit _ i hi,
        restrictionLT_functor_of_lt hj iter hij (iter i hij) (by rfl)]
    · rw [functor_obj_eq_colimit, restrictionLT_functor]
  map_eq_ι i hi hij := by
    obtain hij | rfl := hij.lt_or_eq
    · intro k hk
      simp [functor_map hj iter _ hij (iter i hij) (by rfl),
        map_eq_ι _ _ hi _ _ hk,
        congr_colimit_ι (restrictionLT_functor_of_lt hj iter hij (iter i hij) (by rfl)) hi]
    · intro k hk
      simp [functor_map_to_top _ _ _ hk,
        congr_colimit_ι (restrictionLT_functor hj iter) hi ⟨k, hk⟩]

variable (Φ)

instance nonempty (j : J) : Nonempty (Φ.Iteration j) := by
  induction j using SuccOrder.limitRecOn with
  | hm i hi =>
      obtain rfl : i = ⊥ := by simpa using hi
      exact ⟨mkOfBot Φ J⟩
  | hs i hi hi' => exact ⟨mkOfSucc hi hi'.some⟩
  | hl i hi hi' => exact ⟨mkOfLimit hi (fun a ha ↦ (hi' a ha).some)⟩

end Iteration

end SuccStruct

end SmallObject

end CategoryTheory
