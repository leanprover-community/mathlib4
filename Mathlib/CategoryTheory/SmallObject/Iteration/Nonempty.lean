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
  [HasIterationOfShape J C]

namespace Iteration

variable (J) in
/-- The obvious term in `Φ.Iteration ε ⊥` that is given by `Φ.X₀`. -/
def mkOfBot : Φ.Iteration (⊥ : J) where
  F := (Functor.const _).obj Φ.X₀
  obj_bot := rfl
  arrowSucc_eq _ h := by simp at h
  arrowMap_limit  _ h₁ h₂ := (h₁.not_isMin (by simpa using h₂)).elim

variable {Φ}

open Functor in
/-- When `j : J` is not maximal, this is the extension in `Φ.Iteration (Order.succ j)`
of any `iter : Φ.Iteration j`. -/
noncomputable def mkOfSucc {j : J} (hj : ¬IsMax j) (iter : Φ.Iteration j) :
    Φ.Iteration (Order.succ j) where
  F := extendToSucc hj iter.F (Φ.toSucc _)
  obj_bot := by rw [extendToSucc_obj_eq _ _ _ _ bot_le, obj_bot]
  arrowSucc_eq i hi₁ := by
    rw [Order.lt_succ_iff_of_not_isMax hj] at hi₁
    obtain hi₁ | rfl := hi₁.lt_or_eq
    · rw [arrowSucc_def, arrowMap_extendToSucc _ _ _ _ _ _ (Order.succ_le_of_lt hi₁),
        ← arrowSucc_def _ _ hi₁, iter.arrowSucc_eq i hi₁,
        extendToSucc_obj_eq hj iter.F (Φ.toSucc _) i hi₁.le]
    · rw [arrowSucc_extendToSucc, toSuccArrow,
        extendToSucc_obj_eq hj iter.F (Φ.toSucc _) i]
  arrowMap_limit i hi hij k hk := by
    have hij' := (Order.IsSuccLimit.le_succ_iff hi).1 hij
    rw [arrowMap_extendToSucc _ _ _ _ _ _ hij', arrowMap_limit _ _ hi _ _ hk]
    congr 1
    apply Arrow.functor_ext
    rintro ⟨k₁, h₁⟩ ⟨k₂, h₂⟩ f
    dsimp
    rw [← arrowMap, ← arrowMap, arrowMap_extendToSucc]
    rfl

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

lemma arrowMap_functor (i₁ i₂ : J) (h₁₂ : i₁ ≤ i₂) (h₂ : i₂ < j) :
    arrowMap (functor hj iter) i₁ i₂ h₁₂ h₂.le =
      Arrow.mk (mapObj (iter i₁ (lt_of_le_of_lt h₁₂ h₂)) (iter i₂ h₂) h₁₂
        (by simp) (by simp) h₁₂) :=
  arrowMap_ofCocone _ _ _ _ h₂

lemma arrowMap_functor_to_top (i : J) (hi : i < j) :
    letI := hasColimitsOfShape_of_isSuccLimit C j hj
    arrowMap (functor hj iter) i j hi.le (by simp) =
      Arrow.mk (colimit.ι (inductiveSystem iter) ⟨i, hi⟩) :=
  arrowMap_ofCocone_to_top _ _ _

end mkOfLimit

set_option backward.dsimp.proofs true in
open mkOfLimit in
/-- When `j` is a limit element, this is the element in `Φ.Iteration j`
that is constructed from elements in `Φ.Iteration i` for all `i < j`. -/
noncomputable def mkOfLimit {j : J} (hj : Order.IsSuccLimit j)
    (iter : ∀ (i : J), i < j → Φ.Iteration i) :
    Φ.Iteration j where
  F := functor hj iter
  obj_bot := functor_obj hj iter ⊥ (Order.IsSuccLimit.bot_lt hj) (mkOfBot Φ J) (by rfl)
  arrowSucc_eq i hi := by
    rw [arrowSucc_def, arrowMap_functor _ _ _ _ (Order.le_succ i)
        ((Order.IsSuccLimit.succ_lt_iff hj).2 hi), arrow_mk_mapObj,
      ← arrowSucc_def _ _ ((Order.lt_succ_of_le_of_not_isMax (by rfl) (not_isMax_of_lt hi))),
      arrowSucc_eq, functor_obj _ _ _ hi]
  arrowMap_limit i hi hij k hk := by
    obtain hij | rfl := hij.lt_or_eq
    · rw [arrowMap_functor _ _ _ _ _ hij, arrow_mk_mapObj,
        arrowMap_limit _ _ hi _ _ hk]
      congr 1
      apply Arrow.functor_ext
      rintro ⟨l₁, hl₁⟩ ⟨l₂, hl₂⟩ f
      dsimp
      rw [← arrowMap, ← arrowMap, arrowMap_functor hj iter l₁ l₂ _ (hl₂.trans hij),
        arrow_mk_mapObj]
      apply congr_arrowMap
    · rw [arrowMap_functor_to_top _ _ _ hk, ← arrowι_def _ hi]
      congr 1
      apply Arrow.functor_ext
      rintro ⟨l₁, hl₁⟩ ⟨l₂, hl₂⟩ f
      dsimp
      rw [← arrowMap, arrow_mk_mapObj, arrowMap_functor _ _ _ _ _ hl₂, arrow_mk_mapObj]

variable (Φ)

instance nonempty (j : J) : Nonempty (Φ.Iteration j) := by
  induction j using SuccOrder.limitRecOn with
  | isMin i hi =>
      obtain rfl : i = ⊥ := by simpa using hi
      exact ⟨mkOfBot Φ J⟩
  | succ i hi hi' => exact ⟨mkOfSucc hi hi'.some⟩
  | isSuccLimit i hi hi' => exact ⟨mkOfLimit hi (fun a ha ↦ (hi' a ha).some)⟩

end Iteration

end SuccStruct

end SmallObject

end CategoryTheory
