/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.IsLimit
import Mathlib.CategoryTheory.Limits.Shapes.Preorder.PrincipalSeg
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Fin.SuccPredOrder
import Mathlib.Order.Interval.Set.InitialSeg
import Mathlib.Order.Interval.Set.Limit
import Mathlib.Order.SuccPred.InitialSeg
import Mathlib.Order.SuccPred.Limit
import Mathlib.Order.SuccPred.LinearLocallyFinite

/-!
# Continuity of functors from well-ordered types

Let `F : J ⥤ C` be functor from a well-ordered type `J`.
We introduce the typeclass `F.IsWellOrderContinuous`
to say that if `m` is a limit element, then `F.obj m`
is the colimit of the `F.obj j` for `j < m`.

-/

universe w w' v u

namespace CategoryTheory.Functor

open Category Limits

variable {C : Type u} [Category.{v} C] {J : Type w} [PartialOrder J]

/-- A functor `F : J ⥤ C` is well-order-continuous if for any limit element `m : J`,
`F.obj m` identifies to the colimit of the `F.obj j` for `j < m`. -/
class IsWellOrderContinuous (F : J ⥤ C) : Prop where
  nonempty_isColimit (m : J) (hm : Order.IsSuccLimit m) :
    Nonempty (IsColimit ((Set.principalSegIio m).cocone F))

/-- If `F : J ⥤ C` is well-order-continuous and `m : J` is a limit element, then
`F.obj m` identifies to the colimit of the `F.obj j` for `j < m`. -/
noncomputable def isColimitOfIsWellOrderContinuous (F : J ⥤ C) [F.IsWellOrderContinuous]
    (m : J) (hm : Order.IsSuccLimit m) :
    IsColimit ((Set.principalSegIio m).cocone F) :=
      (IsWellOrderContinuous.nonempty_isColimit m hm).some

/-- If `F : J ⥤ C` is well-order-continuous and `h : α <i J` is a principal
segment such that `h.top` is a limit element, then
`F.obj h.top` identifies to the colimit of the `F.obj j` for `j : α`. -/
noncomputable def isColimitOfIsWellOrderContinuous' (F : J ⥤ C) [F.IsWellOrderContinuous]
    {α : Type*} [PartialOrder α] (f : α <i J) (hα : Order.IsSuccLimit f.top) :
    IsColimit (f.cocone F) :=
  (F.isColimitOfIsWellOrderContinuous f.top hα).whiskerEquivalence
    f.orderIsoIio.equivalence

instance (F : ℕ ⥤ C) : F.IsWellOrderContinuous where
  nonempty_isColimit m hm := by simp at hm

instance {n : ℕ} (F : Fin n ⥤ C) : F.IsWellOrderContinuous where
  nonempty_isColimit _ hj := (Order.not_isSuccLimit hj).elim

lemma isWellOrderContinuous_of_iso {F G : J ⥤ C} (e : F ≅ G) [F.IsWellOrderContinuous] :
    G.IsWellOrderContinuous where
  nonempty_isColimit (m : J) (hm : Order.IsSuccLimit m) :=
    ⟨(IsColimit.precomposeHomEquiv (isoWhiskerLeft _ e) _).1
      (IsColimit.ofIsoColimit (F.isColimitOfIsWellOrderContinuous m hm)
        (Cocones.ext (e.app _)))⟩

instance (F : J ⥤ C) {J' : Type w'} [PartialOrder J'] (f : J' ≤i J)
    [F.IsWellOrderContinuous] :
    (f.monotone.functor ⋙ F).IsWellOrderContinuous where
  nonempty_isColimit m' hm' := ⟨F.isColimitOfIsWellOrderContinuous'
    ((Set.principalSegIio m').transInitial f) (by simpa)⟩

instance (F : J ⥤ C) {J' : Type w'} [PartialOrder J'] (e : J' ≃o J)
    [F.IsWellOrderContinuous] :
    (e.equivalence.functor ⋙ F).IsWellOrderContinuous :=
  inferInstanceAs (e.toInitialSeg.monotone.functor ⋙ F).IsWellOrderContinuous

instance IsWellOrderContinuous.restriction_setIci
    {J : Type w} [LinearOrder J]
    {F : J ⥤ C} [F.IsWellOrderContinuous] (j : J) :
    ((Subtype.mono_coe (Set.Ici j)).functor ⋙ F).IsWellOrderContinuous where
  nonempty_isColimit m hm := ⟨by
    let f : Set.Iio m → Set.Iio m.1 := fun ⟨⟨a, ha⟩, ha'⟩ ↦ ⟨a, ha'⟩
    have hf : Monotone f := fun _ _ h ↦ h
    have : hf.functor.Final := by
      rw [Monotone.final_functor_iff]
      rintro ⟨j', hj'⟩
      simp only [Set.mem_Iio] at hj'
      dsimp only [f]
      by_cases h : j' ≤ j
      · refine ⟨⟨⟨j, le_refl j⟩, ?_⟩, h⟩
        by_contra!
        simp only [Set.mem_Iio, not_lt] at this
        apply hm.1
        rintro ⟨k, hk⟩ hkm
        exact this.trans hk
      · simp only [not_le] at h
        exact ⟨⟨⟨j', h.le⟩, hj'⟩, by rfl⟩
    exact (Functor.Final.isColimitWhiskerEquiv (F := hf.functor) _).2
      (F.isColimitOfIsWellOrderContinuous m.1 (Set.Ici.isSuccLimit_coe m hm))⟩

end CategoryTheory.Functor
