/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Order.InitialSeg
import Mathlib.Order.SuccPred.Limit
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.IsLimit

/-!
# Cocones associated to principal segments

-/

open CategoryTheory Category Limits

/-- `Set.Iic j` is an initial segment. -/
@[simps]
def Set.initialSegIic {α : Type*} [Preorder α] (j : α) :
    Set.Iic j ≤i α where
  toFun := fun ⟨j, hj⟩ ↦ j
  inj' _ _ _ := by aesop
  map_rel_iff' := by aesop
  mem_range_of_rel' x k h := by simpa using h.le.trans x.2

/-- `Set.Iio j` is a principal segment. -/
@[simps]
def Set.principalSegIio {α : Type*} [Preorder α] (j : α) :
    Set.Iio j <i α where
  top := j
  toFun := fun ⟨j, hj⟩ ↦ j
  inj' _ _ _ := by aesop
  map_rel_iff' := by aesop
  mem_range_iff_rel' := by aesop

variable {α α' β : Type*} [PartialOrder α] [PartialOrder α'] [PartialOrder β]

/-- If `f : α <i β` is a principal segment, this is the induced order
isomorphism `α ≃o Set.Iio f.top`. -/
@[simps! apply_coe]
noncomputable def PrincipalSeg.orderIsoIio (f : α <i β) :
    α ≃o Set.Iio f.top where
  toEquiv := Equiv.ofBijective (f := fun a ↦ ⟨f a, f.lt_top a⟩) (by
    constructor
    · intro x y hxy
      exact f.injective (by simpa using hxy)
    · rintro ⟨z, hz⟩
      obtain ⟨x, hx⟩ := f.mem_range_of_rel_top hz
      exact ⟨x, by simpa using hx⟩)
  map_rel_iff' := by simp

variable {C : Type*} [Category C]

/-- When `f : α <i β` and a functor `F : β ⥤ C`, this is the cocone
for `f.monotone.functor ⋙ F : α ⥤ C` whose point if `F.obj f.top`. -/
@[simps]
def PrincipalSeg.cocone (f : α <i β) (F : β ⥤ C) :
    Cocone (f.monotone.functor ⋙ F) where
  pt := F.obj f.top
  ι :=
    { app i := F.map (homOfLE (f.lt_top i).le)
      naturality i j f := by
        dsimp
        rw [← F.map_comp, comp_id]
        rfl }

/-- If `f : α <i β` is a principal segment and `F : β ⥤ C`, then `f.cocone F`
is colimit if `(Set.principalSegIio f.top).cocone F` is. -/
noncomputable def PrincipalSeg.coconeIsColimitOfIsColimit (f : α <i β) (F : β ⥤ C)
    (h : IsColimit ((Set.principalSegIio f.top).cocone F)) :
    IsColimit (f.cocone F) :=
  h.whiskerEquivalence f.orderIsoIio.equivalence

@[simp]
lemma InitialSeg.covBy_iff (f : α ≤i β) (a b : α) : f a ⋖ f b ↔ a ⋖ b := by
  constructor
  · exact fun hab ↦ ⟨by simpa using hab.1, fun c ↦ by simpa using @hab.2 (f c)⟩
  · intro hab
    refine ⟨by simpa using hab.1, fun c hac hbc ↦ ?_⟩
    obtain ⟨c, rfl⟩ := f.mem_range_of_rel hbc
    exact @hab.2 c (by simpa using hac) (by simpa using hbc)

@[simp]
lemma InitialSeg.isSuccPrelimit_iff (f : α ≤i β) (a : α) :
    Order.IsSuccPrelimit (f a) ↔ Order.IsSuccPrelimit a := by
  constructor
  · exact fun ha b hb ↦ ha (f b) (by simpa using hb)
  · intro ha b hb
    obtain ⟨b, rfl⟩ := f.mem_range_of_rel hb.1
    simp only [covBy_iff] at hb
    exact ha b hb

@[simp]
lemma InitialSeg.isSuccLimit_iff (f : α ≤i β) (a : α) :
    Order.IsSuccLimit (f a) ↔ Order.IsSuccLimit a := by
  simp [Order.IsSuccLimit]
