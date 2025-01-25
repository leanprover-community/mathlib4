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
def Set.initialSegIic {J : Type*} [Preorder J] (j : J) :
    Set.Iic j ≤i J where
  toFun := fun ⟨j, hj⟩ ↦ j
  inj' _ _ _ := by aesop
  map_rel_iff' := by aesop
  mem_range_of_rel' x k h := by simpa using h.le.trans x.2

/-- `Set.Iio j` is a principal segment. -/
@[simps]
def Set.principalSegIio {J : Type*} [Preorder J] (j : J) :
    Set.Iio j <i J where
  top := j
  toFun := fun ⟨j, hj⟩ ↦ j
  inj' _ _ _ := by aesop
  map_rel_iff' := by aesop
  mem_range_iff_rel' := by aesop

@[simps! apply_coe]
noncomputable def PrincipalSeg.orderIsoIio {α β : Type*} [PartialOrder α] [PartialOrder β]
    (h : α <i β) :
    α ≃o Set.Iio h.top where
  toEquiv := Equiv.ofBijective (f := fun a ↦ ⟨h a, h.lt_top a⟩) (by
    constructor
    · intro x y hxy
      exact h.injective (by simpa using hxy)
    · rintro ⟨z, hz⟩
      obtain ⟨x, hx⟩ := h.mem_range_of_rel_top hz
      exact ⟨x, by simpa using hx⟩)
  map_rel_iff' := by simp

variable {α α' β : Type*} [PartialOrder α] [PartialOrder α'] [PartialOrder β]
  {C : Type*} [Category C]

/-- When `h : α <i β` and a functor `F : β ⥤ C`, this is the cocone
for `h.monotone.functor ⋙ F : α ⥤ C` whose point if `F.obj h.top`. -/
@[simps]
def PrincipalSeg.cocone (h : α <i β) (F : β ⥤ C) :
    Cocone (h.monotone.functor ⋙ F) where
  pt := F.obj h.top
  ι :=
    { app i := F.map (homOfLE (h.lt_top i).le)
      naturality i j f := by
        dsimp
        rw [← F.map_comp, comp_id]
        rfl }

/-- If `h : α <i β` is a principal segment and `F : β ⥤ C`, then `h.cocone F`
is colimit if `(Set.principalSegIio h.top).cocone F` is. -/
noncomputable def PrincipalSeg.coconeIsColimitOfIsColimit (h : α <i β) (F : β ⥤ C)
    (htop : IsColimit ((Set.principalSegIio h.top).cocone F)) :
    IsColimit (h.cocone F) :=
  htop.whiskerEquivalence h.orderIsoIio.equivalence

@[simp]
lemma InitialSeg.covBy_iff (h : α ≤i β) (a b : α) : h a ⋖ h b ↔ a ⋖ b := by
  constructor
  · exact fun hab ↦ ⟨by simpa using hab.1, fun c ↦ by simpa using @hab.2 (h c)⟩
  · intro hab
    refine ⟨by simpa using hab.1, fun c hac hbc ↦ ?_⟩
    obtain ⟨c, rfl⟩ := h.mem_range_of_rel hbc
    exact @hab.2 c (by simpa using hac) (by simpa using hbc)

@[simp]
lemma InitialSeg.isSuccPrelimit_iff (h : α ≤i β) (a : α) :
    Order.IsSuccPrelimit (h a) ↔ Order.IsSuccPrelimit a := by
  constructor
  · exact fun ha b hb ↦ ha (h b) (by simpa using hb)
  · intro ha b hb
    obtain ⟨b, rfl⟩ := h.mem_range_of_rel hb.1
    simp only [covBy_iff] at hb
    exact ha b hb

@[simp]
lemma InitialSeg.isSuccLimit_iff (h : α ≤i β) (a : α) :
    Order.IsSuccLimit (h a) ↔ Order.IsSuccLimit a := by
  simp [Order.IsSuccLimit]
