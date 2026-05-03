/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.CechAddCommGrpCat
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.CategoryTheory.Limits.Preorder

@[expose] public section

open CategoryTheory

namespace TopologicalSpace

open Limits Opposite

universe u

variable {T : Type u} [TopologicalSpace T]

namespace Opens

variable {ι : Type*} [Finite ι] (U : ι → Opens T)

abbrev fan : Fan U :=
  Fan.mk (⟨⋂ i, U i, isOpen_iInter_of_finite (fun i ↦ (U i).isOpen)⟩)
    (fun i ↦ homOfLE (by tauto))

def isLimitFan : IsLimit (fan U) :=
  Preorder.isLimitOfIsGLB _ _
    ⟨Preorder.conePt_mem_lowerBounds _ (fan U), fun V hV v hv ↦ by
      simp only [Fan.mk_pt, mem_mk, Set.mem_iInter, SetLike.mem_coe]
      exact fun i ↦ hV ⟨⟨i⟩, rfl⟩ hv⟩

end Opens

section

variable (F : (Opens T)ᵒᵖ ⥤ AddCommGrpCat.{u}) {ι : Type u} (U : ι → Opens T) (n : ℕ)

abbrev cechFan (i : Fin (n + 1) → ι) : Fan (U ∘ i) := Opens.fan _

def isLimitCechFan (i : Fin (n + 1) → ι) : IsLimit (cechFan U n i) :=
  Opens.isLimitFan _

noncomputable def cechCochainAddCommGrpCatIso :
    ((cechComplexFunctor U).obj F).X n ≅
      (cechCochainAddCommGrpCatFunctor U (cechFan U n)).obj F :=
  cechComplexFunctorAddCommGrpCatObjXIso U _ (isLimitCechFan U n) F

end

noncomputable example {T : Type u} [TopologicalSpace T]
    (F : (Opens T)ᵒᵖ ⥤ AddCommGrpCat.{u})
    {ι : Type u} (U : ι → Opens T) {n : ℕ}
    (f : ∀ (i : (Fin (n + 1) → ι)),
      F.obj (op ⟨⋂ (k : Fin (n + 1)), U (i k), isOpen_iInter_of_finite (fun _ ↦ (U _).isOpen)⟩)) :
    ((cechComplexFunctor U).obj F).X n :=
  (cechCochainAddCommGrpCatIso F U n).inv f

end TopologicalSpace
