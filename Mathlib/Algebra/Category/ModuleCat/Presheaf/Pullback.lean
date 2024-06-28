/-
Copyright (c) 2024 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Joel Riou
-/

import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Adjunctions

universe v v₁ v₂ u₁ u₂ u

open CategoryTheory Opposite

variable {C : Type u₁} [Category.{u} C] {D : Type u₂} [Category.{v₂} D]

namespace ModuleCat

variable {R X Y : Type u} [Ring R] {M : ModuleCat.{u} R}

noncomputable def freeDesc (f : X ⟶ M) : (free R).obj X ⟶ M :=
  ((adj R).homEquiv _ _).symm f

noncomputable
def freeUnit (x : X) : (free R).obj X := Finsupp.single x 1

@[simp]
lemma freeDesc_apply (f : X ⟶ M) (x : X) : freeDesc f (freeUnit x) = f x := by
    dsimp [freeDesc, freeUnit, adj]
    erw [Finsupp.lift_apply, Finsupp.sum_single_index]
    all_goals simp

lemma free_ext (f g : (free R).obj X ⟶ M) (h : ∀ x, f (freeUnit x) = g (freeUnit x)) : f = g :=
  Finsupp.lhom_ext' <| fun x ↦ LinearMap.ext_ring (h x)

lemma free_map_eq_freeDesc (f : X → Y) : (free R).map f = freeDesc (fun x ↦ freeUnit (f x)) := by
  apply free_ext
  intro x
  rw [freeDesc_apply]
  simp [freeUnit]
  erw [Finsupp.lmapDomain_apply, Finsupp.mapDomain, Finsupp.sum_single_index]
  simp

@[simp]
lemma adj_homEquiv_symm_apply (f : X ⟶ M) : ((adj R).homEquiv _ _).symm f = freeDesc f :=
  rfl

end ModuleCat

namespace PresheafOfModules


variable {F}
variable {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} (φ : S ⟶ F.op ⋙ R)

open ModuleCat in
@[simps!]
noncomputable
def freeObj (F : Cᵒᵖ ⥤ Type u) : PresheafOfModules.{u} S :=
  BundledCorePresheafOfModules.toPresheafOfModules
  { obj := fun X ↦ (ModuleCat.free (S.obj X)).obj (F.obj X)
    map := fun {X Y} f ↦ freeDesc <| (freeUnit <| F.map f ·)
    map_id := fun X ↦ by
      apply free_ext
      intro x
      dsimp
      erw [freeDesc_apply]
      simp
      rfl
    map_comp := fun {X Y Z} f g ↦ by
      apply free_ext
      intro x
      sorry
       }

open ModuleCat in
noncomputable
def freeMap {F G : Cᵒᵖ ⥤ Type u} (α : F ⟶ G) : freeObj (S := S) F ⟶ freeObj G :=
  PresheafOfModules.Hom.mk'' (fun X ↦ (free _).map (α.app X)) <| fun {X Y} f ↦ by
    apply free_ext
    intro x
    simp_rw [free_map_eq_freeDesc]
    dsimp only [freeObj]
    erw [BundledCorePresheafOfModules.restrictionApp_toPresheafOfModules]
    erw [BundledCorePresheafOfModules.restrictionApp_toPresheafOfModules]
    dsimp only
    erw [comp_apply, comp_apply]
    erw [ModuleCat.restrictScalars.map_apply]
    sorry

variable (S) in
noncomputable
def free : (Cᵒᵖ ⥤ Type u) ⥤ PresheafOfModules.{u} S where
  obj := freeObj
  map := freeMap
  map_id _ := by
    simp only [freeMap, NatTrans.id_app, CategoryTheory.Functor.map_id]
    rfl
  map_comp _ _ := by
    simp only [freeMap, NatTrans.comp_app, CategoryTheory.Functor.map_comp]
    rfl

variable (S) in
protected
def forget := toPresheaf S ⋙ (whiskeringRight _ _ _).obj (forget _)

noncomputable
def freeHomEquiv (X : Cᵒᵖ ⥤ Type u) (F : PresheafOfModules S) :
    ((free S).obj X ⟶ F) ≃ (X ⟶ (PresheafOfModules.forget S).obj F) where
  toFun α := ⟨fun c ↦ ((ModuleCat.adj _).homEquiv _ _) (α.app c), sorry⟩
  invFun β := PresheafOfModules.Hom.mk'' (fun c ↦ ((ModuleCat.adj _).homEquiv _ _).symm (β.app c)) sorry
  left_inv α := by aesop
  right_inv β := by aesop

variable (S) in
noncomputable
def adj : free S ⊣ PresheafOfModules.forget S :=
  Adjunction.mkOfHomEquiv
  { homEquiv := freeHomEquiv
    homEquiv_naturality_left_symm := sorry
    homEquiv_naturality_right := sorry }

noncomputable
def freeYonedaEquiv (M : PresheafOfModules.{u} S) (X : C) :
    ((free S).obj (yoneda.obj X) ⟶ M) ≃ (M.obj (op X)) :=
  ((adj S).homEquiv _ _).trans yonedaEquiv

-- Is the following cocone a colimit cocone?

-- open Limits in
-- noncomputable
-- def tautologicalCocone (M : PresheafOfModules.{u} S) : Cocone <|
--       CostructuredArrow.proj yoneda ((PresheafOfModules.forget _).obj M) ⋙ (yoneda ⋙ free S) where
--   pt := M
--   ι :=
--     { app := fun X ↦ ((adj S).homEquiv _ _).symm X.hom
--       naturality := sorry }

-- Or this one?

-- open Limits in
-- noncomputable
-- def tautologicalCocone' (M : PresheafOfModules.{u} S) : Cocone <|
--       CostructuredArrow.proj (yoneda ⋙ free S) M ⋙ (yoneda ⋙ free S) where
--   pt := M
--   ι :=
--     { app := fun X ↦ X.hom
--       naturality := sorry }


end PresheafOfModules
