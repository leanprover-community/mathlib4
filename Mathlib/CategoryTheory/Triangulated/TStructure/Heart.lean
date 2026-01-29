/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Triangulated.TStructure.Induced

/-!
# The heart of a t-structure

## References
* [Beilinson, Bernstein, Deligne, Gabber, *Faisceaux pervers*][bbd-1982]

-/

@[expose] public section

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

open Pretriangulated Triangulated

namespace Triangulated

namespace TStructure

variable (t : TStructure C)

def heart : ObjectProperty C := fun X ↦ t.le 0 X ∧ t.ge 0 X

lemma mem_heart_iff (X : C) :
    t.heart X ↔ t.IsLE X 0 ∧ t.IsGE X 0 := by
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨⟨h₁⟩, ⟨h₂⟩⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨t.le_of_isLE _ _, t.ge_of_isGE _ _⟩

instance : t.heart.IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    rw [mem_heart_iff] at hX ⊢
    have := hX.1
    have := hX.2
    constructor
    · exact t.isLE_of_iso e 0
    · exact t.isGE_of_iso e 0

class HasHeart where
  H : Type*
  [cat : Category H]
  [preadditive : Preadditive H]
  ι : H ⥤ C
  additive_ι : ι.Additive := by infer_instance
  fullι : ι.Full := by infer_instance
  faithful_ι : ι.Faithful := by infer_instance
  hι : ι.essImage = t.heart := by simp

def hasHeartFullSubcategory : t.HasHeart where
  H := t.heart.FullSubcategory
  ι := t.heart.ι
  hι := by
    ext X
    constructor
    · rintro ⟨⟨Y, hY⟩, ⟨e : Y ≅ X⟩⟩
      exact t.heart.prop_of_iso e hY
    · intro hX
      exact ⟨⟨X, hX⟩, ⟨Iso.refl _⟩⟩

variable [ht : t.HasHeart]

def Heart := ht.H

instance : Category t.Heart := ht.cat

def ιHeart : t.Heart ⥤ C := ht.ι

instance : Preadditive t.Heart := ht.preadditive
instance : t.ιHeart.Full := ht.fullι
instance : t.ιHeart.Faithful := ht.faithful_ι
instance : t.ιHeart.Additive := ht.additive_ι

lemma ιHeart_obj_mem (X : t.Heart) : t.heart (t.ιHeart.obj X) := by
  change (t.ιHeart.obj X) ∈ setOf t.heart
  rw [← ht.hι]
  exact t.ιHeart.obj_mem_essImage X

instance (X : t.Heart) : t.IsLE (t.ιHeart.obj X) 0 :=
  ⟨(t.ιHeart_obj_mem X).1⟩

instance (X : t.Heart) : t.IsGE (t.ιHeart.obj X) 0 :=
  ⟨(t.ιHeart_obj_mem X).2⟩

lemma mem_essImage_ιHeart_iff (X : C) :
    t.ιHeart.essImage X ↔ t.heart X := by
  dsimp [ιHeart]
  rw [ht.hι]

noncomputable def heartMk (X : C) (hX : t.heart X) : t.Heart :=
  Functor.essImage.witness ((t.mem_essImage_ιHeart_iff X).2 hX)

noncomputable def ιHeartObjHeartMkIso (X : C) (hX : t.heart X) :
    t.ιHeart.obj (t.heartMk X hX) ≅ X :=
  Functor.essImage.getIso ((t.mem_essImage_ιHeart_iff X).2 hX)

@[simps obj]
noncomputable def liftHeart {D : Type*} [Category D]
    (F : D ⥤ C) (hF : ∀ (X : D), t.heart (F.obj X)) :
    D ⥤ t.Heart where
  obj X := t.heartMk (F.obj X) (hF X)
  map {X Y} f := t.ιHeart.preimage ((t.ιHeartObjHeartMkIso _ (hF X)).hom ≫ F.map f ≫
      (t.ιHeartObjHeartMkIso _ (hF Y)).inv)
  map_id X := t.ιHeart.map_injective (by simp)
  map_comp f g := t.ιHeart.map_injective (by simp)

@[simp, reassoc]
lemma ιHeart_map_liftHeart_map {D : Type*} [Category D]
    (F : D ⥤ C) (hF : ∀ (X : D), t.heart (F.obj X)) {X Y : D} (f : X ⟶ Y) :
    t.ιHeart.map ((t.liftHeart F hF).map f) =
      (t.ιHeartObjHeartMkIso _ (hF X)).hom ≫ F.map f ≫
        (t.ιHeartObjHeartMkIso _ (hF Y)).inv := by
  simp [liftHeart]

noncomputable def liftHeartιHeart {D : Type*} [Category D]
    (F : D ⥤ C) (hF : ∀ (X : D), t.heart (F.obj X)) :
    t.liftHeart F hF ⋙ t.ιHeart ≅ F :=
  NatIso.ofComponents (fun X => t.ιHeartObjHeartMkIso _ (hF X)) (by aesop_cat)

end TStructure

end Triangulated

namespace ObjectProperty

variable (P : ObjectProperty C) [P.IsTriangulated]
    (t : TStructure C) [P.HasInducedTStructure t]

@[simp]
lemma mem_tStructure_heart_iff (X : P.FullSubcategory) :
    (P.tStructure t).heart X ↔ t.heart X.1 := by
  rfl

end ObjectProperty

end CategoryTheory
