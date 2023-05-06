import Mathlib.CategoryTheory.Localization.Triangulated

namespace CategoryTheory

open Category Limits Preadditive ZeroObject

namespace Triangulated

open Pretriangulated

variable (C : Type _) [Category C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

structure Subcategory where
  set : Set C
  zero : (0 : C) ∈ set
  shift : ∀ (X : C) (n : ℤ) (_ : X ∈ set), X⟦n⟧ ∈ set
  ext₂ : ∀ (T : Triangle C) (_ : T ∈ distTriang C)
    (_ : T.obj₁ ∈ set) (_ : T.obj₃ ∈ set), T.obj₂ ∈ set

namespace Subcategory

variable {C}
variable (S : Subcategory C)

def W : MorphismProperty C := fun X Y f => ∃ (Z : C) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧)
  (_ : Triangle.mk f g h ∈ distTriang C), Z ∈ S.set

def W' : MorphismProperty C := fun Y Z g => ∃ (X : C) (f : X ⟶ Y) (h : Z ⟶ X⟦(1 : ℤ)⟧)
  (_ : Triangle.mk f g h ∈ distTriang C), X ∈ S.set

variable {S}

def W.mk {T : Triangle C} (hT : T ∈ distTriang C) (h : T.obj₃ ∈ S.set) : S.W T.mor₁ :=
  ⟨T.obj₃, T.mor₂, T.mor₃, hT, h⟩

def W'.mk {T : Triangle C} (hT : T ∈ distTriang C) (h : T.obj₁ ∈ S.set) : S.W' T.mor₂ :=
  ⟨T.obj₁, T.mor₁, T.mor₃, hT, h⟩

noncomputable def W.triangle {X Y : C} (f : X ⟶ Y) (hf : S.W f) : Triangle C :=
  Triangle.mk f hf.choose_spec.choose hf.choose_spec.choose_spec.choose

lemma W.triangleDistinguished {X Y : C} (f : X ⟶ Y) (hf : S.W f) :
   (W.triangle f hf) ∈ distTriang C :=
  hf.choose_spec.choose_spec.choose_spec.choose

lemma W.triangle_obj₃_mem {X Y : C} (f : X ⟶ Y) (hf : S.W f) :
  (W.triangle f hf).obj₃ ∈ S.set :=
  hf.choose_spec.choose_spec.choose_spec.choose_spec

variable (S)

lemma W_eq_W' : S.W = S.W' := by
  apply MorphismProperty.ext
  intro X Y f
  constructor
  . rintro ⟨Z, g, h, H, mem⟩
    refine' ⟨_, _, _, inv_rot_of_dist_triangle _ H, S.shift _ (-1) mem⟩
  . rintro ⟨Z, g, h, H, mem⟩
    refine' ⟨_, _, _, rot_of_dist_triangle _ H, S.shift _ 1 mem⟩

def W.mk' {T : Triangle C} (hT : T ∈ distTriang C) (h : T.obj₁ ∈ S.set) : S.W T.mor₂ := by
  simpa only [W_eq_W'] using W'.mk hT h

instance instContainsIdentitiesW : S.W.ContainsIdentities :=
  ⟨fun X => ⟨_, _, _, contractible_distinguished X, S.zero⟩⟩

end Subcategory

end Triangulated

end CategoryTheory
