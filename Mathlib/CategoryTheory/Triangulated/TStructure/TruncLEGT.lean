/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-!
# Truncations for a t-structure

-/

@[expose] public section

namespace CategoryTheory

open Limits Pretriangulated

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

namespace Triangulated

namespace TStructure

variable (t : TStructure C)

noncomputable def truncLE (n : ℤ) : C ⥤ C := t.truncLT (n+1)

instance (n : ℤ) : (t.truncLE n).Additive := by
  dsimp only [truncLE]
  infer_instance

instance (n : ℤ) (X : C) : t.IsLE ((t.truncLE n).obj X) n := by
  have : t.IsLE ((t.truncLE n).obj X) (n+1-1) := by
    dsimp [truncLE]
    infer_instance
  exact t.isLE_of_LE _ (n+1-1) n (by lia)

noncomputable def truncGT (n : ℤ) : C ⥤ C := t.truncGE (n+1)

instance (n : ℤ) : (t.truncGT n).Additive := by
  dsimp only [truncGT]
  infer_instance

instance (n : ℤ) (X : C) : t.IsGE ((t.truncGT n).obj X) (n+1) := by
  dsimp [truncGT]
  infer_instance

instance (n : ℤ) (X : C) : t.IsGE ((t.truncGT (n-1)).obj X) n :=
  t.isGE_of_GE _ n (n-1+1) (by lia)

noncomputable def truncLEIsoTruncLT (a b : ℤ) (h : a + 1 = b) : t.truncLE a ≅ t.truncLT b :=
  eqToIso (congr_arg t.truncLT h)

noncomputable def truncGTIsoTruncGE (a b : ℤ) (h : a + 1 = b) : t.truncGT a ≅ t.truncGE b :=
  eqToIso (congr_arg t.truncGE h)

noncomputable def truncLEι (n : ℤ) : t.truncLE n ⟶ 𝟭 C := t.truncLTι (n + 1)

@[reassoc (attr := simp)]
lemma truncLEIsoTruncLT_hom_ι (a b : ℤ) (h : a + 1 = b) :
    (t.truncLEIsoTruncLT a b h).hom ≫ t.truncLTι b = t.truncLEι a := by
  subst h
  dsimp [truncLEIsoTruncLT, truncLEι]
  rw [Category.id_comp]

@[reassoc (attr := simp)]
lemma truncLEIsoTruncLT_hom_ι_app (a b : ℤ) (h : a + 1 = b) (X : C) :
    (t.truncLEIsoTruncLT a b h).hom.app X ≫ (t.truncLTι b).app X = (t.truncLEι a).app X :=
  congr_app (t.truncLEIsoTruncLT_hom_ι a b h) X

@[reassoc (attr := simp)]
lemma truncLEIsoTruncLT_inv_ι (a b : ℤ) (h : a + 1 = b) :
    (t.truncLEIsoTruncLT a b h).inv ≫ t.truncLEι a = t.truncLTι b := by
  subst h
  dsimp [truncLEIsoTruncLT, truncLEι, truncLE]
  rw [Category.id_comp]

@[reassoc (attr := simp)]
lemma truncLEIsoTruncLT_inv_ι_app (a b : ℤ) (h : a + 1 = b) (X : C) :
    (t.truncLEIsoTruncLT a b h).inv.app X ≫ (t.truncLEι a).app X = (t.truncLTι b).app X :=
  congr_app (t.truncLEIsoTruncLT_inv_ι a b h) X

noncomputable def truncGTπ (n : ℤ) : 𝟭 C ⟶ t.truncGT n := t.truncGEπ (n + 1)

@[reassoc (attr := simp)]
lemma π_truncGTIsoTruncGE_hom (a b : ℤ) (h : a + 1 = b) :
    t.truncGTπ a ≫ (t.truncGTIsoTruncGE a b h).hom = t.truncGEπ b := by
  subst h
  dsimp [truncGTIsoTruncGE, truncGTπ]
  rw [Category.comp_id]

@[reassoc (attr := simp)]
lemma π_truncGTIsoTruncGE_hom_ι_app (a b : ℤ) (h : a + 1 = b) (X : C) :
    (t.truncGTπ a).app X ≫ (t.truncGTIsoTruncGE a b h).hom.app X = (t.truncGEπ b).app X :=
  congr_app (t.π_truncGTIsoTruncGE_hom a b h) X

@[reassoc (attr := simp)]
lemma π_truncGTIsoTruncGE_inv (a b : ℤ) (h : a + 1 = b) :
    t.truncGEπ b ≫ (t.truncGTIsoTruncGE a b h).inv = t.truncGTπ a := by
  subst h
  dsimp [truncGTIsoTruncGE, truncGTπ, truncGT]
  rw [Category.comp_id]

@[reassoc (attr := simp)]
lemma π_truncGTIsoTruncGE_inv_ι_app (a b : ℤ) (h : a + 1 = b) (X : C) :
    (t.truncGEπ b).app X ≫ (t.truncGTIsoTruncGE a b h).inv.app X = (t.truncGTπ a).app X :=
  congr_app (t.π_truncGTIsoTruncGE_inv a b h) X

noncomputable def truncGEδLE (a b : ℤ) (h : a + 1 = b) :
    t.truncGE b ⟶ t.truncLE a ⋙ shiftFunctor C (1 : ℤ) :=
  t.truncGEδLT b ≫ Functor.whiskerRight (t.truncLEIsoTruncLT a b h).inv (shiftFunctor C (1 : ℤ))

@[simps!]
noncomputable def triangleLEGE (a b : ℤ) (h : a + 1 = b) : C ⥤ Triangle C :=
  Triangle.functorMk (t.truncLEι a) (t.truncGEπ b) (t.truncGEδLE a b h)

noncomputable def triangleLEGEIsoTriangleLTGE (a b : ℤ) (h : a + 1 = b) :
    t.triangleLEGE a b h ≅ t.triangleLTGE b := by
  refine Triangle.functorIsoMk _ _ (t.truncLEIsoTruncLT a b h) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · cat_disch
  · cat_disch
  · ext
    dsimp [truncGEδLE]
    simp only [Category.assoc, Category.id_comp, ← Functor.map_comp,
      Iso.inv_hom_id_app, Functor.map_id, Category.comp_id]

lemma triangleLEGE_distinguished (a b : ℤ) (h : a + 1 = b) (X : C) :
    (t.triangleLEGE a b h).obj X ∈ distTriang C :=
  isomorphic_distinguished _ (t.triangleLTGE_distinguished b X) _
    ((t.triangleLEGEIsoTriangleLTGE a b h).app X)

noncomputable def truncGTδLE (n : ℤ) :
    t.truncGT n ⟶ t.truncLE n ⋙ shiftFunctor C (1 : ℤ) :=
  (t.truncGTIsoTruncGE n (n+1) rfl).hom ≫ t.truncGEδLE n (n+1) (by lia)

@[simps!]
noncomputable def triangleLEGT (n : ℤ) : C ⥤ Triangle C :=
  Triangle.functorMk (t.truncLEι n) (t.truncGTπ n) (t.truncGTδLE n)

noncomputable def triangleLEGTIsoTriangleLEGE (a b : ℤ) (h : a + 1 = b) :
    t.triangleLEGT a ≅ t.triangleLEGE a b h := by
  refine Triangle.functorIsoMk _ _ (Iso.refl _) (Iso.refl _) (t.truncGTIsoTruncGE a b h) ?_ ?_ ?_
  · cat_disch
  · cat_disch
  · ext
    dsimp [truncGTδLE]
    subst h
    simp only [Functor.map_id, Category.comp_id]

lemma triangleLEGT_distinguished (n : ℤ) (X : C) :
    (t.triangleLEGT n).obj X ∈ distTriang C :=
  isomorphic_distinguished _ (t.triangleLEGE_distinguished n (n+1) rfl X) _
    ((t.triangleLEGTIsoTriangleLEGE n (n+1) rfl).app X)

end TStructure

end Triangulated

end CategoryTheory
