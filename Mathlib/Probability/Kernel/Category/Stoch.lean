/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Probability.Kernel.Category.SFinite
public import Mathlib

@[expose] public section

open CategoryTheory ProbabilityTheory MeasureTheory ObjectProperty MonoidalCategory

universe u

abbrev StochHom : MorphismProperty SFinKer := fun _ _ κ => IsMarkovKernel κ.1

instance {X Y : SFinKer} {κ : X ⟶ Y} {hκ : StochHom κ} : IsMarkovKernel κ.1 := hκ

instance : StochHom.IsMultiplicative where
  id_mem X := by
    kernel_cat
    infer_instance
  comp_mem κ η hκ hη := by
    kernel_cat
    infer_instance

abbrev Stoch := WideSubcategory StochHom

noncomputable section

instance : MonoidalCategory Stoch.{u} where
  tensorObj X Y := ⟨X.obj ⊗ Y.obj⟩
  whiskerLeft X Y Z κ := by
    refine ⟨X.obj ◁ κ.1, ?_⟩
    kernel_cat
    have : IsMarkovKernel (κ.1.1) := κ.2
    simp only [Set.mem_setOf_eq]
    infer_instance
  whiskerRight κ Y := by
    refine ⟨κ.1 ▷ Y.obj, ?_⟩
    kernel_cat
    have : IsMarkovKernel (κ.1.1) := κ.2
    simp only [Set.mem_setOf_eq]
    infer_instance
  tensorUnit := ⟨SFinKer.of PUnit⟩
  associator X Y Z := by
    refine ⟨⟨(α_ X.obj Y.obj Z.obj).hom, ?_⟩, ⟨(α_ X.obj Y.obj Z.obj).inv, ?_⟩, ?_, ?_⟩
    · kernel_cat
      exact Kernel.IsMarkovKernel.map Kernel.id (by fun_prop)
    · kernel_cat
      exact Kernel.IsMarkovKernel.map Kernel.id (by fun_prop)
    all_goals
    rw [Subtype.ext_iff]
    simp
  leftUnitor X := by
    refine ⟨⟨(λ_ X.obj).hom, ?_⟩, ⟨(λ_ X.obj).inv, ?_⟩, ?_, ?_⟩
    · kernel_cat
      exact Kernel.IsMarkovKernel.map Kernel.id (by fun_prop)
    · kernel_cat
      exact Kernel.IsMarkovKernel.map Kernel.id (by fun_prop)
    all_goals
    rw [Subtype.ext_iff]
    simp
  rightUnitor X := by
    refine ⟨⟨(ρ_ X.obj).hom, ?_⟩, ⟨(ρ_ X.obj).inv, ?_⟩, ?_, ?_⟩
    · kernel_cat
      exact Kernel.IsMarkovKernel.map Kernel.id (by fun_prop)
    · kernel_cat
      exact Kernel.IsMarkovKernel.map Kernel.id (by fun_prop)
    all_goals
    rw [Subtype.ext_iff]
    simp
  id_tensorHom_id X Y := by
    kernel_cat
    simp
  tensorHom_comp_tensorHom κ₁ κ₂ η₁ η₂ := by
    rw [Subtype.ext_iff]
    simp only [WideSubcategory.comp_def, ← MonoidalCategory.tensorHom_def]
    exact MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _
  associator_naturality κ₁ κ₂ η := by
    rw [Subtype.ext_iff]
    simp only [WideSubcategory.comp_def]
    exact MonoidalCategory.associator_naturality _ _ _
  pentagon W X Y Z := by
    rw [Subtype.ext_iff]
    simp only [WideSubcategory.comp_def]
    exact MonoidalCategory.pentagon _ _ _ _
  leftUnitor_naturality κ := by
    rw [Subtype.ext_iff]
    simp only [WideSubcategory.comp_def]
    exact MonoidalCategory.leftUnitor_naturality _
  rightUnitor_naturality κ := by
    rw [Subtype.ext_iff]
    simp only [WideSubcategory.comp_def]
    exact MonoidalCategory.rightUnitor_naturality _
  triangle X Y := by
    rw [Subtype.ext_iff]
    simp only [WideSubcategory.comp_def]
    exact MonoidalCategory.triangle _ _


end
