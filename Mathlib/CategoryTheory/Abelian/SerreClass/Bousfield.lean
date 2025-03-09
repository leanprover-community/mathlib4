/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Abelian.SerreClass.MorphismProperty
import Mathlib.CategoryTheory.Localization.Bousfield

/-!
# Bousfield localizations with respect to Serre classes

-/

namespace CategoryTheory

open Localization Limits MorphismProperty

variable {C D : Type*} [Category C] [Category D]

abbrev Functor.kernel (G : D ⥤ C) : ObjectProperty D :=
  ObjectProperty.inverseImage IsZero G

variable [Abelian C] [Abelian D] (G : D ⥤ C)
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

namespace Abelian

example : G.kernel.IsSerreClass := inferInstance

lemma serreW_kernel_eq_inverseImage_isomorphisms :
    G.kernel.serreW = (isomorphisms C).inverseImage G := by
  ext X Y f
  simp only [inverseImage_iff, isomorphisms.iff, ObjectProperty.serreW,
    ObjectProperty.prop_inverseImage_iff]
  have h₁ : Mono (G.map f) ↔ IsZero (G.obj (kernel f)) := by
    have hS : ((ShortComplex.mk _ _ (kernel.condition f)).map G).Exact :=
      (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel f)).map G
    have := hS.mono_g_iff
    dsimp at this
    rw [this]
    refine ⟨fun h ↦ ?_, fun h ↦ h.eq_of_src _ _⟩
    rw [IsZero.iff_id_eq_zero, ← cancel_mono (G.map (kernel.ι f)), h, comp_zero, zero_comp]
  have h₂ : Epi (G.map f) ↔ IsZero (G.obj (cokernel f)) := by
    have hS : ((ShortComplex.mk _ _ (cokernel.condition f)).map G).Exact :=
      (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f)).map G
    have := hS.epi_f_iff
    dsimp at this
    rw [this]
    refine ⟨fun h ↦ ?_, fun h ↦ h.eq_of_tgt _ _⟩
    rw [IsZero.iff_id_eq_zero, ← cancel_epi (G.map (cokernel.π f)), h, comp_zero, zero_comp]
  rw [← h₁, ← h₂]
  constructor
  · rintro ⟨_, _⟩
    exact isIso_of_mono_of_epi (G.map f)
  · intro; constructor <;> infer_instance

lemma serreW_kernel_eq_leftBousfield_W_of_rightAdjoint
    {F : C ⥤ D} (adj : G ⊣ F) [F.Full] [F.Faithful] :
    G.kernel.serreW = (LeftBousfield.W (· ∈ Set.range F.obj)) := by
  rw [LeftBousfield.W_eq_inverseImage_isomorphisms adj,
    serreW_kernel_eq_inverseImage_isomorphisms]

lemma isLocalization_serreW_kernel_of_leftAdjoint
    {F : C ⥤ D} (adj : G ⊣ F) [F.Full] [F.Faithful] :
    G.IsLocalization G.kernel.serreW := by
  rw [serreW_kernel_eq_inverseImage_isomorphisms G]
  exact adj.isLocalization

end Abelian

end CategoryTheory
