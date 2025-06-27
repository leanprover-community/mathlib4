/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.ExactCategory.Basic
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.Abelian

/-!
# Abelian categories are exact

-/

namespace CategoryTheory

open Limits

variable {C : Type _} [Category C] [Abelian C]

namespace Abelian

instance monomorphisms_stableUnderCobaseChange :
    (MorphismProperty.monomorphisms C).IsStableUnderCobaseChange :=
  MorphismProperty.IsStableUnderCobaseChange.mk' (fun _ _ _ f _ _ (_ : Mono f) ↦
    (inferInstanceAs (Mono _)))

instance epimorphisms_stableUnderBaseChange :
    (MorphismProperty.epimorphisms C).IsStableUnderBaseChange :=
  MorphismProperty.IsStableUnderBaseChange.mk' (fun _ _ _ _ g _ (_ : Epi g) ↦
    (inferInstanceAs (Epi _)))

end Abelian

namespace ExactCategory

namespace OfAbelian

def shortExact : ObjectProperty (ShortComplex C) := fun S => S.ShortExact

lemma respectsIso_shortExact : (shortExact (C := C)).IsClosedUnderIsomorphisms  :=
  ⟨fun {_ _} e => ShortComplex.shortExact_of_iso e⟩

lemma fAdmissible_iff_mono {X Y : C} (f : X ⟶ Y) :
    ShortComplex.fAdmissible shortExact f ↔ Mono f := by
  constructor
  · rintro ⟨_, _, _, H⟩
    exact H.mono_f
  · intro h
    exact ⟨_, _, cokernel.condition f,
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _) }⟩

lemma gAdmissible_iff_epi {X Y : C} (f : X ⟶ Y) :
    ShortComplex.gAdmissible shortExact f ↔ Epi f := by
  constructor
  · rintro ⟨_, _, _, H⟩
    exact H.epi_g
  · intro h
    exact ⟨_, _, kernel.condition f,
      { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _) }⟩

lemma fAdmissible_eq_monomorphisms :
    ShortComplex.fAdmissible shortExact =
      MorphismProperty.monomorphisms C := by
  ext
  apply fAdmissible_iff_mono

lemma gAdmissible_eq_epimorphisms :
    ShortComplex.gAdmissible shortExact =
      MorphismProperty.epimorphisms C := by
  ext
  apply gAdmissible_iff_epi

end OfAbelian

noncomputable def ofAbelian : ExactCategory C where
  shortExact' := OfAbelian.shortExact
  respectsIso_shortExact' := OfAbelian.respectsIso_shortExact
  shortExact_kernel' S hS := ⟨hS.fIsKernel⟩
  shortExact_cokernel' S hS := ⟨hS.gIsCokernel⟩
  admissibleMono_id X := by
    rw [OfAbelian.fAdmissible_iff_mono]
    infer_instance
  admissibleEpi_id X := by
    rw [OfAbelian.gAdmissible_iff_epi]
    infer_instance
  admissibleMono_stableUnderComposition := ⟨by
    rintro _ _ _ f g hf hg
    rw [OfAbelian.fAdmissible_iff_mono] at hf hg ⊢
    apply mono_comp⟩
  admissibleEpi_stableUnderComposition := ⟨by
    rintro _ _ _ f g hf hg
    rw [OfAbelian.gAdmissible_iff_epi] at hf hg ⊢
    apply epi_comp⟩
  admissibleMono_coquarrable X Y f _ X' g := inferInstance
  admissibleEpi_quarrable X Y f _ Y' g := inferInstance
  admissibleMono_stableUnderCobaseChange := by
    rw [OfAbelian.fAdmissible_eq_monomorphisms]
    exact Abelian.monomorphisms_stableUnderCobaseChange
  admissibleEpi_stableUnderBaseChange := by
    rw [OfAbelian.gAdmissible_eq_epimorphisms]
    exact Abelian.epimorphisms_stableUnderBaseChange

end ExactCategory

end CategoryTheory
