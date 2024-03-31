import Mathlib.CategoryTheory.ExactCategory.Basic
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.Abelian

namespace CategoryTheory

open Limits

variable {C : Type _} [Category C] [Abelian C]

namespace Abelian

lemma monomorphisms_stableUnderCobaseChange :
    (MorphismProperty.monomorphisms C).StableUnderCobaseChange :=
  MorphismProperty.StableUnderCobaseChange.mk
    (MorphismProperty.RespectsIso.monomorphisms _)
    (fun _ _ _ f _ (_ : Mono f) => (inferInstance : Mono _))

lemma epimorphisms_stableUnderBaseChange :
    (MorphismProperty.epimorphisms C).StableUnderBaseChange :=
  MorphismProperty.StableUnderBaseChange.mk
    (MorphismProperty.RespectsIso.epimorphisms _)
    (fun _ _ _ _ g (_ : Epi g) => (inferInstance : Epi _))

end Abelian

namespace ExactCategory

namespace OfAbelian

def shortExact : ShortComplex C → Prop := fun S => S.ShortExact

lemma respectsIso_shortExact : ClosedUnderIsomorphisms (shortExact (C := C)) :=
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
  admissibleMono_stableUnderComposition _ _ _ _ _ hf hg := by
    rw [OfAbelian.fAdmissible_iff_mono] at hf hg ⊢
    apply mono_comp
  admissibleEpi_stableUnderComposition _ _ _ _ _ hf hg := by
    rw [OfAbelian.gAdmissible_iff_epi] at hf hg ⊢
    apply epi_comp
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
