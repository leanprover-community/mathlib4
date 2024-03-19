import Mathlib.CategoryTheory.EffectiveEpi.Preserves
import Mathlib.CategoryTheory.EffectiveEpi.Coproduct
import Mathlib.CategoryTheory.Extensive
import Mathlib.CategoryTheory.Limits.Preserves.Finite

namespace CategoryTheory

open Limits

variable {C : Type*} [Category C] [FinitaryPreExtensive C]

theorem effectiveEpi_desc_iff_effectiveEpiFamily {α : Type} [Finite α]
    {B : C} (X : α → C) (π : (a : α) → X a ⟶ B) :
    EffectiveEpi (Sigma.desc π) ↔ EffectiveEpiFamily X π := by
  exact ⟨fun h ↦ ⟨⟨@effectiveEpiFamilyStructOfEffectiveEpiDesc _ _ _ _ X π _ h _ _ (fun g ↦
    (FinitaryPreExtensive.sigma_desc_iso (fun a ↦ Sigma.ι X a) g inferInstance).epi_of_iso)⟩⟩,
    fun _ ↦ inferInstance⟩

variable {D : Type*} [Category D] [FinitaryPreExtensive D]
variable (F : C ⥤ D) [PreservesFiniteCoproducts F]

instance [F.ReflectsEffectiveEpis] : F.ReflectsFiniteEffectiveEpiFamilies where
  reflects {α _ B} X π h := by
    have : Fintype α := Fintype.ofFinite _
    simp only [← effectiveEpi_desc_iff_effectiveEpiFamily]
    apply F.effectiveEpi_of_map
    convert (inferInstance :
      EffectiveEpi (inv (sigmaComparison F X) ≫ (Sigma.desc (fun a ↦ F.map (π a)))))
    simp

instance [F.PreservesEffectiveEpis] : F.PreservesFiniteEffectiveEpiFamilies where
  preserves {α _ B} X π h := by
    have : Fintype α := Fintype.ofFinite _
    simp only [← effectiveEpi_desc_iff_effectiveEpiFamily]
    convert (inferInstance :
      EffectiveEpi ((sigmaComparison F X) ≫ (F.map (Sigma.desc π))))
    simp
