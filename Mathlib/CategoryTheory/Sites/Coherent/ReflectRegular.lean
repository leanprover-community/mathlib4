import Mathlib.CategoryTheory.EffectiveEpi.Preserves
import Mathlib.CategoryTheory.Sites.Coherent.RegularTopology

namespace CategoryTheory

variable {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
  [F.PreservesEffectiveEpis] [F.ReflectsEffectiveEpis]
  (h : ∀ (X : D), ∃ (W : C) (π : F.obj W ⟶ X), EffectiveEpi π)
  [Preregular D] [Full F] [Faithful F]

lemma reflects_preregular : Preregular C where
  exists_fac f g _ := by
    obtain ⟨W', f', _, i, w⟩ := Preregular.exists_fac (F.map f) (F.map g)
    obtain ⟨W, π, _⟩ := h W'
    refine ⟨W, Full.preimage (π ≫ f'), ⟨F.effectiveEpi_of_map _ ?_, Full.preimage (π ≫ i), ?_⟩⟩
    · simp only [Full.witness]
      infer_instance
    · apply Faithful.map_injective (F := F)
      simp [w]
