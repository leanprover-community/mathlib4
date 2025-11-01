/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Sites.Precoverage
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# The jointly surjective precoverage

In the category of types, the jointly surjective precoverage has the jointly surjective
families as coverings. We show that this precoverage is stable under the standard constructions.

## Notes

See `CategoryTheory.Sites.Types` for the Grothendieck topology of jointly surjective covers.
-/

universe u

namespace CategoryTheory

open Limits

namespace Types

/-- The jointly surjective precoverage in the category of types has the jointly surjective
families as coverings. -/
def jointlySurjectivePrecoverage : Precoverage (Type u) where
  coverings X R := ∀ x : X, ∃ (Y : Type u) (g : Y ⟶ X), R g ∧ x ∈ Set.range g

lemma mem_jointlySurjectivePrecoverage_iff {X : Type u} {R : Presieve X} :
    R ∈ jointlySurjectivePrecoverage X ↔
      ∀ x : X, ∃ (Y : Type u) (g : Y ⟶ X), R g ∧ x ∈ Set.range g :=
  .rfl

lemma singleton_mem_jointlySurjectivePrecoverage_iff {X Y : Type u} {f : X ⟶ Y} :
    Presieve.singleton f ∈ jointlySurjectivePrecoverage Y ↔ Function.Surjective f := by
  rw [mem_jointlySurjectivePrecoverage_iff]
  refine ⟨fun hf x ↦ ?_, fun hf x ↦ ⟨X, f, ⟨⟩, by simp [hf.range_eq]⟩⟩
  obtain ⟨_, _, ⟨⟩, hx⟩ := hf x
  exact hx

@[simp]
lemma ofArrows_mem_jointlySurjectivePrecoverage_iff {X : Type u} {ι : Type*} {Y : ι → Type u}
    {f : ∀ i, Y i ⟶ X} :
    Presieve.ofArrows Y f ∈ jointlySurjectivePrecoverage X ↔
      ∀ x, ∃ (i : ι), x ∈ Set.range (f i) := by
  refine ⟨fun h x ↦ ?_, fun h x ↦ ?_⟩
  · obtain ⟨Y, g, ⟨i⟩, hx⟩ := h x
    use i
  · obtain ⟨i, hx⟩ := h x
    use Y i, f i, ⟨i⟩

instance : jointlySurjectivePrecoverage.HasIsos where
  mem_coverings_of_isIso {S T} f hf x := by
    use S, f, ⟨⟩
    exact surjective_of_epi f x

instance : jointlySurjectivePrecoverage.IsStableUnderComposition where
  comp_mem_coverings {ι} S X f hf σ Y g hg := by
    simp_rw [ofArrows_mem_jointlySurjectivePrecoverage_iff] at hf hg ⊢
    intro x
    obtain ⟨i, y, rfl⟩ := hf x
    obtain ⟨j, z, rfl⟩ := hg i y
    use ⟨i, j⟩, z
    simp

instance : jointlySurjectivePrecoverage.IsStableUnderSup where
  sup_mem_coverings {X} R S hR _ x := by
    obtain ⟨Y, f, hf, hx⟩ := hR x
    use Y, f, .inl hf

end Types

variable {C : Type*} [Category C] (F : C ⥤ Type u)

lemma Presieve.mem_comap_jointlySurjectivePrecoverage_iff {X : C} {R : Presieve X} :
    R ∈ Types.jointlySurjectivePrecoverage.comap F X ↔
      ∀ x : F.obj X, ∃ (Y : C) (f : Y ⟶ X), R f ∧ x ∈ Set.range (F.map f) := by
  rw [Precoverage.mem_comap_iff]
  refine ⟨fun h x ↦ ?_, fun h x ↦ ?_⟩
  · obtain ⟨-, -, ⟨hf⟩, hi⟩ := h x
    exact ⟨_, _, hf, hi⟩
  · obtain ⟨Y, g, hg, hi⟩ := h x
    exact ⟨_, _, ⟨hg⟩, hi⟩

/-- The pullback of the jointly surjective precoverage of types to any category `C` via a
(forgetful) functor `C ⥤ Type u` is stable under base change if the canonical map
`F (X ×[Y] Z) ⟶ F(X) ×[F(Y)] F(Z)` is surjective. -/
lemma isStableUnderBaseChange_comap_jointlySurjectivePrecoverage
    (H : ∀ {X Y S : C} (f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g],
      Function.Surjective (pullbackComparison F f g)) :
    (Types.jointlySurjectivePrecoverage.comap F).IsStableUnderBaseChange where
  mem_coverings_of_isPullback {ι} S X f hf Y g P p₁ p₂ h := by
    rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows,
      Types.ofArrows_mem_jointlySurjectivePrecoverage_iff] at hf ⊢
    intro x
    obtain ⟨i, hi⟩ := hf (F.map g x)
    have : HasPullback g (f i) := (h i).hasPullback
    use i
    have : F.map (p₁ i) = F.map ((h i).isoPullback.hom) ≫ pullbackComparison F g (f i) ≫
        pullback.fst _ _ := by simp [← Functor.map_comp]
    rwa [this, types_comp, types_comp, Function.comp_assoc, Set.range_comp,
      Function.Surjective.range_eq <| (H _ _).comp (surjective_of_epi _), Set.image_univ,
      Types.range_pullbackFst]

instance : Types.jointlySurjectivePrecoverage.IsStableUnderBaseChange := by
  rw [← Precoverage.comap_id Types.jointlySurjectivePrecoverage]
  apply isStableUnderBaseChange_comap_jointlySurjectivePrecoverage
  intro X Y S f g _
  exact surjective_of_epi _

end CategoryTheory
