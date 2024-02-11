/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Nick Kuhn
-/
import Mathlib.CategoryTheory.Sites.Coherent.CoherentSheaves
/-!

# Description of the covering sieves of the coherent topology

This file characterises the covering sieves of the coherent topology.

## Main result

* `coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily`: a sieve is a covering sieve for the
  coherent topology if and only if it contains a finite effective epimorphic family.

-/

namespace CategoryTheory

variable {C : Type*} [Category C] [Precoherent C] {X : C}

/--
For a precoherent category, any sieve that contains an `EffectiveEpiFamily` is a sieve of the
coherent topology.
Note: This is one direction of `mem_sieves_iff_hasEffectiveEpiFamily`, but is needed for the proof.
-/
theorem coherentTopology.mem_sieves_of_hasEffectiveEpiFamily (S : Sieve X) :
    (∃ (α : Type) (_ : Fintype α) (Y : α → C) (π : (a : α) → (Y a ⟶ X)),
      EffectiveEpiFamily Y π ∧ (∀ a : α, (S.arrows) (π a)) ) →
        (S ∈ GrothendieckTopology.sieves (coherentTopology C) X) := by
  intro ⟨α, _, Y, π, hπ⟩
  refine Coverage.saturate_of_superset (coherentCoverage C) ?_
    (Coverage.saturate.of X _ ⟨α, inferInstance, Y, π, rfl, hπ.1⟩)
  rw [Sieve.sets_iff_generate]
  apply Presieve.le_of_factorsThru_sieve (Presieve.ofArrows (fun i => Y i) π) S _
  intro W g f
  refine ⟨W, 𝟙 W, ?_⟩
  rcases f with ⟨i⟩
  exact ⟨π i, hπ.2 i, by simp⟩

/--
Effective epi families in a precoherent category are transitive, in the sense that an
`EffectiveEpiFamily` and an `EffectiveEpiFamily` over each member, the composition is an
`EffectiveEpiFamily`.
Note: The finiteness condition is an artifact of the proof and is probably unnecessary.
-/
theorem EffectiveEpiFamily.transitive_of_finite {α : Type} [Fintype α] {Y : α → C}
    (π : (a : α) → (Y a ⟶ X)) (h : EffectiveEpiFamily Y π) {β : α → Type} [∀ (a: α), Fintype (β a)]
    {Y_n : (a : α) → β a → C} (π_n : (a : α) → (b : β a) → (Y_n a b ⟶ Y a))
    (H : ∀ a, EffectiveEpiFamily (Y_n a) (π_n a)) :
    EffectiveEpiFamily
      (fun (c : Σ a, β a) => Y_n c.fst c.snd) (fun c => π_n c.fst c.snd ≫ π c.fst) := by
  rw [← Sieve.effectiveEpimorphic_family]
  suffices h₂ : (Sieve.generate (Presieve.ofArrows (fun (⟨a, b⟩ : Σ _, β _) => Y_n a b)
        (fun ⟨a,b⟩ => π_n a b ≫ π a))) ∈ GrothendieckTopology.sieves (coherentTopology C) X by
    change Nonempty _
    rw [← Sieve.forallYonedaIsSheaf_iff_colimit]
    exact fun W => coherentTopology.isSheaf_yoneda_obj W _ h₂
  -- Show that a covering sieve is a colimit, which implies the original set of arrows is regular
  -- epimorphic. We use the transitivity property of saturation
  apply Coverage.saturate.transitive X (Sieve.generate (Presieve.ofArrows Y π))
  · apply Coverage.saturate.of
    use α, inferInstance, Y, π
  · intro V f ⟨Y₁, h, g, ⟨hY, hf⟩⟩
    rw [← hf, Sieve.pullback_comp]
    apply (coherentTopology C).pullback_stable'
    apply coherentTopology.mem_sieves_of_hasEffectiveEpiFamily
    -- Need to show that the pullback of the family `π_n` to a given `Y i` is effective epimorphic
    rcases hY with ⟨i⟩
    exact ⟨β i, inferInstance, Y_n i, π_n i, H i, fun b ↦
      ⟨Y_n i b, (𝟙 _), π_n i b ≫ π i, ⟨(⟨i, b⟩ : Σ (i : α), β i)⟩, by simp⟩⟩

/--
A sieve belongs to the coherent topology if and only if it contains a finite
`EffectiveEpiFamily`.
-/
theorem coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily (S : Sieve X) :
    (S ∈ GrothendieckTopology.sieves (coherentTopology C) X) ↔
    (∃ (α : Type) (_ : Fintype α) (Y : α → C) (π : (a : α) → (Y a ⟶ X)),
        EffectiveEpiFamily Y π ∧ (∀ a : α, (S.arrows) (π a)) )  := by
  constructor
  · intro h
    induction' h with Y T hS Y Y R S _ _ a b
    · rcases hS with ⟨a, h, Y', π, h', _⟩
      refine ⟨a, h, Y', π, inferInstance, fun a' ↦ ?_⟩
      rcases h' with ⟨rfl, _⟩
      exact ⟨Y' a', 𝟙 Y' a', π a', Presieve.ofArrows.mk a', by simp⟩
    · exact ⟨Unit, Unit.fintype, fun _ => Y, fun _ => (𝟙 Y), inferInstance, by simp⟩
    · rcases a with ⟨α, w, Y₁, π, ⟨h₁,h₂⟩⟩
      choose β _ Y_n π_n H using fun a => b (h₂ a)
      exact ⟨(Σ a, β a), inferInstance, fun ⟨a,b⟩ => Y_n a b, fun ⟨a, b⟩ => (π_n a b) ≫ (π a),
        EffectiveEpiFamily.transitive_of_finite _ h₁ _ (fun a => (H a).1),
        fun c => (H c.fst).2 c.snd⟩
  · exact coherentTopology.mem_sieves_of_hasEffectiveEpiFamily S

end CategoryTheory
