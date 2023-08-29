/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/

import Mathlib.CategoryTheory.Sites.Canonical
import Mathlib.CategoryTheory.Sites.Coverage
import Mathlib.CategoryTheory.Sites.EffectiveEpimorphic
import Mathlib.Data.Fintype.Sigma
/-!

# The Coherent Grothendieck Topology

This file defines the coherent Grothendieck topology (and coverage) on a category `C`.
The category `C` must satisfy a `Precoherent C` condition, which is essentially the minimal
requirement for the coherent coverage to exist.
Given such a category, the coherent coverage is `coherentCoverage C` and the corresponding
Grothendieck topology is `coherentTopology C`.

In `isSheaf_coherent`, we characterize the sheaf condition for presheaves of types for the
coherent Grothendieck topology in terms of finite effective epimorphic families.

## References:
- [Elephant]: *Sketches of an Elephant*, P. T. Johnstone: C2.1, Example 2.1.12.
- [nLab, *Coherent Coverage*](https://ncatlab.org/nlab/show/coherent+coverage)

-/

set_option autoImplicit true

namespace CategoryTheory

open Limits

variable (C : Type*) [Category C]

/--
The condition `Precoherent C` is essentially the minimal condition required to define the
coherent coverage on `C`.
-/
class Precoherent : Prop where
  /--
  Given an effective epi family `π₁` over `B₁` and a morphism `f : B₂ ⟶ B₁`, there exists
  an effective epi family `π₂` over `B₂`, such that `π₂` factors through `π₁`.
  -/
  pullback {B₁ B₂ : C} (f : B₂ ⟶ B₁) :
    ∀ (α : Type) [Fintype α] (X₁ : α → C) (π₁ : (a : α) → (X₁ a ⟶ B₁)),
      EffectiveEpiFamily X₁ π₁ →
    ∃ (β : Type) (_ : Fintype β) (X₂ : β → C) (π₂ : (b : β) → (X₂ b ⟶ B₂)),
      EffectiveEpiFamily X₂ π₂ ∧
      ∃ (i : β → α) (ι : (b :  β) → (X₂ b ⟶ X₁ (i b))),
      ∀ (b : β), ι b ≫ π₁ _ = π₂ _ ≫ f

/--
The coherent coverage on a precoherent category `C`.
-/
def coherentCoverage [Precoherent C] : Coverage C where
  covering B := { S | ∃ (α : Type) (_ : Fintype α) (X : α → C) (π : (a : α) → (X a ⟶ B)),
    S = Presieve.ofArrows X π ∧ EffectiveEpiFamily X π }
  pullback := by
    rintro B₁ B₂ f S ⟨α, _, X₁, π₁, rfl, hS⟩
    -- ⊢ ∃ T, T ∈ (fun B => {S | ∃ α x X π, S = Presieve.ofArrows X π ∧ EffectiveEpiF …
    obtain ⟨β,_,X₂,π₂,h,i,ι,hh⟩ := Precoherent.pullback f α X₁ π₁ hS
    -- ⊢ ∃ T, T ∈ (fun B => {S | ∃ α x X π, S = Presieve.ofArrows X π ∧ EffectiveEpiF …
    refine ⟨Presieve.ofArrows X₂ π₂, ⟨β, inferInstance, X₂, π₂, rfl, h⟩, ?_⟩
    -- ⊢ Presieve.FactorsThruAlong (Presieve.ofArrows X₂ π₂) (Presieve.ofArrows X₁ π₁ …
    rintro _ _ ⟨b⟩
    -- ⊢ ∃ W i e, Presieve.ofArrows X₁ π₁ e ∧ i ≫ e = π₂ b ≫ f
    refine ⟨(X₁ (i b)), ι _, π₁ _, ⟨_⟩, hh _⟩
    -- 🎉 no goals

/--
The coherent Grothendieck topology on a precoherent category `C`.
-/
def coherentTopology [Precoherent C] : GrothendieckTopology C :=
  Coverage.toGrothendieck _ <| coherentCoverage C

lemma isSheaf_coherent [Precoherent C] (P : Cᵒᵖ ⥤ Type w) :
    Presieve.IsSheaf (coherentTopology C) P ↔
    (∀ (B : C) (α : Type) [Fintype α] (X : α → C) (π : (a : α) → (X a ⟶ B)),
      EffectiveEpiFamily X π → (Presieve.ofArrows X π).IsSheafFor P) := by
  constructor
  -- ⊢ Presieve.IsSheaf (coherentTopology C) P → ∀ (B : C) (α : Type) [inst : Finty …
  · intro hP B α _ X π h
    -- ⊢ Presieve.IsSheafFor P (Presieve.ofArrows X π)
    simp only [coherentTopology, Presieve.isSheaf_coverage] at hP
    -- ⊢ Presieve.IsSheafFor P (Presieve.ofArrows X π)
    apply hP
    -- ⊢ Presieve.ofArrows X π ∈ Coverage.covering (coherentCoverage C) B
    refine ⟨α, inferInstance, X, π, rfl, h⟩
    -- 🎉 no goals
  · intro h
    -- ⊢ Presieve.IsSheaf (coherentTopology C) P
    simp only [coherentTopology, Presieve.isSheaf_coverage]
    -- ⊢ ∀ {X : C} (R : Presieve X), R ∈ Coverage.covering (coherentCoverage C) X → P …
    rintro B S ⟨α, _, X, π, rfl, hS⟩
    -- ⊢ Presieve.IsSheafFor P (Presieve.ofArrows X π)
    exact h _ _ _ _ hS
    -- 🎉 no goals


namespace coherentTopology

variable {C : Type*} [Category C] [Precoherent C]

variable {X : C}
/--
For a precoherent category, any sieve that contains an `EffectiveEpiFamily` is a sieve of the
coherent topology.
Note: This is one direction of `mem_sieves_iff_hasEffectiveEpiFamily`, but is needed for the proof.
-/
theorem mem_sieves_of_hasEffectiveEpiFamily (S : Sieve X) :
    (∃ (α : Type) (_ : Fintype α) (Y : α → C) (π : (a : α) → (Y a ⟶ X)),
        EffectiveEpiFamily Y π ∧ (∀ a : α, (S.arrows) (π a)) ) →
          (S ∈ GrothendieckTopology.sieves (coherentTopology C) X) := by
  rintro ⟨α, ⟨h, ⟨Y, ⟨π, hπ⟩⟩⟩⟩
  -- ⊢ S ∈ GrothendieckTopology.sieves (coherentTopology C) X
  have h_le : Sieve.generate (Presieve.ofArrows _ π) ≤ S := by
    rw [Sieve.sets_iff_generate (Presieve.ofArrows _ π) S]
    apply Presieve.le_of_factorsThru_sieve (Presieve.ofArrows (fun i => Y i) π) S _
    intro W g f
    use W, 𝟙 W
    rcases f with ⟨i⟩
    exact ⟨π i, ⟨hπ.2 i,Category.id_comp (π i) ⟩⟩
  apply Coverage.saturate_of_superset (coherentCoverage C) h_le
  -- ⊢ Coverage.saturate (coherentCoverage C) X (Sieve.generate (Presieve.ofArrows  …
  exact Coverage.saturate.of X _ ⟨α, inferInstance, Y, π, ⟨rfl, hπ.1⟩⟩
  -- 🎉 no goals

/-- Every Yoneda-presheaf is a sheaf for the coherent topology. -/
theorem isSheaf_yoneda_obj (W : C) : Presieve.IsSheaf (coherentTopology C) (yoneda.obj W) := by
  rw [isSheaf_coherent]
  -- ⊢ ∀ (B : C) (α : Type) [inst : Fintype α] (X : α → C) (π : (a : α) → X a ⟶ B), …
  intro X α _ Y π H
  -- ⊢ Presieve.IsSheafFor (yoneda.obj W) (Presieve.ofArrows Y π)
  have h_colim := isColimitOfEffectiveEpiFamilyStruct Y π H.effectiveEpiFamily.some
  -- ⊢ Presieve.IsSheafFor (yoneda.obj W) (Presieve.ofArrows Y π)
  rw [←Sieve.generateFamily_eq] at h_colim
  -- ⊢ Presieve.IsSheafFor (yoneda.obj W) (Presieve.ofArrows Y π)
  intro x hx
  -- ⊢ ∃! t, Presieve.FamilyOfElements.IsAmalgamation x t
  let x_ext := Presieve.FamilyOfElements.sieveExtend x
  -- ⊢ ∃! t, Presieve.FamilyOfElements.IsAmalgamation x t
  have hx_ext := Presieve.FamilyOfElements.Compatible.sieveExtend hx
  -- ⊢ ∃! t, Presieve.FamilyOfElements.IsAmalgamation x t
  let S := Sieve.generate (Presieve.ofArrows Y π)
  -- ⊢ ∃! t, Presieve.FamilyOfElements.IsAmalgamation x t
  obtain ⟨t, t_amalg, t_uniq⟩ : ∃! t, x_ext.IsAmalgamation t :=
    (Sieve.forallYonedaIsSheaf_iff_colimit S).mpr ⟨h_colim⟩ W x_ext hx_ext
  refine ⟨t, ?_, ?_⟩
  -- ⊢ (fun t => Presieve.FamilyOfElements.IsAmalgamation x t) t
  · convert Presieve.isAmalgamation_restrict (Sieve.le_generate (Presieve.ofArrows Y π)) _ _ t_amalg
    -- ⊢ x = Presieve.FamilyOfElements.restrict (_ : Presieve.ofArrows Y π ≤ (Sieve.g …
    exact (Presieve.restrict_extend hx).symm
    -- 🎉 no goals
  · exact fun y hy ↦ t_uniq y <| Presieve.isAmalgamation_sieveExtend x y hy
    -- 🎉 no goals

/-- The coherent topology on a precoherent category is subcanonical. -/
theorem isSubcanonical : Sheaf.Subcanonical (coherentTopology C) :=
  Sheaf.Subcanonical.of_yoneda_isSheaf _ isSheaf_yoneda_obj

end coherentTopology

variable {C : Type*} [Category C] [Precoherent C]

variable {X : C}

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
  -- ⊢ Presieve.EffectiveEpimorphic (Presieve.ofArrows (fun c => Y_n c.fst c.snd) f …
  suffices h₂ : (Sieve.generate (Presieve.ofArrows (fun (⟨a, b⟩ : Σ _, β _) => Y_n a b)
        (fun ⟨a,b⟩ => π_n a b ≫ π a))) ∈ GrothendieckTopology.sieves (coherentTopology C) X by
    change Nonempty _
    rw [← Sieve.forallYonedaIsSheaf_iff_colimit]
    exact fun W => coherentTopology.isSheaf_yoneda_obj W _ h₂
  let h' := h
  -- ⊢ Sieve.generate
  rw [← Sieve.effectiveEpimorphic_family] at h'
  -- ⊢ Sieve.generate
  let H' := H
  -- ⊢ Sieve.generate
  conv at H' =>
    intro a
    rw [← Sieve.effectiveEpimorphic_family]
  -- Show that a covering sieve is a colimit, which implies the original set of arrows is regular
  -- epimorphic. We use the transitivity property of saturation
  apply Coverage.saturate.transitive X (Sieve.generate (Presieve.ofArrows Y π))
  · apply Coverage.saturate.of
    -- ⊢ Presieve.ofArrows Y π ∈ Coverage.covering (coherentCoverage C) X
    use α, inferInstance, Y, π
    -- 🎉 no goals
  · intro V f ⟨Y₁, h, g, ⟨hY, hf⟩⟩
    -- ⊢ Coverage.saturate (coherentCoverage C) V
    rw [← hf, Sieve.pullback_comp]
    -- ⊢ Coverage.saturate (coherentCoverage C) V
    apply (coherentTopology C).pullback_stable'
    -- ⊢ Sieve.pullback g
    apply coherentTopology.mem_sieves_of_hasEffectiveEpiFamily
    -- ⊢ ∃ α_1 x Y_1 π_1,
    -- Need to show that the pullback of the family `π_n` to a given `Y i` is effective epimorphic
    rcases hY with ⟨i⟩
    -- ⊢ ∃ α_1 x Y π_1,
    use β i, inferInstance, Y_n i, π_n i, H i
    -- ⊢ ∀ (a : β i),
    intro b
    -- ⊢ (Sieve.pullback (π i)
    use Y_n i b, (𝟙 _), π_n i b ≫ π i, ⟨(⟨i, b⟩ : Σ (i : α), β i)⟩
    -- ⊢ 𝟙 (Y_n i b) ≫ π_n i b ≫ π i = π_n i b ≫ π i
    exact Category.id_comp (π_n i b ≫ π i)
    -- 🎉 no goals

/--
A sieve belongs to the coherent topology if and only if it contains a finite
`EffectiveEpiFamily`.
-/
theorem coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily (S : Sieve X) :
(S ∈ GrothendieckTopology.sieves (coherentTopology C) X) ↔
    (∃ (α : Type) (_ : Fintype α) (Y : α → C) (π : (a : α) → (Y a ⟶ X)),
        EffectiveEpiFamily Y π ∧ (∀ a : α, (S.arrows) (π a)) )  := by
  constructor
  -- ⊢ S ∈ GrothendieckTopology.sieves (coherentTopology C) X → ∃ α x Y π, Effectiv …
  · intro h
    -- ⊢ ∃ α x Y π, EffectiveEpiFamily Y π ∧ ∀ (a : α), S.arrows (π a)
    induction' h with Y T hS Y Y R S _ _ a b
    · rcases hS with ⟨a, h, Y', π, h'⟩
      -- ⊢ ∃ α x Y_1 π, EffectiveEpiFamily Y_1 π ∧ ∀ (a : α), (Sieve.generate T).arrows …
      use a, h, Y', π, by tauto
      -- ⊢ ∀ (a : a), (Sieve.generate T).arrows (π a)
      intro a'
      -- ⊢ (Sieve.generate T).arrows (π a')
      rcases h' with ⟨rfl, _⟩
      -- ⊢ (Sieve.generate (Presieve.ofArrows Y' π)).arrows (π a')
      simp only [Sieve.generate_apply]
      -- ⊢ ∃ Y_1 h g, Presieve.ofArrows Y' π g ∧ h ≫ g = π a'
      use Y' a', 𝟙 Y' a', π a', Presieve.ofArrows.mk a'
      -- ⊢ 𝟙 Y' a' ≫ π a' = π a'
      apply Category.id_comp
      -- 🎉 no goals
    · use Unit, Unit.fintype, fun _ => Y, fun _ => (𝟙 Y)
      -- ⊢ (EffectiveEpiFamily (fun x => Y) fun x => 𝟙 Y) ∧ (Unit → ⊤.arrows (𝟙 Y))
      cases' S with arrows downward_closed
      -- ⊢ (EffectiveEpiFamily (fun x => Y) fun x => 𝟙 Y) ∧ ∀ (a : Unit), ⊤.arrows ((fu …
      exact ⟨inferInstance, by simp only [Sieve.top_apply, forall_const]⟩
      -- 🎉 no goals
    · rcases a with ⟨α, w, Y₁, π, ⟨h₁,h₂⟩⟩
      -- ⊢ ∃ α x Y_1 π, EffectiveEpiFamily Y_1 π ∧ ∀ (a : α), S.arrows (π a)
      choose β _ Y_n π_n H using fun a => b (h₂ a)
      -- ⊢ ∃ α x Y_1 π, EffectiveEpiFamily Y_1 π ∧ ∀ (a : α), S.arrows (π a)
      use (Σ a, β a), inferInstance, fun ⟨a,b⟩ => Y_n a b, fun ⟨a, b⟩ => (π_n a b) ≫ (π a)
      -- ⊢ (EffectiveEpiFamily
      constructor
      · exact EffectiveEpiFamily.transitive_of_finite _ h₁ _ (fun a => (H a).1)
        -- 🎉 no goals
      · exact fun c => (H c.fst).2 c.snd
        -- 🎉 no goals
  · exact coherentTopology.mem_sieves_of_hasEffectiveEpiFamily S
    -- 🎉 no goals

end CategoryTheory
