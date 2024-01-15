import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.RegularExtensive

universe u

namespace CategoryTheory

open GrothendieckTopology

variable {C : Type*} [Category C]
variable [Precoherent C]

namespace Equivalence

variable {D : Type*} [Category D]
variable (e : C ≌ D)

theorem precoherent : Precoherent D where
  pullback f α _ X₁ π₁ _ := by
    have : EffectiveEpiFamily _ fun i ↦ (e.inverse.map (π₁ i)) :=
      ⟨⟨effectiveEpiFamilyStructOfEquivalence e.symm X₁ π₁⟩⟩
    obtain ⟨β, x, X₂', π₂', _, i, ι', h'⟩ :=
      Precoherent.pullback (e.inverse.map f) α (fun i ↦ e.inverse.obj (X₁ i))
      (fun i ↦ (e.inverse.map (π₁ i))) this
    refine ⟨β, x, _, fun b ↦ e.functor.map (π₂' b) ≫ e.counit.app _, ?_, i,
      fun b ↦ (e.toAdjunction.homEquiv _ _).symm (ι' b), fun b ↦ ?_⟩
    · have : EffectiveEpiFamily _ fun i ↦ (e.functor.map (π₂' i)) :=
        ⟨⟨effectiveEpiFamilyStructOfEquivalence e X₂' π₂'⟩⟩
      infer_instance
    · simpa using congrArg ((fun f ↦ f ≫ e.counit.app _) ∘ e.functor.map) (h' b)

theorem precoherent_eq :
    haveI := precoherent e
    (e.locallyCoverDense (coherentTopology C)).inducedTopology =
    coherentTopology D := by
  ext d S
  haveI := precoherent e
  simp only [LocallyCoverDense.inducedTopology]
  change ((Sieve.functorPushforward e.inverse S) ∈ sieves _ _) ↔ _
  simp only [coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily]
  constructor
  · intro ⟨α, _, Y, π, _, h⟩
    refine ⟨α, inferInstance, _, fun b ↦ e.functor.map (π b) ≫ e.counit.app _, ?_, ?_⟩
    · have : EffectiveEpiFamily _ fun i ↦ (e.functor.map (π i)) :=
        ⟨⟨effectiveEpiFamilyStructOfEquivalence e Y π⟩⟩
      infer_instance
    · intro a
      obtain ⟨d', g₁, g₂, h₁, h₂⟩ := h a
      simp only [h₂, Functor.map_comp, fun_inv_map, Functor.comp_obj, Functor.id_obj,
        Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
      rw [← Category.assoc]
      exact Sieve.downward_closed S h₁ _
  · intro ⟨α, _, Y, π, _, h⟩
    refine ⟨α, inferInstance, _, fun b ↦ e.unitInv.app _ ≫ e.inverse.map (π b), ?_, ?_⟩
    · have : EffectiveEpiFamily (fun a ↦ (𝟭 C).obj _) fun i ↦ (e.inverse.map (π i)) :=
        ⟨⟨effectiveEpiFamilyStructOfEquivalence e.symm Y π⟩⟩
      infer_instance
    · exact fun a ↦ ⟨Y a, π a, e.unitInv.app _, h a, rfl⟩

end Equivalence

instance [EssentiallySmall C] : Precoherent (SmallModel C) := (equivSmallModel C).precoherent
