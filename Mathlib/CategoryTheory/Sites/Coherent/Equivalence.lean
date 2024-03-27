/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Sites.Coherent.CoherentTopology
import Mathlib.CategoryTheory.Sites.Coherent.RegularTopology
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.EffectiveEpi.Preserves
import Mathlib.CategoryTheory.Sites.Equivalence
/-!

# Coherence and equivalence of categories

This file proves that the coherent and regular topologies transfer nicely along equivalences of
categories.
-/

namespace CategoryTheory

variable {C : Type*} [Category C]

open GrothendieckTopology

namespace Equivalence

variable {D : Type*} [Category D]
variable (e : C ≌ D)

section Coherent

variable [Precoherent C]

/-- `Precoherent` is preserved by equivalence of categories. -/
theorem precoherent : Precoherent D where
  pullback f α _ X₁ π₁ _ := by
    obtain ⟨β, x, X₂', π₂', _, i, ι', h'⟩ :=
      Precoherent.pullback (e.inverse.map f) α (fun i ↦ e.inverse.obj (X₁ i))
      (fun i ↦ (e.inverse.map (π₁ i))) inferInstance
    refine ⟨β, x, _, fun b ↦ e.functor.map (π₂' b) ≫ e.counit.app _, ?_, i,
      fun b ↦ (e.toAdjunction.homEquiv _ _).symm (ι' b), fun b ↦ ?_⟩
    · have : EffectiveEpiFamily _ fun i ↦ (e.functor.map (π₂' i)) :=
        ⟨⟨effectiveEpiFamilyStructOfEquivalence e X₂' π₂'⟩⟩
      infer_instance
    · simpa using congrArg ((fun f ↦ f ≫ e.counit.app _) ∘ e.functor.map) (h' b)

instance [EssentiallySmall C] :
    Precoherent (SmallModel C) := (equivSmallModel C).precoherent

/--
Transferring the coherent topology along an equivalence of categories gives the coherent topology.
-/
theorem precoherent_eq : haveI := precoherent e
    (e.locallyCoverDense (coherentTopology C)).inducedTopology =
    coherentTopology D := by
  ext _ S
  haveI := precoherent e
  simp only [LocallyCoverDense.inducedTopology]
  change (Sieve.functorPushforward e.inverse S) ∈ sieves _ _ ↔ _
  simp only [coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily]
  constructor
  · intro ⟨α, _, Y, π, _, h⟩
    refine ⟨α, inferInstance, _, fun b ↦ e.functor.map (π b) ≫ e.counit.app _, ?_, ?_⟩
    · have : EffectiveEpiFamily _ fun i ↦ (e.functor.map (π i)) :=
        ⟨⟨effectiveEpiFamilyStructOfEquivalence e Y π⟩⟩
      infer_instance
    · intro a
      obtain ⟨_, _, _, h₁, h₂⟩ := h a
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

instance : haveI := precoherent e
    e.TransportsGrothendieckTopology (coherentTopology C) (coherentTopology D) where
  eq_inducedTopology := e.precoherent_eq.symm

variable (A : Type*) [Category A]

/--
Equivalent precoherent categories give equivalent coherent toposes.
-/
@[simps!]
def sheafCongrPrecoherent : haveI := e.precoherent
    Sheaf (coherentTopology C) A ≌ Sheaf (coherentTopology D) A := e.sheafCongr _ _ _

open Presheaf

/--
The coherent sheaf condition can be checked after precomposing with the equivalence.
-/
theorem precoherent_isSheaf_iff (F : Cᵒᵖ ⥤ A) : haveI := e.precoherent
    IsSheaf (coherentTopology C) F ↔ IsSheaf (coherentTopology D) (e.inverse.op ⋙ F) := by
  refine ⟨fun hF ↦ ((e.sheafCongrPrecoherent A).functor.obj ⟨F, hF⟩).cond, fun hF ↦ ?_⟩
  rw [isSheaf_of_iso_iff (P' := e.functor.op ⋙ e.inverse.op ⋙ F)]
  · exact (e.sheafCongrPrecoherent A).inverse.obj ⟨e.inverse.op ⋙ F, hF⟩ |>.cond
  · exact isoWhiskerRight e.op.unitIso F

/--
The coherent sheaf condition on an essentially small site can be checked after precomposing with
the equivalence with a small category.
-/
theorem precoherent_isSheaf_iff_of_essentiallySmall [EssentiallySmall C] (F : Cᵒᵖ ⥤ A) :
    IsSheaf (coherentTopology C) F ↔ IsSheaf (coherentTopology (SmallModel C))
    ((equivSmallModel C).inverse.op ⋙ F) := precoherent_isSheaf_iff _ _ _

end Coherent

section Regular

variable [Preregular C]

/-- `Preregular` is preserved by equivalence of categories. -/
theorem preregular : Preregular D where
  exists_fac f π _ := by
    obtain ⟨W, h', _, i', w⟩ := Preregular.exists_fac (e.inverse.map f) (e.inverse.map π)
    refine ⟨e.functor.obj W, e.functor.map h' ≫ e.counit.app _, inferInstance,
      e.functor.map i' ≫ e.counit.app _, ?_⟩
    simpa using congrArg ((fun f ↦ f ≫ e.counit.app _) ∘ e.functor.map) w

instance [EssentiallySmall C] :
    Preregular (SmallModel C) := (equivSmallModel C).preregular

/--
Transferring the regular topology along an equivalence of categories gives the regular topology.
-/
theorem preregular_eq : haveI := preregular e
    (e.locallyCoverDense (regularTopology C)).inducedTopology =
    regularTopology D := by
  ext _ S
  haveI := preregular e
  simp only [LocallyCoverDense.inducedTopology]
  change (Sieve.functorPushforward e.inverse S) ∈ sieves _ _ ↔ _
  simp only [regularTopology.mem_sieves_iff_hasEffectiveEpi]
  constructor
  · intro ⟨Y, π, _, h⟩
    refine ⟨_, e.functor.map π ≫ e.counit.app _, inferInstance, ?_⟩
    obtain ⟨_, _, _, h₁, h₂⟩ := h
    simp only [h₂, Functor.map_comp, fun_inv_map, Functor.comp_obj, Functor.id_obj,
      Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    rw [← Category.assoc]
    exact Sieve.downward_closed S h₁ _
  · intro ⟨Y, π, _, h⟩
    exact ⟨_, e.unitInv.app _ ≫ e.inverse.map π, inferInstance, Y, π, e.unitInv.app _, h, rfl⟩

instance : haveI := preregular e
    e.TransportsGrothendieckTopology (regularTopology C) (regularTopology D) where
  eq_inducedTopology := e.preregular_eq.symm

variable (A : Type*) [Category A]

/--
Equivalent preregular categories give equivalent regular toposes.
-/
@[simps!]
def sheafCongrPreregular : haveI := e.preregular
    Sheaf (regularTopology C) A ≌ Sheaf (regularTopology D) A := e.sheafCongr _ _ _

open Presheaf

/--
The regular sheaf condition can be checked after precomposing with the equivalence.
-/
theorem preregular_isSheaf_iff (F : Cᵒᵖ ⥤ A) : haveI := e.preregular
    IsSheaf (regularTopology C) F ↔ IsSheaf (regularTopology D) (e.inverse.op ⋙ F) := by
  refine ⟨fun hF ↦ ((e.sheafCongrPreregular A).functor.obj ⟨F, hF⟩).cond, fun hF ↦ ?_⟩
  rw [isSheaf_of_iso_iff (P' := e.functor.op ⋙ e.inverse.op ⋙ F)]
  · exact (e.sheafCongrPreregular A).inverse.obj ⟨e.inverse.op ⋙ F, hF⟩ |>.cond
  · exact isoWhiskerRight e.op.unitIso F

/--
The regular sheaf condition on an essentially small site can be checked after precomposing with
the equivalence with a small category.
-/
theorem preregular_isSheaf_iff_of_essentiallySmall [EssentiallySmall C] (F : Cᵒᵖ ⥤ A) :
    IsSheaf (regularTopology C) F ↔ IsSheaf (regularTopology (SmallModel C))
    ((equivSmallModel C).inverse.op ⋙ F) := preregular_isSheaf_iff _ _ _

end Regular

end Equivalence
