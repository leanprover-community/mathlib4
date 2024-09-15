/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.Topology.Algebra.Group.Basic

/-!

# Topology of fundamental group

In this file we define a natural topology on the automorphism group of a functor
`F : C ⥤ FintypeCat`: It is defined as the subspace topology induced by the natural
embedding of `Aut F` into `∀ X, Aut (F.obj X)` where
`Aut (F.obj X)` carries the discrete topology.

## References

- Stacks Project: Tag 0BMQ

-/
universe u₁ u₂ v₁ v₂ v w

namespace CategoryTheory

namespace PreGaloisCategory

open Functor

variable {C : Type u₁} [Category.{u₂} C] (F : C ⥤ FintypeCat.{w})

/-- For a functor `F : C ⥤ FintypeCat`, the canonical embedding of `Aut F` into
the product over `Aut (F.obj X)` for all objects `X`. -/
def autEmbedding : Aut F →* ∀ X, Aut (F.obj X) :=
  MonoidHom.mk' (fun σ X ↦ σ.app X) (fun _ _ ↦ rfl)

@[simp]
lemma autEmbedding_apply (σ : Aut F) (X : C) : autEmbedding F σ X = σ.app X :=
  rfl

lemma autEmbedding_injective : Function.Injective (autEmbedding F) := by
  intro σ τ h
  ext X x
  have : σ.app X = τ.app X := congr_fun h X
  rw [← Iso.app_hom, ← Iso.app_hom, this]

/-- We put the discrete topology on `F.obj X`. -/
scoped instance (X : C) : TopologicalSpace (F.obj X) := ⊥

@[scoped instance]
lemma obj_discreteTopology (X : C) : DiscreteTopology (F.obj X) := ⟨rfl⟩

/-- We put the discrete topology on `Aut (F.obj X)`. -/
scoped instance (X : C) : TopologicalSpace (Aut (F.obj X)) := ⊥

@[scoped instance]
lemma aut_discreteTopology (X : C) : DiscreteTopology (Aut (F.obj X)) := ⟨rfl⟩

/-- `Aut F` is equipped with the by the embedding into `∀ X, Aut (F.obj X)` induced embedding. -/
instance : TopologicalSpace (Aut F) :=
  TopologicalSpace.induced (autEmbedding F) inferInstance

/-- The image of `Aut F` in `∀ X, Aut (F.obj X)` are precisely the compatible families of
automorphisms. -/
lemma autEmbedding_range :
    Set.range (autEmbedding F) =
      ⋂ (f : Arrow C), { a | F.map f.hom ≫ (a f.right).hom = (a f.left).hom ≫ F.map f.hom } := by
  ext a
  simp only [Set.mem_range, id_obj, Set.mem_iInter, Set.mem_setOf_eq]
  refine ⟨fun ⟨σ, h⟩ i ↦ h.symm ▸ σ.hom.naturality i.hom, fun h ↦ ?_⟩
  · use NatIso.ofComponents (fun X => a X) (fun {X Y} f ↦ h ⟨X, Y, f⟩)
    rfl

/-- The image of `Aut F` in `∀ X, Aut (F.obj X)` is closed. -/
lemma autEmbedding_range_isClosed : IsClosed (Set.range (autEmbedding F)) := by
  rw [autEmbedding_range]
  refine isClosed_iInter (fun f ↦ isClosed_eq (X := F.obj f.left → F.obj f.right) ?_ ?_)
  · fun_prop
  · fun_prop

lemma autEmbedding_closedEmbedding : ClosedEmbedding (autEmbedding F) where
  induced := rfl
  inj := autEmbedding_injective F
  isClosed_range := autEmbedding_range_isClosed F

instance : CompactSpace (Aut F) := ClosedEmbedding.compactSpace (autEmbedding_closedEmbedding F)

instance : T2Space (Aut F) :=
  T2Space.of_injective_continuous (autEmbedding_injective F) continuous_induced_dom

instance : TotallyDisconnectedSpace (Aut F) :=
  (Embedding.isTotallyDisconnected_range (autEmbedding_closedEmbedding F).embedding).mp
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)

instance : ContinuousMul (Aut F) :=
  Inducing.continuousMul (autEmbedding F)
    (autEmbedding_closedEmbedding F).toInducing

instance : ContinuousInv (Aut F) :=
  Inducing.continuousInv (autEmbedding_closedEmbedding F).toInducing (fun _ ↦ rfl)

instance : TopologicalGroup (Aut F) := ⟨⟩

instance (X : C) : SMul (Aut (F.obj X)) (F.obj X) := ⟨fun σ a => σ.hom a⟩

instance (X : C) : ContinuousSMul (Aut (F.obj X)) (F.obj X) := by
  constructor
  fun_prop

end PreGaloisCategory

end CategoryTheory
