/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Limits.FintypeCat
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.CategoryTheory.Galois.Decomposition

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
      { a | ∀ (X Y : C) (f : X ⟶ Y), F.map f ≫ (a Y).hom = (a X).hom ≫ F.map f } := by
  ext a
  simp only [Set.mem_range, Set.mem_setOf_eq]
  constructor
  · intro ⟨σ, h⟩
    rw [← h]
    exact σ.hom.naturality
  · intro h
    use NatIso.ofComponents (fun X => (a X))
    rfl

/-- The image of `Aut F` in `∀ X, Aut (F.obj X)` is closed. -/
lemma autEmbedding_range_isClosed : IsClosed (Set.range (autEmbedding F)) := by
  rw [autEmbedding_range, ← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro a h
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_forall] at h
  obtain ⟨X, Y, f, (h : (a Y).hom ∘ F.map f ≠ F.map f ∘ (a X).hom)⟩ := h
  rw [Function.ne_iff] at h
  obtain ⟨x, hx⟩ := h
  let sx (A : C) : Set (Aut (F.obj A)) :=
    { γ | ∀ (h : X ⟶ A), γ.hom (F.map h x) = (a A).hom (F.map h x) }
  let sy (A : C) : Set (Aut (F.obj A)) :=
    { γ | ∀ (h : Y ⟶ A), γ.hom (F.map h (F.map f x)) = (a A).hom (F.map h (F.map f x)) }
  have hx : IsOpen (Set.pi {X} sx) := isOpen_set_pi (Set.toFinite {X}) (fun _ _ ↦ trivial)
  have hy : IsOpen (Set.pi {Y} sy) := isOpen_set_pi (Set.toFinite {Y}) (fun _ _ ↦ trivial)
  use Set.pi {X} sx ∩ Set.pi {Y} sy
  refine ⟨?_, IsOpen.inter hx hy, ?_⟩
  · intro γ hγ
    simp only [Set.singleton_pi] at hγ
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_forall]
    use X, Y, f
    rw [← ne_eq, Function.ne_iff]
    use x
    simp only [FintypeCat.comp_apply]
    have hty : (γ Y).hom (F.map f x) = (a Y).hom (F.map f x) := by simpa using hγ.2 (𝟙 Y)
    have htx : (γ X).hom x = (a X).hom x := by simpa using hγ.1 (𝟙 X)
    rwa [htx, hty]
  · simp [sx, sy]

lemma autEmbedding_closedEmbedding : ClosedEmbedding (autEmbedding F) where
  induced := rfl
  inj := autEmbedding_injective F
  isClosed_range := autEmbedding_range_isClosed F

instance (X Y : C) : Finite (F.obj X ⟶ F.obj Y) :=
  inferInstanceAs <| Finite (F.obj X → F.obj Y)

instance (X : C) : Finite (Aut (F.obj X)) :=
  Finite.of_injective _ (fun _ _ h ↦ Iso.ext h)

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

instance continuousSMul_aut_fiber (X : C) : ContinuousSMul (Aut F) (F.obj X) where
  continuous_smul := by
    let g : Aut (F.obj X) × F.obj X → F.obj X := fun ⟨σ, x⟩ ↦ σ.hom x
    let h (q : Aut F × F.obj X) : Aut (F.obj X) × F.obj X :=
      ⟨((fun p ↦ p X) ∘ autEmbedding F) q.1, q.2⟩
    show Continuous (g ∘ h)
    fun_prop

variable [GaloisCategory C] [FiberFunctor F]

/--
If `H` is an open subset of `Aut F` such that `1 ∈ H`, there exists a finite
set `I` of connected objects of `C` such that every `σ : Aut F` that induces the identity
on `F.obj X` for all `X ∈ I` is contained in `H`. In other words: The kernel
of the evaluation map `Aut F →* ∏ X : I ↦ Aut (F.obj X)` is contained in `H`.
-/
lemma exists_set_ker_evaluation_subset_of_isOpen {H : Set (Aut F)} (hone : 1 ∈ H)
    (h : IsOpen H) : ∃ (I : Set C) (_ : Fintype I), (∀ X ∈ I, IsConnected X) ∧
    (∀ σ : Aut F, (∀ X : I, σ.hom.app X = 𝟙 (F.obj X)) → σ ∈ H) := by
  obtain ⟨U, hUopen, rfl⟩ := isOpen_induced_iff.mp h
  obtain ⟨I, u, ho, ha⟩ := isOpen_pi_iff.mp hUopen 1 hone
  choose fι ff fc h4 h5 h6 using (fun X : I => has_decomp_connected_components X.val)
  refine ⟨⋃ X, Set.range (ff X), Fintype.ofFinite _, ?_, ?_⟩
  · rintro X ⟨A, ⟨Y, rfl⟩, hA2⟩
    obtain ⟨i, rfl⟩ := hA2
    exact h5 Y i
  · refine fun σ h ↦ ha (fun X XinI ↦ ?_)
    suffices h : autEmbedding F σ X = 1 by
      rw [h]
      exact (ho X XinI).right
    have h : σ.hom.app X = 𝟙 (F.obj X) := by
      have : Fintype (fι ⟨X, XinI⟩) := Fintype.ofFinite _
      ext x
      obtain ⟨⟨j⟩, a, ha : F.map _ a = x⟩ := Limits.FintypeCat.jointly_surjective
        (Discrete.functor (ff ⟨X, XinI⟩) ⋙ F) _ (Limits.isColimitOfPreserves F (h4 ⟨X, XinI⟩)) x
      rw [FintypeCat.id_apply, ← ha, FunctorToFintypeCat.naturality]
      simp [h ⟨(ff _) j, ⟨Set.range (ff ⟨X, XinI⟩), ⟨⟨_, rfl⟩, ⟨j, rfl⟩⟩⟩⟩]
    exact Iso.ext h

end PreGaloisCategory

end CategoryTheory
