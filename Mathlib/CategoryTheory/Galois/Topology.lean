/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Galois.Prorepresentability
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Basic

/-!

# Topology of fundamental group

In this file we define a natural topology on the automorphism group of a functor
`F : C ⥤ FintypeCat`: It is defined as the subspace topology induced by the natural
embedding of `Aut F` into `∀ X, Aut (F.obj X)` where
`Aut (F.obj X)` carries the discrete topology.

## References

- [Stacks 0BMQ](https://stacks.math.columbia.edu/tag/0BMQ)

-/

@[expose] public section

open Topology

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

/-- `Aut F` is equipped with the topology induced by the embedding into
`∀ X, Aut (F.obj X)`. -/
instance : TopologicalSpace (Aut F) :=
  TopologicalSpace.induced (autEmbedding F) inferInstance

/-lemma autEmbedding_range :
    Set.range (autEmbedding F) =
      ⋂ (f : Arrow C), { a | F.map f.hom ≫ (a f.right).hom = (a f.left).hom ≫ F.map f.hom } := by
  ext a
  simp only [Set.mem_range, id_obj, Set.mem_iInter, Set.mem_setOf_eq]
  refine ⟨fun ⟨σ, h⟩ i ↦ h.symm ▸ σ.hom.naturality i.hom, fun h ↦ ?_⟩
  · use NatIso.ofComponents a (fun {X Y} f ↦ h ⟨X, Y, f⟩)
    rfl-/

/-- The image of `Aut F` in `∀ X, Aut (F.obj X)` are precisely the compatible families of
automorphisms. -/
lemma autEmbedding_range :
    Set.range (autEmbedding F) = ⋂ (f : Arrow C), { a | (F.map f.hom ≫ (a f.right).hom : _ → _) =
      (a f.left).hom ≫ F.map f.hom } := by
  ext a
  simp +instances only [Set.mem_range, DFunLike.coe_fn_eq, Set.mem_iInter, Set.mem_setOf_eq]
  refine ⟨fun ⟨σ, h⟩ i ↦ by cat_disch, fun h ↦ ?_⟩
  exact ⟨NatIso.ofComponents a (fun {X Y} f ↦ by
    ext; simpa using ConcreteCategory.congr_hom (h ⟨X, Y, f⟩) _), rfl⟩

/-- The image of `Aut F` in `∀ X, Aut (F.obj X)` is closed. -/
lemma autEmbedding_range_isClosed : IsClosed (Set.range (autEmbedding F)) := by
  rw [autEmbedding_range]
  exact isClosed_iInter (fun f ↦ isClosed_eq (by fun_prop) (by fun_prop))

lemma autEmbedding_isClosedEmbedding : IsClosedEmbedding (autEmbedding F) where
  eq_induced := rfl
  injective := autEmbedding_injective F
  isClosed_range := autEmbedding_range_isClosed F

instance : CompactSpace (Aut F) := (autEmbedding_isClosedEmbedding F).compactSpace

instance : T2Space (Aut F) :=
  T2Space.of_injective_continuous (autEmbedding_injective F) continuous_induced_dom

instance : TotallyDisconnectedSpace (Aut F) :=
  (autEmbedding_isClosedEmbedding F).isEmbedding.isTotallyDisconnected_range.mp
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)

instance : ContinuousMul (Aut F) :=
  (autEmbedding_isClosedEmbedding F).isInducing.continuousMul (autEmbedding F)

instance : ContinuousInv (Aut F) :=
  (autEmbedding_isClosedEmbedding F).isInducing.continuousInv fun _ ↦ rfl

instance : IsTopologicalGroup (Aut F) := ⟨⟩

instance (X : C) : SMul (Aut (F.obj X)) (F.obj X) := ⟨fun σ a => σ.hom a⟩

instance (X : C) : ContinuousSMul (Aut (F.obj X)) (F.obj X) := by
  constructor
  fun_prop

instance continuousSMul_aut_fiber (X : C) : ContinuousSMul (Aut F) (F.obj X) where
  continuous_smul := by
    let g : Aut (F.obj X) × F.obj X → F.obj X := fun ⟨σ, x⟩ ↦ σ.hom x
    let h (q : Aut F × F.obj X) : Aut (F.obj X) × F.obj X :=
      ⟨((fun p ↦ p X) ∘ autEmbedding F) q.1, q.2⟩
    change Continuous (g ∘ h)
    fun_prop

/-- If `G` is a functor of categories of finite types, the induced map `Aut F → Aut (F ⋙ G)` is
continuous. -/
lemma continuous_mapAut_whiskeringRight (G : FintypeCat.{w} ⥤ FintypeCat.{v}) :
    Continuous (((whiskeringRight _ _ _).obj G).mapAut F) := by
  rw [Topology.IsInducing.continuous_iff (autEmbedding_isClosedEmbedding _).isInducing,
    continuous_pi_iff]
  intro X
  change Continuous fun a ↦ G.mapAut (F.obj X) (autEmbedding F a X)
  fun_prop

/-- If `G` is a fully faithful functor of categories of finite types, this is the isomorphism of
topological groups `Aut F ≃ₜ* Aut (F ⋙ G)`. -/
noncomputable def autEquivAutWhiskerRight {G : FintypeCat.{w} ⥤ FintypeCat.{v}}
    (h : G.FullyFaithful) :
    Aut F ≃ₜ* Aut (F ⋙ G) where
  __ := (h.whiskeringRight C).autMulEquivOfFullyFaithful F
  continuous_toFun := continuous_mapAut_whiskeringRight F G
  continuous_invFun := Continuous.continuous_symm_of_equiv_compact_to_t2
    (f := ((h.whiskeringRight C).autMulEquivOfFullyFaithful F).toEquiv)
    (continuous_mapAut_whiskeringRight F G)

variable [GaloisCategory C] [FiberFunctor F]

set_option backward.isDefEq.respectTransparency false in
/--
If `H` is an open subset of `Aut F` such that `1 ∈ H`, there exists a finite
set `I` of connected objects of `C` such that every `σ : Aut F` that induces the identity
on `F.obj X` for all `X ∈ I` is contained in `H`. In other words: The kernel
of the evaluation map `Aut F →* ∏ X : I ↦ Aut (F.obj X)` is contained in `H`.
-/
lemma exists_set_ker_evaluation_subset_of_isOpen
    {H : Set (Aut F)} (h1 : 1 ∈ H) (h : IsOpen H) :
    ∃ (I : Set C) (_ : Fintype I), (∀ X ∈ I, IsConnected X) ∧
      (∀ σ : Aut F, (∀ X : I, σ.hom.app X = 𝟙 (F.obj X)) → σ ∈ H) := by
  obtain ⟨U, hUopen, rfl⟩ := isOpen_induced_iff.mp h
  obtain ⟨I, u, ho, ha⟩ := isOpen_pi_iff.mp hUopen 1 h1
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

open Limits

/-- The stabilizers of points in the fibers of Galois objects form a neighbourhood basis
of the identity in `Aut F`. -/
lemma nhds_one_has_basis_stabilizers : (nhds (1 : Aut F)).HasBasis (fun _ ↦ True)
    (fun X : PointedGaloisObject F ↦ MulAction.stabilizer (Aut F) X.pt) where
  mem_iff' S := by
    rw [mem_nhds_iff]
    refine ⟨?_, ?_⟩
    · intro ⟨U, hU, hUopen, hUone⟩
      obtain ⟨I, _, hc, hmem⟩ := exists_set_ker_evaluation_subset_of_isOpen F hUone hUopen
      let P : C := ∏ᶜ fun X : I ↦ X.val
      obtain ⟨A, a, hgal, hbij⟩ := exists_galois_representative F P
      refine ⟨⟨A, a, hgal⟩, trivial, ?_⟩
      intro t (ht : t.hom.app A a = a)
      apply hU
      apply hmem
      haveI (X : I) : IsConnected X.val := hc X.val X.property
      haveI (X : I) : Nonempty (F.obj X.val) := nonempty_fiber_of_isConnected F X
      intro X
      ext x
      simp only [FintypeCat.id_apply]
      obtain ⟨z, rfl⟩ :=
        surjective_of_nonempty_fiber_of_isConnected F (Pi.π (fun X : I ↦ X.val) X) x
      obtain ⟨f, rfl⟩ := hbij.surjective z
      rw [FunctorToFintypeCat.naturality, FunctorToFintypeCat.naturality, ht]
    · intro ⟨X, _, h⟩
      exact ⟨MulAction.stabilizer (Aut F) X.pt, h, stabilizer_isOpen (Aut F) X.pt,
        Subgroup.one_mem _⟩

end PreGaloisCategory

end CategoryTheory
