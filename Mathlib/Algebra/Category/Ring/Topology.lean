/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Christian Merten
-/
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Topology.Algebra.Ring.Basic

/-!
# Topology on `Hom(R, S)`

In this file, we define topology on `Hom(R, S)` for a topological ring `S`,
given by the coarsest topology that makes `f ↦ f x` continuous for all `x : R`.
Alternatively, given a presentation `R = ℤ[x₁,...,xₙ]/I`,
this is the subspace topology `Hom(R, S) ↪ Hom(ℤ[x₁,...,xₙ], S) = Sⁿ`.

## Main results
- `CommRingCat.HomTopology.isClosedEmbedding_precomp_of_surjective`:
  `Hom(R/I, T)` is a closed subspace of `Hom(R, T)` if `T` is Hausdorff.
- `CommRingCat.HomTopology.mvPolynomialHomeo`:
  `Hom(S[Xᵢ], R)` is homeomorphic to `Hom(S, R) × Rⁱ`.
- `CommRingCat.HomTopology.isEmbedding_pushout`:
  `Hom(A ⊗[S] B, R)` has the subspace topology from `Hom(A, R) × Hom(B, R)`.

-/

universe u v

open CategoryTheory Topology

namespace CommRingCat.HomTopology

variable {A B R S T : CommRingCat.{u}}

/--
The topology on `Hom(R, S)` for a topological ring `S`, given by the coarsest topology that
makes `f ↦ f x` continuous for all `x : R` (see `continuous_apply`).
Alternatively, given a presentation `R = ℤ[x₁,...,xₙ]/I`,
This is the subspace topology `Hom(R, S) ↪ Hom(ℤ[x₁,...,xₙ], S) = Sⁿ` (see `mvPolynomialHomeo`).

This is a scoped instance in `CommRingCat.HomTopology`.
-/
scoped instance [TopologicalSpace S] : TopologicalSpace (R ⟶ S) :=
  .induced (fun f ↦ f.hom : _ → R → S) inferInstance

@[fun_prop]
nonrec lemma continuous_apply [TopologicalSpace S] (x : R) :
    Continuous (fun f : R ⟶ S ↦ f.hom x) :=
  (continuous_apply x).comp continuous_induced_dom

@[fun_prop]
lemma continuous_precomp [TopologicalSpace T] (f : R ⟶ S) :
    Continuous ((f ≫ ·) : (S ⟶ T) → (R ⟶ T)) :=
  continuous_induced_rng.mpr ((Pi.continuous_precomp f.hom).comp continuous_induced_dom)

/-- If `R ≅ S`, then `Hom(R, T)` is homeomorphc to `Hom(S, T)`. -/
@[simps]
def precompHomeo [TopologicalSpace T] (f : R ≅ S) :
    (S ⟶ T) ≃ₜ (R ⟶ T) where
  continuous_toFun := continuous_precomp f.hom
  continuous_invFun := continuous_precomp f.inv
  left_inv _ := by simp
  right_inv _ := by simp

lemma isHomeomorph_precomp [TopologicalSpace T] (f : R ⟶ S) [IsIso f] :
    IsHomeomorph ((f ≫ ·) : (S ⟶ T) → (R ⟶ T)) :=
  (precompHomeo (asIso f)).isHomeomorph

/-- `Hom(R/I, T)` has the subspace topology of `Hom(R, T)`. -/
lemma isEmbedding_precomp_of_surjective
    [TopologicalSpace T] (f : R ⟶ S) (hf : Function.Surjective f) :
    Topology.IsEmbedding ((f ≫ ·) : (S ⟶ T) → (R ⟶ T)) := by
  refine IsEmbedding.of_comp (continuous_precomp _) (IsInducing.induced _).continuous ?_
  suffices IsEmbedding ((· ∘ f.hom) : (S → T) → (R → T)) from
    this.comp (.induced (fun f g e ↦ by ext a; exact congr($e a)))
  exact Function.Surjective.isEmbedding_comp _ hf

/-- `Hom(R/I, T)` is a closed subspace of `Hom(R, T)` if `T` is T1. -/
lemma isClosedEmbedding_precomp_of_surjective
    [TopologicalSpace T] [T1Space T] (f : R ⟶ S) (hf : Function.Surjective f) :
    Topology.IsClosedEmbedding ((f ≫ ·) : (S ⟶ T) → (R ⟶ T)) := by
  refine ⟨isEmbedding_precomp_of_surjective f hf, ?_⟩
  have : IsClosed (⋂ i : RingHom.ker f.hom, { f : R ⟶ T | f i = 0 }) :=
    isClosed_iInter fun x ↦ (isClosed_singleton (x := 0)).preimage (continuous_apply (S := T) x.1)
  convert this
  ext x
  simp only [Set.mem_range, Set.iInf_eq_iInter, Set.mem_iInter, Set.mem_setOf_eq, Subtype.forall,
    RingHom.mem_ker]
  constructor
  · rintro ⟨g, rfl⟩ a ha; simp [ha]
  · exact fun H ↦ ⟨CommRingCat.ofHom (RingHom.liftOfSurjective f.hom hf ⟨x.hom, H⟩),
      by ext; simp [RingHom.liftOfRightInverse_comp_apply]⟩

/-- `Hom(S[Xᵢ], R)` is homeomorphic to `Hom(S, R) × Rⁱ`. -/
@[simps! apply_fst apply_snd symm_apply_hom]
noncomputable
def mvPolynomialHomeo (σ : Type v) (R S : CommRingCat.{max u v})
    [TopologicalSpace R] [TopologicalRing R] :
    (CommRingCat.of (MvPolynomial σ S) ⟶ R) ≃ₜ ((S ⟶ R) × (σ → R)) where
  toFun f := ⟨CommRingCat.ofHom MvPolynomial.C ≫ f, fun i ↦ f (.X i)⟩
  invFun fx := CommRingCat.ofHom (MvPolynomial.eval₂Hom fx.1.hom fx.2)
  left_inv f := by ext <;> simp
  right_inv fx := by ext <;> simp
  continuous_toFun := by fun_prop
  continuous_invFun := by
    refine continuous_induced_rng.mpr ?_
    refine continuous_pi fun p ↦ ?_
    simp only [Function.comp_apply, hom_ofHom, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq]
    fun_prop

variable (R S) in
lemma isEmbedding_hom [TopologicalSpace S] :
    IsEmbedding (fun f : R ⟶ S ↦ (f.hom : R → S)) :=
  ⟨.induced _, fun _ _ e ↦ by ext; rw [e]⟩

open Limits

variable (R S) in
lemma isClosedEmbedding_hom
    [TopologicalSpace S] [TopologicalRing S] [T1Space S] :
    IsClosedEmbedding (fun f : R ⟶ S ↦ (f.hom : R → S)) := by
  let f : CommRingCat.of (MvPolynomial R (⊥_ CommRingCat)) ⟶ R :=
    CommRingCat.ofHom (MvPolynomial.eval₂Hom (initial.to R).hom id)
  have : Function.Surjective f := Function.LeftInverse.surjective (g := .X) fun x ↦ by simp [f]
  convert ((mvPolynomialHomeo R S (.of _)).trans
    (.uniqueProd (⊥_ CommRingCat ⟶ S) _)).isClosedEmbedding.comp
    (isClosedEmbedding_precomp_of_surjective f this) using 2 with g
  ext x
  simp [f]

instance [TopologicalSpace S] [T2Space S] : T2Space (R ⟶ S) :=
  (isEmbedding_hom R S).t2Space

instance [TopologicalSpace S] [TopologicalRing S] [T1Space S] [CompactSpace S] :
    CompactSpace (R ⟶ S) :=
  (isClosedEmbedding_hom R S).compactSpace

open Limits

/-- `Hom(A ⊗[S] B, R)` has the subspace topology from `Hom(A, R) × Hom(B, R)`. -/
lemma isEmbedding_pushout [TopologicalSpace R] [TopologicalRing R]
    (φ : S ⟶ A) (ψ : S ⟶ B) :
    IsEmbedding fun f : pushout φ ψ ⟶ R ↦ (pushout.inl φ ψ ≫ f, pushout.inr φ ψ ≫ f) := by
  let PA := CommRingCat.of (MvPolynomial A S)
  let PB := CommRingCat.of (MvPolynomial B S)
  let fA : PA ⟶ A := CommRingCat.ofHom (MvPolynomial.eval₂Hom φ.hom id)
  have hfA : Function.Surjective fA.hom := fun x ↦ ⟨.X x, by simp [PA, fA]⟩
  let fB : PB ⟶ B := CommRingCat.ofHom (MvPolynomial.eval₂Hom ψ.hom id)
  have hfB : Function.Surjective fB.hom := fun x ↦ ⟨.X x, by simp [PB, fB]⟩
  have := (isEmbedding_precomp_of_surjective (T := R) fA hfA).prodMap
    (isEmbedding_precomp_of_surjective (T := R) fB hfB)
  rw [← IsEmbedding.of_comp_iff this]
  let PAB := CommRingCat.of (MvPolynomial (A ⊕ B) S)
  let fAB : PAB ⟶ pushout φ ψ :=
    CommRingCat.ofHom (MvPolynomial.eval₂Hom (φ ≫ pushout.inl φ ψ).hom
      (Sum.elim (pushout.inl φ ψ).hom (pushout.inr φ ψ).hom))
  have hfAB : Function.Surjective fAB := by
    rw [← RingHom.range_eq_top, ← top_le_iff,
      ← closure_range_union_range_eq_top_of_isPushout (.of_hasPushout _ _), Subring.closure_le]
    simp only [Set.union_subset_iff, RingHom.coe_range, Set.range_subset_iff, Set.mem_range]
    exact ⟨fun x ↦ ⟨.X (.inl x), by simp [fAB, PAB]⟩, fun x ↦ ⟨.X (.inr x), by simp [fAB, PAB]⟩⟩
  let F : ((S ⟶ R) × ((A ⊕ B) → R)) → ((S ⟶ R) × (A → R)) × ((S ⟶ R) × (B → R)) :=
    fun x ↦ ⟨⟨x.1, x.2 ∘ Sum.inl⟩, ⟨x.1, x.2 ∘ Sum.inr⟩⟩
  have hF : IsEmbedding F := (Homeomorph.prodProdProdComm _ _ _ _).isEmbedding.comp
    ((isEmbedding_graph continuous_id).prodMap Homeomorph.sumArrowHomeomorphProdArrow.isEmbedding)
  have H := (mvPolynomialHomeo A R S).symm.isEmbedding.prodMap
    (mvPolynomialHomeo B R S).symm.isEmbedding
  convert ((H.comp hF).comp (mvPolynomialHomeo _ R S).isEmbedding).comp
    (isEmbedding_precomp_of_surjective (T := R) fAB hfAB)
  have (s) : (pushout.inr φ ψ).hom (ψ.hom s) = (pushout.inl φ ψ).hom (φ.hom s) :=
    congr($(pushout.condition (f := φ)).hom s).symm
  ext f s <;> simp [fA, fB, fAB, PA, PB, PAB, F, this]

end CommRingCat.HomTopology
