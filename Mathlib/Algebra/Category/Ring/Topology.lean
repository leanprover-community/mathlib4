/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Christian Merten
-/
module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

/-!
# Topology on `Hom(R, S)`

In this file, we define topology on `Hom(A, R)` for a topological ring `R`,
given by the coarsest topology that makes `f ↦ f x` continuous for all `x : A`.
Alternatively, given a presentation `A = ℤ[xᵢ]/I`,
this is the subspace topology `Hom(A, R) ↪ Hom(ℤ[xᵢ], R) = Rᶥ`.

## Main results
- `CommRingCat.HomTopology.isClosedEmbedding_precomp_of_surjective`:
  `Hom(A/I, R)` is a closed subspace of `Hom(A, R)` if `R` is Hausdorff.
- `CommRingCat.HomTopology.mvPolynomialHomeomorph`:
  `Hom(A[Xᵢ], R)` is homeomorphic to `Hom(A, R) × Rᶥ`.
- `CommRingCat.HomTopology.isEmbedding_pushout`:
  `Hom(B ⊗[A] C, R)` has the subspace topology from `Hom(B, R) × Hom(C, R)`.

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe u v

open CategoryTheory Topology

namespace CommRingCat.HomTopology

variable {R A B C : CommRingCat.{u}} [TopologicalSpace R]

/--
The topology on `Hom(A, R)` for a topological ring `R`, given by the coarsest topology that
makes `f ↦ f x` continuous for all `x : A` (see `continuous_apply`).
Alternatively, given a presentation `A = ℤ[xᵢ]/I`,
this is the subspace topology `Hom(A, R) ↪ Hom(ℤ[xᵢ], R) = Rᶥ` (see `mvPolynomialHomeomorph`).

This is a scoped instance in `CommRingCat.HomTopology`.
-/
scoped instance : TopologicalSpace (A ⟶ R) :=
  .induced (fun f ↦ f.hom : _ → A → R) inferInstance

@[fun_prop]
nonrec lemma continuous_apply (x : A) :
    Continuous (fun f : A ⟶ R ↦ f.hom x) :=
  (continuous_apply x).comp continuous_induced_dom

variable (R A) in
lemma isEmbedding_hom :
    IsEmbedding (fun f : A ⟶ R ↦ (f.hom : A → R)) :=
  ⟨.induced _, fun _ _ e ↦ by ext; rw [e]⟩

@[fun_prop]
lemma continuous_precomp (f : A ⟶ B) :
    Continuous ((f ≫ ·) : (B ⟶ R) → (A ⟶ R)) :=
  continuous_induced_rng.mpr ((Pi.continuous_precomp f.hom).comp continuous_induced_dom)

/-- If `A ≅ B`, then `Hom(A, R)` is homeomorphic to `Hom(B, R)`. -/
@[simps]
def precompHomeomorph (f : A ≅ B) :
    (B ⟶ R) ≃ₜ (A ⟶ R) where
  toFun φ := _
  invFun φ := _
  continuous_toFun := continuous_precomp f.hom
  continuous_invFun := continuous_precomp f.inv
  left_inv _ := by simp
  right_inv _ := by simp

lemma isHomeomorph_precomp (f : A ⟶ B) [IsIso f] :
    IsHomeomorph ((f ≫ ·) : (B ⟶ R) → (A ⟶ R)) :=
  (precompHomeomorph (asIso f)).isHomeomorph

/-- `Hom(A/I, R)` has the subspace topology of `Hom(A, R)`.
More generally, a surjection `A ⟶ B` gives rise to an embedding `Hom(B, R) ⟶ Hom(A, R)` -/
lemma isEmbedding_precomp_of_surjective
    (f : A ⟶ B) (hf : Function.Surjective f) :
    Topology.IsEmbedding ((f ≫ ·) : (B ⟶ R) → (A ⟶ R)) := by
  refine IsEmbedding.of_comp (continuous_precomp _) (IsInducing.induced _).continuous ?_
  suffices IsEmbedding ((· ∘ f.hom) : (B → R) → (A → R)) from
    this.comp (.induced (fun f g e ↦ by ext a; exact congr($e a)))
  exact Function.Surjective.isEmbedding_comp _ hf

/-- `Hom(A/I, R)` is a closed subspace of `Hom(A, R)` if `R` is T1. -/
lemma isClosedEmbedding_precomp_of_surjective
    [T1Space R] (f : A ⟶ B) (hf : Function.Surjective f) :
    Topology.IsClosedEmbedding ((f ≫ ·) : (B ⟶ R) → (A ⟶ R)) := by
  refine ⟨isEmbedding_precomp_of_surjective f hf, ?_⟩
  have : IsClosed (⋂ i : RingHom.ker f.hom, { f : A ⟶ R | f i = 0 }) :=
    isClosed_iInter fun x ↦ (isClosed_singleton (x := 0)).preimage (continuous_apply (R := R) x.1)
  convert this
  ext x
  simp only [Set.mem_range, Set.mem_iInter, Set.mem_setOf_eq, Subtype.forall, RingHom.mem_ker]
  constructor
  · rintro ⟨g, rfl⟩ a ha; simp [ha]
  · exact fun H ↦ ⟨CommRingCat.ofHom (RingHom.liftOfSurjective f.hom hf ⟨x.hom, H⟩),
      by ext; simp [RingHom.liftOfRightInverse_comp_apply]⟩

/-- `Hom(A[Xᵢ], R)` is homeomorphic to `Hom(A, R) × Rⁱ`. -/
@[simps! apply_fst apply_snd symm_apply_hom]
noncomputable
def mvPolynomialHomeomorph (σ : Type v) (R A : CommRingCat.{max u v})
    [TopologicalSpace R] [IsTopologicalRing R] :
    (CommRingCat.of (MvPolynomial σ A) ⟶ R) ≃ₜ ((A ⟶ R) × (σ → R)) where
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

open Limits

variable (R A) in
lemma isClosedEmbedding_hom [IsTopologicalRing R] [T1Space R] :
    IsClosedEmbedding (fun f : A ⟶ R ↦ (f.hom : A → R)) := by
  let f : CommRingCat.of (MvPolynomial A (⊥_ CommRingCat)) ⟶ A :=
    CommRingCat.ofHom (MvPolynomial.eval₂Hom (initial.to A).hom id)
  have : Function.Surjective f := Function.LeftInverse.surjective (g := .X) fun x ↦ by simp [f]
  convert ((mvPolynomialHomeomorph A R (.of _)).trans
    (.uniqueProd (⊥_ CommRingCat ⟶ R) _)).isClosedEmbedding.comp
    (isClosedEmbedding_precomp_of_surjective f this) using 2 with g
  ext x
  simp +instances [f]

instance [T2Space R] : T2Space (A ⟶ R) :=
  (isEmbedding_hom R A).t2Space

instance [IsTopologicalRing R] [T1Space R] [CompactSpace R] :
    CompactSpace (A ⟶ R) :=
  (isClosedEmbedding_hom R A).compactSpace

open Limits

set_option backward.isDefEq.respectTransparency false in
/-- `Hom(B ⊗[A] C, R)` has the subspace topology from `Hom(B, R) × Hom(C, R)`. -/
lemma isEmbedding_pushout [IsTopologicalRing R] (φ : A ⟶ B) (ψ : A ⟶ C) :
    IsEmbedding fun f : pushout φ ψ ⟶ R ↦ (pushout.inl φ ψ ≫ f, pushout.inr φ ψ ≫ f) := by
  -- The key idea: Let `X = Spec B` and `Y = Spec C`.
  -- We want to show `(X × Y)(R)` has the subspace topology from `X(R) × Y(R)`.
  -- We already know that `X(R) × Y(R)` is a subspace of `𝔸ᴮ(R) × 𝔸ᶜ(R)` and by explicit calculation
  -- this is isomorphic to `𝔸ᴮ⁺ᶜ(R)` which `(X × Y)(R)` embeds into.
  let PB := CommRingCat.of (MvPolynomial B A)
  let PC := CommRingCat.of (MvPolynomial C A)
  let fB : PB ⟶ B := CommRingCat.ofHom (MvPolynomial.eval₂Hom φ.hom id)
  have hfB : Function.Surjective fB.hom := fun x ↦ ⟨.X x, by simp [PB, fB]⟩
  let fC : PC ⟶ C := CommRingCat.ofHom (MvPolynomial.eval₂Hom ψ.hom id)
  have hfC : Function.Surjective fC.hom := fun x ↦ ⟨.X x, by simp [PC, fC]⟩
  have := (isEmbedding_precomp_of_surjective (R := R) fB hfB).prodMap
    (isEmbedding_precomp_of_surjective (R := R) fC hfC)
  rw [← IsEmbedding.of_comp_iff this]
  let PBC := CommRingCat.of (MvPolynomial (B ⊕ C) A)
  let fBC : PBC ⟶ pushout φ ψ :=
    CommRingCat.ofHom (MvPolynomial.eval₂Hom (φ ≫ pushout.inl φ ψ).hom
      (Sum.elim (pushout.inl φ ψ).hom (pushout.inr φ ψ).hom))
  have hfBC : Function.Surjective fBC := by
    rw [← RingHom.range_eq_top, ← top_le_iff,
      ← closure_range_union_range_eq_top_of_isPushout (.of_hasPushout _ _), Subring.closure_le]
    simp only [Set.union_subset_iff, RingHom.coe_range, Set.range_subset_iff, Set.mem_range]
    exact ⟨fun x ↦ ⟨.X (.inl x), by simp [fBC, PBC]⟩, fun x ↦ ⟨.X (.inr x), by simp [fBC, PBC]⟩⟩
  let F : ((A ⟶ R) × ((B ⊕ C) → R)) → ((A ⟶ R) × (B → R)) × ((A ⟶ R) × (C → R)) :=
    fun x ↦ ⟨⟨x.1, x.2 ∘ Sum.inl⟩, ⟨x.1, x.2 ∘ Sum.inr⟩⟩
  have hF : IsEmbedding F := (Homeomorph.prodProdProdComm _ _ _ _).isEmbedding.comp
    ((isEmbedding_graph continuous_id).prodMap Homeomorph.sumArrowHomeomorphProdArrow.isEmbedding)
  have H := (mvPolynomialHomeomorph B R A).symm.isEmbedding.prodMap
    (mvPolynomialHomeomorph C R A).symm.isEmbedding
  convert ((H.comp hF).comp (mvPolynomialHomeomorph _ R A).isEmbedding).comp
    (isEmbedding_precomp_of_surjective (R := R) fBC hfBC)
  have (s : _) : (pushout.inr φ ψ).hom (ψ.hom s) = (pushout.inl φ ψ).hom (φ.hom s) :=
    congr($(pushout.condition (f := φ)).hom s).symm
  ext f s <;> simp [fB, fC, fBC, PB, PC, PBC, F, this]

end CommRingCat.HomTopology
