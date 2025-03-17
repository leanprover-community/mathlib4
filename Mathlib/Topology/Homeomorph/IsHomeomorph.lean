/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Sébastien Gouëzel, Zhouhang Zhou, Reid Barton
-/
-- tODO: fix copyright; this is a much more recent contribution!
import Mathlib.Topology.Homeomorph.Constructions
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Predicate saying that `f` is a homeomorphism

-/

assert_not_exists Module MonoidWithZero

open Filter Function Set Topology

variable {X Y W Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [TopologicalSpace W] {f : X → Y}

/-- Predicate saying that `f` is a homeomorphism.

This should be used only when `f` is a concrete function whose continuous inverse is not easy to
write down. Otherwise, `Homeomorph` should be preferred as it bundles the continuous inverse.

Having both `Homeomorph` and `IsHomeomorph` is justified by the fact that so many function
properties are unbundled in the topology part of the library, and by the fact that a homeomorphism
is not merely a continuous bijection, that is `IsHomeomorph f` is not equivalent to
`Continuous f ∧ Bijective f` but to `Continuous f ∧ Bijective f ∧ IsOpenMap f`. -/
structure IsHomeomorph (f : X → Y) : Prop where
  continuous : Continuous f
  isOpenMap : IsOpenMap f
  bijective : Bijective f

protected theorem Homeomorph.isHomeomorph (h : X ≃ₜ Y) : IsHomeomorph h :=
  ⟨h.continuous, h.isOpenMap, h.bijective⟩

namespace IsHomeomorph
variable (hf : IsHomeomorph f)
include hf

protected lemma injective : Function.Injective f := hf.bijective.injective
protected lemma surjective : Function.Surjective f := hf.bijective.surjective

variable (f) in
/-- Bundled homeomorphism constructed from a map that is a homeomorphism. -/
@[simps! toEquiv apply symm_apply]
noncomputable def homeomorph : X ≃ₜ Y where
  continuous_toFun := hf.1
  continuous_invFun := by
    rw [continuous_iff_continuousOn_univ, ← hf.bijective.2.range_eq]
    exact hf.isOpenMap.continuousOn_range_of_leftInverse (leftInverse_surjInv hf.bijective)
  toEquiv := Equiv.ofBijective f hf.bijective

protected lemma isClosedMap : IsClosedMap f := (hf.homeomorph f).isClosedMap
lemma isInducing : IsInducing f := (hf.homeomorph f).isInducing
lemma isQuotientMap : IsQuotientMap f := (hf.homeomorph f).isQuotientMap
lemma isEmbedding : IsEmbedding f := (hf.homeomorph f).isEmbedding
lemma isOpenEmbedding : IsOpenEmbedding f := (hf.homeomorph f).isOpenEmbedding
lemma isClosedEmbedding : IsClosedEmbedding f := (hf.homeomorph f).isClosedEmbedding
lemma isDenseEmbedding : IsDenseEmbedding f := (hf.homeomorph f).isDenseEmbedding

@[deprecated (since := "2024-10-28")] alias inducing := isInducing

@[deprecated (since := "2024-10-26")]
alias embedding := isEmbedding

@[deprecated (since := "2024-10-22")]
alias quotientMap := isQuotientMap

@[deprecated (since := "2024-10-20")] alias closedEmbedding := isClosedEmbedding
@[deprecated (since := "2024-10-18")]
alias openEmbedding := isOpenEmbedding

@[deprecated (since := "2024-09-30")]
alias denseEmbedding := isDenseEmbedding

end IsHomeomorph

/-- A map is a homeomorphism iff it is the map underlying a bundled homeomorphism `h : X ≃ₜ Y`. -/
lemma isHomeomorph_iff_exists_homeomorph : IsHomeomorph f ↔ ∃ h : X ≃ₜ Y, h = f :=
  ⟨fun hf => ⟨hf.homeomorph f, rfl⟩, fun ⟨h, h'⟩ => h' ▸ h.isHomeomorph⟩

/-- A map is a homeomorphism iff it is continuous and has a continuous inverse. -/
lemma isHomeomorph_iff_exists_inverse : IsHomeomorph f ↔ Continuous f ∧ ∃ g : Y → X,
    LeftInverse g f ∧ RightInverse g f ∧ Continuous g := by
  refine ⟨fun hf ↦ ⟨hf.continuous, ?_⟩, fun ⟨hf, g, hg⟩ ↦ ?_⟩
  · let h := hf.homeomorph f
    exact ⟨h.symm, h.left_inv, h.right_inv, h.continuous_invFun⟩
  · exact (Homeomorph.mk ⟨f, g, hg.1, hg.2.1⟩ hf hg.2.2).isHomeomorph

/-- A map is a homeomorphism iff it is a surjective embedding. -/
lemma isHomeomorph_iff_isEmbedding_surjective : IsHomeomorph f ↔ IsEmbedding f ∧ Surjective f where
  mp hf := ⟨hf.isEmbedding, hf.surjective⟩
  mpr h := ⟨h.1.continuous, ((isOpenEmbedding_iff f).2 ⟨h.1, h.2.range_eq ▸ isOpen_univ⟩).isOpenMap,
    h.1.injective, h.2⟩

@[deprecated (since := "2024-10-26")]
alias isHomeomorph_iff_embedding_surjective := isHomeomorph_iff_isEmbedding_surjective

/-- A map is a homeomorphism iff it is continuous, closed and bijective. -/
lemma isHomeomorph_iff_continuous_isClosedMap_bijective  : IsHomeomorph f ↔
    Continuous f ∧ IsClosedMap f ∧ Function.Bijective f :=
  ⟨fun hf => ⟨hf.continuous, hf.isClosedMap, hf.bijective⟩, fun ⟨hf, hf', hf''⟩ =>
    ⟨hf, fun _ hu => isClosed_compl_iff.1 (image_compl_eq hf'' ▸ hf' _ hu.isClosed_compl), hf''⟩⟩

/-- A map from a compact space to a T2 space is a homeomorphism iff it is continuous and
  bijective. -/
lemma isHomeomorph_iff_continuous_bijective [CompactSpace X] [T2Space Y] :
    IsHomeomorph f ↔ Continuous f ∧ Bijective f := by
  rw [isHomeomorph_iff_continuous_isClosedMap_bijective]
  refine and_congr_right fun hf ↦ ?_
  rw [eq_true hf.isClosedMap, true_and]

protected lemma IsHomeomorph.id : IsHomeomorph (@id X) := ⟨continuous_id, .id, bijective_id⟩

lemma IsHomeomorph.comp {g : Y → Z} (hg : IsHomeomorph g) (hf : IsHomeomorph f) :
    IsHomeomorph (g ∘ f) := ⟨hg.1.comp hf.1, hg.2.comp hf.2, hg.3.comp hf.3⟩

lemma IsHomeomorph.sumMap {g : Z → W} (hf : IsHomeomorph f) (hg : IsHomeomorph g) :
    IsHomeomorph (Sum.map f g) := ⟨hf.1.sumMap hg.1, hf.2.sumMap hg.2, hf.3.sumMap hg.3⟩

lemma IsHomeomorph.prodMap {g : Z → W} (hf : IsHomeomorph f) (hg : IsHomeomorph g) :
    IsHomeomorph (Prod.map f g) := ⟨hf.1.prodMap hg.1, hf.2.prodMap hg.2, hf.3.prodMap hg.3⟩

lemma IsHomeomorph.sigmaMap {ι κ : Type*} {X : ι → Type*} {Y : κ → Type*}
    [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)] {f : ι → κ}
    (hf : Bijective f) {g : (i : ι) → X i → Y (f i)} (hg : ∀ i, IsHomeomorph (g i)) :
    IsHomeomorph (Sigma.map f g) := by
  simp_rw [isHomeomorph_iff_isEmbedding_surjective,] at hg ⊢
  exact ⟨(isEmbedding_sigmaMap hf.1).2 fun i ↦ (hg i).1, hf.2.sigma_map fun i ↦ (hg i).2⟩

lemma IsHomeomorph.pi_map {ι : Type*} {X Y : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, TopologicalSpace (Y i)] {f : (i : ι) → X i → Y i} (h : ∀ i, IsHomeomorph (f i)) :
    IsHomeomorph (fun (x : ∀ i, X i) i ↦ f i (x i)) :=
  (Homeomorph.piCongrRight fun i ↦ (h i).homeomorph (f i)).isHomeomorph
