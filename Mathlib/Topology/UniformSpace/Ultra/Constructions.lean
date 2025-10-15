/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Topology.UniformSpace.DiscreteUniformity
import Mathlib.Topology.UniformSpace.Pi
import Mathlib.Topology.UniformSpace.Ultra.Basic

/-!
# Products of ultrametric (nonarchimedean) uniform spaces

## Main results

* `IsUltraUniformity.prod`: a product of uniform spaces with nonarchimedean uniformities
  has a nonarchimedean uniformity.
* `IsUltraUniformity.pi`: an indexed product of uniform spaces with nonarchimedean uniformities
  has a nonarchimedean uniformity.

## Implementation details

This file can be split to separate imports to have the `Prod` and `Pi` instances separately,
but would be somewhat unnatural since they are closely related.
The `Prod` instance only requires `Mathlib/Topology/UniformSpace/Basic.lean`.

-/

variable {X Y : Type*}

lemma IsTransitiveRel.entourageProd {s : Set (X × X)} {t : Set (Y × Y)}
    (hs : IsTransitiveRel s) (ht : IsTransitiveRel t) :
    IsTransitiveRel (entourageProd s t) :=
  fun _ _ _ h h' ↦ ⟨hs h.left h'.left, ht h.right h'.right⟩

lemma IsUltraUniformity.comap {u : UniformSpace Y} (h : IsUltraUniformity Y) (f : X → Y) :
    @IsUltraUniformity _ (u.comap f) := by
  letI := u.comap f
  refine .mk_of_hasBasis (h.hasBasis.comap (Prod.map f f)) ?_ ?_
  · exact fun _ ⟨_, hU, _⟩ ↦ hU.preimage_prodMap f
  · exact fun _ ⟨_, _, hU⟩ ↦ hU.preimage_prodMap f

lemma IsUltraUniformity.inf {u u' : UniformSpace X} (h : @IsUltraUniformity _ u)
    (h' : @IsUltraUniformity _ u') :
    @IsUltraUniformity _ (u ⊓ u') := by
  letI := u ⊓ u'
  refine .mk_of_hasBasis (h.hasBasis.inf h'.hasBasis) ?_ ?_
  · exact fun _ ⟨⟨_, hU, _⟩, _, hU', _⟩ ↦ hU.inter hU'
  · exact fun _ ⟨⟨_, _, hU⟩, _, _, hU'⟩ ↦ hU.inter hU'

/-- The product of uniform spaces with nonarchimedean uniformities has a
nonarchimedean uniformity. -/
instance IsUltraUniformity.prod [UniformSpace X] [UniformSpace Y]
    [IsUltraUniformity X] [IsUltraUniformity Y] :
    IsUltraUniformity (X × Y) :=
  .inf (.comap ‹_› _) (.comap ‹_› _)

lemma IsUltraUniformity.iInf {ι : Type*} {U : (i : ι) → UniformSpace X}
    (hU : ∀ i, @IsUltraUniformity X (U i)) :
    @IsUltraUniformity _ (⨅ i, U i : UniformSpace X) := by
  letI : UniformSpace X := ⨅ i, U i
  refine .mk_of_hasBasis (iInf_uniformity ▸ Filter.HasBasis.iInf fun i ↦ (hU i).hasBasis) ?_ ?_
  · exact fun _ ⟨_, h⟩ ↦ IsSymmetricRel.iInter fun i ↦ (h i).right.left
  · exact fun _ ⟨_, h⟩ ↦ IsTransitiveRel.iInter fun i ↦ (h i).right.right

/-- The indexed product of uniform spaces with nonarchimedean uniformities has a
nonarchimedean uniformity. -/
instance IsUltraUniformity.pi {ι : Type*} {X : ι → Type*} [U : Π i, UniformSpace (X i)]
    [h : ∀ i, IsUltraUniformity (X i)] :
    IsUltraUniformity (Π i, X i) := by
  suffices @IsUltraUniformity _ (⨅ i, UniformSpace.comap (Function.eval i) (U i)) by
    simpa [Pi.uniformSpace_eq _] using this
  exact .iInf fun i ↦ .comap (h i) (Function.eval i)

instance IsUltraUniformity.bot [UniformSpace X] [DiscreteUniformity X] : IsUltraUniformity X := by
  have := Filter.hasBasis_principal (idRel (α := X))
  rw [← DiscreteUniformity.eq_principal_idRel] at this
  apply mk_of_hasBasis this
  · simpa using isSymmetricRel_idRel
  · simpa using isTransitiveRel_idRel

lemma IsUltraUniformity.top : @IsUltraUniformity X (⊤ : UniformSpace X) := by
  letI : UniformSpace X := ⊤
  have := Filter.hasBasis_top (α := (X × X))
  rw [← top_uniformity] at this
  apply mk_of_hasBasis this
  · simpa using isSymmetricRel_univ
  · simpa using isTransitiveRel_univ
