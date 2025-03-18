/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Topology.UniformSpace.Pi
import Mathlib.Topology.UniformSpace.Ultra.Basic

/-!
# Binary products of ultrametric (nonarchimedean) uniform spaces

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
  constructor
  refine (h.hasBasis.comap (Prod.map f f)).to_hasBasis' ?_ ?_
  · simp only [uniformity_comap, Filter.mem_comap, id_eq, and_imp]
    intro s hs hss hst
    exact ⟨_, ⟨⟨s, hs, Set.preimage_mono (subset_refl _)⟩, hss.preimage_map _, hst.preimage_map _⟩,
      subset_refl _⟩
  · aesop

lemma IsUltraUniformity.inf {u u' : UniformSpace X} (h : @IsUltraUniformity _ u)
    (h' : @IsUltraUniformity _ u') :
    @IsUltraUniformity _ (u ⊓ u') := by
  letI := u ⊓ u'
  constructor
  refine (h.hasBasis.inf h'.hasBasis).to_hasBasis' ?_ ?_
  · simp only [id_eq, Set.subset_inter_iff, and_imp, Prod.forall]
    intros
    exact ⟨_, ⟨Filter.mem_inf_of_inter ‹_› ‹_› (subset_refl _),
      IsSymmetricRel.inter ‹_› ‹_›, IsTransitiveRel.inter ‹_› ‹_›⟩,
      Set.inter_subset_left, Set.inter_subset_right⟩
  · aesop

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
  constructor
  rw [iInf_uniformity]
  refine (Filter.hasBasis_iInf (fun i ↦ (hU i).hasBasis)).to_hasBasis' ?_ ?_
  · simp only [id_eq, Set.iInter_coe_set, Set.subset_iInter_iff, and_imp]
    intro ⟨s, f⟩ hsf ih
    simp only at ih ⊢
    refine ⟨⋂ i : s, f i, ⟨?_, ?_, ?_⟩, ?_⟩
    · rw [Filter.mem_iInf]
      exact ⟨s, hsf, f, fun _ ↦ (ih _).left, rfl⟩
    · exact IsSymmetricRel.iInter (fun i ↦ (ih i).right.left)
    · exact IsTransitiveRel.iInter (fun i ↦ (ih i).right.right)
    · intros
      exact Set.iInter_subset _ _
  · aesop

/-- The indexed product of uniform spaces with nonarchimedean uniformities has a
nonarchimedean uniformity. -/
instance IsUltraUniformity.pi {ι : Type*} {X : ι → Type*} [U : Π i, UniformSpace (X i)]
    [h : ∀ i, IsUltraUniformity (X i)] :
    IsUltraUniformity (Π i, X i) := by
  suffices @IsUltraUniformity _ (⨅ i, UniformSpace.comap (Function.eval i) (U i)) by
    simpa [Pi.uniformSpace_eq _] using this
  exact .iInf fun i ↦ .comap (h i) (Function.eval i)
