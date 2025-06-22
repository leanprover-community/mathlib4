/-
Copyright (c) 2025 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
import Mathlib

open AlgebraicGeometry Set Order LocallyRingedSpace Topology TopologicalSpace
  CategoryTheory

/-!
# Algebraic Cycles

We define algebraic cycles on a scheme `X` to be functions `c : X → ℤ` whose support is
locally finite.

## Main definitions

-/

universe u v
variable (R : Type*)
         [CommRing R]
         (i : ℕ)
         {X Y : Scheme.{u}}

abbrev AlgebraicCycle (X : Scheme) := Function.locallyFinsuppWithin (⊤ : Set X) ℤ

structure HomogenousCycle (X : Scheme) (d : ℕ) where
  cycle : AlgebraicCycle X
  homogenous : ∀ x ∈ cycle.support, height x = d

namespace AlgebraicCycle

variable (f : X ⟶ Y)
         (c : AlgebraicCycle X)
         (x : X)
         (z : Y)

/--
The cycle containing a single point with a chosen coefficient
-/
noncomputable
def single (coeff : ℤ) : AlgebraicCycle X where
  toFun := Set.indicator {x} (Function.const X coeff)
  supportWithinDomain' := by simp
  supportLocallyFiniteWithinDomain' z hz :=
    ⟨⊤, ⟨Filter.univ_mem' fun a ↦ trivial, by simp [← Function.const_def, toFinite]⟩⟩

/--
Implementation detail for the pushforward; the support of a cycle on X intersected with the preimage
of a point z : Y along a morphism f : X ⟶ Y.
-/
def preimageSupport : Set X :=
  f.base ⁻¹' {z} ∩ c.support

/--
Implementation detail for the pushforward; the support of a cycle on X intersected with the preimage
of a point z : Y along a quasicompact morphism f : X ⟶ Y is finite.
-/
def preimageSupportFinite [qf : QuasiCompact f] :
 (preimageSupport f c z).Finite :=
 supportLocallyFiniteWithin_top_inter_compact_finite c.supportLocallyFiniteWithinDomain' <|
  QuasiCompact.isCompact_preimage_singleton f z

noncomputable
def _root_.AlgebraicGeometry.LocallyRingedSpace.Hom.degree : ℕ := @Module.finrank
    (IsLocalRing.ResidueField (Y.presheaf.stalk (f.base x)))
    (IsLocalRing.ResidueField (X.presheaf.stalk x))
    (by infer_instance)
    (by infer_instance)
    (by have :=
      RingHom.toAlgebra (IsLocalRing.ResidueField.map (f.stalkMap x).hom);exact Algebra.toModule)

open Classical in
noncomputable
def mapAux {Y : Scheme} (f : X ⟶ Y) (x : X) : ℤ :=
  if height x = height (f.base x) then Hom.degree f x else 0

lemma map_locally_finite {Y : Scheme}
  (f : X ⟶ Y) [qc : QuasiCompact f] (c : AlgebraicCycle X) :
  ∀ z ∈ (⊤ : Set Y), ∃ t ∈ 𝓝 z, (t ∩ Function.support fun z ↦
  ∑ x ∈ (preimageSupportFinite f c z).toFinset, (c x) * mapAux f x).Finite := by
  intro y hy
  have : ∃ W : Y.Opens, IsAffineOpen W ∧ y ∈ W := by sorry
  obtain ⟨W, hW⟩ := this
  have cpct : IsCompact (f.base ⁻¹' W) := qc.1 W.carrier W.is_open' <|
     AlgebraicGeometry.IsAffineOpen.isCompact hW.1
  use W
  refine ⟨IsOpen.mem_nhds (Opens.isOpen W) hW.2, ?_⟩

  have pbfinite : (f.base ⁻¹' W ∩ Function.support c).Finite :=
   supportLocallyFiniteWithin_top_inter_compact_finite c.supportLocallyFiniteWithinDomain' cpct

  suffices (W.carrier ∩ {z : Y | (preimageSupport f c z).Nonempty}).Finite by
      apply Finite.subset this
      apply inter_subset_inter Set.Subset.rfl
      intro x
      simp only [top_eq_univ, Function.mem_support, ne_eq, mem_setOf_eq]
      contrapose!
      intro aux
      rw [Finset.sum_eq_zero]
      intro x hx
      simp only [Finite.mem_toFinset, aux] at hx
      simp only [mem_empty_iff_false] at hx

  have : W.carrier ∩ {z | (preimageSupport f c z).Nonempty} ⊆
    f.base '' (f.base ⁻¹' ((W.carrier ∩ {z | (preimageSupport f c z).Nonempty})) ∩ c.support) := by
    intro a ha
    rw [image_preimage_inter]
    suffices a ∈ f.base '' c.support from mem_inter ha this
    have := ha.2.some_mem
    simp[preimageSupport] at this ⊢
    exact ⟨ha.2.some, this.symm⟩

  refine Finite.subset (Finite.image _ ?_) this
  rw[preimage_inter]
  have : f.base ⁻¹' W.carrier ∩ f.base ⁻¹' {z | (preimageSupport f c z).Nonempty} ∩ c.support ⊆
      f.base ⁻¹' W.carrier ∩ (⋃ z : Y, preimageSupport f c z) := by
    intro p hp
    simp[preimageSupport] at hp ⊢
    exact ⟨hp.1.1, hp.2⟩

  apply Finite.subset _ this
  rw[inter_iUnion]
  simp[preimageSupport]
  suffices (⋃ i : Y, f.base ⁻¹' W.carrier ∩ c.support).Finite by
    apply Finite.subset this
    simp only [Opens.carrier_eq_coe, top_eq_univ, iUnion_subset_iff]
    intro y x hx
    simp at hx ⊢
    exact ⟨hx.1, ⟨Nonempty.intro y, hx.2.2⟩⟩

  suffices (f.base ⁻¹' W.carrier ∩ c.support).Finite by
    apply Finite.subset this
    intro a ha
    simp only [Opens.carrier_eq_coe, top_eq_univ, mem_iUnion, mem_inter_iff, mem_preimage,
      SetLike.mem_coe, Function.mem_support, ne_eq, exists_and_left, exists_const_iff] at ha ⊢
    exact ⟨ha.1, ha.2.2⟩

  exact pbfinite

open Classical in
noncomputable
def map {Y : Scheme}
  (f : X ⟶ Y) [qc : QuasiCompact f] (c : AlgebraicCycle X) : AlgebraicCycle Y where
  toFun z := (∑ x ∈ (preimageSupportFinite f c z).toFinset, (c x) * mapAux f x)
  supportWithinDomain' := by simp
  supportLocallyFiniteWithinDomain' := fun z a ↦ map_locally_finite f c z a

@[simp]
lemma map_id (c : AlgebraicCycle X) :
    map (𝟙 X) c = c := by
   ext z
   have : (c z ≠ 0 ∧ (preimageSupportFinite (𝟙 X) c z).toFinset = {z}) ∨
          (c z = 0 ∧ (preimageSupportFinite (𝟙 X) c z).toFinset = ∅) := by
    simp[preimageSupportFinite, preimageSupport, Finite.toFinset]
    by_cases o : c z = 0
    · exact Or.inr o
    · apply Or.inl
      refine ⟨o, ?_⟩
      ext a
      simp only [mem_toFinset, mem_inter_iff, mem_singleton_iff, Function.mem_support, ne_eq,
        Finset.mem_singleton, and_iff_left_iff_imp]
      intro h
      rw[h]
      exact o
   suffices (map (𝟙 X) c).toFun z = c.toFun z from this
   obtain h | h := this
   all_goals simp[map, mapAux]
             rw[h.2]
             simp only [Hom.degree, Scheme.id.base, TopCat.hom_id, ContinuousMap.id_apply,
               Scheme.stalkMap_id, CommRingCat.hom_id, IsLocalRing.ResidueField.map_id,
               Module.finrank_self, Nat.cast_one, mul_one, Finset.sum_singleton]
   · rfl
   · exact h.1.symm

end AlgebraicCycle
