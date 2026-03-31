/-
Copyright (c) 2025 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
module

public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.Topology.LocallyFinsupp
public import Mathlib.Algebra.GradedMonoid
public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Topology.Spectral.ConstructibleTopology

/-!
# Algebraic Cycles

In this file we define algebraic cycles on a scheme `X` with coefficients in a type `R` and provide
some basic API for working with them. We define an algebraic cycle on a scheme `X` with
coefficients in a type `R` to be functions `c : X → R` whose support is locally finite.

Here we're making use of the equivalence between irreducible closed subsets of a scheme and their
generic points in order to reuse the API in Function.locallyFinsupp, hence the slightly
nonstandard definition.
-/

@[expose] public section

open Set Order Topology TopologicalSpace CategoryTheory

universe u v
variable {X Y R : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : IsSpectralMap f) (w : X → R)

namespace Function
namespace locallyFinsupp

section Zero
variable [Zero R]
/--
The cycle containing a single point with a chosen coefficient
-/
noncomputable
def single (x : X) (coeff : R) : Function.locallyFinsupp X R where
  toFun := Set.indicator {x} (Function.const X coeff)
  supportWithinDomain' := by simp only [support_indicator]; exact LE.le.subset fun _ a_1 ↦ trivial
  supportLocallyFiniteWithinDomain' z hz :=
    ⟨⊤, ⟨Filter.univ_mem' fun a ↦ trivial, by simp [← Function.const_def, toFinite]⟩⟩

variable (f) in
/--
Implementation detail for the pushforward; the support of a cycle on X intersected with the preimage
of a point z : Y along a morphism `f : X ⟶ Y`.
-/
def preimageSupport (c : locallyFinsupp X R) (z : Y) : Set X :=
  f ⁻¹' {z} ∩ c.support

end Zero

section map

variable [Semiring R] {W : TopologicalSpace.Opens Y} (hW : IsCompact W.1)
  (c : Function.locallyFinsupp X R)

lemma preimageSupport_inter_subset : W.carrier ∩ {z | (preimageSupport f c z).Nonempty} ⊆
    f '' (f ⁻¹' ((W.carrier ∩ {z | (preimageSupport f c z).Nonempty})) ∩ c.support) := by
  intro a ha
  rw [image_preimage_inter]
  suffices a ∈ f '' c.support from mem_inter ha this
  have := ha.2.some_mem
  simp only [preimageSupport, mem_inter_iff, mem_preimage, mem_singleton_iff,
    Function.mem_support, ne_eq, mem_image] at this ⊢
  exact ⟨ha.2.some, this.symm⟩

lemma preimageSupport_preimage_inter_subset : f ⁻¹' W.carrier ∩
    f ⁻¹' {z | (preimageSupport f c z).Nonempty} ∩ c.support ⊆
    f ⁻¹' W.carrier ∩ (⋃ z : Y, preimageSupport f c z) := by
  intro p hp
  simp only [Opens.carrier_eq_coe, preimageSupport, preimage_setOf_eq, mem_inter_iff,
    mem_preimage, SetLike.mem_coe, mem_setOf_eq, Function.mem_support, ne_eq, mem_iUnion,
    mem_singleton_iff, exists_and_right, exists_eq', true_and] at hp ⊢
  exact ⟨hp.1.1, hp.2⟩

lemma preimage_inter_support_finite_of_isAffineOpen (hf : IsSpectralMap f) (hW : IsCompact W.1) :
    (f ⁻¹' W.carrier ∩ c.support).Finite :=
  LocallyFiniteSupport.finite_inter_support_of_isCompact c.locallyFiniteSupport <|
  hf.2 W.is_open' hW

lemma iUnion_preimage_inter_support_finite_of_isAffineOpen (hf : IsSpectralMap f)
    (hW : IsCompact W.1) :
    (⋃ _ : Y, f ⁻¹' W.carrier ∩ c.support).Finite := by
  suffices (f ⁻¹' W.carrier ∩ c.support).Finite by
    apply Finite.subset this
    intro a ha
    simp only [Opens.carrier_eq_coe, mem_iUnion, mem_inter_iff, mem_preimage,
      SetLike.mem_coe, Function.mem_support, ne_eq, exists_and_left, exists_const_iff] at ha ⊢
    exact ⟨ha.1, ha.2.2⟩
  exact preimage_inter_support_finite_of_isAffineOpen c hf hW

lemma inter_nonempty_finite (hf : IsSpectralMap f) (hW : IsCompact W.1)
   : (W.carrier ∩ {z : Y | (preimageSupport f c z).Nonempty}).Finite := by
  refine Finite.subset (Finite.image _ ?_) (preimageSupport_inter_subset c)
  rw[preimage_inter]
  apply Finite.subset _ (preimageSupport_preimage_inter_subset c)
  rw[inter_iUnion]
  suffices (⋃ i : Y, f ⁻¹' W.carrier ∩ c.support).Finite by
    apply Finite.subset this
    simp only [Opens.carrier_eq_coe, iUnion_subset_iff]
    intro y x hx
    simp only [mem_inter_iff, mem_preimage, SetLike.mem_coe,
      Function.mem_support, ne_eq, mem_iUnion, exists_and_left, exists_const_iff] at hx ⊢
    exact ⟨hx.1, ⟨Nonempty.intro y, hx.2.2⟩⟩
  exact iUnion_preimage_inter_support_finite_of_isAffineOpen c hf hW

variable {N : Type*} [PrespectralSpace Y]

/--
The pushforward of an algebraic cycle has locally finite support.
-/
lemma map_locally_finite (hf : IsSpectralMap f)
    (h : ∀ z, (preimageSupport f c z).Finite) :
    ∀ z : Y, ∃ t ∈ 𝓝 z, (t ∩ Function.support fun z ↦
    ∑ x ∈ (h z).toFinset, (c x) * w x).Finite := by
  intro y
  have : ∃ W : TopologicalSpace.Opens Y, IsCompact W.1 ∧ y ∈ W := by
    obtain ⟨U, hU⟩ := (PrespectralSpace.isTopologicalBasis (X := Y)).exists_subset_of_mem_open
        (by simp : y ∈ ⊤) (by simp)
    use ⟨U, hU.1.1⟩
    exact ⟨hU.1.2, hU.2.1⟩
  obtain ⟨W, hW⟩ := this
  use W
  refine ⟨IsOpen.mem_nhds (Opens.isOpen W) hW.2, ?_⟩
  suffices (W.carrier ∩ {z : Y | (preimageSupport f c z).Nonempty}).Finite by
      apply Finite.subset this
      apply inter_subset_inter Set.Subset.rfl
      intro x
      simp only [Function.mem_support, ne_eq, mem_setOf_eq]
      contrapose!
      intro aux
      rw [Finset.sum_eq_zero]
      simp_all
  exact inter_nonempty_finite c hf hW.1

variable (f) in
/--
The pushforward by a spectral map with quasicompact fibers with respect to a weight function `w`.
This is mainly used when interpretting locally fin supp functions as algebraic cycles (in this case
the weight function corresponds to a dimension or codimension function).



NOTE: It is probably more sensible to define this for functions with compact fibers, rather than
simply functions whose fibers have nonempty intersection with c.support. Maybe this way is fine too
-/
noncomputable
def map (hf : IsSpectralMap f) (h : ∀ z, (preimageSupport f c z).Finite) :
    Function.locallyFinsupp Y R
    where
  toFun z := (∑ x ∈ (h z).toFinset, (c x) * w x)
  supportWithinDomain' := by simp
  supportLocallyFiniteWithinDomain' z _ := map_locally_finite w c hf h z

/--
Pushforward preserves cycles of pure dimension `d` in the dimension grading.
-/
lemma map_homogeneneous (s : Set X) (t : Set Y) (hc : c.support ⊆ s)
    (h1 : ∀ z, (preimageSupport f c z).Finite)
    (h : ∀ x : X, x ∈ s → w x ≠ 0 → f x ∈ t) :
    (map f w c hf h1).support ⊆ t:= by
  intro y hy
  simp only [map, preimageSupport, Function.mem_support,
    ne_eq] at hy
  obtain ⟨x, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
  simp only [Finite.mem_toFinset, mem_inter_iff, mem_preimage, mem_singleton_iff,
    Function.mem_support, ne_eq] at hx
  specialize h x (hc hx.1.2)
  grind

/--
The pushforward of `c` along the identity morphism is `c`.
-/
@[simp]
lemma map_id [PrespectralSpace X] (h : ∀ z, (preimageSupport id c z).Finite)
    (hw : ∀ z : X, w z = 1) :
    map id w c isSpectralMap_id h = c := by
   ext z
   have : (c z ≠ 0 ∧ (h z).toFinset = {z}) ∨
          (c z = 0 ∧ (h z).toFinset = ∅) := by
    simp only [ne_eq, Finite.toFinset, preimageSupport, preimage_id_eq, id_eq, toFinset_eq_empty,
      singleton_inter_eq_empty,
      Function.mem_support, not_not, and_self]
    refine Or.elim (em (c z = 0)) (fun o ↦ Or.inr o) (fun o ↦ Or.inl ⟨o, Finset.ext (fun a ↦ ?_)⟩)
    simp only [mem_toFinset, mem_inter_iff, mem_singleton_iff, Function.mem_support, ne_eq,
      Finset.mem_singleton, and_iff_left_iff_imp]
    rintro rfl
    assumption
   suffices (map id w c isSpectralMap_id h).toFun z = c.toFun z from this
   obtain h | h := this
   all_goals simp only [map]
             rw[h.2]
             simp only [Finset.sum_singleton, Finset.sum_empty]
   · rw [hw]
     exact MulOneClass.mul_one (c z)
   · exact h.1.symm

end map
end locallyFinsupp
end Function
