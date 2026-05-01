/-
Copyright (c) 2026 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
module

public import Mathlib.Topology.LocallyFinsupp
public import Mathlib.Topology.Spectral.Basic

/-!
# Pushforward of functions with locally finite support

In this file we define the notion of the pushforward of a function with locally finite support
between prespectral spaces. This is a nonstandard notion that arises because of our choice in
mathlib to model algebraic cycles as functions with locally finite support.
This makes it so that standard notions in the theory of cycles can be defined in more generality
than usual.

In the usual definition of the proper pushforward of algebraic cycles, one needs to adjust the
coefficients by scaling by the degree of the corresponding extension of residue fields (assuming
the dimensions are the same and hence that this is a finite extension), or in the case where the
dimensions of the points differ scaling by zero. This is described in more detail in stacks 02R4.
The exact values of this scaling function are not relevant for the mere construction of the
pushforward, so our definition of the pushforward of a cycle `c` on a scheme `X` with coefficients
in `R` is done with respect to some `w : X → R`, about which we do not assume anything.
-/

@[expose] public section

open Set Order Topology TopologicalSpace

universe u v
variable {X Y R : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : IsSpectralMap f) (w : X → R)

namespace Function
namespace locallyFinsupp

section map

variable [Semiring R] {W : TopologicalSpace.Opens Y} (c : Function.locallyFinsupp X R)

lemma inter_preimageSupport_nonempty_finite (hf : IsSpectralMap f) (hW : IsCompact W.1) :
    (W.carrier ∩ {z : Y | (f ⁻¹' {z} ∩ c.support).Nonempty}).Finite := by
  suffices (f ⁻¹' (W.carrier ∩ {z | (f ⁻¹' {z} ∩ c.support).Nonempty}) ∩ c.support).Finite from
    (this.image f).subset (fun a ha ↦ by grind [Set.Nonempty])
  rw [preimage_inter]
  suffices (f ⁻¹' W ∩ ⋃ z, f ⁻¹' {z} ∩ c.support).Finite by
    apply Finite.subset this
    rw [Set.inter_assoc]
    exact Set.inter_subset_inter_right _ (fun p hp ↦ by simp_all)
  rw [inter_iUnion]
  suffices (f ⁻¹' W.carrier ∩ c.support).Finite by
    grind [Opens.carrier_eq_coe, iUnion_subset_iff, SetLike.mem_coe,
      Function.mem_support, Finite.subset]
  exact LocallyFiniteSupport.finite_inter_support_of_isCompact c.locallyFiniteSupport <|
    hf.2 W.is_open' hW

variable {N : Type*} [PrespectralSpace Y]

lemma map_locally_finite (hf : IsSpectralMap f) (hf' : ∀ y : Y, IsCompact <| f ⁻¹' {y}) (y : Y) :
    ∃ t ∈ 𝓝 y, (t ∩ Function.support fun z ↦
    ∑ x ∈ (c.locallyFiniteSupport.finite_inter_support_of_isCompact <| hf' z).toFinset,
    (c x) * w x).Finite := by
  obtain ⟨W, hW⟩ : ∃ W : TopologicalSpace.Opens Y, IsCompact W.1 ∧ y ∈ W := by
    obtain ⟨U, hU⟩ := (PrespectralSpace.isTopologicalBasis (X := Y)).exists_subset_of_mem_open
        (by simp : y ∈ ⊤) (by simp)
    use ⟨U, hU.1.1⟩
    exact ⟨hU.1.2, hU.2.1⟩
  use W
  refine ⟨IsOpen.mem_nhds (Opens.isOpen W) hW.2, ?_⟩
  suffices (W.carrier ∩ {z : Y | (f ⁻¹' {z} ∩ support c.toFun).Nonempty}).Finite by
    apply Finite.subset this
    apply inter_subset_inter_right
    intro x
    contrapose!
    simp +contextual only [mem_setOf_eq, not_nonempty_iff_eq_empty, mem_support, toFinite_toFinset,
      toFinset_empty, Finset.sum_empty, ne_eq, not_true_eq_false, not_false_eq_true, implies_true]
  exact inter_preimageSupport_nonempty_finite c hf hW.1

variable (f) in
/--
The pushforward of a function `c` of locally finite support
by a spectral map whose fibers intersect `c` in finitely many places
with respect to a weight function `w`. This is mainly used when interpretting locally fin supp
functions as algebraic cycles (in this case the weight function would be as described in stacks
02R4, where the weight function is the degree of the corresponding extension of residue fields
if the dimensions of the points correspond, and is zero otherwise).
-/
@[simps]
noncomputable
def map (hf : IsSpectralMap f) (hf' : ∀ y : Y, IsCompact <| f ⁻¹' {y}) :
    Function.locallyFinsupp Y R where
  toFun z := ∑ x ∈ (c.locallyFiniteSupport.finite_inter_support_of_isCompact <| hf' z).toFinset,
    (c x) * w x
  supportWithinDomain' := by simp
  supportLocallyFiniteWithinDomain' z _ := map_locally_finite w c hf hf' z

/--
Pushforward preserves cycles of pure dimension `d` in the dimension grading.
-/
lemma map_homogeneous (s : Set X) (t : Set Y) (hc : c.support ⊆ s)
    (hf' : ∀ y : Y, IsCompact <| f ⁻¹' {y})
    (h : ∀ x : X, x ∈ s → w x ≠ 0 → f x ∈ t) :
    (map f w c hf hf').support ⊆ t := by
  intro y hy
  simp only [map, Function.mem_support, ne_eq] at hy
  obtain ⟨x, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
  simp only [Finite.mem_toFinset, mem_inter_iff, mem_preimage, mem_singleton_iff,
    Function.mem_support, ne_eq] at hx
  specialize h x (hc hx.1.2)
  grind

/--
The pushforward of `c` along the identity morphism is `c`.
-/
@[simp]
lemma map_id [PrespectralSpace X] (hw : ∀ z : X, w z = 1) :
    map id w c isSpectralMap_id (by simp) = c := by
  classical
  ext z
  change ∑ x ∈ _, c x * w x = c z
  rw [show (Set.Finite.toFinset _ : Finset X) = if c z = 0 then ∅ else {z} from by
    ext; split_ifs <;> aesop]
  split_ifs with h <;> simp [hw, h]

end map
end locallyFinsupp
end Function
