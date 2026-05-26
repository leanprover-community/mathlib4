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
than usual, and allows us to reuse a lot of API to develop the theory of cycles.

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

namespace Function.locallyFinsupp

section map

variable [Semiring R] {W : Set Y} (hW : IsOpen W) (c : Function.locallyFinsupp X R)

variable [PrespectralSpace Y]

variable (f) in
/--
The pushforward of a function `c` of locally finite support
by a spectral map with respect to a weight function `w`. This is mainly used when interpretting
locally fin supp functions as algebraic cycles (in this case the weight function would be as
described in stacks 02R4, where the weight function is the degree of the corresponding extension of
residue fields if the dimensions of the points correspond, and is zero otherwise).
-/
noncomputable
def map (hf : IsSpectralMap f) (c : locallyFinsupp X R) : Function.locallyFinsupp Y R where
  toFun z := ∑ᶠ x ∈ f ⁻¹' {z}, c x * w x
  supportWithinDomain' := by simp
  supportLocallyFiniteWithinDomain' y _ := by
    obtain ⟨U, hU⟩ := (PrespectralSpace.isTopologicalBasis (X := Y)).exists_subset_of_mem_open
      (by simp : y ∈ ⊤) (by simp)
    refine ⟨U, IsOpen.mem_nhds hU.1.1 hU.2.1, ?_⟩
    suffices h : (U ∩ {z | (f ⁻¹' {z} ∩ support ⇑c).Nonempty}).Finite by
      refine h.subset (inter_subset_inter_right U fun y hy ↦ ?_)
      obtain ⟨x, (hx : f x = y), h'⟩ := exists_ne_zero_of_finsum_mem_ne_zero hy
      use x
      grind [mem_support]
    suffices (f ⁻¹' (U ∩ {z | (f ⁻¹' {z} ∩ c.support).Nonempty}) ∩ c.support).Finite from
      (this.image f).subset (fun a ha ↦ by grind [Set.Nonempty])
    exact (c.locallyFiniteSupport.finite_inter_support_of_isCompact <| hf.2 hU.1.1 hU.1.2).subset
      (by simp; grind)

@[simp]
lemma map_apply (hf : IsSpectralMap f) (c : locallyFinsupp X R) (y : Y) :
    map f w hf c y = ∑ᶠ x ∈ f ⁻¹' {y}, c x * w x := rfl

lemma map_homogeneous (s : Set X) (t : Set Y) (hc : c.support ⊆ s)
    (h : ∀ x : X, x ∈ s → w x ≠ 0 → f x ∈ t) : (map f w hf c).support ⊆ t := by
  intro y hy
  obtain ⟨x, (rfl : f x = y), h'⟩ := exists_ne_zero_of_finsum_mem_ne_zero hy
  grind [mem_support]

@[simp]
lemma map_id [PrespectralSpace X] (hw : ∀ z : X, w z = 1) :
    map id w isSpectralMap_id c = c := by
  ext
  simp [map, hw]

end map
end Function.locallyFinsupp
