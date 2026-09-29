/-
Copyright (c) 2026 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
module

public import Mathlib.Topology.LocallyFinsupp
public import Mathlib.Topology.Spectral.Prespectral

/-!
# Pushforward of functions with locally finite support

In this file we define the notion of the pushforward of a function with locally finite support
along a spectral map into a prespectral space. This is used for defining the (proper) pushforward
of algebraic cycles in algebraic geometry.

## Main declarations

- `Function.locallyFinsupp.map`: If `f : X → Y` is a spectral map between spectral spaces and
  `c : X → R` is locally of finite support, the pushforward of `c` along `f` at `y : Y` is
  `∑ᶠ x ∈ f ⁻¹' {y}, c x * w x`, where `w : X → R` is a weight function.

## Notes

In the case of algebraic cycles, the weight function used in `Function.locallyFinsupp.map` will be
specialized to the degree of the residue field extension
(see https://stacks.math.columbia.edu/tag/02R4).
-/

@[expose] public section

open Set

variable {X Y R : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {f : X → Y} (hf : IsSpectralMap f) (w : X → R)

namespace Function.locallyFinsupp

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring R] (c : Function.locallyFinsupp X R)

/-- The preimage of a compact open set under a spectral map meets the support of `c` in a finite
set. -/
lemma finite_preimage_inter_support (hf : IsSpectralMap f) {U : Set Y} (hU : IsOpen U)
    (hU' : IsCompact U) : (f ⁻¹' U ∩ c.support).Finite :=
  c.locallyFiniteSupport.finite_inter_support_of_isCompact (hf.2 hU hU')

variable [PrespectralSpace Y]

/-- The fibre of a spectral map over a point meets the support of `c` in a finite set. -/
lemma finite_preimage_singleton_inter_support (hf : IsSpectralMap f) (y : Y) :
    (f ⁻¹' {y} ∩ c.support).Finite := by
  obtain ⟨U, ⟨hU, hU'⟩, hyU, -⟩ :=
    PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open (mem_univ y) isOpen_univ
  exact (c.finite_preimage_inter_support hf hU hU').subset (by gcongr; simpa)

variable (f) in
/--
The pushforward of a function `c` of locally finite support by a spectral map with respect to a
weight function `w`.
-/
noncomputable
def map (hf : IsSpectralMap f) : locallyFinsupp X R →+ locallyFinsupp Y R where
  toFun c :=
    { toFun y := ∑ᶠ x ∈ f ⁻¹' {y}, c x * w x
      supportWithinDomain' := subset_univ _
      supportLocallyFiniteWithinDomain' y _ := by
        obtain ⟨U, ⟨hU, hU'⟩, hyU, -⟩ :=
          PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open (mem_univ y) isOpen_univ
        refine ⟨U, hU.mem_nhds hyU,
          ((c.finite_preimage_inter_support hf hU hU').image f).subset ?_⟩
        rintro _ ⟨hzU, hz⟩
        obtain ⟨x, rfl, hx⟩ := exists_ne_zero_of_finsum_mem_ne_zero hz
        exact ⟨x, ⟨hzU, left_ne_zero_of_mul hx⟩, rfl⟩ }
  map_zero' := by ext; simp
  map_add' c c' := by
    ext y
    simp only [locallyFinsuppWithin.coe_add, Pi.add_apply, add_mul]
    exact finsum_mem_add_distrib'
      ((c.finite_preimage_singleton_inter_support hf y).subset
        (inter_subset_inter_right _ fun _ ↦ left_ne_zero_of_mul))
      ((c'.finite_preimage_singleton_inter_support hf y).subset
        (inter_subset_inter_right _ fun _ ↦ left_ne_zero_of_mul))

@[simp]
lemma map_apply (hf : IsSpectralMap f) (c : locallyFinsupp X R) (y : Y) :
    map f w hf c y = ∑ᶠ x ∈ f ⁻¹' {y}, c x * w x := rfl

lemma support_map_subset_of_forall_mem (s : Set X) (t : Set Y) (hc : c.support ⊆ s)
    (h : ∀ x : X, x ∈ s → w x ≠ 0 → f x ∈ t) : (map f w hf c).support ⊆ t := by
  intro y hy
  obtain ⟨x, (rfl : f x = y), hx⟩ := exists_ne_zero_of_finsum_mem_ne_zero hy
  exact h x (hc (left_ne_zero_of_mul hx)) (right_ne_zero_of_mul hx)

end NonUnitalNonAssocSemiring

section NonAssocSemiring

variable [NonAssocSemiring R] (c : Function.locallyFinsupp X R) [PrespectralSpace X]

@[simp]
lemma map_id_apply (hw : ∀ z : X, w z = 1) :
    map id w isSpectralMap_id c = c := by
  ext
  simp [hw]

lemma map_id (hw : ∀ z : X, w z = 1) :
    map id w isSpectralMap_id = AddMonoidHom.id (locallyFinsupp X R) :=
  AddMonoidHom.ext (map_id_apply w · hw)

end NonAssocSemiring

end Function.locallyFinsupp
