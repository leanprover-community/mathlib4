/-
Copyright (c) 2017 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Topology.UniformSpace.Basic
import Mathlib.Topology.Bases

/-!
# Ultrametric (nonarchimedean) uniform spaces

Ultrametric (nonarchimedean) uniform spaces are ones that generalize ultrametric spaces by
having a uniformity based on equivalence relations.

## Main definitions

In this file we define `IsUltraUniformity`, a Prop mixin typeclass.

## Main results

* `TopologicalSpace.isTopologicalBasis_clopens`: a uniform space with a nonarchimedean uniformity
  has a topological basis of clopen sets in the topology, meaning that it is topologically
  zero-dimensional.

## Implementation notes

As in the `Topology/UniformSpace/Defs.lean` file, we do not reuse `Data/Rel.lean`
but rather extend the relation properties as needed.

## TODOs

* Prove that `IsUltraUniformity` iff `IsUltrametricDist` on a `PseudoMetricSpace`
* Generalize `IsUltrametricDist` to `IsUltrametricUniformity`
* Provide `IsUltraUniformity` for the uniformity in a `Valued` ring
* Generalize results about open/closed balls and spheres in `IsUltraUniformity` to
  combine applications for `MetricSpace.ball` and valued "balls"
* Use `IsUltraUniformity` to work with profinite/totally separated spaces
* Define the nonarchimedean uniformity of a space that is a product of `IsUltraUniformity`s
* Show that the `UniformSpace.Completion` of an `IsUltraUniformity` is `IsUltraUniformity`

## References

* [D. Windisch, *Equivalent characterizations of non-Archimedean uniform spaces*][windisch2021]
* [A. C. M. van Rooij, *Non-Archimedean uniformities*][vanrooij1970]

-/

open Set Filter Topology
open scoped Uniformity

variable {X : Type*}

/-- The relation is transitive. -/
def TransitiveRel (V : Set (X × X)) : Prop :=
  ∀ ⦃x y z⦄, (x, y) ∈ V → (y, z) ∈ V → (x, z) ∈ V

lemma TransitiveRel.comp_eq_of_idRel_subset {s : Set (X × X)}
    (h : TransitiveRel s) (h' : idRel ⊆ s) :
    s ○ s = s := by
  refine le_antisymm ?_ (subset_comp_self h')
  intro ⟨x, y⟩
  simp only [mem_compRel, forall_exists_index, and_imp]
  intro z
  exact @h x z y

variable [UniformSpace X]

variable (X) in
/-- A uniform space is ultrametric if the uniformity `𝓤 X` has a basis of equivalence relations. -/
class IsUltraUniformity : Prop where
  has_basis : (𝓤 X).HasBasis
    (fun s : Set (X × X) => s ∈ 𝓤 X ∧ SymmetricRel s ∧ TransitiveRel s) id

variable [IsUltraUniformity X]

namespace UniformSpace

lemma nhds_basis_clopens (x : X) :
    (𝓝 x).HasBasis (fun s : Set X => x ∈ s ∧ IsClopen s) id := by
  constructor
  intro t
  constructor
  · rw [nhds_eq_comap_uniformity, Filter.mem_comap]
    rintro ⟨u, hu, hu'⟩
    rw [IsUltraUniformity.has_basis.mem_iff] at hu
    obtain ⟨v, hv, hv'⟩ := hu
    refine ⟨{y | (x, y) ∈ v}, ⟨?_, ?_⟩, ?_⟩
    · simp only [mem_setOf_eq]
      exact refl_mem_uniformity hv.left
    · constructor
      · rw [← isOpen_compl_iff, isOpen_uniformity]
        simp only [mem_compl_iff, mem_setOf_eq]
        intro z hz
        rw [IsUltraUniformity.has_basis.mem_iff]
        refine ⟨v, hv, ?_⟩
        intro ⟨a, b⟩
        simp only [id_eq, mem_setOf_eq]
        rintro h rfl H
        rw [hv.right.left.mk_mem_comm] at h
        exact hz (hv.right.right H h)
      · rw [isOpen_uniformity]
        simp only [mem_setOf_eq]
        intro z hz
        rw [IsUltraUniformity.has_basis.mem_iff]
        refine ⟨v, hv, ?_⟩
        intro ⟨a, b⟩
        simp only [id_eq, mem_setOf_eq]
        rintro h rfl
        exact hv.right.right hz h
    · refine le_trans ?_ hu'
      intro z
      simp only [id_eq, mem_setOf_eq, mem_preimage]
      intro hz
      exact hv' hz
  · rintro ⟨u, ⟨hu, hu'⟩, hu''⟩
    rw [_root_.mem_nhds_iff]
    exact ⟨u, hu'', hu'.right, hu⟩

/-- A uniform space with a nonarchimedean uniformity is zero-dimensional. -/
lemma _root_.TopologicalSpace.isTopologicalBasis_clopens :
    TopologicalSpace.IsTopologicalBasis {s : Set X | IsClopen s} := by
  apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds fun U (hU : IsClopen U) => hU.2
  intro x U hxU U_op
  have : U ∈ 𝓝 x := IsOpen.mem_nhds U_op hxU
  rcases (nhds_basis_clopens x).mem_iff.mp this with ⟨V, ⟨hxV, hV⟩, hVU : V ⊆ U⟩
  use V
  tauto

end UniformSpace
