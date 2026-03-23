/-
Copyright (c) 2024 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Data.Set.Subset
public import Mathlib.Order.Irreducible
public import Mathlib.Topology.Order.LowerUpperTopology
public import Mathlib.Topology.Sets.Closeds

/-!
# Hull-Kernel Topology

Let `α` be a `CompleteLattice` and let `T` be a subset of `α`. The pair of maps
`S → sInf (Subtype.val '' S)` and `a → T ↓∩ Ici a` are often referred to as the `kernel` and the
`hull` respectively. They form an antitone Galois connection between the subsets of `T` and `α`.
When `α` can be generated from `T` by taking infs, this becomes a Galois insertion and the relative
topology (`Topology.lower`) on `T` takes on a particularly simple form: the relative-open sets are
exactly the sets of the form `(hull T a)ᶜ` for some `a` in `α`. The topological closure coincides
with the closure arising from the Galois insertion. For this reason the relative lower topology on
`T` is often referred to as the "hull-kernel topology". The names "Jacobson topology" and "structure
topology" also occur in the literature.

## Main statements

- `PrimitiveSpectrum.isTopologicalBasis_relativeLower` - the sets `(hull a)ᶜ` form a basis for the
  relative lower topology on `T`.
- `PrimitiveSpectrum.isOpen_iff` - for a complete lattice, the sets `(hull a)ᶜ` are the relative
  topology.
- `PrimitiveSpectrum.gc` - the `kernel` and the `hull` form a Galois connection
- `PrimitiveSpectrum.gi` - when `T` generates `α`, the Galois connection becomes an insertion.

## Implementation notes

The antitone Galois connection from `Set T` to `α` is implemented as a monotone Galois connection
between `Set T` to `αᵒᵈ`.

## Motivation

The motivating example for the study of a set `T` of prime elements which generate `α` is the
primitive spectrum of the lattice of M-ideals of a Banach space.

## References

* [Gierz et al, *A Compendium of Continuous Lattices*][GierzEtAl1980]
* [Henriksen et al, *Joincompact spaces, continuous lattices and C*-algebras*][henriksen_et_al1997]

## Tags

lower topology, hull-kernel topology, Jacobson topology, structure topology, primitive spectrum

-/

@[expose] public section

variable {α}

open TopologicalSpace
open Topology
open Set
open Set.Notation

section SemilatticeInf

variable [SemilatticeInf α]
namespace PrimitiveSpectrum

/-- For `a` of type `α` the set of element of `T` which dominate `a` is the `hull` of `a` in `T`. -/
abbrev hull (T : Set α) (a : α) := T ↓∩ Ici a

variable {T : Set α}

/-- The set of relative-closed sets of the form `hull T a` for some `a` in `α` is closed under
pairwise union. -/
lemma hull_inf (hT : ∀ p ∈ T, InfPrime p) (a b : α) :
    hull T (a ⊓ b) = hull T a ∪ hull T b := by
  ext p
  constructor <;> intro h
  · exact (hT p p.2).2 h
  · rcases h with (h1 | h3)
    · exact inf_le_of_left_le h1
    · exact inf_le_of_right_le h3

variable [OrderTop α]

open Finset in
/-- Every relative-closed set of the form `T ↓∩ (↑(upperClosure F))` for `F` finite is a
relative-closed set of the form `hull T a` where `a = ⨅ F`. -/
lemma hull_finsetInf (hT : ∀ p ∈ T, InfPrime p) (F : Finset α) :
    hull T (inf F id) = T ↓∩ upperClosure (F : Set α) := by
  rw [coe_upperClosure]
  induction F using Finset.cons_induction with
  | empty =>
    simp only [coe_empty, mem_empty_iff_false, iUnion_of_empty, iUnion_empty, Set.preimage_empty,
      inf_empty]
    by_contra hf
    rw [← Set.not_nonempty_iff_eq_empty, not_not] at hf
    obtain ⟨x, hx⟩ := hf
    exact (hT x (Subtype.coe_prop x)).1 (isMax_iff_eq_top.mpr (eq_top_iff.mpr hx))
  | cons a F' _ I4 => simp [hull_inf hT, I4]

open Finset in
/-- Every relative-open set of the form `T ↓∩ (↑(upperClosure F))ᶜ` for `F` finite
is a relative-open set of the form `(hull T a)ᶜ` where `a = ⨅ F`. -/
lemma preimage_upperClosure_compl_finset (hT : ∀ p ∈ T, InfPrime p) (F : Finset α) :
    T ↓∩ (upperClosure (F : Set α))ᶜ = (hull T (inf F id))ᶜ := by
  rw [Set.preimage_compl, (hull_finsetInf hT)]

variable [TopologicalSpace α] [IsLower α]

/-
The relative-open sets of the form `(hull T a)ᶜ` for `a` in `α` form a basis for the relative
Lower topology.
-/
lemma isTopologicalBasis_relativeLower (hT : ∀ p ∈ T, InfPrime p) :
    IsTopologicalBasis { S : Set T | ∃ (a : α), (hull T a)ᶜ = S } := by
  convert isTopologicalBasis_subtype Topology.IsLower.isTopologicalBasis (· ∈ T)
  ext R
  simp only [preimage_compl, mem_setOf_eq, IsLower.lowerBasis, mem_image, exists_exists_and_eq_and]
  constructor <;> intro ha
  · obtain ⟨a, ha'⟩ := ha
    use {a}
    rw [← (Function.Injective.preimage_image Subtype.val_injective R), ← ha']
    simp only [finite_singleton, upperClosure_singleton, UpperSet.coe_Ici, image_val_compl,
      Subtype.image_preimage_coe, diff_self_inter, preimage_diff, Subtype.coe_preimage_self,
      true_and]
    exact compl_eq_univ_diff (Subtype.val ⁻¹' Ici a)
  · obtain ⟨F, hF⟩ := ha
    lift F to Finset α using hF.1
    use Finset.inf F id
    ext
    simp [hull_finsetInf hT, ← hF.2]

end PrimitiveSpectrum

end SemilatticeInf

namespace PrimitiveSpectrum
variable [CompleteLattice α] {T : Set α}

universe v

lemma hull_iSup {ι : Sort v} (s : ι → α) : hull T (iSup s) = ⋂ i, hull T (s i) := by aesop

lemma hull_sSup (S : Set α) : hull T (sSup S) = ⋂₀ { hull T a | a ∈ S } := by aesop

/- When `α` is complete, a set is Lower topology relative-open if and only if it is of the form
`(hull T a)ᶜ` for some `a` in `α`.-/
lemma isOpen_iff [TopologicalSpace α] [IsLower α] (hT : ∀ p ∈ T, InfPrime p)
    (S : Set T) : IsOpen S ↔ ∃ (a : α), S = (hull T a)ᶜ := by
  constructor <;> intro h
  · let R := {a : α | (hull T a)ᶜ ⊆ S}
    use sSup R
    rw [IsTopologicalBasis.open_eq_sUnion' (isTopologicalBasis_relativeLower hT) h]
    aesop
  · obtain ⟨a, ha⟩ := h
    exact ⟨(Ici a)ᶜ, isClosed_Ici.isOpen_compl, ha.symm⟩

/- When `α` is complete, a set is closed in the relative lower topology if and only if it is of the
form `hull T a` for some `a` in `α`.-/
lemma isClosed_iff [TopologicalSpace α] [IsLower α] (hT : ∀ p ∈ T, InfPrime p)
    {S : Set T} : IsClosed S ↔ ∃ (a : α), S = hull T a := by
  simp only [← isOpen_compl_iff, isOpen_iff hT, compl_inj_iff]

/-- For a subset `S` of `T`, `kernel S` is the infimum of `S` (considered as a set of `α`) -/
abbrev kernel (S : Set T) := sInf (Subtype.val '' S)

/- The pair of maps `kernel` and `hull` form an antitone Galois connection between the
subsets of `T` and `α`. -/
open OrderDual in
theorem gc : GaloisConnection (α := Set T) (β := αᵒᵈ)
    (fun S => toDual (kernel S)) (fun a => hull T (ofDual a)) := fun S a => by
  simp [Set.subset_def]

lemma gc_closureOperator (S : Set T) : gc.closureOperator S = hull T (kernel S) := by
  simp only [toDual_sInf, GaloisConnection.closureOperator_apply, ofDual_sSup]
  rw [← preimage_comp, ← OrderDual.toDual_symm_eq, Equiv.symm_comp_self, preimage_id_eq, id_eq]

variable (T)

/-- `T` order generates `α` if, for every `a` in `α`, there exists a subset of `T` such that `a` is
the `kernel` of `S`. -/
def OrderGenerates := ∀ (a : α), ∃ (S : Set T), a = kernel S

variable {T}

/--
When `T` is order generating, the `kernel` and the `hull` form a Galois insertion
-/
def gi (hG : OrderGenerates T) : GaloisInsertion (α := Set T) (β := αᵒᵈ)
    (OrderDual.toDual ∘ kernel)
    (hull T ∘ OrderDual.ofDual) :=
  gc.toGaloisInsertion fun a ↦ by
    obtain ⟨S, rfl⟩ := hG a
    rw [OrderDual.le_toDual, kernel, kernel]
    exact sInf_le_sInf <| image_val_mono fun c hcS => by
      rw [hull, mem_preimage, mem_Ici]
      exact sInf_le (mem_image_of_mem Subtype.val hcS)

lemma kernel_hull (hG : OrderGenerates T) (a : α) : kernel (hull T a) = a := by
  conv_rhs => rw [← OrderDual.ofDual_toDual a, ← (gi hG).l_u_eq a]
  rfl

lemma hull_kernel_of_isClosed [TopologicalSpace α] [IsLower α]
    (hT : ∀ p ∈ T, InfPrime p) (hG : OrderGenerates T) {C : Set T} (h : IsClosed C) :
    hull T (kernel C) = C := by
  obtain ⟨a, ha⟩ := (isClosed_iff hT).mp h
  rw [ha, kernel_hull hG]

lemma closedsGC_closureOperator [TopologicalSpace α] [IsLower α]
    (hT : ∀ p ∈ T, InfPrime p) (hG : OrderGenerates T) (S : Set T) :
    (TopologicalSpace.Closeds.gc (α := T)).closureOperator S = hull T (kernel S) := by
  simp only [GaloisConnection.closureOperator_apply, Closeds.coe_closure, closure, le_antisymm_iff]
  constructor
  · exact fun ⦃a⦄ a ↦ a (hull T (kernel S)) ⟨(isClosed_iff hT).mpr ⟨kernel S, rfl⟩,
      image_subset_iff.mp (fun _ hbS => sInf_le hbS)⟩
  · simp_rw [le_eq_subset, subset_sInter_iff]
    intro R hR
    rw [← (hull_kernel_of_isClosed hT hG hR.1), ← gc_closureOperator]
    exact ClosureOperator.monotone _ hR.2

end PrimitiveSpectrum
