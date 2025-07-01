/-
Copyright (c) 2024 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/

import Mathlib.Data.Set.Subset
import Mathlib.Order.Irreducible
import Mathlib.Topology.Order.LowerUpperTopology
import Mathlib.Topology.Sets.Closeds

/-!
# Hull-Kernel Topology

Let `α` be a `CompleteLattice` and let `T` be a subset of `α`. The relative topology
(`Topology.lower`) on `T` takes on a particularly simple form when every element of `T` is
`InfPrime` in `α`. In this case, the relative-open sets are exactly the sets of the form
`T ↓∩ (Ici a)ᶜ` for some `a` in `α`.

The pair of maps `S → ⊓ S` and `a → T ↓∩ Ici a` are often referred to as the kernel and the hull.
They form an antitone Galois connection between the subsets of `T` and `α`. When `α` can be
generated from `T` by taking infs, this becomes a Galois insertion and the topological closure
coincides with the closure arising from the Galois insertion. For this reason the relative lower
topology on `T` is often referred to as the "hull-kernel topology". The names "Jacobson topology"
and "structure topology" also occur in the literature.

## Main statements

- `PrimitiveSpectrum.relativeLowerIsTopologicalBasis` - the sets `T ↓∩ Ici a` form a basis for the
  relative lower topology on `T`.
- `PrimitiveSpectrum.isOpen_iff` - for a complete lattice, the sets `T ↓∩ Ici a` are the relative
  topology.
- `PrimitiveSpectrum.gc` - the kernel and the hull form a Galois connection
- `PrimitiveSpectrum.gi` - when `T` generates `α`, the Galois connection becomes an insertion.
- `PrimitiveSpectrum.lowerTopology_closureOperator_eq_gc_closureOperator` - relative lower topology
  closure coincides with the "hull-kernel" closure arising from the Galois insertion.

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

variable {α}

open TopologicalSpace
open Topology
open Set
open Set.Notation

section SemilatticeInf

variable [SemilatticeInf α]
namespace PrimitiveSpectrum

abbrev hull (T : Set α) (a : α) := T ↓∩ Ici a

variable {T : Set α}

/- The set of relative-closed sets of the form `T ↓∩ Ici a` for some `a` in `α` is closed under
pairwise union. -/
lemma preimage_Ici_union_preimage_Ici (hT : ∀ p ∈ T, InfPrime p) (a b : α) :
    hull T a ∪ hull T b = hull T (a ⊓ b) := by
  ext p
  constructor <;> intro h
  · rcases h with (h1 | h3)
    · exact inf_le_of_left_le h1
    · exact inf_le_of_right_le h3
  · exact (hT p p.2).2 h

/- The set of relative-open sets of the form `T ↓∩ (Ici a)ᶜ` for some `a` in `α` is closed under
pairwise intersection. -/
lemma preimage_Ici_compl_inter_preimage_Ici_compl (hT : ∀ p ∈ T, InfPrime p) (a b : α) :
    (hull T a)ᶜ ∩ (hull T b)ᶜ = (hull T (a ⊓ b))ᶜ := by
  rw [← (preimage_Ici_union_preimage_Ici hT), compl_union]

variable [DecidableEq α] [OrderTop α]

/- Every relative-closed set of the form `T ↓∩ (↑(upperClosure F))` for `F` finite is a
relative-closed set of the form `T ↓∩ Ici a` where `a = ⨅ F`. -/
open Finset in
lemma preimage_upperClosure_finset (hT : ∀ p ∈ T, InfPrime p) (F : Finset α) :
    T ↓∩ upperClosure F.toSet = hull T (inf F id) := by
  rw [coe_upperClosure]
  induction' F using Finset.induction_on with a F' _ I4
  · simp only [coe_empty, mem_empty_iff_false, iUnion_of_empty, iUnion_empty, Set.preimage_empty,
      inf_empty, Set.Ici_top]
    symm
    by_contra hf
    rw [← Set.not_nonempty_iff_eq_empty, not_not] at hf
    obtain ⟨x, hx⟩ := hf
    exact (hT x (Subtype.coe_prop x)).1 (isMax_iff_eq_top.mpr (eq_top_iff.mpr hx))
  · simp only [coe_insert, mem_insert_iff, mem_coe, iUnion_iUnion_eq_or_left, Set.preimage_union,
      preimage_iUnion, inf_insert, id_eq, ← (preimage_Ici_union_preimage_Ici hT), ← I4]

/- Every relative-open set of the form `T ↓∩ (↑(upperClosure F))ᶜ` for `F` finite is a relative-open
set of the form `T ↓∩ (Ici a)ᶜ` where `a = ⨅ F`. -/
open Finset in
lemma preimage_upperClosure_compl_finset (hT : ∀ p ∈ T, InfPrime p) (F : Finset α) :
    T ↓∩ (upperClosure F.toSet)ᶜ = (hull T (inf F id))ᶜ := by
  rw [Set.preimage_compl, (preimage_upperClosure_finset hT)]

variable [TopologicalSpace α] [IsLower α]

/-
The relative-open sets of the form `T ↓∩ (Ici a)ᶜ` for `a` in `α` form a basis for the relative
Lower topology.
-/
lemma relativeLowerIsTopologicalBasis (hT : ∀ p ∈ T, InfPrime p) :
    IsTopologicalBasis { S : Set T | ∃ (a : α), (hull T a)ᶜ = S } := by
  convert isTopologicalBasis_subtype Topology.IsLower.isTopologicalBasis T
  ext R
  simp only [preimage_compl, mem_setOf_eq, IsLower.lowerBasis, mem_image, exists_exists_and_eq_and]
  constructor <;> intro ha
  · obtain ⟨a, ha'⟩ :=  ha
    use {a}
    rw [← (Function.Injective.preimage_image Subtype.val_injective R), ← ha']
    simp only [finite_singleton, upperClosure_singleton, UpperSet.coe_Ici, image_val_compl,
      Subtype.image_preimage_coe, diff_self_inter, preimage_diff, Subtype.coe_preimage_self,
      true_and]
    exact compl_eq_univ_diff (Subtype.val ⁻¹' Ici a)
  · obtain ⟨F, hF⟩ := ha
    lift F to Finset α using hF.1
    use Finset.inf F id
    rw [← (preimage_upperClosure_finset hT), ← hF.2]
    rfl

end PrimitiveSpectrum

end SemilatticeInf

section PrimativeSpectrum

variable [CompleteLattice α]

variable {T : Set α}

namespace PrimitiveSpectrum

lemma sInter_preimage_Ici (S : Set α) : ⋂₀ { hull T a | a ∈ S } = hull T (sSup S) := by
  ext x : 1
  simp_all only [mem_sInter, mem_setOf_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    mem_preimage, mem_Ici, sSup_le_iff]

/- When `α` is complete, the relative basis for the lower topology is also closed under arbitrary
unions. -/
lemma sUnion_Ici_Compl_eq (S : Set α) : ⋃₀ { (hull T a)ᶜ | a ∈ S } = (hull T (sSup S))ᶜ := by
  simp [sUnion_eq_compl_sInter_compl, ← sInter_preimage_Ici, compl_sInter]

/- When `α` is complete, a set is Lower topology relative-open if and only if it is of the form
`T ↓∩ (Ici a)ᶜ` for some `a` in `α`.-/
lemma isOpen_iff [TopologicalSpace α] [IsLower α] [DecidableEq α] (hT : ∀ p ∈ T, InfPrime p)
    (S : Set T) : IsOpen S ↔ ∃ (a : α), S = (hull T a)ᶜ := by
  constructor <;> intro h
  · let R := {a : α | (hull T a)ᶜ ⊆ S}
    use sSup R
    rw [IsTopologicalBasis.open_eq_sUnion' (relativeLowerIsTopologicalBasis hT) h]
    aesop
  · obtain ⟨a, ha⟩ := h
    exact ⟨(Ici a)ᶜ, ⟨isOpen_compl_iff.mpr isClosed_Ici, ha.symm⟩⟩

/- When `α` is complete, a set is closed in the relative lower topology if and only if it is of the
form `T ↓∩ Ici a` for some `a` in `α`.-/
lemma isClosed_iff [TopologicalSpace α] [IsLower α] [DecidableEq α] (hT : ∀ p ∈ T, InfPrime p)
    (S : Set T) : IsClosed S ↔ ∃ (a : α), S = hull T a := by
  simp only [← isOpen_compl_iff, (isOpen_iff hT), preimage_compl, compl_inj_iff]

abbrev kernel (S : Set T) := sInf (Subtype.val '' S)

/- The pair of maps `S ↦ sInf S` (kernel) and `a ↦ T ↓∩ Ici a` (hull) form an antitone Galois
connection betwen the subsets of `T` and `α`. -/
open OrderDual in
theorem gc : GaloisConnection (α := Set T) (β := αᵒᵈ)
    (fun S => toDual (kernel S)) (fun a => hull T (ofDual a)) := fun S a => by
  simp only [toDual_sInf, sSup_le_iff, mem_preimage, mem_image, Subtype.exists, exists_and_right,
      exists_eq_right, ← ofDual_le_ofDual, forall_exists_index, OrderDual.forall, ofDual_toDual]
  exact ⟨fun h b hbS => h _ (Subtype.coe_prop b) hbS, fun h b _ hbS => h hbS⟩

lemma gc_closureOperator (S : Set T) : gc.closureOperator S = hull T (kernel S) := by
  simp only [toDual_sInf, GaloisConnection.closureOperator_apply, ofDual_sSup]
  rw [← preimage_comp, ← OrderDual.toDual_symm_eq, Equiv.symm_comp_self, preimage_id_eq, id_eq]

variable (T)

/-- `T` is said to order generate `α` if, for every `a` in `α`, there exists a subset of `T` such
that `a` is the inf of `S`. -/
def OrderGenerate := ∀ (a : α), ∃ (S : Set T), a = kernel S

variable {T}

/--
When `T` is order generating, the kernel and the hull form a Galois insertion
-/
def gi (hG : OrderGenerate T) : GaloisInsertion (α := Set T) (β := αᵒᵈ)
    (fun S => OrderDual.toDual (kernel S))
    (fun a => hull T (OrderDual.ofDual a)) :=
  gc.toGaloisInsertion fun a ↦ (by
    rw [OrderDual.le_toDual]
    obtain ⟨S, hS⟩ := hG a
    exact le_of_le_of_eq (sInf_le_sInf (image_val_mono (fun c hcS => mem_preimage.mpr (mem_Ici.mpr
      (by rw [hS]; exact CompleteSemilatticeInf.sInf_le _ _ (mem_image_of_mem Subtype.val hcS))))))
      (hS.symm))

lemma kernel_hull_eq (hG : OrderGenerate T) (a : α) : kernel (hull T a) = a := by
  conv_rhs => rw [← OrderDual.ofDual_toDual a, ← (gi hG).l_u_eq a]
  rfl

lemma gc_closureOperator_of_isClosed [TopologicalSpace α] [IsLower α] [DecidableEq α]
    (hT : ∀ p ∈ T, InfPrime p) (hG : OrderGenerate T) {C : Set T} (h : IsClosed C) :
    gc.closureOperator C = C := by
  obtain ⟨a, ha⟩ := (isClosed_iff hT C).mp h
  rw [GaloisConnection.closureOperator_apply, ha, kernel_hull_eq hG, OrderDual.ofDual_toDual]

lemma lowerTopology_closureOperator_eq [TopologicalSpace α] [IsLower α] [DecidableEq α]
    (hT : ∀ p ∈ T, InfPrime p) (hG : OrderGenerate T) (S : Set T) :
    (TopologicalSpace.Closeds.gc (α := T)).closureOperator S = hull T (kernel S) := by
  simp only [GaloisConnection.closureOperator_apply, Closeds.coe_closure, closure, le_antisymm_iff]
  constructor
  · exact fun ⦃a⦄ a ↦ a (hull T (kernel S)) ⟨(isClosed_iff hT _).mpr ⟨kernel S, rfl⟩,
      image_subset_iff.mp (fun _ hbS => CompleteSemilatticeInf.sInf_le _ _ hbS)⟩
  · simp_rw [le_eq_subset, subset_sInter_iff]
    intro R hR
    rw [← (gc_closureOperator_of_isClosed hT hG hR.1), ← gc_closureOperator]
    exact ClosureOperator.monotone _ hR.2

theorem lowerTopology_closureOperator_eq_gc_closureOperator
    [TopologicalSpace α] [IsLower α] [DecidableEq α] (hT : ∀ p ∈ T, InfPrime p)
    (hG : OrderGenerate T) :
    (TopologicalSpace.Closeds.gc (α := T)).closureOperator = gc.closureOperator := by
  ext S a
  rw [gc_closureOperator, (lowerTopology_closureOperator_eq hT hG)]

end PrimitiveSpectrum

end PrimativeSpectrum
