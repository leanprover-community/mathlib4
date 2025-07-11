/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Filippo A. E. Nuccio, Sam van Gool
-/
import Mathlib.Data.Fintype.Order
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Order.Irreducible
import Mathlib.Order.UpperLower.Closure

/-!
# Birkhoff representation

This file proves two facts which together are commonly referred to as "Birkhoff representation":
1. Any nonempty finite partial order is isomorphic to the partial order of sup-irreducible elements
  in its lattice of lower sets.
2. Any nonempty finite distributive lattice is isomorphic to the lattice of lower sets of its
  partial order of sup-irreducible elements.

## Main declarations

For a finite nonempty partial order `α`:
* `OrderEmbedding.supIrredLowerSet`: `α` is isomorphic to the order of its irreducible lower sets.

If `α` is moreover a distributive lattice:
* `OrderIso.lowerSetSupIrred`: `α` is isomorphic to the lattice of lower sets of its irreducible
  elements.
* `OrderEmbedding.birkhoffSet`, `OrderEmbedding.birkhoffFinset`: Order embedding of `α` into the
  powerset lattice of its irreducible elements.
* `LatticeHom.birkhoffSet`, `LatticeHom.birkhoffFinet`: Same as the previous two, but bundled as
  an injective lattice homomorphism.
* `exists_birkhoff_representation`: `α` embeds into some powerset algebra. You should prefer using
  this over the explicit Birkhoff embedding because the Birkhoff embedding is littered with
  decidability footguns that this existential-packaged version can afford to avoid.

## See also

These results form the object part of finite Stone duality: the functorial contravariant
equivalence between the category of finite distributive lattices and the category of finite
partial orders. TODO: extend to morphisms.

## References

* [G. Birkhoff, *Rings of sets*][birkhoff1937]

## Tags

birkhoff, representation, stone duality, lattice embedding
-/

open Finset Function OrderDual UpperSet LowerSet

variable {α : Type*}

section PartialOrder
variable [PartialOrder α]

namespace UpperSet
variable {s : UpperSet α}

@[simp] lemma infIrred_Ici (a : α) : InfIrred (Ici a) := by
  refine ⟨fun h ↦ Ici_ne_top h.eq_top, fun s t hst ↦ ?_⟩
  have := mem_Ici_iff.2 (le_refl a)
  rw [← hst] at this
  exact this.imp (fun ha ↦ le_antisymm (le_Ici.2 ha) <| hst.ge.trans inf_le_left) fun ha ↦
      le_antisymm (le_Ici.2 ha) <| hst.ge.trans inf_le_right

variable [Finite α]

@[simp] lemma infIrred_iff_of_finite : InfIrred s ↔ ∃ a, Ici a = s := by
  refine ⟨fun hs ↦ ?_, ?_⟩
  · obtain ⟨a, ha, has⟩ := (s : Set α).toFinite.exists_minimal (coe_nonempty.2 hs.ne_top)
    exact ⟨a, (hs.2 <| erase_inf_Ici ha fun b hb ↦ le_imp_eq_iff_le_imp_ge.2 <| has hb).resolve_left
      (lt_erase.2 ha).ne'⟩
  · rintro ⟨a, rfl⟩
    exact infIrred_Ici _

end UpperSet

namespace LowerSet
variable {s : LowerSet α}

@[simp] lemma supIrred_Iic (a : α) : SupIrred (Iic a) := by
  refine ⟨fun h ↦ Iic_ne_bot h.eq_bot, fun s t hst ↦ ?_⟩
  have := mem_Iic_iff.2 (le_refl a)
  rw [← hst] at this
  exact this.imp (fun ha ↦ (le_sup_left.trans_eq hst).antisymm <| Iic_le.2 ha) fun ha ↦
    (le_sup_right.trans_eq hst).antisymm <| Iic_le.2 ha

variable [Finite α]

@[simp] lemma supIrred_iff_of_finite : SupIrred s ↔ ∃ a, Iic a = s := by
  refine ⟨fun hs ↦ ?_, ?_⟩
  · obtain ⟨a, ha, has⟩ := (s : Set α).toFinite.exists_maximal (coe_nonempty.2 hs.ne_bot)
    exact ⟨a, (hs.2 <| erase_sup_Iic ha fun b hb ↦
      le_imp_eq_iff_le_imp_ge'.2 <| has hb).resolve_left (erase_lt.2 ha).ne⟩
  · rintro ⟨a, rfl⟩
    exact supIrred_Iic _

end LowerSet

namespace OrderEmbedding

/-- The **Birkhoff Embedding** of a finite partial order as sup-irreducible elements in its
lattice of lower sets. -/
def supIrredLowerSet : α ↪o {s : LowerSet α // SupIrred s} where
  toFun a := ⟨Iic a, supIrred_Iic _⟩
  inj' _ := by simp
  map_rel_iff' := by simp

/-- The **Birkhoff Embedding** of a finite partial order as inf-irreducible elements in its
lattice of lower sets. -/
def infIrredUpperSet : α ↪o {s : UpperSet α // InfIrred s} where
  toFun a := ⟨Ici a, infIrred_Ici _⟩
  inj' _ := by simp
  map_rel_iff' := by simp

@[simp] lemma supIrredLowerSet_apply (a : α) : supIrredLowerSet a = ⟨Iic a, supIrred_Iic _⟩ := rfl
@[simp] lemma infIrredUpperSet_apply (a : α) : infIrredUpperSet a = ⟨Ici a, infIrred_Ici _⟩ := rfl

variable [Finite α]

lemma supIrredLowerSet_surjective : Surjective (supIrredLowerSet (α := α)) := by
  aesop (add simp Surjective)

lemma infIrredUpperSet_surjective : Surjective (infIrredUpperSet (α := α)) := by
  aesop (add simp Surjective)

end OrderEmbedding

namespace OrderIso
variable [Finite α]

/-- **Birkhoff Representation for partial orders.** Any partial order is isomorphic
to the partial order of sup-irreducible elements in its lattice of lower sets. -/
noncomputable def supIrredLowerSet : α ≃o {s : LowerSet α // SupIrred s} :=
  RelIso.ofSurjective _ OrderEmbedding.supIrredLowerSet_surjective

/-- **Birkhoff Representation for partial orders.** Any partial order is isomorphic
to the partial order of inf-irreducible elements in its lattice of upper sets. -/
noncomputable def infIrredUpperSet : α ≃o {s : UpperSet α // InfIrred s} :=
  RelIso.ofSurjective _ OrderEmbedding.infIrredUpperSet_surjective

@[simp] lemma supIrredLowerSet_apply (a : α) : supIrredLowerSet a = ⟨Iic a, supIrred_Iic _⟩ := rfl
@[simp] lemma infIrredUpperSet_apply (a : α) : infIrredUpperSet a = ⟨Ici a, infIrred_Ici _⟩ := rfl

end OrderIso
end PartialOrder

namespace OrderIso
section SemilatticeSup
variable [SemilatticeSup α] [OrderBot α] [Finite α]

@[simp] lemma supIrredLowerSet_symm_apply (s : {s : LowerSet α // SupIrred s}) [Fintype s] :
    supIrredLowerSet.symm s = (s.1 : Set α).toFinset.sup id := by
  classical
  obtain ⟨s, hs⟩ := s
  obtain ⟨a, rfl⟩ := supIrred_iff_of_finite.1 hs
  cases nonempty_fintype α
  have : LocallyFiniteOrder α := Fintype.toLocallyFiniteOrder
  simp [symm_apply_eq]

end SemilatticeSup

section SemilatticeInf
variable [SemilatticeInf α] [OrderTop α] [Finite α]

@[simp] lemma infIrredUpperSet_symm_apply (s : {s : UpperSet α // InfIrred s}) [Fintype s] :
    infIrredUpperSet.symm s = (s.1 : Set α).toFinset.inf id := by
  classical
  obtain ⟨s, hs⟩ := s
  obtain ⟨a, rfl⟩ := infIrred_iff_of_finite.1 hs
  cases nonempty_fintype α
  have : LocallyFiniteOrder α := Fintype.toLocallyFiniteOrder
  simp [symm_apply_eq]

end SemilatticeInf
end OrderIso

section DistribLattice
variable [DistribLattice α] [Fintype α] [@DecidablePred α SupIrred]

open Classical in
/-- **Birkhoff Representation for finite distributive lattices**. Any nonempty finite distributive
lattice is isomorphic to the lattice of lower sets of its sup-irreducible elements. -/
noncomputable def OrderIso.lowerSetSupIrred [OrderBot α] : α ≃o LowerSet {a : α // SupIrred a} :=
  Equiv.toOrderIso
    { toFun := fun a ↦ ⟨{b | ↑b ≤ a}, fun _ _ hcb hba ↦ hba.trans' hcb⟩
      invFun := fun s ↦ (s : Set {a : α // SupIrred a}).toFinset.sup (↑)
      left_inv := fun a ↦ by
        refine le_antisymm (Finset.sup_le fun b ↦ Set.mem_toFinset.1) ?_
        obtain ⟨s, rfl, hs⟩ := exists_supIrred_decomposition a
        exact Finset.sup_le fun i hi ↦
          le_sup_of_le (b := ⟨i, hs hi⟩) (Set.mem_toFinset.2 <| le_sup (f := id) hi) le_rfl
      right_inv := fun s ↦ by
        ext a
        dsimp
        refine ⟨fun ha ↦ ?_, fun ha ↦ ?_⟩
        · obtain ⟨i, hi, ha⟩ := a.2.supPrime.le_finset_sup.1 ha
          exact s.lower ha (Set.mem_toFinset.1 hi)
        · dsimp
          exact le_sup (Set.mem_toFinset.2 ha) }
    (fun _ _ hbc _ ↦ le_trans' hbc) fun _ _ hst ↦ Finset.sup_mono <| Set.toFinset_mono hst

namespace OrderEmbedding

/-- **Birkhoff's Representation Theorem**. Any finite distributive lattice can be embedded in a
powerset lattice. -/
noncomputable def birkhoffSet : α ↪o Set {a : α // SupIrred a} := by
  by_cases h : IsEmpty α
  · exact OrderEmbedding.ofIsEmpty
  rw [not_isEmpty_iff] at h
  have := Fintype.toOrderBot α
  exact OrderIso.lowerSetSupIrred.toOrderEmbedding.trans ⟨⟨_, SetLike.coe_injective⟩, Iff.rfl⟩

/-- **Birkhoff's Representation Theorem**. Any finite distributive lattice can be embedded in a
powerset lattice. -/
noncomputable def birkhoffFinset : α ↪o Finset {a : α // SupIrred a} := by
  exact birkhoffSet.trans Fintype.finsetOrderIsoSet.symm.toOrderEmbedding

@[simp] lemma coe_birkhoffFinset (a : α) : birkhoffFinset a = birkhoffSet a := by
  classical
  -- TODO: This should be a single `simp` call but `simp` refuses to use
  -- `OrderIso.coe_toOrderEmbedding` and `Fintype.coe_finsetOrderIsoSet_symm`
  simp [birkhoffFinset]
  rw [OrderIso.coe_toOrderEmbedding, Fintype.coe_finsetOrderIsoSet_symm]
  simp

@[simp] lemma birkhoffSet_sup (a b : α) : birkhoffSet (a ⊔ b) = birkhoffSet a ∪ birkhoffSet b := by
  unfold OrderEmbedding.birkhoffSet; split <;> simp [eq_iff_true_of_subsingleton]

@[simp] lemma birkhoffSet_inf (a b : α) : birkhoffSet (a ⊓ b) = birkhoffSet a ∩ birkhoffSet b := by
  unfold OrderEmbedding.birkhoffSet; split <;> simp [eq_iff_true_of_subsingleton]

@[simp] lemma birkhoffSet_apply [OrderBot α] (a : α) :
    birkhoffSet a = OrderIso.lowerSetSupIrred a := by
  simp [birkhoffSet]; have : Subsingleton (OrderBot α) := inferInstance; convert rfl

variable [DecidableEq α]

@[simp] lemma birkhoffFinset_sup (a b : α) :
    birkhoffFinset (a ⊔ b) = birkhoffFinset a ∪ birkhoffFinset b := by
  classical
  dsimp [OrderEmbedding.birkhoffFinset]
  rw [birkhoffSet_sup, OrderIso.coe_toOrderEmbedding]
  simp

@[simp] lemma birkhoffFinset_inf (a b : α) :
    birkhoffFinset (a ⊓ b) = birkhoffFinset a ∩ birkhoffFinset b := by
  classical
  dsimp [OrderEmbedding.birkhoffFinset]
  rw [birkhoffSet_inf, OrderIso.coe_toOrderEmbedding]
  simp

end OrderEmbedding

namespace LatticeHom

/-- **Birkhoff's Representation Theorem**. Any finite distributive lattice can be embedded in a
powerset lattice. -/
noncomputable def birkhoffSet : LatticeHom α (Set {a : α // SupIrred a}) where
  toFun := OrderEmbedding.birkhoffSet
  map_sup' := OrderEmbedding.birkhoffSet_sup
  map_inf' := OrderEmbedding.birkhoffSet_inf

open Classical in
/-- **Birkhoff's Representation Theorem**. Any finite distributive lattice can be embedded in a
powerset lattice. -/
noncomputable def birkhoffFinset : LatticeHom α (Finset {a : α // SupIrred a}) where
  toFun := OrderEmbedding.birkhoffFinset
  map_sup' := OrderEmbedding.birkhoffFinset_sup
  map_inf' := OrderEmbedding.birkhoffFinset_inf

lemma birkhoffFinset_injective : Injective (birkhoffFinset (α := α)) :=
  OrderEmbedding.birkhoffFinset.injective

end LatticeHom

lemma exists_birkhoff_representation.{u} (α : Type u) [Finite α] [DistribLattice α] :
    ∃ (β : Type u) (_ : DecidableEq β) (_ : Fintype β) (f : LatticeHom α (Finset β)),
      Injective f := by
  classical
  cases nonempty_fintype α
  exact ⟨{a : α // SupIrred a}, _, inferInstance, _, LatticeHom.birkhoffFinset_injective⟩

end DistribLattice
