/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Prod

/-!
# Lattice operations on finsets of products

This file is concerned with folding binary lattice operations over finsets.
-/

public section

assert_not_exists IsOrderedMonoid MonoidWithZero

open Function Multiset OrderDual

variable {F α β γ ι κ : Type*}

namespace Finset


section Sup

-- TODO: define with just `[Bot α]` where some lemmas hold without requiring `[OrderBot α]`
variable [SemilatticeSup α] [OrderBot α]

/-- See also `Finset.product_biUnion`. -/
@[to_dual inf_product_left]
theorem sup_product_left (s : Finset β) (t : Finset γ) (f : β × γ → α) :
    (s ×ˢ t).sup f = s.sup fun i => t.sup fun i' => f ⟨i, i'⟩ :=
  eq_of_forall_ge_iff fun a => by simp [@forall_comm _ γ]

@[to_dual inf_product_right]
theorem sup_product_right (s : Finset β) (t : Finset γ) (f : β × γ → α) :
    (s ×ˢ t).sup f = t.sup fun i' => s.sup fun i => f ⟨i, i'⟩ := by
  rw [sup_product_left, Finset.sup_comm]

section Prod
variable {ι κ α β : Type*} [SemilatticeSup α] [SemilatticeSup β] [OrderBot α] [OrderBot β]
  {s : Finset ι} {t : Finset κ}

@[to_dual (attr := simp)]
lemma sup_prodMap (hs : s.Nonempty) (ht : t.Nonempty) (f : ι → α) (g : κ → β) :
    sup (s ×ˢ t) (Prod.map f g) = (sup s f, sup t g) :=
  eq_of_forall_ge_iff fun i ↦ by
    obtain ⟨a, ha⟩ := hs
    obtain ⟨b, hb⟩ := ht
    simp only [Prod.map, Finset.sup_le_iff, mem_product, and_imp, Prod.forall, Prod.le_def]
    exact ⟨fun h ↦ ⟨fun i hi ↦ (h _ _ hi hb).1, fun j hj ↦ (h _ _ ha hj).2⟩, by simp_all⟩

end Prod

end Sup

section DistribLattice

variable [DistribLattice α]

variable [OrderBot α] {s : Finset ι} {t : Finset κ} {f : ι → α} {g : κ → α} {a : α}

@[to_dual]
theorem sup_inf_sup (s : Finset ι) (t : Finset κ) (f : ι → α) (g : κ → α) :
    s.sup f ⊓ t.sup g = (s ×ˢ t).sup fun i => f i.1 ⊓ g i.2 := by
  simp_rw [Finset.sup_inf_distrib_right, Finset.sup_inf_distrib_left, sup_product_left]

end DistribLattice

section Sup'

variable [SemilatticeSup α]

variable {s : Finset β} (H : s.Nonempty) (f : β → α)

@[to_dual inf'_product_left]
theorem sup'_product_left {t : Finset γ} (h : (s ×ˢ t).Nonempty) (f : β × γ → α) :
    (s ×ˢ t).sup' h f = s.sup' h.fst fun i => t.sup' h.snd fun i' => f ⟨i, i'⟩ :=
  eq_of_forall_ge_iff fun a => by simp [@forall_comm _ γ]

@[to_dual inf'_product_right]
theorem sup'_product_right {t : Finset γ} (h : (s ×ˢ t).Nonempty) (f : β × γ → α) :
    (s ×ˢ t).sup' h f = t.sup' h.snd fun i' => s.sup' h.fst fun i => f ⟨i, i'⟩ := by
  rw [sup'_product_left, Finset.sup'_comm]

section Prod
variable {ι κ α β : Type*} [SemilatticeSup α] [SemilatticeSup β] {s : Finset ι} {t : Finset κ}

/-- See also `Finset.sup'_prodMap`. -/
@[to_dual /-- See also `Finset.inf'_prodMap`. -/]
lemma prodMk_sup'_sup' (hs : s.Nonempty) (ht : t.Nonempty) (f : ι → α) (g : κ → β) :
    (sup' s hs f, sup' t ht g) = sup' (s ×ˢ t) (hs.product ht) (Prod.map f g) :=
  eq_of_forall_ge_iff fun i ↦ by
    obtain ⟨a, ha⟩ := hs
    obtain ⟨b, hb⟩ := ht
    simp only [Prod.map, sup'_le_iff, mem_product, and_imp, Prod.forall, Prod.le_def]
    exact ⟨by simp_all, fun h ↦ ⟨fun i hi ↦ (h _ _ hi hb).1, fun j hj ↦ (h _ _ ha hj).2⟩⟩

/-- See also `Finset.prodMk_sup'_sup'`. -/
@[to_dual -- (attr := simp) -- TODO: Why does `Prod.map_apply` simplify the LHS?
/-- See also `Finset.prodMk_inf'_inf'`. -/]
lemma sup'_prodMap (hst : (s ×ˢ t).Nonempty) (f : ι → α) (g : κ → β) :
    sup' (s ×ˢ t) hst (Prod.map f g) = (sup' s hst.fst f, sup' t hst.snd g) :=
  (prodMk_sup'_sup' _ _ _ _).symm

end Prod

end Sup'

section DistribLattice
variable [DistribLattice α] {s : Finset ι} {t : Finset κ} (hs : s.Nonempty) (ht : t.Nonempty)
  {f : ι → α} {g : κ → α} {a : α}

@[to_dual]
theorem sup'_inf_sup' (f : ι → α) (g : κ → α) :
    s.sup' hs f ⊓ t.sup' ht g = (s ×ˢ t).sup' (hs.product ht) fun i => f i.1 ⊓ g i.2 := by
  simp_rw [Finset.sup'_inf_distrib_right, Finset.sup'_inf_distrib_left, sup'_product_left]

end DistribLattice

end Finset
