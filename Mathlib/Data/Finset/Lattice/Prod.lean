/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod

/-!
# Lattice operations on finsets of products

This file is concerned with folding binary lattice operations over finsets.
-/

assert_not_exists OrderedCommMonoid MonoidWithZero

open Function Multiset OrderDual

variable {F α β γ ι κ : Type*}

namespace Finset

/-! ### sup -/


section Sup

-- TODO: define with just `[Bot α]` where some lemmas hold without requiring `[OrderBot α]`
variable [SemilatticeSup α] [OrderBot α]

/-- See also `Finset.product_biUnion`. -/
theorem sup_product_left (s : Finset β) (t : Finset γ) (f : β × γ → α) :
    (s ×ˢ t).sup f = s.sup fun i => t.sup fun i' => f ⟨i, i'⟩ :=
  eq_of_forall_ge_iff fun a => by simp [@forall_swap _ γ]

theorem sup_product_right (s : Finset β) (t : Finset γ) (f : β × γ → α) :
    (s ×ˢ t).sup f = t.sup fun i' => s.sup fun i => f ⟨i, i'⟩ := by
  rw [sup_product_left, Finset.sup_comm]

section Prod
variable {ι κ α β : Type*} [SemilatticeSup α] [SemilatticeSup β] [OrderBot α] [OrderBot β]
  {s : Finset ι} {t : Finset κ}

@[simp] lemma sup_prodMap (hs : s.Nonempty) (ht : t.Nonempty) (f : ι → α) (g : κ → β) :
    sup (s ×ˢ t) (Prod.map f g) = (sup s f, sup t g) :=
  eq_of_forall_ge_iff fun i ↦ by
    obtain ⟨a, ha⟩ := hs
    obtain ⟨b, hb⟩ := ht
    simp only [Prod.map, Finset.sup_le_iff, mem_product, and_imp, Prod.forall, Prod.le_def]
    exact ⟨fun h ↦ ⟨fun i hi ↦ (h _ _ hi hb).1, fun j hj ↦ (h _ _ ha hj).2⟩, by aesop⟩

end Prod

end Sup

/-! ### inf -/


section Inf

-- TODO: define with just `[Top α]` where some lemmas hold without requiring `[OrderTop α]`
variable [SemilatticeInf α] [OrderTop α]

theorem inf_product_left (s : Finset β) (t : Finset γ) (f : β × γ → α) :
    (s ×ˢ t).inf f = s.inf fun i => t.inf fun i' => f ⟨i, i'⟩ :=
  @sup_product_left αᵒᵈ _ _ _ _ _ _ _

theorem inf_product_right (s : Finset β) (t : Finset γ) (f : β × γ → α) :
    (s ×ˢ t).inf f = t.inf fun i' => s.inf fun i => f ⟨i, i'⟩ :=
  @sup_product_right αᵒᵈ _ _ _ _ _ _ _

section Prod
variable {ι κ α β : Type*} [SemilatticeInf α] [SemilatticeInf β] [OrderTop α] [OrderTop β]
  {s : Finset ι} {t : Finset κ}

@[simp] lemma inf_prodMap (hs : s.Nonempty) (ht : t.Nonempty) (f : ι → α) (g : κ → β) :
    inf (s ×ˢ t) (Prod.map f g) = (inf s f, inf t g) :=
  sup_prodMap (α := αᵒᵈ) (β := βᵒᵈ) hs ht _ _

end Prod

end Inf

section DistribLattice

variable [DistribLattice α]

section OrderBot

variable [OrderBot α] {s : Finset ι} {t : Finset κ} {f : ι → α} {g : κ → α} {a : α}

theorem sup_inf_sup (s : Finset ι) (t : Finset κ) (f : ι → α) (g : κ → α) :
    s.sup f ⊓ t.sup g = (s ×ˢ t).sup fun i => f i.1 ⊓ g i.2 := by
  simp_rw [Finset.sup_inf_distrib_right, Finset.sup_inf_distrib_left, sup_product_left]

end OrderBot

section OrderTop

variable [OrderTop α] {f : ι → α} {g : κ → α} {s : Finset ι} {t : Finset κ} {a : α}

theorem inf_sup_inf (s : Finset ι) (t : Finset κ) (f : ι → α) (g : κ → α) :
    s.inf f ⊔ t.inf g = (s ×ˢ t).inf fun i => f i.1 ⊔ g i.2 :=
  @sup_inf_sup αᵒᵈ _ _ _ _ _ _ _ _

end OrderTop

end DistribLattice

section Sup'

variable [SemilatticeSup α]

variable {s : Finset β} (H : s.Nonempty) (f : β → α)

theorem sup'_product_left {t : Finset γ} (h : (s ×ˢ t).Nonempty) (f : β × γ → α) :
    (s ×ˢ t).sup' h f = s.sup' h.fst fun i => t.sup' h.snd fun i' => f ⟨i, i'⟩ :=
  eq_of_forall_ge_iff fun a => by simp [@forall_swap _ γ]

theorem sup'_product_right {t : Finset γ} (h : (s ×ˢ t).Nonempty) (f : β × γ → α) :
    (s ×ˢ t).sup' h f = t.sup' h.snd fun i' => s.sup' h.fst fun i => f ⟨i, i'⟩ := by
  rw [sup'_product_left, Finset.sup'_comm]

section Prod
variable {ι κ α β : Type*} [SemilatticeSup α] [SemilatticeSup β] {s : Finset ι} {t : Finset κ}

/-- See also `Finset.sup'_prodMap`. -/
lemma prodMk_sup'_sup' (hs : s.Nonempty) (ht : t.Nonempty) (f : ι → α) (g : κ → β) :
    (sup' s hs f, sup' t ht g) = sup' (s ×ˢ t) (hs.product ht) (Prod.map f g) :=
  eq_of_forall_ge_iff fun i ↦ by
    obtain ⟨a, ha⟩ := hs
    obtain ⟨b, hb⟩ := ht
    simp only [Prod.map, sup'_le_iff, mem_product, and_imp, Prod.forall, Prod.le_def]
    exact ⟨by aesop, fun h ↦ ⟨fun i hi ↦ (h _ _ hi hb).1, fun j hj ↦ (h _ _ ha hj).2⟩⟩

/-- See also `Finset.prodMk_sup'_sup'`. -/
-- @[simp] -- TODO: Why does `Prod.map_apply` simplify the LHS?
lemma sup'_prodMap (hst : (s ×ˢ t).Nonempty) (f : ι → α) (g : κ → β) :
    sup' (s ×ˢ t) hst (Prod.map f g) = (sup' s hst.fst f, sup' t hst.snd g) :=
  (prodMk_sup'_sup' _ _ _ _).symm

end Prod

end Sup'

section Inf'

variable [SemilatticeInf α]

variable {s : Finset β} (H : s.Nonempty) (f : β → α)

theorem inf'_product_left {t : Finset γ} (h : (s ×ˢ t).Nonempty) (f : β × γ → α) :
    (s ×ˢ t).inf' h f = s.inf' h.fst fun i => t.inf' h.snd fun i' => f ⟨i, i'⟩ :=
  sup'_product_left (α := αᵒᵈ) h f

theorem inf'_product_right {t : Finset γ} (h : (s ×ˢ t).Nonempty) (f : β × γ → α) :
    (s ×ˢ t).inf' h f = t.inf' h.snd fun i' => s.inf' h.fst fun i => f ⟨i, i'⟩ :=
  sup'_product_right (α := αᵒᵈ) h f

section Prod
variable {ι κ α β : Type*} [SemilatticeInf α] [SemilatticeInf β] {s : Finset ι} {t : Finset κ}

/-- See also `Finset.inf'_prodMap`. -/
lemma prodMk_inf'_inf' (hs : s.Nonempty) (ht : t.Nonempty) (f : ι → α) (g : κ → β) :
    (inf' s hs f, inf' t ht g) = inf' (s ×ˢ t) (hs.product ht) (Prod.map f g) :=
  prodMk_sup'_sup' (α := αᵒᵈ) (β := βᵒᵈ) hs ht _ _

/-- See also `Finset.prodMk_inf'_inf'`. -/
-- @[simp] -- TODO: Why does `Prod.map_apply` simplify the LHS?
lemma inf'_prodMap (hst : (s ×ˢ t).Nonempty) (f : ι → α) (g : κ → β) :
    inf' (s ×ˢ t) hst (Prod.map f g) = (inf' s hst.fst f, inf' t hst.snd g) :=
  (prodMk_inf'_inf' _ _ _ _).symm

end Prod

end Inf'

section DistribLattice
variable [DistribLattice α] {s : Finset ι} {t : Finset κ} (hs : s.Nonempty) (ht : t.Nonempty)
  {f : ι → α} {g : κ → α} {a : α}

theorem sup'_inf_sup' (f : ι → α) (g : κ → α) :
    s.sup' hs f ⊓ t.sup' ht g = (s ×ˢ t).sup' (hs.product ht) fun i => f i.1 ⊓ g i.2 := by
  simp_rw [Finset.sup'_inf_distrib_right, Finset.sup'_inf_distrib_left, sup'_product_left]

theorem inf'_sup_inf' (f : ι → α) (g : κ → α) :
    s.inf' hs f ⊔ t.inf' ht g = (s ×ˢ t).inf' (hs.product ht) fun i => f i.1 ⊔ g i.2 :=
  @sup'_inf_sup' αᵒᵈ _ _ _ _ _ hs ht _ _

end DistribLattice

end Finset
