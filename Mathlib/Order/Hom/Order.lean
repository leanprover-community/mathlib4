/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Anne Baanen
-/
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Order.Hom.Basic

/-!
# Lattice structure on order homomorphisms

This file defines the lattice structure on order homomorphisms, which are bundled
monotone functions.

## Main definitions

* `OrderHom.instCompleteLattice`: if `β` is a complete lattice, so is `α →o β`

## Tags

monotone map, bundled morphism
-/


namespace OrderHom

variable {α β : Type*}

section Preorder

variable [Preorder α]

instance [SemilatticeSup β] : Max (α →o β) where
  max f g := ⟨fun a => f a ⊔ g a, f.mono.sup g.mono⟩

@[simp] lemma coe_sup [SemilatticeSup β] (f g : α →o β) :
    ((f ⊔ g : α →o β) : α → β) = (f : α → β) ⊔ g := rfl

instance [SemilatticeSup β] : SemilatticeSup (α →o β) :=
  { (_ : PartialOrder (α →o β)) with
    max := Max.max
    le_sup_left := fun _ _ _ => le_sup_left
    le_sup_right := fun _ _ _ => le_sup_right
    sup_le := fun _ _ _ h₀ h₁ x => sup_le (h₀ x) (h₁ x) }

instance [SemilatticeInf β] : Min (α →o β) where
  min f g := ⟨fun a => f a ⊓ g a, f.mono.inf g.mono⟩

@[simp] lemma coe_inf [SemilatticeInf β] (f g : α →o β) :
    ((f ⊓ g : α →o β) : α → β) = (f : α → β) ⊓ g := rfl

instance [SemilatticeInf β] : SemilatticeInf (α →o β) :=
  { (_ : PartialOrder (α →o β)), (dualIso α β).symm.toGaloisInsertion.liftSemilatticeInf with
    min := (· ⊓ ·) }

instance lattice [Lattice β] : Lattice (α →o β) :=
  { (_ : SemilatticeSup (α →o β)), (_ : SemilatticeInf (α →o β)) with }

@[simps]
instance [Preorder β] [OrderBot β] : Bot (α →o β) where
  bot := const α ⊥

instance orderBot [Preorder β] [OrderBot β] : OrderBot (α →o β) where
  bot := ⊥
  bot_le _ _ := bot_le

@[simps]
instance instTopOrderHom [Preorder β] [OrderTop β] : Top (α →o β) where
  top := const α ⊤

instance orderTop [Preorder β] [OrderTop β] : OrderTop (α →o β) where
  top := ⊤
  le_top _ _ := le_top

instance [CompleteLattice β] : InfSet (α →o β) where
  sInf s := ⟨fun x => ⨅ f ∈ s, (f :) x, fun _ _ h => iInf₂_mono fun f _ => f.mono h⟩

@[simp]
theorem sInf_apply [CompleteLattice β] (s : Set (α →o β)) (x : α) :
    sInf s x = ⨅ f ∈ s, (f :) x :=
  rfl

theorem iInf_apply {ι : Sort*} [CompleteLattice β] (f : ι → α →o β) (x : α) :
    (⨅ i, f i) x = ⨅ i, f i x :=
  (sInf_apply _ _).trans iInf_range

@[simp, norm_cast]
theorem coe_iInf {ι : Sort*} [CompleteLattice β] (f : ι → α →o β) :
    ((⨅ i, f i : α →o β) : α → β) = ⨅ i, (f i : α → β) := by
  funext x; simp [iInf_apply]

instance [CompleteLattice β] : SupSet (α →o β) where
  sSup s := ⟨fun x => ⨆ f ∈ s, (f :) x, fun _ _ h => iSup₂_mono fun f _ => f.mono h⟩

@[simp]
theorem sSup_apply [CompleteLattice β] (s : Set (α →o β)) (x : α) :
    sSup s x = ⨆ f ∈ s, (f :) x :=
  rfl

theorem iSup_apply {ι : Sort*} [CompleteLattice β] (f : ι → α →o β) (x : α) :
    (⨆ i, f i) x = ⨆ i, f i x :=
  (sSup_apply _ _).trans iSup_range

@[simp, norm_cast]
theorem coe_iSup {ι : Sort*} [CompleteLattice β] (f : ι → α →o β) :
    ((⨆ i, f i : α →o β) : α → β) = ⨆ i, (f i : α → β) := by
  funext x; simp [iSup_apply]

instance [CompleteLattice β] : CompleteLattice (α →o β) :=
  { (_ : Lattice (α →o β)), OrderHom.orderTop, OrderHom.orderBot with
    -- Porting note: Added `by apply`, was `fun s f hf x => le_iSup_of_le f (le_iSup _ hf)`
    le_sSup := fun s f hf x => le_iSup_of_le f (by apply le_iSup _ hf)
    sSup_le := fun _ _ hf x => iSup₂_le fun g hg => hf g hg x
    le_sInf := fun _ _ hf x => le_iInf₂ fun g hg => hf g hg x
    sInf_le := fun _ f hf _ => iInf_le_of_le f (iInf_le _ hf) }

theorem iterate_sup_le_sup_iff {α : Type*} [SemilatticeSup α] (f : α →o α) :
    (∀ n₁ n₂ a₁ a₂, f^[n₁ + n₂] (a₁ ⊔ a₂) ≤ f^[n₁] a₁ ⊔ f^[n₂] a₂) ↔
      ∀ a₁ a₂, f (a₁ ⊔ a₂) ≤ f a₁ ⊔ a₂ := by
  constructor <;> intro h
  · exact h 1 0
  · intro n₁ n₂ a₁ a₂
    have h' : ∀ n a₁ a₂, f^[n] (a₁ ⊔ a₂) ≤ f^[n] a₁ ⊔ a₂ := by
      intro n
      induction n with
      | zero => intro a₁ a₂; rfl
      | succ n ih =>
        intro a₁ a₂
        calc
          f^[n + 1] (a₁ ⊔ a₂) = f^[n] (f (a₁ ⊔ a₂)) := Function.iterate_succ_apply f n _
          _ ≤ f^[n] (f a₁ ⊔ a₂) := f.mono.iterate n (h a₁ a₂)
          _ ≤ f^[n] (f a₁) ⊔ a₂ := ih _ _
          _ = f^[n + 1] a₁ ⊔ a₂ := by rw [← Function.iterate_succ_apply]
    calc
      f^[n₁ + n₂] (a₁ ⊔ a₂) = f^[n₁] (f^[n₂] (a₁ ⊔ a₂)) :=
        Function.iterate_add_apply f n₁ n₂ _
      _ = f^[n₁] (f^[n₂] (a₂ ⊔ a₁)) := by rw [sup_comm]
      _ ≤ f^[n₁] (f^[n₂] a₂ ⊔ a₁) := f.mono.iterate n₁ (h' n₂ _ _)
      _ = f^[n₁] (a₁ ⊔ f^[n₂] a₂) := by rw [sup_comm]
      _ ≤ f^[n₁] a₁ ⊔ f^[n₂] a₂ := h' n₁ a₁ _

end Preorder

end OrderHom
