/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Anne Baanen

! This file was ported from Lean 3 source module order.hom.order
! leanprover-community/mathlib commit ba2245edf0c8bb155f1569fd9b9492a9b384cde6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.GaloisConnection
import Mathlib.Order.Hom.Basic

/-!
# Lattice structure on order homomorphisms

This file defines the lattice structure on order homomorphisms, which are bundled
monotone functions.

## Main definitions

 * `order_hom.complete_lattice`: if `β` is a complete lattice, so is `α →o β`

## Tags

monotone map, bundled morphism
-/


namespace OrderHom

variable {α β : Type _}

section Preorder

variable [Preorder α]

@[simps]
instance [SemilatticeSup β] :
    HasSup (α →o β) where sup f g := ⟨fun a => f a ⊔ g a, f.mono.sup g.mono⟩

instance [SemilatticeSup β] : SemilatticeSup (α →o β) :=
  { (_ : PartialOrder (α →o β)) with
    sup := HasSup.sup
    le_sup_left := fun a b x => le_sup_left
    le_sup_right := fun a b x => le_sup_right
    sup_le := fun a b c h₀ h₁ x => sup_le (h₀ x) (h₁ x) }

@[simps]
instance [SemilatticeInf β] :
    HasInf (α →o β) where inf f g := ⟨fun a => f a ⊓ g a, f.mono.inf g.mono⟩

instance [SemilatticeInf β] : SemilatticeInf (α →o β) :=
  { (_ : PartialOrder (α →o β)), (dualIso α β).symm.toGaloisInsertion.liftSemilatticeInf with
    inf := (· ⊓ ·) }

instance [Lattice β] : Lattice (α →o β) :=
  { (_ : SemilatticeSup (α →o β)), (_ : SemilatticeInf (α →o β)) with }

@[simps]
instance [Preorder β] [OrderBot β] : Bot (α →o β) where bot := const α ⊥

instance [Preorder β] [OrderBot β] :
    OrderBot (α →o β) where
  bot := ⊥
  bot_le a x := bot_le

@[simps]
instance [Preorder β] [OrderTop β] : Top (α →o β) where top := const α ⊤

instance [Preorder β] [OrderTop β] :
    OrderTop (α →o β) where
  top := ⊤
  le_top a x := le_top

instance [CompleteLattice β] :
    InfSet
      (α →o
        β) where inf s := ⟨fun x => ⨅ f ∈ s, (f : _) x, fun x y h => infᵢ₂_mono fun f _ => f.mono h⟩

@[simp]
theorem Inf_apply [CompleteLattice β] (s : Set (α →o β)) (x : α) : infₛ s x = ⨅ f ∈ s, (f : _) x :=
  rfl
#align order_hom.Inf_apply OrderHom.Inf_apply

theorem infi_apply {ι : Sort _} [CompleteLattice β] (f : ι → α →o β) (x : α) :
    (⨅ i, f i) x = ⨅ i, f i x :=
  (Inf_apply _ _).trans infᵢ_range
#align order_hom.infi_apply OrderHom.infi_apply

@[simp, norm_cast]
theorem coe_infi {ι : Sort _} [CompleteLattice β] (f : ι → α →o β) :
    ((⨅ i, f i : α →o β) : α → β) = ⨅ i, f i :=
  funext fun x => (infi_apply f x).trans (@infᵢ_apply _ _ _ _ (fun i => f i) _).symm
#align order_hom.coe_infi OrderHom.coe_infi

instance [CompleteLattice β] :
    SupSet
      (α →o
        β) where sup s := ⟨fun x => ⨆ f ∈ s, (f : _) x, fun x y h => supᵢ₂_mono fun f _ => f.mono h⟩

@[simp]
theorem Sup_apply [CompleteLattice β] (s : Set (α →o β)) (x : α) : supₛ s x = ⨆ f ∈ s, (f : _) x :=
  rfl
#align order_hom.Sup_apply OrderHom.Sup_apply

theorem supr_apply {ι : Sort _} [CompleteLattice β] (f : ι → α →o β) (x : α) :
    (⨆ i, f i) x = ⨆ i, f i x :=
  (Sup_apply _ _).trans supᵢ_range
#align order_hom.supr_apply OrderHom.supr_apply

@[simp, norm_cast]
theorem coe_supr {ι : Sort _} [CompleteLattice β] (f : ι → α →o β) :
    ((⨆ i, f i : α →o β) : α → β) = ⨆ i, f i :=
  funext fun x => (supr_apply f x).trans (@supᵢ_apply _ _ _ _ (fun i => f i) _).symm
#align order_hom.coe_supr OrderHom.coe_supr

instance [CompleteLattice β] : CompleteLattice (α →o β) :=
  { (_ : Lattice (α →o β)), OrderHom.orderTop, OrderHom.orderBot with
    sup := supₛ
    le_Sup := fun s f hf x => le_supᵢ_of_le f (le_supᵢ _ hf)
    Sup_le := fun s f hf x => supᵢ₂_le fun g hg => hf g hg x
    inf := infₛ
    le_Inf := fun s f hf x => le_infᵢ₂ fun g hg => hf g hg x
    Inf_le := fun s f hf x => infᵢ_le_of_le f (infᵢ_le _ hf) }

theorem iterate_sup_le_sup_iff {α : Type _} [SemilatticeSup α] (f : α →o α) :
    (∀ n₁ n₂ a₁ a₂, (f^[n₁ + n₂]) (a₁ ⊔ a₂) ≤ (f^[n₁]) a₁ ⊔ (f^[n₂]) a₂) ↔
      ∀ a₁ a₂, f (a₁ ⊔ a₂) ≤ f a₁ ⊔ a₂ :=
  by
  constructor <;> intro h
  · exact h 1 0
  · intro n₁ n₂ a₁ a₂
    have h' : ∀ n a₁ a₂, (f^[n]) (a₁ ⊔ a₂) ≤ (f^[n]) a₁ ⊔ a₂ := by
      intro n
      induction' n with n ih <;> intro a₁ a₂
      · rfl
      ·
        calc
          (f^[n + 1]) (a₁ ⊔ a₂) = (f^[n]) (f (a₁ ⊔ a₂)) := Function.iterate_succ_apply f n _
          _ ≤ (f^[n]) (f a₁ ⊔ a₂) := f.mono.iterate n (h a₁ a₂)
          _ ≤ (f^[n]) (f a₁) ⊔ a₂ := ih _ _
          _ = (f^[n + 1]) a₁ ⊔ a₂ := by rw [← Function.iterate_succ_apply]

    calc
      (f^[n₁ + n₂]) (a₁ ⊔ a₂) = (f^[n₁]) ((f^[n₂]) (a₁ ⊔ a₂)) :=
        Function.iterate_add_apply f n₁ n₂ _
      _ = (f^[n₁]) ((f^[n₂]) (a₂ ⊔ a₁)) := by rw [sup_comm]
      _ ≤ (f^[n₁]) ((f^[n₂]) a₂ ⊔ a₁) := f.mono.iterate n₁ (h' n₂ _ _)
      _ = (f^[n₁]) (a₁ ⊔ (f^[n₂]) a₂) := by rw [sup_comm]
      _ ≤ (f^[n₁]) a₁ ⊔ (f^[n₂]) a₂ := h' n₁ a₁ _

#align order_hom.iterate_sup_le_sup_iff OrderHom.iterate_sup_le_sup_iff

end Preorder

end OrderHom
