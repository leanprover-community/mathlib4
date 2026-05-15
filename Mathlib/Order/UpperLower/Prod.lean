/-
Copyright (c) 2022 Yaël Dillies, Sara Rousta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Sara Rousta
-/
module

public import Mathlib.Order.UpperLower.Closure
import Mathlib.Data.Set.Prod
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Monotonicity.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Util.CompileInductive
import Mathlib.Tactic.FBinop

/-!
# Upper and lower set product

The Cartesian product of sets carries over to upper and lower sets in a natural way. This file
defines said product over the types `UpperSet` and `LowerSet` and proves some of its properties.

## Notation

* `×ˢ` is notation for `UpperSet.prod` / `LowerSet.prod`.
-/

@[expose] public section

open Set

variable {α β : Type*}

section Preorder

variable [Preorder α] [Preorder β]

section

variable {s : Set α} {t : Set β}

theorem IsUpperSet.prod (hs : IsUpperSet s) (ht : IsUpperSet t) : IsUpperSet (s ×ˢ t) :=
  fun _ _ h ha => ⟨hs h.1 ha.1, ht h.2 ha.2⟩

theorem IsLowerSet.prod (hs : IsLowerSet s) (ht : IsLowerSet t) : IsLowerSet (s ×ˢ t) :=
  fun _ _ h ha => ⟨hs h.1 ha.1, ht h.2 ha.2⟩

end

namespace UpperSet

variable (s s₁ s₂ : UpperSet α) (t t₁ t₂ : UpperSet β) {x : α × β}

/-- The product of two upper sets as an upper set. -/
def prod : UpperSet (α × β) :=
  ⟨s ×ˢ t, s.2.prod t.2⟩

instance instSProd : SProd (UpperSet α) (UpperSet β) (UpperSet (α × β)) where
  sprod := UpperSet.prod

@[simp, norm_cast]
theorem coe_prod : ((s ×ˢ t : UpperSet (α × β)) : Set (α × β)) = (s : Set α) ×ˢ t :=
  rfl

@[simp]
theorem mem_prod {s : UpperSet α} {t : UpperSet β} : x ∈ s ×ˢ t ↔ x.1 ∈ s ∧ x.2 ∈ t :=
  Iff.rfl

theorem Ici_prod (x : α × β) : Ici x = Ici x.1 ×ˢ Ici x.2 :=
  rfl

@[simp]
theorem Ici_prod_Ici (a : α) (b : β) : Ici a ×ˢ Ici b = Ici (a, b) :=
  rfl

@[simp]
theorem prod_top : s ×ˢ (⊤ : UpperSet β) = ⊤ :=
  ext prod_empty

@[simp]
theorem top_prod : (⊤ : UpperSet α) ×ˢ t = ⊤ :=
  ext empty_prod

@[simp]
theorem bot_prod_bot : (⊥ : UpperSet α) ×ˢ (⊥ : UpperSet β) = ⊥ :=
  ext univ_prod_univ

@[simp]
theorem sup_prod : (s₁ ⊔ s₂) ×ˢ t = s₁ ×ˢ t ⊔ s₂ ×ˢ t :=
  ext inter_prod

@[simp]
theorem prod_sup : s ×ˢ (t₁ ⊔ t₂) = s ×ˢ t₁ ⊔ s ×ˢ t₂ :=
  ext prod_inter

@[simp]
theorem inf_prod : (s₁ ⊓ s₂) ×ˢ t = s₁ ×ˢ t ⊓ s₂ ×ˢ t :=
  ext union_prod

@[simp]
theorem prod_inf : s ×ˢ (t₁ ⊓ t₂) = s ×ˢ t₁ ⊓ s ×ˢ t₂ :=
  ext prod_union

theorem prod_sup_prod : s₁ ×ˢ t₁ ⊔ s₂ ×ˢ t₂ = (s₁ ⊔ s₂) ×ˢ (t₁ ⊔ t₂) :=
  ext prod_inter_prod

variable {s s₁ s₂ t t₁ t₂}

@[gcongr, mono]
theorem prod_mono : s₁ ≤ s₂ → t₁ ≤ t₂ → s₁ ×ˢ t₁ ≤ s₂ ×ˢ t₂ :=
  Set.prod_mono

theorem prod_mono_left : s₁ ≤ s₂ → s₁ ×ˢ t ≤ s₂ ×ˢ t :=
  Set.prod_mono_left

theorem prod_mono_right : t₁ ≤ t₂ → s ×ˢ t₁ ≤ s ×ˢ t₂ :=
  Set.prod_mono_right

@[simp]
theorem prod_self_le_prod_self : s₁ ×ˢ s₁ ≤ s₂ ×ˢ s₂ ↔ s₁ ≤ s₂ :=
  prod_self_subset_prod_self

@[simp]
theorem prod_self_lt_prod_self : s₁ ×ˢ s₁ < s₂ ×ˢ s₂ ↔ s₁ < s₂ :=
  prod_self_ssubset_prod_self

theorem prod_le_prod_iff : s₁ ×ˢ t₁ ≤ s₂ ×ˢ t₂ ↔ s₁ ≤ s₂ ∧ t₁ ≤ t₂ ∨ s₂ = ⊤ ∨ t₂ = ⊤ :=
  prod_subset_prod_iff.trans <| by simp

@[simp]
theorem prod_eq_top : s ×ˢ t = ⊤ ↔ s = ⊤ ∨ t = ⊤ := by
  simp_rw [SetLike.ext'_iff]
  exact prod_eq_empty_iff

@[simp]
theorem codisjoint_prod :
    Codisjoint (s₁ ×ˢ t₁) (s₂ ×ˢ t₂) ↔ Codisjoint s₁ s₂ ∨ Codisjoint t₁ t₂ := by
  simp_rw [codisjoint_iff, prod_sup_prod, prod_eq_top]

end UpperSet

namespace LowerSet

variable (s s₁ s₂ : LowerSet α) (t t₁ t₂ : LowerSet β) {x : α × β}

/-- The product of two lower sets as a lower set. -/
def prod : LowerSet (α × β) := ⟨s ×ˢ t, s.2.prod t.2⟩

instance instSProd : SProd (LowerSet α) (LowerSet β) (LowerSet (α × β)) where
  sprod := LowerSet.prod

@[simp, norm_cast]
theorem coe_prod : ((s ×ˢ t : LowerSet (α × β)) : Set (α × β)) = (s : Set α) ×ˢ t := rfl

@[simp]
theorem mem_prod {s : LowerSet α} {t : LowerSet β} : x ∈ s ×ˢ t ↔ x.1 ∈ s ∧ x.2 ∈ t :=
  Iff.rfl

theorem Iic_prod (x : α × β) : Iic x = Iic x.1 ×ˢ Iic x.2 :=
  rfl

@[simp]
theorem Ici_prod_Ici (a : α) (b : β) : Iic a ×ˢ Iic b = Iic (a, b) :=
  rfl

@[simp]
theorem prod_bot : s ×ˢ (⊥ : LowerSet β) = ⊥ :=
  ext prod_empty

@[simp]
theorem bot_prod : (⊥ : LowerSet α) ×ˢ t = ⊥ :=
  ext empty_prod

@[simp]
theorem top_prod_top : (⊤ : LowerSet α) ×ˢ (⊤ : LowerSet β) = ⊤ :=
  ext univ_prod_univ

@[simp]
theorem inf_prod : (s₁ ⊓ s₂) ×ˢ t = s₁ ×ˢ t ⊓ s₂ ×ˢ t :=
  ext inter_prod

@[simp]
theorem prod_inf : s ×ˢ (t₁ ⊓ t₂) = s ×ˢ t₁ ⊓ s ×ˢ t₂ :=
  ext prod_inter

@[simp]
theorem sup_prod : (s₁ ⊔ s₂) ×ˢ t = s₁ ×ˢ t ⊔ s₂ ×ˢ t :=
  ext union_prod

@[simp]
theorem prod_sup : s ×ˢ (t₁ ⊔ t₂) = s ×ˢ t₁ ⊔ s ×ˢ t₂ :=
  ext prod_union

theorem prod_inf_prod : s₁ ×ˢ t₁ ⊓ s₂ ×ˢ t₂ = (s₁ ⊓ s₂) ×ˢ (t₁ ⊓ t₂) :=
  ext prod_inter_prod

variable {s s₁ s₂ t t₁ t₂}

theorem prod_mono : s₁ ≤ s₂ → t₁ ≤ t₂ → s₁ ×ˢ t₁ ≤ s₂ ×ˢ t₂ := Set.prod_mono

theorem prod_mono_left : s₁ ≤ s₂ → s₁ ×ˢ t ≤ s₂ ×ˢ t := Set.prod_mono_left

theorem prod_mono_right : t₁ ≤ t₂ → s ×ˢ t₁ ≤ s ×ˢ t₂ := Set.prod_mono_right

@[simp]
theorem prod_self_le_prod_self : s₁ ×ˢ s₁ ≤ s₂ ×ˢ s₂ ↔ s₁ ≤ s₂ :=
  prod_self_subset_prod_self

@[simp]
theorem prod_self_lt_prod_self : s₁ ×ˢ s₁ < s₂ ×ˢ s₂ ↔ s₁ < s₂ :=
  prod_self_ssubset_prod_self

theorem prod_le_prod_iff : s₁ ×ˢ t₁ ≤ s₂ ×ˢ t₂ ↔ s₁ ≤ s₂ ∧ t₁ ≤ t₂ ∨ s₁ = ⊥ ∨ t₁ = ⊥ :=
  prod_subset_prod_iff.trans <| by simp

@[simp]
theorem prod_eq_bot : s ×ˢ t = ⊥ ↔ s = ⊥ ∨ t = ⊥ := by
  simp_rw [SetLike.ext'_iff]
  exact prod_eq_empty_iff

@[simp]
theorem disjoint_prod : Disjoint (s₁ ×ˢ t₁) (s₂ ×ˢ t₂) ↔ Disjoint s₁ s₂ ∨ Disjoint t₁ t₂ := by
  simp_rw [disjoint_iff, prod_inf_prod, prod_eq_bot]

end LowerSet

@[simp]
theorem upperClosure_prod (s : Set α) (t : Set β) :
    upperClosure (s ×ˢ t) = upperClosure s ×ˢ upperClosure t := by
  ext
  simp [Prod.le_def, @and_and_and_comm _ (_ ∈ t)]

@[simp]
theorem lowerClosure_prod (s : Set α) (t : Set β) :
    lowerClosure (s ×ˢ t) = lowerClosure s ×ˢ lowerClosure t := by
  ext
  simp [Prod.le_def, @and_and_and_comm _ (_ ∈ t)]

end Preorder
