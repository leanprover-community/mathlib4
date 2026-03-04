/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
module

public import Mathlib.Data.Set.Basic

/-! # Lemmas about `inclusion`, the injection of subtypes induced by `⊆` -/

@[expose] public section

open Function

namespace Set

variable {α : Type*} {s t u : Set α}

/-- `inclusion` is the "identity" function between two subsets `s` and `t`, where `s ⊆ t` -/
abbrev inclusion (h : s ⊆ t) : s → t := fun x ↦ ⟨x, h x.prop⟩

theorem inclusion_self (x : s) : inclusion Subset.rfl x = x :=
  rfl

theorem inclusion_eq_id (h : s ⊆ s) : inclusion h = id :=
  rfl

theorem inclusion_eq_subtype_map (h : s ⊆ t) : inclusion h = Subtype.map id h :=
  rfl

@[simp]
theorem inclusion_mk {h : s ⊆ t} (a : α) (ha : a ∈ s) : inclusion h ⟨a, ha⟩ = ⟨a, h ha⟩ :=
  rfl

theorem inclusion_right (h : s ⊆ t) (x : t) (m : (x : α) ∈ s) : inclusion h ⟨x, m⟩ = x :=
  rfl

@[simp]
theorem inclusion_inclusion (hst : s ⊆ t) (htu : t ⊆ u) (x : s) :
    inclusion htu (inclusion hst x) = inclusion (hst.trans htu) x :=
  rfl

@[simp]
theorem inclusion_comp_inclusion {α} {s t u : Set α} (hst : s ⊆ t) (htu : t ⊆ u) :
    inclusion htu ∘ inclusion hst = inclusion (hst.trans htu) :=
  funext (inclusion_inclusion hst htu)

@[simp]
theorem coe_inclusion (h : s ⊆ t) (x : s) : (inclusion h x : α) = (x : α) :=
  rfl

theorem val_comp_inclusion (h : s ⊆ t) : Subtype.val ∘ inclusion h = Subtype.val :=
  rfl

theorem inclusion_injective (h : s ⊆ t) : (inclusion h).Injective :=
  Subtype.map_injective h injective_id

theorem inclusion_inj (h : s ⊆ t) {x y : s} : inclusion h x = inclusion h y ↔ x = y :=
  (inclusion_injective h).eq_iff

theorem eq_of_inclusion_surjective {s t : Set α} {h : s ⊆ t}
    (h_surj : Function.Surjective (inclusion h)) : s = t :=
  h.antisymm fun x hx ↦ by grind [h_surj ⟨x, hx⟩]

theorem inclusion_le_inclusion [LE α] {s t : Set α} (h : s ⊆ t) {x y : s} :
    inclusion h x ≤ inclusion h y ↔ x ≤ y := .rfl

theorem inclusion_lt_inclusion [LT α] {s t : Set α} (h : s ⊆ t) {x y : s} :
    inclusion h x < inclusion h y ↔ x < y := .rfl

end Set
