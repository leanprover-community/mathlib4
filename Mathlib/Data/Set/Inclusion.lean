/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
import Mathlib.Data.Set.Basic

/-! # Lemmas about `inclusion`, the injection of subtypes induced by `⊆` -/

open Function

namespace Set

variable {α : Type*} {s t u : Set α}

/-- `inclusion` is the "identity" function between two subsets `s` and `t`, where `s ⊆ t` -/
abbrev inclusion (h : s ⊆ t) : s → t := fun x : s => (⟨x, h x.2⟩ : t)

theorem inclusion_self (x : s) : inclusion Subset.rfl x = x := by
  cases x
  rfl

theorem inclusion_eq_id (h : s ⊆ s) : inclusion h = id :=
  funext inclusion_self

@[simp]
theorem inclusion_mk {h : s ⊆ t} (a : α) (ha : a ∈ s) : inclusion h ⟨a, ha⟩ = ⟨a, h ha⟩ :=
  rfl

theorem inclusion_right (h : s ⊆ t) (x : t) (m : (x : α) ∈ s) : inclusion h ⟨x, m⟩ = x := by
  cases x
  rfl

@[simp]
theorem inclusion_inclusion (hst : s ⊆ t) (htu : t ⊆ u) (x : s) :
    inclusion htu (inclusion hst x) = inclusion (hst.trans htu) x := by
  cases x
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

theorem inclusion_injective (h : s ⊆ t) : Injective (inclusion h)
  | ⟨_, _⟩, ⟨_, _⟩ => Subtype.ext_iff_val.2 ∘ Subtype.ext_iff_val.1

theorem inclusion_inj (h : s ⊆ t) {x y : s} : inclusion h x = inclusion h y ↔ x = y :=
  (inclusion_injective h).eq_iff

theorem eq_of_inclusion_surjective {s t : Set α} {h : s ⊆ t}
    (h_surj : Function.Surjective (inclusion h)) : s = t := by
  refine Set.Subset.antisymm h (fun x hx => ?_)
  obtain ⟨y, hy⟩ := h_surj ⟨x, hx⟩
  exact mem_of_eq_of_mem (congr_arg Subtype.val hy).symm y.prop

theorem inclusion_le_inclusion [LE α] {s t : Set α} (h : s ⊆ t) {x y : s} :
    inclusion h x ≤ inclusion h y ↔ x ≤ y := Iff.rfl

theorem inclusion_lt_inclusion [LT α] {s t : Set α} (h : s ⊆ t) {x y : s} :
    inclusion h x < inclusion h y ↔ x < y := Iff.rfl

end Set
