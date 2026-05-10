/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Violeta Hernández Palacios
-/
module

public import Mathlib.Order.Cofinal
public import Mathlib.SetTheory.Cardinal.Basic

/-!
# Cofinality of an order

This file contains the definition of the cofinality `Order.cof α` of an order. This is the smallest
cardinality of a cofinal subset.
-/

public noncomputable section

open Function Cardinal Set Order

universe u v w

variable {α γ : Type u} {β : Type v}

/-! ### Cofinality of orders -/

namespace Order
section Preorder
variable [Preorder α]

variable (α) in
/-- The cofinality of a preorder is the smallest cardinality of a cofinal subset. -/
def cof : Cardinal :=
  ⨅ s : {s : Set α // IsCofinal s}, #s

theorem cof_le {s : Set α} (h : IsCofinal s) : cof α ≤ #s :=
  ciInf_le' (ι := {s : Set α // IsCofinal s}) _ ⟨s, h⟩

theorem le_lift_cof_iff {c : Cardinal.{max u v}} :
    c ≤ lift.{v} (cof α) ↔ ∀ s : Set α, IsCofinal s → c ≤ lift.{v} #s := by
  rw [cof, lift_iInf, le_ciInf_iff']
  simp

theorem le_cof_iff {c : Cardinal} : c ≤ cof α ↔ ∀ s : Set α, IsCofinal s → c ≤ #s := by
  simpa using @le_lift_cof_iff.{u, u} α _ c

@[deprecated (since := "2026-02-18")] alias le_cof := le_cof_iff

variable (α) in
theorem cof_eq : ∃ s : Set α, IsCofinal s ∧ #s = cof α := by
  obtain ⟨s, hs⟩ := ciInf_mem fun s : {s : Set α // IsCofinal s} ↦ #s
  exact ⟨s.1, s.2, hs⟩

variable (α) in
theorem cof_le_cardinalMk : cof α ≤ #α :=
  cof_le .univ |>.trans_eq mk_univ

theorem cof_eq_zero_iff : cof α = 0 ↔ IsEmpty α := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ by simp [cof]⟩
  obtain ⟨s, hs, hs'⟩ := cof_eq α
  simp_all [mk_eq_zero_iff, isCofinal_empty_iff]

@[simp]
theorem cof_eq_zero [h : IsEmpty α] : cof α = 0 :=
  cof_eq_zero_iff.2 h

theorem cof_ne_zero_iff : cof α ≠ 0 ↔ Nonempty α := by
  simpa using cof_eq_zero_iff.not

@[simp]
theorem cof_ne_zero [h : Nonempty α] : cof α ≠ 0 :=
  cof_ne_zero_iff.2 h

theorem cof_eq_one_iff : cof α = 1 ↔ ∃ x : α, IsTop x := by
  refine ⟨fun h ↦ ?_, fun ⟨t, ht⟩ ↦ ?_⟩
  · obtain ⟨s, hs, hs'⟩ := cof_eq α
    rw [h, mk_set_eq_one_iff] at hs'
    obtain ⟨t, rfl⟩ := hs'
    use t
    rwa [isCofinal_singleton_iff] at hs
  · apply le_antisymm
    · apply (cof_le (s := {t}) _).trans_eq (mk_singleton _)
      rwa [isCofinal_singleton_iff]
    · rw [Cardinal.one_le_iff_ne_zero, cof_ne_zero_iff]
      use t

@[simp]
theorem cof_eq_one [OrderTop α] : cof α = 1 :=
  cof_eq_one_iff.2 ⟨⊤, isTop_top⟩

theorem cof_ne_one_iff : cof α ≠ 1 ↔ NoTopOrder α := by
  rw [← not_iff_not, not_not, noTopOrder_iff, cof_eq_one_iff]
  simp

@[simp]
theorem cof_ne_one [h : NoTopOrder α] : cof α ≠ 1 :=
  cof_ne_one_iff.2 h

theorem cof_le_one_iff [Nonempty α] : cof α ≤ 1 ↔ ∃ x : α, IsTop x := by
  rw [le_iff_lt_or_eq, Cardinal.lt_one_iff, cof_eq_one_iff]
  simp

theorem one_lt_cof_iff [Nonempty α] : 1 < cof α ↔ NoTopOrder α := by
  rw [← not_iff_not, not_lt, noTopOrder_iff, cof_le_one_iff]
  simp

@[simp]
theorem one_lt_cof [Nonempty α] [h : NoTopOrder α] : 1 < cof α :=
  one_lt_cof_iff.2 h

end Preorder

section LinearOrder
variable [LinearOrder α] [LinearOrder β] [LinearOrder γ]

theorem lift_cof_congr_of_strictMono {f : α → β} (hf : StrictMono f) (hf' : IsCofinal (range f)) :
    lift.{v} (cof α) = lift.{u} (cof β) := by
  apply le_antisymm <;> rw [le_lift_cof_iff] <;> intro s hs
  · have H (x : s) : ∃ y : α, x ≤ f y := by simpa using hf' x
    choose g hg using H
    refine (lift_le.2 <| cof_le (s := range g) fun a ↦ ?_).trans mk_range_le_lift
    obtain ⟨_, ⟨b, rfl⟩, hb⟩ := hf' (f a)
    obtain ⟨c, hc, hc'⟩ := hs (f b)
    refine ⟨_, Set.mem_range_self ⟨c, hc⟩, ?_⟩
    rw [← hf.le_iff_le]
    exact hb.trans (hc'.trans (hg ⟨c, hc⟩))
  · exact (lift_le.2 <| cof_le (hs.image hf.monotone hf')).trans mk_image_le_lift

theorem cof_congr_of_strictMono {f : α → γ} (hf : StrictMono f) (hf' : IsCofinal (range f)) :
    cof α = cof γ := by
  simpa using lift_cof_congr_of_strictMono hf hf'

@[simp]
theorem cof_lt_aleph0_iff : Order.cof α < ℵ₀ ↔ Order.cof α ≤ 1 := by
  refine ⟨fun h ↦ ?_, (lt_of_le_of_lt · one_lt_aleph0)⟩
  obtain ⟨s, hs, hs'⟩ := Order.cof_eq α
  have hf : s.Finite := by
    rw [Set.Finite, ← mk_lt_aleph0_iff]
    exact hs'.trans_lt h
  obtain ⟨t, ht, ht'⟩ := hf.exists_subsingleton_isCofinal hs
  apply (cof_le ht').trans
  simpa

@[simp]
theorem aleph0_le_cof_iff : ℵ₀ ≤ Order.cof α ↔ 1 < Order.cof α := by
  simp [← not_lt]

@[simp]
theorem cof_eq_aleph0 [NoMaxOrder α] [Nonempty α] [Countable α] : cof α = ℵ₀ :=
  ((cof_le_cardinalMk _).trans mk_le_aleph0).antisymm (by simp)

theorem cof_nat : cof ℕ = ℵ₀ := by simp

end LinearOrder
end Order

section Congr
variable [Preorder α] [Preorder β] [Preorder γ]

theorem GaloisConnection.cof_le_lift {f : β → α} {g : α → β} (h : GaloisConnection f g) :
    Cardinal.lift.{u} (Order.cof β) ≤ Cardinal.lift.{v} (Order.cof α) := by
  rw [le_lift_cof_iff]
  exact fun s hs ↦ (lift_le.2 <| cof_le (h.map_isCofinal hs)).trans mk_image_le_lift

theorem GaloisConnection.cof_le {f : γ → α} {g : α → γ} (h : GaloisConnection f g) :
    Order.cof γ ≤ Order.cof α := by
  simpa using h.cof_le_lift

theorem OrderIso.lift_cof_congr (f : α ≃o β) :
    Cardinal.lift.{v} (Order.cof α) = Cardinal.lift.{u} (Order.cof β) :=
  f.to_galoisConnection.cof_le_lift.antisymm (f.symm.to_galoisConnection.cof_le_lift)

@[deprecated (since := "2026-03-20")] alias OrderIso.lift_cof_eq := OrderIso.lift_cof_congr

theorem OrderIso.cof_congr (f : α ≃o γ) : Order.cof α = Order.cof γ := by
  simpa using f.lift_cof_congr

@[deprecated (since := "2026-03-20")] alias OrderIso.cof_eq := OrderIso.cof_congr

@[deprecated (since := "2026-02-18")] alias RelIso.cof_eq_lift := OrderIso.lift_cof_congr
@[deprecated (since := "2026-02-18")] alias RelIso.cof_eq := OrderIso.cof_congr

end Congr

/-- If the union of `s` is cofinal and `s` is smaller than the cofinality, then `s` has a cofinal
member. -/
theorem isCofinal_of_isCofinal_sUnion {α : Type*} [LinearOrder α] {s : Set (Set α)}
    (h₁ : IsCofinal (⋃₀ s)) (h₂ : #s < Order.cof α) : ∃ x ∈ s, IsCofinal x := by
  contrapose! h₂
  simp_rw [not_isCofinal_iff] at h₂
  choose f hf using h₂
  refine (cof_le (s := range fun x ↦ f x.1 x.2) fun a ↦ ?_).trans mk_range_le
  obtain ⟨b, ⟨t, ht, hb⟩, hab⟩ := h₁ a
  simpa using ⟨t, ht, hab.trans (hf t ht b hb).le⟩

/-- If the union of the `ι`-indexed family `s` is cofinal and `ι` is smaller than the cofinality,
then `s` has a cofinal member. -/
theorem isCofinal_of_isCofinal_iUnion {α : Type*} {ι} [LinearOrder α] {s : ι → Set α}
    (h₁ : IsCofinal (⋃ i, s i)) (h₂ : #ι < Order.cof α) : ∃ i, IsCofinal (s i) := by
  rw [← sUnion_range] at h₁
  obtain ⟨_, ⟨i, rfl⟩, h⟩ := isCofinal_of_isCofinal_sUnion h₁ (mk_range_le.trans_lt h₂)
  exact ⟨i, h⟩
