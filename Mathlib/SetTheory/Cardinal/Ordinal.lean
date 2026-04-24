/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.SetTheory.Ordinal.Principal

/-!
# Ordinal arithmetic with cardinals

This file collects results about the cardinality of different ordinal operations.
-/

public section

universe u v
open Cardinal Ordinal Set

/-! ### Cardinal operations with ordinal indices -/

namespace Cardinal

/-- Bounds the cardinal of an ordinal-indexed union of sets. -/
lemma mk_biUnion_le_of_le_lift {β : Type v} {o : Ordinal.{u}} {c : Cardinal.{v}}
    (ho : lift.{v} o.card ≤ lift.{u} c) (hc : ℵ₀ ≤ c) (A : Ordinal → Set β)
    (hA : ∀ j < o, #(A j) ≤ c) : #(⋃ j < o, A j) ≤ c := by
  simp_rw [← mem_Iio, biUnion_eq_iUnion, iUnion, iSup, ← ToType.mk.symm.surjective.range_comp]
  rw [← lift_le.{u}]
  apply ((mk_iUnion_le_lift _).trans _).trans_eq (mul_eq_self (aleph0_le_lift.2 hc))
  rw [mk_toType]
  refine mul_le_mul' ho (ciSup_le' ?_)
  intro i
  simpa using hA _ i.toOrd.prop

@[deprecated (since := "2026-01-26")]
alias mk_iUnion_Ordinal_lift_le_of_le := mk_biUnion_le_of_le_lift

lemma mk_biUnion_le_of_le {β : Type*} {o : Ordinal} {c : Cardinal}
    (ho : o.card ≤ c) (hc : ℵ₀ ≤ c) (A : Ordinal → Set β)
    (hA : ∀ j < o, #(A j) ≤ c) : #(⋃ j < o, A j) ≤ c := by
  apply mk_biUnion_le_of_le_lift _ hc A hA
  rwa [Cardinal.lift_le]

@[deprecated (since := "2026-01-26")]
alias mk_iUnion_Ordinal_le_of_le := mk_biUnion_le_of_le

end Cardinal

/-! ### Cardinality of ordinals -/

namespace Ordinal

theorem lift_card_iSup_le_sum_card {ι : Type u} [Small.{v} ι] (f : ι → Ordinal.{v}) :
    Cardinal.lift.{u} (⨆ i, f i).card ≤ Cardinal.sum fun i ↦ (f i).card := by
  simp_rw [← mk_toType]
  rw [← mk_sigma, ← Cardinal.lift_id'.{v} #(Σ _, _), ← Cardinal.lift_umax.{v, u}]
  apply lift_mk_le_lift_mk_of_surjective (f := .mk ∘ (⟨·.2.toOrd,
    (mem_Iio.mp (ToType.toOrd _).2).trans_le (Ordinal.le_iSup _ _)⟩))
  rw [EquivLike.comp_surjective]
  rintro ⟨x, hx⟩
  obtain ⟨i, hi⟩ := Ordinal.lt_iSup_iff.mp hx
  exact ⟨⟨i, .mk ⟨x, hi⟩⟩, by simp⟩

theorem card_iSup_le_sum_card {ι : Type u} (f : ι → Ordinal.{max u v}) :
    (⨆ i, f i).card ≤ Cardinal.sum (fun i ↦ (f i).card) := by
  have := lift_card_iSup_le_sum_card f
  rwa [Cardinal.lift_id'] at this

theorem card_iSup_Iio_le_sum_card {o : Ordinal.{u}} (f : Iio o → Ordinal.{max u v}) :
    (⨆ a : Iio o, f a).card ≤ Cardinal.sum fun i : o.ToType ↦ (f i.toOrd).card := by
  apply le_of_eq_of_le (congr_arg _ _).symm (card_iSup_le_sum_card _)
  simpa using ToType.mk.symm.iSup_comp (g := fun x ↦ f x)

theorem card_iSup_Iio_le_card_mul_iSup {o : Ordinal.{u}} (f : Iio o → Ordinal.{max u v}) :
    (⨆ a : Iio o, f a).card ≤ Cardinal.lift.{v} o.card * ⨆ a : Iio o, (f a).card := by
  apply (card_iSup_Iio_le_sum_card f).trans
  convert ← sum_le_lift_mk_mul_iSup _
  · exact mk_toType o
  · exact ToType.mk.symm.iSup_comp (g := fun x ↦ (f x).card)

theorem card_opow_le_of_omega0_le_left {a : Ordinal} (ha : ω ≤ a) (b : Ordinal) :
    (a ^ b).card ≤ max a.card b.card := by
  refine limitRecOn b ?_ ?_ ?_
  · simpa using one_lt_omega0.le.trans ha
  · intro b IH
    simp_rw [Order.succ_eq_add_one]
    rw [opow_add_one, card_mul, card_add_one, Cardinal.mul_eq_max_of_aleph0_le_right, max_comm]
    · grw [IH]
      rw [← max_assoc, max_self]
      grw [← le_self_add]
    · rw [ne_eq, card_eq_zero, opow_eq_zero]
      rintro ⟨rfl, -⟩
      cases omega0_pos.not_ge ha
    · rwa [aleph0_le_card]
  · intro b hb IH
    rw [(isNormal_opow (one_lt_omega0.trans_le ha)).apply_of_isSuccLimit hb]
    apply (card_iSup_Iio_le_card_mul_iSup _).trans
    rw [Cardinal.lift_id, Cardinal.mul_eq_max_of_aleph0_le_right, max_comm]
    · apply max_le _ (le_max_right _ _)
      apply ciSup_le'
      rintro ⟨c, (hcb : c < b)⟩
      grw [IH c hcb, hcb]
    · simpa using hb.ne_bot
    · exact le_ciSup_of_le Cardinal.bddAbove_of_small
        ⟨1, one_lt_omega0.trans_le <| omega0_le_of_isSuccLimit hb⟩ (by simpa)

theorem card_opow_le_of_omega0_le_right (a : Ordinal) {b : Ordinal} (hb : ω ≤ b) :
    (a ^ b).card ≤ max a.card b.card := by
  obtain ⟨n, rfl⟩ | ha := eq_natCast_or_omega0_le a
  · apply (card_le_card <| opow_le_opow_left b (natCast_lt_omega0 n).le).trans
    apply (card_opow_le_of_omega0_le_left le_rfl _).trans
    simp [hb]
  · exact card_opow_le_of_omega0_le_left ha b

theorem card_opow_le (a b : Ordinal) : (a ^ b).card ≤ max ℵ₀ (max a.card b.card) := by
  obtain ⟨n, rfl⟩ | ha := eq_natCast_or_omega0_le a
  · obtain ⟨m, rfl⟩ | hb := eq_natCast_or_omega0_le b
    · rw [opow_natCast, ← natCast_pow, card_nat]
      exact le_max_of_le_left natCast_le_aleph0
    · exact (card_opow_le_of_omega0_le_right _ hb).trans (le_max_right _ _)
  · exact (card_opow_le_of_omega0_le_left ha _).trans (le_max_right _ _)

theorem card_opow_eq_of_omega0_le_left {a b : Ordinal} (ha : ω ≤ a) (hb : 0 < b) :
    (a ^ b).card = max a.card b.card := by
  apply (card_opow_le_of_omega0_le_left ha b).antisymm (max_le _ _) <;> apply card_le_card
  · exact left_le_opow a hb
  · exact right_le_opow b (one_lt_omega0.trans_le ha)

theorem card_opow_eq_of_omega0_le_right {a b : Ordinal} (ha : 1 < a) (hb : ω ≤ b) :
    (a ^ b).card = max a.card b.card := by
  apply (card_opow_le_of_omega0_le_right a hb).antisymm (max_le _ _) <;> apply card_le_card
  · exact left_le_opow a (omega0_pos.trans_le hb)
  · exact right_le_opow b ha

theorem card_omega0_opow {a : Ordinal} (h : a ≠ 0) : card (ω ^ a) = max ℵ₀ a.card := by
  rw [card_opow_eq_of_omega0_le_left le_rfl h.bot_lt, card_omega0]

theorem card_opow_omega0 {a : Ordinal} (h : 1 < a) : card (a ^ ω) = max ℵ₀ a.card := by
  rw [card_opow_eq_of_omega0_le_right h le_rfl, card_omega0, max_comm]

theorem isPrincipal_opow_omega (o : Ordinal) : IsPrincipal (· ^ ·) (ω_ o) := by
  obtain rfl | ho := eq_zero_or_pos o
  · rw [omega_zero]
    exact isPrincipal_opow_omega0
  · intro a b ha hb
    rw [lt_omega_iff_card_lt] at ha hb ⊢
    apply (card_opow_le a b).trans_lt (max_lt _ (max_lt ha hb))
    rwa [← aleph_zero, aleph_lt_aleph]

@[deprecated (since := "2026-03-18")] alias principal_opow_omega := isPrincipal_opow_omega

theorem IsInitial.isPrincipal_opow {o : Ordinal} (h : IsInitial o) (ho : ω ≤ o) :
    IsPrincipal (· ^ ·) o := by
  obtain ⟨a, rfl⟩ := mem_range_omega_iff.2 ⟨ho, h⟩
  exact isPrincipal_opow_omega a

@[deprecated (since := "2026-03-18")] alias IsInitial.principal_opow := IsInitial.isPrincipal_opow

theorem isPrincipal_opow_ord {c : Cardinal} (hc : ℵ₀ ≤ c) : IsPrincipal (· ^ ·) c.ord := by
  apply (isInitial_ord c).isPrincipal_opow
  rwa [omega0_le_ord]

@[deprecated (since := "2026-03-18")] alias principal_opow_ord := isPrincipal_opow_ord

/-! ### Initial ordinals are principal -/

theorem isPrincipal_add_ord {c : Cardinal} (hc : ℵ₀ ≤ c) : IsPrincipal (· + ·) c.ord := by
  intro a b ha hb
  rw [lt_ord, card_add] at *
  exact add_lt_of_lt hc ha hb

@[deprecated (since := "2026-03-18")] alias principal_add_ord := isPrincipal_add_ord

theorem IsInitial.isPrincipal_add {o : Ordinal} (h : IsInitial o) (ho : ω ≤ o) :
    IsPrincipal (· + ·) o := by
  rw [← h.ord_card]
  apply isPrincipal_add_ord
  rwa [aleph0_le_card]

@[deprecated (since := "2026-03-18")] alias IsInitial.principal_add := IsInitial.isPrincipal_add

theorem isPrincipal_add_omega (o : Ordinal) : IsPrincipal (· + ·) (ω_ o) :=
  (isInitial_omega o).isPrincipal_add (omega0_le_omega o)

@[deprecated (since := "2026-03-18")] alias principal_add_omega := isPrincipal_add_omega

theorem isPrincipal_mul_ord {c : Cardinal} (hc : ℵ₀ ≤ c) : IsPrincipal (· * ·) c.ord := by
  intro a b ha hb
  rw [lt_ord, card_mul] at *
  exact mul_lt_of_lt hc ha hb

@[deprecated (since := "2026-03-18")] alias principal_mul_ord := isPrincipal_mul_ord

theorem IsInitial.isPrincipal_mul {o : Ordinal} (h : IsInitial o) (ho : ω ≤ o) :
    IsPrincipal (· * ·) o := by
  rw [← h.ord_card]
  apply isPrincipal_mul_ord
  rwa [aleph0_le_card]

@[deprecated (since := "2026-03-18")] alias IsInitial.principal_mul := IsInitial.isPrincipal_mul

theorem isPrincipal_mul_omega (o : Ordinal) : IsPrincipal (· * ·) (ω_ o) :=
  (isInitial_omega o).isPrincipal_mul (omega0_le_omega o)

@[deprecated (since := "2026-03-18")] alias principal_mul_omega := isPrincipal_mul_omega

end Ordinal
