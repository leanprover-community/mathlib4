/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Algebra.Order.GroupWithZero.Range
import Mathlib.Algebra.Order.Hom.MonoidWithZero
import Mathlib.RingTheory.Valuation.ValuativeRel.Basic

/-!
# Equivalence of value group definitions

## Main Definitions
* `ValueGroup₀Iso`: when a commutative ring has a valuative relation,
  the relation's value group is mul-order-isomorphic to the value group of the valuation
  induced by the relation.
* `Valuation.Compatible.ValueGroup₀Iso`: When a commutative ring has a valuative relation,
  the relation's value group is mul-order-isomorphic to the value group of any valuation
  compatible to the relation.

-/

noncomputable section

open ValuativeRel

variable {R : Type*} [CommRing R]

variable {Γ₀ Γ₀' : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  [LinearOrderedCommGroupWithZero Γ₀']

lemma Valuation.IsEquiv.exists_mem_valueGroup' {v : Valuation R Γ₀} {v' : Valuation R Γ₀'}
    (h : v.IsEquiv v') {x : Γ₀ˣ} (hx : x ∈ MonoidWithZeroHom.valueGroup v) :
    ∃ y : Γ₀'ˣ, y ∈ MonoidWithZeroHom.valueGroup v' ∧
      ∀ (r s : R) (_hs : v s ≠ 0) (_hs' : v' s ≠ 0), v r / v s = x ↔ v' r / v' s = y := by
  simp_rw [MonoidWithZeroHom.mem_valueGroup_iff_of_comm] at hx ⊢
  obtain ⟨y, hy, z, hz⟩ := hx
  rw [mul_comm, ← eq_div_iff_mul_eq hy] at hz
  have hy' : v' y ≠ 0 := h.ne_zero.mp hy
  have hz' : v' z ≠ 0 := by
    rw [← h.ne_zero]
    intro H
    simp [H] at hz
  refine ⟨(Units.mk0 _ hz') / Units.mk0 _ hy', ⟨y, hy', z, ?_⟩, ?_⟩
  · simp [mul_div_cancel₀ (v' z) hy']
  · intro r s hs hs'
    rw [Units.val_div_eq_div_val, eq_div_iff_mul_eq (by simp [hy']), hz,
      eq_div_iff_mul_eq (by simp [hy])]
    simp only [Units.val_mk0]
    simp [div_mul_eq_mul_div₀, div_eq_iff hs, div_eq_iff hs', ← map_mul, h.val_eq]

lemma Valuation.IsEquiv.exists_mem_valueGroup {v : Valuation R Γ₀} {v' : Valuation R Γ₀'}
    (h : v.IsEquiv v') {x : Γ₀ˣ} (hx : x ∈ MonoidWithZeroHom.valueGroup v) :
    ∃ y : Γ₀'ˣ, y ∈ MonoidWithZeroHom.valueGroup v' ∧ ∀ r : R, v r = x ↔ v' r = y := by
  obtain ⟨y, hy, hy'⟩ := h.exists_mem_valueGroup' hx
  refine ⟨y, hy, ?_⟩
  intro r
  specialize hy' r 1 (by simp) (by simp)
  simpa using hy'

/-- When two valuations are equivalent, their value groups are isomorphic. -/
def Valuation.IsEquiv.orderMonoidIso {v : Valuation R Γ₀} {v' : Valuation R Γ₀'}
    (h : v.IsEquiv v') :
    MonoidWithZeroHom.ValueGroup₀ v ≃*o MonoidWithZeroHom.ValueGroup₀ v' := by
  refine ⟨MulEquiv.withZero ⟨⟨fun x ↦ ?_, fun x ↦ ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · exact ⟨(h.exists_mem_valueGroup' x.prop).choose,
      (h.exists_mem_valueGroup' x.prop).choose_spec.left⟩
  · exact ⟨(h.symm.exists_mem_valueGroup' x.prop).choose,
      (h.symm.exists_mem_valueGroup' x.prop).choose_spec.left⟩
  · intro x
    simp only [Subtype.ext_iff]
    generalize_proofs A B C D
    obtain ⟨y, hy, z, hz⟩ := (MonoidWithZeroHom.mem_valueGroup_iff_of_comm _).mp x.prop
    generalize hvy : v y = vy
    lift vy to Γ₀ˣ using IsUnit.mk0 _ (hvy ▸ hy)
    have hz0 : v z ≠ 0 := by
      intro H
      simp [hvy, ← Units.val_mul, H] at hz
    generalize hvz : v z = vz
    lift vz to Γ₀ˣ using IsUnit.mk0 _ (hvz ▸ hz0)
    rw [hvz, hvy, ← Units.val_mul, ← Units.ext_iff, eq_comm, ← div_eq_iff_eq_mul'] at hz
    refine Eq.trans ?_ hz
    rw [Units.ext_iff, Units.val_div_eq_div_val, ← hvy, ← hvz] at hz
    rwa [eq_comm, Units.ext_iff, Units.val_div_eq_div_val, ← hvy, ← hvz, ← D.choose_spec.right
      _ _ (h.ne_zero.mp hy) hy, ← C.choose_spec.right _ _ hy (h.ne_zero.mp hy)]
  · -- same argument, just switching v and v'
    intro x
    simp only [Subtype.ext_iff]
    generalize_proofs A B C D
    obtain ⟨y, hy, z, hz⟩ := (MonoidWithZeroHom.mem_valueGroup_iff_of_comm _).mp x.prop
    generalize hvy : v' y = vy
    lift vy to Γ₀'ˣ using IsUnit.mk0 _ (hvy ▸ hy)
    have hz0 : v' z ≠ 0 := by
      intro H
      simp [hvy, ← Units.val_mul, H] at hz
    generalize hvz : v' z = vz
    lift vz to Γ₀'ˣ using IsUnit.mk0 _ (hvz ▸ hz0)
    rw [hvz, hvy, ← Units.val_mul, ← Units.ext_iff, eq_comm, ← div_eq_iff_eq_mul'] at hz
    refine Eq.trans ?_ hz
    rw [Units.ext_iff, Units.val_div_eq_div_val, ← hvy, ← hvz] at hz
    rwa [eq_comm, Units.ext_iff, Units.val_div_eq_div_val, ← hvy, ← hvz, ← D.choose_spec.right
      _ _ (h.ne_zero.mpr hy) hy, ← C.choose_spec.right _ _ hy (h.ne_zero.mpr hy)]
  · intro _ _
    simp only [ne_eq, Subgroup.coe_mul, Units.val_mul, MulMemClass.mk_mul_mk, Subtype.ext_iff,
      Units.ext_iff]
    generalize_proofs A B C D E
    obtain ⟨a, ha, b, hb⟩ := (MonoidWithZeroHom.mem_valueGroup_iff_of_comm' _).mp C.choose_spec.left
    obtain ⟨m, hm, n, hn⟩ := (MonoidWithZeroHom.mem_valueGroup_iff_of_comm' _).mp D.choose_spec.left
    obtain ⟨r, hr, s, hs⟩ := (MonoidWithZeroHom.mem_valueGroup_iff_of_comm' _).mp E.choose_spec.left
    rw [eq_comm, hs, hn, div_mul_div_comm, ← map_mul, ← map_mul,
      ← C.choose_spec.right _ _ (by simp [h.ne_zero, hm, hr]) (by simp [hm, hr]), map_mul,
      map_mul, ← div_mul_div_comm]
    congr
    · rwa [D.choose_spec.right _ _ (by simp [h.ne_zero, hm]) (by simp [hm]), eq_comm]
    · rwa [E.choose_spec.right _ _ (by simp [h.ne_zero, hr]) (by simp [hr]), eq_comm]
  · intro x y
    induction x using WithZero.recZeroCoe
    · simp
    induction y using WithZero.recZeroCoe
    · simp
    · rename_i x y
      simp only [ne_eq, MulEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe,
        MulEquiv.withZero_apply_apply, WithZero.map'_coe, MonoidHom.coe_coe, MulEquiv.coe_mk,
        Equiv.coe_fn_mk, WithZero.coe_le_coe, Subtype.mk_le_mk]
      generalize_proofs A B C D
      obtain ⟨a, ha, b, hb⟩ :=
        (MonoidWithZeroHom.mem_valueGroup_iff_of_comm' _).mp C.choose_spec.left
      obtain ⟨m, hm, n, hn⟩ :=
        (MonoidWithZeroHom.mem_valueGroup_iff_of_comm' _).mp D.choose_spec.left
      rw [← Units.val_le_val, hb, hn]
      rw [eq_comm] at hb hn
      rw [← C.choose_spec.right _ _ (h.ne_zero.mpr ha) ha] at hb
      rw [← D.choose_spec.right _ _ (h.ne_zero.mpr hm) hm] at hn
      rw [div_le_div_iff₀, ← map_mul, ← map_mul, ← h, map_mul, map_mul, ← div_le_div_iff₀, hb, hn]
      · simp
      · simp [zero_lt_iff, h.ne_zero, ha]
      · simp [zero_lt_iff, h.ne_zero, hm]
      · simp [zero_lt_iff, ha]
      · simp [zero_lt_iff, hm]

variable [ValuativeRel R]

/-- When a commutative ring has a valuative relation, the relation's value group is
mul-order-isomorphic to the value group of the valuation induced by the relation. -/
@[simps!]
def ValueGroup₀Iso :
    MonoidWithZeroHom.ValueGroup₀ (valuation R) ≃*o ValueGroupWithZero R := by
  refine ⟨.ofBijective (OrderMonoidIso.withZeroUnits.toMonoidHom.comp
    MonoidWithZeroHom.valueGroup₀.MonoidWithZeroHom.toMonoidHom)
      ⟨OrderMonoidIso.withZeroUnits.injective.comp
       MonoidWithZeroHom.valueGroup₀.MonoidWithZeroHom_strictMono.injective, ?_⟩,
      (OrderMonoidIso.withZeroUnits.strictMono.comp
      MonoidWithZeroHom.valueGroup₀.MonoidWithZeroHom_strictMono).le_iff_le⟩
  intro x
  obtain ⟨γ, rfl⟩ := OrderMonoidIso.withZeroUnits.surjective x
  induction γ using WithZero.recZeroCoe with
  | zero =>
    use 0
    simp
  | coe x =>
    obtain ⟨r, s, h⟩ := valuation_surjective x.val
    refine ⟨WithZero.coe ⟨x, ?_⟩, by simp⟩
    rw [MonoidWithZeroHom.mem_valueGroup_iff_of_comm]
    refine ⟨s, by simp, r, ?_⟩
    rw [← h, mul_div_cancel₀]
    simp

/-- When a commutative ring has a valuative relation, the relation's value group is
mul-order-isomorphic to the value group of any valuation compatible to the relation. -/
nonrec def Valuation.Compatible.ValueGroup₀Iso (v : Valuation R Γ₀) [h : v.Compatible] :
    MonoidWithZeroHom.ValueGroup₀ v ≃*o ValueGroupWithZero R :=
  (isEquiv v (valuation R)).orderMonoidIso.trans ValueGroup₀Iso
