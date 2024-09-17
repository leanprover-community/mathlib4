/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Algebra.Order.Archimedean.Submonoid
import Mathlib.Algebra.Order.Monoid.Submonoid
import Mathlib.Data.Int.SuccPred
import Mathlib.GroupTheory.ArchimedeanDensely
import Mathlib.Order.SuccPred.TypeTags
import Mathlib.RingTheory.Valuation.Integers

/-!
# Ring of integers under a given valuation in an multiplicatively archimedean codomain

-/

namespace Valuation.Integers

section Field

variable {F Γ₀ O : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀]
  [CommRing O] [Algebra O F] {v : Valuation F Γ₀}

lemma isPrincipalIdealRing_iff_not_denselyOrdered [MulArchimedean Γ₀] (hv : Integers v O) :
    IsPrincipalIdealRing O ↔ ¬ DenselyOrdered (Set.range v) := by
  refine ⟨fun _ ↦ not_denselyOrdered_of_isPrincipalIdealRing hv, fun H ↦ ?_⟩
  let l : LinearOrderedCommGroupWithZero (MonoidHom.mrange v) :=
  { zero := ⟨0, by simp⟩
    zero_mul := by
      intro a
      exact Subtype.ext (zero_mul a.val)
    mul_zero := by
      intro a
      exact Subtype.ext (mul_zero a.val)
    zero_le_one := Subtype.coe_le_coe.mp (zero_le_one)
    inv := fun x ↦ ⟨x⁻¹, by
      obtain ⟨y, hy⟩ := x.prop
      simp_rw [← hy, ← v.map_inv]
      exact MonoidHom.mem_mrange.mpr ⟨_, rfl⟩⟩
    exists_pair_ne := ⟨⟨v 0, by simp⟩, ⟨v 1, by simp [- _root_.map_one]⟩, by simp⟩
    inv_zero := Subtype.ext inv_zero
    mul_inv_cancel := by
      rintro ⟨a, ha⟩ h
      simp only [ne_eq, Subtype.ext_iff] at h
      simpa using mul_inv_cancel₀ h }
  have h0 : (0 : MonoidHom.mrange v) = ⟨0, by simp⟩ := rfl
  rcases subsingleton_or_nontrivial (MonoidHom.mrange v)ˣ with hs|_
  · have : ∀ x : (MonoidHom.mrange v)ˣ, x.val = 1 := by
      intro x
      rw [← Units.val_one, Units.eq_iff]
      exact Subsingleton.elim _ _
    replace this : ∀ x ≠ 0, v x = 1 := by
      intros x hx
      specialize this (Units.mk0 ⟨v x, by simp⟩ _)
      · simp [ne_eq, Subtype.ext_iff, h0, hx]
      simpa [Subtype.ext_iff] using this
    suffices ∀ I : Ideal O, I = ⊥ ∨ I = ⊤ by
      constructor
      intro I
      rcases this I with rfl|rfl
      -- TODO
      · exact ⟨0, by ext; simp [Ideal.mem_span_singleton', eq_comm]⟩
      · exact ⟨1, by simp only [Ideal.submodule_span_eq, Ideal.span_singleton_one]⟩
    intro I
    rcases eq_or_ne I ⊤ with rfl|hI
    · simp
    simp only [hI, or_false]
    ext x
    rcases eq_or_ne x 0 with rfl|hx
    · simp
    · specialize this (algebraMap O F x) (by simp [map_eq_zero_iff _ hv.hom_inj, hx])
      simp only [Ideal.mem_bot, hx, iff_false]
      contrapose! hI
      exact Ideal.eq_top_of_isUnit_mem _ hI (isUnit_of_one' hv this)
  replace H : ¬ DenselyOrdered (MonoidHom.mrange v) := H
  rw [← LinearOrderedCommGroupWithZero.discrete_iff_not_denselyOrdered (MonoidHom.mrange v)] at H
  obtain ⟨e⟩ := H
  constructor
  intro S
  rw [isPrincipal_iff_exists_isGreatest hv]
  rcases eq_or_ne S ⊥ with rfl|hS
  · simp only [Function.comp_apply, Submodule.bot_coe, Set.image_singleton, _root_.map_zero]
    exact ⟨0, by simp⟩
  let e' : (MonoidHom.mrange v)ˣ ≃o Multiplicative ℤ := ⟨
    (MulEquiv.unzero (WithZero.withZeroUnitsEquiv.trans e)).toEquiv, by
    intros
    simp only [MulEquiv.unzero, WithZero.withZeroUnitsEquiv,
      MulEquiv.trans_apply, MulEquiv.coe_mk, Equiv.coe_fn_mk, WithZero.recZeroCoe_coe,
      OrderMonoidIso.coe_mulEquiv, MulEquiv.symm_trans_apply, MulEquiv.symm_mk, Units.val_mk0,
      Equiv.coe_fn_symm_mk, map_eq_zero, WithZero.coe_ne_zero, ↓reduceDIte, WithZero.unzero_coe,
      MulEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe, ← Units.val_le_val]
    rw [← map_le_map_iff e, ← WithZero.coe_le_coe, WithZero.coe_unzero, WithZero.coe_unzero]⟩
  let _ : SuccOrder (MonoidHom.mrange v)ˣ := .ofOrderIso e'.symm
  have : IsSuccArchimedean (MonoidHom.mrange v)ˣ := .of_orderIso e'.symm
  set T : Set (MonoidHom.mrange v)ˣ := {y | ∃ (x : O) (h : x ≠ 0), x ∈ S ∧
      y = Units.mk0 ⟨v (algebraMap O F x), by simp⟩
      (by simp [map_ne_zero_iff, Subtype.ext_iff, h0, map_eq_zero_iff _ hv.hom_inj, h])} with hT
  have : BddAbove (α := (MonoidHom.mrange v)ˣ) T := by
    refine ⟨1, ?_⟩
    simp only [ne_eq, exists_and_left, mem_upperBounds, Set.mem_setOf_eq, forall_exists_index,
      and_imp, hT]
    rintro _ x _ hx' rfl
    simp [← Units.val_le_val, ← Subtype.coe_le_coe, hv.map_le_one]
  have hTn : T.Nonempty := by
    rw [Submodule.ne_bot_iff] at hS
    obtain ⟨x, hx, hx'⟩ := hS
    refine ⟨Units.mk0 ⟨v (algebraMap O F x), by simp⟩ ?_, ?_⟩
    · simp [map_ne_zero_iff, Subtype.ext_iff, h0, map_eq_zero_iff _ hv.hom_inj, hx']
    · simp only [hT, ne_eq, exists_and_left, Set.mem_setOf_eq, Units.mk0_inj, Subtype.mk.injEq,
      exists_prop', nonempty_prop]
      exact ⟨_, hx, hx', rfl⟩
  obtain ⟨_, ⟨x, hx, hxS, rfl⟩, hx'⟩ := this.exists_isGreatest_of_nonempty hTn
  refine ⟨_, ⟨x, hxS, rfl⟩, ?_⟩
  simp only [hT, ne_eq, exists_and_left, mem_upperBounds, Set.mem_setOf_eq, ← Units.val_le_val,
    Units.val_mk0, ← Subtype.coe_le_coe, forall_exists_index, and_imp, Function.comp_apply,
    Set.mem_image, SetLike.mem_coe, forall_apply_eq_imp_iff₂] at hx' ⊢
  intro y hy
  rcases eq_or_ne y 0 with rfl|hy'
  · simp
  specialize hx' _ y hy hy' rfl
  simpa [← Units.val_le_val, ← Subtype.coe_le_coe] using hx'

end Field

end Valuation.Integers
