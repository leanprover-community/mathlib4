/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Algebra.Order.Monoid.Canonical.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.ZMod.Torsion

/-!
# Torsion group of p-adic integers

This file shows that the `p`-adic integers `ℤ_[p]` have `p - 1` roots-of-unity.

-/

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

open Polynomial

lemma norm_p_sub_one_choose {k : ℕ} (hk : k < p) :
    ‖((p - 1).choose k : ℤ_[p])‖ = 1 := by
  simp only [norm_def, coe_natCast, Padic.norm_natCast_eq_one_iff]
  exact Nat.Prime.coprime_choose_of_lt Fact.out (by grind) (by grind)

lemma restrictRootsOfUnity_toZMod_injective :
    Function.Injective (restrictRootsOfUnity (toZMod (p := p)) (p - 1)) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨x, hx⟩
  simp only [mem_rootsOfUnity] at hx
  rw [Subtype.ext_iff, Units.ext_iff]
  simp only [restrictRootsOfUnity_coe_apply, OneMemClass.coe_one, Units.val_one, Subgroup.mk_eq_one,
    ← (ZMod.val_injective _).eq_iff, val_toZMod_eq_zmodRepr, ZMod.val_one]
  intro h
  obtain ⟨c, hc⟩ := (norm_lt_one_iff_dvd _).mp (norm_sub_zmodRepr_lt_one x.val)
  suffices c = 0 by simpa [this, sub_eq_zero, h] using hc
  rw [h, sub_eq_iff_eq_add'] at hc
  simp only [Units.ext_iff, Units.val_pow_eq_pow_val, hc, Nat.cast_one, add_pow,
    Nat.Prime.one_le Fact.out, Nat.sub_add_cancel, one_pow, one_mul, Units.val_one] at hx
  obtain ⟨y, hy⟩ := Nat.exists_eq_add_of_le' (Nat.Prime.two_le (p := p) Fact.out)
  have hy' : Finset.range p = Finset.range (y + 2) := by grind
  have hyp : y + 1 = p - 1 := by grind
  simp only [hy', Finset.sum_range_succ, hyp, tsub_self, pow_zero, Nat.choose_self, Nat.cast_one,
    mul_one, add_eq_right] at hx
  by_contra! hc
  rw [← nnnorm_eq_zero, IsUltrametricDist.nnnorm_sum_eq_sup_of_pairwise_ne] at hx
  · have : 0 < p - 1 := by grind
    simp +contextual only [nnnorm_mul, nnnorm_pow, Finset.sup_eq_zero, Finset.mem_range,
      mul_eq_zero, pow_eq_zero_iff', nnnorm_eq_zero, Nat.cast_eq_zero, Nat.Prime.ne_zero Fact.out,
      false_or, ne_eq, Nat.choose_eq_zero_iff, Std.not_gt_of_lt, or_false, forall_and] at hx
    refine hc (hx.left 0 ?_)
    grind
  · intro a ha b hb hab H
    have : p - 1 < p := by grind
    rw [← NNReal.coe_inj] at H
    simp only [Finset.coe_range, Set.mem_Iio,
      nnnorm_mul, nnnorm_pow, NNReal.coe_mul, NNReal.coe_pow, coe_nnnorm] at ha hb H
    rw [norm_p_sub_one_choose (ha.trans this), norm_p_sub_one_choose (hb.trans this),
      mul_one, mul_one, ← norm_mul, ← zpow_natCast, ← zpow_natCast,
      ← div_eq_one_iff_eq (by simp [hc, Nat.Prime.ne_zero Fact.out]), div_eq_mul_inv, ← zpow_neg,
      ← zpow_add₀ (by simp [hc, Nat.Prime.ne_zero Fact.out])] at H
    simp only [ha.le, Nat.cast_sub, hb.le, neg_sub, sub_add_sub_cancel'] at H
    rw [zpow_eq_one_iff_right₀] at H
    · grind
    · exact norm_nonneg _
    · rw [norm_mul]
      refine (mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) ?_ (norm_le_one _)).ne
      rw [norm_natCast_lt_one_iff]

lemma restrictRootsOfUnity_toZMod_surjective :
    Function.Surjective (restrictRootsOfUnity (toZMod (p := p)) (p - 1)) := by
  rcases (Nat.Prime.two_le (Fact.out : p.Prime)).eq_or_lt with rfl | hp2
  · exact Function.surjective_to_subsingleton _
  let F : ℤ[X] := X ^ (p - 1) - 1
  have hF (n : ZMod p) : n ≠ 0 →
      ‖F.aeval (n.val : ℤ_[p])‖ < ‖F.derivative.aeval (n.val : ℤ_[p])‖ ^ 2 := by
    intro hn
    simp only [aeval_sub, map_pow, aeval_X, ← Nat.cast_pow, map_one, derivative_sub,
      derivative_X_pow, map_natCast, derivative_one, sub_zero, map_mul, norm_mul, F]
    rw [norm_natCast_eq_one_iff.mpr, norm_natCast_eq_one_iff.mpr, one_mul, one_pow,
        norm_lt_one_iff_dvd, ← zmodRepr_eq_zero_iff_dvd, ← val_toZMod_eq_zmodRepr]
    · simpa [sub_eq_zero] using ZMod.pow_card_sub_one_eq_one hn
    · rw [Nat.coprime_pow_right_iff, Nat.coprime_comm, ← ZMod.isUnit_iff_coprime]
      · simp [hn]
      · grind
    · simp [Nat.Prime.coprime_iff_not_dvd, Fact.out]
  replace hF : ∀ (x : ℤ_[p]), x.zmodRepr ≠ 0 →
    ‖F.aeval (x.zmodRepr : ℤ_[p])‖ < ‖F.derivative.aeval (x.zmodRepr : ℤ_[p])‖ ^ 2 := by
    intro x hx
    specialize hF (toZMod x) ?_
    · simp [← (ZMod.val_injective p).ne_iff, hx]
    simpa using hF
  have : ∀ x : ℤ_[p]ˣ, ∃ z : ℤ_[p]ˣ, z ^ (p - 1) = 1 ∧ z.val.zmodRepr = x.val.zmodRepr := by
    intro x
    have hx : ‖(x.val.zmodRepr : ℤ_[p]) ^ (p - 1) - 1‖ < 1 := by
      rw [norm_lt_one_iff_dvd, ← zmodRepr_eq_zero_iff_dvd, ← val_toZMod_eq_zmodRepr]
      simp only [← val_toZMod_eq_zmodRepr, ZMod.natCast_val, map_sub, map_pow,
        ZMod.ringHom_map_cast, map_one, ZMod.val_eq_zero, sub_eq_zero]
      refine ZMod.pow_card_sub_one_eq_one ?_
      rw [ne_eq, ← ZMod.val_eq_zero, val_toZMod_eq_zmodRepr]
      exact zmodRepr_units_ne_zero x
    obtain ⟨z, hz, hz', hz'', hz'''⟩ := hensels_lemma (p := p) (F := F) (a := x.val.zmodRepr)
      (hF _ (zmodRepr_units_ne_zero _))
    replace hz'' : ‖z‖ = 1 := by
      suffices ‖z‖ ^ (p - 2) = 1 by
        rwa [pow_eq_one_iff_of_nonneg (norm_nonneg z) (by grind)] at this
      simpa [F, derivative_X_pow,
        ((norm_natCast_zmodRepr_eq x.val).resolve_right (zmodRepr_units_ne_zero _))] using hz''
    refine ⟨mkUnits hz'', ?_, ?_⟩
    · simpa [Units.ext_iff, F, sub_eq_zero] using hz
    · simp only [val_mkUnits, Subtype.coe_eta]
      apply zmodRepr_unique _ _ (zmodRepr_lt_p _)
      simp [F, derivative_X_pow,
        (norm_natCast_zmodRepr_eq x.val).resolve_right (zmodRepr_units_ne_zero _)] at hz'
      rwa [← mem_nonunits, ← IsLocalRing.mem_maximalIdeal] at hz'
  intro x
  have hx : ‖((x.val.val.val : ℤ_[p]))‖ = 1 := by
    rw [norm_natCast_eq_one_iff]
    exact (ZMod.val_coe_unit_coprime _).symm
  obtain ⟨z, hz, hz'⟩ := this (mkUnits (u := (x.val.val.val : ℤ_[p])) hx)
  refine ⟨⟨z, hz⟩, ?_⟩
  simp [restrictRootsOfUnity, Subtype.ext_iff, Units.ext_iff]
  rw [← (ZMod.val_injective _).eq_iff, val_toZMod_eq_zmodRepr, hz']
  simp only [val_mkUnits, Subtype.coe_eta, zmodRepr_natCast_of_lt (ZMod.val_lt _)]

/-- The `p - 1` roots-of-unity of the `p`-adic integers are isomorphic to the units of `ZMod p`. -/
noncomputable
def rootsOfUnityMulEquiv :
    rootsOfUnity (p - 1) ℤ_[p] ≃* (ZMod p)ˣ :=
  MulEquiv.trans
    (.ofBijective _ ⟨restrictRootsOfUnity_toZMod_injective, restrictRootsOfUnity_toZMod_surjective⟩)
    ((MulEquiv.subgroupCongr (ZMod.rootsOfUnity_eq_top)).trans Subgroup.topEquiv)

instance : HasEnoughRootsOfUnity ℤ_[p] (p - 1) := by
  have : NeZero (p - 1) := by
    have : 2 ≤ p := Nat.Prime.two_le Fact.out
    exact ⟨by grind⟩
  exact (MulEquiv.ofBijective _ ⟨restrictRootsOfUnity_toZMod_injective,
    restrictRootsOfUnity_toZMod_surjective⟩).symm.hasEnoughRootsOfUnity

end PadicInt
