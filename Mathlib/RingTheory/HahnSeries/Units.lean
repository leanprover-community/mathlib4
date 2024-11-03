/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.RingTheory.HahnSeries.Summable

/-!
# Invertible Hahn Series
A Hahn series with coefficients in a commutative ring is invertible if its order and leading
coefficient are invertible.  When the commutative ring is a domain, this condition is also
necessary.

## Main Definitions
  * `powers`: the summable family given by non-negative powers of a positive-order Hahn series.

## Main results
  * If `R` is a commutative domain, and `Γ` is a linearly ordered additive commutative group, then
  a Hahn series is a unit if and only if its leading term is a unit in `R`.

## References
- [J. van der Hoeven, *Operators on Generalized Power Series*][van_der_hoeven]
-/


open Finset Function

open Pointwise

noncomputable section

variable {Γ Γ' R V α β : Type*}

namespace HahnSeries

namespace SummableFamily

theorem isPWO_iUnion_support_powers [LinearOrderedCancelAddCommMonoid Γ] [Ring R] [IsDomain R]
    {x : HahnSeries Γ R} (hx : 0 < x.orderTop) : (⋃ n : ℕ, (x ^ n).support).IsPWO := by
  apply (x.isWF_support.isPWO.addSubmonoid_closure _).mono _
  · exact fun g hg => WithTop.coe_le_coe.1
      (le_trans (le_of_lt hx) (orderTop_le_of_coeff_ne_zero hg))
  refine Set.iUnion_subset fun n => ?_
  induction' n with n ih <;> intro g hn
  · simp only [pow_zero, support_one, Set.mem_singleton_iff] at hn
    rw [hn, SetLike.mem_coe]
    exact AddSubmonoid.zero_mem _
  · obtain ⟨i, hi, j, hj, rfl⟩ := support_mul_subset_add_support hn
    exact SetLike.mem_coe.2 (AddSubmonoid.add_mem _ (ih hi) (AddSubmonoid.subset_closure hj))

section powers

variable [LinearOrderedCancelAddCommMonoid Γ] [CommRing R] [IsDomain R]

/-- The powers of an element of positive valuation form a summable family. -/
@[simps]
def powers (x : HahnSeries Γ R) (hx : 0 < x.orderTop) : SummableFamily Γ R ℕ where
  toFun n := x ^ n
  isPWO_iUnion_support' := isPWO_iUnion_support_powers hx
  finite_co_support' g := by
    have hpwo := isPWO_iUnion_support_powers hx
    by_cases hg : g ∈ ⋃ n : ℕ, { g | (x ^ n).coeff g ≠ 0 }
    swap; · exact Set.finite_empty.subset fun n hn => hg (Set.mem_iUnion.2 ⟨n, hn⟩)
    apply hpwo.isWF.induction hg
    intro y ys hy
    refine
      ((((addAntidiagonal x.isPWO_support hpwo y).finite_toSet.biUnion fun ij hij =>
                    hy ij.snd ?_ ?_).image
                Nat.succ).union
            (Set.finite_singleton 0)).subset
        ?_
    · exact (mem_addAntidiagonal.1 (mem_coe.1 hij)).2.1
    · obtain ⟨hi, _, rfl⟩ := mem_addAntidiagonal.1 (mem_coe.1 hij)
      rw [← zero_add ij.snd, ← add_assoc, add_zero]
      exact
        add_lt_add_right (WithTop.coe_lt_coe.1 (hx.trans_le (orderTop_le_of_coeff_ne_zero hi)))
          _
    · rintro (_ | n) hn
      · exact Set.mem_union_right _ (Set.mem_singleton 0)
      · obtain ⟨i, hi, j, hj, rfl⟩ := support_mul_subset_add_support hn
        refine Set.mem_union_left _ ⟨n, Set.mem_iUnion.2 ⟨⟨j, i⟩, Set.mem_iUnion.2 ⟨?_, hi⟩⟩, rfl⟩
        simp only [Set.mem_iUnion, mem_addAntidiagonal, mem_coe, eq_self_iff_true, Ne, mem_support,
          Set.mem_setOf_eq]
        exact ⟨hj, ⟨n, hi⟩, add_comm j i⟩

variable {x : HahnSeries Γ R} (hx : 0 < x.orderTop)

@[simp]
theorem coe_powers : ⇑(powers x hx) = HPow.hPow x :=
  rfl

theorem embDomain_succ_smul_powers :
    (x • powers x hx).embDomain ⟨Nat.succ, Nat.succ_injective⟩ =
      powers x hx - ofFinsupp (Finsupp.single 0 1) := by
  apply SummableFamily.ext
  rintro (_ | n)
  · rw [embDomain_notin_range, sub_apply, coe_powers, pow_zero, coe_ofFinsupp,
      Finsupp.single_eq_same, sub_self]
    rw [Set.mem_range, not_exists]
    exact Nat.succ_ne_zero
  · refine Eq.trans (embDomain_image _ ⟨Nat.succ, Nat.succ_injective⟩) ?_
    rw [smul_apply, powers_toFun, coe_sub, coe_powers, Pi.sub_apply, coe_ofFinsupp, pow_succ',
      Finsupp.single_eq_of_ne (Nat.zero_ne_add_one n), sub_zero, of_symm_smul_of_eq_mul]

theorem one_sub_self_mul_hsum_powers : (1 - x) * (powers x hx).hsum = 1 := by
  rw [← hsum_smul, sub_smul 1 x (powers x hx), one_smul, hsum_sub, ←
    hsum_embDomain (x • powers x hx) ⟨Nat.succ, Nat.succ_injective⟩, embDomain_succ_smul_powers]
  simp

end powers

end SummableFamily

section Inversion

variable [LinearOrderedAddCommGroup Γ]

section IsDomain

variable [CommRing R] [IsDomain R]

theorem unit_aux (x : HahnSeries Γ R) {r : R} (hr : r * x.leadingCoeff = 1) :
    0 < (1 - single (-x.order) r * x).orderTop := by
  by_cases hx : x = 0; · simp_all [hx]
  have hrz : r ≠ 0 := by
    intro h
    rw [h, zero_mul] at hr
    exact (zero_ne_one' R) hr
  refine lt_of_le_of_ne (le_trans ?_ min_orderTop_le_orderTop_sub) fun h => ?_
  · refine le_min (by rw [orderTop_one]) ?_
    refine le_trans ?_ orderTop_add_orderTop_le_orderTop_mul
    by_cases h : x = 0; · simp [h]
    rw [← order_eq_orderTop_of_ne h, orderTop_single
      (fun _ => by simp_all only [zero_mul, zero_ne_one]), ← @WithTop.coe_add,
      WithTop.coe_nonneg, neg_add_cancel]
  · apply coeff_orderTop_ne h.symm
    simp only [C_apply, single_mul_single, zero_add, mul_one, sub_coeff', Pi.sub_apply, one_coeff,
      ↓reduceIte]
    have hrc := mul_coeff_order_add_order ((single (-x.order)) r) x
    rw [order_single hrz, leadingCoeff_of_single, neg_add_cancel, hr] at hrc
    rw [hrc, sub_self]

theorem isUnit_iff {x : HahnSeries Γ R} : IsUnit x ↔ IsUnit (x.leadingCoeff) := by
  constructor
  · rintro ⟨⟨u, i, ui, iu⟩, rfl⟩
    refine
      isUnit_of_mul_eq_one (u.leadingCoeff) (i.leadingCoeff)
        ((mul_coeff_order_add_order u i).symm.trans ?_)
    rw [ui, one_coeff, if_pos]
    rw [← order_mul (left_ne_zero_of_mul_eq_one ui) (right_ne_zero_of_mul_eq_one ui), ui, order_one]
  · rintro ⟨⟨u, i, ui, iu⟩, h⟩
    rw [Units.val_mk] at h
    rw [h] at iu
    have h := SummableFamily.one_sub_self_mul_hsum_powers (unit_aux x iu)
    rw [sub_sub_cancel] at h
    exact isUnit_of_mul_isUnit_right (isUnit_of_mul_eq_one _ _ h)

end IsDomain

open Classical in
instance instField [Field R] : Field (HahnSeries Γ R) where
  __ : IsDomain (HahnSeries Γ R) := inferInstance
  inv x :=
    if x0 : x = 0 then 0
    else
      (single (-x.order)) (x.leadingCoeff)⁻¹ *
        (SummableFamily.powers _ (unit_aux x (inv_mul_cancel₀ (leadingCoeff_ne_iff.mpr x0)))).hsum
  inv_zero := dif_pos rfl
  mul_inv_cancel x x0 := (congr rfl (dif_neg x0)).trans <| by
    have h :=
      SummableFamily.one_sub_self_mul_hsum_powers
        (unit_aux x (inv_mul_cancel₀ (leadingCoeff_ne_iff.mpr x0)))
    rw [sub_sub_cancel] at h
    rw [← mul_assoc, mul_comm x, h]
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

end Inversion

end HahnSeries
