/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta

! This file was ported from Lean 3 source module data.rat.nnrat
! leanprover-community/mathlib commit 28aa996fc6fb4317f0083c4e6daf79878d81be33
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Algebra.Basic
import Mathbin.Algebra.Order.Nonneg.Field

/-!
# Nonnegative rationals

This file defines the nonnegative rationals as a subtype of `rat` and provides its algebraic order
structure.

We also define an instance `can_lift ℚ ℚ≥0`. This instance can be used by the `lift` tactic to
replace `x : ℚ` and `hx : 0 ≤ x` in the proof context with `x : ℚ≥0` while replacing all occurences
of `x` with `↑x`. This tactic also works for a function `f : α → ℚ` with a hypothesis
`hf : ∀ x, 0 ≤ f x`.

## Notation

`ℚ≥0` is notation for `nnrat` in locale `nnrat`.
-/


open Function

open BigOperators

/-- Nonnegative rational numbers. -/
def Nnrat :=
  { q : ℚ // 0 ≤ q }deriving CanonicallyOrderedCommSemiring, CanonicallyLinearOrderedSemifield,
  LinearOrderedCommGroupWithZero, Sub, OrderedSub, DenselyOrdered, Archimedean, Inhabited
#align nnrat Nnrat

-- mathport name: nnrat
scoped[Nnrat] notation "ℚ≥0" => Nnrat

namespace Nnrat

variable {α : Type _} {p q : ℚ≥0}

instance : Coe ℚ≥0 ℚ :=
  ⟨Subtype.val⟩

-- Simp lemma to put back `n.val` into the normal form given by the coercion.
@[simp]
theorem val_eq_coe (q : ℚ≥0) : q.val = q :=
  rfl
#align nnrat.val_eq_coe Nnrat.val_eq_coe

instance canLift : CanLift ℚ ℚ≥0 coe fun q => 0 ≤ q where prf q hq := ⟨⟨q, hq⟩, rfl⟩
#align nnrat.can_lift Nnrat.canLift

@[ext]
theorem ext : (p : ℚ) = (q : ℚ) → p = q :=
  Subtype.ext
#align nnrat.ext Nnrat.ext

protected theorem coe_injective : Injective (coe : ℚ≥0 → ℚ) :=
  Subtype.coe_injective
#align nnrat.coe_injective Nnrat.coe_injective

@[simp, norm_cast]
theorem coe_inj : (p : ℚ) = q ↔ p = q :=
  Subtype.coe_inj
#align nnrat.coe_inj Nnrat.coe_inj

theorem ext_iff : p = q ↔ (p : ℚ) = q :=
  Subtype.ext_iff
#align nnrat.ext_iff Nnrat.ext_iff

theorem ne_iff {x y : ℚ≥0} : (x : ℚ) ≠ (y : ℚ) ↔ x ≠ y :=
  Nnrat.coe_inj.Not
#align nnrat.ne_iff Nnrat.ne_iff

@[norm_cast]
theorem coe_mk (q : ℚ) (hq) : ((⟨q, hq⟩ : ℚ≥0) : ℚ) = q :=
  rfl
#align nnrat.coe_mk Nnrat.coe_mk

/-- Reinterpret a rational number `q` as a non-negative rational number. Returns `0` if `q ≤ 0`. -/
def Rat.toNnrat (q : ℚ) : ℚ≥0 :=
  ⟨max q 0, le_max_right _ _⟩
#align rat.to_nnrat Rat.toNnrat

theorem Rat.coe_toNnrat (q : ℚ) (hq : 0 ≤ q) : (q.toNnrat : ℚ) = q :=
  max_eq_left hq
#align rat.coe_to_nnrat Rat.coe_toNnrat

theorem Rat.le_coe_toNnrat (q : ℚ) : q ≤ q.toNnrat :=
  le_max_left _ _
#align rat.le_coe_to_nnrat Rat.le_coe_toNnrat

open _Root_.Rat (toNnrat)

@[simp]
theorem coe_nonneg (q : ℚ≥0) : (0 : ℚ) ≤ q :=
  q.2
#align nnrat.coe_nonneg Nnrat.coe_nonneg

@[simp, norm_cast]
theorem coe_zero : ((0 : ℚ≥0) : ℚ) = 0 :=
  rfl
#align nnrat.coe_zero Nnrat.coe_zero

@[simp, norm_cast]
theorem coe_one : ((1 : ℚ≥0) : ℚ) = 1 :=
  rfl
#align nnrat.coe_one Nnrat.coe_one

@[simp, norm_cast]
theorem coe_add (p q : ℚ≥0) : ((p + q : ℚ≥0) : ℚ) = p + q :=
  rfl
#align nnrat.coe_add Nnrat.coe_add

@[simp, norm_cast]
theorem coe_mul (p q : ℚ≥0) : ((p * q : ℚ≥0) : ℚ) = p * q :=
  rfl
#align nnrat.coe_mul Nnrat.coe_mul

@[simp, norm_cast]
theorem coe_inv (q : ℚ≥0) : ((q⁻¹ : ℚ≥0) : ℚ) = q⁻¹ :=
  rfl
#align nnrat.coe_inv Nnrat.coe_inv

@[simp, norm_cast]
theorem coe_div (p q : ℚ≥0) : ((p / q : ℚ≥0) : ℚ) = p / q :=
  rfl
#align nnrat.coe_div Nnrat.coe_div

@[simp, norm_cast]
theorem coe_bit0 (q : ℚ≥0) : ((bit0 q : ℚ≥0) : ℚ) = bit0 q :=
  rfl
#align nnrat.coe_bit0 Nnrat.coe_bit0

@[simp, norm_cast]
theorem coe_bit1 (q : ℚ≥0) : ((bit1 q : ℚ≥0) : ℚ) = bit1 q :=
  rfl
#align nnrat.coe_bit1 Nnrat.coe_bit1

@[simp, norm_cast]
theorem coe_sub (h : q ≤ p) : ((p - q : ℚ≥0) : ℚ) = p - q :=
  max_eq_left <| le_sub_comm.2 <| by simp [show (q : ℚ) ≤ p from h]
#align nnrat.coe_sub Nnrat.coe_sub

@[simp]
theorem coe_eq_zero : (q : ℚ) = 0 ↔ q = 0 := by norm_cast
#align nnrat.coe_eq_zero Nnrat.coe_eq_zero

theorem coe_ne_zero : (q : ℚ) ≠ 0 ↔ q ≠ 0 :=
  coe_eq_zero.Not
#align nnrat.coe_ne_zero Nnrat.coe_ne_zero

@[simp, norm_cast]
theorem coe_le_coe : (p : ℚ) ≤ q ↔ p ≤ q :=
  Iff.rfl
#align nnrat.coe_le_coe Nnrat.coe_le_coe

@[simp, norm_cast]
theorem coe_lt_coe : (p : ℚ) < q ↔ p < q :=
  Iff.rfl
#align nnrat.coe_lt_coe Nnrat.coe_lt_coe

@[simp, norm_cast]
theorem coe_pos : (0 : ℚ) < q ↔ 0 < q :=
  Iff.rfl
#align nnrat.coe_pos Nnrat.coe_pos

theorem coe_mono : Monotone (coe : ℚ≥0 → ℚ) := fun _ _ => coe_le_coe.2
#align nnrat.coe_mono Nnrat.coe_mono

theorem toNnrat_mono : Monotone toNnrat := fun x y h => max_le_max h le_rfl
#align nnrat.to_nnrat_mono Nnrat.toNnrat_mono

@[simp]
theorem toNnrat_coe (q : ℚ≥0) : toNnrat q = q :=
  ext <| max_eq_left q.2
#align nnrat.to_nnrat_coe Nnrat.toNnrat_coe

@[simp]
theorem toNnrat_coe_nat (n : ℕ) : toNnrat n = n :=
  ext <| by simp [Rat.coe_toNnrat]
#align nnrat.to_nnrat_coe_nat Nnrat.toNnrat_coe_nat

/-- `to_nnrat` and `coe : ℚ≥0 → ℚ` form a Galois insertion. -/
protected def gi : GaloisInsertion toNnrat coe :=
  GaloisInsertion.monotoneIntro coe_mono toNnrat_mono Rat.le_coe_toNnrat toNnrat_coe
#align nnrat.gi Nnrat.gi

/-- Coercion `ℚ≥0 → ℚ` as a `ring_hom`. -/
def coeHom : ℚ≥0 →+* ℚ :=
  ⟨coe, coe_one, coe_mul, coe_zero, coe_add⟩
#align nnrat.coe_hom Nnrat.coeHom

@[simp, norm_cast]
theorem coe_nat_cast (n : ℕ) : (↑(↑n : ℚ≥0) : ℚ) = n :=
  map_natCast coeHom n
#align nnrat.coe_nat_cast Nnrat.coe_nat_cast

@[simp]
theorem mk_coe_nat (n : ℕ) : @Eq ℚ≥0 (⟨(n : ℚ), n.cast_nonneg⟩ : ℚ≥0) n :=
  ext (coe_nat_cast n).symm
#align nnrat.mk_coe_nat Nnrat.mk_coe_nat

/-- The rational numbers are an algebra over the non-negative rationals. -/
instance : Algebra ℚ≥0 ℚ :=
  coeHom.toAlgebra

/-- A `mul_action` over `ℚ` restricts to a `mul_action` over `ℚ≥0`. -/
instance [MulAction ℚ α] : MulAction ℚ≥0 α :=
  MulAction.compHom α coeHom.toMonoidHom

/-- A `distrib_mul_action` over `ℚ` restricts to a `distrib_mul_action` over `ℚ≥0`. -/
instance [AddCommMonoid α] [DistribMulAction ℚ α] : DistribMulAction ℚ≥0 α :=
  DistribMulAction.compHom α coeHom.toMonoidHom

/-- A `module` over `ℚ` restricts to a `module` over `ℚ≥0`. -/
instance [AddCommMonoid α] [Module ℚ α] : Module ℚ≥0 α :=
  Module.compHom α coeHom

@[simp]
theorem coe_coeHom : ⇑coeHom = coe :=
  rfl
#align nnrat.coe_coe_hom Nnrat.coe_coeHom

@[simp, norm_cast]
theorem coe_indicator (s : Set α) (f : α → ℚ≥0) (a : α) :
    ((s.indicator f a : ℚ≥0) : ℚ) = s.indicator (fun x => f x) a :=
  (coeHom : ℚ≥0 →+ ℚ).map_indicator _ _ _
#align nnrat.coe_indicator Nnrat.coe_indicator

@[simp, norm_cast]
theorem coe_pow (q : ℚ≥0) (n : ℕ) : (↑(q ^ n) : ℚ) = q ^ n :=
  coeHom.map_pow _ _
#align nnrat.coe_pow Nnrat.coe_pow

@[norm_cast]
theorem coe_list_sum (l : List ℚ≥0) : (l.Sum : ℚ) = (l.map coe).Sum :=
  coeHom.map_list_sum _
#align nnrat.coe_list_sum Nnrat.coe_list_sum

@[norm_cast]
theorem coe_list_prod (l : List ℚ≥0) : (l.Prod : ℚ) = (l.map coe).Prod :=
  coeHom.map_list_prod _
#align nnrat.coe_list_prod Nnrat.coe_list_prod

@[norm_cast]
theorem coe_multiset_sum (s : Multiset ℚ≥0) : (s.Sum : ℚ) = (s.map coe).Sum :=
  coeHom.map_multiset_sum _
#align nnrat.coe_multiset_sum Nnrat.coe_multiset_sum

@[norm_cast]
theorem coe_multiset_prod (s : Multiset ℚ≥0) : (s.Prod : ℚ) = (s.map coe).Prod :=
  coeHom.map_multiset_prod _
#align nnrat.coe_multiset_prod Nnrat.coe_multiset_prod

@[norm_cast]
theorem coe_sum {s : Finset α} {f : α → ℚ≥0} : ↑(∑ a in s, f a) = ∑ a in s, (f a : ℚ) :=
  coeHom.map_sum _ _
#align nnrat.coe_sum Nnrat.coe_sum

theorem toNnrat_sum_of_nonneg {s : Finset α} {f : α → ℚ} (hf : ∀ a, a ∈ s → 0 ≤ f a) :
    (∑ a in s, f a).toNnrat = ∑ a in s, (f a).toNnrat :=
  by
  rw [← coe_inj, coe_sum, Rat.coe_toNnrat _ (Finset.sum_nonneg hf)]
  exact Finset.sum_congr rfl fun x hxs => by rw [Rat.coe_toNnrat _ (hf x hxs)]
#align nnrat.to_nnrat_sum_of_nonneg Nnrat.toNnrat_sum_of_nonneg

@[norm_cast]
theorem coe_prod {s : Finset α} {f : α → ℚ≥0} : ↑(∏ a in s, f a) = ∏ a in s, (f a : ℚ) :=
  coeHom.map_prod _ _
#align nnrat.coe_prod Nnrat.coe_prod

theorem toNnrat_prod_of_nonneg {s : Finset α} {f : α → ℚ} (hf : ∀ a ∈ s, 0 ≤ f a) :
    (∏ a in s, f a).toNnrat = ∏ a in s, (f a).toNnrat :=
  by
  rw [← coe_inj, coe_prod, Rat.coe_toNnrat _ (Finset.prod_nonneg hf)]
  exact Finset.prod_congr rfl fun x hxs => by rw [Rat.coe_toNnrat _ (hf x hxs)]
#align nnrat.to_nnrat_prod_of_nonneg Nnrat.toNnrat_prod_of_nonneg

@[norm_cast]
theorem nsmul_coe (q : ℚ≥0) (n : ℕ) : ↑(n • q) = n • (q : ℚ) :=
  coeHom.toAddMonoidHom.map_nsmul _ _
#align nnrat.nsmul_coe Nnrat.nsmul_coe

theorem bddAbove_coe {s : Set ℚ≥0} : BddAbove (coe '' s : Set ℚ) ↔ BddAbove s :=
  ⟨fun ⟨b, hb⟩ =>
    ⟨toNnrat b, fun ⟨y, hy⟩ hys =>
      show y ≤ max b 0 from (hb <| Set.mem_image_of_mem _ hys).trans <| le_max_left _ _⟩,
    fun ⟨b, hb⟩ => ⟨b, fun y ⟨x, hx, Eq⟩ => Eq ▸ hb hx⟩⟩
#align nnrat.bdd_above_coe Nnrat.bddAbove_coe

theorem bddBelow_coe (s : Set ℚ≥0) : BddBelow ((coe : ℚ≥0 → ℚ) '' s) :=
  ⟨0, fun r ⟨q, _, h⟩ => h ▸ q.2⟩
#align nnrat.bdd_below_coe Nnrat.bddBelow_coe

@[simp, norm_cast]
theorem coe_max (x y : ℚ≥0) : ((max x y : ℚ≥0) : ℚ) = max (x : ℚ) (y : ℚ) :=
  coe_mono.map_max
#align nnrat.coe_max Nnrat.coe_max

@[simp, norm_cast]
theorem coe_min (x y : ℚ≥0) : ((min x y : ℚ≥0) : ℚ) = min (x : ℚ) (y : ℚ) :=
  coe_mono.map_min
#align nnrat.coe_min Nnrat.coe_min

theorem sub_def (p q : ℚ≥0) : p - q = toNnrat (p - q) :=
  rfl
#align nnrat.sub_def Nnrat.sub_def

@[simp]
theorem abs_coe (q : ℚ≥0) : |(q : ℚ)| = q :=
  abs_of_nonneg q.2
#align nnrat.abs_coe Nnrat.abs_coe

end Nnrat

open Nnrat

namespace Rat

variable {p q : ℚ}

@[simp]
theorem toNnrat_zero : toNnrat 0 = 0 := by simp [to_nnrat] <;> rfl
#align rat.to_nnrat_zero Rat.toNnrat_zero

@[simp]
theorem toNnrat_one : toNnrat 1 = 1 := by simp [to_nnrat, max_eq_left zero_le_one]
#align rat.to_nnrat_one Rat.toNnrat_one

@[simp]
theorem toNnrat_pos : 0 < toNnrat q ↔ 0 < q := by simp [to_nnrat, ← coe_lt_coe]
#align rat.to_nnrat_pos Rat.toNnrat_pos

@[simp]
theorem toNnrat_eq_zero : toNnrat q = 0 ↔ q ≤ 0 := by
  simpa [-to_nnrat_pos] using (@to_nnrat_pos q).Not
#align rat.to_nnrat_eq_zero Rat.toNnrat_eq_zero

alias to_nnrat_eq_zero ↔ _ to_nnrat_of_nonpos
#align rat.to_nnrat_of_nonpos Rat.toNnrat_of_nonpos

@[simp]
theorem toNnrat_le_toNnrat_iff (hp : 0 ≤ p) : toNnrat q ≤ toNnrat p ↔ q ≤ p := by
  simp [← coe_le_coe, to_nnrat, hp]
#align rat.to_nnrat_le_to_nnrat_iff Rat.toNnrat_le_toNnrat_iff

@[simp]
theorem toNnrat_lt_toNnrat_iff' : toNnrat q < toNnrat p ↔ q < p ∧ 0 < p :=
  by
  simp [← coe_lt_coe, to_nnrat, lt_irrefl]
  exact lt_trans'
#align rat.to_nnrat_lt_to_nnrat_iff' Rat.toNnrat_lt_toNnrat_iff'

theorem toNnrat_lt_toNnrat_iff (h : 0 < p) : toNnrat q < toNnrat p ↔ q < p :=
  toNnrat_lt_toNnrat_iff'.trans (and_iff_left h)
#align rat.to_nnrat_lt_to_nnrat_iff Rat.toNnrat_lt_toNnrat_iff

theorem toNnrat_lt_toNnrat_iff_of_nonneg (hq : 0 ≤ q) : toNnrat q < toNnrat p ↔ q < p :=
  toNnrat_lt_toNnrat_iff'.trans ⟨And.left, fun h => ⟨h, hq.trans_lt h⟩⟩
#align rat.to_nnrat_lt_to_nnrat_iff_of_nonneg Rat.toNnrat_lt_toNnrat_iff_of_nonneg

@[simp]
theorem toNnrat_add (hq : 0 ≤ q) (hp : 0 ≤ p) : toNnrat (q + p) = toNnrat q + toNnrat p :=
  Nnrat.ext <| by simp [to_nnrat, hq, hp, add_nonneg]
#align rat.to_nnrat_add Rat.toNnrat_add

theorem toNnrat_add_le : toNnrat (q + p) ≤ toNnrat q + toNnrat p :=
  coe_le_coe.1 <| max_le (add_le_add (le_max_left _ _) (le_max_left _ _)) <| coe_nonneg _
#align rat.to_nnrat_add_le Rat.toNnrat_add_le

theorem toNnrat_le_iff_le_coe {p : ℚ≥0} : toNnrat q ≤ p ↔ q ≤ ↑p :=
  Nnrat.gi.gc q p
#align rat.to_nnrat_le_iff_le_coe Rat.toNnrat_le_iff_le_coe

theorem le_toNnrat_iff_coe_le {q : ℚ≥0} (hp : 0 ≤ p) : q ≤ toNnrat p ↔ ↑q ≤ p := by
  rw [← coe_le_coe, Rat.coe_toNnrat p hp]
#align rat.le_to_nnrat_iff_coe_le Rat.le_toNnrat_iff_coe_le

theorem le_toNnrat_iff_coe_le' {q : ℚ≥0} (hq : 0 < q) : q ≤ toNnrat p ↔ ↑q ≤ p :=
  (le_or_lt 0 p).elim le_toNnrat_iff_coe_le fun hp => by
    simp only [(hp.trans_le q.coe_nonneg).not_le, to_nnrat_eq_zero.2 hp.le, hq.not_le]
#align rat.le_to_nnrat_iff_coe_le' Rat.le_toNnrat_iff_coe_le'

theorem toNnrat_lt_iff_lt_coe {p : ℚ≥0} (hq : 0 ≤ q) : toNnrat q < p ↔ q < ↑p := by
  rw [← coe_lt_coe, Rat.coe_toNnrat q hq]
#align rat.to_nnrat_lt_iff_lt_coe Rat.toNnrat_lt_iff_lt_coe

theorem lt_toNnrat_iff_coe_lt {q : ℚ≥0} : q < toNnrat p ↔ ↑q < p :=
  Nnrat.gi.gc.lt_iff_lt
#align rat.lt_to_nnrat_iff_coe_lt Rat.lt_toNnrat_iff_coe_lt

@[simp]
theorem toNnrat_bit0 (hq : 0 ≤ q) : toNnrat (bit0 q) = bit0 (toNnrat q) :=
  toNnrat_add hq hq
#align rat.to_nnrat_bit0 Rat.toNnrat_bit0

@[simp]
theorem toNnrat_bit1 (hq : 0 ≤ q) : toNnrat (bit1 q) = bit1 (toNnrat q) :=
  (toNnrat_add (by simp [hq]) zero_le_one).trans <| by simp [to_nnrat_one, bit1, hq]
#align rat.to_nnrat_bit1 Rat.toNnrat_bit1

theorem toNnrat_mul (hp : 0 ≤ p) : toNnrat (p * q) = toNnrat p * toNnrat q :=
  by
  cases' le_total 0 q with hq hq
  · ext <;> simp [to_nnrat, hp, hq, max_eq_left, mul_nonneg]
  · have hpq := mul_nonpos_of_nonneg_of_nonpos hp hq
    rw [to_nnrat_eq_zero.2 hq, to_nnrat_eq_zero.2 hpq, mul_zero]
#align rat.to_nnrat_mul Rat.toNnrat_mul

theorem toNnrat_inv (q : ℚ) : toNnrat q⁻¹ = (toNnrat q)⁻¹ :=
  by
  obtain hq | hq := le_total q 0
  · rw [to_nnrat_eq_zero.mpr hq, inv_zero, to_nnrat_eq_zero.mpr (inv_nonpos.mpr hq)]
  · nth_rw 1 [← Rat.coe_toNnrat q hq]
    rw [← coe_inv, to_nnrat_coe]
#align rat.to_nnrat_inv Rat.toNnrat_inv

theorem toNnrat_div (hp : 0 ≤ p) : toNnrat (p / q) = toNnrat p / toNnrat q := by
  rw [div_eq_mul_inv, div_eq_mul_inv, ← to_nnrat_inv, ← to_nnrat_mul hp]
#align rat.to_nnrat_div Rat.toNnrat_div

theorem toNnrat_div' (hq : 0 ≤ q) : toNnrat (p / q) = toNnrat p / toNnrat q := by
  rw [div_eq_inv_mul, div_eq_inv_mul, to_nnrat_mul (inv_nonneg.2 hq), to_nnrat_inv]
#align rat.to_nnrat_div' Rat.toNnrat_div'

end Rat

/-- The absolute value on `ℚ` as a map to `ℚ≥0`. -/
@[pp_nodot]
def Rat.nnabs (x : ℚ) : ℚ≥0 :=
  ⟨abs x, abs_nonneg x⟩
#align rat.nnabs Rat.nnabs

@[norm_cast, simp]
theorem Rat.coe_nnabs (x : ℚ) : (Rat.nnabs x : ℚ) = abs x := by simp [Rat.nnabs]
#align rat.coe_nnabs Rat.coe_nnabs

/-! ### Numerator and denominator -/


namespace Nnrat

variable {p q : ℚ≥0}

/-- The numerator of a nonnegative rational. -/
def num (q : ℚ≥0) : ℕ :=
  (q : ℚ).num.natAbs
#align nnrat.num Nnrat.num

/-- The denominator of a nonnegative rational. -/
def denom (q : ℚ≥0) : ℕ :=
  (q : ℚ).den
#align nnrat.denom Nnrat.denom

@[simp]
theorem natAbs_num_coe : (q : ℚ).num.natAbs = q.num :=
  rfl
#align nnrat.nat_abs_num_coe Nnrat.natAbs_num_coe

@[simp]
theorem den_coe : (q : ℚ).den = q.den :=
  rfl
#align nnrat.denom_coe Nnrat.den_coe

theorem ext_num_denom (hn : p.num = q.num) (hd : p.den = q.den) : p = q :=
  ext <|
    Rat.ext
      ((Int.natAbs_inj_of_nonneg_of_nonneg (Rat.num_nonneg_iff_zero_le.2 p.2) <|
            Rat.num_nonneg_iff_zero_le.2 q.2).1
        hn)
      hd
#align nnrat.ext_num_denom Nnrat.ext_num_denom

theorem ext_num_denom_iff : p = q ↔ p.num = q.num ∧ p.den = q.den :=
  ⟨by
    rintro rfl
    exact ⟨rfl, rfl⟩, fun h => ext_num_denom h.1 h.2⟩
#align nnrat.ext_num_denom_iff Nnrat.ext_num_denom_iff

@[simp]
theorem num_div_denom (q : ℚ≥0) : (q.num : ℚ≥0) / q.den = q :=
  by
  ext1
  rw [coe_div, coe_nat_cast, coe_nat_cast, Num, ← Int.cast_ofNat,
    Int.natAbs_of_nonneg (Rat.num_nonneg_iff_zero_le.2 q.prop)]
  exact Rat.num_div_den q
#align nnrat.num_div_denom Nnrat.num_div_denom

/-- A recursor for nonnegative rationals in terms of numerators and denominators. -/
protected def rec {α : ℚ≥0 → Sort _} (h : ∀ m n : ℕ, α (m / n)) (q : ℚ≥0) : α q :=
  (num_div_denom _).rec (h _ _)
#align nnrat.rec Nnrat.rec

end Nnrat

