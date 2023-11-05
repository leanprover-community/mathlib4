/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Order.Nonneg.Field
import Mathlib.Algebra.Order.Nonneg.Floor

#align_import data.rat.nnrat from "leanprover-community/mathlib"@"b3f4f007a962e3787aa0f3b5c7942a1317f7d88e"

/-!
# Nonnegative rationals

This file defines the nonnegative rationals as a subtype of `Rat` and provides its algebraic order
structure.

We also define an instance `CanLift ℚ ℚ≥0`. This instance can be used by the `lift` tactic to
replace `x : ℚ` and `hx : 0 ≤ x` in the proof context with `x : ℚ≥0` while replacing all occurrences
of `x` with `↑x`. This tactic also works for a function `f : α → ℚ` with a hypothesis
`hf : ∀ x, 0 ≤ f x`.

## Notation

`ℚ≥0` is notation for `NNRat` in locale `NNRat`.
-/


open Function

open BigOperators

/-- Nonnegative rational numbers. -/
def NNRat := { q : ℚ // 0 ≤ q } deriving
  CanonicallyOrderedCommSemiring, CanonicallyLinearOrderedSemifield, LinearOrderedCommGroupWithZero,
  Sub, Inhabited

-- Porting note: Added these instances to get `OrderedSub, DenselyOrdered, Archimedean`
-- instead of `deriving` them
instance : OrderedSub NNRat := Nonneg.orderedSub
instance : DenselyOrdered NNRat := Nonneg.densely_ordered
instance : Archimedean NNRat := Nonneg.archimedean

-- mathport name: nnrat
scoped[NNRat] notation "ℚ≥0" => NNRat

namespace NNRat

variable {α : Type*} {p q : ℚ≥0}

instance : Coe ℚ≥0 ℚ :=
  ⟨Subtype.val⟩

/-
-- Simp lemma to put back `n.val` into the normal form given by the coercion.
@[simp]
theorem val_eq_coe (q : ℚ≥0) : q.val = q :=
  rfl
-/
-- Porting note: `val_eq_coe` is no longer needed.
#noalign nnrat.val_eq_coe

instance canLift : CanLift ℚ ℚ≥0 (↑) fun q ↦ 0 ≤ q where
  prf q hq := ⟨⟨q, hq⟩, rfl⟩

@[ext]
theorem ext : (p : ℚ) = (q : ℚ) → p = q :=
  Subtype.ext

protected theorem coe_injective : Injective ((↑) : ℚ≥0 → ℚ) :=
  Subtype.coe_injective

@[simp, norm_cast]
theorem coe_inj : (p : ℚ) = q ↔ p = q :=
  Subtype.coe_inj

theorem ext_iff : p = q ↔ (p : ℚ) = q :=
  Subtype.ext_iff

theorem ne_iff {x y : ℚ≥0} : (x : ℚ) ≠ (y : ℚ) ↔ x ≠ y :=
  NNRat.coe_inj.not

@[norm_cast]
theorem coe_mk (q : ℚ) (hq) : ((⟨q, hq⟩ : ℚ≥0) : ℚ) = q :=
  rfl

/-- Reinterpret a rational number `q` as a non-negative rational number. Returns `0` if `q ≤ 0`. -/
def _root_.Rat.toNNRat (q : ℚ) : ℚ≥0 :=
  ⟨max q 0, le_max_right _ _⟩

theorem _root_.Rat.coe_toNNRat (q : ℚ) (hq : 0 ≤ q) : (q.toNNRat : ℚ) = q :=
  max_eq_left hq

theorem _root_.Rat.le_coe_toNNRat (q : ℚ) : q ≤ q.toNNRat :=
  le_max_left _ _

open Rat (toNNRat)

@[simp]
theorem coe_nonneg (q : ℚ≥0) : (0 : ℚ) ≤ q :=
  q.2

@[simp, norm_cast]
theorem coe_zero : ((0 : ℚ≥0) : ℚ) = 0 :=
  rfl

@[simp, norm_cast]
theorem coe_one : ((1 : ℚ≥0) : ℚ) = 1 :=
  rfl

@[simp, norm_cast]
theorem coe_add (p q : ℚ≥0) : ((p + q : ℚ≥0) : ℚ) = p + q :=
  rfl

@[simp, norm_cast]
theorem coe_mul (p q : ℚ≥0) : ((p * q : ℚ≥0) : ℚ) = p * q :=
  rfl

@[simp, norm_cast]
theorem coe_inv (q : ℚ≥0) : ((q⁻¹ : ℚ≥0) : ℚ) = (q : ℚ)⁻¹ :=
  rfl

@[simp, norm_cast]
theorem coe_div (p q : ℚ≥0) : ((p / q : ℚ≥0) : ℚ) = p / q :=
  rfl

-- Porting note: `bit0` `bit1` are deprecated, so remove these theorems.
#noalign nnrat.coe_bit0
#noalign nnrat.coe_bit1

@[simp, norm_cast]
theorem coe_sub (h : q ≤ p) : ((p - q : ℚ≥0) : ℚ) = p - q :=
  max_eq_left <| le_sub_comm.2 <| by rwa [sub_zero]

@[simp]
theorem coe_eq_zero : (q : ℚ) = 0 ↔ q = 0 := by norm_cast

theorem coe_ne_zero : (q : ℚ) ≠ 0 ↔ q ≠ 0 :=
  coe_eq_zero.not

@[norm_cast] -- Porting note: simp can prove this
theorem coe_le_coe : (p : ℚ) ≤ q ↔ p ≤ q :=
  Iff.rfl

@[norm_cast] -- Porting note: simp can prove this
theorem coe_lt_coe : (p : ℚ) < q ↔ p < q :=
  Iff.rfl

@[simp, norm_cast]
theorem coe_pos : (0 : ℚ) < q ↔ 0 < q :=
  Iff.rfl

theorem coe_mono : Monotone ((↑) : ℚ≥0 → ℚ) :=
  fun _ _ ↦ coe_le_coe.2

theorem toNNRat_mono : Monotone toNNRat :=
  fun _ _ h ↦ max_le_max h le_rfl

@[simp]
theorem toNNRat_coe (q : ℚ≥0) : toNNRat q = q :=
  ext <| max_eq_left q.2

@[simp]
theorem toNNRat_coe_nat (n : ℕ) : toNNRat n = n :=
  ext <| by simp only [Nat.cast_nonneg, Rat.coe_toNNRat]; rfl

/-- `toNNRat` and `(↑) : ℚ≥0 → ℚ` form a Galois insertion. -/
protected def gi : GaloisInsertion toNNRat (↑) :=
  GaloisInsertion.monotoneIntro coe_mono toNNRat_mono Rat.le_coe_toNNRat toNNRat_coe

/-- Coercion `ℚ≥0 → ℚ` as a `RingHom`. -/
def coeHom : ℚ≥0 →+* ℚ where
  toFun := (↑)
  map_one' := coe_one
  map_mul' := coe_mul
  map_zero' := coe_zero
  map_add' := coe_add

@[simp, norm_cast]
theorem coe_natCast (n : ℕ) : (↑(↑n : ℚ≥0) : ℚ) = n :=
  map_natCast coeHom n

@[simp]
theorem mk_coe_nat (n : ℕ) : @Eq ℚ≥0 (⟨(n : ℚ), n.cast_nonneg⟩ : ℚ≥0) n :=
  ext (coe_natCast n).symm

/-- The rational numbers are an algebra over the non-negative rationals. -/
instance : Algebra ℚ≥0 ℚ :=
  coeHom.toAlgebra

/-- A `MulAction` over `ℚ` restricts to a `MulAction` over `ℚ≥0`. -/
instance [MulAction ℚ α] : MulAction ℚ≥0 α :=
  MulAction.compHom α coeHom.toMonoidHom

/-- A `DistribMulAction` over `ℚ` restricts to a `DistribMulAction` over `ℚ≥0`. -/
instance [AddCommMonoid α] [DistribMulAction ℚ α] : DistribMulAction ℚ≥0 α :=
  DistribMulAction.compHom α coeHom.toMonoidHom

/-- A `Module` over `ℚ` restricts to a `Module` over `ℚ≥0`. -/
instance [AddCommMonoid α] [Module ℚ α] : Module ℚ≥0 α :=
  Module.compHom α coeHom

@[simp]
theorem coe_coeHom : ⇑coeHom = ((↑) : ℚ≥0 → ℚ) :=
  rfl

@[simp, norm_cast]
theorem coe_indicator (s : Set α) (f : α → ℚ≥0) (a : α) :
    ((s.indicator f a : ℚ≥0) : ℚ) = s.indicator (fun x ↦ ↑(f x)) a :=
  (coeHom : ℚ≥0 →+ ℚ).map_indicator _ _ _

@[simp, norm_cast]
theorem coe_pow (q : ℚ≥0) (n : ℕ) : (↑(q ^ n) : ℚ) = (q : ℚ) ^ n :=
  coeHom.map_pow _ _

@[norm_cast]
theorem coe_list_sum (l : List ℚ≥0) : (l.sum : ℚ) = (l.map (↑)).sum :=
  coeHom.map_list_sum _

@[norm_cast]
theorem coe_list_prod (l : List ℚ≥0) : (l.prod : ℚ) = (l.map (↑)).prod :=
  coeHom.map_list_prod _

@[norm_cast]
theorem coe_multiset_sum (s : Multiset ℚ≥0) : (s.sum : ℚ) = (s.map (↑)).sum :=
  coeHom.map_multiset_sum _

@[norm_cast]
theorem coe_multiset_prod (s : Multiset ℚ≥0) : (s.prod : ℚ) = (s.map (↑)).prod :=
  coeHom.map_multiset_prod _

@[norm_cast]
theorem coe_sum {s : Finset α} {f : α → ℚ≥0} : ↑(∑ a in s, f a) = ∑ a in s, (f a : ℚ) :=
  coeHom.map_sum _ _

theorem toNNRat_sum_of_nonneg {s : Finset α} {f : α → ℚ} (hf : ∀ a, a ∈ s → 0 ≤ f a) :
    (∑ a in s, f a).toNNRat = ∑ a in s, (f a).toNNRat := by
  rw [← coe_inj, coe_sum, Rat.coe_toNNRat _ (Finset.sum_nonneg hf)]
  exact Finset.sum_congr rfl fun x hxs ↦ by rw [Rat.coe_toNNRat _ (hf x hxs)]

@[norm_cast]
theorem coe_prod {s : Finset α} {f : α → ℚ≥0} : ↑(∏ a in s, f a) = ∏ a in s, (f a : ℚ) :=
  coeHom.map_prod _ _

theorem toNNRat_prod_of_nonneg {s : Finset α} {f : α → ℚ} (hf : ∀ a ∈ s, 0 ≤ f a) :
    (∏ a in s, f a).toNNRat = ∏ a in s, (f a).toNNRat := by
  rw [← coe_inj, coe_prod, Rat.coe_toNNRat _ (Finset.prod_nonneg hf)]
  exact Finset.prod_congr rfl fun x hxs ↦ by rw [Rat.coe_toNNRat _ (hf x hxs)]

@[norm_cast]
theorem nsmul_coe (q : ℚ≥0) (n : ℕ) : ↑(n • q) = n • (q : ℚ) :=
  coeHom.toAddMonoidHom.map_nsmul _ _

theorem bddAbove_coe {s : Set ℚ≥0} : BddAbove ((↑) '' s : Set ℚ) ↔ BddAbove s :=
  ⟨fun ⟨b, hb⟩ ↦
    ⟨toNNRat b, fun ⟨y, _⟩ hys ↦
      show y ≤ max b 0 from (hb <| Set.mem_image_of_mem _ hys).trans <| le_max_left _ _⟩,
    fun ⟨b, hb⟩ ↦ ⟨b, fun _ ⟨_, hx, Eq⟩ ↦ Eq ▸ hb hx⟩⟩

theorem bddBelow_coe (s : Set ℚ≥0) : BddBelow (((↑) : ℚ≥0 → ℚ) '' s) :=
  ⟨0, fun _ ⟨q, _, h⟩ ↦ h ▸ q.2⟩

@[simp, norm_cast]
theorem coe_max (x y : ℚ≥0) : ((max x y : ℚ≥0) : ℚ) = max (x : ℚ) (y : ℚ) :=
  coe_mono.map_max

@[simp, norm_cast]
theorem coe_min (x y : ℚ≥0) : ((min x y : ℚ≥0) : ℚ) = min (x : ℚ) (y : ℚ) :=
  coe_mono.map_min

theorem sub_def (p q : ℚ≥0) : p - q = toNNRat (p - q) :=
  rfl

@[simp]
theorem abs_coe (q : ℚ≥0) : |(q : ℚ)| = q :=
  abs_of_nonneg q.2

end NNRat

open NNRat

namespace Rat

variable {p q : ℚ}

@[simp]
theorem toNNRat_zero : toNNRat 0 = 0 := rfl

@[simp]
theorem toNNRat_one : toNNRat 1 = 1 := rfl

@[simp]
theorem toNNRat_pos : 0 < toNNRat q ↔ 0 < q := by simp [toNNRat, ← coe_lt_coe]

@[simp]
theorem toNNRat_eq_zero : toNNRat q = 0 ↔ q ≤ 0 := by
  simpa [-toNNRat_pos] using (@toNNRat_pos q).not

alias ⟨_, toNNRat_of_nonpos⟩ := toNNRat_eq_zero

@[simp]
theorem toNNRat_le_toNNRat_iff (hp : 0 ≤ p) : toNNRat q ≤ toNNRat p ↔ q ≤ p := by
  simp [← coe_le_coe, toNNRat, hp]

@[simp]
theorem toNNRat_lt_toNNRat_iff' : toNNRat q < toNNRat p ↔ q < p ∧ 0 < p := by
  simp [← coe_lt_coe, toNNRat, lt_irrefl]

theorem toNNRat_lt_toNNRat_iff (h : 0 < p) : toNNRat q < toNNRat p ↔ q < p :=
  toNNRat_lt_toNNRat_iff'.trans (and_iff_left h)

theorem toNNRat_lt_toNNRat_iff_of_nonneg (hq : 0 ≤ q) : toNNRat q < toNNRat p ↔ q < p :=
  toNNRat_lt_toNNRat_iff'.trans ⟨And.left, fun h ↦ ⟨h, hq.trans_lt h⟩⟩

@[simp]
theorem toNNRat_add (hq : 0 ≤ q) (hp : 0 ≤ p) : toNNRat (q + p) = toNNRat q + toNNRat p :=
  NNRat.ext <| by simp [toNNRat, hq, hp, add_nonneg]

theorem toNNRat_add_le : toNNRat (q + p) ≤ toNNRat q + toNNRat p :=
  coe_le_coe.1 <| max_le (add_le_add (le_max_left _ _) (le_max_left _ _)) <| coe_nonneg _

theorem toNNRat_le_iff_le_coe {p : ℚ≥0} : toNNRat q ≤ p ↔ q ≤ ↑p :=
  NNRat.gi.gc q p

theorem le_toNNRat_iff_coe_le {q : ℚ≥0} (hp : 0 ≤ p) : q ≤ toNNRat p ↔ ↑q ≤ p := by
  rw [← coe_le_coe, Rat.coe_toNNRat p hp]

theorem le_toNNRat_iff_coe_le' {q : ℚ≥0} (hq : 0 < q) : q ≤ toNNRat p ↔ ↑q ≤ p :=
  (le_or_lt 0 p).elim le_toNNRat_iff_coe_le fun hp ↦ by
    simp only [(hp.trans_le q.coe_nonneg).not_le, toNNRat_eq_zero.2 hp.le, hq.not_le]

theorem toNNRat_lt_iff_lt_coe {p : ℚ≥0} (hq : 0 ≤ q) : toNNRat q < p ↔ q < ↑p := by
  rw [← coe_lt_coe, Rat.coe_toNNRat q hq]

theorem lt_toNNRat_iff_coe_lt {q : ℚ≥0} : q < toNNRat p ↔ ↑q < p :=
  NNRat.gi.gc.lt_iff_lt

-- Porting note: `bit0` `bit1` are deprecated, so remove these theorems.
#noalign rat.to_nnrat_bit0
#noalign rat.to_nnrat_bit1

theorem toNNRat_mul (hp : 0 ≤ p) : toNNRat (p * q) = toNNRat p * toNNRat q := by
  cases' le_total 0 q with hq hq
  · ext <;> simp [toNNRat, hp, hq, max_eq_left, mul_nonneg]
  · have hpq := mul_nonpos_of_nonneg_of_nonpos hp hq
    rw [toNNRat_eq_zero.2 hq, toNNRat_eq_zero.2 hpq, mul_zero]

theorem toNNRat_inv (q : ℚ) : toNNRat q⁻¹ = (toNNRat q)⁻¹ := by
  obtain hq | hq := le_total q 0
  · rw [toNNRat_eq_zero.mpr hq, inv_zero, toNNRat_eq_zero.mpr (inv_nonpos.mpr hq)]
  · nth_rw 1 [← Rat.coe_toNNRat q hq]
    rw [← coe_inv, toNNRat_coe]

theorem toNNRat_div (hp : 0 ≤ p) : toNNRat (p / q) = toNNRat p / toNNRat q := by
  rw [div_eq_mul_inv, div_eq_mul_inv, ← toNNRat_inv, ← toNNRat_mul hp]

theorem toNNRat_div' (hq : 0 ≤ q) : toNNRat (p / q) = toNNRat p / toNNRat q := by
  rw [div_eq_inv_mul, div_eq_inv_mul, toNNRat_mul (inv_nonneg.2 hq), toNNRat_inv]

end Rat

/-- The absolute value on `ℚ` as a map to `ℚ≥0`. -/
--@[pp_nodot]  -- Porting note: Commented out.
def Rat.nnabs (x : ℚ) : ℚ≥0 :=
  ⟨abs x, abs_nonneg x⟩

@[norm_cast, simp]
theorem Rat.coe_nnabs (x : ℚ) : (Rat.nnabs x : ℚ) = abs x := rfl

/-! ### Numerator and denominator -/


namespace NNRat

variable {p q : ℚ≥0}

/-- The numerator of a nonnegative rational. -/
def num (q : ℚ≥0) : ℕ :=
  (q : ℚ).num.natAbs

/-- The denominator of a nonnegative rational. -/
def den (q : ℚ≥0) : ℕ :=
  (q : ℚ).den

@[simp]
theorem natAbs_num_coe : (q : ℚ).num.natAbs = q.num :=
  rfl

@[simp]
theorem den_coe : (q : ℚ).den = q.den :=
  rfl

theorem ext_num_den (hn : p.num = q.num) (hd : p.den = q.den) : p = q := by
  ext
  · apply (Int.natAbs_inj_of_nonneg_of_nonneg _ _).1 hn
    exact Rat.num_nonneg_iff_zero_le.2 p.2
    exact Rat.num_nonneg_iff_zero_le.2 q.2
  · exact hd

theorem ext_num_den_iff : p = q ↔ p.num = q.num ∧ p.den = q.den :=
  ⟨by rintro rfl; exact ⟨rfl, rfl⟩, fun h ↦ ext_num_den h.1 h.2⟩

@[simp]
theorem num_div_den (q : ℚ≥0) : (q.num : ℚ≥0) / q.den = q := by
  ext1
  rw [coe_div, coe_natCast, coe_natCast, num, ← Int.cast_ofNat,
    Int.natAbs_of_nonneg (Rat.num_nonneg_iff_zero_le.2 q.prop)]
  exact Rat.num_div_den q

/-- A recursor for nonnegative rationals in terms of numerators and denominators. -/
protected def rec {α : ℚ≥0 → Sort*} (h : ∀ m n : ℕ, α (m / n)) (q : ℚ≥0) : α q := by
  rw [← num_div_den q]
  apply h

end NNRat
