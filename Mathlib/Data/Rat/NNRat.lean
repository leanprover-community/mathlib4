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
#align nnrat NNRat

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
#align nnrat.can_lift NNRat.canLift

@[ext]
theorem ext : (p : ℚ) = (q : ℚ) → p = q :=
  Subtype.ext
#align nnrat.ext NNRat.ext

protected theorem coe_injective : Injective ((↑) : ℚ≥0 → ℚ) :=
  Subtype.coe_injective
#align nnrat.coe_injective NNRat.coe_injective

@[simp, norm_cast]
theorem coe_inj : (p : ℚ) = q ↔ p = q :=
  Subtype.coe_inj
#align nnrat.coe_inj NNRat.coe_inj

theorem ext_iff : p = q ↔ (p : ℚ) = q :=
  Subtype.ext_iff
#align nnrat.ext_iff NNRat.ext_iff

theorem ne_iff {x y : ℚ≥0} : (x : ℚ) ≠ (y : ℚ) ↔ x ≠ y :=
  NNRat.coe_inj.not
#align nnrat.ne_iff NNRat.ne_iff

@[norm_cast]
theorem coe_mk (q : ℚ) (hq) : ((⟨q, hq⟩ : ℚ≥0) : ℚ) = q :=
  rfl
#align nnrat.coe_mk NNRat.coe_mk

/-- Reinterpret a rational number `q` as a non-negative rational number. Returns `0` if `q ≤ 0`. -/
def _root_.Rat.toNNRat (q : ℚ) : ℚ≥0 :=
  ⟨max q 0, le_max_right _ _⟩
#align rat.to_nnrat Rat.toNNRat

theorem _root_.Rat.coe_toNNRat (q : ℚ) (hq : 0 ≤ q) : (q.toNNRat : ℚ) = q :=
  max_eq_left hq
#align rat.coe_to_nnrat Rat.coe_toNNRat

theorem _root_.Rat.le_coe_toNNRat (q : ℚ) : q ≤ q.toNNRat :=
  le_max_left _ _
#align rat.le_coe_to_nnrat Rat.le_coe_toNNRat

open Rat (toNNRat)

@[simp]
theorem coe_nonneg (q : ℚ≥0) : (0 : ℚ) ≤ q :=
  q.2
#align nnrat.coe_nonneg NNRat.coe_nonneg

@[simp, norm_cast]
theorem coe_zero : ((0 : ℚ≥0) : ℚ) = 0 :=
  rfl
#align nnrat.coe_zero NNRat.coe_zero

@[simp, norm_cast]
theorem coe_one : ((1 : ℚ≥0) : ℚ) = 1 :=
  rfl
#align nnrat.coe_one NNRat.coe_one

@[simp, norm_cast]
theorem coe_add (p q : ℚ≥0) : ((p + q : ℚ≥0) : ℚ) = p + q :=
  rfl
#align nnrat.coe_add NNRat.coe_add

@[simp, norm_cast]
theorem coe_mul (p q : ℚ≥0) : ((p * q : ℚ≥0) : ℚ) = p * q :=
  rfl
#align nnrat.coe_mul NNRat.coe_mul

@[simp, norm_cast]
theorem coe_inv (q : ℚ≥0) : ((q⁻¹ : ℚ≥0) : ℚ) = (q : ℚ)⁻¹ :=
  rfl
#align nnrat.coe_inv NNRat.coe_inv

@[simp, norm_cast]
theorem coe_div (p q : ℚ≥0) : ((p / q : ℚ≥0) : ℚ) = p / q :=
  rfl
#align nnrat.coe_div NNRat.coe_div

-- Porting note: `bit0` `bit1` are deprecated, so remove these theorems.
#noalign nnrat.coe_bit0
#noalign nnrat.coe_bit1

@[simp, norm_cast]
theorem coe_sub (h : q ≤ p) : ((p - q : ℚ≥0) : ℚ) = p - q :=
  max_eq_left <| le_sub_comm.2 <| by rwa [sub_zero]
                                     -- 🎉 no goals
#align nnrat.coe_sub NNRat.coe_sub

@[simp]
theorem coe_eq_zero : (q : ℚ) = 0 ↔ q = 0 := by norm_cast
                                                -- 🎉 no goals
#align nnrat.coe_eq_zero NNRat.coe_eq_zero

theorem coe_ne_zero : (q : ℚ) ≠ 0 ↔ q ≠ 0 :=
  coe_eq_zero.not
#align nnrat.coe_ne_zero NNRat.coe_ne_zero

@[norm_cast] -- Porting note: simp can prove this
theorem coe_le_coe : (p : ℚ) ≤ q ↔ p ≤ q :=
  Iff.rfl
#align nnrat.coe_le_coe NNRat.coe_le_coe

@[norm_cast] -- Porting note: simp can prove this
theorem coe_lt_coe : (p : ℚ) < q ↔ p < q :=
  Iff.rfl
#align nnrat.coe_lt_coe NNRat.coe_lt_coe

@[simp, norm_cast]
theorem coe_pos : (0 : ℚ) < q ↔ 0 < q :=
  Iff.rfl
#align nnrat.coe_pos NNRat.coe_pos

theorem coe_mono : Monotone ((↑) : ℚ≥0 → ℚ) :=
  fun _ _ ↦ coe_le_coe.2
#align nnrat.coe_mono NNRat.coe_mono

theorem toNNRat_mono : Monotone toNNRat :=
  fun _ _ h ↦ max_le_max h le_rfl
#align nnrat.to_nnrat_mono NNRat.toNNRat_mono

@[simp]
theorem toNNRat_coe (q : ℚ≥0) : toNNRat q = q :=
  ext <| max_eq_left q.2
#align nnrat.to_nnrat_coe NNRat.toNNRat_coe

@[simp]
theorem toNNRat_coe_nat (n : ℕ) : toNNRat n = n :=
  ext <| by simp only [Nat.cast_nonneg, Rat.coe_toNNRat]; rfl
            -- ⊢ ↑n = ↑↑n
                                                          -- 🎉 no goals
#align nnrat.to_nnrat_coe_nat NNRat.toNNRat_coe_nat

/-- `toNNRat` and `(↑) : ℚ≥0 → ℚ` form a Galois insertion. -/
protected def gi : GaloisInsertion toNNRat (↑) :=
  GaloisInsertion.monotoneIntro coe_mono toNNRat_mono Rat.le_coe_toNNRat toNNRat_coe
#align nnrat.gi NNRat.gi

/-- Coercion `ℚ≥0 → ℚ` as a `RingHom`. -/
def coeHom : ℚ≥0 →+* ℚ where
  toFun := (↑)
  map_one' := coe_one
  map_mul' := coe_mul
  map_zero' := coe_zero
  map_add' := coe_add
#align nnrat.coe_hom NNRat.coeHom

@[simp, norm_cast]
theorem coe_natCast (n : ℕ) : (↑(↑n : ℚ≥0) : ℚ) = n :=
  map_natCast coeHom n
#align nnrat.coe_nat_cast NNRat.coe_natCast

@[simp]
theorem mk_coe_nat (n : ℕ) : @Eq ℚ≥0 (⟨(n : ℚ), n.cast_nonneg⟩ : ℚ≥0) n :=
  ext (coe_natCast n).symm
#align nnrat.mk_coe_nat NNRat.mk_coe_nat

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
#align nnrat.coe_coe_hom NNRat.coe_coeHom

@[simp, norm_cast]
theorem coe_indicator (s : Set α) (f : α → ℚ≥0) (a : α) :
    ((s.indicator f a : ℚ≥0) : ℚ) = s.indicator (fun x ↦ ↑(f x)) a :=
  (coeHom : ℚ≥0 →+ ℚ).map_indicator _ _ _
#align nnrat.coe_indicator NNRat.coe_indicator

@[simp, norm_cast]
theorem coe_pow (q : ℚ≥0) (n : ℕ) : (↑(q ^ n) : ℚ) = (q : ℚ) ^ n :=
  coeHom.map_pow _ _
#align nnrat.coe_pow NNRat.coe_pow

@[norm_cast]
theorem coe_list_sum (l : List ℚ≥0) : (l.sum : ℚ) = (l.map (↑)).sum :=
  coeHom.map_list_sum _
#align nnrat.coe_list_sum NNRat.coe_list_sum

@[norm_cast]
theorem coe_list_prod (l : List ℚ≥0) : (l.prod : ℚ) = (l.map (↑)).prod :=
  coeHom.map_list_prod _
#align nnrat.coe_list_prod NNRat.coe_list_prod

@[norm_cast]
theorem coe_multiset_sum (s : Multiset ℚ≥0) : (s.sum : ℚ) = (s.map (↑)).sum :=
  coeHom.map_multiset_sum _
#align nnrat.coe_multiset_sum NNRat.coe_multiset_sum

@[norm_cast]
theorem coe_multiset_prod (s : Multiset ℚ≥0) : (s.prod : ℚ) = (s.map (↑)).prod :=
  coeHom.map_multiset_prod _
#align nnrat.coe_multiset_prod NNRat.coe_multiset_prod

@[norm_cast]
theorem coe_sum {s : Finset α} {f : α → ℚ≥0} : ↑(∑ a in s, f a) = ∑ a in s, (f a : ℚ) :=
  coeHom.map_sum _ _
#align nnrat.coe_sum NNRat.coe_sum

theorem toNNRat_sum_of_nonneg {s : Finset α} {f : α → ℚ} (hf : ∀ a, a ∈ s → 0 ≤ f a) :
    (∑ a in s, f a).toNNRat = ∑ a in s, (f a).toNNRat := by
  rw [← coe_inj, coe_sum, Rat.coe_toNNRat _ (Finset.sum_nonneg hf)]
  -- ⊢ ∑ i in s, f i = ∑ a in s, ↑(toNNRat (f a))
  exact Finset.sum_congr rfl fun x hxs ↦ by rw [Rat.coe_toNNRat _ (hf x hxs)]
  -- 🎉 no goals
#align nnrat.to_nnrat_sum_of_nonneg NNRat.toNNRat_sum_of_nonneg

@[norm_cast]
theorem coe_prod {s : Finset α} {f : α → ℚ≥0} : ↑(∏ a in s, f a) = ∏ a in s, (f a : ℚ) :=
  coeHom.map_prod _ _
#align nnrat.coe_prod NNRat.coe_prod

theorem toNNRat_prod_of_nonneg {s : Finset α} {f : α → ℚ} (hf : ∀ a ∈ s, 0 ≤ f a) :
    (∏ a in s, f a).toNNRat = ∏ a in s, (f a).toNNRat := by
  rw [← coe_inj, coe_prod, Rat.coe_toNNRat _ (Finset.prod_nonneg hf)]
  -- ⊢ ∏ i in s, f i = ∏ a in s, ↑(toNNRat (f a))
  exact Finset.prod_congr rfl fun x hxs ↦ by rw [Rat.coe_toNNRat _ (hf x hxs)]
  -- 🎉 no goals
#align nnrat.to_nnrat_prod_of_nonneg NNRat.toNNRat_prod_of_nonneg

@[norm_cast]
theorem nsmul_coe (q : ℚ≥0) (n : ℕ) : ↑(n • q) = n • (q : ℚ) :=
  coeHom.toAddMonoidHom.map_nsmul _ _
#align nnrat.nsmul_coe NNRat.nsmul_coe

theorem bddAbove_coe {s : Set ℚ≥0} : BddAbove ((↑) '' s : Set ℚ) ↔ BddAbove s :=
  ⟨fun ⟨b, hb⟩ ↦
    ⟨toNNRat b, fun ⟨y, _⟩ hys ↦
      show y ≤ max b 0 from (hb <| Set.mem_image_of_mem _ hys).trans <| le_max_left _ _⟩,
    fun ⟨b, hb⟩ ↦ ⟨b, fun _ ⟨_, hx, Eq⟩ ↦ Eq ▸ hb hx⟩⟩
#align nnrat.bdd_above_coe NNRat.bddAbove_coe

theorem bddBelow_coe (s : Set ℚ≥0) : BddBelow (((↑) : ℚ≥0 → ℚ) '' s) :=
  ⟨0, fun _ ⟨q, _, h⟩ ↦ h ▸ q.2⟩
#align nnrat.bdd_below_coe NNRat.bddBelow_coe

@[simp, norm_cast]
theorem coe_max (x y : ℚ≥0) : ((max x y : ℚ≥0) : ℚ) = max (x : ℚ) (y : ℚ) :=
  coe_mono.map_max
#align nnrat.coe_max NNRat.coe_max

@[simp, norm_cast]
theorem coe_min (x y : ℚ≥0) : ((min x y : ℚ≥0) : ℚ) = min (x : ℚ) (y : ℚ) :=
  coe_mono.map_min
#align nnrat.coe_min NNRat.coe_min

theorem sub_def (p q : ℚ≥0) : p - q = toNNRat (p - q) :=
  rfl
#align nnrat.sub_def NNRat.sub_def

@[simp]
theorem abs_coe (q : ℚ≥0) : |(q : ℚ)| = q :=
  abs_of_nonneg q.2
#align nnrat.abs_coe NNRat.abs_coe

end NNRat

open NNRat

namespace Rat

variable {p q : ℚ}

@[simp]
theorem toNNRat_zero : toNNRat 0 = 0 := rfl
#align rat.to_nnrat_zero Rat.toNNRat_zero

@[simp]
theorem toNNRat_one : toNNRat 1 = 1 := rfl
#align rat.to_nnrat_one Rat.toNNRat_one

@[simp]
theorem toNNRat_pos : 0 < toNNRat q ↔ 0 < q := by simp [toNNRat, ← coe_lt_coe]
                                                  -- 🎉 no goals
#align rat.to_nnrat_pos Rat.toNNRat_pos

@[simp]
theorem toNNRat_eq_zero : toNNRat q = 0 ↔ q ≤ 0 := by
  simpa [-toNNRat_pos] using (@toNNRat_pos q).not
  -- 🎉 no goals
#align rat.to_nnrat_eq_zero Rat.toNNRat_eq_zero

alias ⟨_, toNNRat_of_nonpos⟩ := toNNRat_eq_zero
#align rat.to_nnrat_of_nonpos Rat.toNNRat_of_nonpos

@[simp]
theorem toNNRat_le_toNNRat_iff (hp : 0 ≤ p) : toNNRat q ≤ toNNRat p ↔ q ≤ p := by
  simp [← coe_le_coe, toNNRat, hp]
  -- 🎉 no goals
#align rat.to_nnrat_le_to_nnrat_iff Rat.toNNRat_le_toNNRat_iff

@[simp]
theorem toNNRat_lt_toNNRat_iff' : toNNRat q < toNNRat p ↔ q < p ∧ 0 < p := by
  simp [← coe_lt_coe, toNNRat, lt_irrefl]
  -- 🎉 no goals
#align rat.to_nnrat_lt_to_nnrat_iff' Rat.toNNRat_lt_toNNRat_iff'

theorem toNNRat_lt_toNNRat_iff (h : 0 < p) : toNNRat q < toNNRat p ↔ q < p :=
  toNNRat_lt_toNNRat_iff'.trans (and_iff_left h)
#align rat.to_nnrat_lt_to_nnrat_iff Rat.toNNRat_lt_toNNRat_iff

theorem toNNRat_lt_toNNRat_iff_of_nonneg (hq : 0 ≤ q) : toNNRat q < toNNRat p ↔ q < p :=
  toNNRat_lt_toNNRat_iff'.trans ⟨And.left, fun h ↦ ⟨h, hq.trans_lt h⟩⟩
#align rat.to_nnrat_lt_to_nnrat_iff_of_nonneg Rat.toNNRat_lt_toNNRat_iff_of_nonneg

@[simp]
theorem toNNRat_add (hq : 0 ≤ q) (hp : 0 ≤ p) : toNNRat (q + p) = toNNRat q + toNNRat p :=
  NNRat.ext <| by simp [toNNRat, hq, hp, add_nonneg]
                  -- 🎉 no goals
#align rat.to_nnrat_add Rat.toNNRat_add

theorem toNNRat_add_le : toNNRat (q + p) ≤ toNNRat q + toNNRat p :=
  coe_le_coe.1 <| max_le (add_le_add (le_max_left _ _) (le_max_left _ _)) <| coe_nonneg _
#align rat.to_nnrat_add_le Rat.toNNRat_add_le

theorem toNNRat_le_iff_le_coe {p : ℚ≥0} : toNNRat q ≤ p ↔ q ≤ ↑p :=
  NNRat.gi.gc q p
#align rat.to_nnrat_le_iff_le_coe Rat.toNNRat_le_iff_le_coe

theorem le_toNNRat_iff_coe_le {q : ℚ≥0} (hp : 0 ≤ p) : q ≤ toNNRat p ↔ ↑q ≤ p := by
  rw [← coe_le_coe, Rat.coe_toNNRat p hp]
  -- 🎉 no goals
#align rat.le_to_nnrat_iff_coe_le Rat.le_toNNRat_iff_coe_le

theorem le_toNNRat_iff_coe_le' {q : ℚ≥0} (hq : 0 < q) : q ≤ toNNRat p ↔ ↑q ≤ p :=
  (le_or_lt 0 p).elim le_toNNRat_iff_coe_le fun hp ↦ by
    simp only [(hp.trans_le q.coe_nonneg).not_le, toNNRat_eq_zero.2 hp.le, hq.not_le]
    -- 🎉 no goals
#align rat.le_to_nnrat_iff_coe_le' Rat.le_toNNRat_iff_coe_le'

theorem toNNRat_lt_iff_lt_coe {p : ℚ≥0} (hq : 0 ≤ q) : toNNRat q < p ↔ q < ↑p := by
  rw [← coe_lt_coe, Rat.coe_toNNRat q hq]
  -- 🎉 no goals
#align rat.to_nnrat_lt_iff_lt_coe Rat.toNNRat_lt_iff_lt_coe

theorem lt_toNNRat_iff_coe_lt {q : ℚ≥0} : q < toNNRat p ↔ ↑q < p :=
  NNRat.gi.gc.lt_iff_lt
#align rat.lt_to_nnrat_iff_coe_lt Rat.lt_toNNRat_iff_coe_lt

-- Porting note: `bit0` `bit1` are deprecated, so remove these theorems.
#noalign rat.to_nnrat_bit0
#noalign rat.to_nnrat_bit1

theorem toNNRat_mul (hp : 0 ≤ p) : toNNRat (p * q) = toNNRat p * toNNRat q := by
  cases' le_total 0 q with hq hq
  -- ⊢ toNNRat (p * q) = toNNRat p * toNNRat q
  · ext <;> simp [toNNRat, hp, hq, max_eq_left, mul_nonneg]
    -- ⊢ (↑(toNNRat (p * q))).num = (↑(toNNRat p * toNNRat q)).num
            -- 🎉 no goals
            -- 🎉 no goals
  · have hpq := mul_nonpos_of_nonneg_of_nonpos hp hq
    -- ⊢ toNNRat (p * q) = toNNRat p * toNNRat q
    rw [toNNRat_eq_zero.2 hq, toNNRat_eq_zero.2 hpq, mul_zero]
    -- 🎉 no goals
#align rat.to_nnrat_mul Rat.toNNRat_mul

theorem toNNRat_inv (q : ℚ) : toNNRat q⁻¹ = (toNNRat q)⁻¹ := by
  obtain hq | hq := le_total q 0
  -- ⊢ toNNRat q⁻¹ = (toNNRat q)⁻¹
  · rw [toNNRat_eq_zero.mpr hq, inv_zero, toNNRat_eq_zero.mpr (inv_nonpos.mpr hq)]
    -- 🎉 no goals
  · nth_rw 1 [← Rat.coe_toNNRat q hq]
    -- ⊢ toNNRat (↑(toNNRat q))⁻¹ = (toNNRat q)⁻¹
    rw [← coe_inv, toNNRat_coe]
    -- 🎉 no goals
#align rat.to_nnrat_inv Rat.toNNRat_inv

theorem toNNRat_div (hp : 0 ≤ p) : toNNRat (p / q) = toNNRat p / toNNRat q := by
  rw [div_eq_mul_inv, div_eq_mul_inv, ← toNNRat_inv, ← toNNRat_mul hp]
  -- 🎉 no goals
#align rat.to_nnrat_div Rat.toNNRat_div

theorem toNNRat_div' (hq : 0 ≤ q) : toNNRat (p / q) = toNNRat p / toNNRat q := by
  rw [div_eq_inv_mul, div_eq_inv_mul, toNNRat_mul (inv_nonneg.2 hq), toNNRat_inv]
  -- 🎉 no goals
#align rat.to_nnrat_div' Rat.toNNRat_div'

end Rat

/-- The absolute value on `ℚ` as a map to `ℚ≥0`. -/
--@[pp_nodot]  -- Porting note: Commented out.
def Rat.nnabs (x : ℚ) : ℚ≥0 :=
  ⟨abs x, abs_nonneg x⟩
#align rat.nnabs Rat.nnabs

@[norm_cast, simp]
theorem Rat.coe_nnabs (x : ℚ) : (Rat.nnabs x : ℚ) = abs x := rfl
#align rat.coe_nnabs Rat.coe_nnabs

/-! ### Numerator and denominator -/


namespace NNRat

variable {p q : ℚ≥0}

/-- The numerator of a nonnegative rational. -/
def num (q : ℚ≥0) : ℕ :=
  (q : ℚ).num.natAbs
#align nnrat.num NNRat.num

/-- The denominator of a nonnegative rational. -/
def den (q : ℚ≥0) : ℕ :=
  (q : ℚ).den
#align nnrat.denom NNRat.den

@[simp]
theorem natAbs_num_coe : (q : ℚ).num.natAbs = q.num :=
  rfl
#align nnrat.nat_abs_num_coe NNRat.natAbs_num_coe

@[simp]
theorem den_coe : (q : ℚ).den = q.den :=
  rfl
#align nnrat.denom_coe NNRat.den_coe

theorem ext_num_den (hn : p.num = q.num) (hd : p.den = q.den) : p = q := by
  ext
  -- ⊢ (↑p).num = (↑q).num
  · apply (Int.natAbs_inj_of_nonneg_of_nonneg _ _).1 hn
    -- ⊢ 0 ≤ (↑p).num
    exact Rat.num_nonneg_iff_zero_le.2 p.2
    -- ⊢ 0 ≤ (↑q).num
    exact Rat.num_nonneg_iff_zero_le.2 q.2
    -- 🎉 no goals
  · exact hd
    -- 🎉 no goals
#align nnrat.ext_num_denom NNRat.ext_num_den

theorem ext_num_den_iff : p = q ↔ p.num = q.num ∧ p.den = q.den :=
  ⟨by rintro rfl; exact ⟨rfl, rfl⟩, fun h ↦ ext_num_den h.1 h.2⟩
      -- ⊢ num p = num p ∧ den p = den p
                  -- 🎉 no goals
#align nnrat.ext_num_denom_iff NNRat.ext_num_den_iff

@[simp]
theorem num_div_den (q : ℚ≥0) : (q.num : ℚ≥0) / q.den = q := by
  ext1
  -- ⊢ ↑(↑(num q) / ↑(den q)) = ↑q
  rw [coe_div, coe_natCast, coe_natCast, num, ← Int.cast_ofNat,
    Int.natAbs_of_nonneg (Rat.num_nonneg_iff_zero_le.2 q.prop)]
  exact Rat.num_div_den q
  -- 🎉 no goals
#align nnrat.num_div_denom NNRat.num_div_den

/-- A recursor for nonnegative rationals in terms of numerators and denominators. -/
protected def rec {α : ℚ≥0 → Sort*} (h : ∀ m n : ℕ, α (m / n)) (q : ℚ≥0) : α q := by
  rw [← num_div_den q]
  -- ⊢ α (↑(num q) / ↑(den q))
  apply h
  -- 🎉 no goals
#align nnrat.rec NNRat.rec

end NNRat
