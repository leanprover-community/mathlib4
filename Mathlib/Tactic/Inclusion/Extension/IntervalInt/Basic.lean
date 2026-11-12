/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Tactic.Inclusion.Extension.IntervalInt.BinarySplit

/-!
# Basic inclusion extensions for interval_int

This file defines basic operations for the `interval_int` inclusion family.
-/

@[expose] public section

open Lean Qq

namespace Inclusion.IntervalInt

/-- Construct an inclusion variable for an integer expression using an integer interval. -/
@[inclusion_ext(_ : ℤ)]
meta def mkIntIVar : InclusionExt :=
  mkNDIVarExt `interval_int
    ⟨q(ℤ), q(Interval ℤ), q(instToSetIntervalOfPreorder (α := ℤ))⟩
    (Interval.mkBinarySplitCover q(binarySplit))

@[inclusion_op interval_int]
theorem ofNat_mem (n : ℕ) : (OfNat.ofNat n : ℤ) ∈ Interval.singleton (n : ℤ) :=
  ⟨le_rfl, le_rfl⟩

section Arithmetic

@[inclusion_op interval_int]
theorem add_mem {x y : ℤ} {I J : Interval ℤ} (hx : x ∈ I) (hy : y ∈ J) : x + y ∈ I.add J := by
  simpa using Interval.add_mem (AddMonoidHom.id ℤ) (by simp [hx]) (by simp [hy])

@[inclusion_op interval_int]
theorem neg_mem {x : ℤ} {I : Interval ℤ} (hx : x ∈ I) : -x ∈ I.neg := by
  simpa using Interval.neg_mem (AddMonoidHom.id ℤ) (by simp [hx])

@[inclusion_op interval_int]
theorem abs_mem {x : ℤ} {I : Interval ℤ} (hx : x ∈ I) : |x| ∈ I.abs := by
  simpa using Interval.abs_mem (OrderEmbedding.id ℤ) rfl (by simp) (by simp [hx])

@[inclusion_op interval_int]
theorem sub_mem {x y : ℤ} {I J : Interval ℤ} (hx : x ∈ I) (hy : y ∈ J) : x - y ∈ I.sub J := by
  simpa using Interval.sub_mem (AddMonoidHom.id ℤ) (by simp [hx]) (by simp [hy])

@[inclusion_op interval_int]
theorem mul_mem {x y : ℤ} {I J : Interval ℤ} (hx : x ∈ I) (hy : y ∈ J) : x * y ∈ I.mul J := by
  simpa using Interval.mul_mem (OrderEmbedding.id ℤ) rfl (by simp) (by simp [hx]) (by simp [hy])

@[inclusion_op interval_int]
theorem pow_mem (n : ℕ) {x : ℤ} {I : Interval ℤ} (hx : x ∈ I) : x ^ n ∈ I.pow n := by
  simpa using Interval.pow_mem (OrderEmbedding.id ℤ) rfl rfl (by simp) (by simp) n (by simp [hx])

end Arithmetic

section Props

@[inclusion_op interval_int]
theorem le_mem {x y : ℤ} {I J : Interval ℤ} (hx : x ∈ I) (hy : y ∈ J) :
    (x ≤ y) ∈ I.le J :=
  Interval.le_mem (OrderEmbedding.id ℤ) (by simp [hx]) (by simp [hy])

@[inclusion_op interval_int]
theorem lt_mem {x y : ℤ} {I J : Interval ℤ} (hx : x ∈ I) (hy : y ∈ J) :
    (x < y) ∈ I.lt J :=
  Interval.lt_mem (OrderEmbedding.id ℤ) (by simp [hx]) (by simp [hy])

@[inclusion_op interval_int]
theorem eq_mem {x y : ℤ} {I J : Interval ℤ} (hx : x ∈ I) (hy : y ∈ J) :
    (x = y) ∈ I.eq J :=
  Interval.eq_mem (OrderEmbedding.id ℤ) (by simp [hx]) (by simp [hy])

@[inclusion_op interval_int]
theorem mem_Ici {a x : ℤ} {I J : Interval ℤ} (ha : a ∈ I) (hx : x ∈ J) :
    (x ∈ Set.Ici a) ∈ I.le J := le_mem ha hx

@[inclusion_op interval_int]
theorem mem_Ioi {a x : ℤ} {I J : Interval ℤ} (ha : a ∈ I) (hx : x ∈ J) :
    (x ∈ Set.Ioi a) ∈ I.lt J := lt_mem ha hx

@[inclusion_op interval_int]
theorem mem_Iic {b x : ℤ} {I J : Interval ℤ} (hx : x ∈ I) (hb : b ∈ J) :
    (x ∈ Set.Iic b) ∈ I.le J := le_mem hx hb

@[inclusion_op interval_int]
theorem mem_Iio {b x : ℤ} {I J : Interval ℤ} (hx : x ∈ I) (hb : b ∈ J) :
    (x ∈ Set.Iio b) ∈ I.lt J := lt_mem hx hb

@[inclusion_op interval_int]
theorem mem_Icc {a b x : ℤ} {I J K : Interval ℤ} (ha : a ∈ I) (hx : x ∈ J) (hb : b ∈ K) :
    (x ∈ Set.Icc a b) ∈ (I.le J).and (J.le K) :=
  IntervalBool.and_mem (le_mem ha hx) (le_mem hx hb)

@[inclusion_op interval_int]
theorem mem_Ico {a b x : ℤ} {I J K : Interval ℤ} (ha : a ∈ I) (hx : x ∈ J) (hb : b ∈ K) :
    (x ∈ Set.Ico a b) ∈ (I.le J).and (J.lt K) :=
  IntervalBool.and_mem (le_mem ha hx) (lt_mem hx hb)

@[inclusion_op interval_int]
theorem mem_Ioc {a b x : ℤ} {I J K : Interval ℤ} (ha : a ∈ I) (hx : x ∈ J) (hb : b ∈ K) :
    (x ∈ Set.Ioc a b) ∈ (I.lt J).and (J.le K) :=
  IntervalBool.and_mem (lt_mem ha hx) (le_mem hx hb)

@[inclusion_op interval_int]
theorem mem_Ioo {a b x : ℤ} {I J K : Interval ℤ} (ha : a ∈ I) (hx : x ∈ J) (hb : b ∈ K) :
    (x ∈ Set.Ioo a b) ∈ (I.lt J).and (J.lt K) :=
  IntervalBool.and_mem (lt_mem ha hx) (lt_mem hx hb)

end Props

end Inclusion.IntervalInt
