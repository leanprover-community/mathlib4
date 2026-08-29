/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.BinarySplit

/-!
# Basic inclusion extensions for interval_dyadic_real

This file defines basic operations for the `interval_dyadic_real` inclusion family.
-/

@[expose] public section

open Lean Qq

namespace Inclusion
namespace IntervalDyadicReal

/-- Construct an inclusion variable for a real expression using a dyadic interval. -/
@[inclusion_ext(_ : ℝ)]
meta def mkRealIVar : InclusionExt :=
  mkNDIVarExt `interval_dyadic_real
    ⟨q(ℝ), q(Interval Dyadic), q(instToSetIntervalDyadicReal)⟩ mkBinarySplitCover

@[grind =]
theorem mem_iff_mem_map {x : ℝ} {I : Interval Dyadic} : x ∈ I ↔ x ∈ I.map Dyadic.toReal :=
  Iff.rfl

section Constants

@[inclusion_op interval_dyadic_real]
theorem natCast_mem (n : ℕ) : (n : ℝ) ∈ Interval.singleton (n : Dyadic) := by
  simpa [mem_iff_mem_map] using Interval.mem_map_singleton (n : Dyadic) Dyadic.toReal

@[inclusion_op interval_dyadic_real]
theorem ofNat_mem (n : ℕ) : (OfNat.ofNat n : ℝ) ∈ Interval.singleton (n : Dyadic) := by
  rw [Semiring.toGrindSemiring_ofNat]
  exact natCast_mem n

@[inclusion_op interval_dyadic_real]
theorem intCast_mem (z : ℤ) : (z : ℝ) ∈ Interval.singleton (z : Dyadic) := by
  simpa [mem_iff_mem_map] using Interval.mem_map_singleton (z : Dyadic) Dyadic.toReal

end Constants

section Arithmetic

@[inclusion_op interval_dyadic_real]
theorem add_mem {x y : ℝ} {I J : Interval Dyadic} (hx : x ∈ I) (hy : y ∈ J) : x + y ∈ I.add J :=
  Interval.add_mem Dyadic.toRealAddMonoidHom hx hy

@[inclusion_op interval_dyadic_real]
theorem neg_mem {x : ℝ} {I : Interval Dyadic} (hx : x ∈ I) : -x ∈ I.neg :=
  Interval.neg_mem Dyadic.toRealAddMonoidHom hx

@[inclusion_op interval_dyadic_real]
theorem sub_mem {x y : ℝ} {I J : Interval Dyadic} (hx : x ∈ I) (hy : y ∈ J) : x - y ∈ I.sub J :=
  Interval.sub_mem Dyadic.toRealAddMonoidHom hx hy

end Arithmetic

section Props

@[inclusion_op interval_dyadic_real]
theorem le_mem {x y : ℝ} {I J : Interval Dyadic} (hx : x ∈ I) (hy : y ∈ J) :
    (x ≤ y) ∈ I.le J :=
  Interval.le_mem Dyadic.toRealOrderEmbedding hx hy

@[inclusion_op interval_dyadic_real]
theorem lt_mem {x y : ℝ} {I J : Interval Dyadic} (hx : x ∈ I) (hy : y ∈ J) :
    (x < y) ∈ I.lt J :=
  Interval.lt_mem Dyadic.toRealOrderEmbedding hx hy

@[inclusion_op interval_dyadic_real]
theorem eq_mem {x y : ℝ} {I J : Interval Dyadic} (hx : x ∈ I) (hy : y ∈ J) :
    (x = y) ∈ I.eq J :=
  Interval.eq_mem Dyadic.toRealOrderEmbedding hx hy

@[inclusion_op interval_dyadic_real]
theorem mem_Ici {a x : ℝ} {I J : Interval Dyadic} (ha : a ∈ I) (hx : x ∈ J) :
    (x ∈ Set.Ici a) ∈ I.le J :=
  Interval.mem_Ici Dyadic.toRealOrderEmbedding ha hx

@[inclusion_op interval_dyadic_real]
theorem mem_Ioi {a x : ℝ} {I J : Interval Dyadic} (ha : a ∈ I) (hx : x ∈ J) :
    (x ∈ Set.Ioi a) ∈ I.lt J :=
  Interval.mem_Ioi Dyadic.toRealOrderEmbedding ha hx

@[inclusion_op interval_dyadic_real]
theorem mem_Iic {b x : ℝ} {I J : Interval Dyadic} (hx : x ∈ I) (hb : b ∈ J) :
    (x ∈ Set.Iic b) ∈ I.le J :=
  Interval.mem_Iic Dyadic.toRealOrderEmbedding hx hb

@[inclusion_op interval_dyadic_real]
theorem mem_Iio {b x : ℝ} {I J : Interval Dyadic} (hx : x ∈ I) (hb : b ∈ J) :
    (x ∈ Set.Iio b) ∈ I.lt J :=
  Interval.mem_Iio Dyadic.toRealOrderEmbedding hx hb

@[inclusion_op interval_dyadic_real]
theorem mem_Icc {a b x : ℝ} {I J K : Interval Dyadic} (ha : a ∈ I) (hx : x ∈ J) (hb : b ∈ K) :
    (x ∈ Set.Icc a b) ∈ (I.le J).and (J.le K) :=
  Interval.mem_Icc Dyadic.toRealOrderEmbedding ha hx hb

@[inclusion_op interval_dyadic_real]
theorem mem_Ico {a b x : ℝ} {I J K : Interval Dyadic} (ha : a ∈ I) (hx : x ∈ J) (hb : b ∈ K) :
    (x ∈ Set.Ico a b) ∈ (I.le J).and (J.lt K) :=
  Interval.mem_Ico Dyadic.toRealOrderEmbedding ha hx hb

@[inclusion_op interval_dyadic_real]
theorem mem_Ioc {a b x : ℝ} {I J K : Interval Dyadic} (ha : a ∈ I) (hx : x ∈ J) (hb : b ∈ K) :
    (x ∈ Set.Ioc a b) ∈ (I.lt J).and (J.le K) :=
  Interval.mem_Ioc Dyadic.toRealOrderEmbedding ha hx hb

@[inclusion_op interval_dyadic_real]
theorem mem_Ioo {a b x : ℝ} {I J K : Interval Dyadic} (ha : a ∈ I) (hx : x ∈ J) (hb : b ∈ K) :
    (x ∈ Set.Ioo a b) ∈ (I.lt J).and (J.lt K) :=
  Interval.mem_Ioo Dyadic.toRealOrderEmbedding ha hx hb

end Props

end IntervalDyadicReal

end Inclusion
