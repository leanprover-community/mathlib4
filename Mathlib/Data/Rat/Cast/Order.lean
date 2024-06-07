/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Tactic.Positivity.Core

#align_import data.rat.cast from "leanprover-community/mathlib"@"acebd8d49928f6ed8920e502a6c90674e75bd441"

/-!
# Casts of rational numbers into linear ordered fields.
-/

variable {F ι α β : Type*}

namespace Rat

open Rat

@[simp]
theorem castHom_rat : castHom ℚ = RingHom.id ℚ :=
  RingHom.ext cast_id
#align rat.cast_hom_rat Rat.castHom_rat

section LinearOrderedField

variable {K : Type*} [LinearOrderedField K]

theorem cast_pos_of_pos {r : ℚ} (hr : 0 < r) : (0 : K) < r := by
  rw [Rat.cast_def]
  exact div_pos (Int.cast_pos.2 <| num_pos.2 hr) (Nat.cast_pos.2 r.pos)
#align rat.cast_pos_of_pos Rat.cast_pos_of_pos

@[mono]
theorem cast_strictMono : StrictMono ((↑) : ℚ → K) := fun m n => by
  simpa only [sub_pos, cast_sub] using @cast_pos_of_pos K _ (n - m)
#align rat.cast_strict_mono Rat.cast_strictMono

@[mono]
theorem cast_mono : Monotone ((↑) : ℚ → K) :=
  cast_strictMono.monotone
#align rat.cast_mono Rat.cast_mono

/-- Coercion from `ℚ` as an order embedding. -/
@[simps!]
def castOrderEmbedding : ℚ ↪o K :=
  OrderEmbedding.ofStrictMono (↑) cast_strictMono
#align rat.cast_order_embedding Rat.castOrderEmbedding
#align rat.cast_order_embedding_apply Rat.castOrderEmbedding_apply

@[simp, norm_cast]
theorem cast_le {m n : ℚ} : (m : K) ≤ n ↔ m ≤ n :=
  castOrderEmbedding.le_iff_le
#align rat.cast_le Rat.cast_le

@[simp, norm_cast]
theorem cast_lt {m n : ℚ} : (m : K) < n ↔ m < n :=
  cast_strictMono.lt_iff_lt
#align rat.cast_lt Rat.cast_lt

@[simp]
theorem cast_nonneg {n : ℚ} : 0 ≤ (n : K) ↔ 0 ≤ n := by
  norm_cast
#align rat.cast_nonneg Rat.cast_nonneg

@[simp]
theorem cast_nonpos {n : ℚ} : (n : K) ≤ 0 ↔ n ≤ 0 := by
  norm_cast
#align rat.cast_nonpos Rat.cast_nonpos

@[simp]
theorem cast_pos {n : ℚ} : (0 : K) < n ↔ 0 < n := by
  norm_cast
#align rat.cast_pos Rat.cast_pos

@[simp]
theorem cast_lt_zero {n : ℚ} : (n : K) < 0 ↔ n < 0 := by
  norm_cast
#align rat.cast_lt_zero Rat.cast_lt_zero

@[simp, norm_cast]
theorem cast_min {a b : ℚ} : (↑(min a b) : K) = min (a : K) (b : K) :=
  (@cast_mono K _).map_min
#align rat.cast_min Rat.cast_min

@[simp, norm_cast]
theorem cast_max {a b : ℚ} : (↑(max a b) : K) = max (a : K) (b : K) :=
  (@cast_mono K _).map_max
#align rat.cast_max Rat.cast_max


@[simp, norm_cast]
theorem cast_abs {q : ℚ} : ((|q| : ℚ) : K) = |(q : K)| := by simp [abs_eq_max_neg]
#align rat.cast_abs Rat.cast_abs

open Set

@[simp]
theorem preimage_cast_Icc (a b : ℚ) : (↑) ⁻¹' Icc (a : K) b = Icc a b :=
  castOrderEmbedding.preimage_Icc ..
#align rat.preimage_cast_Icc Rat.preimage_cast_Icc

@[simp]
theorem preimage_cast_Ico (a b : ℚ) : (↑) ⁻¹' Ico (a : K) b = Ico a b :=
  castOrderEmbedding.preimage_Ico ..
#align rat.preimage_cast_Ico Rat.preimage_cast_Ico

@[simp]
theorem preimage_cast_Ioc (a b : ℚ) : (↑) ⁻¹' Ioc (a : K) b = Ioc a b :=
  castOrderEmbedding.preimage_Ioc a b
#align rat.preimage_cast_Ioc Rat.preimage_cast_Ioc

@[simp]
theorem preimage_cast_Ioo (a b : ℚ) : (↑) ⁻¹' Ioo (a : K) b = Ioo a b :=
  castOrderEmbedding.preimage_Ioo a b
#align rat.preimage_cast_Ioo Rat.preimage_cast_Ioo

@[simp]
theorem preimage_cast_Ici (a : ℚ) : (↑) ⁻¹' Ici (a : K) = Ici a :=
  castOrderEmbedding.preimage_Ici a
#align rat.preimage_cast_Ici Rat.preimage_cast_Ici

@[simp]
theorem preimage_cast_Iic (a : ℚ) : (↑) ⁻¹' Iic (a : K) = Iic a :=
  castOrderEmbedding.preimage_Iic a
#align rat.preimage_cast_Iic Rat.preimage_cast_Iic

@[simp]
theorem preimage_cast_Ioi (a : ℚ) : (↑) ⁻¹' Ioi (a : K) = Ioi a :=
  castOrderEmbedding.preimage_Ioi a
#align rat.preimage_cast_Ioi Rat.preimage_cast_Ioi

@[simp]
theorem preimage_cast_Iio (a : ℚ) : (↑) ⁻¹' Iio (a : K) = Iio a :=
  castOrderEmbedding.preimage_Iio a
#align rat.preimage_cast_Iio Rat.preimage_cast_Iio

@[simp]
theorem preimage_cast_uIcc (a b : ℚ) : (↑) ⁻¹' uIcc (a : K) b = uIcc a b :=
  (castOrderEmbedding (K := K)).preimage_uIcc a b

@[simp]
theorem preimage_cast_uIoc (a b : ℚ) : (↑) ⁻¹' uIoc (a : K) b = uIoc a b :=
  (castOrderEmbedding (K := K)).preimage_uIoc a b

end LinearOrderedField
end Rat

namespace Mathlib.Meta.Positivity
open Lean Meta Qq Function

/-- Extension for Rat.cast. -/
@[positivity Rat.cast _]
def evalRatCast : PositivityExt where eval {u α} _zα _pα e := do
  let ~q(@Rat.cast _ (_) ($a : ℚ)) := e | throwError "not Rat.cast"
  match ← core q(inferInstance) q(inferInstance) a with
  | .positive pa =>
    let _oα ← synthInstanceQ q(LinearOrderedField $α)
    assumeInstancesCommute
    return .positive q((Rat.cast_pos (K := $α)).mpr $pa)
  | .nonnegative pa =>
    let _oα ← synthInstanceQ q(LinearOrderedField $α)
    assumeInstancesCommute
    return .nonnegative q((Rat.cast_nonneg (K := $α)).mpr $pa)
  | .nonzero pa =>
    let _oα ← synthInstanceQ q(DivisionRing $α)
    let _cα ← synthInstanceQ q(CharZero $α)
    assumeInstancesCommute
    return .nonzero q((Rat.cast_ne_zero (α := $α)).mpr $pa)
  | .none => pure .none

end Mathlib.Meta.Positivity
