/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Tactic.Positivity.Core
import Mathlib.Algebra.Order.Field.Basic

#align_import data.rat.cast from "leanprover-community/mathlib"@"acebd8d49928f6ed8920e502a6c90674e75bd441"

/-!
# Casts of rational numbers into linear ordered fields.
-/

variable {F ι α β : Type*}

namespace Rat
variable {p q : ℚ}

@[simp]
theorem castHom_rat : castHom ℚ = RingHom.id ℚ :=
  RingHom.ext cast_id
#align rat.cast_hom_rat Rat.castHom_rat

section LinearOrderedField

variable {K : Type*} [LinearOrderedField K]

theorem cast_pos_of_pos (hq : 0 < q) : (0 : K) < q := by
  rw [Rat.cast_def]
  exact div_pos (Int.cast_pos.2 <| num_pos.2 hq) (Nat.cast_pos.2 q.pos)
#align rat.cast_pos_of_pos Rat.cast_pos_of_pos

@[mono]
theorem cast_strictMono : StrictMono ((↑) : ℚ → K) := fun p q => by
  simpa only [sub_pos, cast_sub] using cast_pos_of_pos (K := K) (q := q - p)
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

@[simp, norm_cast] lemma cast_le : (p : K) ≤ q ↔ p ≤ q := castOrderEmbedding.le_iff_le
#align rat.cast_le Rat.cast_le

@[simp, norm_cast] lemma cast_lt : (p : K) < q ↔ p < q := cast_strictMono.lt_iff_lt
#align rat.cast_lt Rat.cast_lt

@[simp] lemma cast_nonneg : 0 ≤ (q : K) ↔ 0 ≤ q := by norm_cast
#align rat.cast_nonneg Rat.cast_nonneg

@[simp] lemma cast_nonpos : (q : K) ≤ 0 ↔ q ≤ 0 := by norm_cast
#align rat.cast_nonpos Rat.cast_nonpos

@[simp] lemma cast_pos : (0 : K) < q ↔ 0 < q := by norm_cast
#align rat.cast_pos Rat.cast_pos

@[simp] lemma cast_lt_zero : (q : K) < 0 ↔ q < 0 := by norm_cast
#align rat.cast_lt_zero Rat.cast_lt_zero

@[simp, norm_cast]
lemma cast_min (p q : ℚ) : (↑(min p q) : K) = min (p : K) (q : K) := (@cast_mono K _).map_min
#align rat.cast_min Rat.cast_min

@[simp, norm_cast]
lemma cast_max (p q : ℚ) : (↑(max p q) : K) = max (p : K) (q : K) := (@cast_mono K _).map_max
#align rat.cast_max Rat.cast_max

@[simp, norm_cast] lemma cast_abs (q : ℚ) : ((|q| : ℚ) : K) = |(q : K)| := by simp [abs_eq_max_neg]
#align rat.cast_abs Rat.cast_abs

open Set

@[simp]
theorem preimage_cast_Icc (p q : ℚ) : (↑) ⁻¹' Icc (p : K) q = Icc p q :=
  castOrderEmbedding.preimage_Icc ..
#align rat.preimage_cast_Icc Rat.preimage_cast_Icc

@[simp]
theorem preimage_cast_Ico (p q : ℚ) : (↑) ⁻¹' Ico (p : K) q = Ico p q :=
  castOrderEmbedding.preimage_Ico ..
#align rat.preimage_cast_Ico Rat.preimage_cast_Ico

@[simp]
theorem preimage_cast_Ioc (p q : ℚ) : (↑) ⁻¹' Ioc (p : K) q = Ioc p q :=
  castOrderEmbedding.preimage_Ioc p q
#align rat.preimage_cast_Ioc Rat.preimage_cast_Ioc

@[simp]
theorem preimage_cast_Ioo (p q : ℚ) : (↑) ⁻¹' Ioo (p : K) q = Ioo p q :=
  castOrderEmbedding.preimage_Ioo p q
#align rat.preimage_cast_Ioo Rat.preimage_cast_Ioo

@[simp]
theorem preimage_cast_Ici (q : ℚ) : (↑) ⁻¹' Ici (q : K) = Ici q :=
  castOrderEmbedding.preimage_Ici q
#align rat.preimage_cast_Ici Rat.preimage_cast_Ici

@[simp]
theorem preimage_cast_Iic (q : ℚ) : (↑) ⁻¹' Iic (q : K) = Iic q :=
  castOrderEmbedding.preimage_Iic q
#align rat.preimage_cast_Iic Rat.preimage_cast_Iic

@[simp]
theorem preimage_cast_Ioi (q : ℚ) : (↑) ⁻¹' Ioi (q : K) = Ioi q :=
  castOrderEmbedding.preimage_Ioi q
#align rat.preimage_cast_Ioi Rat.preimage_cast_Ioi

@[simp]
theorem preimage_cast_Iio (q : ℚ) : (↑) ⁻¹' Iio (q : K) = Iio q :=
  castOrderEmbedding.preimage_Iio q
#align rat.preimage_cast_Iio Rat.preimage_cast_Iio

@[simp]
theorem preimage_cast_uIcc (p q : ℚ) : (↑) ⁻¹' uIcc (p : K) q = uIcc p q :=
  (castOrderEmbedding (K := K)).preimage_uIcc p q

@[simp]
theorem preimage_cast_uIoc (p q : ℚ) : (↑) ⁻¹' uIoc (p : K) q = uIoc p q :=
  (castOrderEmbedding (K := K)).preimage_uIoc p q

end LinearOrderedField
end Rat

namespace NNRat

variable {K} [LinearOrderedSemifield K] {p q : ℚ≥0}

theorem cast_strictMono : StrictMono ((↑) : ℚ≥0 → K) := fun p q h => by
  rwa [NNRat.cast_def, NNRat.cast_def, div_lt_div_iff, ← Nat.cast_mul, ← Nat.cast_mul,
    Nat.cast_lt (α := K), ← NNRat.lt_def]
  · simp
  · simp

@[mono]
theorem cast_mono : Monotone ((↑) : ℚ≥0 → K) :=
  cast_strictMono.monotone

/-- Coercion from `ℚ` as an order embedding. -/
@[simps!]
def castOrderEmbedding : ℚ≥0 ↪o K :=
  OrderEmbedding.ofStrictMono (↑) cast_strictMono

@[simp, norm_cast] lemma cast_le : (p : K) ≤ q ↔ p ≤ q := castOrderEmbedding.le_iff_le
@[simp, norm_cast] lemma cast_lt : (p : K) < q ↔ p < q := cast_strictMono.lt_iff_lt
@[simp] lemma cast_nonpos : (q : K) ≤ 0 ↔ q ≤ 0 := by norm_cast
@[simp] lemma cast_pos : (0 : K) < q ↔ 0 < q := by norm_cast
@[norm_cast] lemma cast_lt_zero : (q : K) < 0 ↔ q < 0 := by norm_cast
@[simp] lemma not_cast_lt_zero : ¬(q : K) < 0 := mod_cast not_lt_zero'

@[simp, norm_cast] lemma cast_min (p q : ℚ≥0) : (↑(min p q) : K) = min (p : K) (q : K) :=
  (@cast_mono K _).map_min

@[simp, norm_cast] lemma cast_max (p q : ℚ≥0) : (↑(max p q) : K) = max (p : K) (q : K) :=
  (@cast_mono K _).map_max

open Set

@[simp]
theorem preimage_cast_Icc (p q : ℚ≥0) : (↑) ⁻¹' Icc (p : K) q = Icc p q :=
  castOrderEmbedding.preimage_Icc ..

@[simp]
theorem preimage_cast_Ico (p q : ℚ≥0) : (↑) ⁻¹' Ico (p : K) q = Ico p q :=
  castOrderEmbedding.preimage_Ico ..

@[simp]
theorem preimage_cast_Ioc (p q : ℚ≥0) : (↑) ⁻¹' Ioc (p : K) q = Ioc p q :=
  castOrderEmbedding.preimage_Ioc p q

@[simp]
theorem preimage_cast_Ioo (p q : ℚ≥0) : (↑) ⁻¹' Ioo (p : K) q = Ioo p q :=
  castOrderEmbedding.preimage_Ioo p q

@[simp]
theorem preimage_cast_Ici (p : ℚ≥0) : (↑) ⁻¹' Ici (p : K) = Ici p :=
  castOrderEmbedding.preimage_Ici p

@[simp]
theorem preimage_cast_Iic (p : ℚ≥0) : (↑) ⁻¹' Iic (p : K) = Iic p :=
  castOrderEmbedding.preimage_Iic p

@[simp]
theorem preimage_cast_Ioi (p : ℚ≥0) : (↑) ⁻¹' Ioi (p : K) = Ioi p :=
  castOrderEmbedding.preimage_Ioi p

@[simp]
theorem preimage_cast_Iio (p : ℚ≥0) : (↑) ⁻¹' Iio (p : K) = Iio p :=
  castOrderEmbedding.preimage_Iio p

@[simp]
theorem preimage_cast_uIcc (p q : ℚ≥0) : (↑) ⁻¹' uIcc (p : K) q = uIcc p q :=
  (castOrderEmbedding (K := K)).preimage_uIcc p q

@[simp]
theorem preimage_cast_uIoc (p q : ℚ≥0) : (↑) ⁻¹' uIoc (p : K) q = uIoc p q :=
  (castOrderEmbedding (K := K)).preimage_uIoc p q

end NNRat

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

/-- Extension for NNRat.cast. -/
@[positivity NNRat.cast _]
def evalNNRatCast : PositivityExt where eval {u α} _zα _pα e := do
  let ~q(@NNRat.cast _ (_) ($a : ℚ≥0)) := e | throwError "not NNRat.cast"
  match ← core q(inferInstance) q(inferInstance) a with
  | .positive pa =>
    let _oα ← synthInstanceQ q(LinearOrderedSemifield $α)
    assumeInstancesCommute
    return .positive q((NNRat.cast_pos (K := $α)).mpr $pa)
  | _ =>
    let _oα ← synthInstanceQ q(LinearOrderedSemifield $α)
    assumeInstancesCommute
    return .nonnegative q(NNRat.cast_nonneg _)

end Mathlib.Meta.Positivity
