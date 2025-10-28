/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Tactic.Positivity.Core

/-!
# Casts of rational numbers into linear ordered fields.
-/

variable {F ι α β : Type*}

namespace Rat
variable {p q : ℚ}

@[simp]
theorem castHom_rat : castHom ℚ = RingHom.id ℚ :=
  RingHom.ext cast_id

section LinearOrderedField

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem cast_pos_of_pos (hq : 0 < q) : (0 : K) < q := by
  rw [Rat.cast_def]
  exact div_pos (Int.cast_pos.2 <| num_pos.2 hq) (Nat.cast_pos.2 q.pos)

@[gcongr, mono]
theorem cast_strictMono : StrictMono ((↑) : ℚ → K) := fun p q => by
  simpa only [sub_pos, cast_sub] using cast_pos_of_pos (K := K) (q := q - p)

@[gcongr, mono]
theorem cast_mono : Monotone ((↑) : ℚ → K) :=
  cast_strictMono.monotone

/-- Coercion from `ℚ` as an order embedding. -/
@[simps!]
def castOrderEmbedding : ℚ ↪o K :=
  OrderEmbedding.ofStrictMono (↑) cast_strictMono

@[simp, norm_cast] lemma cast_le : (p : K) ≤ q ↔ p ≤ q := castOrderEmbedding.le_iff_le

@[simp, norm_cast] lemma cast_lt : (p : K) < q ↔ p < q := cast_strictMono.lt_iff_lt

@[simp] lemma cast_nonneg : 0 ≤ (q : K) ↔ 0 ≤ q := by norm_cast

@[simp] lemma cast_nonpos : (q : K) ≤ 0 ↔ q ≤ 0 := by norm_cast

@[simp] lemma cast_pos : (0 : K) < q ↔ 0 < q := by norm_cast

@[simp] lemma cast_lt_zero : (q : K) < 0 ↔ q < 0 := by norm_cast

@[simp, norm_cast]
theorem cast_le_natCast {m : ℚ} {n : ℕ} : (m : K) ≤ n ↔ m ≤ (n : ℚ) := by
  rw [← cast_le (K := K), cast_natCast]

@[simp, norm_cast]
theorem natCast_le_cast {m : ℕ} {n : ℚ} : (m : K) ≤ n ↔ (m : ℚ) ≤ n := by
  rw [← cast_le (K := K), cast_natCast]

@[simp, norm_cast]
theorem cast_le_intCast {m : ℚ} {n : ℤ} : (m : K) ≤ n ↔ m ≤ (n : ℚ) := by
  rw [← cast_le (K := K), cast_intCast]

@[simp, norm_cast]
theorem intCast_le_cast {m : ℤ} {n : ℚ} : (m : K) ≤ n ↔ (m : ℚ) ≤ n := by
  rw [← cast_le (K := K), cast_intCast]

@[simp, norm_cast]
theorem cast_lt_natCast {m : ℚ} {n : ℕ} : (m : K) < n ↔ m < (n : ℚ) := by
  rw [← cast_lt (K := K), cast_natCast]

@[simp, norm_cast]
theorem natCast_lt_cast {m : ℕ} {n : ℚ} : (m : K) < n ↔ (m : ℚ) < n := by
  rw [← cast_lt (K := K), cast_natCast]

@[simp, norm_cast]
theorem cast_lt_intCast {m : ℚ} {n : ℤ} : (m : K) < n ↔ m < (n : ℚ) := by
  rw [← cast_lt (K := K), cast_intCast]

@[simp, norm_cast]
theorem intCast_lt_cast {m : ℤ} {n : ℚ} : (m : K) < n ↔ (m : ℚ) < n := by
  rw [← cast_lt (K := K), cast_intCast]

@[simp, norm_cast]
lemma cast_min (p q : ℚ) : (↑(min p q) : K) = min (p : K) (q : K) := (@cast_mono K _).map_min

@[simp, norm_cast]
lemma cast_max (p q : ℚ) : (↑(max p q) : K) = max (p : K) (q : K) := (@cast_mono K _).map_max

@[simp, norm_cast] lemma cast_abs (q : ℚ) : ((|q| : ℚ) : K) = |(q : K)| := by simp [abs_eq_max_neg]

open Set

@[simp]
theorem preimage_cast_Icc (p q : ℚ) : (↑) ⁻¹' Icc (p : K) q = Icc p q :=
  castOrderEmbedding.preimage_Icc ..

@[simp]
theorem preimage_cast_Ico (p q : ℚ) : (↑) ⁻¹' Ico (p : K) q = Ico p q :=
  castOrderEmbedding.preimage_Ico ..

@[simp]
theorem preimage_cast_Ioc (p q : ℚ) : (↑) ⁻¹' Ioc (p : K) q = Ioc p q :=
  castOrderEmbedding.preimage_Ioc p q

@[simp]
theorem preimage_cast_Ioo (p q : ℚ) : (↑) ⁻¹' Ioo (p : K) q = Ioo p q :=
  castOrderEmbedding.preimage_Ioo p q

@[simp]
theorem preimage_cast_Ici (q : ℚ) : (↑) ⁻¹' Ici (q : K) = Ici q :=
  castOrderEmbedding.preimage_Ici q

@[simp]
theorem preimage_cast_Iic (q : ℚ) : (↑) ⁻¹' Iic (q : K) = Iic q :=
  castOrderEmbedding.preimage_Iic q

@[simp]
theorem preimage_cast_Ioi (q : ℚ) : (↑) ⁻¹' Ioi (q : K) = Ioi q :=
  castOrderEmbedding.preimage_Ioi q

@[simp]
theorem preimage_cast_Iio (q : ℚ) : (↑) ⁻¹' Iio (q : K) = Iio q :=
  castOrderEmbedding.preimage_Iio q

@[simp]
theorem preimage_cast_uIcc (p q : ℚ) : (↑) ⁻¹' uIcc (p : K) q = uIcc p q :=
  (castOrderEmbedding (K := K)).preimage_uIcc p q

@[simp]
theorem preimage_cast_uIoc (p q : ℚ) : (↑) ⁻¹' uIoc (p : K) q = uIoc p q :=
  (castOrderEmbedding (K := K)).preimage_uIoc p q

end LinearOrderedField
end Rat

namespace NNRat

variable {K} [Semifield K] [LinearOrder K] [IsStrictOrderedRing K] {p q : ℚ≥0}

theorem cast_strictMono : StrictMono ((↑) : ℚ≥0 → K) := fun p q h => by
  rwa [NNRat.cast_def, NNRat.cast_def, div_lt_div_iff₀, ← Nat.cast_mul, ← Nat.cast_mul,
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
@[simp] lemma cast_le_one : (p : K) ≤ 1 ↔ p ≤ 1 := by norm_cast
@[simp] lemma one_le_cast : 1 ≤ (p : K) ↔ 1 ≤ p := by norm_cast
@[simp] lemma cast_lt_one : (p : K) < 1 ↔ p < 1 := by norm_cast
@[simp] lemma one_lt_cast : 1 < (p : K) ↔ 1 < p := by norm_cast

section ofNat
variable {n : ℕ} [n.AtLeastTwo]

@[simp] lemma cast_le_ofNat : (p : K) ≤ ofNat(n) ↔ p ≤ OfNat.ofNat n := by
  simp [← cast_le (K := K)]

@[simp] lemma ofNat_le_cast : ofNat(n) ≤ (p : K) ↔ OfNat.ofNat n ≤ p := by
  simp [← cast_le (K := K)]

@[simp] lemma cast_lt_ofNat : (p : K) < ofNat(n) ↔ p < OfNat.ofNat n := by
  simp [← cast_lt (K := K)]

@[simp] lemma ofNat_lt_cast : ofNat(n) < (p : K) ↔ OfNat.ofNat n < p := by
  simp [← cast_lt (K := K)]

end ofNat

@[simp, norm_cast]
theorem cast_le_natCast {m : ℚ≥0} {n : ℕ} : (m : K) ≤ n ↔ m ≤ (n : ℚ≥0) := by
  rw [← cast_le (K := K), cast_natCast]

@[simp, norm_cast]
theorem natCast_le_cast {m : ℕ} {n : ℚ≥0} : (m : K) ≤ n ↔ (m : ℚ≥0) ≤ n := by
  rw [← cast_le (K := K), cast_natCast]

@[simp, norm_cast]
theorem cast_lt_natCast {m : ℚ≥0} {n : ℕ} : (m : K) < n ↔ m < (n : ℚ≥0) := by
  rw [← cast_lt (K := K), cast_natCast]

@[simp, norm_cast]
theorem natCast_lt_cast {m : ℕ} {n : ℚ≥0} : (m : K) < n ↔ (m : ℚ≥0) < n := by
  rw [← cast_lt (K := K), cast_natCast]

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
    let _oα ← synthInstanceQ q(Field $α)
    let _oα ← synthInstanceQ q(LinearOrder $α)
    let _oα ← synthInstanceQ q(IsStrictOrderedRing $α)
    assumeInstancesCommute
    return .positive q((Rat.cast_pos (K := $α)).mpr $pa)
  | .nonnegative pa =>
    let _oα ← synthInstanceQ q(Field $α)
    let _oα ← synthInstanceQ q(LinearOrder $α)
    let _oα ← synthInstanceQ q(IsStrictOrderedRing $α)
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
    let _oα ← synthInstanceQ q(Semifield $α)
    let _oα ← synthInstanceQ q(LinearOrder $α)
    let _oα ← synthInstanceQ q(IsStrictOrderedRing $α)
    assumeInstancesCommute
    return .positive q((NNRat.cast_pos (K := $α)).mpr $pa)
  | _ =>
    let _oα ← synthInstanceQ q(Semifield $α)
    let _oα ← synthInstanceQ q(LinearOrder $α)
    let _oα ← synthInstanceQ q(IsStrictOrderedRing $α)
    assumeInstancesCommute
    return .nonnegative q(NNRat.cast_nonneg _)

end Mathlib.Meta.Positivity
