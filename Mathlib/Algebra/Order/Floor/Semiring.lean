/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kevin Kappelmann
-/
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Order.Interval.Set.Defs

/-!
# Lemmas on `Nat.floor` and `Nat.ceil` for semirings

This file contains basic results on the natural-valued floor and ceiling functions.

## TODO

`LinearOrderedSemiring` can be relaxed to `OrderedSemiring` in many lemmas.

## Tags

rounding, floor, ceil
-/

assert_not_exists Finset

open Set

variable {R K : Type*}

namespace Nat

section LinearOrderedSemiring

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a b : R} {n : ℕ}

section floor

theorem floor_lt (ha : 0 ≤ a) : ⌊a⌋₊ < n ↔ a < n :=
  lt_iff_lt_of_le_iff_le <| le_floor_iff ha

theorem floor_lt_one (ha : 0 ≤ a) : ⌊a⌋₊ < 1 ↔ a < 1 :=
  (floor_lt ha).trans <| by rw [Nat.cast_one]

theorem floor_le (ha : 0 ≤ a) : (⌊a⌋₊ : R) ≤ a :=
  (le_floor_iff ha).1 le_rfl

theorem floor_eq_iff (ha : 0 ≤ a) : ⌊a⌋₊ = n ↔ ↑n ≤ a ∧ a < ↑n + 1 := by
  rw [← le_floor_iff ha, ← Nat.cast_one, ← Nat.cast_add, ← floor_lt ha, Nat.lt_add_one_iff,
    le_antisymm_iff, and_comm]

variable [IsStrictOrderedRing R]

theorem lt_of_floor_lt (h : ⌊a⌋₊ < n) : a < n :=
  lt_of_not_ge fun h' => (le_floor h').not_gt h

theorem lt_one_of_floor_lt_one (h : ⌊a⌋₊ < 1) : a < 1 := mod_cast lt_of_floor_lt h

theorem lt_succ_floor (a : R) : a < ⌊a⌋₊.succ :=
  lt_of_floor_lt <| Nat.lt_succ_self _

@[bound]
theorem lt_floor_add_one (a : R) : a < ⌊a⌋₊ + 1 := by simpa using lt_succ_floor a

@[simp]
theorem floor_natCast (n : ℕ) : ⌊(n : R)⌋₊ = n :=
  eq_of_forall_le_iff fun a => by
    rw [le_floor_iff, Nat.cast_le]
    exact n.cast_nonneg

@[simp]
theorem floor_zero : ⌊(0 : R)⌋₊ = 0 := by rw [← Nat.cast_zero, floor_natCast]

@[simp]
theorem floor_one : ⌊(1 : R)⌋₊ = 1 := by rw [← Nat.cast_one, floor_natCast]

@[simp]
theorem floor_ofNat (n : ℕ) [n.AtLeastTwo] : ⌊(ofNat(n) : R)⌋₊ = ofNat(n) :=
  Nat.floor_natCast _

theorem floor_of_nonpos (ha : a ≤ 0) : ⌊a⌋₊ = 0 :=
  ha.lt_or_eq.elim FloorSemiring.floor_of_neg <| by
    rintro rfl
    exact floor_zero

@[gcongr]
theorem floor_mono : Monotone (floor : R → ℕ) := fun a b h => by
  obtain ha | ha := le_total a 0
  · rw [floor_of_nonpos ha]
    exact Nat.zero_le _
  · exact le_floor ((floor_le ha).trans h)

@[bound] lemma floor_le_floor (hab : a ≤ b) : ⌊a⌋₊ ≤ ⌊b⌋₊ := floor_mono hab

theorem le_floor_iff' (hn : n ≠ 0) : n ≤ ⌊a⌋₊ ↔ (n : R) ≤ a := by
  obtain ha | ha := le_total a 0
  · rw [floor_of_nonpos ha]
    exact
      iff_of_false (Nat.pos_of_ne_zero hn).not_ge
        (not_le_of_gt <| ha.trans_lt <| cast_pos.2 <| Nat.pos_of_ne_zero hn)
  · exact le_floor_iff ha

@[simp]
theorem one_le_floor_iff (x : R) : 1 ≤ ⌊x⌋₊ ↔ 1 ≤ x :=
  mod_cast le_floor_iff' one_ne_zero

theorem floor_lt' (hn : n ≠ 0) : ⌊a⌋₊ < n ↔ a < n :=
  lt_iff_lt_of_le_iff_le <| le_floor_iff' hn

theorem floor_pos : 0 < ⌊a⌋₊ ↔ 1 ≤ a := by
  rw [Nat.lt_iff_add_one_le, zero_add, le_floor_iff' Nat.one_ne_zero, cast_one]

theorem pos_of_floor_pos (h : 0 < ⌊a⌋₊) : 0 < a :=
  (le_or_gt a 0).resolve_left fun ha => lt_irrefl 0 <| by rwa [floor_of_nonpos ha] at h

theorem lt_of_lt_floor (h : n < ⌊a⌋₊) : ↑n < a :=
  (Nat.cast_lt.2 h).trans_le <| floor_le (pos_of_floor_pos <| (Nat.zero_le n).trans_lt h).le

theorem floor_le_of_le (h : a ≤ n) : ⌊a⌋₊ ≤ n :=
  le_imp_le_iff_lt_imp_lt.2 lt_of_lt_floor h

theorem floor_le_one_of_le_one (h : a ≤ 1) : ⌊a⌋₊ ≤ 1 :=
  floor_le_of_le <| h.trans_eq <| Nat.cast_one.symm

@[simp]
theorem floor_eq_zero : ⌊a⌋₊ = 0 ↔ a < 1 := by
  rw [← lt_one_iff, ← @cast_one R]
  exact floor_lt' Nat.one_ne_zero

theorem floor_eq_iff' (hn : n ≠ 0) : ⌊a⌋₊ = n ↔ ↑n ≤ a ∧ a < ↑n + 1 := by
  rw [← le_floor_iff' hn, ← Nat.cast_one, ← Nat.cast_add, ← floor_lt' (Nat.add_one_ne_zero n),
    Nat.lt_add_one_iff, le_antisymm_iff, and_comm]

theorem floor_eq_on_Ico (n : ℕ) : ∀ a ∈ (Set.Ico n (n + 1) : Set R), ⌊a⌋₊ = n := fun _ ⟨h₀, h₁⟩ =>
  (floor_eq_iff <| n.cast_nonneg.trans h₀).mpr ⟨h₀, h₁⟩

theorem floor_eq_on_Ico' (n : ℕ) :
    ∀ a ∈ (Set.Ico n (n + 1) : Set R), (⌊a⌋₊ : R) = n :=
  fun x hx => mod_cast floor_eq_on_Ico n x hx

@[simp]
theorem preimage_floor_zero : (floor : R → ℕ) ⁻¹' {0} = Iio 1 :=
  ext fun _ => floor_eq_zero

theorem preimage_floor_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    (floor : R → ℕ) ⁻¹' {n} = Ico (n : R) (n + 1) :=
  ext fun _ => floor_eq_iff' hn

end floor

/-! #### Ceil -/

section ceil

theorem add_one_le_ceil_iff : n + 1 ≤ ⌈a⌉₊ ↔ (n : R) < a := by
  rw [← Nat.lt_ceil, Nat.add_one_le_iff]

@[simp]
theorem one_le_ceil_iff : 1 ≤ ⌈a⌉₊ ↔ 0 < a := by
  rw [← zero_add 1, Nat.add_one_le_ceil_iff, Nat.cast_zero]

@[bound]
theorem le_ceil (a : R) : a ≤ ⌈a⌉₊ :=
  ceil_le.1 le_rfl

theorem ceil_mono : Monotone (ceil : R → ℕ) :=
  gc_ceil_coe.monotone_l

@[gcongr, bound] lemma ceil_le_ceil (hab : a ≤ b) : ⌈a⌉₊ ≤ ⌈b⌉₊ := ceil_mono hab

@[simp]
theorem ceil_eq_zero : ⌈a⌉₊ = 0 ↔ a ≤ 0 := by rw [← Nat.le_zero, ceil_le, Nat.cast_zero]

theorem ceil_eq_iff (hn : n ≠ 0) : ⌈a⌉₊ = n ↔ ↑(n - 1) < a ∧ a ≤ n := by
  rw [← ceil_le, ← not_le, ← ceil_le, not_le,
    tsub_lt_iff_right (Nat.add_one_le_iff.2 (pos_iff_ne_zero.2 hn)), Nat.lt_add_one_iff,
    le_antisymm_iff, and_comm]

@[simp]
theorem preimage_ceil_zero : (Nat.ceil : R → ℕ) ⁻¹' {0} = Iic 0 :=
  ext fun _ => ceil_eq_zero

theorem preimage_ceil_of_ne_zero (hn : n ≠ 0) : (Nat.ceil : R → ℕ) ⁻¹' {n} = Ioc (↑(n - 1) : R) n :=
  ext fun _ => ceil_eq_iff hn

variable [IsStrictOrderedRing R]

@[bound]
theorem ceil_le_floor_add_one (a : R) : ⌈a⌉₊ ≤ ⌊a⌋₊ + 1 := by
  rw [ceil_le, Nat.cast_add, Nat.cast_one]
  exact (lt_floor_add_one a).le

@[simp]
theorem ceil_intCast {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
    [FloorSemiring R] (z : ℤ) :
    ⌈(z : R)⌉₊ = z.toNat :=
  eq_of_forall_ge_iff fun a => by
    simp only [ceil_le, Int.toNat_le]
    norm_cast

@[simp]
theorem ceil_natCast (n : ℕ) : ⌈(n : R)⌉₊ = n :=
  eq_of_forall_ge_iff fun a => by rw [ceil_le, cast_le]

@[simp]
theorem ceil_zero : ⌈(0 : R)⌉₊ = 0 := by rw [← Nat.cast_zero, ceil_natCast]

@[simp]
theorem ceil_one : ⌈(1 : R)⌉₊ = 1 := by rw [← Nat.cast_one, ceil_natCast]

@[simp]
theorem ceil_ofNat (n : ℕ) [n.AtLeastTwo] : ⌈(ofNat(n) : R)⌉₊ = ofNat(n) := ceil_natCast n

theorem lt_of_ceil_lt (h : ⌈a⌉₊ < n) : a < n :=
  (le_ceil a).trans_lt (Nat.cast_lt.2 h)

theorem le_of_ceil_le (h : ⌈a⌉₊ ≤ n) : a ≤ n :=
  (le_ceil a).trans (Nat.cast_le.2 h)

@[bound]
theorem floor_le_ceil (a : R) : ⌊a⌋₊ ≤ ⌈a⌉₊ := by
  obtain ha | ha := le_total a 0
  · rw [floor_of_nonpos ha]
    exact Nat.zero_le _
  · exact cast_le.1 ((floor_le ha).trans <| le_ceil _)

theorem floor_lt_ceil_of_lt_of_pos {a b : R} (h : a < b) (h' : 0 < b) : ⌊a⌋₊ < ⌈b⌉₊ := by
  rcases le_or_gt 0 a with (ha | ha)
  · rw [floor_lt ha]
    exact h.trans_le (le_ceil _)
  · rwa [floor_of_nonpos ha.le, lt_ceil, Nat.cast_zero]

end ceil

/-! #### Intervals -/

@[simp]
theorem preimage_Ioo {a b : R} (ha : 0 ≤ a) :
    (Nat.cast : ℕ → R) ⁻¹' Set.Ioo a b = Set.Ioo ⌊a⌋₊ ⌈b⌉₊ := by
  ext
  simp [floor_lt, lt_ceil, ha]

@[simp]
theorem preimage_Ico {a b : R} : (Nat.cast : ℕ → R) ⁻¹' Set.Ico a b = Set.Ico ⌈a⌉₊ ⌈b⌉₊ := by
  ext
  simp [ceil_le, lt_ceil]

@[simp]
theorem preimage_Ioc {a b : R} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Nat.cast : ℕ → R) ⁻¹' Set.Ioc a b = Set.Ioc ⌊a⌋₊ ⌊b⌋₊ := by
  ext
  simp [floor_lt, le_floor_iff, hb, ha]

@[simp]
theorem preimage_Icc {a b : R} (hb : 0 ≤ b) :
    (Nat.cast : ℕ → R) ⁻¹' Set.Icc a b = Set.Icc ⌈a⌉₊ ⌊b⌋₊ := by
  ext
  simp [ceil_le, hb, le_floor_iff]

@[simp]
theorem preimage_Ioi {a : R} (ha : 0 ≤ a) : (Nat.cast : ℕ → R) ⁻¹' Set.Ioi a = Set.Ioi ⌊a⌋₊ := by
  ext
  simp [floor_lt, ha]

@[simp]
theorem preimage_Ici {a : R} : (Nat.cast : ℕ → R) ⁻¹' Set.Ici a = Set.Ici ⌈a⌉₊ := by
  ext
  simp [ceil_le]

@[simp]
theorem preimage_Iio {a : R} : (Nat.cast : ℕ → R) ⁻¹' Set.Iio a = Set.Iio ⌈a⌉₊ := by
  ext
  simp [lt_ceil]

@[simp]
theorem preimage_Iic {a : R} (ha : 0 ≤ a) : (Nat.cast : ℕ → R) ⁻¹' Set.Iic a = Set.Iic ⌊a⌋₊ := by
  ext
  simp [le_floor_iff, ha]

theorem floor_add_natCast [IsStrictOrderedRing R] (ha : 0 ≤ a) (n : ℕ) : ⌊a + n⌋₊ = ⌊a⌋₊ + n :=
  eq_of_forall_le_iff fun b => by
    rw [le_floor_iff (add_nonneg ha n.cast_nonneg)]
    obtain hb | hb := le_total n b
    · obtain ⟨d, rfl⟩ := exists_add_of_le hb
      rw [Nat.cast_add, add_comm n, add_comm (n : R), add_le_add_iff_right, add_le_add_iff_right,
        le_floor_iff ha]
    · obtain ⟨d, rfl⟩ := exists_add_of_le hb
      rw [Nat.cast_add, add_left_comm _ b, add_left_comm _ (b : R)]
      refine iff_of_true ?_ le_self_add
      exact le_add_of_nonneg_right <| ha.trans <| le_add_of_nonneg_right d.cast_nonneg

variable [IsStrictOrderedRing R]

theorem floor_add_one (ha : 0 ≤ a) : ⌊a + 1⌋₊ = ⌊a⌋₊ + 1 := by
  rw [← cast_one, floor_add_natCast ha 1]

theorem floor_add_ofNat (ha : 0 ≤ a) (n : ℕ) [n.AtLeastTwo] :
    ⌊a + ofNat(n)⌋₊ = ⌊a⌋₊ + ofNat(n) :=
  floor_add_natCast ha n

@[simp]
theorem floor_sub_natCast [Sub R] [OrderedSub R] [ExistsAddOfLE R] (a : R) (n : ℕ) :
    ⌊a - n⌋₊ = ⌊a⌋₊ - n := by
  obtain ha | ha := le_total a 0
  · rw [floor_of_nonpos ha, floor_of_nonpos (tsub_nonpos_of_le (ha.trans n.cast_nonneg)), zero_tsub]
  rcases le_total a n with h | h
  · rw [floor_of_nonpos (tsub_nonpos_of_le h), eq_comm, tsub_eq_zero_iff_le]
    exact Nat.cast_le.1 ((Nat.floor_le ha).trans h)
  · rw [eq_tsub_iff_add_eq_of_le (le_floor h), ← floor_add_natCast _, tsub_add_cancel_of_le h]
    exact le_tsub_of_add_le_left ((add_zero _).trans_le h)

@[simp]
theorem floor_sub_one [Sub R] [OrderedSub R] [ExistsAddOfLE R] (a : R) : ⌊a - 1⌋₊ = ⌊a⌋₊ - 1 :=
  mod_cast floor_sub_natCast a 1

@[simp]
theorem floor_sub_ofNat [Sub R] [OrderedSub R] [ExistsAddOfLE R] (a : R) (n : ℕ) [n.AtLeastTwo] :
    ⌊a - ofNat(n)⌋₊ = ⌊a⌋₊ - ofNat(n) :=
  floor_sub_natCast a n

theorem ceil_add_natCast (ha : 0 ≤ a) (n : ℕ) : ⌈a + n⌉₊ = ⌈a⌉₊ + n :=
  eq_of_forall_ge_iff fun b => by
    rw [← not_lt, ← not_lt, not_iff_not, lt_ceil]
    obtain hb | hb := le_or_gt n b
    · obtain ⟨d, rfl⟩ := exists_add_of_le hb
      rw [Nat.cast_add, add_comm n, add_comm (n : R), add_lt_add_iff_right, add_lt_add_iff_right,
        lt_ceil]
    · exact iff_of_true (lt_add_of_nonneg_of_lt ha <| cast_lt.2 hb) (Nat.lt_add_left _ hb)

theorem ceil_add_one (ha : 0 ≤ a) : ⌈a + 1⌉₊ = ⌈a⌉₊ + 1 := by
  rw [cast_one.symm, ceil_add_natCast ha 1]

theorem ceil_add_ofNat (ha : 0 ≤ a) (n : ℕ) [n.AtLeastTwo] :
    ⌈a + ofNat(n)⌉₊ = ⌈a⌉₊ + ofNat(n) :=
  ceil_add_natCast ha n

@[bound]
theorem ceil_lt_add_one (ha : 0 ≤ a) : (⌈a⌉₊ : R) < a + 1 :=
  lt_ceil.1 <| (Nat.lt_succ_self _).trans_le (ceil_add_one ha).ge

@[bound]
theorem ceil_add_le (a b : R) : ⌈a + b⌉₊ ≤ ⌈a⌉₊ + ⌈b⌉₊ := by
  rw [ceil_le, Nat.cast_add]
  gcongr <;> apply le_ceil

variable [Sub R] [OrderedSub R] [ExistsAddOfLE R]

@[simp] lemma ceil_sub_natCast (a : R) (n : ℕ) : ⌈a - n⌉₊ = ⌈a⌉₊ - n := by
  obtain han | hna := le_total a n
  · rwa [ceil_eq_zero.2 (tsub_nonpos_of_le han), eq_comm, tsub_eq_zero_iff_le, Nat.ceil_le]
  · refine eq_tsub_of_add_eq ?_
    rw [← ceil_add_natCast, tsub_add_cancel_of_le hna]
    exact le_tsub_of_add_le_left ((add_zero _).trans_le hna)

@[simp] lemma ceil_sub_one (a : R) : ⌈a - 1⌉₊ = ⌈a⌉₊ - 1 := by simpa using ceil_sub_natCast a 1

@[simp] lemma ceil_sub_ofNat (a : R) (n : ℕ) [n.AtLeastTwo] : ⌈a - ofNat(n)⌉₊ = ⌈a⌉₊ - ofNat(n) :=
  ceil_sub_natCast a n

end LinearOrderedSemiring

section LinearOrderedRing

variable [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorSemiring R]

@[bound]
theorem sub_one_lt_floor (a : R) : a - 1 < ⌊a⌋₊ :=
  sub_lt_iff_lt_add.2 <| lt_floor_add_one a

lemma abs_sub_floor_le {a : R} (ha : 0 ≤ a) : |a - ⌊a⌋₊| ≤ 1 := by
  refine abs_le.mpr ⟨?_, ?_⟩
  · simpa using (floor_le ha).trans (le_add_of_nonneg_right zero_le_one)
  · simpa [add_comm] using (lt_floor_add_one a).le

lemma abs_floor_sub_le {a : R} (ha : 0 ≤ a) : |⌊a⌋₊ - a| ≤ 1 :=
  abs_sub_comm a ⌊a⌋₊ ▸ abs_sub_floor_le ha

lemma abs_sub_ceil_le {a : R} (ha : 0 ≤ a) : |a - ⌈a⌉₊| ≤ 1 := by
  refine abs_le.mpr ⟨?_, ?_⟩
  · simpa using (ceil_lt_add_one ha).le
  · simpa using (le_ceil a).trans (le_add_of_nonneg_left zero_le_one)

lemma abs_ceil_sub_le {a : R} (ha : 0 ≤ a) : |⌈a⌉₊ - a| ≤ 1 :=
  abs_sub_comm a ⌈a⌉₊ ▸ abs_sub_ceil_le ha

end LinearOrderedRing

variable [Semiring R] [LinearOrder R] [FloorSemiring R] {a : R}
variable {S : Type*} [Semiring S] [LinearOrder S] [FloorSemiring S] {b : S}

theorem floor_congr [IsStrictOrderedRing R] [IsStrictOrderedRing S]
    (h : ∀ n : ℕ, (n : R) ≤ a ↔ (n : S) ≤ b) : ⌊a⌋₊ = ⌊b⌋₊ := by
  have h₀ : 0 ≤ a ↔ 0 ≤ b := by simpa only [cast_zero] using h 0
  obtain ha | ha := lt_or_ge a 0
  · rw [floor_of_nonpos ha.le, floor_of_nonpos (le_of_not_ge <| h₀.not.mp ha.not_ge)]
  exact (le_floor <| (h _).1 <| floor_le ha).antisymm (le_floor <| (h _).2 <| floor_le <| h₀.1 ha)

theorem ceil_congr (h : ∀ n : ℕ, a ≤ n ↔ b ≤ n) : ⌈a⌉₊ = ⌈b⌉₊ :=
  (ceil_le.2 <| (h _).2 <| le_ceil _).antisymm <| ceil_le.2 <| (h _).1 <| le_ceil _

variable {F : Type*} [FunLike F R S] [RingHomClass F R S]

theorem map_floor [IsStrictOrderedRing R] [IsStrictOrderedRing S]
    (f : F) (hf : StrictMono f) (a : R) : ⌊f a⌋₊ = ⌊a⌋₊ :=
  floor_congr fun n => by rw [← map_natCast f, hf.le_iff_le]

theorem map_ceil (f : F) (hf : StrictMono f) (a : R) : ⌈f a⌉₊ = ⌈a⌉₊ :=
  ceil_congr fun n => by rw [← map_natCast f, hf.le_iff_le]

end Nat

/-- There exists at most one `FloorSemiring` structure on a linear ordered semiring. -/
theorem subsingleton_floorSemiring {R} [Semiring R] [LinearOrder R] :
    Subsingleton (FloorSemiring R) := by
  refine ⟨fun H₁ H₂ => ?_⟩
  have : H₁.ceil = H₂.ceil := funext fun a => (H₁.gc_ceil.l_unique H₂.gc_ceil) fun n => rfl
  have : H₁.floor = H₂.floor := by
    ext a
    rcases lt_or_ge a 0 with h | h
    · rw [H₁.floor_of_neg, H₂.floor_of_neg] <;> exact h
    · refine eq_of_forall_le_iff fun n => ?_
      rw [H₁.gc_floor, H₂.gc_floor] <;> exact h
  cases H₁
  cases H₂
  congr
