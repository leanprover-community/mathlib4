/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.CompleteField
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
import Mathlib.Algebra.Order.Hom.Monoid
import Mathlib.Algebra.Order.Hom.Ring
import Mathlib.Algebra.Order.Module.OrderedSMul

/-!
# Embedding of archimedean groups into reals

This file provides embedding of any archimedean groups into reals.

## Main declarations
* `Archimedean.embedReal` defines an injective `M →+o ℝ` for archimedean group `M` with a positive
  `1` element. `1` is preserved by the map.
* `Archimedean.exists_orderAddMonoidHom_real_injective` states there exists an injective `M →+o ℝ`
  for any archimedean group `M` without specifying the `1` element in `M`.
* `Archimedean.embedRealOrderRingHom` upgrades `Archimedean.embedReal` to a `M →+*o ℝ` when
  `M` is an archimedean ring.
-/


variable {M : Type*}
variable [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M] [One M]

theorem mul_smul_one_lt_iff {num : ℤ} {n den : ℕ} (hn : 0 < n) {x : M} :
    (num * n) • 1 < (n * den : ℤ) • x ↔ num • 1 < den • x := by
  rw [mul_comm num, mul_smul, mul_smul, natCast_zsmul x den]
  exact ⟨fun h ↦ lt_of_smul_lt_smul_left h (Int.natCast_nonneg n),
    fun h ↦ zsmul_lt_zsmul_right (Int.natCast_pos.mpr hn) h⟩

/-- For `u v : ℚ` and `x y : M`, one can informally write
`u < x → v < y → u + v < x + y`. We formalize this using smul. -/
theorem num_smul_one_lt_den_smul_add {u v : ℚ} {x y : M}
    (hu : u.num • 1 < u.den • x) (hv : v.num • 1 < v.den • y) :
    (u + v).num • 1 < (u + v).den • (x + y) := by
  have hu' : (u.num * v.den) • 1 < (u.den * v.den : ℤ) • x := by
    simpa [mul_comm] using (mul_smul_one_lt_iff v.den_pos).mpr hu
  suffices ((u + v).num * u.den * v.den) • 1 <
      ((u + v).den : ℤ) • (u.den * v.den : ℤ) • (x + y) by
    refine (mul_smul_one_lt_iff (mul_pos u.den_pos v.den_pos)).mp ?_
    rwa [Nat.cast_mul, ← mul_assoc, mul_comm _ ((u + v).den : ℤ), ← smul_eq_mul ((u + v).den : ℤ),
      smul_assoc]
  rw [Rat.add_num_den', mul_comm, ← smul_smul]
  rw [smul_lt_smul_iff_of_pos_left (by simpa using (u + v).den_pos)]
  rw [add_smul, smul_add]
  exact add_lt_add hu' ((mul_smul_one_lt_iff u.den_pos).mpr hv)

/-- Given `x` from `M`, one can informally write that, by transitivity,
`num / den ≤ x → x ≤ n → num / den ≤ n` for `den : ℕ` and `num n : ℕ`.
To avoid writing division for integer `num` and `den`, we express this in terms of
multiplication. -/
theorem num_le_nat_mul_den [ZeroLEOneClass M] [NeZero (1 : M)]
    {num : ℤ} {den : ℕ} {x : M} (h : num • 1 ≤ den • x)
    {n : ℤ} (hn : x ≤ n • 1) : num ≤ n * den := by
  refine le_of_smul_le_smul_right (h.trans ?_) (by simp)
  rw [mul_comm, ← smul_smul]
  simpa using nsmul_le_nsmul_right hn den

namespace Archimedean

/-- Set of rational numbers that are less than the "number" `x / 1`.
 Formally, these are numbers `p / q` such that `p • 1 < q • x`. -/
abbrev ratLt (x : M) : Set ℚ := {r | r.num • 1 < r.den • x}

theorem mkRat_mem_ratLt {num : ℤ} {den : ℕ} (hden : den ≠ 0) {x : M} :
    mkRat num den ∈ ratLt x ↔ num • 1 < den • x := by
  rw [Set.mem_setOf]
  obtain ⟨m, hm0, hnum, hden⟩ := Rat.mkRat_num_den hden (show mkRat num den = _ by rfl)
  have hnum : num = (mkRat num den).num * m := hnum
  have hden : den = (mkRat num den).den * m := hden
  conv in num • 1 => rw [hnum, mul_comm, ← smul_smul, natCast_zsmul]
  conv in den • x => rw [hden, mul_comm, ← smul_smul]
  exact (smul_lt_smul_iff_of_pos_left (Nat.zero_lt_of_ne_zero hm0)).symm

/-- `ratLt` as a set of real numbers. -/
abbrev ratLt' (x : M) : Set ℝ := (Rat.castHom ℝ) '' (ratLt x)

/-- Mapping `M` to `ℝ`, defined as the supremum of `ratLt' x`. -/
noncomputable
abbrev embedRealFun (x : M) := sSup (ratLt' x)

variable [ZeroLEOneClass M] [NeZero (1 : M)] [Archimedean M]

theorem ratLt_bddAbove (x : M) : BddAbove (ratLt x) := by
  obtain ⟨n, hn⟩ := Archimedean.arch x zero_lt_one
  use n
  rw [ratLt, mem_upperBounds]
  intro ⟨num, den, _, _⟩
  rw [Rat.le_iff]
  suffices num • 1 < den • x → num ≤ n * den by simpa using this
  intro h
  exact num_le_nat_mul_den h.le (by simpa using hn)

theorem ratLt_nonempty (x : M) : (ratLt x).Nonempty := by
  obtain hneg | rfl | hxpos := lt_trichotomy x 0
  · obtain ⟨n, hn⟩ := Archimedean.arch (-x - x) zero_lt_one
    use Rat.ofInt (-n)
    suffices -(n • 1) < x by simpa using this
    exact neg_lt.mpr (lt_of_lt_of_le (by simpa using hneg) hn)
  · exact ⟨Rat.ofInt (-1), by simp⟩
  · obtain ⟨n, hn⟩ := Archimedean.arch 1 hxpos
    use Rat.mk' 1 (n + 1) (by simp) (by simp)
    simpa using hn.trans_lt <| (nsmul_lt_nsmul_iff_left hxpos).mpr (by simp)

open Pointwise in
theorem ratLt_add (x y : M) : ratLt (x + y) = ratLt x + ratLt y := by
  ext a
  rw [Set.mem_add]
  constructor
  · /- Given `a ∈ ratLt 1 (x + y)`, find `u ∈ ratLt 1 x`, `v ∈ ratLt 1 y`
      such that `u + v = a`.
      In a naive attempt, one can take the denominator `d` of `a`,
      and find the largest `u = p / d < x / 1`.
      However, `d` could be too "coarse", and `v = a - u` could be 1/d too large than `y / 1`.
      To ensure a large enough denominator, we take `d * k`, where
      `1 + 1 ≤ k • (d • (x + y) - a.num • 1)`. -/
    intro h
    rw [Set.mem_setOf_eq] at h
    obtain ⟨k, hk⟩ := Archimedean.arch (1 + 1) <| sub_pos.mpr h
    have hk0 : k ≠ 0 := by
      contrapose! hk
      simp [hk]
    have hka0 : k * a.den ≠ 0 := mul_ne_zero hk0 a.den_ne_zero
    obtain ⟨m, ⟨hm1, hm2⟩, _⟩ := existsUnique_add_zsmul_mem_Ico zero_lt_one 0 (k • a.den • x - 1)
    refine ⟨mkRat m (k * a.den), ?_, mkRat (k * a.num - m) (k * a.den) , ?_, ?_⟩
    · rw [mkRat_mem_ratLt hka0, ← smul_smul]
      simpa using hm2
    · have hk' : 1 + (k • a.num • 1 - k • a.den • y) ≤ k • a.den • x - 1 := by
        rw [smul_add, smul_sub, smul_add, le_sub_iff_add_le, ← sub_le_iff_le_add] at hk
        rw [le_sub_iff_add_le]
        convert hk using 1
        abel
      have : k • a.num • 1 - k • a.den • y < m • 1 :=
        lt_of_lt_of_le (lt_add_of_pos_left _ zero_lt_one) (by simpa using hk'.trans hm1)
      rw [mkRat_mem_ratLt hka0, sub_smul, sub_lt_comm, ← smul_smul, ← smul_smul, natCast_zsmul]
      exact this
    · rw [Rat.mkRat_add_mkRat_of_den _ _ hka0]
      rw [add_sub_cancel, Rat.mkRat_mul_left hk0, Rat.mkRat_num_den']
  · -- `u ∈ ratLt 1 x`, `v ∈ ratLt 1 y` → `u + v ∈ ratLt 1 (x + y)`
    intro ⟨u, hu, v, hv, huv⟩
    rw [← huv]
    rw [Set.mem_setOf_eq] at hu hv ⊢
    exact num_smul_one_lt_den_smul_add hu hv

theorem ratLt'_bddAbove (x : M) : BddAbove (ratLt' x) :=
   Monotone.map_bddAbove Rat.cast_mono <| ratLt_bddAbove x

theorem ratLt'_nonempty (x : M) : (ratLt' x).Nonempty := Set.image_nonempty.mpr (ratLt_nonempty x)

open Pointwise in
theorem ratLt'_add (x y : M) : ratLt' (x + y) = ratLt' x + ratLt' y := by
  rw [ratLt', ratLt_add, Set.image_add]

variable (M) in
theorem embedRealFun_zero : embedRealFun (0 : M) = 0 := by
  apply le_antisymm
  · apply csSup_le (ratLt'_nonempty 0)
    intro x
    unfold ratLt' ratLt
    suffices ∀ (y : ℚ), y.num • (1 : M) < 0 → y = x → x ≤ 0 by simpa using this
    intro y hy hyx
    rw [← hyx, Rat.cast_nonpos, ← Rat.num_nonpos]
    exact (neg_of_smul_neg_right hy zero_le_one).le
  · rw [le_csSup_iff (ratLt'_bddAbove (0 : M)) (ratLt'_nonempty 0)]
    intro x
    rw [mem_upperBounds]
    suffices (∀ (y : ℚ), y.num • (1 : M) < 0 → y ≤ x) → 0 ≤ x by simpa using this
    intro h
    have h' (y : ℚ) (hy: y < 0) : y ≤ x := by
      exact h _ <| (smul_neg_iff_of_neg_left (by simpa using hy)).mpr zero_lt_one
    contrapose! h'
    obtain ⟨y, hxy, hy⟩ := exists_rat_btwn h'
    exact ⟨y, by simpa using hy, hxy⟩

theorem embedRealFun_add (x y : M) : embedRealFun (x + y) = embedRealFun x + embedRealFun y := by
  rw [embedRealFun, ratLt'_add, csSup_add (ratLt'_nonempty x) (ratLt'_bddAbove x)
    (ratLt'_nonempty y) (ratLt'_bddAbove y)]

variable (M) in
theorem embedRealFun_strictMono : StrictMono (embedRealFun (M := M)) := by
  intro x y h
  have hyz : 0 < y - x := sub_pos.mpr h
  have hy : y = y - x + x := (sub_add_cancel y x).symm
  apply lt_of_sub_pos
  rw [hy, embedRealFun_add, add_sub_cancel_right]
  obtain ⟨n, hn⟩ := Archimedean.arch 1 hyz
  have : (Rat.mk' 1 (n + 1) (by simp) (by simp) : ℝ) ∈ ratLt' (y - x) := by
    simpa using hn.trans_lt <| nsmul_lt_nsmul_left hyz (show n < n + 1 by simp)
  exact lt_csSup_of_lt (ratLt'_bddAbove (y - x)) this (by simp [← Rat.num_pos])

variable (M) in
/-- The bundled `M →+o ℝ` for archimedean `M` that preserves `1`. -/
noncomputable
def embedReal : M →+o ℝ where
  toFun := embedRealFun
  map_zero' := embedRealFun_zero M
  map_add' := embedRealFun_add
  monotone' := (embedRealFun_strictMono M).monotone

theorem embedReal_apply (a : M) :  embedReal M a = embedRealFun a := by rfl

variable (M) in
theorem embedReal_injective : Function.Injective (embedReal M) :=
  (embedRealFun_strictMono M).injective

@[simp]
theorem embedReal_one : (embedReal M) 1 = 1 := by
  rw [embedReal_apply]
  apply le_antisymm
  · apply csSup_le (ratLt'_nonempty 1)
    suffices ∀ (x : ℚ), x.num • (1 : M) < (x.den : ℤ) • (1 : M) → (x : ℝ) ≤ 1 by simpa using this
    intro x hx
    suffices x ≤ 1 by norm_cast
    simpa [Rat.le_iff] using ((smul_lt_smul_iff_of_pos_right zero_lt_one).mp hx).le
  · rw [le_csSup_iff (ratLt'_bddAbove (1 : M)) (ratLt'_nonempty 1)]
    simp_rw [mem_upperBounds]
    suffices ∀ (x : ℝ), (∀ (y : ℚ), y.num • (1 : M) < (y.den : ℤ) • 1 → y ≤ x) → 1 ≤ x by
      simpa using this
    intro x h
    have h' (y : ℚ) (hy : y < 1) : y ≤ x :=
      h _ ((smul_lt_smul_iff_of_pos_right zero_lt_one).mpr (by simpa using (Rat.lt_iff _ _).mp hy))
    contrapose! h'
    obtain ⟨y, hxy, hy⟩ := exists_rat_btwn h'
    exact ⟨y, (by norm_cast at hy), hxy⟩

omit [One M] [ZeroLEOneClass M] [NeZero (1 : M)] in
variable (M) in
theorem exists_orderAddMonoidHom_real_injective :
    ∃ f : M →+o ℝ, Function.Injective f := by
  by_cases h : Subsingleton M
  · exact ⟨0, Function.injective_of_subsingleton _⟩
  · have : Nontrivial M := not_subsingleton_iff_nontrivial.mp h
    obtain ⟨a, ha⟩ := exists_ne (0 : M)
    let one : One M := ⟨|a|⟩
    have : ZeroLEOneClass M := ⟨abs_nonneg a⟩
    have : NeZero (1 : M) := ⟨abs_ne_zero.mpr ha⟩
    exact ⟨embedReal M, embedReal_injective M⟩

/-! ### promote to OrderRingHom for Archimedean ring -/

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [One M]

/-- A version of `ratLt` restricted to positive numbers. -/
abbrev posRatLt (x : M) : Set ℚ := {r | 0 < r ∧ r.num • 1 < r.den • x}

/-- A version of `ratLt'` restricted to positive numbers. -/
abbrev posRatLt' (x : M) : Set ℝ := (Rat.castHom ℝ) '' (posRatLt x)

theorem posRatLt_subset_ratLt (x : M) : posRatLt x ⊆ ratLt x := by simp

theorem pos_of_mem_posRatLt' {x : M} {r : ℝ} (hr : r ∈ posRatLt' x) : 0 < r := by
  rw [Set.mem_image] at hr
  obtain ⟨x, hx, rfl⟩ := hr
  simpa using hx.1

theorem mem_posRatLt'_iff (x : M) (y : ℝ) : y ∈ posRatLt' x ↔ 0 < y ∧ y ∈ ratLt' x := by
  unfold posRatLt' posRatLt ratLt'
  rw [Set.setOf_and, Set.image_inter (by simpa using Rat.cast_injective), Set.mem_inter_iff]
  aesop

variable [IsOrderedAddMonoid M]

theorem mkRat_mem_posRatLt {num : ℤ} {den : ℕ} (hden : den ≠ 0) (x : M) :
    mkRat num den ∈ posRatLt x ↔ 0 < num ∧ num • 1 < den • x := by
  rw [← mkRat_mem_ratLt hden, ← Rat.mkRat_pos_iff _ hden]
  rfl

variable [Archimedean M]

theorem posRatLt_nonempty {x : M} (hx : 0 < x) : (posRatLt x).Nonempty := by
  obtain ⟨n, hn⟩ := Archimedean.arch 1 hx
  use Rat.mk' 1 (n + 1) (by simp) (by simp)
  refine ⟨Rat.num_pos.mp (by simp), ?_⟩
  simpa using hn.trans_lt <| (nsmul_lt_nsmul_iff_left hx).mpr (by simp)

theorem posRatLt'_nonempty {x : M} (hx : 0 < x) :
    (posRatLt' x).Nonempty := by
  rw [Set.image_nonempty]
  exact posRatLt_nonempty hx

variable [ZeroLEOneClass M] [NeZero (1 : M)]

theorem posRatLt_bddAbove (x : M) : BddAbove (posRatLt x) :=
  (ratLt_bddAbove x).mono (posRatLt_subset_ratLt x)

theorem posRatLt'_bddAbove (x : M) : BddAbove (posRatLt' x) :=
  Monotone.map_bddAbove Rat.cast_mono <| posRatLt_bddAbove _

theorem sup_posRatLt'_pos {x : M} (hx : 0 < x) :
    0 < sSup (posRatLt' x) := by
  obtain ⟨a, ha⟩ := posRatLt'_nonempty hx
  apply lt_csSup_of_lt (posRatLt'_bddAbove _) ha
  rw [Set.mem_image] at ha
  obtain ⟨b, hb, rfl⟩ := ha
  simpa using hb.1

variable {M : Type*} [Ring M] [LinearOrder M] [IsStrictOrderedRing M]

theorem mem_posRatLt_mul (x y : M) {u v : ℚ} (hu : u ∈ posRatLt x) (hv : v ∈ posRatLt y) :
    u * v ∈ posRatLt (x * y) := by
  obtain ⟨hu0, hu⟩ := hu
  obtain ⟨hv0, hv⟩ := hv
  refine ⟨mul_pos hu0 hv0, ?_⟩
  have hgcd : 0 < (u.num * v.num).natAbs.gcd (u.den * v.den) := by simp [u.den_pos, v.den_pos]
  apply (smul_lt_smul_iff_of_pos_left hgcd).mp
  rw [zsmul_one, nsmul_eq_mul, smul_smul]
  norm_cast
  rw [mul_comm _ (u * v).num, mul_comm _ (u * v).den]
  rw [← Rat.den_mul_den_eq_den_mul_gcd, ← Rat.num_mul_num_eq_num_mul_gcd]
  rw [mul_smul_mul_comm u.den v.den x y]
  push_cast
  exact mul_lt_mul (by simpa using hu) (by simpa using hv.le)
    (by simpa using hv0) (lt_trans (by simpa using hu0) hu).le

variable [Archimedean M]

open Pointwise in
theorem posRatLt_mul (x : M) {y : M} (hy : 0 < y) :
    posRatLt (x * y) = posRatLt x * posRatLt y := by
  ext a
  rw [Set.mem_mul]
  constructor
  · /- we'd like to find u ∈ posRatLt x and v ∈ posRatLt y such that u * v = a ∈ posRatLt (x * y)
       This can be accomplished by giving a large enough denomitor to the largest possible
       numerator to u. Here we take
       k = ⌈(a.den • y + 1) / (a.den • (x * y) - a.num)⌉
       u = ⌊k • x - 1⌋ / k
       v = a / u
    -/
    intro ⟨ha0, ha⟩
    obtain ⟨k, hk⟩ := Archimedean.arch (a.den • y + 1) (sub_pos.mpr ha)
    have hk0 : 0 < k := by
      contrapose! hk
      rw [show k = 0 by simpa using hk]
      simpa using add_pos (mul_pos (by simpa using a.den_pos) hy) (by simp)
    rw [smul_sub, smul_smul, le_sub_iff_add_le', ← add_assoc] at hk
    obtain ⟨m, ⟨hm1, hm2⟩, _⟩ := existsUnique_add_zsmul_mem_Ico zero_lt_one 0 (k • x - 1)
    have hm1 : k • x - 1 ≤ m := by simpa using hm1
    have hm0 : 0 < m := by
      suffices 0 < k • x - 1 by simpa using lt_of_lt_of_le this hm1
      apply sub_pos_of_lt
      refine lt_of_mul_lt_mul_of_nonneg_right ?_
        (show 0 ≤ a.den • y from smul_nonneg (by simp) hy.le)
      rw [← mul_smul_mul_comm]
      refine lt_of_lt_of_le ?_ hk
      trans k • a.num + a.den • y
      · simpa using mul_pos (by simpa using hk0) (by simpa using ha0)
      · simp
    refine ⟨mkRat m k, ?_, mkRat (a.num * k) (a.den * m.toNat) , ?_, ?_⟩
    · rw [mkRat_mem_posRatLt (ne_of_gt hk0) x]
      exact ⟨hm0, by simpa using hm2⟩
    · rw [mkRat_mem_posRatLt (ne_of_gt (mul_pos a.den_pos (by simpa using hm0))) y]
      constructor
      · exact mul_pos (by simpa using ha0) (by simpa using hk0)
      · refine lt_of_lt_of_le (?_ : _ < (a.den * (k • x - 1)) * y) ?_
        · rw [mul_sub_one, sub_mul, lt_sub_iff_add_lt]
          rw [show a.den * k • x = a.den • k • x from (nsmul_eq_mul _ _).symm]
          rw [smul_smul, mul_comm a.den k, mul_comm a.num k, smul_mul_assoc]
          exact lt_of_lt_of_le (by simp) hk
        · suffices a.den * (k • x - 1) * y ≤ a.den * m.toNat * y by simpa using this
          refine mul_le_mul_of_nonneg_right ?_ hy.le
          refine mul_le_mul_of_nonneg_left ?_ (by simp)
          apply hm1.trans_eq
          suffices m = m.toNat by norm_cast
          exact (Int.toNat_of_nonneg hm0.le).symm
    · rw [Rat.mkRat_mul_mkRat, mul_comm a.num, mul_comm a.den, ← mul_assoc, ← mul_assoc, mul_comm m]
      rw [show k * m = (k * m.toNat : ℕ) by simp [hm0.le]]
      rw [Rat.mkRat_mul_left (ne_of_gt (mul_pos hk0 (by simpa using hm0)))]
      simp
  · intro ⟨u, hu, v, hv, huv⟩
    rw [← huv]
    apply mem_posRatLt_mul _ _ hu hv

open Pointwise in
theorem posRatLt'_mul (x : M) {y : M} (hy : 0 < y) :
    posRatLt' (x * y) = posRatLt' x * posRatLt' y := by
  simp_rw [posRatLt', posRatLt_mul x hy, Set.image_mul]

theorem sup_ratLt_eq_sup_posRatLt {x : M} (hx : 0 < x) :
    sSup (ratLt' x) = sSup (posRatLt' x) := by
  apply eq_of_forall_ge_iff
  intro y
  rw [csSup_le_iff (posRatLt'_bddAbove x) (posRatLt'_nonempty hx)]
  rw [csSup_le_iff (ratLt'_bddAbove x) (ratLt'_nonempty x)]
  simp_rw [mem_posRatLt'_iff]
  constructor
  · intro h b ⟨hb0, hb⟩
    exact h b hb
  · intro h b hb
    obtain hb0 | hb0 := lt_or_ge 0 b
    · exact h b ⟨hb0, hb⟩
    · obtain ⟨c, hc⟩ := (posRatLt'_nonempty hx)
      rw [mem_posRatLt'_iff] at hc
      exact le_trans (le_trans hb0 hc.1.le) (h c hc)

theorem embedReal_mul_of_nonneg {x y : M} (hx : 0 < x) (hy : 0 < y) :
    embedReal M (x * y) = embedReal M x * embedReal M y := by
  simp_rw [embedReal_apply, embedRealFun]
  rw [sup_ratLt_eq_sup_posRatLt hx, sup_ratLt_eq_sup_posRatLt hy]
  rw [sup_ratLt_eq_sup_posRatLt (mul_pos hx hy)]
  refine eq_of_forall_ge_iff fun c => ?_
  open Pointwise in
  have h : posRatLt' x * posRatLt' y = Set.image2 (· * ·) (posRatLt' x) (posRatLt' y) := by rfl
  rw [csSup_le_iff (posRatLt'_bddAbove _) (posRatLt'_nonempty (mul_pos hx hy))]
  rw [posRatLt'_mul x hy, h, Set.forall_mem_image2]
  rw [← le_div_iff₀ (sup_posRatLt'_pos hy)]
  rw [csSup_le_iff (posRatLt'_bddAbove _) (posRatLt'_nonempty hx)]
  conv in ∀ x' ∈ posRatLt' x, x' ≤ c / sSup (posRatLt' y) =>
    intro x' hx'
    rw [le_div_iff₀ (sup_posRatLt'_pos hy), ← le_div_iff₀' (pos_of_mem_posRatLt' hx')]
    rw [csSup_le_iff (posRatLt'_bddAbove _) (posRatLt'_nonempty hy)]
    intro y' hy'
    rw [le_div_iff₀' (pos_of_mem_posRatLt' hx')]

theorem embedReal_mul (x y : M) : embedReal M (x * y) = embedReal M x * embedReal M y := by
  obtain hx | rfl | hx := lt_trichotomy 0 x
  · obtain hy | rfl | hy := lt_trichotomy 0 y
    · exact embedReal_mul_of_nonneg hx hy
    · simp
    · rw [show y = - -y by simp]
      rw [mul_neg, map_neg, map_neg, mul_neg _ (embedReal M (-y))]
      exact congrArg Neg.neg <| embedReal_mul_of_nonneg hx (by simpa using hy)
  · simp
  · rw [show x = - -x by simp]
    obtain hy | rfl | hy := lt_trichotomy 0 y
    · rw [neg_mul, map_neg, map_neg, neg_mul _ (embedReal M y)]
      exact congrArg Neg.neg <| embedReal_mul_of_nonneg (by simpa using hx) hy
    · simp
    · rw [show y = - -y by simp]
      rw [neg_mul_neg, map_neg _ (-x), map_neg _ (-y), neg_mul_neg (embedReal M (-x))]
      exact embedReal_mul_of_nonneg (by simpa using hx) (by simpa using hy)

variable (M) in
/-- `embedReal` as an `OrderRingHom`. -/
noncomputable
def embedRealOrderRingHom : M →+*o ℝ where
  __ := embedReal M
  map_one' := embedReal_one
  map_mul' := embedReal_mul

variable (M) in
theorem embedRealOrderRingHom_eq_embedReal : embedRealOrderRingHom M = embedReal M := rfl

variable (M) in
theorem embedRealOrderRingHom_injective : Function.Injective (embedRealOrderRingHom M) := by
  simpa [embedRealOrderRingHom_eq_embedReal] using embedReal_injective M

/-- For a field, the `embedRealOrderRingHom` we have constructed is the same as
`LinearOrderedField.inducedOrderRingHom`. -/
theorem embedRealOrderRingHom_eq_inducedOrderRingHom (M : Type*)
    [Field M] [LinearOrder M] [IsStrictOrderedRing M] [Archimedean M] :
    embedRealOrderRingHom M = LinearOrderedField.inducedOrderRingHom M ℝ :=
  Subsingleton.allEq _ _

end Archimedean
