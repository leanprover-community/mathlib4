/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
import Mathlib.Algebra.Order.Hom.Monoid
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Data.Real.Archimedean

/-!
# Embedding of archimedean groups into reals

This file provides embedding of any archimedean groups into reals.

## Main declarations
* `Archimedean.embedReal` defines an injective `M →+o ℝ` for archimedean group `M` with a positive
  `1` element. `1` is preserved by the map.
* `Archimedean.exists_orderAddMonoidHom_real_injective` states there exists an injective `M →+o ℝ`
  for any archimedean group `M` without specifying the `1` element in `M`.
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
    refine ⟨mkRat m (k * a.den), ?_, mkRat (k * a.num - m) (k * a.den), ?_, ?_⟩
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
  · push_neg at h
    obtain ⟨a, ha⟩ := exists_ne (0 : M)
    let one : One M := ⟨|a|⟩
    have : ZeroLEOneClass M := ⟨abs_nonneg a⟩
    have : NeZero (1 : M) := ⟨abs_ne_zero.mpr ha⟩
    exact ⟨embedReal M, embedReal_injective M⟩

end Archimedean
