/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/

import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
import Mathlib.Algebra.Order.Hom.Monoid
import Mathlib.Algebra.Order.Module.OrderedSMul
import Mathlib.Tactic.Qify

/-!
# Embedding of archimedean groups into reals

This file provides embedding of any archimedean groups into reals.

## Main declarations
* `orderAddMonoidHom_real_of_pos` defines a `M →+o ℝ` for archimedean group `M`
  that maps a given positive element to the real number 1.
* `exists_orderAddMonoidHom_real_injective` states there exists an injective `M →+o ℝ`
  for any archimedean group `M`.
-/


theorem Rat.mkRat_add_mkRat_of_den (n₁ n₂ : Int) {d : Nat} (z : d ≠ 0)  :
    mkRat n₁ d + mkRat n₂ d = mkRat (n₁ + n₂) d := by
  rw [Rat.mkRat_add_mkRat _ _ z z, ← add_mul, Rat.mkRat_mul_right z]

namespace Archimedean

variable {M : Type*}
variable [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

/-- Set of rational numbers that are less than the "number" `x / one`. Formally,
 these are numbers `p / q` such that `p • one < q • x`. -/
abbrev ratLt (one x : M) : Set ℚ := {r | r.num • one < r.den • x}

theorem mkRat_mem_ratLt {num : ℤ} {den : ℕ} (hden: den ≠ 0) {one x : M} :
    mkRat num den ∈ ratLt one x ↔ num • one < den • x := by
  rw [Set.mem_setOf]
  obtain ⟨m, hm0, hnum, hden⟩ := Rat.mkRat_num_den hden (show mkRat num den = _ by rfl)
  have hnum : num = (mkRat num den).num * m := hnum
  have hden : den = (mkRat num den).den * m := hden
  conv in num • one => rw [hnum, mul_comm, ← smul_smul, natCast_zsmul]
  conv in den • x => rw [hden, mul_comm, ← smul_smul]
  exact (smul_lt_smul_iff_of_pos_left (Nat.zero_lt_of_ne_zero hm0)).symm

/-- `ratLt` as a set of real numbers. -/
abbrev ratLt' (one x : M) : Set ℝ := (Rat.castHom ℝ) '' (ratLt one x)

/-- Mapping `M` to `ℝ`, defined as the supremum of `ratLt' one x`. -/
noncomputable
abbrev embed_real (one : M) (x : M) := sSup (ratLt' one x)

variable [Archimedean M]

theorem ratLt_bddAbove {one : M} (hpos : 0 < one) (x : M) : BddAbove (ratLt one x) := by
  obtain ⟨n, hn⟩ := Archimedean.arch x hpos
  use Rat.ofInt n
  rw [ratLt, mem_upperBounds]
  intro ⟨num, den, _, _⟩
  rw [Rat.le_iff]
  suffices num • one < den • x → num ≤ n * den by simpa using this
  intro h
  refine le_of_smul_le_smul_right (h.le.trans ?_) hpos
  rw [mul_comm, ← smul_smul]
  simpa using nsmul_le_nsmul_right hn den

theorem ratLt_nonempty {one : M} (hpos : 0 < one) (x : M) : (ratLt one x).Nonempty := by
  obtain hneg | rfl | hxpos := lt_trichotomy x 0
  · obtain ⟨n, hn⟩ := Archimedean.arch (-x - x) hpos
    use Rat.ofInt (-n)
    suffices -(n • one) < x by simpa using this
    refine neg_lt.mpr (lt_of_lt_of_le ?_ hn)
    simpa using hneg
  · exact ⟨Rat.ofInt (-1), by simpa using hpos⟩
  · obtain ⟨n, hn⟩ := Archimedean.arch one hxpos
    use Rat.mk' 1 (n + 1) (by simp) (by simp)
    simpa using hn.trans_lt <| (nsmul_lt_nsmul_iff_left hxpos).mpr (by simp)

open Pointwise in
theorem ratLt_add {one : M} (hpos : 0 < one) (x y : M) :
    ratLt one (x + y) = ratLt one x + ratLt one y := by
  ext a
  rw [Set.mem_add]
  constructor
  · /- Given `a ∈ ratLt one (x + y)`, find `u ∈ ratLt one x`, `v ∈ ratLt one y`
       such that `u + v = a`.
       In a naive attempt, one can take the denominator `d` of `a`,
       and find the largest `u = p / d < x / one`
       However, `d` could be too "coarse", and `v = a - u` could be 1/d too large than `y / one`
       To ensure a large enough denominator, we take `d * k`, where
       `one + one ≤ k • (d • (x + y) - a.num • one)` -/
    intro h
    rw [Set.mem_setOf_eq] at h
    have : 0 < a.den • (x + y) - a.num • one := sub_pos.mpr h
    obtain ⟨k, hk⟩ := Archimedean.arch (one + one) this
    have hk0 : k ≠ 0 := by
      contrapose! hk
      rw [hk]
      simpa using hpos
    have hka0 : k * a.den ≠ 0 := mul_ne_zero hk0 a.den_ne_zero
    obtain ⟨m, ⟨hm1, hm2⟩, _⟩ := existsUnique_add_zsmul_mem_Ico hpos 0 (k • a.den • x - one)
    refine ⟨mkRat m (k * a.den), ?_, mkRat (k * a.num - m) (k * a.den) , ?_, ?_⟩
    · rw [mkRat_mem_ratLt hka0, ← smul_smul]
      simpa using hm2
    · have hk' : one + (k • a.num • one - k • a.den • y) ≤ k • a.den • x - one := by
        rw [smul_add, smul_sub, smul_add] at hk
        rw [le_sub_iff_add_le, ← sub_le_iff_le_add] at hk
        rw [le_sub_iff_add_le]
        convert hk using 1
        abel
      have h : one + (k • a.num • one - k • a.den • y) ≤ m • one := by
        simpa using hk'.trans hm1
      have : k • a.num • one - k • a.den • y < m • one := by
        exact lt_of_lt_of_le (lt_add_of_pos_left _ hpos) h
      rw [mkRat_mem_ratLt hka0, sub_smul, sub_lt_comm, ← smul_smul, ← smul_smul, natCast_zsmul]
      exact this
    · rw [Rat.mkRat_add_mkRat_of_den _ _ hka0]
      rw [add_sub_cancel, Rat.mkRat_mul_left hk0, Rat.mkRat_num_den']
  · intro ⟨u, hu, v, hv, huv⟩
    rw [← huv]
    rw [Set.mem_setOf_eq] at hu hv ⊢
    have hu' : (u.num * v.den) • one < (u.den * v.den: ℤ) • x := by
      rw [mul_comm u.num, mul_comm (u.den : ℤ)]
      rw [← smul_smul, ← smul_smul]
      exact zsmul_lt_zsmul_right (by simpa using v.den_pos) (by simpa using hu)
    have hv' : (v.num * u.den) • one < (u.den * v.den: ℤ) • y := by
      rw [mul_comm]
      rw [← smul_smul, ← smul_smul]
      apply zsmul_lt_zsmul_right (by simpa using u.den_pos) (by simpa using hv)
    suffices ((u + v).num * u.den * v.den) • one <
        ((u + v).den : ℤ) • (u.den * v.den : ℤ) • (x + y) by
      rw [mul_assoc, mul_comm, zsmul_comm, ← smul_smul] at this
      rw [smul_lt_smul_iff_of_pos_left
        (mul_pos (by simpa using u.den_pos) (by simpa using v.den_pos))] at this
      simpa using this
    rw [Rat.add_num_den']
    rw [mul_comm, ←smul_smul]
    rw [smul_lt_smul_iff_of_pos_left (by simpa using (u + v).den_pos)]
    rw [add_smul, smul_add]
    apply add_lt_add hu' hv'

theorem ratLt'_bddAbove {one : M} (hpos : 0 < one) (x : M) : BddAbove (ratLt' one x) := by
  refine Monotone.map_bddAbove ?_ ?_
  · exact Rat.cast_mono
  · exact ratLt_bddAbove hpos x

theorem ratLt'_nonempty {one : M} (hpos : 0 < one) (x : M): (ratLt' one x).Nonempty := by
  apply Set.image_nonempty.mpr (ratLt_nonempty hpos x)

open Pointwise in
theorem ratLt'_add {one : M} (hpos : 0 < one) (x y : M) :
    ratLt' one (x + y) = ratLt' one x + ratLt' one y := by
  unfold ratLt'
  rw [ratLt_add hpos, Set.image_add]

theorem embed_real_zero {one : M} (hpos: 0 < one) : embed_real one 0 = 0 := by
  apply le_antisymm
  · apply csSup_le (ratLt'_nonempty hpos 0)
    intro x
    unfold ratLt' ratLt
    suffices ∀ (y : ℚ), y.num • one < 0 → y = x → x ≤ 0 by simpa using this
    intro y hy hyx
    have hynum : y.num < 0 := by
      contrapose! hy
      exact smul_nonneg hy hpos.le
    rw [← hyx]
    simpa using (Rat.num_neg.mp hynum).le
  · rw [le_csSup_iff (ratLt'_bddAbove hpos 0) (ratLt'_nonempty hpos 0)]
    intro x
    rw [mem_upperBounds]
    suffices (∀ (y : ℚ), y.num • one < 0 → y ≤ x) → 0 ≤ x by simpa using this
    intro h
    have h' (y : ℚ) (hy: y < 0) : y ≤ x := by
      exact h _ <| (smul_neg_iff_of_neg_left (by simpa using hy)).mpr hpos
    contrapose! h'
    obtain ⟨y, hxy, hy⟩ := exists_rat_btwn h'
    exact ⟨y, by simpa using hy, hxy⟩

theorem embed_real_add {one : M} (hpos: 0 < one) (x y : M) :
    embed_real one (x + y) = embed_real one x + embed_real one y := by
  unfold embed_real
  rw [ratLt'_add hpos]
  rw [csSup_add (ratLt'_nonempty hpos x) (ratLt'_bddAbove hpos x)
    (ratLt'_nonempty hpos y) (ratLt'_bddAbove hpos y)]

theorem embed_real_strictMono {one : M} (hpos: 0 < one) : StrictMono (embed_real one) := by
  intro x y h
  have hyz : 0 < y - x := sub_pos.mpr h
  have hy : y = y - x + x := (sub_add_cancel y x).symm
  apply lt_of_sub_pos
  rw [hy, embed_real_add hpos, add_sub_cancel_right]
  obtain ⟨n, hn⟩ := Archimedean.arch one hyz
  have : (Rat.mk' 1 (n + 1) (by simp) (by simp) : ℝ) ∈ ratLt' one (y - x) := by
    simpa using hn.trans_lt <| nsmul_lt_nsmul_left hyz (show n < n + 1 by simp)
  apply lt_csSup_of_lt (ratLt'_bddAbove hpos (y - x)) this
  rw [Rat.cast_pos, ← Rat.num_pos]
  simp only [zero_lt_one]

/-- The bundled `M →+o ℝ` for archimedean `M`.
The given element `one` is mapped to the real number 1. -/
noncomputable
def orderAddMonoidHom_real_of_pos {one : M} (hpos: 0 < one) : M →+o ℝ where
  toFun := embed_real one
  map_zero' := embed_real_zero hpos
  map_add' := embed_real_add hpos
  monotone' := (embed_real_strictMono hpos).monotone

theorem orderAddMonoidHom_real_apply {one : M} (hpos: 0 < one) (a : M):
    (orderAddMonoidHom_real_of_pos hpos) a = embed_real one a := by rfl

theorem orderAddMonoidHom_real_injective_of_pos {one : M} (hpos: 0 < one) :
    Function.Injective (orderAddMonoidHom_real_of_pos hpos) :=
  (embed_real_strictMono hpos).injective

theorem orderAddMonoidHom_real_one {one : M} (hpos: 0 < one) :
    (orderAddMonoidHom_real_of_pos hpos) one = 1 := by
  rw [orderAddMonoidHom_real_apply]
  apply le_antisymm
  · apply csSup_le (ratLt'_nonempty hpos one)
    suffices ∀ (x : ℚ), x.num • one < (x.den : ℤ) • one → (x : ℝ) ≤ 1 by simpa using this
    intro x hx
    suffices x ≤ 1 by norm_cast
    rw [Rat.le_iff]
    simpa using ((smul_lt_smul_iff_of_pos_right hpos).mp hx).le
  · rw [le_csSup_iff (ratLt'_bddAbove hpos one) (ratLt'_nonempty hpos one)]
    simp_rw [mem_upperBounds]
    suffices ∀ (x : ℝ), (∀ (y : ℚ), y.num • one < (y.den : ℤ) • one → y ≤ x) → 1 ≤ x by
      simpa using this
    intro x h
    have h' (y : ℚ) (hy : y < 1) : y ≤ x := by
      refine h _ ((smul_lt_smul_iff_of_pos_right hpos).mpr ?_)
      simpa using (Rat.lt_iff _ _).mp hy
    contrapose! h'
    obtain ⟨y, hxy, hy⟩ := exists_rat_btwn h'
    norm_cast at hy
    refine ⟨y, hy, hxy⟩

variable (M) in
theorem exists_orderAddMonoidHom_real_injective :
    ∃ f : M →+o ℝ, Function.Injective f := by
  by_cases h : Subsingleton M
  · exact ⟨0, Function.injective_of_subsingleton _⟩
  · have : Nontrivial M := not_subsingleton_iff_nontrivial.mp h
    obtain ⟨a, ha⟩ := exists_ne (0 : M)
    have ha : 0 < |a| := by simpa using ha
    exact ⟨orderAddMonoidHom_real_of_pos ha, orderAddMonoidHom_real_injective_of_pos ha⟩

end Archimedean
