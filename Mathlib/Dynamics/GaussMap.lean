/-
Copyright (c) 2026 Tobias Weiss. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Weiss
-/
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Set.Basic
import Mathlib.Topology.Algebra.Ring.Real

/-!
# The Gauss map and its inverse branches

The Gauss map `T : (0, 1] → [0, 1)`, `T x = 1/x - ⌊1/x⌋`, generates the regular
continued-fraction expansion of a real number. We define it as the fractional
part of `1/x`, extended by `0` outside `(0, 1]` so that it becomes a
(self-)map of the real line, and we study its inverse branches
`Iₙ x = 1/(n + 1 + x)`.

The inverse branches map the unit interval onto the partition intervals
`[1/(n+2), 1/(n+1)]`. These intervals form a generating partition of `(0, 1]`,
the combinatorial backbone of the transfer-operator approach to the Selberg
zeta function.

## Main definitions

* `gaussMap`: the Gauss map `T x = 1/x - ⌊1/x⌋` on `(0, 1]`, extended by `0`
* `gaussInverseBranch n`: the `n`-th inverse branch `x ↦ 1 / (n + 1 + x)`

## Main statements

* `gaussMap_in_range`: the Gauss map takes values in `[0, 1]`
* `gaussInverseBranch_Icc_range`: the `n`-th inverse branch maps `[0, 1]`
  onto `[1/(n+2), 1/(n+1)]`
* `gaussInverseBranch_partition`: the closed branch images cover `(0, 1]`
* `gaussInverseBranch_disjoint`: distinct open branch images are disjoint
-/

open Set

/-- The Gauss map `T x = 1/x - ⌊1/x⌋` on `(0, 1]`, extended by `0` elsewhere. -/
noncomputable def gaussMap (x : ℝ) : ℝ :=
  if 0 < x ∧ x ≤ 1 then Int.fract (1 / x) else 0

/-- The `n`-th inverse branch of the Gauss map: `Iₙ x = 1/(n + 1 + x)`. -/
noncomputable def gaussInverseBranch (n : ℕ) : ℝ → ℝ := fun x => 1 / (n + 1 + x)

section Basic

variable {x : ℝ}

/-- On `(0, 1]` the Gauss map is the fractional part of `1/x`. -/
theorem gaussMap_eq (hx : 0 < x ∧ x ≤ 1) : gaussMap x = Int.fract (1 / x) := by
  simp [gaussMap, hx]

/-- The Gauss map is nonnegative. -/
theorem gaussMap_nonneg (x : ℝ) : 0 ≤ gaussMap x := by
  unfold gaussMap
  split
  · exact Int.fract_nonneg _
  · rfl

/-- The Gauss map takes values in `[0, 1]`. -/
theorem gaussMap_in_range (x : ℝ) : 0 ≤ gaussMap x ∧ gaussMap x ≤ 1 := by
  unfold gaussMap
  split
  · exact ⟨Int.fract_nonneg _, Int.fract_lt_one _ |>.le⟩
  · exact ⟨le_refl 0, zero_le_one⟩

/-- The Gauss map agrees with `1/x - ⌊1/x⌋` on `(0, 1]`. -/
theorem gaussMap_eq_sub_floor (hx : 0 < x ∧ x ≤ 1) : gaussMap x = 1 / x - ⌊1 / x⌋ := by
  rw [gaussMap_eq hx, Int.fract]

/-- The Gauss map of an inverse-branch image is the original point (on the
open interval `(0, 1)`; note `T 1 = 0`). -/
theorem gaussMap_gaussInverseBranch {n : ℕ} {x : ℝ} (hx : 0 < x ∧ x < 1) :
    gaussMap (gaussInverseBranch n x) = x := by
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hpos : (0 : ℝ) < n + 1 + x := by linarith
  have hle : (1 : ℝ) ≤ n + 1 + x := by linarith
  have htle : 1 / (n + 1 + x) ≤ 1 := by rw [div_le_one hpos]; exact hle
  have hfr : Int.fract (n + 1 + x) = Int.fract x :=
    Int.fract_eq_fract.2 ⟨(n : ℤ) + 1, by push_cast; ring⟩
  have hx0 : 0 < 1 / (n + 1 + x) := by
    have hden : (0:ℝ) < n + 1 + x := by linarith
    exact div_pos one_pos hden
  have hx1 : 1 / (n + 1 + x) ≤ 1 := by
    have h1 : (1:ℝ) ≤ n + 1 + x := by linarith
    have h2 : (0:ℝ) < n + 1 + x := by linarith
    exact (div_le_one h2).2 h1
  have hfr : Int.fract (n + 1 + x) = Int.fract x :=
    Int.fract_eq_fract.2 ⟨(n : ℤ) + 1, by push_cast; ring⟩
  change gaussMap (1 / (n + 1 + x)) = x
  rw [gaussMap_eq ⟨hx0, hx1⟩, one_div_one_div, hfr, Int.fract_eq_self.2 ⟨hx.1.le, hx.2⟩]

end Basic

section Branches

variable (n : ℕ)

/-- Each inverse branch is continuous away from its pole `x = -(n+1)`. -/
theorem gaussInverseBranch_continuousAt {x : ℝ} (hx : x ≠ -((n : ℝ) + 1)) :
    ContinuousAt (gaussInverseBranch n) x := by
  have hne : ((n : ℝ) + 1 + x) ≠ 0 := by
    intro h
    apply hx
    linarith
  have hcont : ContinuousAt (fun y : ℝ => (n : ℝ) + 1 + y) x :=
    continuousAt_const.add continuousAt_id
  have hfun : gaussInverseBranch n = fun y => ((n : ℝ) + 1 + y)⁻¹ := by
    funext y
    simp [gaussInverseBranch]
  rw [hfun]
  exact ContinuousAt.inv₀ hcont hne

/-- The inverse branch maps `[0, 1]` onto `[1/(n+2), 1/(n+1)]`. -/
theorem gaussInverseBranch_Icc_range :
    gaussInverseBranch n '' Icc (0 : ℝ) 1 = Icc (1 / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 1)) := by
  have hp1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hp2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_Icc] at hx ⊢
    have hpx : (0 : ℝ) < (n : ℝ) + 1 + x := by linarith
    exact ⟨(div_le_div_iff₀ hp2 hpx).2 (by linarith),
      (div_le_div_iff₀ hpx hp1).2 (by linarith)⟩
  · rintro ⟨hy0, hy1⟩
    have hypos : (0 : ℝ) < y := lt_of_lt_of_le (div_pos one_pos hp2) hy0
    refine ⟨1 / y - ((n : ℝ) + 1), ⟨?_, ?_⟩, ?_⟩
    · -- `0 ≤ 1/y - (n+1)` reduces to `(n+1) * y ≤ 1`
      rw [sub_nonneg, le_div_iff₀ hypos]
      exact (mul_le_mul_of_nonneg_left hy1 hp1.le).trans (mul_one_div_cancel (ne_of_gt hp1)).le
    · -- `1/y - (n+1) ≤ 1` reduces to `1 ≤ (n+2) * y`
      have key2 : (1 : ℝ) ≤ (n + 1 + 1) * y := by
        have h22 : ((n : ℝ) + 1 + 1) = (n : ℝ) + 2 := by ring
        rw [h22]
        have h := mul_le_mul_of_nonneg_left hy0 hp2.le
        rwa [mul_one_div_cancel (ne_of_gt hp2)] at h
      rw [sub_le_iff_le_add', div_le_iff₀ hypos]
      exact key2
    · -- the witness maps back to `y`
      have hden : (n : ℝ) + 1 + (1 / y - ((n : ℝ) + 1)) = 1 / y := by ring
      simp only [gaussInverseBranch]
      rw [hden, one_div_one_div]

/-- The closed branch images cover `(0, 1]`. -/
theorem gaussInverseBranch_partition :
    ⋃ n : ℕ, gaussInverseBranch n '' Icc (0 : ℝ) 1 = Ioc (0 : ℝ) 1 := by
  ext y
  simp only [mem_iUnion, mem_image, mem_Ioc]
  constructor
  · rintro ⟨n, x, ⟨hx0, hx1⟩, rfl⟩
    simp only [gaussInverseBranch]
    have hpx : (0 : ℝ) < (n : ℝ) + 1 + x := by linarith
    exact ⟨div_pos one_pos hpx, by rw [div_le_one hpx]; linarith⟩
  · rintro ⟨hy0, hy1⟩
    -- pick `n = ⌊1/y⌋₊ - 1`: then `n + 1 = ⌊1/y⌋₊ ≤ 1/y ≤ ⌊1/y⌋₊ + 1 = n + 2`
    have hu1 : (1 : ℝ) ≤ 1 / y := (one_le_div hy0).2 hy1
    have hk1 : 1 ≤ ⌊1 / y⌋₊ := (Nat.one_le_floor_iff _).2 hu1
    have hkle : ((⌊1 / y⌋₊ : ℕ) : ℝ) ≤ 1 / y := Nat.floor_le (one_div_pos.2 hy0).le
    have hklt : 1 / y < ((⌊1 / y⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
    have hrn1 : (((⌊1 / y⌋₊ - 1 : ℕ) : ℝ)) + 1 = ((⌊1 / y⌋₊ : ℕ) : ℝ) := by
      have hk0 : ⌊1 / y⌋₊ ≠ 0 := by omega
      have h := congrArg (Nat.cast (R := ℝ)) (Nat.sub_one_add_one hk0)
      rwa [Nat.cast_add_one] at h
    refine ⟨⌊1 / y⌋₊ - 1, 1 / y - (((⌊1 / y⌋₊ - 1 : ℕ) : ℝ) + 1), ⟨by linarith, by linarith⟩,
      ?_⟩
    have hden : ((⌊1 / y⌋₊ : ℕ) : ℝ) + (1 / y - ((⌊1 / y⌋₊ : ℕ) : ℝ)) = 1 / y := by ring
    simp only [gaussInverseBranch]
    rw [hrn1, hden, one_div_one_div]

/-- The images of the open unit interval under distinct inverse branches are
disjoint. (The closed branch images overlap at their endpoints — e.g. `1/2`
lies in both `I₀ '' [0,1]` and `I₁ '' [0,1]` — so disjointness is stated for
the interiors; equivalently, the half-open images `[1/(n+2), 1/(n+1))` form a
genuine partition of `(0, 1)`.) -/
theorem gaussInverseBranch_disjoint {n m : ℕ} (hnm : n ≠ m) :
    Disjoint (gaussInverseBranch n '' Ioo (0 : ℝ) 1) (gaussInverseBranch m '' Ioo (0 : ℝ) 1) := by
  rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
  rintro y ⟨⟨x, hx, hxe⟩, z, hz, hze⟩
  rw [mem_Ioo] at hx hz
  have hI : ∀ (k : ℕ) (w : ℝ), gaussInverseBranch k w = 1 / ((k:ℝ) + 1 + w) := fun _ _ => rfl
  have heq : (1:ℝ) / ((n:ℝ) + 1 + x) = (1:ℝ) / ((m:ℝ) + 1 + z) := by
    have h1 : (1:ℝ) / ((n:ℝ) + 1 + x) = y := by rw [← hI n x]; exact hxe
    have h2 : (1:ℝ) / ((m:ℝ) + 1 + z) = y := by rw [← hI m z]; exact hze
    exact h1.trans h2.symm
  have hnn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have hA : ((n : ℝ) + 1 + x) ≠ 0 := by linarith [hx.1.le]
  have hB : ((m : ℝ) + 1 + z) ≠ 0 := by linarith [hz.1.le]
  field_simp at heq
  rcases lt_or_gt_of_ne hnm with h | h
  · have hnm1 : (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
    linarith
  · have hnm1 : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
    linarith

end Branches
