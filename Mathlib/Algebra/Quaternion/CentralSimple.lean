/-
Copyright (c) 2026 Mathias Stout, Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mathias Stout, Justus Springer
-/
module

public import Mathlib.Algebra.Central.Defs
public import Mathlib.Algebra.Quaternion.Basic

import Mathlib.Tactic.LinearCombination

/-!
# Quaternion algebras are central simple

We show that the quaternion algebra `ℍ[R,a,b,c]` over a field `R` is a central simple
`R`-algebra, provided that `c * (b ^ 2 + 4 * a) ≠ 0`.

## Main results

* `QuaternionAlgebra.isCentral`: `ℍ[R,a,b,c]` is central if `b ^ 2 + 4 * a ≠ 0`,
* `QuaternionAlgebra.isSimpleRing`: `ℍ[R,a,b,c]` is simple if additionally `c ≠ 0`.

Together with `QuaternionAlgebra.finrank_eq_four`, this shows that `ℍ[R,a,b,c]` is a central
simple algebra of dimension four. Note that `b ^ 2 + 4 * a` is the discriminant of the minimal
polynomial `X ^ 2 - b * X - a` of `i`.

## Implementation notes

The local macro `quat_simp` is used throughout to simplify quaternion algebra expressions by
unfolding component-wise lemmas for `re`, `imI`, `imJ`, and `imK`.

-/

@[expose] public section

open Quaternion

namespace QuaternionAlgebra

variable {R : Type*} {a b c : R}

local macro "quat_simp" : tactic =>
  `(tactic| simp only [re_add, re_sub, re_mul, imI_add, imI_sub, imI_mul, imJ_add, imJ_sub,
    imJ_mul, imK_add, imK_sub, imK_mul, zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add,
    mul_one, one_mul, sub_zero, zero_sub, sub_self, sub_neg_eq_add])

/-- The quaternion algebra `ℍ[R,a,b,c]` is a central algebra over `R`
if `b ^ 2 + 4 * a ≠ 0`. -/
theorem isCentral [CommRing R] [IsDomain R] (h : b ^ 2 + 4 * a ≠ 0) :
    Algebra.IsCentral R ℍ[R,a,b,c] := by
  constructor
  rintro ⟨w, p, q, r⟩ hx
  rw [Subalgebra.mem_center_iff] at hx
  have hi := hx ⟨0, 1, 0, 0⟩
  have hj := hx ⟨0, 0, 1, 0⟩
  simp only [mk_mul_mk, zero_mul, mul_one, zero_add, mul_zero, add_zero, sub_zero, one_mul,
    zero_sub, mk.injEq, true_and, sub_self, add_eq_left] at hi hj
  obtain ⟨hi₁, hi₂⟩ := hi
  obtain ⟨-, -, hj₁, hj₂⟩ := hj
  suffices H : p = 0 ∧ q = 0 ∧ r = 0 by simpa only [H] using ⟨w, rfl⟩
  split_ands <;> refine (mul_eq_zero.mp ?_).resolve_left h
  · linear_combination b * hj₁ - 2 * a * hj₂
  · linear_combination -b * hi₁ + 2 * a * hi₂
  · linear_combination b * hi₂ + 2 * hi₁

variable [Field R]

private lemma eq_top_of_mem_re {I : TwoSidedIdeal ℍ[R,a,b,c]} (x : ℍ[R,a,b,c]) (hxI : x ∈ I)
    (re_x : x.re ≠ 0) (imI_x : x.imI = 0) (imJ_x : x.imJ = 0) (imK_x : x.imK = 0) : I = ⊤ :=
  I.eq_top_of_isUnit_mem hxI <|
    isUnit_of_isUnit_re x (isUnit_iff_ne_zero.mpr re_x) imI_x imJ_x imK_x

private lemma eq_top_of_mem_imJ_imK (hc : c ≠ 0) (h : b ^ 2 + 4 * a ≠ 0)
    {I : TwoSidedIdeal ℍ[R,a,b,c]} (x : ℍ[R,a,b,c]) (hxI : x ∈ I) (hx : x ≠ 0) (hx₁ : x.re = 0)
    (hx₂ : x.imI = 0) : I = ⊤ := by
  let y : ℍ[R,a,b,c] := ⟨0, 0, 1, 0⟩ * x + x * ⟨0, 0, 1, 0⟩
  have hy₁ : y.re = (x.imJ + b * x.imK + x.imJ) * c := by unfold y; quat_simp; ring
  by_cases H : x.imJ + b * x.imK + x.imJ = 0
  · let z : ℍ[R,a,b,c] := ⟨0, 1, 0, 0⟩ * x - x * ⟨0, 1, 0, 0⟩
    have hz₃ : z.imJ = a * x.4 * 2 - b * x.3 := by unfold z; quat_simp; ring
    have hz₄ : z.imK = 0 := by unfold z; quat_simp; exact H
    by_cases H' : a * x.4 * 2 - b * x.3 = 0
    · contrapose! hx
      exact QuaternionAlgebra.ext hx₁ hx₂
        ((mul_eq_zero_iff_left h).mp <| by linear_combination -b * H' + 2 * a * H)
        ((mul_eq_zero_iff_left h).mp <| by linear_combination 2 * H' + b * H)
    · apply eq_top_of_mem_re (⟨0, 0, 1, 0⟩ * z)
        (I.mul_mem_left _ z (I.sub_mem (I.mul_mem_left _ _ hxI) (I.mul_mem_right _ _ hxI)))
        (by simpa [hz₃, hz₄] using ⟨hc, H'⟩) <;> simp [z, hz₄]
  · apply eq_top_of_mem_re y (I.add_mem (I.mul_mem_left _ _ hxI) (I.mul_mem_right _ _ hxI))
      (hy₁ ▸ mul_ne_zero H hc) <;> simp [y, hx₁, hx₂]

/-- The quaternion algebra `ℍ[R,a,b,c]` is a simple ring if `c ≠ 0` and
`b ^ 2 + 4 * a ≠ 0`. -/
theorem isSimpleRing (hc : c ≠ 0) (h : b ^ 2 + 4 * a ≠ 0) : IsSimpleRing ℍ[R,a,b,c] := by
  apply IsSimpleRing.of_eq_bot_or_eq_top
  intro I
  rw [or_iff_not_imp_left]
  intro hI
  obtain ⟨x, hxI, hx⟩ := TwoSidedIdeal.exists_mem_ne_zero_of_ne_bot _ hI
  let y : ℍ[R,a,b,c] := ⟨0, 1, 0, 0⟩ * x - x * ⟨0, 1, 0, 0⟩
  have hy₃ : y.3 = 2 * a * x.4 - b * x.3 := by unfold y; quat_simp; ring
  have hy₄ : y.4 = x.3 * 2 + b * x.4 := by unfold y; quat_simp; ring
  have hyI : y ∈ I := I.sub_mem (I.mul_mem_left _ _ hxI) (I.mul_mem_right _ _ hxI)
  by_cases H : y = 0
  · simp only [H, imJ_zero, imK_zero] at hy₃ hy₄
    have hx₃ : x.3 = 0 := (mul_eq_zero_iff_left h).mp <| by linear_combination b * hy₃ - 2 * a * hy₄
    have hx₄ : x.4 = 0 := (mul_eq_zero_iff_left h).mp <| by linear_combination -2 * hy₃ - b * hy₄
    by_cases hx₂ : x.2 = 0
    · exact eq_top_of_mem_re x hxI (fun H ↦ hx (QuaternionAlgebra.ext H hx₂ hx₃ hx₄)) hx₂ hx₃ hx₄
    · let z : ℍ[R,a,b,c] := ⟨0, 0, 1, 0⟩ * x - x * ⟨0, 0, 1, 0⟩
      have hzI : z ∈ I := I.sub_mem (I.mul_mem_left _ _ hxI) (I.mul_mem_right _ _ hxI)
      have hz₃ : z.3 = b * x.2 := by unfold z; quat_simp; ring
      have hz₄ : z.4 = -2 * x.2 := by unfold z; quat_simp; ring
      by_cases hz : z = 0
      · simp only [hz, imJ_zero, imK_zero] at hz₃ hz₄
        have hx₂ : x.2 = 0 := (mul_eq_zero_iff_left h).mp <| by
          linear_combination -b * hz₃ + 2 * a * hz₄
        exact eq_top_of_mem_re x hxI (fun H ↦ hx (QuaternionAlgebra.ext H hx₂ hx₃ hx₄)) hx₂ hx₃ hx₄
      · apply eq_top_of_mem_imJ_imK hc h z hzI hz <;> simp [z, hx₃, hx₄]
  · apply eq_top_of_mem_imJ_imK hc h y hyI H <;> (unfold y; quat_simp)

end QuaternionAlgebra
