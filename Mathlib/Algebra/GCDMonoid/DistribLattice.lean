/-
Copyright (c) 2026 Haoxiang Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haoxiang Yu
-/
module

public import Mathlib.Algebra.GCDMonoid.Basic
public import Mathlib.Order.Lattice

variable {α : Type*} [CommMonoidWithZero α] [GCDMonoid α]

local infixl:50 " ~ᵤ " => Associated

instance : Lattice (Associates α) :=
  { Associates.instPartialOrder with
    sup := GCDMonoid.lcm
    inf := GCDMonoid.gcd
    le_sup_left := dvd_lcm_left
    le_sup_right := dvd_lcm_right
    sup_le _ _ _ := lcm_dvd
    inf_le_left := gcd_dvd_left
    inf_le_right := gcd_dvd_right
    le_inf _ _ _ := dvd_gcd }

@[simp]
lemma gcd_mul_gcd' (a b x y : α) : gcd a b * gcd x y ~ᵤ gcd (gcd (a * x) (a * y)) (gcd (b * x) (b * y)) := by
  calc
    _ ~ᵤ gcd (a * gcd x y) (b * gcd x y) := (gcd_mul_right' (gcd x y) a b).symm
    _ ~ᵤ _ := ((gcd_mul_left' a x y).gcd (gcd_mul_left' b x y)).symm

instance : DistribLattice (Associates α) := DistribLattice.ofInfSupLe
  (by
    rintro ⟨x⟩ ⟨y⟩ ⟨z⟩
    change ⟦gcd x (lcm y z)⟧ ∣ ⟦lcm (gcd x y) (gcd x z)⟧
    rw [Associates.mk_dvd_mk]
    by_cases h : gcd (gcd x y) (gcd x z) = 0
    · simp only [gcd_eq_zero_iff] at h
      simp only [h, lcm_zero_right, gcd_zero_zero, dvd_refl]
    rw [
      ← mul_dvd_mul_iff_left h,
      (gcd_mul_lcm (gcd x y) (gcd x z)).dvd_iff_dvd_right,
      (gcd_mul_gcd' x y x z).dvd_iff_dvd_right,
      mul_comm x z,
    ]
    let w := gcd (gcd x y) (gcd x z)
    have wx : w ∣ x := (gcd_dvd_left (gcd x y) (gcd x z)).trans (gcd_dvd_left x y)
    have wy : w ∣ y := (gcd_dvd_left (gcd x y) (gcd x z)).trans (gcd_dvd_right x y)
    have wz : w ∣ z := (gcd_dvd_right (gcd x y) (gcd x z)).trans (gcd_dvd_right x z)
    have x' := gcd_dvd_left x (lcm y z)

    refine dvd_gcd (dvd_gcd (mul_dvd_mul wx x') (mul_dvd_mul wz x')) (dvd_gcd (mul_dvd_mul wy x') ?_)
    rw [← (gcd_mul_lcm y z).dvd_iff_dvd_right]
    exact mul_dvd_mul (dvd_gcd wy wz) <| gcd_dvd_right x (lcm y z))
