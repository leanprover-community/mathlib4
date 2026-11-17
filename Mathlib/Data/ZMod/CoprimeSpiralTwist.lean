/-
Copyright (c) 2026 Qamar Munawer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qamar Munawer
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Linarith

/-!
# Coprime Spiral Bijections on `ZMod N`

This file studies the linear spiral homomorphism `spiralMap N k m = (k : ZMod N) * m` on
`ZMod N`. When `Nat.Coprime k N`, multiplication by `k` is a unit operation on `ZMod N`,
ensuring that every non-zero element `m ≠ 0` has non-zero coordinates in both components of
the spiral embedding `m ↦ (m, spiralMap N k m)`.

## Main results

* `CoprimeSpiralTwist.spiralMap_eq_zero_iff`: `spiralMap N k m = 0 ↔ m = 0` when `k` and
  `N` are coprime.
* `CoprimeSpiralTwist.spiralMap_bijective`: bijectivity of `spiralMap N k` for coprime
  `k, N`.
* `CoprimeSpiralTwist.spiral_both_coords_ne_zero`: for `m ≠ 0`, both `m ≠ 0` and
  `spiralMap N k m ≠ 0`.
-/

@[expose] public section

namespace CoprimeSpiralTwist

/-- The linear spiral multiplication map `m ↦ (k : ZMod N) * m` on `ZMod N`. -/
def spiralMap (N k : ℕ) (m : ZMod N) : ZMod N :=
  (k : ZMod N) * m

/-- When `k` and `N` are coprime, `(k : ZMod N)` is a unit in `ZMod N`. -/
theorem isUnit_coe_of_coprime {N k : ℕ} (h_coprime : Nat.Coprime k N) :
    IsUnit (k : ZMod N) := by
  have h_eq : ((ZMod.unitOfCoprime k h_coprime : (ZMod N)ˣ) : ZMod N) = (k : ZMod N) :=
    ZMod.coe_unitOfCoprime k h_coprime
  rw [← h_eq]
  exact Units.isUnit _

/-- Trivial kernel: if `Nat.Coprime k N`, then `spiralMap N k m = 0` if and only if `m = 0`. -/
theorem spiralMap_eq_zero_iff {N k : ℕ} (h_coprime : Nat.Coprime k N) (m : ZMod N) :
    spiralMap N k m = 0 ↔ m = 0 := by
  unfold spiralMap
  exact (isUnit_coe_of_coprime h_coprime).mul_right_eq_zero

/-- Every non-zero mode `m ≠ 0` has non-zero image under a coprime spiral map. -/
theorem spiralMap_ne_zero_of_ne_zero {N k : ℕ} (h_coprime : Nat.Coprime k N)
    {m : ZMod N} (hm : m ≠ 0) :
    spiralMap N k m ≠ 0 := by
  intro h_zero
  exact hm ((spiralMap_eq_zero_iff h_coprime m).mp h_zero)

/-- Simultaneous two-plane non-vanishing: for any `m ≠ 0` and `Nat.Coprime k N`, both
coordinates of the spiral pair `(m, spiralMap N k m)` are strictly non-zero in `ZMod N`. -/
theorem spiral_both_coords_ne_zero {N k : ℕ} (h_coprime : Nat.Coprime k N)
    {m : ZMod N} (hm : m ≠ 0) :
    m ≠ 0 ∧ spiralMap N k m ≠ 0 :=
  ⟨hm, spiralMap_ne_zero_of_ne_zero h_coprime hm⟩

/-- The coprime spiral map is a bijection on `ZMod N`. -/
theorem spiralMap_bijective {N k : ℕ} (h_coprime : Nat.Coprime k N) :
    Function.Bijective (spiralMap N k) := by
  unfold spiralMap
  let u : (ZMod N)ˣ := ZMod.unitOfCoprime k h_coprime
  have hu : (u : ZMod N) = (k : ZMod N) := ZMod.coe_unitOfCoprime k h_coprime
  rw [← hu, Function.bijective_iff_has_inverse]
  refine ⟨fun m => ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * m, ?_, ?_⟩
  · intro m
    calc
      ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * ((u : ZMod N) * m) =
          (((u⁻¹ * u : (ZMod N)ˣ) : ZMod N)) * m := by
        simp
      _ = m := by simp
  · intro m
    calc
      (u : ZMod N) * (((u⁻¹ : (ZMod N)ˣ) : ZMod N) * m) =
          (((u * u⁻¹ : (ZMod N)ˣ) : ZMod N)) * m := by
        simp
      _ = m := by simp

/-- Additive two-plane lower bound: if each non-trivial coordinate contributes at least `g` to
a quadratic form, any mode twisted in both planes satisfies `2 * g ≤ w₁ + w₂`. -/
theorem two_plane_gap_lower_bound {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] {g w₁ w₂ : F} (hw₁ : g ≤ w₁) (hw₂ : g ≤ w₂) :
    2 * g ≤ w₁ + w₂ := by
  linarith

end CoprimeSpiralTwist
