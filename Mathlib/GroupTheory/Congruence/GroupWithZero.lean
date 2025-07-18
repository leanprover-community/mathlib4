/-
Copyright (c) 2025 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/

import Mathlib.Algebra.GroupWithZero.InjSurj
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.GroupTheory.Congruence.Defs

/-!
# Quotients of monoids and groups with zeros by a congruence relation
-/

namespace Con

variable {M : Type*}

section Monoid

instance instZero [Zero M] [Mul M] (c : Con M) : Zero c.Quotient where
  zero := Quotient.mk'' (0 : M)

/-- The 0 of the quotient of a monoid with zero by a congruence relation is the equivalence class
of the original 0. -/
theorem coe_zero [Zero M] [Mul M] {c : Con M} : ((0 : M) : c.Quotient) = 0 :=
  rfl

instance instMulZeroClass [MulZeroClass M] (c : Con M) :
    MulZeroClass c.Quotient :=
  Function.Surjective.mulZeroClass _ Quotient.mk''_surjective rfl (fun _ _ => rfl)

instance instMulZeroOneClass [MulZeroOneClass M] (c : Con M) :
    MulZeroOneClass c.Quotient := fast_instance%
  Function.Surjective.mulZeroOneClass _ Quotient.mk''_surjective rfl rfl (fun _ _ => rfl)

instance instSemigroupWithZero [SemigroupWithZero M] (c : Con M) :
    SemigroupWithZero c.Quotient := fast_instance%
  Function.Surjective.semigroupWithZero _ Quotient.mk''_surjective rfl (fun _ _ => rfl)

instance instMonoidWithZero [MonoidWithZero M] (c : Con M) :
    MonoidWithZero c.Quotient := fast_instance%
  Function.Surjective.monoidWithZero _ Quotient.mk''_surjective rfl rfl
    (fun _ _ => rfl) (fun _ _ => rfl)

instance instCommMonoidWithZero [CommMonoidWithZero M] (c : Con M) :
    CommMonoidWithZero c.Quotient := fast_instance%
  Function.Surjective.commMonoidWithZero _ Quotient.mk''_surjective rfl rfl
    (fun _ _ => rfl) (fun _ _ => rfl)

/-- If zero is equivalent to some unit under a (multiplicative) congruence relation,
it is equivalent to any element. -/
theorem zero_of_isUnit [MonoidWithZero M] {c : Con M} {x : M} (h0 : c 0 x) (hx : IsUnit x)
    (y : M) : c 0 y := by
  rcases hx with ⟨u, rfl⟩
  simpa using c.mul h0 (c.refl ((u⁻¹ : Mˣ) * y))

end Monoid

section Group

variable [GroupWithZero M] (c : Con M)

protected theorem inv₀ {x y} (h : c x y) : c x⁻¹ y⁻¹ := by
  rcases eq_or_ne x 0 with rfl|hx <;>
  rcases eq_or_ne y 0 with rfl|hy
  · simpa using c.refl 0
  · simpa using c.zero_of_isUnit h hy.isUnit _
  · simpa using c.symm <| c.zero_of_isUnit (c.symm h) hx.isUnit _
  · simp only [← Con.eq] at *
    have cancel₁ (x : M) (hx : x ≠ 0) : (x : c.Quotient) * x⁻¹ = 1 := by
      simp [← Con.coe_mul, mul_inv_cancel₀ hx]
    have cancel₂ (x : M) (hx : x ≠ 0) : x⁻¹ * (x : c.Quotient) = 1 := by
      simp [← Con.coe_mul, inv_mul_cancel₀ hx]
    have : (⟨_, _, cancel₁ x hx, cancel₂ x hx⟩ : c.Quotientˣ) =
            ⟨_, _, cancel₁ y hy, cancel₂ y hy⟩ := Units.ext h
    exact congr_arg Units.inv this

protected theorem div₀ : ∀ {w x y z}, c w x → c y z → c (w / y) (x / z) := @fun w x y z h1 h2 => by
  simpa only [div_eq_mul_inv] using c.mul h1 (c.inv₀ h2)

protected theorem zpow₀ : ∀ (n : ℤ) {w x}, c w x → c (w ^ n) (x ^ n)
  | Int.ofNat n, w, x, h => by simpa only [zpow_natCast, Int.ofNat_eq_coe] using c.pow n h
  | Int.negSucc n, w, x, h => by simpa only [zpow_negSucc] using c.inv₀ (c.pow _ h)

instance instInv₀ : Inv c.Quotient :=
  ⟨(Quotient.map' Inv.inv) fun _ _ => c.inv₀⟩

instance instDiv₀ : Div c.Quotient :=
  ⟨(Quotient.map₂ (· / ·)) fun _ _ h₁ _ _ h₂ => c.div₀ h₁ h₂⟩

instance instZPow₀ : Pow c.Quotient ℤ :=
  ⟨fun x z => Quotient.map' (fun x => x ^ z) (fun _ _ h => c.zpow₀ z h) x⟩

instance instGroupWithZero [hc : Fact (c ≠ ⊤)] :
    GroupWithZero c.Quotient := fast_instance%
  Function.Surjective.groupWithZero zero_ne_one _ Quotient.mk''_surjective rfl rfl
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

instance instCommGroupWithZero {M : Type*} [CommGroupWithZero M] (c : Con M) [Fact (c ≠ ⊤)] :
    CommGroupWithZero c.Quotient where

end Group

end Con
