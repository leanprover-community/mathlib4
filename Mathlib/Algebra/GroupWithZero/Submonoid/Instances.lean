/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/

import Mathlib.Algebra.Group.Submonoid.Operations
import Mathlib.Algebra.GroupWithZero.Units.Lemmas

/-!
# Instances for the range submonoid of a monoid with zero hom
-/

assert_not_exists Ring

namespace MonoidWithZeroHom

variable {G H : Type*}

instance [MulZeroOneClass G] [MulZeroOneClass H] (f : G →*₀ H) :
    MulZeroOneClass (MonoidHom.mrange f) where
  zero := ⟨0, 0, by simp⟩
  zero_mul _ := Subtype.ext (zero_mul _)
  mul_zero _ := Subtype.ext (mul_zero _)

@[simp]
lemma val_mrange_zero [MulZeroOneClass G] [MulZeroOneClass H] (f : G →*₀ H) :
    ((0 : MonoidHom.mrange f) : H) = 0 :=
  rfl

instance [MulZeroOneClass G] [MonoidWithZero H] (f : G →*₀ H) :
    MonoidWithZero (MonoidHom.mrange f) where

instance [MulZeroOneClass G] [CommMonoidWithZero H] (f : G →*₀ H) :
    CommMonoidWithZero (MonoidHom.mrange f) where

instance [GroupWithZero G] [GroupWithZero H] (f : G →*₀ H) :
    GroupWithZero (MonoidHom.mrange f) where
  inv := fun x ↦ ⟨x⁻¹, by
    obtain ⟨y, hy⟩ := x.prop
    use y⁻¹
    simp [← hy]⟩
  exists_pair_ne := ⟨⟨f 0, 0, rfl⟩, ⟨f 1, by simp [- map_one]⟩, by simp⟩
  inv_zero := Subtype.ext inv_zero
  mul_inv_cancel := by
    rintro ⟨a, ha⟩ h
    simp only [ne_eq, Subtype.ext_iff] at h
    simpa using mul_inv_cancel₀ h

instance [GroupWithZero G] [CommGroupWithZero H] (f : G →*₀ H) :
    CommGroupWithZero (MonoidHom.mrange f) where

end MonoidWithZeroHom
