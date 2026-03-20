/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas

/-!
# Instances for the range submonoid of a monoid with zero hom
-/

@[expose] public section

assert_not_exists Ring

namespace MonoidWithZeroHom

variable {G H F : Type*}

instance [MulZeroOneClass G] [MulZeroOneClass H] [FunLike F G H] [MonoidWithZeroHomClass F G H]
    (f : F) : MulZeroOneClass (MonoidHom.mrange (f : G →* H)) where
  zero := ⟨0, 0, by simp⟩
  zero_mul _ := Subtype.ext (zero_mul _)
  mul_zero _ := Subtype.ext (mul_zero _)

@[simp]
lemma val_mrange_zero [MulZeroOneClass G] [MulZeroOneClass H] [FunLike F G H]
    [MonoidWithZeroHomClass F G H] (f : F) :
    ((0 : MonoidHom.mrange (f : G →* H)) : H) = 0 :=
  rfl

instance [MulZeroOneClass G] [MonoidWithZero H] [FunLike F G H]
    [MonoidWithZeroHomClass F G H] (f : F) :
    MonoidWithZero (MonoidHom.mrange (f : G →* H)) where

instance [MulZeroOneClass G] [CommMonoidWithZero H] [FunLike F G H]
    [MonoidWithZeroHomClass F G H] (f : F) :
    CommMonoidWithZero (MonoidHom.mrange (f : G →* H)) where

instance [GroupWithZero G] [GroupWithZero H] [FunLike F G H]
    [MonoidWithZeroHomClass F G H] (f : F) :
    GroupWithZero (MonoidHom.mrange (f : G →* H)) where
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

instance [GroupWithZero G] [CommGroupWithZero H] [FunLike F G H]
    [MonoidWithZeroHomClass F G H] (f : F) :
    CommGroupWithZero (MonoidHom.mrange (f : G →* H)) where

end MonoidWithZeroHom
