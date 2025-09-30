/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.GroupWithZero.Hom

/-! # Isomorphisms of monoids with zero -/

assert_not_exists Ring

namespace MulEquivClass
variable {F α β : Type*} [EquivLike F α β]

-- See note [lower instance priority]
instance (priority := 100) toZeroHomClass [MulZeroClass α] [MulZeroClass β] [MulEquivClass F α β] :
    ZeroHomClass F α β where
  map_zero f :=
    calc
      f 0 = f 0 * f (EquivLike.inv f 0) := by rw [← map_mul, zero_mul]
        _ = 0 := by simp

-- See note [lower instance priority]
instance (priority := 100) toMonoidWithZeroHomClass
    [MulZeroOneClass α] [MulZeroOneClass β] [MulEquivClass F α β] :
    MonoidWithZeroHomClass F α β :=
  { MulEquivClass.instMonoidHomClass F, MulEquivClass.toZeroHomClass with }

end MulEquivClass

namespace MulEquiv

variable {G H : Type*} [MulZeroOneClass G] [MulZeroOneClass H]

/-- An isomorphism of monoids with zero can be treated as a homomorphism preserving zero.
This is a helper projection that utilizes the `MonoidWithZeroHomClass` instance. -/
def toMonoidWithZeroHom (f : G ≃* H) : G →*₀ H := f

@[simp] lemma toMonoidWithZeroHom_apply (f : G ≃* H) (x : G) : f.toMonoidWithZeroHom x = f x := rfl

lemma toMonoidWithZeroHom_injective (f : G ≃* H) :
    Function.Injective f.toMonoidWithZeroHom :=
  f.injective

lemma toMonoidWithZeroHom_surjective (f : G ≃* H) :
    Function.Surjective f.toMonoidWithZeroHom :=
  f.surjective

lemma toMonoidWithZeroHom_bijective (f : G ≃* H) :
    Function.Bijective f.toMonoidWithZeroHom :=
  f.bijective

@[simp] lemma toMonoidWithZeroHom_inj {f g : G ≃* H} :
    f.toMonoidWithZeroHom = g.toMonoidWithZeroHom ↔ f = g := by
  simp [MonoidWithZeroHom.ext_iff, MulEquiv.ext_iff]

end MulEquiv
