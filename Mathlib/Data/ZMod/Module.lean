/-
Copyright (c) 2023 Lawrence Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lawrence Wu
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.LinearMap

/-!
# The `ZMod n`-module structure on Abelian groups whose elements have order dividing `n`
-/

variable {n : ℕ} {M M₁ F S : Type*} [AddCommGroup M] [AddCommGroup M₁] [AddMonoidHomClass F M M₁]
  [Module (ZMod n) M] [Module (ZMod n) M₁] [SetLike S M] [AddSubgroupClass S M] {x : M} {K : S}

namespace ZMod

theorem map_smul (f : F) (c : ZMod n) (x : M) : f (c • x) = c • f x := by
  rw [← ZMod.int_cast_zmod_cast c]
  exact map_int_cast_smul f _ _ c x

theorem smul_mem (hx : x ∈ K) (c : ZMod n) : c • x ∈ K := by
  rw [← ZMod.int_cast_zmod_cast c, ← zsmul_eq_smul_cast]
  exact zsmul_mem hx c

end ZMod

variable (n)

namespace AddMonoidHom

/-- Reinterpret an additive homomorphism as a `ℤ/nℤ`-linear map.

See also:
`AddMonoidHom.toIntLinearMap`, `AddMonoidHom.toNatLinearMap`, `AddMonoidHom.toRatLinearMap` -/
def toZModLinearMap (f : M →+ M₁) : M →ₗ[ZMod n] M₁ := { f with map_smul' := ZMod.map_smul f }

theorem toZModLinearMap_injective: Function.Injective <| toZModLinearMap n (M := M) (M₁ := M₁) :=
  fun _ _ h ↦ ext fun x ↦ congr($h x)

@[simp]
theorem coe_toZModLinearMap (f : M →+ M₁) : ⇑(f.toZModLinearMap n) = f := rfl

end AddMonoidHom

namespace AddSubgroup

/-- Reinterpret an additive subgroup of a `ℤ/nℤ`-module as a `ℤ/nℤ`-submodule.

See also: `AddSubgroup.toIntSubmodule`, `AddSubmonoid.toNatSubmodule`. -/
def toZModSubmodule : AddSubgroup M ≃o Submodule (ZMod n) M where
  toFun S := { S with smul_mem' := fun c _ h ↦ ZMod.smul_mem (K := S) h c }
  invFun := Submodule.toAddSubgroup
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

@[simp]
theorem toZModSubmodule_symm :
    ⇑((toZModSubmodule n).symm : _ ≃o AddSubgroup M) = Submodule.toAddSubgroup :=
  rfl

@[simp]
theorem coe_toZModSubmodule (S : AddSubgroup M) : (toZModSubmodule n S : Set M) = S :=
  rfl

@[simp]
theorem toZModSubmodule_toAddSubgroup (S : AddSubgroup M) :
    (toZModSubmodule n S).toAddSubgroup = S :=
  rfl

@[simp]
theorem _root_.Submodule.toAddSubgroup_toZModSubmodule (S : Submodule (ZMod n) M) :
    toZModSubmodule n S.toAddSubgroup = S :=
  rfl

end AddSubgroup
