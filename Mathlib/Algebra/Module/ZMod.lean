/-
Copyright (c) 2023 Lawrence Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lawrence Wu
-/
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Data.ZMod.Basic

/-!
# The `ZMod n`-module structure on Abelian groups whose elements have order dividing `n`
-/

namespace AddCommMonoid

/-- A type synonym for a commutative monoid whose elements have order dividing `n`. -/
@[nolint unusedArguments]
def toZModModule (M : Type*) [AddCommMonoid M] (n : ℕ) (_ : ∀ x : M, n • x = 0) := M

variable {M : Type*} [AddCommMonoid M] {n : ℕ} {h : ∀ x : M, n • x = 0}


variable (n h) in
/-- Convert an element of `m` to an element of `toZModModule M n h`. -/
def toZModModule.of (m : M) : toZModModule M n h := m

/-- Convert an element of `toZModModule M n h` to an element of `M`. -/
def toZModModule.to (m : toZModModule M n h) : M := m

instance : AddCommMonoid (toZModModule M n h) :=
  inferInstanceAs (AddCommMonoid M)

theorem toZModModule.smul_eq_zero (x : toZModModule M n h) : n • x = 0 :=
  h x

variable (h) in
/-- The `ZMod n`-module structure on commutative monoids whose elements have order dividing `n ≠ 0`.
Also implies a group structure via `Module.addCommMonoidToAddCommGroup`.
See note [reducible non-instances]. -/
instance zmodModule [NeZero n] : Module (ZMod n) (toZModModule M n h) := by
  have h_mod (c : ℕ) (x : M) : (c % n) • x = c • x := by
    suffices (c % n + c / n * n) • x = c • x by rwa [add_nsmul, mul_nsmul, h, add_zero] at this
    rw [Nat.mod_add_div']
  have := NeZero.ne n
  match n with
  | n + 1 => exact {
    smul := fun (c : Fin _) x ↦ c.val • x
    smul_zero := fun _ ↦ nsmul_zero _
    zero_smul := fun _ ↦ zero_nsmul _
    smul_add := fun _ _ _ ↦ nsmul_add _ _ _
    one_smul := fun _ ↦ (h_mod _ _).trans <| one_nsmul _
    add_smul := fun _ _ _ ↦ (h_mod _ _).trans <| add_nsmul _ _ _
    mul_smul := fun _ _ _ ↦ (h_mod _ _).trans <| mul_nsmul' _ _ _
  }

end AddCommMonoid

namespace AddCommGroup

open AddCommMonoid

variable {G : Type*} [AddCommGroup G] {n : ℕ} {h : ∀ g : G, n • g = 0}

instance : AddCommGroup (toZModModule G n h) :=
  inferInstanceAs (AddCommGroup G)

/-- The `ZMod n`-module structure on Abelian groups whose elements have order dividing `n`.
See note [reducible non-instances]. -/
instance zmodModule : Module (ZMod n) (toZModModule G n h) :=
  match n with
  | 0 => AddCommGroup.toIntModule G
  | _ + 1 => AddCommMonoid.zmodModule h

theorem toZModModule.coe_smul (k : ℤ) (g : toZModModule G n h) : (k : ZMod n) • g = k • g :=
  match n with
  | 0 => rfl
  | m + 1 => by
    have H := (k.mod_modEq (m + 1 : ℕ)).of_dvd
      (Int.natCast_dvd_natCast.mpr (addOrderOf_dvd_iff_nsmul_eq_zero.mpr (h g)))
    rwa [← zsmul_eq_zsmul_iff_modEq, ← ZMod.val_intCast, Nat.cast_smul_eq_nsmul] at H

end AddCommGroup

namespace CommGroup

/-- A type synonym for a commutative groups whose elements have order dividing `n`. -/
@[nolint unusedArguments]
def toZModModule (G : Type*) [CommGroup G] (n : ℕ) (_ : ∀ g : G, g ^ n = 1) := G

variable {G : Type*} [CommGroup G] {n : ℕ} {h : ∀ g : G, g ^ n = 1}

instance : CommGroup (toZModModule G n h) :=
  inferInstanceAs (CommGroup G)

instance : MulDistribMulAction (ZMod n) (toZModModule G n h) :=
  { smul m a := m • AddCommMonoid.toZModModule.of n h (Additive.ofMul a)
    one_smul a := one_smul (ZMod n) (AddCommMonoid.toZModModule.of n h (Additive.ofMul a))
    mul_smul m m' a := mul_smul m m' (AddCommMonoid.toZModModule.of n h (Additive.ofMul a))
    smul_mul m a b := smul_add m (AddCommMonoid.toZModModule.of n h (Additive.ofMul a))
      (AddCommMonoid.toZModModule.of n h (Additive.ofMul b))
    smul_one m := smul_zero (A := AddCommMonoid.toZModModule (Additive G) n h) m }

theorem toZModModule.coe_smul (k : ℤ) (g : toZModModule G n h) : (k : ZMod n) • g = g ^ k :=
  AddCommGroup.toZModModule.coe_smul (G := Additive G) k g

theorem toZModModule.zero_smul (g : toZModModule G n h) : (0 : ZMod n) • g = 1 :=
  _root_.zero_smul (M := AddCommMonoid.toZModModule (Additive G) n h) (ZMod n) g

theorem toZModModule.neg_smul (k : ZMod n) (g : toZModModule G n h) : -k • g = (k • g)⁻¹ :=
  _root_.neg_smul (M := AddCommMonoid.toZModModule (Additive G) n h) k g

theorem toZModModule.add_smul (k m : ZMod n) (g : toZModModule G n h) :
    (k + m) • g = k • g * m • g :=
  _root_.add_smul (M := AddCommMonoid.toZModModule (Additive G) n h) k m g

theorem toZModModule.sub_smul (k m : ZMod n) (g : toZModModule G n h) :
    (k - m) • g = k • g / m • g :=
  _root_.sub_smul (M := AddCommMonoid.toZModModule (Additive G) n h) k m g

end CommGroup

variable {n : ℕ} {M M₁ : Type*}

/-- A type synonym for a commutative quotient groups whose elements have order dividing `n`. -/
def QuotientAddGroup.toZModModule {G : Type*} [AddCommGroup G] {H : AddSubgroup G}
    (_ : ∀ x, n • x ∈ H) := G ⧸ H

instance {G : Type*} [AddCommGroup G] {H : AddSubgroup G} (hH : ∀ x, n • x ∈ H) :
    AddCommMonoid (QuotientAddGroup.toZModModule hH) :=
  inferInstanceAs (AddCommMonoid (G ⧸ H))

/-- The quotient of an abelian group by a subgroup containing all multiples of `n` is a
`n`-torsion group. -/
-- See note [reducible non-instances]
instance QuotientAddGroup.zmodModule {G : Type*} [AddCommGroup G] {H : AddSubgroup G}
    (hH : ∀ x, n • x ∈ H) : Module (ZMod n) (QuotientAddGroup.toZModModule hH) :=
  AddCommGroup.zmodModule (h := by simpa [forall_mk, ← mk_nsmul])

variable {F S : Type*} [AddCommGroup M] [AddCommGroup M₁] [FunLike F M M₁]
  [AddMonoidHomClass F M M₁] [Module (ZMod n) M] [Module (ZMod n) M₁] [SetLike S M]
  [AddSubgroupClass S M] {x : M} {K : S}

namespace ZMod

theorem map_smul (f : F) (c : ZMod n) (x : M) : f (c • x) = c • f x := by
  rw [← ZMod.intCast_zmod_cast c]
  exact map_intCast_smul f _ _ (cast c) x

theorem smul_mem (hx : x ∈ K) (c : ZMod n) : c • x ∈ K := by
  rw [← ZMod.intCast_zmod_cast c, Int.cast_smul_eq_zsmul]
  exact zsmul_mem hx (cast c)

end ZMod

variable (n)

namespace AddMonoidHom

/-- Reinterpret an additive homomorphism as a `ℤ/nℤ`-linear map.

See also:
`AddMonoidHom.toIntLinearMap`, `AddMonoidHom.toNatLinearMap`, `AddMonoidHom.toRatLinearMap` -/
def toZModLinearMap (f : M →+ M₁) : M →ₗ[ZMod n] M₁ := { f with map_smul' := ZMod.map_smul f }

theorem toZModLinearMap_injective : Function.Injective <| toZModLinearMap n (M := M) (M₁ := M₁) :=
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

@[simp] lemma coe_toZModSubmodule (S : AddSubgroup M) : (toZModSubmodule n S : Set M) = S := rfl
@[simp] lemma mem_toZModSubmodule {S : AddSubgroup M} : x ∈ toZModSubmodule n S ↔ x ∈ S := .rfl

@[simp]
theorem toZModSubmodule_toAddSubgroup (S : AddSubgroup M) :
    (toZModSubmodule n S).toAddSubgroup = S :=
  rfl

@[simp]
theorem _root_.Submodule.toAddSubgroup_toZModSubmodule (S : Submodule (ZMod n) M) :
    toZModSubmodule n S.toAddSubgroup = S :=
  rfl

end AddSubgroup
