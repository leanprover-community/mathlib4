/-
Copyright (c) 2023 Lawrence Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lawrence Wu
-/
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.GroupTheory.Sylow

/-!
# The `ZMod n`-module structure on Abelian groups whose elements have order dividing `n`
-/

assert_not_exists TwoSidedIdeal

variable {n : ℕ} {M M₁ : Type*}

/-- The `ZMod n`-module structure on commutative monoids whose elements have order dividing `n ≠ 0`.
Also implies a group structure via `Module.addCommMonoidToAddCommGroup`.
See note [reducible non-instances]. -/
abbrev AddCommMonoid.zmodModule [NeZero n] [AddCommMonoid M] (h : ∀ (x : M), n • x = 0) :
    Module (ZMod n) M := by
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

/-- The `ZMod n`-module structure on Abelian groups whose elements have order dividing `n`.
See note [reducible non-instances]. -/
abbrev AddCommGroup.zmodModule {G : Type*} [AddCommGroup G] (h : ∀ (x : G), n • x = 0) :
    Module (ZMod n) G :=
  match n with
  | 0 => AddCommGroup.toIntModule G
  | _ + 1 => AddCommMonoid.zmodModule h

/-- The quotient of an abelian group by a subgroup containing all multiples of `n` is a
`n`-torsion group. -/
-- See note [reducible non-instances]
abbrev QuotientAddGroup.zmodModule {G : Type*} [AddCommGroup G] {H : AddSubgroup G}
    (hH : ∀ x, n • x ∈ H) : Module (ZMod n) (G ⧸ H) :=
  AddCommGroup.zmodModule <| by simpa [QuotientAddGroup.forall_mk, ← QuotientAddGroup.mk_nsmul]

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

/-- `AddMonoidHom.toZModLinearMap` as an equivalence. -/
def toZModLinearMapEquiv : (M →+ M₁) ≃+ (M →ₗ[ZMod n] M₁) where
  toFun f := f.toZModLinearMap n
  invFun g := g
  map_add' f₁ f₂ := by ext; simp

end AddMonoidHom

namespace AddSubgroup

/-- Reinterpret an additive subgroup of a `ℤ/nℤ`-module as a `ℤ/nℤ`-submodule.

See also: `AddSubgroup.toIntSubmodule`, `AddSubmonoid.toNatSubmodule`. -/
def toZModSubmodule : AddSubgroup M ≃o Submodule (ZMod n) M where
  toFun S := { S with smul_mem' := fun c _ h ↦ ZMod.smul_mem (K := S) h c }
  invFun := Submodule.toAddSubgroup
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

namespace ZModModule
variable {p : ℕ} {G : Type*} [AddCommGroup G]

/-- In an elementary abelian `p`-group, every finite subgroup `H` contains a further subgroup of
cardinality between `k` and `p * k`, if `k ≤ |H|`. -/
lemma exists_submodule_subset_card_le (hp : p.Prime) [Module (ZMod p) G]
    (H : Submodule (ZMod p) G) {k : ℕ} (hk : k ≤ Nat.card H) (h'k : k ≠ 0) :
    ∃ H' : Submodule (ZMod p) G, Nat.card H' ≤ k ∧ k < p * Nat.card H' ∧ H' ≤ H := by
  obtain ⟨H'm, H'mHm, H'mk, kH'm⟩ := Sylow.exists_subgroup_le_card_le
    (H := AddSubgroup.toSubgroup ((AddSubgroup.toZModSubmodule _).symm H)) hp
      isPGroup_multiplicative hk h'k
  exact ⟨AddSubgroup.toZModSubmodule _ (AddSubgroup.toSubgroup.symm H'm), H'mk, kH'm, H'mHm⟩

end ZModModule
