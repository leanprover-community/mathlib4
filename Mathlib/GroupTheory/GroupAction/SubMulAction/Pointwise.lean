/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module group_theory.group_action.sub_mul_action.pointwise
! leanprover-community/mathlib commit f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.GroupTheory.GroupAction.SubMulAction

/-!
# Pointwise monoid structures on sub_mul_action

This file provides `SubMulAction.Monoid` and weaker typeclasses, which show that `SubMulAction`s
inherit the same pointwise multiplications as sets.

To match `Submodule.Semiring`, we do not put these in the `Pointwise` locale.

-/


open Pointwise

variable {R M : Type _}

namespace SubMulAction

section One

variable [Monoid R] [MulAction R M] [One M]

instance : One (SubMulAction R M)
    where one :=
    { carrier := Set.range fun r : R => r • (1 : M)
      smul_mem' := fun r m ⟨r', hr'⟩ => hr' ▸ ⟨r * r', mul_smul _ _ _⟩ }

theorem coe_one : ↑(1 : SubMulAction R M) = Set.range fun r : R => r • (1 : M) :=
  rfl
#align sub_mul_action.coe_one SubMulAction.coe_one

@[simp]
theorem mem_one {x : M} : x ∈ (1 : SubMulAction R M) ↔ ∃ r : R, r • 1 = x :=
  Iff.rfl
#align sub_mul_action.mem_one SubMulAction.mem_one

theorem subset_coe_one : (1 : Set M) ⊆ (1 : SubMulAction R M) := fun x hx =>
  ⟨1, (one_smul _ _).trans hx.symm⟩
#align sub_mul_action.subset_coe_one SubMulAction.subset_coe_one

end One

section Mul

variable [Monoid R] [MulAction R M] [Mul M] [IsScalarTower R M M]

instance : Mul (SubMulAction R M)
    where mul p q :=
    { carrier := Set.image2 (· * ·) p q
      smul_mem' := fun r m ⟨m₁, m₂, hm₁, hm₂, h⟩ =>
        h ▸ smul_mul_assoc r m₁ m₂ ▸ Set.mul_mem_mul (p.smul_mem _ hm₁) hm₂ }

@[norm_cast]
theorem coe_mul (p q : SubMulAction R M) : ↑(p * q) = (p * q : Set M) :=
  rfl
#align sub_mul_action.coe_mul SubMulAction.coe_mul

theorem mem_mul {p q : SubMulAction R M} {x : M} : x ∈ p * q ↔ ∃ y z, y ∈ p ∧ z ∈ q ∧ y * z = x :=
  Set.mem_mul
#align sub_mul_action.mem_mul SubMulAction.mem_mul

end Mul

section MulOneClass

variable [Monoid R] [MulAction R M] [MulOneClass M] [IsScalarTower R M M] [SMulCommClass R M M]

instance : MulOneClass (SubMulAction R M)
    where
  mul := (· * ·)
  one := 1
  mul_one a := by
    ext
    simp only [mem_mul, mem_one, mul_smul_comm, exists_and_left, exists_exists_eq_and, mul_one]
    constructor
    · rintro ⟨y, hy, r, rfl⟩
      exact smul_mem _ _ hy
    · intro hx
      exact ⟨x, hx, 1, one_smul _ _⟩
  one_mul a := by
    ext
    simp only [mem_mul, mem_one, smul_mul_assoc, exists_and_left, exists_exists_eq_and, one_mul]
    refine' ⟨_, fun hx => ⟨1, x, hx, one_smul _ _⟩⟩
    rintro ⟨r, y, hy, rfl⟩
    exact smul_mem _ _ hy

end MulOneClass

section Semigroup

variable [Monoid R] [MulAction R M] [Semigroup M] [IsScalarTower R M M]

instance : Semigroup (SubMulAction R M)
    where
  mul := (· * ·)
  mul_assoc a b c := SetLike.coe_injective (mul_assoc (_ : Set _) _ _)

end Semigroup

section Monoid

variable [Monoid R] [MulAction R M] [Monoid M] [IsScalarTower R M M] [SMulCommClass R M M]

instance : Monoid (SubMulAction R M) :=
  { SubMulAction.semigroup,
    SubMulAction.mulOneClass with
    mul := (· * ·)
    one := 1 }

theorem coe_pow (p : SubMulAction R M) : ∀ {n : ℕ} (hn : n ≠ 0), ↑(p ^ n) = (p ^ n : Set M)
  | 0, hn => (hn rfl).elim
  | 1, hn => by rw [pow_one, pow_one]
  | n + 2, hn => by rw [pow_succ _ (n + 1), pow_succ _ (n + 1), coe_mul, coe_pow n.succ_ne_zero]
#align sub_mul_action.coe_pow SubMulAction.coe_pow

theorem subset_coe_pow (p : SubMulAction R M) : ∀ {n : ℕ}, (p ^ n : Set M) ⊆ ↑(p ^ n)
  | 0 => by
    rw [pow_zero, pow_zero]
    exact subset_coe_one
  | n + 1 => (coe_pow p n.succ_ne_zero).Superset
#align sub_mul_action.subset_coe_pow SubMulAction.subset_coe_pow

end Monoid

end SubMulAction
