/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# Pointwise monoid structures on SubMulAction

This file provides `SubMulAction.Monoid` and weaker typeclasses, which show that `SubMulAction`s
inherit the same pointwise multiplications as sets.

To match `Submodule.idemSemiring`, we do not put these in the `Pointwise` locale.

-/


open Pointwise

variable {R M : Type*}

namespace SubMulAction

section One

variable [Monoid R] [MulAction R M] [One M]

instance : One (SubMulAction R M) where
  one :=
    { carrier := Set.range fun r : R => r • (1 : M)
      smul_mem' := fun r _ ⟨r', hr'⟩ => hr' ▸ ⟨r * r', mul_smul _ _ _⟩ }

theorem coe_one : ↑(1 : SubMulAction R M) = Set.range fun r : R => r • (1 : M) :=
  rfl

@[simp]
theorem mem_one {x : M} : x ∈ (1 : SubMulAction R M) ↔ ∃ r : R, r • (1 : M) = x :=
  Iff.rfl

theorem subset_coe_one : (1 : Set M) ⊆ (1 : SubMulAction R M) := fun _ hx =>
  ⟨1, (one_smul _ _).trans hx.symm⟩

end One

section Mul

variable [Monoid R] [MulAction R M] [Mul M] [IsScalarTower R M M]

instance : Mul (SubMulAction R M) where
  mul p q :=
    { carrier := Set.image2 (· * ·) p q
      smul_mem' := fun r _ ⟨m₁, hm₁, m₂, hm₂, h⟩ =>
        h ▸ smul_mul_assoc r m₁ m₂ ▸ Set.mul_mem_mul (p.smul_mem _ hm₁) hm₂ }

@[norm_cast]
theorem coe_mul (p q : SubMulAction R M) : ↑(p * q) = (p * q : Set M) :=
  rfl

theorem mem_mul {p q : SubMulAction R M} {x : M} : x ∈ p * q ↔ ∃ y ∈ p, ∃ z ∈ q, y * z = x :=
  Set.mem_mul

end Mul

section MulOneClass

variable [Monoid R] [MulAction R M] [MulOneClass M] [IsScalarTower R M M] [SMulCommClass R M M]

instance : MulOneClass (SubMulAction R M) where
  mul := (· * ·)
  one := 1
  mul_one a := by
    ext x
    simp only [mem_mul, mem_one, mul_smul_comm, exists_exists_eq_and, mul_one]
    constructor
    · rintro ⟨y, hy, r, rfl⟩
      exact smul_mem _ _ hy
    · intro hx
      exact ⟨x, hx, 1, one_smul _ _⟩
  one_mul a := by
    ext x
    simp only [mem_mul, mem_one, smul_mul_assoc, exists_exists_eq_and, one_mul]
    refine ⟨?_, fun hx => ⟨1, x, hx, one_smul _ _⟩⟩
    rintro ⟨r, y, hy, rfl⟩
    exact smul_mem _ _ hy

@[deprecated (since := "04-06-2025")] alias mulOneClass := instMulOneClass

end MulOneClass

section Semigroup

variable [Monoid R] [MulAction R M] [Semigroup M] [IsScalarTower R M M]

instance : Semigroup (SubMulAction R M) where
  mul := (· * ·)
  mul_assoc _ _ _ := SetLike.coe_injective (mul_assoc (_ : Set _) _ _)

@[deprecated (since := "04-06-2025")] alias semiGroup := instSemigroup

end Semigroup

section Monoid

variable [Monoid R] [MulAction R M] [Monoid M] [IsScalarTower R M M] [SMulCommClass R M M]

instance : Monoid (SubMulAction R M) := { }

theorem coe_pow (p : SubMulAction R M) : ∀ {n : ℕ} (_ : n ≠ 0), ↑(p ^ n) = (p : Set M) ^ n
  | 0, hn => (hn rfl).elim
  | 1, _ => by rw [pow_one, pow_one]
  | n + 2, _ => by
    rw [pow_succ _ (n + 1), pow_succ _ (n + 1), coe_mul, coe_pow _ n.succ_ne_zero]

theorem subset_coe_pow (p : SubMulAction R M) : ∀ {n : ℕ}, (p : Set M) ^ n ⊆ ↑(p ^ n)
  | 0 => by
    rw [pow_zero, pow_zero]
    exact subset_coe_one
  | n + 1 => by rw [← Nat.succ_eq_add_one, coe_pow _ n.succ_ne_zero]

end Monoid

end SubMulAction
