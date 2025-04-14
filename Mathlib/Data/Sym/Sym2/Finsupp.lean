/-
Copyright (c) 2025 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Finsupp.Defs

/-!
# Finitely supported functions from the symmetric square

This file lifts functions `α →₀ M₀` to functions `Sym2 α →₀ M₀` by precomposing with multiplication.
-/

open Sym2

variable {α M₀ : Type*} [CommMonoidWithZero M₀] {f : α →₀ M₀}

namespace Finsupp

lemma sym2_support_eq_preimage_support_mul [NoZeroDivisors M₀] (f : α →₀ M₀) :
    f.support.sym2 = map f ⁻¹' mul.support := by ext ⟨a, b⟩; simp

lemma mem_sym2_support_of_mul_ne_zero (p : Sym2 α) (hp : mul (p.map f) ≠ 0) :
    p ∈ f.support.sym2 := by
  obtain ⟨a, b⟩ := p
  simp only [map_pair_eq, mul_mk, ne_eq] at hp
  simpa using .intro (left_ne_zero_of_mul hp) (right_ne_zero_of_mul hp)

/-- The composition of a `Finsupp` with `Sym2.mul` as a `Finsupp`. -/
noncomputable def sym2Mul (f : α →₀ M₀) : Sym2 α →₀ M₀ :=
  .onFinset f.support.sym2 (fun p ↦ mul (p.map f)) mem_sym2_support_of_mul_ne_zero

lemma support_sym2Mul_subset : f.sym2Mul.support ⊆ f.support.sym2 := support_onFinset_subset

@[simp, norm_cast] lemma coe_sym2Mul (f : α →₀ M₀) : f.sym2Mul = mul ∘ map f := rfl

lemma sym2Mul_apply_mk (p : α × α) : f.sym2Mul (.mk p) = f p.1 * f p.2 := rfl

end Finsupp
