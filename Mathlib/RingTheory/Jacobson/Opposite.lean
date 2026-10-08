/-
Copyright (c) 2022 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto, Jaehyeon Shin
-/
module

public import Mathlib.RingTheory.Jacobson.Radical

import Mathlib.Algebra.Group.Units.Opposite
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.Tactic.NoncommRing

/-!
# Left-right symmetry of the Jacobson radical

We characterize membership in the Jacobson radical by invertibility of `1 + a * x`
and `1 + x * a`, then use these criteria to prove `Ring.op_mem_jacobson`.
We also show that radical powers and nilpotence are preserved under taking opposites,
and construct the corresponding isomorphism of radical quotient rings.

The radical symmetry proof is adapted from Haruhisa Enomoto's Lean 3 formalization:
https://github.com/haruhisa-enomoto/lean-noncommutative-ring/blob/master/src/nc_jacobson_ideal.lean
-/

public section

namespace Ring

open MulOpposite

variable {R : Type*} [Ring R] {x : R}

/-- Membership in the Jacobson radical is detected by left inverses. -/
theorem mem_jacobson_iff_exists_left_inv :
    x ∈ jacobson R ↔ ∀ a : R, ∃ b : R, b * (1 + a * x) = 1 := by
  rw [← Ideal.jacobson_bot, Ideal.mem_jacobson_iff]
  simp only [Ideal.mem_bot, sub_eq_zero, mul_add, mul_one, mul_assoc, add_comm]

/-- The left inverses in the radical criterion are actually two-sided inverses. -/
theorem mem_jacobson_iff_isUnit_one_add_mul :
    x ∈ jacobson R ↔ ∀ a : R, IsUnit (1 + a * x) := by
  rw [mem_jacobson_iff_exists_left_inv]
  constructor
  · intro h a
    obtain ⟨b, hb⟩ := h a
    have heq : b = 1 + (-b * a) * x := by
      calc
        b = b * (1 + a * x) + (-b * a) * x := by noncomm_ring
        _ = 1 + (-b * a) * x := by rw [hb]
    obtain ⟨c, hc⟩ := h (-b * a)
    rw [← heq] at hc
    have hcb : c = 1 + a * x := by
      calc
        c = c * (b * (1 + a * x)) := by rw [hb, mul_one]
        _ = 1 + a * x := by rw [← mul_assoc, hc, one_mul]
    exact ⟨⟨1 + a * x, b, by rwa [hcb] at hc, hb⟩, rfl⟩
  · intro h a
    exact (h a).exists_left_inv

/-- Swapping the two factors in `1 + a * b` preserves invertibility. -/
private theorem isUnit_one_add_mul_swap {a b : R} (h : IsUnit (1 + a * b)) :
    IsUnit (1 + b * a) := by
  obtain ⟨u, hu⟩ := h
  have hl : (↑u⁻¹ : R) * (1 + a * b) = 1 := by rw [← hu]; exact u.inv_val
  have hr : (1 + a * b) * (↑u⁻¹ : R) = 1 := by rw [← hu]; exact u.val_inv
  refine ⟨⟨1 + b * a, 1 - b * ↑u⁻¹ * a, ?_, ?_⟩, rfl⟩
  · calc
      (1 + b * a) * (1 - b * ↑u⁻¹ * a) =
          1 + b * a - b * ((1 + a * b) * ↑u⁻¹) * a := by noncomm_ring
      _ = 1 := by rw [hr]; noncomm_ring
  · calc
      (1 - b * ↑u⁻¹ * a) * (1 + b * a) =
          1 + b * a - b * (↑u⁻¹ * (1 + a * b)) * a := by noncomm_ring
      _ = 1 := by rw [hl]; noncomm_ring

/-- The equivalent unit criterion with multiplication on the other side. -/
theorem mem_jacobson_iff_isUnit_one_add_mul' :
    x ∈ jacobson R ↔ ∀ a : R, IsUnit (1 + x * a) := by
  rw [mem_jacobson_iff_isUnit_one_add_mul]
  exact ⟨fun h a ↦ isUnit_one_add_mul_swap (h a),
    fun h a ↦ isUnit_one_add_mul_swap (h a)⟩

/-- The Jacobson radical is invariant under passage to the opposite ring. -/
@[simp]
theorem op_mem_jacobson :
    MulOpposite.op x ∈ jacobson Rᵐᵒᵖ ↔ x ∈ jacobson R := by
  rw [mem_jacobson_iff_isUnit_one_add_mul, mem_jacobson_iff_isUnit_one_add_mul']
  constructor
  · intro h a
    simpa using (h (MulOpposite.op a)).unop
  · intro h a
    simpa using (h a.unop).op

/-- Powers of the Jacobson radical are preserved by the opposite operation. -/
theorem op_mem_jacobson_pow (n : ℕ) (x : R) :
    op x ∈ jacobson Rᵐᵒᵖ ^ n ↔ x ∈ jacobson R ^ n := by
  induction n generalizing x with
  | zero => simp [Submodule.pow_zero, Ideal.one_eq_top]
  | succ n ih =>
    rw [Submodule.pow_succ, Ideal.IsTwoSided.pow_succ]
    constructor
    · intro hx
      change (op x).unop ∈ jacobson R * jacobson R ^ n
      refine Submodule.mul_induction_on hx (fun a ha b hb ↦ ?_) (fun a b ha hb ↦ ?_)
      · exact Ideal.mul_mem_mul (op_mem_jacobson.mp hb) ((ih a.unop).mp ha)
      · exact (jacobson R * jacobson R ^ n).add_mem ha hb
    · intro hx
      refine Submodule.mul_induction_on hx (fun a ha b hb ↦ ?_) (fun a b ha hb ↦ ?_)
      · exact Ideal.mul_mem_mul ((ih b).mpr hb) (op_mem_jacobson.mpr ha)
      · exact (jacobson Rᵐᵒᵖ ^ n * jacobson Rᵐᵒᵖ).add_mem ha hb

/-- Nilpotence of the Jacobson radical is left-right symmetric. -/
theorem isNilpotent_jacobson_op_iff :
    IsNilpotent (jacobson Rᵐᵒᵖ) ↔ IsNilpotent (jacobson R) := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, le_antisymm (fun x hx ↦ ?_) bot_le⟩
    have h := (op_mem_jacobson_pow n x).mpr hx
    rw [hn] at h
    simpa using h
  · rintro ⟨n, hn⟩
    refine ⟨n, le_antisymm (fun x hx ↦ ?_) bot_le⟩
    have h := (op_mem_jacobson_pow n x.unop).mp hx
    rw [hn] at h
    simpa using h

/-- Quotienting by the Jacobson radical commutes with taking the opposite ring. -/
noncomputable def jacobsonQuotientOpEquiv :
    (Rᵐᵒᵖ ⧸ jacobson Rᵐᵒᵖ) ≃+* (R ⧸ jacobson R)ᵐᵒᵖ := by
  let f := (Ideal.Quotient.mk (jacobson R)).op
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective y.unop
    exact ⟨op x, congrArg op hx⟩
  have hk : RingHom.ker f = jacobson Rᵐᵒᵖ := by
    ext x
    change op (Ideal.Quotient.mk (jacobson R) x.unop) = 0 ↔ _
    rw [op_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
    exact (op_mem_jacobson (x := x.unop)).symm
  exact (Ideal.quotEquivOfEq hk.symm).trans (RingHom.quotientKerEquivOfSurjective hf)

end Ring
