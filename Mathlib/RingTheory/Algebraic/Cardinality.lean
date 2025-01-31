/-
Copyright (c) 2022 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Algebra.Polynomial.Cardinal
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Algebraic.Defs

/-!
# Cardinality of algebraic extensions

This file contains results on cardinality of algebraic extensions.
-/


universe u v

open scoped Cardinal Polynomial

open Cardinal

namespace Algebra.IsAlgebraic

variable (R : Type u) [CommRing R] (L : Type v) [CommRing L] [IsDomain L] [Algebra R L]
variable [NoZeroSMulDivisors R L] [Algebra.IsAlgebraic R L]

theorem lift_cardinalMk_le_sigma_polynomial :
    lift.{u} #L ≤ #(Σ p : R[X], { x : L // x ∈ p.aroots L }) := by
  have := @lift_mk_le_lift_mk_of_injective L (Σ p : R[X], {x : L | x ∈ p.aroots L})
    (fun x : L =>
      let p := Classical.indefiniteDescription _ (Algebra.IsAlgebraic.isAlgebraic x)
      ⟨p.1, x, by
        dsimp
        have := (Polynomial.map_ne_zero_iff (FaithfulSMul.algebraMap_injective R L)).2 p.2.1
        rw [Polynomial.mem_roots this, Polynomial.IsRoot, Polynomial.eval_map,
          ← Polynomial.aeval_def, p.2.2]⟩)
    fun x y => by
      intro h
      simp only [Set.coe_setOf, ne_eq, Set.mem_setOf_eq, Sigma.mk.inj_iff] at h
      refine (Subtype.heq_iff_coe_eq ?_).1 h.2
      simp only [h.1, forall_true_iff]
  rwa [lift_umax, lift_id'.{v}] at this

theorem lift_cardinalMk_le_max : lift.{u} #L ≤ lift.{v} #R ⊔ ℵ₀ :=
  calc
    lift.{u} #L ≤ #(Σ p : R[X], { x : L // x ∈ p.aroots L }) :=
      lift_cardinalMk_le_sigma_polynomial R L
    _ = Cardinal.sum fun p : R[X] => #{x : L | x ∈ p.aroots L} := by
      rw [← mk_sigma]; rfl
    _ ≤ Cardinal.sum.{u, v} fun _ : R[X] => ℵ₀ :=
      (sum_le_sum _ _ fun _ => (Multiset.finite_toSet _).lt_aleph0.le)
    _ = lift.{v} #(R[X]) * ℵ₀ := by rw [sum_const, lift_aleph0]
    _ ≤ lift.{v} (#R ⊔ ℵ₀) ⊔ ℵ₀ ⊔ ℵ₀ := (mul_le_max _ _).trans <| by
      gcongr; simp only [lift_le, Polynomial.cardinalMk_le_max]
    _ = _ := by simp

variable (L : Type u) [CommRing L] [IsDomain L] [Algebra R L]
variable [NoZeroSMulDivisors R L] [Algebra.IsAlgebraic R L]

theorem cardinalMk_le_sigma_polynomial :
    #L ≤ #(Σ p : R[X], { x : L // x ∈ p.aroots L }) := by
  simpa only [lift_id] using lift_cardinalMk_le_sigma_polynomial R L

@[deprecated (since := "2024-11-10")]
alias cardinal_mk_le_sigma_polynomial := cardinalMk_le_sigma_polynomial

/-- The cardinality of an algebraic extension is at most the maximum of the cardinality
of the base ring or `ℵ₀`. -/
@[stacks 09GK]
theorem cardinalMk_le_max : #L ≤ max #R ℵ₀ := by
  simpa only [lift_id] using lift_cardinalMk_le_max R L

@[deprecated (since := "2024-11-10")] alias cardinal_mk_le_max := cardinalMk_le_max

end Algebra.IsAlgebraic
