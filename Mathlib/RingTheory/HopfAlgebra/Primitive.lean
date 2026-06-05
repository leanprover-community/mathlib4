/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.RingTheory.Bialgebra.Primitive
public import Mathlib.RingTheory.HopfAlgebra.Basic

/-!
# Primitive elements in a Hopf algebra

This file collects Hopf-algebra-side facts about primitive elements
(see `Mathlib.RingTheory.Bialgebra.Primitive` for the predicate).

## Main declarations

* `HopfAlgebra.antipode_of_isPrimitive` : the antipode sends primitive elements to their negation.
* `HopfAlgebra.ofPrimitives` : construct a Hopf algebra structure on a bialgebra
  generated as an algebra by primitive elements, given a candidate anti-algebra hom that
  sends each generator to its negation.
-/

public section

namespace HopfAlgebra

open Bialgebra Coalgebra LinearMap MulOpposite WithConv

universe u v

variable {R : Type u} {A : Type v} [CommSemiring R]

/-- The antipode of a Hopf algebra sends primitive elements to their negation. -/
theorem antipode_of_isPrimitive [Ring A] [HopfAlgebra R A] {a : A} (ha : IsPrimitiveElem R a) :
    antipode R a = -a := by
  have key := mul_antipode_rTensor_comul_apply (R := R) a
  rw [ha.comul_eq_tmul_one_add_one_tmul, ha.counit_eq_zero, map_add, rTensor_tmul,
    rTensor_tmul, antipode_one, map_add, mul'_apply, mul'_apply, mul_one, one_mul,
    map_zero] at key
  exact eq_neg_of_add_eq_zero_left key

/-- Construct a Hopf algebra structure on a bialgebra `A` that is generated as an algebra by
primitive elements. The candidate antipode `S : A →ₐ[R] Aᵐᵒᵖ` must send each generator `p` in a
primitive-generating set `s` to `op (-p)`; the antipode axioms then extend automatically. -/
noncomputable abbrev ofPrimitives [Ring A] [Bialgebra R A]
    (S : A →ₐ[R] Aᵐᵒᵖ) {s : Set A}
    (hs_gen : Algebra.adjoin R s = ⊤)
    (hs_prim : ∀ p ∈ s, IsPrimitiveElem R p)
    (hS : ∀ p ∈ s, S p = op (-p)) :
    HopfAlgebra R A := by
  set S₀ : A →ₗ[R] A := (opLinearEquiv R).symm.toLinearMap ∘ₗ S.toLinearMap with hS₀
  have hS₀_antihom : ∀ x y : A, S₀ (x * y) = S₀ y * S₀ x := fun x y => by simp [hS₀, map_mul]
  -- Verification of antipode axioms on primitive generators.
  have h_prim_r : ∀ p ∈ s, mul' R A (S₀.rTensor A (comul p)) =
      algebraMap R A (counit p) := fun p hp => by
    simp only [(hs_prim p hp).comul_eq_tmul_one_add_one_tmul, (hs_prim p hp).counit_eq_zero,
      hS p hp, hS₀, coe_opLinearEquiv_symm_toLinearMap,
      AlgHom.toLinearMap_apply, comp_apply, rTensor_tmul, mul'_apply,
      map_add, map_zero, map_one, unop_op, unop_one, mul_one, one_mul, neg_add_cancel]
  have h_prim_l : ∀ p ∈ s, mul' R A (S₀.lTensor A (comul p)) =
      algebraMap R A (counit p) := fun p hp => by
    simp only [(hs_prim p hp).comul_eq_tmul_one_add_one_tmul, (hs_prim p hp).counit_eq_zero,
      hS p hp, hS₀, coe_opLinearEquiv_symm_toLinearMap,
      AlgHom.toLinearMap_apply, comp_apply, lTensor_tmul, mul'_apply,
      map_add, map_zero, map_one, unop_op, unop_one, mul_one, one_mul, add_neg_cancel]
  refine HopfAlgebra.ofConvInverse S₀ ?_ ?_
  · -- `toConv S₀ * toConv id = 1` ↔ the pointwise `rTensor` antipode axiom; extend via adjoin
    -- induction.
    refine WithConv.ext (LinearMap.ext fun x => ?_)
    change mul' R A (S₀.rTensor A (comul x)) = algebraMap R A (counit x)
    refine Algebra.adjoin_induction h_prim_r (fun r => by simp [hS₀])
      (fun a b _ _ ha hb => by simp [map_add, ha, hb])
      (fun a b _ _ ha hb => ?_) (hs_gen ▸ Algebra.mem_top : x ∈ Algebra.adjoin R s)
    let ℛa := ℛ R a
    let ℛb := ℛ R b
    calc mul' R A (S₀.rTensor A (comul (a * b)))
        _ = ∑ p ∈ ℛa.index, ∑ q ∈ ℛb.index,
              S₀ (ℛa.left p * ℛb.left q) * (ℛa.right p * ℛb.right q) := by
          rw [comul_mul, ← ℛa.eq, ← ℛb.eq, Finset.sum_mul_sum]
          simp [Algebra.TensorProduct.tmul_mul_tmul]
        _ = ∑ p ∈ ℛa.index, ∑ q ∈ ℛb.index,
              S₀ (ℛb.left q) * (S₀ (ℛa.left p) * ℛa.right p) * ℛb.right q := by
          simp_rw [hS₀_antihom, mul_assoc]
        _ = ∑ q ∈ ℛb.index,
              algebraMap R A (counit a) * S₀ (ℛb.left q) * ℛb.right q := by
          have hu : ∑ p ∈ ℛa.index, S₀ (ℛa.left p) * ℛa.right p
                    = algebraMap R A (counit a) := by simpa [← ℛa.eq] using ha
          rw [Finset.sum_comm]
          simp_rw [← Finset.sum_mul, ← Finset.mul_sum, hu, ← Algebra.commutes]
        _ = algebraMap R A (counit a) *
              ∑ q ∈ ℛb.index, S₀ (ℛb.left q) * ℛb.right q := by
          simp_rw [Finset.mul_sum, mul_assoc]
        _ = algebraMap R A (counit a) * algebraMap R A (counit b) := by
          congr 1
          simpa [← ℛb.eq] using hb
        _ = algebraMap R A (counit (a * b)) := by
          rw [counit_mul, map_mul]
  · -- `toConv id * toConv S₀ = 1` ↔ the pointwise `lTensor` antipode axiom.
    refine WithConv.ext (LinearMap.ext fun x => ?_)
    change mul' R A (S₀.lTensor A (comul x)) = algebraMap R A (counit x)
    refine Algebra.adjoin_induction h_prim_l (fun r => by simp [hS₀])
      (fun a b _ _ ha hb => by simp [map_add, ha, hb])
      (fun a b _ _ ha hb => ?_) (hs_gen ▸ Algebra.mem_top : x ∈ Algebra.adjoin R s)
    let ℛa := ℛ R a
    let ℛb := ℛ R b
    calc mul' R A (S₀.lTensor A (comul (a * b)))
        _ = ∑ p ∈ ℛa.index, ∑ q ∈ ℛb.index,
              (ℛa.left p * ℛb.left q) * S₀ (ℛa.right p * ℛb.right q) := by
          rw [comul_mul, ← ℛa.eq, ← ℛb.eq, Finset.sum_mul_sum]
          simp [Algebra.TensorProduct.tmul_mul_tmul]
        _ = ∑ p ∈ ℛa.index, ∑ q ∈ ℛb.index,
              ℛa.left p * (ℛb.left q * S₀ (ℛb.right q)) * S₀ (ℛa.right p) := by
          simp_rw [hS₀_antihom, mul_assoc]
        _ = ∑ p ∈ ℛa.index,
              algebraMap R A (counit b) * ℛa.left p * S₀ (ℛa.right p) := by
          have hv : ∑ q ∈ ℛb.index, ℛb.left q * S₀ (ℛb.right q)
                    = algebraMap R A (counit b) := by simpa [← ℛb.eq] using hb
          simp_rw [← Finset.sum_mul, ← Finset.mul_sum, hv, ← Algebra.commutes]
        _ = algebraMap R A (counit b) *
              ∑ p ∈ ℛa.index, ℛa.left p * S₀ (ℛa.right p) := by
          simp_rw [Finset.mul_sum, mul_assoc]
        _ = algebraMap R A (counit b) * algebraMap R A (counit a) := by
          congr 1
          simpa [← ℛa.eq] using ha
        _ = algebraMap R A (counit (a * b)) := by
          rw [counit_mul, mul_comm (counit a) (counit b), map_mul]

end HopfAlgebra
