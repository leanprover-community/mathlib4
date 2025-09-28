/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Analysis.RCLike.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Topology.Algebra.Valued.ValuedField
import Mathlib.Topology.Algebra.Valued.WithVal
import Mathlib.Topology.GDelta.MetrizableSpace

/-!
# Equivalence between `ℚ_[p]` and `(Rat.padicValuation p).Completion`

The `p`-adic numbers are isomorphic as a field to the completion of the rationals at the
`p`-adic valuation. This is implemented via `Valuation.Completion` using `Rat.padicValuation`,
which is shorthand for `UniformSpace.Completion (WithVal (Rat.padicValuation p))`.

## Main definitions

* `Padic.withValRingEquiv`: the field isomorphism between
  `(Rat.padicValuation p).Completion` and `ℚ_[p]`
* `Padic.withValUniformEquiv`: the uniform space isomorphism between
  `(Rat.padicValuation p).Completion` and `ℚ_[p]`

-/

namespace Padic

variable {p : ℕ} [Fact p.Prime]

open NNReal WithZero UniformSpace

lemma isUniformInducing_cast_withVal : IsUniformInducing ((Rat.castHom ℚ_[p]).comp
    (WithVal.equiv (Rat.padicValuation p)).toRingHom) := by
  have hp0' : 0 < (p : ℚ) := by simp [Nat.Prime.pos Fact.out]
  have hp0 : 0 < (p : ℝ)⁻¹ := by simp [Nat.Prime.pos Fact.out]
  have hp1' : 1 < (p : ℚ) := by simp [Nat.Prime.one_lt Fact.out]
  have hp1 : (p : ℝ)⁻¹ < 1 := by simp [inv_lt_one_iff₀, Nat.Prime.one_lt Fact.out]
  rw [Filter.HasBasis.isUniformInducing_iff (Valued.hasBasis_uniformity _ _)
    (Metric.uniformity_basis_dist_le_pow hp0 hp1)]
  simp only [Set.mem_setOf_eq, dist_eq_norm_sub, inv_pow, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_comp, Rat.coe_castHom, RingHom.coe_coe, Function.comp_apply, ← Rat.cast_sub,
    ← map_sub, Padic.eq_padicNorm, true_and, forall_const]
  constructor
  · intro n
    use Units.mk0 (exp (-n : ℤ)) (by simp)
    intro x y h
    set x' : ℚ := (WithVal.equiv (Rat.padicValuation p)) x with hx
    set y' : ℚ := (WithVal.equiv (Rat.padicValuation p)) y with hy
    rw [Valuation.map_sub_swap, Units.val_mk0] at h
    change Rat.padicValuation p (x' - y') < exp _ at h
    rw [← Nat.cast_pow, ← Rat.cast_natCast, ← Rat.cast_inv_of_ne_zero, Rat.cast_le]
    · rw [map_sub, ← hx, ← hy]
      simp only [Rat.padicValuation, Valuation.coe_mk, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
        padicNorm, zpow_neg, Nat.cast_pow] at h ⊢
      split_ifs with H
      · simp
      · simp only [H, ↓reduceIte, exp_lt_exp, neg_lt_neg_iff] at h
        simpa [hp0', zpow_pos, pow_pos, inv_le_inv₀] using
          zpow_right_mono₀ (a := (p : ℚ)) (by exact_mod_cast (Nat.Prime.one_le Fact.out)) h.le
    · simp [Nat.Prime.ne_zero Fact.out]
  · intro γ
    use (log (γ.val * exp (- 1))).natAbs
    intro x y h
    set x' : ℚ := (WithVal.equiv (Rat.padicValuation p)) x with hx
    set y' : ℚ := (WithVal.equiv (Rat.padicValuation p)) y with hy
    rw [Valuation.map_sub_swap]
    change Rat.padicValuation p (x' - y') < γ
    rw [← Nat.cast_pow, ← Rat.cast_natCast, ← Rat.cast_inv_of_ne_zero, Rat.cast_le] at h
    · change padicNorm p (x' - y') ≤ _ at h
      simp only [Rat.padicValuation, Valuation.coe_mk, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
        padicNorm, zpow_neg, Nat.cast_pow] at h ⊢
      split_ifs with H
      · simp
      · rw [← lt_log_iff_exp_lt (by simp)]
        simp_all [← zpow_natCast, zpow_pos, inv_le_inv₀, zpow_le_zpow_iff_right₀ hp1', abs_le,
          Int.lt_iff_add_one_le]
    · simp [Nat.Prime.ne_zero Fact.out]

lemma isDenseInducing_cast_withVal : IsDenseInducing ((Rat.castHom ℚ_[p]).comp
    (WithVal.equiv (Rat.padicValuation p)).toRingHom) := by
  refine Padic.isUniformInducing_cast_withVal.isDenseInducing ?_
  intro
  -- nhds_discrete causes timeouts on TC search
  simpa [-nhds_discrete] using Padic.denseRange_ratCast p _

open Completion in
open scoped Valued in
/-- The `p`-adic numbers are isomorphic as a field to the completion of the rationals at
the `p`-adic valuation. -/
noncomputable
def withValRingEquiv :
    (Rat.padicValuation p).Completion ≃+* ℚ_[p] where
  toFun := (extensionHom ((Rat.castHom ℚ_[p]).comp (WithVal.equiv (Rat.padicValuation p)).toRingHom)
    Padic.isUniformInducing_cast_withVal.uniformContinuous.continuous)
  invFun := Padic.isDenseInducing_cast_withVal.extend coe'
  left_inv y := by
    induction y using induction_on
    · generalize_proofs _ _ _ H
      refine isClosed_eq ?_ continuous_id
      exact (uniformContinuous_uniformly_extend Padic.isUniformInducing_cast_withVal
        (Padic.denseRange_ratCast p) (uniformContinuous_coe _)).continuous.comp
        (continuous_extension)
    · rw [extensionHom_coe]
      apply IsDenseInducing.extend_eq
      exact continuous_coe _
  right_inv y := by
    induction y using isClosed_property (Padic.denseRange_ratCast p)
    · refine isClosed_eq ?_ continuous_id
      refine continuous_extension.comp ?_
      exact (uniformContinuous_uniformly_extend Padic.isUniformInducing_cast_withVal
        (Padic.denseRange_ratCast p) (uniformContinuous_coe _)).continuous
    · have : ∀ q : ℚ, Padic.isDenseInducing_cast_withVal.extend coe' q = coe'
        ((WithVal.equiv (Rat.padicValuation p)).symm q) := by
        intro q
        apply IsDenseInducing.extend_eq
        exact continuous_coe _
      rw [this, extensionHom_coe]
      simp
  map_mul' := map_mul _
  map_add' := map_add _


@[simp]
lemma coe_withValRingEquiv :
    ⇑(Padic.withValRingEquiv (p := p)) = Completion.extension
      ((↑) ∘ (WithVal.equiv (Rat.padicValuation p))) :=
  rfl

@[simp]
lemma coe_withValRingEquiv_symm :
    ⇑(Padic.withValRingEquiv (p := p)).symm =
      Padic.isDenseInducing_cast_withVal.extend Completion.coe' := by
  rfl

/-- The `p`-adic numbers are isomophic as uniform spaces to the completion of the rationals at
the `p`-adic valuation. -/
noncomputable
def withValUniformEquiv :
    (Rat.padicValuation p).Completion ≃ᵤ ℚ_[p] :=
  UniformEquiv.symm <| Padic.withValRingEquiv.symm.toUniformEquivOfIsUniformInducing <|
    isDenseInducing_cast_withVal.isUniformInducing_extend isUniformInducing_cast_withVal
      (Completion.isUniformInducing_coe _)

@[simp]
lemma toEquiv_withValUniformEquiv_eq_toEquiv_withValRingEquiv :
    (withValUniformEquiv (p := p) : (Rat.padicValuation p).Completion ≃ ℚ_[p]) =
      (withValRingEquiv (p := p) :) :=
  rfl

end Padic
