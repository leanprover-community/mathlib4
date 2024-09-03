/-
Copyright (c) 2023 Yaël Dilies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dilies
-/
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Discrete L2 inner product of finite sequences

This file defines the discrete L2 inner product of functions `f g : ι → R` where `ι` is a fintype as
`∑ i, conj (f i) * g i`. This convention (conjugation on the left) matches the inner product coming
from `RCLike.innerProductSpace`.
-/

open Finset Function Real
open scoped ComplexConjugate ENNReal NNReal NNRat

variable {ι R S : Type*} [Fintype ι]

namespace MeasureTheory
section CommSemiring
variable [CommSemiring R] [StarRing R] [DistribSMul S R]

/-- Inner product giving rise to the discrete L2 norm. -/
def dL2Inner (f g : ι → R) : R := ∑ i, conj (f i) * g i

@[inherit_doc] notation "⟪" f ", " g "⟫_[" S "]" => dL2Inner (R := S) f g

lemma dL2Inner_eq_sum (f g : ι → R) : ⟪f, g⟫_[R] = ∑ i, conj (f i) * g i := rfl

@[simp] lemma conj_dL2Inner (f g : ι → R) : conj ⟪f, g⟫_[R] = ⟪conj f, conj g⟫_[R] := by
  simp [dL2Inner_eq_sum, map_sum]

lemma dL2Inner_anticomm (f g : ι → R) : ⟪f, g⟫_[R] = ⟪conj g, conj f⟫_[R] := by
  simp [dL2Inner_eq_sum, map_sum, mul_comm]

@[simp] lemma dL2Inner_zero_left (g : ι → R) : ⟪0, g⟫_[R] = 0 := by simp [dL2Inner_eq_sum]
@[simp] lemma dL2Inner_zero_right (f : ι → R) : ⟪f, 0⟫_[R] = 0 := by simp [dL2Inner_eq_sum]

@[simp] lemma dL2Inner_of_isEmpty [IsEmpty ι] (f g : ι → R) : ⟪f, g⟫_[R] = 0 := by
  simp [Subsingleton.elim f 0]

@[simp] lemma dL2Inner_const_left (a : R) (f : ι → R) : ⟪const _ a, f⟫_[R] = conj a * ∑ x, f x := by
  simp only [dL2Inner_eq_sum, const_apply, mul_sum]

@[simp]
lemma dL2Inner_const_right (f : ι → R) (a : R) : ⟪f, const _ a⟫_[R] = (∑ x, conj (f x)) * a := by
  simp only [dL2Inner_eq_sum, const_apply, sum_mul]

lemma dL2Inner_add_left (f₁ f₂ g : ι → R) : ⟪f₁ + f₂, g⟫_[R] = ⟪f₁, g⟫_[R] + ⟪f₂, g⟫_[R] := by
  simp_rw [dL2Inner_eq_sum, Pi.add_apply, map_add, add_mul, sum_add_distrib]

lemma dL2Inner_add_right (f g₁ g₂ : ι → R) : ⟪f, g₁ + g₂⟫_[R] = ⟪f, g₁⟫_[R] + ⟪f, g₂⟫_[R] := by
  simp_rw [dL2Inner_eq_sum, Pi.add_apply, mul_add, sum_add_distrib]

lemma dL2Inner_smul_left [Star S] [StarModule S R] [IsScalarTower S R R] (c : S) (f g : ι → R) :
    ⟪c • f, g⟫_[R] = star c • ⟪f, g⟫_[R] := by
  simp only [dL2Inner_eq_sum, Pi.smul_apply, smul_mul_assoc, smul_sum, starRingEnd_apply, star_smul]

lemma dL2Inner_smul_right [SMulCommClass S R R] (c : S) (f g : ι → R) :
    ⟪f, c • g⟫_[R] = c • ⟪f, g⟫_[R] := by
  simp only [dL2Inner_eq_sum, Pi.smul_apply, mul_smul_comm, smul_sum, starRingEnd_apply, star_smul]

lemma smul_dL2Inner_left [InvolutiveStar S] [StarModule S R] [IsScalarTower S R R] (c : S)
    (f g : ι → R) : c • ⟪f, g⟫_[R] = ⟪star c • f, g⟫_[R] := by rw [dL2Inner_smul_left, star_star]

end CommSemiring

section CommRing
variable [CommRing R] [StarRing R]

@[simp]
lemma dL2Inner_neg_left (f g : ι → R) : ⟪-f, g⟫_[R] = -⟪f, g⟫_[R] := by simp [dL2Inner_eq_sum]

@[simp]
lemma dL2Inner_neg_right (f g : ι → R) : ⟪f, -g⟫_[R] = -⟪f, g⟫_[R] := by simp [dL2Inner_eq_sum]

lemma dL2Inner_sub_left (f₁ f₂ g : ι → R) : ⟪f₁ - f₂, g⟫_[R] = ⟪f₁, g⟫_[R] - ⟪f₂, g⟫_[R] := by
  simp_rw [sub_eq_add_neg, dL2Inner_add_left, dL2Inner_neg_left]

lemma dL2Inner_sub_right (f g₁ g₂ : ι → R) : ⟪f, g₁ - g₂⟫_[R] = ⟪f, g₁⟫_[R] - ⟪f, g₂⟫_[R] := by
  simp_rw [sub_eq_add_neg, dL2Inner_add_right, dL2Inner_neg_right]

end CommRing

section OrderedCommSemiring
variable [OrderedCommSemiring R] [StarRing R] [StarOrderedRing R] {f g : ι → R}

lemma dL2Inner_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ ⟪f, g⟫_[R] :=
  sum_nonneg fun _ _ ↦ mul_nonneg (star_nonneg_iff.2 <| hf _) <| hg _

end OrderedCommSemiring

section LinearOrderedCommRing
variable [LinearOrderedCommRing R] [StarRing R] [TrivialStar R] {f g : ι → R}

--TODO: Can we remove the `TrivialStar` assumption?
lemma abs_dL2Inner_le_dL2Inner_abs : |⟪f, g⟫_[R]| ≤ ⟪|f|, |g|⟫_[R] :=
  (abs_sum_le_sum_abs _ _).trans_eq <|
    sum_congr rfl fun i _ ↦ by simp only [abs_mul, conj_trivial, Pi.abs_apply]

end LinearOrderedCommRing

section RCLike
variable {κ : Type*} [RCLike R] {f : ι → R}

lemma dL2Inner_eq_inner (f g : ι → R) :
    ⟪f, g⟫_[R] = inner ((WithLp.equiv 2 _).symm f) ((WithLp.equiv 2 _).symm g) := rfl

lemma inner_eq_dL2Inner (f g : PiLp 2 fun _i : ι ↦ R) :
    inner f g = ⟪WithLp.equiv 2 _ f, WithLp.equiv 2 _ g⟫_[R] := rfl

lemma dL2Inner_self_of_norm_eq_one (hf : ∀ x, ‖f x‖ = 1) : ⟪f, f⟫_[R] = Fintype.card ι := by
  simp [dL2Inner_eq_sum, RCLike.conj_mul, hf, card_univ]

lemma linearIndependent_of_ne_zero_of_dL2Inner_eq_zero {v : κ → ι → R} (hz : ∀ k, v k ≠ 0)
    (ho : Pairwise fun k l ↦ ⟪v k, v l⟫_[R] = 0) : LinearIndependent R v := by
  simp_rw [dL2Inner_eq_inner] at ho
  have := linearIndependent_of_ne_zero_of_inner_eq_zero ?_ ho
  exacts [this, hz]

end RCLike

end MeasureTheory

namespace Mathlib.Meta.Positivity
open Lean Meta Qq Function MeasureTheory

section OrderedCommSemiring
variable [OrderedCommSemiring R] [StarRing R] [StarOrderedRing R] {f g : ι → R}

private lemma dL2Inner_nonneg_of_pos_of_nonneg (hf : 0 < f) (hg : 0 ≤ g) : 0 ≤ ⟪f, g⟫_[R] :=
  dL2Inner_nonneg hf.le hg

private lemma dL2Inner_nonneg_of_nonneg_of_pos (hf : 0 ≤ f) (hg : 0 < g) : 0 ≤ ⟪f, g⟫_[R] :=
  dL2Inner_nonneg hf hg.le

private lemma dL2Inner_nonneg_of_pos_of_pos (hf : 0 < f) (hg : 0 < g) : 0 ≤ ⟪f, g⟫_[R] :=
  dL2Inner_nonneg hf.le hg.le

end OrderedCommSemiring

/-- The `positivity` extension which identifies expressions of the form `⟪f, g⟫_[R]`. -/
@[positivity ⟪_, _⟫_[_]] def evalL2Inner : PositivityExt where eval {u R} _ _ e := do
  match e with
  | ~q(@dL2Inner $ι _ $instι $instring $inststar $f $g) =>
      let _p𝕜 ← synthInstanceQ q(OrderedCommSemiring $R)
      let _p𝕜 ← synthInstanceQ q(StarOrderedRing $R)
      assumeInstancesCommute
      match ← core q(inferInstance) q(inferInstance) f,
        ← core q(inferInstance) q(inferInstance) g with
      | .positive pf, .positive pg => return .nonnegative q(dL2Inner_nonneg_of_pos_of_pos $pf $pg)
      | .positive pf, .nonnegative pg =>
        return .nonnegative q(dL2Inner_nonneg_of_pos_of_nonneg $pf $pg)
      | .nonnegative pf, .positive pg =>
        return .nonnegative q(dL2Inner_nonneg_of_nonneg_of_pos $pf $pg)
      | .nonnegative pf, .nonnegative pg => return .nonnegative q(dL2Inner_nonneg $pf $pg)
      | _, _ => return .none
  | _ => throwError "not dL2Inner"

section OrderedCommSemiring
variable [OrderedCommSemiring R] [StarRing R] [StarOrderedRing R] {f g : ι → R}

example (hf : 0 < f) (hg : 0 < g) : 0 ≤ ⟪f, g⟫_[R] := by positivity
example (hf : 0 < f) (hg : 0 ≤ g) : 0 ≤ ⟪f, g⟫_[R] := by positivity
example (hf : 0 ≤ f) (hg : 0 < g) : 0 ≤ ⟪f, g⟫_[R] := by positivity
example (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ ⟪f, g⟫_[R] := by positivity

end OrderedCommSemiring
end Mathlib.Meta.Positivity
