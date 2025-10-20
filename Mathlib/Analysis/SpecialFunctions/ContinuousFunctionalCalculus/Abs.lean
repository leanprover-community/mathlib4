/-
Copyright (c) 2024 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Jireh Loreaux
-/

import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute


/-!
# Absolute value defined via the continuous functional calculus

This file defines the absolute value via the non-unital continuous functional calculus
and provides basic API.

## Main declarations

+ `CFC.abs`: The absolute value as `abs a := CFC.sqrt (star a * a)`.

-/

variable {𝕜 A : Type*}

open scoped NNReal
open CFC

namespace CFC

section NonUnital

section Real

variable [NonUnitalRing A] [StarRing A] [TopologicalSpace A]
  [Module ℝ A] [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]
  [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A]

/-- The absolute value defined via the non-unital continuous functional calculus. -/
noncomputable def abs (a : A) := sqrt (star a * a)

@[simp, grind =]
lemma abs_neg (a : A) : abs (-a) = abs a := by
  simp [abs]

@[simp, grind ←]
lemma abs_nonneg (a : A) : 0 ≤ abs a := sqrt_nonneg _

lemma abs_star (a : A) (ha : IsStarNormal a := by cfc_tac) : abs (star a) = abs a := by
  simp [abs, star_comm_self']

@[simp, grind =]
lemma abs_zero : abs (0 : A) = 0 := by
  simp [abs]

variable [IsTopologicalRing A] [T2Space A]

lemma abs_mul_abs (a : A) : abs a * abs a = star a * a :=
  sqrt_mul_sqrt_self _ <| star_mul_self_nonneg _

/- The hypotheses could be weakened to `Commute (star a * a) b`, but
in that case one should simply use `Commute.cfcₙ_nnreal` directly.

The point of this theorem is to have simpler hypotheses. -/
lemma _root_.Commute.cfcAbs_left {a b : A} (h₁ : Commute a b) (h₂ : Commute a (star b)) :
    Commute (abs a) b :=
  .cfcₙ_nnreal (by simp_all [h₂.star_left]) _

/- The hypotheses could be weakened to `Commute (star a * a) b`, but
in that case one should simply use `Commute.cfcₙ_nnreal` directly.

The point of this theorem is to have simpler hypotheses. -/
lemma _root_.Commute.cfcAbs_right {a b : A} (h₁ : Commute a b) (h₂ : Commute a (star b)) :
    Commute b (abs a) :=
  h₁.cfcAbs_left h₂ |>.symm

/- The hypotheses could be weakened to `Commute (star a * a) (star b * b)`, but
in that case one should simply use `Commute.cfcₙ_nnreal` (twice) directly.

The point of this theorem is to have simpler hypotheses. -/
lemma _root_.Commute.cfcAbs_cfcAbs {a b : A} (h₁ : Commute a b) (h₂ : Commute a (star b)) :
    Commute (abs a) (abs b) :=
  Commute.cfcₙ_nnreal (by simp_all [h₂.star_left]) _ |>.symm.cfcₙ_nnreal _ |>.symm

/-- Normal elements commute with their absolute value. -/
lemma commute_abs_self (a : A) (ha : IsStarNormal a := by cfc_tac) :
    Commute (abs a) a :=
  .cfcAbs_left (.refl a) ha.star_comm_self.symm

lemma _root_.Commute.cfcAbs_mul_eq {a b : A} (h₁ : Commute a b) (h₂ : Commute a (star b)) :
    abs (a * b) = abs a * abs b := by
  have hab := h₁.cfcAbs_cfcAbs h₂
  rw [abs, CFC.sqrt_eq_iff _ _ (star_mul_self_nonneg _)
    (hab.mul_nonneg (abs_nonneg a) (abs_nonneg b)), hab.eq, hab.mul_mul_mul_comm,
    abs_mul_abs, abs_mul_abs, star_mul, h₂.star_left.symm.mul_mul_mul_comm, h₁.eq]

lemma abs_mul_self (a : A) (ha : IsStarNormal a := by cfc_tac) :
    abs (a * a) = star a * a := by
  rw [Commute.cfcAbs_mul_eq (.refl a) ha.star_comm_self.symm, abs_mul_abs]

lemma abs_nnrpow_two (a : A) : abs a ^ (2 : ℝ≥0) = star a * a := by
  simp only [abs_nonneg, nnrpow_two]
  apply abs_mul_abs

lemma abs_nnrpow_two_mul (a : A) (x : ℝ≥0) :
    abs a ^ (2 * x) = (star a * a) ^ x := by rw [← nnrpow_nnrpow, abs_nnrpow_two]

lemma abs_nnrpow (a : A) (x : ℝ≥0) :
    abs a ^ x = (star a * a) ^ (x / 2) := by
  simp only [← abs_nnrpow_two_mul, mul_div_left_comm, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, div_self, mul_one]

@[grind =]
lemma abs_of_nonneg (a : A) (ha : 0 ≤ a := by cfc_tac) : abs a = a := by
  rw [abs, ha.star_eq, sqrt_mul_self a ha]

lemma abs_of_nonpos (a : A) (ha : a ≤ 0 := by cfc_tac) : abs a = -a := by
  simpa using abs_of_nonneg (-a)

lemma abs_eq_cfcₙ_norm (a : A) (ha : IsSelfAdjoint a := by cfc_tac) :
    abs a = cfcₙ (‖·‖) a := by
  conv_lhs =>
    rw [abs, ha.star_eq, sqrt_eq_real_sqrt .., ← cfcₙ_id' ℝ a, ← cfcₙ_mul .., ← cfcₙ_comp' ..]
  simp [← sq, Real.sqrt_sq_eq_abs]

protected lemma posPart_add_negPart (a : A) (ha : IsSelfAdjoint a := by cfc_tac) :
    a⁺ + a⁻ = abs a := by
  rw [CFC.posPart_def, CFC.negPart_def, ← cfcₙ_add .., abs_eq_cfcₙ_norm a ha]
  exact cfcₙ_congr fun x hx ↦ posPart_add_negPart x

lemma abs_sub_self (a : A) (ha : IsSelfAdjoint a := by cfc_tac) : abs a - a = 2 • a⁻ := by
 simpa [two_smul] using
    congr($(CFC.posPart_add_negPart a) - $(CFC.posPart_sub_negPart a)).symm

lemma abs_add_self (a : A) (ha : IsSelfAdjoint a := by cfc_tac) : abs a + a = 2 • a⁺ := by
  simpa [two_smul] using
    congr($(CFC.posPart_add_negPart a) + $(CFC.posPart_sub_negPart a)).symm

@[simp, grind =]
lemma cfcAbs_cfcAbs (a : A) : abs (abs a) = abs a := abs_of_nonneg ..

variable [StarModule ℝ A]

@[simp, grind =]
lemma abs_smul_nonneg {R : Type*} [Semiring R] [SMulWithZero R ℝ≥0] [SMul R A]
    [IsScalarTower R ℝ≥0 A] (r : R) (a : A) :
    abs (r • a) = r • abs a := by
  suffices ∀ r : ℝ≥0, abs (r • a) = r • abs a by simpa using this (r • 1)
  intro r
  rw [abs, sqrt_eq_iff _ _ (star_mul_self_nonneg _) (smul_nonneg (by positivity) (abs_nonneg _))]
  simp [mul_smul_comm, smul_mul_assoc, abs_mul_abs]

end Real

section RCLike

variable {p : A → Prop} [RCLike 𝕜]
  [NonUnitalRing A] [TopologicalSpace A] [Module 𝕜 A]
  [StarRing A] [PartialOrder A] [StarOrderedRing A]
  [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
  [NonUnitalContinuousFunctionalCalculus 𝕜 A p]

open ComplexOrder

lemma _root_.cfcₙ_norm_sq_nonneg (f : 𝕜 → 𝕜) (a : A) : 0 ≤ cfcₙ (fun z ↦ star (f z) * (f z)) a :=
  cfcₙ_nonneg fun _ _ ↦ star_mul_self_nonneg _

lemma _root_.cfcₙ_norm_nonneg (f : 𝕜 → 𝕜) (a : A) : 0 ≤ cfcₙ (‖f ·‖ : 𝕜 → 𝕜) a :=
  cfcₙ_nonneg fun _ _ ↦ by simp

variable [Module ℝ A] [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]
  [NonnegSpectrumClass ℝ A] [IsTopologicalRing A] [T2Space A]
  [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

variable [StarModule 𝕜 A] [StarModule ℝ A] [IsScalarTower ℝ 𝕜 A] in
@[simp]
lemma abs_smul (r : 𝕜) (a : A) : abs (r • a) = ‖r‖ • abs a := by
  trans abs (‖r‖ • a)
  · simp only [abs, mul_smul_comm, smul_mul_assoc, star_smul, ← smul_assoc,
      RCLike.real_smul_eq_coe_smul (K := 𝕜)]
    simp [-algebraMap_smul, ← smul_mul_assoc, ← mul_comm (starRingEnd _ _), RCLike.conj_mul, sq]
  · lift ‖r‖ to ℝ≥0 using norm_nonneg _ with r
    simp [← NNReal.smul_def]

variable (𝕜) in
lemma abs_eq_cfcₙ_coe_norm (a : A) (ha : p a := by cfc_tac) :
    abs a = cfcₙ (fun z : 𝕜 ↦ (‖z‖ : 𝕜)) a := by
  rw [abs, sqrt_eq_iff _ _ (hb := cfcₙ_norm_nonneg _ _), ← cfcₙ_mul ..]
  conv_rhs => rw [← cfcₙ_id' 𝕜 a, ← cfcₙ_star, ← cfcₙ_mul ..]
  simp [RCLike.conj_mul, sq]

lemma _root_.cfcₙ_comp_norm (f : 𝕜 → 𝕜) (a : A) (ha : p a := by cfc_tac)
    (hf : ContinuousOn f ((fun z ↦ (‖z‖ : 𝕜)) '' quasispectrum 𝕜 a) := by cfc_cont_tac) :
    cfcₙ (f ‖·‖) a = cfcₙ f (abs a) := by
  obtain (hf0 | hf0) := em (f 0 = 0)
  · rw [cfcₙ_comp' f (‖·‖) a, ← abs_eq_cfcₙ_coe_norm _ a]
  · rw [cfcₙ_apply_of_not_map_zero _ hf0,
      cfcₙ_apply_of_not_map_zero _ (fun h ↦ (hf0 <| by simpa using h).elim)]

lemma quasispectrum_abs (a : A) (ha : p a := by cfc_tac) :
    quasispectrum 𝕜 (abs a) = (fun z ↦ (‖z‖ : 𝕜)) '' quasispectrum 𝕜 a := by
  rw [abs_eq_cfcₙ_coe_norm 𝕜 a ha, cfcₙ_map_quasispectrum ..]

end RCLike

end NonUnital

section Unital

section Real

variable [Ring A] [StarRing A] [TopologicalSpace A] [Algebra ℝ A]
  [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A]
  [IsTopologicalRing A] [T2Space A]

lemma abs_eq_cfc_norm (a : A) (ha : IsSelfAdjoint a := by cfc_tac) :
    abs a = cfc (‖·‖) a := by
  rw [abs_eq_cfcₙ_norm _, cfcₙ_eq_cfc]

@[simp]
lemma abs_one : abs (1 : A) = 1 := by
  simp [abs]

variable [StarModule ℝ A]

@[simp]
lemma abs_algebraMap_nnreal (x : ℝ≥0) : abs (algebraMap ℝ≥0 A x) = algebraMap ℝ≥0 A x := by
  simp [Algebra.algebraMap_eq_smul_one]

@[simp]
lemma abs_natCast (n : ℕ) : abs (n : A) = n := by
  simpa only [map_natCast, Nat.abs_cast] using abs_algebraMap_nnreal (n : ℝ≥0)

@[simp]
lemma abs_ofNat (n : ℕ) [n.AtLeastTwo] : abs (ofNat(n) : A) = ofNat(n) := by
  simpa using abs_natCast n

@[simp]
lemma abs_intCast (n : ℤ) : abs (n : A) = |n| := by
  cases n with
  | ofNat _ => simp
  | negSucc n =>
    rw [Int.cast_negSucc, abs_neg, abs_natCast, ← Int.cast_natCast]
    congr

end Real

section RCLike

variable {p : A → Prop} [RCLike 𝕜]
  [Ring A] [TopologicalSpace A] [StarRing A] [PartialOrder A]
  [StarOrderedRing A] [Algebra 𝕜 A]
  [ContinuousFunctionalCalculus 𝕜 A p]
  [Algebra ℝ A] [NonnegSpectrumClass ℝ A] [IsTopologicalRing A] [T2Space A]
  [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

variable [StarModule 𝕜 A] [StarModule ℝ A] [IsScalarTower ℝ 𝕜 A] in
@[simp]
lemma abs_algebraMap (c : 𝕜) : abs (algebraMap 𝕜 A c) = algebraMap ℝ A ‖c‖ := by
  simp [Algebra.algebraMap_eq_smul_one]

lemma _root_.cfc_comp_norm (f : 𝕜 → 𝕜) (a : A) (ha : p a := by cfc_tac)
    (hf : ContinuousOn f ((fun z ↦ (‖z‖ : 𝕜)) '' spectrum 𝕜 a) := by cfc_cont_tac) :
    cfc (f ‖·‖) a = cfc f (abs a) := by
  rw [abs_eq_cfcₙ_coe_norm 𝕜 a, cfcₙ_eq_cfc, ← cfc_comp' ..]

lemma abs_sq (a : A) : (abs a) ^ 2 = star a * a := by
  rw [sq, abs_mul_abs]

lemma spectrum_abs (a : A) (ha : p a := by cfc_tac) :
    spectrum 𝕜 (abs a) = (fun z ↦ (‖z‖ : 𝕜)) '' spectrum 𝕜 a := by
  rw [abs_eq_cfcₙ_coe_norm 𝕜 a, cfcₙ_eq_cfc, cfc_map_spectrum ..]

end RCLike

end Unital

section CStar

/- This section requires `A` to be a `CStarRing` -/

variable [NonUnitalNormedRing A] [StarRing A] [CStarRing A]
  [NormedSpace ℝ A] [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]
  [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A]

open CFC

@[simp, grind =]
lemma abs_eq_zero_iff {a : A} : abs a = 0 ↔ a = 0 := by
  rw [CFC.abs, sqrt_eq_zero_iff _, CStarRing.star_mul_self_eq_zero_iff]

@[simp, grind =]
lemma norm_abs {a : A} : ‖abs a‖ = ‖a‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), sq, sq, ← CStarRing.norm_star_mul_self,
    (abs_nonneg _).star_eq, CFC.abs_mul_abs, CStarRing.norm_star_mul_self]

end CStar

end CFC
