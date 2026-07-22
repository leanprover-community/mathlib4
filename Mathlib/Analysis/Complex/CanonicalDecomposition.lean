/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Meromorphic.FactorizedRational
public import Mathlib.Analysis.Meromorphic.RCLike

/-!
# Canonical Decomposition

If a function `f` is meromorphic on a compact set `U`, then it has only finitely many zeros and
poles on the disk, and the theorem `MeromorphicOn.extract_zeros_poles` can be used to re-write `f`
as `(∏ᶠ u, (· - u) ^ divisor f U u) • g`, where `g` is analytic without zeros on `U`. In case where
`U` is a disk, one consider a similar decomposition, called *Finite Canonical Decomposition* or
*Finite Blaschke Product* that replaces the factors `(· - u)` by canonical factors that take only
values of norm one on the boundary of the disk. This file introduces the canonical factors and
provides API for the canonical decomposition.

See Page 160f of [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677] for a detailed
discussion.

TODO: Formulate a refined version of the canonical decomposition that takes zeros on poles on the
boundary of the ball into account.
-/

@[expose] public section

namespace Complex

open ComplexConjugate Filter Function MeromorphicOn Metric Real Set

variable {R : ℝ} {w : ℂ}

/-!
## Canonical Factors

Given `R : ℝ` and `w : ℂ`, the canonical factor `canonical R w : ℂ → ℂ` is meromorphic function in
normal form that has a single pole at `w`, no zeros, and takes values of norm one on the circle of
radius `R`.
-/

/--
Given `R : ℝ` and `w : ℂ`, the canonical factor is the function
`fun z ↦ (R ^ 2 - (conj w) * z) / (R * (z - w))`. In applications, one will typically consider a
setting where `w ∈ ball 0 R`.
-/
noncomputable def canonicalFactor (R : ℝ) (w : ℂ) : ℂ → ℂ :=
  fun z ↦ (R ^ 2 - (conj w) * z) / (R * (z - w))

lemma canonicalFactor_def (R : ℝ) (w : ℂ) :
    canonicalFactor R w = fun z ↦ (R ^ 2 - (conj w) * z) / (R * (z - w)) :=
  rfl

lemma canonicalFactor_apply (R : ℝ) (w z : ℂ) :
    canonicalFactor R w z = (R ^ 2 - (conj w) * z) / (R * (z - w)) :=
  rfl

@[simp]
lemma canonicalFactor_apply_self (R : ℝ) (w : ℂ) :
    canonicalFactor R w w = 0 := by
  simp [canonicalFactor_apply]

/-!
### Regularity properties
-/

variable (R w) in
/--
Canonical factors are meromorphic.
-/
theorem meromorphic_canonicalFactor : Meromorphic (canonicalFactor R w) := by
  intro x
  unfold canonicalFactor
  fun_prop

open scoped ComplexOrder in
variable (R w) in
/--
The canonical factor `CanonicalFactor R w` is analytic on the complement of `w`.
-/
theorem analyticOnNhd_canonicalFactor : AnalyticOnNhd ℂ (canonicalFactor R w) {w}ᶜ := by
  intro x hx
  rw [canonicalFactor_def]
  obtain (rfl | h) := eq_or_ne R 0
  · simpa using analyticAt_const
  have : x - w ≠ 0 := by grind
  fun_prop (disch := positivity)

/--
The canonical factor `CanonicalFactor R w` has a simple pole at `z = w`.
-/
theorem meromorphicOrderAt_canonicalFactor (h : w ∈ ball 0 R) :
    meromorphicOrderAt (canonicalFactor R w) w = -1 := by
  unfold canonicalFactor
  rw [fun_meromorphicOrderAt_div (by fun_prop) (by fun_prop),
    fun_meromorphicOrderAt_mul (by fun_prop) (by fun_prop)]
  have : meromorphicOrderAt (fun z ↦ ↑R ^ 2 - (starRingEnd ℂ) w * z) w = 0 := by
    refine (MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff ?_).2 ?_
    · apply AnalyticAt.meromorphicNFAt
      fun_prop
    · rw [← normSq_eq_conj_mul_self, normSq_eq_norm_sq w, sub_ne_zero, ne_eq, ← ofReal_pow,
        ofReal_inj, sq_eq_sq₀ (pos_of_mem_ball h).le (norm_nonneg w)]
      rw [mem_ball_iff_norm, sub_zero] at h
      grind
  simp [this, meromorphicOrderAt_const, (pos_of_mem_ball h).ne',
    meromorphicOrderAt_id_sub_const]

/--
Canonical factors are meromorphic in normal form.
-/
theorem meromorphicNFOn_canonicalFactor (h : w ∈ ball 0 R) :
    MeromorphicNFOn (canonicalFactor R w) Set.univ := by
  intro z hz
  obtain (rfl | h₁) := eq_or_ne z w
  · rw [meromorphicNFAt_iff_analyticAt_or]
    right
    refine ⟨meromorphic_canonicalFactor R z z, ?_, by simp⟩
    simpa [meromorphicOrderAt_canonicalFactor h] using WithTop.coe_lt_zero.mpr (by lia : -1 < 0)
  apply (analyticOnNhd_canonicalFactor R w z h₁).meromorphicNFAt

/-!
### Values of Canonical Factors
-/

open scoped ComplexOrder in
/--
The canonical factor `CanonicalFactor R w` has no zeros inside the ball of radius `R`.
-/
theorem canonicalFactor_ne_zero {z : ℂ} (hw : w ∈ ball 0 R) (h₁z : z ∈ closedBall 0 R)
    (h₂z : z ≠ w) :
    canonicalFactor R w z ≠ 0 := by
  obtain ⟨hR, hzw⟩ : 0 < R ∧ z - w ≠ 0 := by grind [mem_ball_zero_iff, norm_nonneg]
  simp only [mem_ball, dist_zero_right, mem_closedBall] at hw h₁z
  have h_num_ne_zero : R ^ 2 - conj w * z ≠ 0 := by
    suffices ‖conj w * z‖ < ‖(R : ℂ) ^ 2‖ by grind
    suffices ‖w‖ * ‖z‖ < R * R by simpa [sq]
    grw [h₁z]
    gcongr
  rw [canonicalFactor_apply]
  positivity

/--
The function `CanonicalFactor R w` vanishes only at `w`.
-/
theorem canonicalFactor_eq_zero_iff {z : ℂ} (hw : w ∈ ball 0 R) (hz : z ∈ ball 0 R) :
    canonicalFactor R w z = 0 ↔ z = w := by
  constructor
  · contrapose
    exact canonicalFactor_ne_zero hw (ball_subset_closedBall hz)
  · simp_all

open scoped ComplexOrder in
/--
The canonical factor `CanonicalFactor R w` takes values of norm one on `sphere 0 R`.
-/
theorem norm_canonicalFactor_eval_circle_eq_one {z : ℂ} (hw : w ∈ ball 0 R) (hz : z ∈ sphere 0 R) :
    ‖canonicalFactor R w z‖ = 1 := by
  obtain ⟨hR, hzw⟩ : 0 < R ∧ z - w ≠ 0 := by
    grind [mem_ball_zero_iff, norm_nonneg, mem_sphere_zero_iff_norm]
  rw [canonicalFactor, norm_div, div_eq_iff (by rw [ne_eq, norm_eq_zero]; positivity), one_mul]
  obtain rfl := by simpa [mem_sphere_zero_iff_norm] using hz
  rw [← ofReal_pow, ← normSq_eq_norm_sq, normSq_eq_conj_mul_self, ← sub_mul, mul_comm _ z]
  simp [← map_sub]

/-!
### Orders and Divisors
-/

/--
Canonical factors are nowhere locally constant zero.
-/
theorem meromorphicOrderAt_canonicalFactor_ne_top {z : ℂ} {R : ℝ} (w : ℂ) (hR : 0 < R) :
    meromorphicOrderAt (canonicalFactor R w) z ≠ ⊤ := by
  apply (meromorphic_canonicalFactor R w).exists_meromorphicOrderAt_ne_top_iff_forall.1
  use 0
  by_cases hw : w = 0
  · simp_all [meromorphicOrderAt_canonicalFactor (mem_ball_self hR)]
  suffices meromorphicOrderAt (canonicalFactor R w) 0 = 0 by simp_all
  rw [MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff]
  · simp_all [canonicalFactor, ne_of_gt hR]
  · apply AnalyticAt.meromorphicNFAt
    apply analyticOnNhd_canonicalFactor
    grind

/--
The divisor of `CanonicalFactor R w` is `-w`.  In other words, the divisor function takes the value
-1 at `w` and is zero elsewhere.
-/
theorem divisor_canonicalFactor (hw : w ∈ ball 0 R) :
    MeromorphicOn.divisor (canonicalFactor R w) (ball 0 R)
      = -(Function.locallyFinsuppWithin.single w 1).restrict (Set.subset_univ (ball 0 R)) := by
  ext z
  by_cases hz : z ∈ ball 0 R
  · rw [MeromorphicOn.divisor_apply
      (fun z hz ↦ meromorphic_canonicalFactor R w z) hz]
    obtain (rfl | h₂z) := eq_or_ne z w
    · rw [meromorphicOrderAt_canonicalFactor hz]
      simp_all [Function.locallyFinsuppWithin.restrict_apply]
    · have : meromorphicOrderAt (canonicalFactor R w) z = 0 := by
        rw [(meromorphicNFOn_canonicalFactor hw (Set.mem_univ z)).meromorphicOrderAt_eq_zero_iff]
        exact canonicalFactor_ne_zero hw (ball_subset_closedBall hz) h₂z
      simp [this, h₂z, Function.locallyFinsuppWithin.restrict_apply, hz]
  · simp_all

/-!
## Canonical Decomposition

The canonical decomposition theorem shows that a meromorphic function `f` on a disk is equal, up to
modification over a discrete set, to a product of canonical factors and a meromorphic function `g`
without zeros or poles in the interior of the disk.

To simplify notation and avoid repetition, we introduce a structure, `CanonicalDecomp`, that bundles
the conclusions of the decomposition theorem.
-/

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {R : ℝ} {c w : ℂ}
  {f : ℂ → E}

/--
Given functions `f`, `g` and a real number `R`, the following convenience structure packs the
information relevant in the canonical decomposition.  The condition "`g` is without zeros or poles"
is formulated by saying that `g` is meromorphic in normal form and `g ≠ 0`.
-/
structure CanonicalDecomp (f g : ℂ → E) (R : ℝ) : Prop where
  /-- A proof that `f` is meromorphic on `closedBall 0 R`. -/
  meromorphicOn : MeromorphicOn f (closedBall 0 R)

  /-- A proof that `g` is meromorphic in normal form on `closedBall 0 R`. -/
  meromorphicNFOn : MeromorphicNFOn g (closedBall 0 R)

  /-- A proof that `g` does not vanish in the interior of the ball. -/
  ne_zero : ∀ u ∈ (ball 0 R), g u ≠ 0

  /--
  A proof that `f` is equal, up to modification over a discrete set, to a product of `g` and
  canonical factors prescribed by the divisor of `f`.
  -/
  eventuallyEq : f =ᶠ[codiscreteWithin (closedBall 0 R)]
    (∏ᶠ u, (canonicalFactor R u) ^ (-MeromorphicOn.divisor f (ball 0 R) u)) • g

-- Auxiliary lemma for the proof of the canonical decomposition theorem: The factor in the canonical
-- decomposition is meromorphic in normal form.
private lemma canonicalDecomposition_aux₁ (F : locallyFinsuppWithin (ball (0 : ℂ) R) ℤ) :
    MeromorphicNFOn (∏ᶠ u, (canonicalFactor R u) ^ (F u)) (ball (0 : ℂ) R) := by
  classical
  refine meromorphicNFOn_finprod (fun w ↦ ?_) fun z hz a ha b hb ↦ ?_
  · by_cases hw : w ∈ ball 0 R
    · exact fun _ _ ↦ (meromorphicNFOn_canonicalFactor hw).zpow (by trivial)
    · simp only [hw, not_false_eq_true, locallyFinsuppWithin.apply_eq_zero_of_notMem, zpow_zero]
      exact analyticOnNhd_const.meromorphicNFOn
  · have ⟨h₂a, h₂b⟩ : a ∈ ball 0 R ∧ b ∈ ball 0 R := by constructor <;> (by_contra; aesop)
    grind [eq_zero_of_zpow_eq_zero hb, eq_zero_of_zpow_eq_zero ha,
      canonicalFactor_eq_zero_iff h₂b hz, canonicalFactor_eq_zero_iff h₂a hz]

-- Auxiliary lemma for the proof of the canonical decomposition theorem: Write a function with
-- finite support as a linear combination of singleton indicator functions.
open Function.locallyFinsuppWithin in
private lemma sum_apply_smul_single_eq_self
    {X : Type*} [TopologicalSpace X] [DecidableEq X] {U : Set X}
    {F : Function.locallyFinsuppWithin U ℤ} (h : F.support.Finite) :
    ∑ x ∈ h.toFinset, (F x) • ((single x (1 : ℤ)).restrict (subset_univ U)) = F := by
  ext z
  by_cases hz : z ∉ U
  · aesop
  simp only [coe_sum, coe_zsmul, zsmul_eq_mul, Finset.sum_apply, Pi.mul_apply, Pi.intCast_apply,
    Int.cast_eq, Function.locallyFinsuppWithin.restrict_apply]
  by_cases hz : z ∈ F.support
  · rw [← Finset.add_sum_erase _ _ (by aesop : z ∈ h.toFinset), Finset.sum_eq_zero (by aesop)]
    aesop
  · aesop

-- Auxiliary lemma for the proof of the canonical decomposition theorem: Exhibit the divisor of the
-- factor in the canonical decomposition as the negative of the divisor of `f`.
private lemma canonicalDecomposition_aux₂ (h₁f : MeromorphicOn f (closedBall 0 R)) :
    divisor (∏ᶠ u, (canonicalFactor R u) ^ (divisor f (ball 0 R) u)) (ball 0 R)
      = -(divisor f (ball 0 R)) := by
  have η₀ : (-divisor f (ball 0 R)).support.Finite := by simp [h₁f.divisor_ball_support_finite]
  rw [finprod_eq_prod_of_mulSupport_subset_of_finite _ (by aesop) η₀, divisor_prod]
  · simp_rw [divisor_zpow (fun z hz ↦ meromorphic_canonicalFactor R _ z)]
    conv_rhs => rw [← sum_apply_smul_single_eq_self η₀]
    apply Finset.sum_congr rfl fun x hx ↦ ?_
    rw [divisor_canonicalFactor, smul_neg, locallyFinsuppWithin.coe_neg, Pi.neg_apply, neg_smul]
    by_contra
    simp_all
  · intro z hz
    apply zpow (fun x hx ↦ meromorphic_canonicalFactor R z x)
  · intro z hz x hx
    rw [meromorphicOrderAt_zpow (meromorphic_canonicalFactor R z x)]
    lift (meromorphicOrderAt (canonicalFactor R z) x) to ℤ using
      (meromorphicOrderAt_canonicalFactor_ne_top z (pos_of_mem_ball hx)) with ℓ
    simp [← WithTop.coe_mul]

-- Auxiliary lemma for the proof of the canonical decomposition theorem: The (inverse of the) factor
-- in the canonical decomposition does not vanish identically.
private lemma canonicalDecomposition_aux₃ {z : ℂ} (hR : 0 < R) :
    meromorphicOrderAt (∏ᶠ (c : ℂ), canonicalFactor R c ^ (divisor f (ball 0 R)) c) z ≠ ⊤ := by
  apply meromorphicOrderAt_finprod_ne_top
    (fun _ ↦ MeromorphicAt.zpow (meromorphic_canonicalFactor _ _ _) _)
  intro c
  rw [meromorphicOrderAt_zpow (meromorphic_canonicalFactor R c z)]
  lift meromorphicOrderAt (canonicalFactor R c) z to ℤ using
    (meromorphicOrderAt_canonicalFactor_ne_top c hR) with ℓ
  simp [← WithTop.coe_mul]

/--
**Canonical decomposition:** A meromorphic function `f` on a disk is equal, up to modification over
a discrete set, to a product of canonical factors and a meromorphic function `g` without zeros or
poles in the interior of the disk.
-/
theorem _root_.MeromorphicOn.exists_canonicalDecomp
    (h₁f : MeromorphicOn f (closedBall 0 R))
    (h₂f : ∀ u : (closedBall (0 : ℂ) R), meromorphicOrderAt f u ≠ ⊤) :
    ∃ g : ℂ → E, CanonicalDecomp f g R := by
  -- Trivial case: If `R` is non-positive, then the ball is empty.
  by_cases hR : R ≤ 0
  · use fun _ ↦ f 0
    exact {
      meromorphicOn := h₁f
      meromorphicNFOn := fun z hz ↦ AnalyticAt.meromorphicNFAt analyticAt_const
      ne_zero := by simp [ball_eq_empty.2 hR]
      eventuallyEq := by
        filter_upwards [self_mem_codiscreteWithin (closedBall 0 R)] with a ha
        have : R = 0 := by grind [nonneg_of_mem_closedBall ha]
        aesop
    }
  rw [not_le] at hR
  -- General case: The requirement that `f =ᶠ[…] (something) • g` implies that `g` must equal
  -- `(something)⁻¹ • g`, converted to a meromorphic function in normal form. The next lines define
  -- `g` in this way and establish basic properties.
  let φ := (∏ᶠ c, canonicalFactor R c ^ (divisor f (ball 0 R)) c) • f
  have hφ : MeromorphicOn φ (closedBall 0 R) := by
    apply smul (MeromorphicOn.finprod _) h₁f
    exact fun z ↦ zpow (fun z₁ hz₁ ↦ meromorphic_canonicalFactor _ _ _) _
  let g := toMeromorphicNFOn φ (closedBall 0 R)
  have h₃g : divisor g (ball 0 R) = 0 := by
    rw [divisor_congr_codiscreteWithin
        ((toMeromorphicNFOn_eqOn_codiscrete hφ).symm.filter_mono
        (codiscreteWithin_mono ball_subset_closedBall)) isOpen_ball,
      divisor_smul _ (fun x hx ↦ h₁f x (ball_subset_closedBall hx))
        (fun z _ ↦ canonicalDecomposition_aux₃ hR)
        (fun z hz ↦ h₂f ⟨z, ball_subset_closedBall hz⟩),
      canonicalDecomposition_aux₂ h₁f, neg_add_cancel]
    apply (canonicalDecomposition_aux₁ _).meromorphicOn
  have h₂g : MeromorphicNFOn g (closedBall 0 R) :=
    meromorphicNFOn_toMeromorphicNFOn φ (closedBall 0 R)
  have h₄g {z : ℂ} (hz : z ∈ closedBall 0 R) : meromorphicOrderAt g z ≠ ⊤ := by
    rw [meromorphicOrderAt_toMeromorphicNFOn hφ hz, meromorphicOrderAt_smul _ (h₁f z hz)]
    · simpa [h₂f ⟨z, hz⟩] using canonicalDecomposition_aux₃ hR
    · apply MeromorphicAt.finprod (fun x ↦ (meromorphic_canonicalFactor R x z).zpow _)
  -- Use the function `g` defined above and establish the required properties
  use g
  have η₀ : (-divisor f (ball 0 R)).support.Finite := by simp [h₁f.divisor_ball_support_finite]
  exact {
    meromorphicOn := h₁f
    meromorphicNFOn := meromorphicNFOn_toMeromorphicNFOn φ (closedBall 0 R)
    ne_zero := by
      intro z hz
      rw [← MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff (h₂g (ball_subset_closedBall hz))]
      have : divisor g (ball 0 R) z = 0 := by simp [h₃g]
      rw [divisor_apply (fun x hx ↦ (h₂g (ball_subset_closedBall hx)).meromorphicAt) hz] at this
      simpa [h₄g (ball_subset_closedBall hz)] using this
    eventuallyEq := by
      trans (∏ i ∈ η₀.toFinset, canonicalFactor R i ^ (-(divisor f (ball 0 R)) i)) • φ
      · unfold φ
        rw [finprod_eq_prod_of_mulSupport_subset_of_finite _ (by aesop) η₀]
        · filter_upwards [codiscreteWithin_mono (by tauto) η₀.compl_mem_codiscrete,
            self_mem_codiscreteWithin (closedBall 0 R)] with a ha h₂a
          simp only [Pi.smul_apply', Finset.prod_apply, Pi.pow_apply]
          rw [← smul_assoc, ← Finset.prod_smul, Finset.prod_eq_one, one_smul]
          intro x hx
          rw [smul_eq_mul, ← zpow_add', neg_add_cancel, zpow_zero]
          simp_all only [ne_eq, Subtype.forall, mem_closedBall, dist_zero_right,
            locallyFinsuppWithin.support_neg, mem_compl_iff, mem_support, Decidable.not_not,
            Finite.mem_toFinset, neg_add_cancel, not_true_eq_false, neg_eq_zero, and_self, or_self,
            or_false]
          apply canonicalFactor_ne_zero _ (by simp_all) (by grind)
          by_contra h
          simp_all
      · rw [finprod_eq_prod_of_mulSupport_subset_of_finite _ (by aesop) η₀]
        filter_upwards [toMeromorphicNFOn_eqOn_codiscrete hφ] using by simp_all [g]
  }

end Complex
