/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Ideal.Norm
import Mathlib.RingTheory.RootsOfUnity.Basic

#align_import number_theory.number_field.units from "leanprover-community/mathlib"@"00f91228655eecdcd3ac97a7fd8dbcb139fe990a"

/-!
# Units of a number field
We prove results about the group `(𝓞 K)ˣ` of units of the ring of integers `𝓞 K` of a number
field `K`.

## Main definitions

* `Units.rank`: the unit rank of the number field `K`.

* `Units.fundSystem`: a fundamental system of units of `K`.

* `Units.basisModTorsion`: a `ℤ`-basis of `(𝓞 K)ˣ ⧸ (torsion K)` (as an additive `ℤ`-module).

## Main results

* `isUnit_iff_norm`: an algebraic integer `x : 𝓞 K` is a unit if and only if `|norm ℚ x| = 1`.

* `Units.mem_torsion`: an unit `x : (𝓞 K)ˣ` is torsion iff `w x = 1` for all infinite places of `K`.

* `Units.exist_unique_eq_mul_prod`: an unit `x : (𝓞 K)ˣ` can be written in a unique way as the
product of a root of unity times the product of powers of units of the fundamental system.

## Tags
number field, units
 -/


open scoped NumberField

noncomputable section

open NumberField Units BigOperators

section Rat

theorem Rat.RingOfIntegers.isUnit_iff {x : 𝓞 ℚ} : IsUnit x ↔ (x : ℚ) = 1 ∨ (x : ℚ) = -1 := by
  simp_rw [(isUnit_map_iff (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ) x).symm, Int.isUnit_iff,
    RingEquiv.coe_toRingHom, RingEquiv.map_eq_one_iff, RingEquiv.map_eq_neg_one_iff, ←
    Subtype.coe_injective.eq_iff]; rfl
#align rat.ring_of_integers.is_unit_iff Rat.RingOfIntegers.isUnit_iff

end Rat

variable (K : Type*) [Field K]

section IsUnit

variable {K}

theorem isUnit_iff_norm [NumberField K] {x : 𝓞 K} :
    IsUnit x ↔ |(RingOfIntegers.norm ℚ x : ℚ)| = 1 := by
  convert (RingOfIntegers.isUnit_norm ℚ (F := K)).symm
  rw [← abs_one, abs_eq_abs, ← Rat.RingOfIntegers.isUnit_iff]
#align is_unit_iff_norm isUnit_iff_norm

end IsUnit

namespace NumberField.Units

section coe

theorem coe_injective : Function.Injective ((↑) : (𝓞 K)ˣ → K) :=
  fun _ _ h => by rwa [SetLike.coe_eq_coe, Units.eq_iff] at h

variable {K}

theorem coe_mul (x y : (𝓞 K)ˣ) : ((x * y : (𝓞 K)ˣ) : K) = (x : K) * (y : K) := rfl

theorem coe_pow (x : (𝓞 K)ˣ) (n : ℕ) : (x ^ n : K) = (x : K) ^ n := by
  rw [← SubmonoidClass.coe_pow, ← val_pow_eq_pow_val]

theorem coe_zpow (x : (𝓞 K)ˣ) (n : ℤ) : (x ^ n : K) = (x : K) ^ n := by
  change ((Units.coeHom K).comp (map (algebraMap (𝓞 K) K))) (x ^ n) = _
  exact map_zpow _ x n

theorem coe_one : ((1 : (𝓞 K)ˣ) : K) = (1 : K) := rfl

theorem coe_neg_one : ((-1 : (𝓞 K)ˣ) : K) = (-1 : K) := rfl

theorem coe_ne_zero (x : (𝓞 K)ˣ) : (x : K) ≠ 0 :=
  Subtype.coe_injective.ne_iff.mpr (_root_.Units.ne_zero x)

end coe

open NumberField.InfinitePlace

section torsion

/-- The torsion subgroup of the group of units. -/
def torsion : Subgroup (𝓞 K)ˣ := CommGroup.torsion (𝓞 K)ˣ

theorem mem_torsion {x : (𝓞 K)ˣ} [NumberField K] :
    x ∈ torsion K ↔ ∀ w : InfinitePlace K, w x = 1 := by
  rw [eq_iff_eq (x : K) 1, torsion, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
  refine ⟨fun ⟨n, h_pos, h_eq⟩ φ => ?_, fun h => ?_⟩
  · refine norm_map_one_of_pow_eq_one φ.toMonoidHom (k := ⟨n, h_pos⟩) ?_
    rw [PNat.mk_coe, ← coe_pow, h_eq, coe_one]
  · obtain ⟨n, hn, hx⟩ := Embeddings.pow_eq_one_of_norm_eq_one K ℂ x.val.prop h
    exact ⟨n, hn, by ext; rw [coe_pow, hx, coe_one]⟩

/-- Shortcut instance because Lean tends to time out before finding the general instance. -/
instance : Nonempty (torsion K) := One.nonempty

/-- The torsion subgroup is finite. -/
instance [NumberField K] : Fintype (torsion K) := by
  refine @Fintype.ofFinite _ (Set.finite_coe_iff.mpr ?_)
  refine Set.Finite.of_finite_image ?_ ((coe_injective K).injOn _)
  refine (Embeddings.finite_of_norm_le K ℂ 1).subset
    (fun a ⟨u, ⟨h_tors, h_ua⟩⟩ => ⟨?_, fun φ => ?_⟩)
  · rw [← h_ua]
    exact u.val.prop
  · rw [← h_ua]
    exact le_of_eq ((eq_iff_eq _ 1).mp ((mem_torsion K).mp h_tors) φ)

-- a shortcut instance to stop the next instance from timing out
instance [NumberField K] : Finite (torsion K) := inferInstance

/-- The torsion subgroup is cylic. -/
instance [NumberField K] : IsCyclic (torsion K) := subgroup_units_cyclic _

/-- The order of the torsion subgroup as positive integer. -/
def torsionOrder [NumberField K] : ℕ+ := ⟨Fintype.card (torsion K), Fintype.card_pos⟩

/-- If `k` does not divide `torsionOrder` then there are no nontrivial roots of unity of
  order dividing `k`. -/
theorem rootsOfUnity_eq_one [NumberField K]  {k : ℕ+} (hc : Nat.Coprime k (torsionOrder K))
    {ζ : (𝓞 K)ˣ} : ζ ∈ rootsOfUnity k (𝓞 K) ↔ ζ = 1 := by
  rw [mem_rootsOfUnity]
  refine ⟨fun h => ?_, fun h => by rw [h, one_pow]⟩
  refine orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hc ?_ ?_)
  · exact orderOf_dvd_of_pow_eq_one h
  · have hζ : ζ ∈ torsion K := by
      rw [torsion, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
      exact ⟨k, k.prop, h⟩
    rw [orderOf_submonoid (⟨ζ, hζ⟩ : torsion K)]
    exact orderOf_dvd_card_univ

/-- The group of roots of unity of order dividing `torsionOrder` is equal to the torsion
group. -/
theorem rootsOfUnity_eq_torsion [NumberField K] :
    rootsOfUnity (torsionOrder K) (𝓞 K) = torsion K := by
  ext ζ
  rw [torsion, mem_rootsOfUnity]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
    exact ⟨↑(torsionOrder K), (torsionOrder K).prop, h⟩
  · exact Subtype.ext_iff.mp (@pow_card_eq_one (torsion K) _ ⟨ζ, h⟩ _)

end torsion

namespace dirichlet
-- This section is devoted to the proof of Dirichlet's unit theorem
-- We define a group morphism from `(𝓞 K)ˣ` to `{w : InfinitePlace K // w ≠ w₀} → ℝ` where `w₀`
-- is a distinguished (arbitrary) infinite place, prove that its kernel is the torsion subgroup
-- (see `logEmbedding_eq_zero_iff`) and that its image, called `unitLattice`, is a full
-- `ℤ`-lattice. It follows that is a free `ℤ`-module (see `unitLattice_moduleFree `) of
-- rank `card (InfinitePlaces K) - 1` (see `unitLattice_rank`).
-- To prove that the `unitLattice` is a full `ℤ`-lattice, we need to prove that it is discrete
-- (see `unitLattice_inter_ball_finite`) and that it spans the full space over `ℝ`
-- (see ` unitLattice_span_eq_top`); this is the main part of the proof, see the section
-- `span_top` below for more details.

open scoped Classical

variable [NumberField K]

variable {K}

/-- The distinguished infinite place. -/
def w₀ : InfinitePlace K := (inferInstance : Nonempty (InfinitePlace K)).some

variable (K)

/-- The logarithmic embedding of the units (seen as an `Additive` group). -/
def logEmbedding : Additive ((𝓞 K)ˣ) →+ ({w : InfinitePlace K // w ≠ w₀} → ℝ) :=
{ toFun := fun x w => mult w.val * Real.log (w.val (Additive.toMul x))
  map_zero' := by simp; rfl
  map_add' := by
    intro _ _
    simp [ne_eq, toMul_add, map_mul, map_eq_zero, coe_ne_zero, Real.log_mul, mul_add]
    rfl }

variable {K}

@[simp]
theorem logEmbedding_component (x : (𝓞 K)ˣ) (w : {w : InfinitePlace K // w ≠ w₀}) :
    (logEmbedding K x) w = mult w.val * Real.log (w.val x) := rfl

theorem logEmbedding_sum_component (x : (𝓞 K)ˣ) :
    ∑ w, logEmbedding K x w = - mult (w₀ : InfinitePlace K) * Real.log (w₀ (x : K)) := by
  have h := congr_arg Real.log (prod_eq_abs_norm (x : K))
  rw [show |(Algebra.norm ℚ) (x : K)| = 1 from isUnit_iff_norm.mp x.isUnit, Rat.cast_one,
    Real.log_one, Real.log_prod] at h
  · simp_rw [Real.log_pow] at h
    rw [← Finset.insert_erase (Finset.mem_univ w₀), Finset.sum_insert (Finset.not_mem_erase w₀
      Finset.univ), add_comm, add_eq_zero_iff_eq_neg] at h
    convert h using 1
    · refine (Finset.sum_subtype _ (fun w => ?_) (fun w => (mult w) * (Real.log (w (x : K))))).symm
      exact ⟨Finset.ne_of_mem_erase, fun h => Finset.mem_erase_of_ne_of_mem h (Finset.mem_univ w)⟩
    · norm_num
  · exact fun w _ => pow_ne_zero _ (AbsoluteValue.ne_zero _ (coe_ne_zero x))

theorem mult_log_place_eq_zero {x : (𝓞 K)ˣ} {w : InfinitePlace K} :
    mult w * Real.log (w x) = 0 ↔ w x = 1 := by
  rw [mul_eq_zero, or_iff_right, Real.log_eq_zero, or_iff_right, or_iff_left]
  · have : 0 ≤ w x := map_nonneg _ _
    linarith
  · simp only [ne_eq, map_eq_zero, coe_ne_zero x]
  · refine (ne_of_gt ?_)
    rw [mult]; split_ifs <;> norm_num

theorem logEmbedding_eq_zero_iff (x : (𝓞 K)ˣ) :
    logEmbedding K x = 0 ↔ x ∈ torsion K := by
  rw [mem_torsion]
  refine ⟨fun h w => ?_, fun h => ?_⟩
  · by_cases hw : w = w₀
    · suffices - mult w₀ * Real.log (w₀ (x : K)) = 0 by
        rw [neg_mul, neg_eq_zero, ← hw] at this
        exact mult_log_place_eq_zero.mp this
      rw [← logEmbedding_sum_component, Finset.sum_eq_zero]
      exact fun w _ => congrFun h w
    · exact mult_log_place_eq_zero.mp (congrFun h ⟨w, hw⟩)
  · ext w
    rw [logEmbedding_component, h w.val, Real.log_one, mul_zero, Pi.zero_apply]

theorem logEmbedding_component_le {r : ℝ} {x : (𝓞 K)ˣ} (hr : 0 ≤ r) (h : ‖logEmbedding K x‖ ≤ r)
    (w : {w : InfinitePlace K // w ≠ w₀}) : |logEmbedding K x w| ≤ r := by
  lift r to NNReal using hr
  simp_rw [Pi.norm_def, NNReal.coe_le_coe, Finset.sup_le_iff, ← NNReal.coe_le_coe] at h
  exact h w (Finset.mem_univ _)

theorem log_le_of_logEmbedding_le {r : ℝ} {x : (𝓞 K)ˣ} (hr : 0 ≤ r) (h : ‖logEmbedding K x‖ ≤ r)
    (w : InfinitePlace K) : |Real.log (w x)| ≤ (Fintype.card (InfinitePlace K)) * r := by
  have tool : ∀ x : ℝ, 0 ≤ x → x ≤ mult w * x := fun x hx => by
      nth_rw 1 [← one_mul x]
      refine mul_le_mul ?_ le_rfl hx ?_
      all_goals { rw [mult]; split_ifs <;> norm_num }
  by_cases hw : w = w₀
  · have hyp := congr_arg (‖·‖) (logEmbedding_sum_component x).symm
    replace hyp := (le_of_eq hyp).trans (norm_sum_le _ _)
    simp_rw [norm_mul, norm_neg, Real.norm_eq_abs, Nat.abs_cast] at hyp
    refine (le_trans ?_ hyp).trans ?_
    · rw [← hw]
      exact tool _ (abs_nonneg _)
    · refine (Finset.sum_le_card_nsmul Finset.univ _  _
        (fun w _ => logEmbedding_component_le hr h w)).trans ?_
      rw [nsmul_eq_mul]
      refine mul_le_mul ?_ le_rfl hr (Fintype.card (InfinitePlace K)).cast_nonneg
      simp [Finset.card_univ]
  · have hyp := logEmbedding_component_le hr h ⟨w, hw⟩
    rw [logEmbedding_component, abs_mul, Nat.abs_cast] at hyp
    refine (le_trans ?_ hyp).trans ?_
    · exact tool _ (abs_nonneg _)
    · nth_rw 1 [← one_mul r]
      exact mul_le_mul (Nat.one_le_cast.mpr Fintype.card_pos) (le_of_eq rfl) hr (Nat.cast_nonneg _)

variable (K)

/-- The lattice formed by the image of the logarithmic embedding. -/
noncomputable def unitLattice : AddSubgroup ({w : InfinitePlace K // w ≠ w₀} → ℝ) :=
  AddSubgroup.map (logEmbedding K) ⊤

theorem unitLattice_inter_ball_finite (r : ℝ) :
    ((unitLattice K : Set ({ w : InfinitePlace K // w ≠ w₀} → ℝ)) ∩
      Metric.closedBall 0 r).Finite := by
  obtain hr | hr := lt_or_le r 0
  · convert Set.finite_empty
    rw [Metric.closedBall_eq_empty.mpr hr]
    exact Set.inter_empty _
  · suffices Set.Finite {x : (𝓞 K)ˣ | IsIntegral ℤ (x : K) ∧
        ∀ (φ : K →+* ℂ), ‖φ x‖ ≤ Real.exp ((Fintype.card (InfinitePlace K)) * r)} by
      refine (Set.Finite.image (logEmbedding K) this).subset ?_
      rintro _ ⟨⟨x, ⟨_, rfl⟩⟩, hx⟩
      refine ⟨x, ⟨x.val.prop, (le_iff_le _ _).mp (fun w => (Real.log_le_iff_le_exp ?_).mp ?_)⟩, rfl⟩
      · exact pos_iff.mpr (coe_ne_zero x)
      · rw [mem_closedBall_zero_iff] at hx
        exact (le_abs_self _).trans (log_le_of_logEmbedding_le hr hx w)
    refine Set.Finite.of_finite_image ?_ ((coe_injective K).injOn _)
    refine (Embeddings.finite_of_norm_le K ℂ
        (Real.exp ((Fintype.card (InfinitePlace K)) * r))).subset ?_
    rintro _ ⟨x, ⟨⟨h_int, h_le⟩, rfl⟩⟩
    exact ⟨h_int, h_le⟩

section span_top
-- To prove that the span over `ℝ` of the `unit_lattice` is equal to the full space, we construct
-- for each infinite place `w₁ ≠ w₀` an unit `u_w₁` of `K` such that, for all infinite places
-- `w` such that `w ≠ w₁`, we have `Real.log w (u_w₁) < 0` (and thus `Real.log w₁ (u_w₁) > 0`).
-- It follows then from a determinant computation (using `Matrix.det_ne_zero_of_neg`) that the
-- image by `logEmbedding` of these units is a `ℝ`-linearly independent family.
-- The unit `u_w₁` is obtained by construction a sequence `seq n` of nonzero algebraic integers
-- that is strictly decreasing at infinite places distinct from `w₁` and of norm `≤ B`. Since
-- there are finitely many ideals of norm `≤ B`, there exists two terms in the sequence defining
-- the same ideal and their quotient is the desired unit `u_w₁` (see `exists_unit`).

open NumberField.mixedEmbedding NNReal

-- See: https://github.com/leanprover/lean4/issues/2220
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

variable (w₁ : InfinitePlace K) {B : ℕ} (hB : minkowskiBound K < (convexBodyLtFactor K) * B)

/-- This result shows that there always exists a next term in the sequence. -/
theorem seq_next {x : 𝓞 K} (hx : x ≠ 0) :
    ∃ y : 𝓞 K, y ≠ 0 ∧ (∀ w, w ≠ w₁ → w y < w x) ∧ |Algebra.norm ℚ (y : K)| ≤ B := by
  let f : InfinitePlace K → ℝ≥0 :=
    fun w => ⟨(w x) / 2, div_nonneg (AbsoluteValue.nonneg _ _) (by norm_num)⟩
  suffices ∀ w, w ≠ w₁ → f w ≠ 0 by
    obtain ⟨g, h_geqf, h_gprod⟩ := adjust_f K B this
    obtain ⟨y, h_ynz, h_yle⟩ := exists_ne_zero_mem_ringOfIntegers_lt (f := g)
      (by rw [convexBodyLt_volume]; convert hB; exact congr_arg ((↑): NNReal → ENNReal) h_gprod)
    refine ⟨y, h_ynz, fun w hw => (h_geqf w hw ▸ h_yle w).trans ?_, ?_⟩
    · rw [← Rat.cast_le (K := ℝ), Rat.cast_coe_nat]
      calc
        _ = ∏ w : InfinitePlace K, w y ^ mult w := (prod_eq_abs_norm (y : K)).symm
        _ ≤ ∏ w : InfinitePlace K, (g w : ℝ) ^ mult w := by
          refine Finset.prod_le_prod ?_ ?_
          · exact fun _ _ => pow_nonneg (by positivity) _
          · exact fun w _ => pow_le_pow_of_le_left (by positivity) (le_of_lt (h_yle w)) (mult w)
        _ ≤ (B : ℝ) := by
          simp_rw [← NNReal.coe_pow, ← NNReal.coe_prod]
          exact le_of_eq (congr_arg toReal h_gprod)
    · refine div_lt_self ?_ (by norm_num)
      simp only [pos_iff, ne_eq, ZeroMemClass.coe_eq_zero, hx]
  intro _ _
  rw [ne_eq, Nonneg.mk_eq_zero, div_eq_zero_iff, map_eq_zero, not_or, ZeroMemClass.coe_eq_zero]
  exact ⟨hx, by norm_num⟩

/-- An infinite sequence of nonzero algebraic integers of `K` satisfying the following properties:
• `seq n` is nonzero;
• for `w : InfinitePlace K`, `w ≠ w₁ → w (seq n+1) < w (seq n)`;
• `∣norm (seq n)∣ ≤ B`. -/
def seq : ℕ → { x : 𝓞 K // x ≠ 0 }
  | 0 => ⟨1, by norm_num⟩
  | n + 1 =>
    ⟨(seq_next K w₁ hB (seq n).prop).choose, (seq_next K w₁ hB (seq n).prop).choose_spec.1⟩

/-- The terms of the sequence are nonzero. -/
theorem seq_ne_zero (n : ℕ) : (seq K w₁ hB n : K) ≠ 0 := by
  refine (map_ne_zero_iff (algebraMap (𝓞 K) K) ?_).mpr (seq K w₁ hB n).prop
  exact IsFractionRing.injective { x // x ∈ 𝓞 K } K

/-- The sequence is strictly decreasing at infinite places distinct from `w₁`. -/
theorem seq_antitone {n m : ℕ} (h : n < m) :
    ∀ w : InfinitePlace K, w ≠ w₁ → w (seq K w₁ hB m) < w (seq K w₁ hB n) := by
  induction m with
  | zero =>
      exfalso
      exact Nat.not_succ_le_zero n h
  | succ m m_ih =>
      intro w hw
      cases eq_or_lt_of_le (Nat.le_of_lt_succ h) with
      | inl hr =>
          rw [hr]
          exact (seq_next K w₁ hB (seq K w₁ hB m).prop).choose_spec.2.1 w hw
      | inr hr =>
          refine lt_trans ?_ (m_ih hr w hw)
          exact (seq_next K w₁ hB (seq K w₁ hB m).prop).choose_spec.2.1 w hw

/-- The terms of the sequence have norm bounded by `B`. -/
theorem seq_norm_bdd (n : ℕ) :
    1 ≤ Int.natAbs (Algebra.norm ℤ (seq K w₁ hB n : 𝓞 K)) ∧
      Int.natAbs (Algebra.norm ℤ (seq K w₁ hB n : 𝓞 K)) ≤ B := by
  cases n with
  | zero =>
      have : 1 ≤ B := by
        contrapose! hB
        simp only [Nat.lt_one_iff.mp hB, CharP.cast_eq_zero, mul_zero, zero_le]
      simp only [ne_eq, seq, _root_.map_one, Int.natAbs_one, le_refl, this, and_self]
  | succ n =>
      refine ⟨Nat.succ_le_iff.mpr (Int.natAbs_pos.mpr ?_), ?_⟩
      · exact Algebra.norm_ne_zero_iff.mpr (seq K w₁ hB n.succ).prop
      · rw [← Nat.cast_le (α := ℚ), Int.cast_natAbs, Int.cast_abs]
        change |algebraMap ℤ ℚ _| ≤ _
        rw [← Algebra.norm_localization ℤ (Sₘ := K) (nonZeroDivisors ℤ)]
        exact (seq_next K w₁ hB (seq K w₁ hB n).prop).choose_spec.2.2

/-- Construct an unit associated to the place `w₁`. The family, for `w₁ ≠ w₀`, formed by the
image by the `logEmbedding` of these units  is `ℝ`-linearly independent, see
`unit_lattice_span_eq_top`. -/
theorem exists_unit (w₁ : InfinitePlace K ) :
    ∃ u : (𝓞 K)ˣ, (∀ w : InfinitePlace K, w ≠ w₁ → Real.log (w u) < 0) := by
  obtain ⟨B, hB⟩ : ∃ B : ℕ, minkowskiBound K < (convexBodyLtFactor K) * B := by
    simp_rw [mul_comm]
    refine ENNReal.exists_nat_mul_gt ?_ ?_
    exact ne_of_gt (convexBodyLtFactor_pos K)
    exact ne_of_lt (minkowskiBound_lt_top K)
  rsuffices ⟨n, m, hnm, h⟩ : ∃ n m, n < m ∧
      (Ideal.span ({ (seq K w₁ hB n : 𝓞 K) }) = Ideal.span ({ (seq K w₁ hB m : 𝓞 K) }))
  · have hu := Ideal.span_singleton_eq_span_singleton.mp h
    refine ⟨hu.choose, fun w hw => Real.log_neg ?_ ?_⟩
    · simp only [pos_iff, ne_eq, ZeroMemClass.coe_eq_zero, ne_zero]
    · calc
        _ = w ((seq K w₁ hB m : K) * (seq K w₁ hB n : K)⁻¹) := by
          rw [← congr_arg ((↑) : (𝓞 K) → K) hu.choose_spec, mul_comm, Submonoid.coe_mul,
            ← mul_assoc, inv_mul_cancel (seq_ne_zero K w₁ hB n), one_mul]
        _ = w (seq K w₁ hB m) * w (seq K w₁ hB n)⁻¹ := _root_.map_mul _ _ _
        _ < 1 := by
          rw [map_inv₀, mul_inv_lt_iff (pos_iff.mpr (seq_ne_zero K w₁ hB n)), mul_one]
          exact seq_antitone K w₁ hB hnm w hw
  refine Set.Finite.exists_lt_map_eq_of_forall_mem
    (t := { I : Ideal (𝓞 K) | 1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ B })
    (fun n => ?_) ?_
  · rw [Set.mem_setOf_eq, Ideal.absNorm_span_singleton]
    exact seq_norm_bdd K w₁ hB n
  · rw [show { I : Ideal (𝓞 K) | 1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ B } =
          (⋃ n ∈ Set.Icc 1 B, { I : Ideal (𝓞 K) | Ideal.absNorm I = n }) by ext; simp]
    exact Set.Finite.biUnion (Set.finite_Icc _ _) (fun n hn => Ideal.finite_setOf_absNorm_eq hn.1)

theorem unitLattice_span_eq_top :
    Submodule.span ℝ (unitLattice K : Set ({w : InfinitePlace K // w ≠ w₀} → ℝ)) = ⊤ := by
  refine le_antisymm (le_top) ?_
  -- The standard basis
  let B := Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀}
  -- The image by log_embedding of the family of units constructed above
  let v := fun w : { w : InfinitePlace K // w ≠ w₀ } => logEmbedding K (exists_unit K w).choose
  -- To prove the result, it is enough to prove that the family `v` is linearly independent
  suffices B.det v ≠ 0 by
    rw [← isUnit_iff_ne_zero, ← is_basis_iff_det] at this
    rw [← this.2]
    exact Submodule.span_monotone (fun _ ⟨w, hw⟩ =>
      ⟨(exists_unit K w).choose, trivial, by rw [← hw]⟩)
  rw [Basis.det_apply]
  -- We use a specific lemma to prove that this determinant is nonzero
  refine det_ne_zero_of_sum_col_lt_diag (fun w => ?_)
  simp_rw [Real.norm_eq_abs, Basis.coePiBasisFun.toMatrix_eq_transpose, Matrix.transpose_apply]
  rw [← sub_pos, Finset.sum_congr rfl (fun x hx => abs_of_neg ?_), Finset.sum_neg_distrib,
    sub_neg_eq_add, Finset.sum_erase_eq_sub (Finset.mem_univ _), ← add_comm_sub]
  refine add_pos_of_nonneg_of_pos ?_ ?_
  · rw [sub_nonneg]
    exact le_abs_self _
  · rw [logEmbedding_sum_component (exists_unit K w).choose]
    refine mul_pos_of_neg_of_neg ?_ ((exists_unit K w).choose_spec _ w.prop.symm)
    rw [mult]; split_ifs <;> norm_num
  · refine mul_neg_of_pos_of_neg ?_ ((exists_unit K w).choose_spec x ?_)
    · rw [mult]; split_ifs <;> norm_num
    · exact Subtype.ext_iff_val.not.mp (Finset.ne_of_mem_erase hx)

end span_top

/-- The unit rank of the number field `K`, it is equal to `card (InfinitePlace K) - 1`. -/
def _root_.NumberField.Units.rank : ℕ := Fintype.card (InfinitePlace K) - 1

open FiniteDimensional

theorem unitLattice_discrete : DiscreteTopology (unitLattice K) := by
  refine discreteTopology_of_open_singleton_zero ?_
  refine isOpen_singleton_of_finite_mem_nhds 0 (s := Metric.closedBall 0 1) ?_ ?_
  · exact Metric.closedBall_mem_nhds _ (by norm_num)
  · refine Set.Finite.of_finite_image ?_ (Set.injOn_of_injective Subtype.val_injective _)
    convert unitLattice_inter_ball_finite K 1
    ext x
    refine ⟨?_, fun ⟨hx1, hx2⟩ => ⟨⟨x, hx1⟩, hx2, rfl⟩⟩
    rintro ⟨x, hx, rfl⟩
    exact ⟨Subtype.mem x, hx⟩

protected theorem finrank :
    finrank ℝ ({w : InfinitePlace K // w ≠ w₀} → ℝ) = Units.rank K := by
  simp only [finrank_fintype_fun_eq_card, Fintype.card_subtype_compl,
    Fintype.card_ofSubsingleton, rank]

theorem unitLattice_moduleFree : Module.Free ℤ (unitLattice K) := by
  have := unitLattice_discrete K
  exact Zlattice.module_free ℝ (unitLattice_span_eq_top K)

theorem unitLattice_moduleFinite : Module.Finite ℤ (unitLattice K) := by
  have := unitLattice_discrete K
  exact Zlattice.module_finite ℝ (unitLattice_span_eq_top K)

theorem unitLattice_rank : finrank ℤ (unitLattice K) = Units.rank K := by
  have := unitLattice_discrete K
  rw [← dirichlet.finrank]
  exact Zlattice.rank ℝ (unitLattice_span_eq_top K)

end dirichlet

variable [NumberField K]

/-- A basis of the quotient `(𝓞 K)ˣ ⧸ (torsion K)` seen as an additive ℤ-module. -/
def basisModTorsion : Basis (Fin (rank K)) ℤ (Additive ((𝓞 K)ˣ ⧸ (torsion K))) := by
  let f : (dirichlet.unitLattice K) ≃ₗ[ℤ] Additive ((𝓞 K)ˣ ⧸ (torsion K)) := by
    refine AddEquiv.toIntLinearEquiv ?_
    rw [dirichlet.unitLattice, ← AddMonoidHom.range_eq_map (dirichlet.logEmbedding K)]
    refine (QuotientAddGroup.quotientKerEquivRange (dirichlet.logEmbedding K)).symm.trans ?_
    refine (QuotientAddGroup.quotientAddEquivOfEq ?_).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective
        (MonoidHom.toAdditive (QuotientGroup.mk' (torsion K))) (fun x => ?_))
    · ext
      rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker, dirichlet.logEmbedding_eq_zero_iff,
        MonoidHom.toAdditive_apply_apply, ofMul_eq_zero, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      rfl
    · refine ⟨Additive.ofMul x.out', ?_⟩
      simp only [MonoidHom.toAdditive_apply_apply, toMul_ofMul, QuotientGroup.mk'_apply,
        QuotientGroup.out_eq']
      rfl
  have : Module.Free ℤ (Additive ((𝓞 K)ˣ ⧸ (torsion K))) :=
      (dirichlet.unitLattice_moduleFree K).of_equiv'  f
  have : Module.Finite ℤ (Additive ((𝓞 K)ˣ ⧸ (torsion K))) := by
    have := dirichlet.unitLattice_moduleFinite K
    exact Module.Finite.equiv f
  have : FiniteDimensional.finrank ℤ (Additive ((𝓞 K)ˣ ⧸ (torsion K))) = rank K := by
    rw [← LinearEquiv.finrank_eq f, dirichlet.unitLattice_rank]
  refine Basis.reindex (Module.Free.chooseBasis ℤ _) (Fintype.equivOfCardEq ?_)
  rw [← FiniteDimensional.finrank_eq_card_chooseBasisIndex, this, Fintype.card_fin]

/-- A fundamental system of units of `K`. The units of `fundSystem` are arbitrary lifts of the
units in `basisModTorsion`. -/
def fundSystem : Fin (rank K) → (𝓞 K)ˣ :=
  fun i => Quotient.out' (Additive.toMul (basisModTorsion K i))

theorem fun_eq_repr {x ζ : (𝓞 K)ˣ} {f : Fin (rank K) → ℤ} (hζ : ζ ∈ torsion K)
    (h : x = ζ * ∏ i, (fundSystem K i) ^ (f i)) :
    f = (basisModTorsion K).repr (Additive.ofMul ↑x) := by
  suffices Additive.ofMul ↑x = ∑ i, (f i) • (basisModTorsion K i) by
    rw [← (basisModTorsion K).repr_sum_self f, ← this]
  calc
    Additive.ofMul ↑x = ∑ i, (f i) • Additive.ofMul ↑(fundSystem K i) := by
                      rw [h, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr hζ, one_mul,
                        QuotientGroup.mk_prod, ofMul_prod]; rfl
                    _ = ∑ i, (f i) • (basisModTorsion K i) := by
                      simp_rw [fundSystem, QuotientGroup.out_eq', ofMul_toMul]

/-- Any unit `x` of `𝓞 K` can be written uniquely as a root of unity times the product of powers
of the units of the fundamental system. -/
theorem exist_unique_eq_mul_prod (x : (𝓞 K)ˣ) : ∃! (ζ : torsion K) (e : Fin (rank K) → ℤ),
    x = ζ * ∏ i, (fundSystem K i) ^ (e i) := by
  let ζ := x * (∏ i, (fundSystem K i) ^ ((basisModTorsion K).repr (Additive.ofMul ↑x) i))⁻¹
  have h_tors : ζ ∈ torsion K := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← ofMul_eq_zero,
      ofMul_mul, ofMul_inv, QuotientGroup.mk_prod, ofMul_prod]
    simp_rw [QuotientGroup.mk_zpow, ofMul_zpow, fundSystem, QuotientGroup.out_eq', ofMul_toMul]
    rw [add_eq_zero_iff_eq_neg, neg_neg]
    exact ((basisModTorsion K).sum_repr (Additive.ofMul ↑x)).symm
  refine ⟨⟨ζ, h_tors⟩, ?_, ?_⟩
  · refine ⟨((basisModTorsion K).repr (Additive.ofMul ↑x) : Fin (rank K) → ℤ), ?_, ?_⟩
    · simp only [_root_.inv_mul_cancel_right]
    · exact fun _ hf => fun_eq_repr K h_tors hf
  · rintro η ⟨_, hf, _⟩
    have f_eq := fun_eq_repr K η.prop hf
    simp_rw [f_eq] at hf
    ext1; dsimp only
    nth_rewrite 1 [hf]
    rw [_root_.mul_inv_cancel_right]

end NumberField.Units
