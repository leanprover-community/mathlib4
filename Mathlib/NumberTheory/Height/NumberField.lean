/-
Copyright (c) 2025 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Ralf Stephan
-/
module

public import Mathlib.NumberTheory.Height.Basic
public import Mathlib.NumberTheory.Height.Northcott
public import Mathlib.NumberTheory.NumberField.ProductFormula

import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Order.Hom.Lattice
import Mathlib.NumberTheory.Height.MvPolynomial
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-!
# Heights over number fields

We provide an instance of `Height.AdmissibleAbsValues` for algebraic number fields
and set up some API.

## Main results

* Heights on number fields satisfy the **Northcott property**: If `K` is a number field,
  then the set of elements of `K` of bounded (multiplicative or logarithmic) height is finite;
  see `NumberField.finite_setOf_mulHeight₁_le` and `NumberField.finite_setOf_logHeight₁_le`.
  We also provide instances for `Northcott (mulHeight₁ (K := K))` (which automatically leads
  also to `Northcott (logHeight₁ (K := K))`).

## TODO

When this file gets long, split the material on heights over `ℚ` off into a file `Rat.lean`.
-/

@[expose] public section

/-!
### Instance for number fields
-/

namespace NumberField

open Height

variable {K : Type*} [Field K] [NumberField K]

variable (K) in
/-- The infinite places of a number field `K` as a `Multiset` of absolute values on `K`,
with multiplicity given by `InfinitePlace.mult`. -/
noncomputable def multisetInfinitePlace : Multiset (AbsoluteValue K ℝ) :=
  .bind (.univ : Finset (InfinitePlace K)).val fun v ↦ .replicate v.mult v.val

@[simp]
lemma mem_multisetInfinitePlace {v : AbsoluteValue K ℝ} :
    v ∈ multisetInfinitePlace K ↔ IsInfinitePlace v := by
  simp [multisetInfinitePlace, Multiset.mem_replicate, isInfinitePlace_iff, eq_comm (a := v)]

set_option backward.isDefEq.respectTransparency false in
lemma count_multisetInfinitePlace_eq_mult [DecidableEq (AbsoluteValue K ℝ)] (v : InfinitePlace K) :
    (multisetInfinitePlace K).count v.val = v.mult := by
  have : DecidableEq (InfinitePlace K) := Subtype.instDecidableEq
  simpa only [multisetInfinitePlace, Multiset.count_bind, Finset.sum_map_val,
    Multiset.count_replicate, ← Subtype.ext_iff] using Fintype.sum_ite_eq' v ..

-- For the user-facing version, see `prod_archAbsVal_eq` below.
private lemma prod_multisetInfinitePlace_eq {M : Type*} [CommMonoid M] (f : AbsoluteValue K ℝ → M) :
    ((multisetInfinitePlace K).map f).prod = ∏ v : InfinitePlace K, f v.val ^ v.mult := by
  classical
  rw [Finset.prod_multiset_map_count]
  exact Finset.prod_bij' (fun w hw ↦ ⟨w, mem_multisetInfinitePlace.mp <| Multiset.mem_dedup.mp hw⟩)
    (fun v _ ↦ v.val) (fun _ _ ↦ Finset.mem_univ _) (fun v _ ↦ by simp [v.isInfinitePlace])
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) fun w hw ↦ by rw [count_multisetInfinitePlace_eq_mult ⟨w, _⟩]

noncomputable
instance instAdmissibleAbsValues : AdmissibleAbsValues K where
  archAbsVal := multisetInfinitePlace K
  nonarchAbsVal := {v | IsFinitePlace v}
  isNonarchimedean v hv := FinitePlace.add_le ⟨v, by simpa using! hv⟩
  hasFiniteMulSupport := FinitePlace.hasFiniteMulSupport
  product_formula {x} hx := private prod_multisetInfinitePlace_eq (· x) ▸ prod_abs_eq_one hx

open AdmissibleAbsValues

lemma prod_archAbsVal_eq {M : Type*} [CommMonoid M] (f : AbsoluteValue K ℝ → M) :
    (archAbsVal.map f).prod = ∏ v : InfinitePlace K, f v.val ^ v.mult :=
  prod_multisetInfinitePlace_eq f

lemma prod_nonarchAbsVal_eq {M : Type*} [CommMonoid M] (f : AbsoluteValue K ℝ → M) :
    (∏ᶠ v : nonarchAbsVal, f v.val) = ∏ᶠ v : FinitePlace K, f v.val :=
  rfl

open Finset Multiset in
lemma sum_archAbsVal_eq {M : Type*} [AddCommMonoid M] (f : AbsoluteValue K ℝ → M) :
    (archAbsVal.map f).sum = ∑ v : InfinitePlace K, v.mult • f v.val := by
  classical
  rw [sum_multiset_map_count]
  exact sum_bij' (⟨·, mem_multisetInfinitePlace.mp <| mem_dedup.mp ·⟩)
    _ (by simp) (by simp [InfinitePlace.isInfinitePlace, archAbsVal]) (by simp) (fun _ _ ↦ rfl)
    fun w hw ↦ by
      simp only [archAbsVal, mem_toFinset, mem_multisetInfinitePlace] at hw ⊢
      simp [count_multisetInfinitePlace_eq_mult ⟨w, hw⟩]

lemma sum_nonarchAbsVal_eq {M : Type*} [AddCommMonoid M] (f : AbsoluteValue K ℝ → M) :
    (∑ᶠ v : nonarchAbsVal, f v.val) = ∑ᶠ v : FinitePlace K, f v.val :=
  rfl

/-- This is the familiar definition of the multiplicative height on a number field. -/
lemma mulHeight₁_eq (x : K) :
    mulHeight₁ x =
      (∏ v : InfinitePlace K, max (v x) 1 ^ v.mult) * ∏ᶠ v : FinitePlace K, max (v x) 1 := by
  simp only [FinitePlace.coe_apply, InfinitePlace.coe_apply, Height.mulHeight₁_eq,
    prod_archAbsVal_eq, prod_nonarchAbsVal_eq fun v ↦ max (v x) 1]

open Real in
/-- This is the familiar definition of the logarithmic height on a number field. -/
lemma logHeight₁_eq (x : K) :
    logHeight₁ x =
      (∑ v : InfinitePlace K, v.mult * log⁺ (v x)) + ∑ᶠ v : FinitePlace K, log⁺ (v x) := by
  simp only [← nsmul_eq_mul, FinitePlace.coe_apply, InfinitePlace.coe_apply, Height.logHeight₁_eq,
    sum_archAbsVal_eq, sum_nonarchAbsVal_eq fun v ↦ log⁺ (v x)]

/-- This is the familiar definition of the multiplicative height on (nonzero) tuples
of number field elements. -/
lemma mulHeight_eq {ι : Type*} {x : ι → K} (hx : x ≠ 0) :
    mulHeight x =
      (∏ v : InfinitePlace K, (⨆ i, v (x i)) ^ v.mult) * ∏ᶠ v : FinitePlace K, ⨆ i, v (x i) := by
  simp only [FinitePlace.coe_apply, InfinitePlace.coe_apply, Height.mulHeight_eq hx,
    prod_archAbsVal_eq, prod_nonarchAbsVal_eq fun v ↦ ⨆ i, v (x i)]

variable (K) in
lemma totalWeight_eq_sum_mult : totalWeight K = ∑ v : InfinitePlace K, v.mult := by
  simp only [totalWeight]
  convert! sum_archAbsVal_eq (fun _ ↦ (1 : ℕ))
  · rw [← Multiset.sum_map_toList, ← Fin.sum_univ_fun_getElem, ← Multiset.length_toList,
      Fin.sum_const, Multiset.length_toList, smul_eq_mul, mul_one]
  · simp

variable (K) in
lemma totalWeight_eq_finrank : totalWeight K = Module.finrank ℚ K := by
  rw [totalWeight_eq_sum_mult, InfinitePlace.sum_mult_eq]

variable (K) in
@[grind! .]
lemma totalWeight_pos : 0 < totalWeight K := by
  have : Inhabited (InfinitePlace K) := Classical.inhabited_of_nonempty'
  simpa [totalWeight, archAbsVal, multisetInfinitePlace]
    using Fintype.sum_pos
      (Function.ne_iff.mpr ⟨default, (default : InfinitePlace K).mult_ne_zero⟩).pos

variable {ι : Type*} [Finite ι] {x : ι → 𝓞 K}

open IsDedekindDomain.HeightOneSpectrum Ideal FinitePlace Finite in
-- This statement is a step in the proof of the next one, which is strictly stronger.
private lemma absNorm_mul_finprod_finitePlace_eq_one_aux [Nonempty ι] (hx : ∀ i, x i ≠ 0) :
    (span <| Set.range x).absNorm * ∏ᶠ v : FinitePlace K, ⨆ i, v (x i) = 1 := by
  have H j : span {x j} ≠ ⊥ := mt span_singleton_eq_bot.mp (hx j)
  have hx' : ⨆ i, span {x i} ≠ ⊥ :=
    iSup_eq_bot.not.mpr <| not_forall.mpr ⟨Classical.ofNonempty, H _⟩
  rw [span_range_eq_iSup, ← finprod_finitePlace_pow_multiplicity hx',
    map_finprod _ <| hasFiniteMulSupport_fun_pow_multiplicity hx' (·), Nat.cast_finprod',
    ← finprod_mul_distrib ?hf <| .iSup (FinitePlace.hasFiniteMulSupport <| mod_cast hx ·)]
  case hf =>
    simp only [map_pow, Nat.cast_pow]
    exact hasFiniteMulSupport_fun_pow_multiplicity hx' fun v ↦ (v.absNorm : ℝ)
  refine finprod_eq_one_of_forall_eq_one fun v ↦ ?_
  have hn := absNorm_eq_zero_iff.not.mpr v.maximalIdeal.ne_bot
  have h {m : ℕ} : (0 : ℝ) < ↑(absNorm v.maximalIdeal.asIdeal ^ m) := by positivity
  rw [multiplicity_iSup _ H, map_pow, mul_eq_one_iff_inv_eq₀ h.ne',
    map_iInf_of_monotone (fun _ ↦ multiplicity ..) (pow_right_monotone <| by lia),
    map_iInf_of_monotone _ Nat.mono_cast,
    map_iInf_of_antitoneOn antitoneOn_inv_pos fun _ ↦ Set.mem_setOf.mpr h]
  refine iSup_congr fun i ↦ ?_
  rw [← mul_eq_one_iff_inv_eq₀ h.ne', mul_comm, Nat.cast_pow]
  exact apply_mul_absNorm_pow_eq_one v (hx i)

-- TODO: Generalize the following to integral closures of `ℤ` in `K` in place of `𝓞 K`.
open Ideal RingOfIntegers in
/-- This statement is equivalent to the fact that the "finite part" of the multiplicative
height of a (non-zero) tuple `x` is the inverse of the absolute norm of the ideal generated
by the values of `x`. We state it in a way that avoids taking an inverse. -/
lemma absNorm_mul_finprod_finitePlace_eq_one (hx : x ≠ 0) :
    (span <| Set.range x).absNorm * ∏ᶠ v : FinitePlace K, ⨆ i, v (x i) = 1 := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
  let i' : { j // (x j : K) ≠ 0 } := ⟨i₀, mod_cast hi₀⟩
  have : Nonempty _ := .intro i'
  have hI : span (Set.range x) = span (Set.range fun i : { j // (x j : K) ≠ 0 } ↦ x i.val) := by
    convert span_range_eq_span_range_support x <;> norm_cast
  have hx₀ : (fun i ↦ (x i : K)) ≠ 0 := Function.ne_iff.mpr ⟨_, i'.prop⟩
  simp_rw [Finite.iSup_eq_iSup_subtype hx₀, hI]
  exact absNorm_mul_finprod_finitePlace_eq_one_aux fun j ↦ mod_cast j.prop

end NumberField

/-!
### The Northcott property for heights on number fields

We show that a number field `K` has the **Northcott property** with respect to the multiplicative
and with respect to the logarithmic height, i.e., for any `B : ℝ` the set of elements `x : K`
such that `mulHeight₁ x ≤ B` (resp., `logHeight₁ x ≤ B`) is finite.
See `NumberField.finite_setOf_mulHeight₁_le` and `NumberField.finite_setOf_logHeight₁_le`.

The main idea of the proof is as follows. We show that for every `x : K` there is `n : ℕ` such that
`n * x` is an algebraic integer and `n ≤ mulHeight₁ x`; see `NumberField.exists_nat_le_mulHeight₁`.
We also show that the set of `a : 𝓞 K` such that `mulHeight₁ (a / n)` is bounded is finite;
see `NumberField.finite_setOf_prod_infinitePlace_iSup_le`. The result for the multiplicative height
follows by combining these two ingredients, and the result for the logarithmic height follows
from that for any field with a family of admissible absolute values
(see `Mathlib.NumberTheory.Height.Northcott`).
-/

section Northcott

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

section withIdeal

open Ideal

private lemma relIndex_span_span_nat_mul (m : ℕ) {n : ℕ} (hn : n ≠ 0) (a : 𝓞 K) :
    (span {(m : 𝓞 K)}).toAddSubgroup.relIndex (span {↑m, a}).toAddSubgroup =
      (span {(n * m : 𝓞 K)}).toAddSubgroup.relIndex (span {↑(n * m), n * a}).toAddSubgroup := by
  let f : 𝓞 K →ₗ[𝓞 K] 𝓞 K := .mulLeft _ n
  have hf : Function.Injective (f : 𝓞 K →+ 𝓞 K) :=
    (injective_iff_map_eq_zero f).mpr fun _ _ ↦ by simp_all [f]
  have H₁ : span {(n * m : 𝓞 K)} = Submodule.map f (span {↑m}) := by
    simp [LinearMap.map_span, f]
  have H₂ : span {↑(n * m), n * a} = Submodule.map f (span {↑m, a}) := by
    simp [LinearMap.map_span, f, Set.image_pair]
  rw [H₁, H₂]
  exact AddSubgroup.relIndex_map_map_of_injective _ _ hf |>.symm

private lemma relIndex_span_span_eq_relIndex_span_span {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    {a b : 𝓞 K} (h : n * a = m * b) :
    (span {(m : 𝓞 K)}).toAddSubgroup.relIndex (span {↑m, a}).toAddSubgroup =
      (span {(n : 𝓞 K)}).toAddSubgroup.relIndex (span {↑n, b}).toAddSubgroup := by
  refine (relIndex_span_span_nat_mul m hn a).trans ?_
  rw [mul_comm, mul_comm n, h]
  exact (relIndex_span_span_nat_mul n hm b).symm

open Module AddSubgroup LinearMap in
lemma exists_nat_ne_zero_exists_integer_mul_eq_and_absNorm_span_eq_pow (x : K) :
    ∃ n : ℕ, n ≠ 0 ∧ ∃ a : 𝓞 K, n * x = a ∧
      (span {(n : 𝓞 K), a}).absNorm = n ^ (Module.finrank ℚ K - 1) := by
  have hx : IsAlgebraic ℤ x := IsFractionRing.isAlgebraic_iff ℤ _ _ |>.mpr (.of_finite ℚ x)
  obtain ⟨m, r, hm, hmr⟩ := hx.exists_nsmul_eq (𝓞 K)
  rw [← RingOfIntegers.coe_eq_algebraMap r] at hmr
  set n := (span {(m : 𝓞 K)}).toAddSubgroup.relIndex (span {(m : 𝓞 K), r}).toAddSubgroup with hndef
  have hn : n ≠ 0 := isFiniteRelIndex (by simp [hm]) _ |>.relIndex_ne_zero
  obtain ⟨a, ha'⟩ : ∃ a, m * a = n * r := by
    have : n • r ∈ span {(m : 𝓞 K)} :=
      (span {(m : 𝓞 K)}).toAddSubgroup.nsmul_relIndex_mem <| Submodule.mem_span_of_mem <| by grind
    simpa [mem_span_singleton', mul_comm] using this
  have ha : n * x = a := by
    refine mul_left_cancel₀ (mod_cast hm : (m : K) ≠ 0) ?_
    rw [mul_left_comm, ← nsmul_eq_mul m, hmr]
    exact_mod_cast ha'.symm
  refine ⟨n, hn, a, ha, mul_left_cancel₀ hn ?_⟩
  nth_rewrite 1 [hndef]
  rw [absNorm_eq_index, mul_pow_sub_one finrank_pos.ne', ← RingOfIntegers.rank,
    ← absNorm_span_natCast, absNorm_eq_index, ← relIndex_span_span_eq_relIndex_span_span hn hm ha']
  exact relIndex_mul_index <| Submodule.toAddSubgroup_mono <| span_mono <| by grind

open Height in
private lemma one_le_pow_totalWeight_mul_finprod {n : ℕ} (hn : n ≠ 0) (a : 𝓞 K) :
    1 ≤ (n ^ totalWeight K : ℝ) * ∏ᶠ (v : FinitePlace K), ⨆ i, v (![↑a, ↑n] i) := by
  have Hw : (0 : ℝ) < n ^ totalWeight K := by positivity
  rw_mod_cast [totalWeight_eq_finrank, ← RingOfIntegers.rank, ← absNorm_span_natCast] at Hw ⊢
  rw [← absNorm_mul_finprod_finitePlace_eq_one (show ![a, n] ≠ 0 by simp [hn])]
  gcongr
  · exact finprod_nonneg fun _ ↦ Real.iSup_nonneg_of_nonnegHomClass ..
  · exact Nat.le_of_dvd Hw <| absNorm_dvd_absNorm_of_le <| span_mono <| by simp
  · apply le_of_eq; congr; ext; congr; ext i; fin_cases i <;> simp

end withIdeal

open Height

section withFinset

open Finset

/-- If `x : K` (for a number field `K`), then we can find a nonzero `n : ℕ` such that
`n ≤ mulHeight₁ x` and `n * x` is integral. I.e., the denominator of `x` can be bounded by
its multplicative height. -/
-- TODO: Use this to show `natDenominator x ≤ mulHeight₁ x` once #39872 is merged.
lemma exists_nat_le_mulHeight₁ (x : K) :
    ∃ n : ℕ, n ≠ 0 ∧ n ≤ mulHeight₁ x ∧ IsIntegral ℤ (n * x) := by
  obtain ⟨n, hn, a, ha₁, ha₂⟩ := exists_nat_ne_zero_exists_integer_mul_eq_and_absNorm_span_eq_pow x
  refine ⟨n, hn, ?_, ha₁ ▸ a.isIntegral_coe⟩
  rw [← totalWeight_eq_finrank] at ha₂
  have hv (i : Fin 2) : (![a, n] i : K) = ![(a : K), n] i := by fin_cases i <;> rfl
  rw [← mul_div_cancel_left₀ x (mod_cast hn : (n : K) ≠ 0), ha₁, mulHeight₁_div_eq_mulHeight,
    mulHeight_eq (by simp [hn])]
  refine le_of_mul_le_mul_left ?_ (show (0 : ℝ) < n ^ (totalWeight K - 1) by positivity)
  have : n ^ (totalWeight K - 1) * ∏ᶠ (v : FinitePlace K), ⨆ i, v (![(a : K), n] i) = 1 := by
    simpa [ha₂, hv] using absNorm_mul_finprod_finitePlace_eq_one (show ![a, n] ≠ 0 by simp [hn])
  rw [pow_sub_one_mul (totalWeight_pos K).ne', mul_left_comm, this, mul_one,
    totalWeight_eq_sum_mult, ← prod_pow_eq_pow_sum univ]
  refine prod_le_prod (fun _ _ ↦ by positivity) fun v _ ↦ ?_
  gcongr
  exact Finite.le_ciSup_of_le 1 <| by simp

private lemma infinitePlace_apply_le_of_prod_le {n : ℕ} (hn : n ≠ 0) (B : ℝ) {x : 𝓞 K}
    (h : ∏ v : InfinitePlace K, (⨆ i, v (![(x : K), n] i)) ^ v.mult ≤ B) (v : InfinitePlace K) :
    v x ≤ B / n ^ (totalWeight K - 1) := by
  classical
  rw [le_div_iff₀' (by positivity)]
  have hv (v : InfinitePlace K) : n ≤ ⨆ i, v (![(x : K), n] i) := Finite.le_ciSup_of_le 1 <| by simp
  calc
    _ ≤ n ^ (totalWeight K - 1) * ⨆ i, v (![(x : K), n] i) := by
      gcongr; exact Finite.le_ciSup_of_le 0 le_rfl
    _ ≤ (∏ v' ∈ univ.erase v, (⨆ i, v' (![↑x, ↑n] i)) ^ v'.mult) *
         (⨆ i, v (![↑x, ↑n] i)) ^ (v.mult - 1) * ⨆ i, v (![(x : K), n] i) := by
      gcongr
      · exact Real.iSup_nonneg_of_nonnegHomClass ..
      · refine mul_le_mul_iff_left₀ ((Nat.cast_pos (α := ℝ)).mpr hn.pos) |>.mp ?_
        rw [pow_sub_one_mul (totalWeight_pos K).ne', totalWeight_eq_sum_mult, ← prod_pow_eq_pow_sum,
          ← prod_erase_mul _ _ (mem_univ v), ← pow_sub_one_mul v.mult_ne_zero, ← mul_assoc]
        gcongr
        · exact prod_nonneg fun _ _ ↦ pow_nonneg (Real.iSup_nonneg_of_nonnegHomClass ..) _
        all_goals exact hv _
    _ ≤ B := by
      rwa [mul_assoc, pow_sub_one_mul v.mult_ne_zero, prod_erase_mul _ _ (mem_univ v)]

end withFinset

lemma finite_setOf_prod_infinitePlace_iSup_le {n : ℕ} (hn : n ≠ 0) (B : ℝ) :
    {x : 𝓞 K | ∏ v : InfinitePlace K, (⨆ i, v (![(x : K), n] i)) ^ v.mult ≤ B}.Finite := by
  set B' := B / n ^ (totalWeight K - 1)
  suffices Set.BijOn ((↑) : 𝓞 K → K) {x | ∀ (v : InfinitePlace K), v x ≤ B'}
      {x | IsIntegral ℤ x ∧ ∀ (φ : K →+* ℂ), ‖φ x‖ ≤ B'} from
    this.finite_iff_finite.mpr (Embeddings.finite_of_norm_le K ℂ B') |>.subset
      fun _ _ ↦ by grind [infinitePlace_apply_le_of_prod_le hn B]
  refine .mk (fun x hx ↦ ?_) (fun _ _ _ _ ↦ RingOfIntegers.ext) fun a ha ↦ ?_ <;>
    simp only [Set.mem_image, Set.mem_setOf_eq] at *
  · exact ⟨x.isIntegral_coe, fun φ ↦ hx <| .mk φ⟩
  · rw [← mem_integralClosure_iff ℤ K] at ha
    exact ⟨⟨a, ha.1⟩, fun v ↦ v.norm_embedding_eq a ▸ ha.2 v.embedding, rfl⟩

/-- The set of `a : 𝓞 K` such that `mulHeight₁ (a / n) = mulHeight ![a, n]` is bounded
(for some given nonzero `n : ℕ`) is finite. -/
lemma finite_setOf_mulHeight_nat_le {n : ℕ} (hn : n ≠ 0) (B : ℝ) :
    {a : 𝓞 K | mulHeight ![(a : K), n] ≤ B}.Finite := by
  suffices {a : 𝓞 K | mulHeight ![(a : K), n] ≤ B} ⊆
      {a | ∏ v : InfinitePlace K, (⨆ i, v (![(a : K), n] i)) ^ v.mult ≤ n ^ totalWeight K * B} from
    (finite_setOf_prod_infinitePlace_iSup_le hn _).subset this
  refine Set.setOf_subset_setOf_of_imp fun a ha ↦ ?_
  rw [mulHeight_eq <| by simp [hn], mul_comm] at ha
  grw [← ha, ← mul_assoc, ← one_le_pow_totalWeight_mul_finprod hn, one_mul]
  -- nonnegativity side goal
  exact Finset.prod_nonneg fun _ _ ↦ pow_nonneg (Real.iSup_nonneg_of_nonnegHomClass ..) _

variable (K) in
/- The set of `x : K` such that `mulHeight₁ x` is bounded and `n * x` is integral
(for some given nonzero `n : ℕ`) is finite.
This is a stepping stone for the proof of the next result, which is strictly stronger. -/
private lemma finite_setOf_isIntegral_nat_mul_and_mulHeight₁_le {n : ℕ} (hn : n ≠ 0) (B : ℝ) :
    {x : K | IsIntegral ℤ (n * x) ∧ mulHeight₁ x ≤ B}.Finite := by
  have hn' : (n : K) ≠ 0 := mod_cast hn
  suffices Set.BijOn (fun a : 𝓞 K ↦ (a / n : K)) {a | mulHeight ![(a : K), n] ≤ B}
      {x | IsIntegral ℤ (n * x) ∧ mulHeight₁ x ≤ B} from
    this.finite_iff_finite.mp <| finite_setOf_mulHeight_nat_le hn B
  refine .mk (fun a ha ↦ ?_) (fun a _ b _ h ↦ ?_) fun x ⟨hx₁, hx₂⟩ ↦ ?_
  · simp only [Set.mem_setOf_eq] at ha ⊢
    rw [mul_div_cancel₀ (a : K) hn', mulHeight₁_div_eq_mulHeight]
    exact ⟨a.isIntegral_coe, ha⟩
  · rwa [div_left_inj' hn', RingOfIntegers.eq_iff] at h
  · simp only [Set.mem_setOf_eq, Set.mem_image]
    obtain ⟨a, ha⟩ : ∃ a : 𝓞 K, n * x = a := ⟨⟨_, hx₁⟩, rfl⟩
    refine ⟨a, ?_, (EuclideanDomain.eq_div_of_mul_eq_right hn' ha).symm⟩
    rwa [← ha, ← mulHeight₁_div_eq_mulHeight, mul_div_cancel_left₀ x hn']

variable (K) in
/-- A number field `K` satisfies the **Northcott property**:
The set of elements of bounded multiplicative height is finite. -/
theorem finite_setOf_mulHeight₁_le (B : ℝ) : {x : K | mulHeight₁ x ≤ B}.Finite := by
  have H : {x : K | mulHeight₁ x ≤ B} =
      ⋃ n : Fin ⌊B⌋₊, {x : K | IsIntegral ℤ ((n + 1) * x) ∧ mulHeight₁ x ≤ B} := by
    ext x : 1
    obtain ⟨n, hn₀, hn₁, hn⟩ := exists_nat_le_mulHeight₁ x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_and_right, iff_and_self]
    refine fun h ↦ ⟨⟨n - 1, by grind [Nat.le_floor <| hn₁.trans h]⟩, ?_⟩
    rwa [← Nat.cast_add_one, Nat.sub_one_add_one hn₀]
  rw [H]
  exact Set.finite_iUnion fun n ↦
    mod_cast finite_setOf_isIntegral_nat_mul_and_mulHeight₁_le K (Nat.zero_ne_add_one n).symm B

instance : Northcott (mulHeight₁ (K := K)) where
  finite_le := finite_setOf_mulHeight₁_le K

variable (K) in
/-- A number field `K` satisfies the **Northcott property**:
The set of elements of bounded logarithmic height is finite. -/
theorem finite_setOf_logHeight₁_le (B : ℝ) :
    {x : K | logHeight₁ x ≤ B}.Finite :=
  Northcott.finite_le B

end NumberField

end Northcott

/-!
### Positivity extension for totalWeight on number fields
-/

namespace Mathlib.Meta.Positivity

open Lean.Meta Qq

/-- Extension for the `positivity` tactic: `Height.totalWeight` is positive for number fields. -/
@[positivity Height.totalWeight _]
meta def evalHeightTotalWeight : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℕ), ~q(@Height.totalWeight $K $KF $KA) =>
    -- Check whether there is a `NumberField` instance for `$K` around.
    match ← trySynthInstanceQ q(NumberField $K) with
    | .some _inst =>
      assertInstancesCommute
      return .positive q(NumberField.totalWeight_pos $K)
    | _ => throwError "field in Height.totalWeight not known to be a number field"
  | _, _, _ => throwError "not Height.totalWeight"

end Mathlib.Meta.Positivity

/-!
### Heights over the rational numbers

We show that the `Height.mulHeight` of a tuple of coprime integers (considered as rational numbers)
equals the maximum of their absolute values and that the `Height.mulHeight₁` of a rational
number is the maximum of the absolute value of the numerator and the denominator.
We add the corresponding results for logarithmic heights.
-/

namespace Rat

open NumberField Height

section tuples

variable {ι : Type*} [Fintype ι] [Nonempty ι] {x : ι → ℤ}

/-- The term corresponding to a finite place in the definition of the multiplicative height
of a tuple of rational numbers equals `1` if the tuple consists of coprime integers. -/
lemma iSup_finitePlace_apply_eq_one_of_gcd_eq_one (v : FinitePlace ℚ) (hx : Finset.univ.gcd x = 1) :
    ⨆ i, v (x i) = 1 := by
  have hv : IsNonarchimedean (v ·) := FinitePlace.add_le v
  have H (n : ℤ) : v n ≤ 1 := IsNonarchimedean.apply_intCast_le_one hv
  obtain ⟨f, hf⟩ := Finset.gcd_eq_sum_mul .univ x
  apply_fun v at hf
  simp_rw [hx, Int.cast_one, map_one, Int.cast_sum, Int.cast_mul] at hf
  replace hf := hf.trans_le hv.apply_sum_univ_le
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i ↦ v (x i * f i))
  rw [← hi, map_mul] at hf
  replace hf : 1 ≤ v (x i) := hf.trans <| mul_le_of_le_one_right (apply_nonneg v _) (H _)
  exact le_antisymm (ciSup_le (H <| x ·)) <| Finite.le_ciSup_of_le i hf

open AdmissibleAbsValues in
/-- The multiplicative height of a tuple of rational numbers that consists of coprime integers
is the maximum of the absolute values of the entries. -/
lemma mulHeight_eq_max_abs_of_gcd_eq_one (hx : Finset.univ.gcd x = 1) :
    mulHeight (((↑) : ℤ → ℚ) ∘ x) = ⨆ i, |x i| := by
  have hx₀ : Int.cast ∘ x ≠ (0 : ι → ℚ) := by
    contrapose! hx
    rw [Function.comp_eq_zero_iff x intCast_injective Rat.intCast_zero] at hx
    rw [hx, Finset.gcd_eq_zero_iff.mpr (by simp)]
    exact zero_ne_one
  simp_rw [Finite.map_iSup_of_monotone _ Int.cast_mono, NumberField.mulHeight_eq hx₀,
    infinitePlace_apply]
  simp [finprod_eq_one_of_forall_eq_one (iSup_finitePlace_apply_eq_one_of_gcd_eq_one · hx)]

open Real in
/-- The logarithmic height of a tuple of rational numbers that consists of coprime integers
is the logarithm of the maximum of the absolute values of the entries. -/
lemma logHeight_eq_max_abs_of_gcd_eq_one (hx : Finset.univ.gcd x = 1) :
    logHeight (((↑) : ℤ →  ℚ) ∘ x) = log ↑(⨆ i, |x i|) := by
  rw [logHeight_eq_log_mulHeight, mulHeight_eq_max_abs_of_gcd_eq_one hx]

end tuples

section mulHeight₁

lemma mulHeight_self_one_eq_mulHeight_num_den (q : ℚ) :
    mulHeight ![q, 1] = mulHeight ![(q.num : ℚ), q.den] := by
  have hq₀ : (q.den : ℚ) ≠ 0 := mod_cast q.den_nz
  rw [← mulHeight_smul_eq_mulHeight _ hq₀]
  simp

/-- The multiplicative height of a rational number is the maximum of the absolute value of
its numerator and its denominator. -/
lemma mulHeight₁_eq_max (q : ℚ) : mulHeight₁ q = max q.num.natAbs q.den := by
  rw [mulHeight₁_eq_mulHeight, mulHeight_self_one_eq_mulHeight_num_den, ← intCast_natCast q.den]
  have : (.univ : Finset (Fin 2)).gcd ![q.num, q.den] = 1 := by
    simpa [Finset.univ_fin2, Int.normalize_coe_nat, ← Int.coe_gcd q.num q.den] using
      Int.isCoprime_iff_gcd_eq_one.mp <| isCoprime_num_den q
  convert! mulHeight_eq_max_abs_of_gcd_eq_one this
  · ext i; fin_cases i <;> simp
  · rw [← Int.cast_natCast, Int.cast_inj]
    push_cast
    refine le_antisymm (max_le ?_ ?_) <| ciSup_le fun i ↦ ?_
    · exact Finite.le_ciSup_of_le 0 <| by simp
    · exact Finite.le_ciSup_of_le 1 <| by simp
    · fin_cases i <;> simp

open Real in
/-- The logarithmic height of a rational number is the logarithm of the maximum of the absolute
value of its numerator and its denominator. -/
lemma logHeight₁_eq_log_max (q : ℚ) : logHeight₁ q = log ↑(max q.num.natAbs q.den) := by
  rw [logHeight₁_eq_log_mulHeight₁, mulHeight₁_eq_max]

/-- The multiplicative height of a positive natural number `n` cast to `ℚ` equals `n`. -/
theorem mulHeight₁_natCast (n : ℕ) [NeZero n] :
    mulHeight₁ (n : ℚ) = n := by
  simp [mulHeight₁_eq_max, show 1 ≤ n by grind [NeZero.ne n]]

/-- The logarithmic height of a positive natural number `n` cast to `ℚ` equals `log n`. -/
theorem logHeight₁_natCast (n : ℕ) [NeZero n] :
    logHeight₁ (n : ℚ) = Real.log n := by
  simp [logHeight₁_eq_log_mulHeight₁, mulHeight₁_natCast n]

end mulHeight₁

end Rat

end
