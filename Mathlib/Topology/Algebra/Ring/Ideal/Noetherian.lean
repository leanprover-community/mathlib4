/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Nailin Guan
-/
module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.KrullDimension.Basic

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Hausdorff-ness for Noetherian rings
-/

public section

open IsLocalRing Module

universe u

variable {R : Type u} [CommRing R] (I : Ideal R)

section

variable (M : Type*) [AddCommGroup M] [Module R M]

variable [IsNoetherianRing R] [Module.Finite R M]

lemma IsHausdorff.of_le_jacobson (h : I ≤ Ring.jacobson R) : IsHausdorff I M :=
  ⟨fun x hx ↦ (Ideal.iInf_pow_smul_eq_bot_of_le_jacobson I h).le (by simpa [SModEq.zero] using hx)⟩

theorem IsHausdorff.of_isLocalRing [IsLocalRing R] (h : I ≠ ⊤) : IsHausdorff I M :=
  of_le_jacobson I M ((le_maximalIdeal h).trans (ringJacobson_eq_maximalIdeal R).ge)

instance [IsLocalRing R] : IsHausdorff (maximalIdeal R) M :=
  .of_le_jacobson _ _ (ringJacobson_eq_maximalIdeal R).ge

lemma IsHausdorff.of_isTorsionFree [IsDomain R] [IsTorsionFree R M] (h : I ≠ ⊤) : IsHausdorff I M :=
  ⟨fun x hx ↦ (I.iInf_pow_smul_eq_bot_of_isTorsionFree h).le (by simpa [SModEq.zero] using hx)⟩

theorem IsHausdorff.of_isDomain [IsDomain R] (h : I ≠ ⊤) : IsHausdorff I R :=
  .of_isTorsionFree I R h

end

instance (priority := 100) {A : Type*} [CommRing A] [IsArtinianRing A] [IsLocalRing A] :
    IsAdicComplete (IsLocalRing.maximalIdeal A) A where
  prec' f hf := by
    obtain ⟨n, hn⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal A).mp ‹_›
    use f n; intro m
    by_cases h : m ≤ n
    · exact hf h
    specialize hf (show n ≤ m by lia)
    rw [hn, zero_smul, Ideal.zero_eq_bot, SModEq.bot] at hf
    rw [hf]

open Polynomial

section

variable {I} (n : ℕ) {J : Ideal R} {ι : Type u} {f : ι → reesAlgebra I}
  (span_eq : (Ideal.span (Set.range f)).map (reesAlgebraToAssociatedGraded I) =
    J.toAssociatedGraded I) (deg : ι → ℕ)

include span_eq

private lemma reesAlgebraToAssociatedGraded_monomial_mem_span
    {r : R} (mem_J : r ∈ J) (mem_pow : r ∈ I ^ n) :
    (reesAlgebraToAssociatedGraded I) ⟨(monomial n) r, reesAlgebra.monomial_mem.mpr mem_pow⟩ ∈
      Ideal.span (Set.range (⇑(reesAlgebraToAssociatedGraded I) ∘ f)):= by
  rw [Set.range_comp, ← Ideal.map_span, span_eq]
  apply Ideal.mem_map_of_mem
  simp only [Ideal.mem_comap, Subalgebra.coe_val, Ideal.mem_map_C_iff]
  intro m
  by_cases eq : m = n
  · simpa [eq]
  · simp only [coeff_monomial_of_ne _ eq, zero_mem]

variable [Fintype ι]

private noncomputable def coeffsOfMemAux {r : R} (mem_J : r ∈ J) (mem_pow : r ∈ I ^ n) :
    ι → (reesAlgebra I) :=
  (Function.surjInv Ideal.Quotient.mk_surjective).comp
    (Classical.choose (Ideal.mem_span_range_iff_exists_fun.mp
      (reesAlgebraToAssociatedGraded_monomial_mem_span n span_eq mem_J mem_pow)))

private noncomputable def coeffsOfMem {r : R} (mem_J : r ∈ J) (mem_pow : r ∈ I ^ n) : ι → R :=
  fun i ↦ if deg i ≤ n then (coeffsOfMemAux n span_eq mem_J mem_pow i).1.coeff (n - (deg i)) else 0

private lemma coeffsOfMemAux_spec {r : R} (mem_J : r ∈ J) (mem_pow : r ∈ I ^ n) :
    (reesAlgebraToAssociatedGraded I) ⟨monomial n r, reesAlgebra.monomial_mem.mpr mem_pow⟩ =
    (reesAlgebraToAssociatedGraded I) (∑ i, coeffsOfMemAux n span_eq mem_J mem_pow i * f i) := by
  simpa [coeffsOfMemAux, Function.surjInv_eq]
    using (Classical.choose_spec (Ideal.mem_span_range_iff_exists_fun.mp
      (reesAlgebraToAssociatedGraded_monomial_mem_span n span_eq mem_J mem_pow))).symm

private lemma coeffsOfMem_mem_pow {r : R} (mem_J : r ∈ J) (mem_pow : r ∈ I ^ n) (i : ι) :
    coeffsOfMem n span_eq deg mem_J mem_pow i ∈ I ^ (n - deg i) := by
  by_cases degle : deg i ≤ n
  · simpa [degle, coeffsOfMem, mem_reesAlgebra_iff] using
      (coeffsOfMemAux n span_eq mem_J mem_pow i).2 (n - deg i)
  · simp [degle, coeffsOfMem]

private lemma coeffsOfMem_eq_zero_of_lt {r : R} (mem_J : r ∈ J) (mem_pow : r ∈ I ^ n) (i : ι) :
    n < deg i → coeffsOfMem n span_eq deg mem_J mem_pow i = 0 := by
  simp only [coeffsOfMem, ite_eq_right_iff, ← not_le]
  tauto

private lemma sub_sum_coeffsOfMem_mem_pow {coeff : ι → R}
    (eq : ∀ i : ι, (f i).1 = monomial (deg i) (coeff i)){r : R} (mem_J : r ∈ J)
    (mem_pow : r ∈ I ^ n) :
    r - ∑ x : ι, coeffsOfMem n span_eq deg mem_J mem_pow x * coeff x ∈ I ^ (n + 1) := by
  have := coeffsOfMemAux_spec n span_eq mem_J mem_pow
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, mem_map_algebraMap_reesAlgebra_iff] at this
  have coeff_eq := this n
  simp only [AddSubgroupClass.coe_sub, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, eq,
    coeff_sub, coeff_monomial_same, finsetSum_coeff] at coeff_eq
  convert coeff_eq
  rw [← Polynomial.C_mul_X_pow_eq_monomial, ← mul_assoc]
  simp [coeff_mul_X_pow', coeffsOfMem]

end

lemma exists_coeffs_isAdicCauchy (J : Ideal R) (ι : Type u) [Fintype ι] (f : ι → reesAlgebra I)
    (deg : ι → ℕ) (coeff : ι → R) (memJ : ∀ i, coeff i ∈ J)
    (eq : ∀ i : ι, (f i).1 = monomial (deg i) (coeff i))
    (span_eq : (Ideal.span (Set.range f)).map (reesAlgebraToAssociatedGraded I) =
      J.toAssociatedGraded I) (r : R) (hr : r ∈ J) :
    ∃ (g : ι → ℕ → R), (∀ i, AdicCompletion.IsAdicCauchy I R (g i)) ∧
      ∀ n, r - ∑ x : ι, g x n * coeff x ∈ I ^ (n + 1) := by
  have memJ' (g' : ι → R) : r - ∑ x, g' x * coeff x ∈ J :=
    sub_mem hr (sum_mem (fun i _ ↦ (Ideal.mul_mem_left _ _ (memJ i))))
  let coeffs' (n : ℕ) : {f : (ι → R) // r - ∑ x, f x * coeff x ∈ I ^ (n + 1)} := by
    induction n with
    | zero => exact ⟨coeffsOfMem 0 span_eq deg hr (by simp),
        sub_sum_coeffsOfMem_mem_pow 0 span_eq deg eq hr (by simp)⟩
    | succ n c =>
      refine ⟨c + coeffsOfMem (n + 1) span_eq deg (memJ' c.1) c.2, ?_⟩
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, ← sub_sub]
      exact sub_sum_coeffsOfMem_mem_pow (n + 1) span_eq deg eq (memJ' c.1) c.2
  have coeffs'_spec_aux (n : ℕ) : (coeffs' (n + 1)).1 = (coeffs' n).1 +
    coeffsOfMem (n + 1) span_eq deg (memJ' (coeffs' n).1) (coeffs' n).2 := rfl
  have coeffs'_spec (n : ℕ) :
    ∀ i, (coeffs' (n + 1)).1 i - (coeffs' n).1 i ∈ I ^ (n + 1 - deg i) := by
    simpa [coeffs'_spec_aux]
      using coeffsOfMem_mem_pow (n + 1) span_eq deg (memJ' (coeffs' n).1) (coeffs' n).2
  let d := ∑ i, deg i
  use fun i n ↦ (coeffs' (d + n)).1 i
  refine ⟨fun i ↦ ?_, fun n ↦ Ideal.pow_le_pow_right (by omega) (coeffs' (d + n)).2⟩
  rw [AdicCompletion.isAdicCauchy_iff]
  intro n
  simp only [smul_eq_mul, Ideal.mul_top]
  rw [SModEq.comm, SModEq.sub_mem, ← add_assoc d n 1]
  have led : deg i ≤ d := Finset.single_le_sum (fun i _ ↦ Nat.zero_le _) (Finset.mem_univ i)
  have : n ≤ d + n + 1 - deg i := by omega
  exact Ideal.pow_le_pow_right this (coeffs'_spec (d + n) i)

lemma isNoetherianRing_of_isAdicComplete_of_fg [IsNoetherianRing (R ⧸ I)] (fg : I.FG)
    [IsAdicComplete I R] : IsNoetherianRing R := by
  apply (isNoetherianRing_iff_ideal_fg R).mpr (fun J ↦ ?_)
  have := isNoetherianRing_reesAlgebra_quotient fg
  obtain ⟨ι, f, deg, coeff, fin, eq, memJ, span_eq⟩ :=
    exists_monomial_span_of_toAssociatedGraded_fg I J (Ideal.fg_of_isNoetherianRing _)
  have : Fintype ι := Fintype.ofFinite ι
  have : Fintype (Set.range coeff) := Fintype.ofFinite _
  use (Set.range coeff).toFinset
  simp only [Set.coe_toFinset]
  apply le_antisymm
  · simp only [Ideal.span_le]
    intro x ⟨i, hi⟩
    simpa [← hi] using memJ i
  · intro j hj
    rcases exists_coeffs_isAdicCauchy I J ι f deg coeff memJ eq span_eq j hj with ⟨c, cauchy, hc⟩
    choose c_lim c_lim_spec using fun i ↦ ‹IsAdicComplete I R›.prec' (c i) (cauchy i)
    rw [Ideal.mem_span_range_iff_exists_fun]
    use c_lim
    rw [IsHausdorff.eq_iff_smodEq (I := I)]
    intro n
    trans ∑ i, (c i n) * coeff i
    · apply SModEq.sum (fun i _ ↦ ?_)
      rw [SModEq.comm, SModEq.sub_mem, ← sub_mul]
      apply Ideal.mul_mem_right
      simpa [SModEq.sub_mem] using c_lim_spec i n
    · simpa [smul_eq_mul, Ideal.mul_top, SModEq.comm, SModEq.sub_mem]
        using Ideal.pow_le_pow_right (Nat.le_succ n) (hc n)

lemma AdicCompletion.isNoetherianRing_of_fg [IsNoetherianRing (R ⧸ I)] (fg : I.FG) :
    IsNoetherianRing (AdicCompletion I R) := by
  let e : (AdicCompletion I R) ⧸ I.map (algebraMap R (AdicCompletion I R)) ≃+* R ⧸ I :=
    (Ideal.quotEquivOfEq (AdicCompletion.ker_evalOneₐ_eq_map I fg).symm).trans
    (RingHom.quotientKerEquivOfSurjective (AdicCompletion.evalOneₐ_surjective I))
  have := isNoetherianRing_of_ringEquiv _ e.symm
  have := AdicCompletion.isAdicComplete_self I fg
  exact isNoetherianRing_of_isAdicComplete_of_fg _ (fg.map (algebraMap R (AdicCompletion I R)))

instance [IsNoetherianRing R] : IsNoetherianRing (AdicCompletion I R) :=
  AdicCompletion.isNoetherianRing_of_fg I I.fg_of_isNoetherianRing

lemma AdicCompletion.ringKrullDim_eq [IsNoetherianRing R] [IsLocalRing R] :
    ringKrullDim (AdicCompletion (maximalIdeal R) R) = ringKrullDim R := by
  have : Nontrivial (AdicCompletion (maximalIdeal R) R ⧸
    (maximalIdeal R).map (algebraMap R (AdicCompletion (maximalIdeal R) R))) := by
    simpa [← AdicCompletion.maximalIdeal_eq_map] using Ideal.IsPrime.ne_top'
  have ht := (Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    (maximalIdeal R) (maximalIdeal (AdicCompletion (maximalIdeal R) R))).symm
  rw [Ideal.map_mk_eq_bot_of_le (le_of_eq AdicCompletion.maximalIdeal_eq_map)] at ht
  simp [← maximalIdeal_height_eq_ringKrullDim, ← ht]
