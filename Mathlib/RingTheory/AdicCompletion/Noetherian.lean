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

lemma exists_coeffs_sub_mem (n : ℕ) (J : Ideal R) (ι : Type u) [Fintype ι] (f : ι → reesAlgebra I)
    (deg : ι → ℕ) (coeff : ι → R) (eq : ∀ i : ι, (f i).1 = monomial (deg i) (coeff i))
    (span_eq : (Ideal.span (Set.range f)).map (reesAlgebraToAssociatedGraded I) =
      J.toAssociatedGraded I)
    (r : R) (rmem_J : r ∈ J) (rmem_pow : r ∈ I ^ n) : ∃ (coeff' : ι → R),
    (∀ i : ι, coeff' i ∈ I ^ (n - deg i)) ∧ (∀ i : ι, deg i > n → coeff' i = 0) ∧
      r - ∑ x : ι, coeff' x * coeff x ∈ I ^ (n + 1) := by
  have : (reesAlgebraToAssociatedGraded I) ⟨monomial n r, reesAlgebra.monomial_mem.mpr rmem_pow⟩ ∈
    J.toAssociatedGraded I := by
    apply Ideal.mem_map_of_mem
    simp only [Ideal.mem_comap, Subalgebra.coe_val, Ideal.mem_map_C_iff]
    intro m
    by_cases eq : m = n
    · simpa [eq]
    · simp only [coeff_monomial_of_ne _ eq, zero_mem]
  rw [← span_eq, Ideal.map_span, ← Set.range_comp, Ideal.mem_span_range_iff_exists_fun] at this
  rcases this with ⟨c, hc⟩
  choose c' c'_spec using fun i ↦ (Ideal.Quotient.mk_surjective (c i))
  have : (reesAlgebraToAssociatedGraded I) ⟨monomial n r, reesAlgebra.monomial_mem.mpr rmem_pow⟩ =
    (reesAlgebraToAssociatedGraded I) (∑ i, c' i * f i) := by simp [← hc, c'_spec]
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, mem_map_algebraMap_reesAlgebra_iff] at this
  have coeff_eq := this n
  simp only [AddSubgroupClass.coe_sub, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, eq,
    coeff_sub, coeff_monomial_same, finsetSum_coeff] at coeff_eq
  let coeff' : ι → R := fun i ↦ if deg i ≤ n then (c' i).1.coeff (n - (deg i)) else 0
  have : ∑ i, ((c' i).1 * (monomial (deg i)) (coeff i)).coeff n = ∑ i, (coeff' i) * (coeff i) := by
    congr
    ext i
    rw [← Polynomial.C_mul_X_pow_eq_monomial, ← mul_assoc]
    simp [coeff_mul_X_pow', coeff']
  rw [this] at coeff_eq
  refine ⟨coeff', fun i ↦ ?_, fun i hi ↦ ?_, coeff_eq⟩
  · by_cases degle : deg i ≤ n
    · simpa [degle, coeff'] using (mem_reesAlgebra_iff I _).mp (c' i).2 (n - deg i)
    · simp [degle, coeff']
  · simp [coeff', hi]

lemma exists_coeffs_isAdicCauchy (J : Ideal R) (ι : Type u) [Fintype ι] (f : ι → reesAlgebra I)
    (deg : ι → ℕ) (coeff : ι → R) (memJ : ∀ i, coeff i ∈ J)
    (eq : ∀ i : ι, (f i).1 = monomial (deg i) (coeff i))
    (span_eq : (Ideal.span (Set.range f)).map (reesAlgebraToAssociatedGraded I) =
      J.toAssociatedGraded I) (r : R) (hr : r ∈ J) :
    ∃ (g : ι → ℕ → R), (∀ i, AdicCompletion.IsAdicCauchy I R (g i)) ∧
      ∀ n, r - ∑ x : ι, g x n * coeff x ∈ I ^ (n + 1) := by
  have exist (n : ℕ) := exists_coeffs_sub_mem I n J ι f deg coeff eq span_eq
  have memJ' (g' : ι → R) : r - ∑ x, g' x * coeff x ∈ J :=
    sub_mem hr (sum_mem (fun i _ ↦ (Ideal.mul_mem_left _ _ (memJ i))))
  let coeffs' (n : ℕ) : {f : (ι → R) // r - ∑ x, f x * coeff x ∈ I ^ (n + 1)} := by
    induction n with
    | zero =>
      exact ⟨Classical.choose (exist 0 r hr (by simp)),
        (Classical.choose_spec (exist 0 r hr (by simp))).2.2⟩
    | succ n coeffs'n =>
      refine ⟨coeffs'n + Classical.choose (exist (n + 1) _ (memJ' coeffs'n.1) coeffs'n.2), ?_⟩
      simp only [gt_iff_lt, Pi.add_apply, add_mul, Finset.sum_add_distrib, ← sub_sub]
      exact (Classical.choose_spec (exist (n + 1) _ (memJ' coeffs'n.1) coeffs'n.2)).2.2
  have coeffs'_spec_aux (n : ℕ) : (coeffs' (n + 1)).1 = (coeffs' n).1 +
      Classical.choose (exist (n + 1) _ (memJ' (coeffs' n).1) (coeffs' n).2) := rfl
  have coeffs'_spec (n : ℕ) :
    ∀ i, (coeffs' (n + 1)).1 i - (coeffs' n).1 i ∈ I ^ (n + 1 - deg i) := by
    simpa [coeffs'_spec_aux]
      using (Classical.choose_spec (exist (n + 1) _ (memJ' (coeffs' n).1) (coeffs' n).2)).1
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
