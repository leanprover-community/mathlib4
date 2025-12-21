/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.FractionRing

/-! # Almost integral elements -/

@[expose] public section

section

open scoped nonZeroDivisors

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

variable (R) in
/-- An element `s` in an `R`-algebra is almost integral if there exists `r ∈ R⁰` such that
`r • s ^ n ∈ R` for all `n`. -/
@[stacks 00GW]
def IsAlmostIntegral (s : S) : Prop := ∃ r ∈ R⁰, ∀ n, r • s ^ n ∈ (algebraMap R S).range

variable (R S) in
/-- The complete integral closure is the subalgebra of almost integral elements. -/
@[stacks 00GX "Part 1"]
def completeIntegralClosure : Subalgebra R S where
  carrier := { s | IsAlmostIntegral R s }
  mul_mem' := by
    rintro a b ⟨r, hr, hr'⟩ ⟨s, hs, hs'⟩
    refine ⟨r * s, mul_mem hr hs, fun n ↦ ?_⟩
    rw [mul_pow, mul_smul_mul_comm]
    exact mul_mem (hr' _) (hs' _)
  add_mem' := by
    rintro a b ⟨r, hr, hr'⟩ ⟨s, hs, hs'⟩
    refine ⟨r * s, mul_mem hr hs, fun n ↦ ?_⟩
    simp only [add_pow, Finset.smul_sum, ← smul_mul_assoc _ (_ * _),
      ← smul_mul_smul_comm _ (a ^ _)]
    exact sum_mem fun i _ ↦ mul_mem (mul_mem (hr' _) (hs' _)) (by simp)
  algebraMap_mem' r := ⟨1, one_mem _, by simp [← map_pow]⟩

lemma mem_completeIntegralClosure {x : S} :
    x ∈ completeIntegralClosure R S ↔ IsAlmostIntegral R x := .rfl

lemma IsIntegral.isAlmostIntegral_of_exists_smul_mem_range
    {s : S} (H : IsIntegral R s) (h : ∃ t ∈ R⁰, t • s ∈ (algebraMap R S).range) :
    IsAlmostIntegral R s := by
  obtain ⟨b, hb', hb⟩ :
      ∃ b ∈ R⁰, ∀ i < (minpoly R s).natDegree, (b • s ^ i) ∈ (algebraMap R S).range := by
    obtain ⟨t, ht, ht'⟩ := h
    refine ⟨t ^ (minpoly R s).natDegree, pow_mem ht _, fun i hi ↦ ?_⟩
    rw [← Nat.sub_add_cancel hi.le, pow_add, mul_smul, ← smul_pow]
    exact (AlgHom.range (Algebra.ofId _ _)).smul_mem (Subalgebra.pow_mem _ ht' _) _
  refine ⟨b, hb', fun n ↦ ?_⟩
  induction n using Nat.strong_induction_on with | h n IH =>
  obtain hn | hn := lt_or_ge n (minpoly R s).natDegree
  · exact hb _ (by simpa)
  have := minpoly.aeval R s
  rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, add_eq_zero_iff_eq_neg',
    Polynomial.coeff_natDegree, minpoly.monic H, one_smul] at this
  rw [← Nat.sub_add_cancel hn, pow_add, this, mul_neg, smul_neg, Finset.mul_sum, Finset.smul_sum]
  simp_rw [mul_smul_comm, ← pow_add, smul_comm b]
  refine neg_mem (sum_mem fun i hi ↦ (AlgHom.range (Algebra.ofId _ _)).smul_mem (IH _ ?_) _)
  simp only [Finset.mem_range] at hi
  lia

lemma IsIntegral.isAlmostIntegral_of_isLocalization
    {s : S} (H : IsIntegral R s) (M : Submonoid R) (hM : M ≤ R⁰) [IsLocalization M S] :
    IsAlmostIntegral R s := by
  obtain ⟨s, t, rfl⟩ := IsLocalization.exists_mk'_eq M s
  exact H.isAlmostIntegral_of_exists_smul_mem_range ⟨t, hM t.2, by simp⟩

@[stacks 00GX "Part 2"]
lemma IsIntegral.isAlmostIntegral [IsFractionRing R S]
    {s : S} (H : IsIntegral R s) : IsAlmostIntegral R s :=
  H.isAlmostIntegral_of_isLocalization _ le_rfl

lemma integralClosure_le_completeIntegralClosure [IsFractionRing R S] :
    integralClosure R S ≤ completeIntegralClosure R S :=
  fun _ h ↦ h.isAlmostIntegral

lemma IsAlmostIntegral.isIntegral_of_nonZeroDivisors_le_comap
    {s : S} (H : IsAlmostIntegral R s) [IsNoetherianRing R]
    (H' : R⁰ ≤ S⁰.comap (algebraMap R S)) : IsIntegral R s := by
  obtain ⟨r, hr, hr'⟩ := H
  let f : Algebra.adjoin R {s} →ₗ[R]
      Submodule.span R {Localization.Away.invSelf (algebraMap R S r)} :=
    (IsScalarTower.toAlgHom R S (Localization.Away (algebraMap R S r))).toLinearMap.restrict
      (p := (Algebra.adjoin R {s}).toSubmodule) <| by
    change (Algebra.adjoin R {s}).toSubmodule ≤ (Submodule.span _ _).comap _
    rw [Algebra.adjoin_eq_span, ← Submonoid.powers_eq_closure, Submodule.span_le]
    rintro _ ⟨n, rfl⟩
    obtain ⟨a, ha⟩ := hr' n
    refine Submodule.mem_span_singleton.mpr ⟨a, ?_⟩
    suffices algebraMap _ _ (s ^ n) * algebraMap _ _ ((algebraMap R S) r) *
        Localization.Away.invSelf ((algebraMap R S) r) = algebraMap S _ (s ^ n) by
      simpa [Algebra.smul_def, IsScalarTower.algebraMap_apply R S (Localization.Away _),
        ha, mul_assoc, mul_left_comm] using this
    simp [mul_assoc, Localization.Away.invSelf, Localization.mk_eq_mk']
  have : Function.Injective f := by
    have : Function.Injective (algebraMap S (Localization.Away (algebraMap R S r))) := by
      apply IsLocalization.injective (M := .powers (algebraMap R S r))
      exact Submonoid.powers_le.mpr (H' hr)
    exact fun x y e ↦ Subtype.ext (this congr($e))
  have : (Algebra.adjoin R {s}).toSubmodule.FG := by
    rw [← Submodule.fg_top, ← Module.finite_def]
    exact .of_injective f this
  exact .of_mem_of_fg _ this _ (Algebra.self_mem_adjoin_singleton R s)

@[stacks 00GX "Part 3"]
lemma IsAlmostIntegral.isIntegral [IsNoetherianRing R] [IsDomain S] [FaithfulSMul R S]
    {s : S} (H : IsAlmostIntegral R s) : IsIntegral R s := by
  have : IsDomain R := (FaithfulSMul.algebraMap_injective R S).isDomain
  exact H.isIntegral_of_nonZeroDivisors_le_comap fun _ ↦ by simp

lemma isAlmostIntegral_iff_isIntegral [IsNoetherianRing R] [IsDomain R] [IsFractionRing R S]
    {s : S} : IsAlmostIntegral R s ↔ IsIntegral R s :=
  letI := IsFractionRing.isDomain R (K := S)
  ⟨IsAlmostIntegral.isIntegral, IsIntegral.isAlmostIntegral⟩

lemma completeIntegralClosure_eq_integralClosure
    [IsNoetherianRing R] [IsDomain R] [IsFractionRing R S] :
    completeIntegralClosure R S = integralClosure R S :=
  SetLike.ext fun _ ↦ isAlmostIntegral_iff_isIntegral

end
