/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
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

/-!
# Hausdorff-ness for Noetherian rings
-/

@[expose] public section

open IsLocalRing Module

universe u

variable {R : Type u} [CommRing R] (I : Ideal R)

section

variable (M : Type*) [AddCommGroup M] [Module R M]

variable [IsNoetherianRing R] [Module.Finite R M]

lemma IsHausdorff.of_le_jacobson (h : I ≤ Ideal.jacobson ⊥) : IsHausdorff I M :=
  ⟨fun x hx ↦ (Ideal.iInf_pow_smul_eq_bot_of_le_jacobson I h).le (by simpa [SModEq.zero] using hx)⟩

theorem IsHausdorff.of_isLocalRing [IsLocalRing R] (h : I ≠ ⊤) : IsHausdorff I M :=
  of_le_jacobson I M ((le_maximalIdeal h).trans (maximalIdeal_le_jacobson _))

instance [IsLocalRing R] : IsHausdorff (maximalIdeal R) M :=
  .of_le_jacobson _ _ (maximalIdeal_le_jacobson _)

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

lemma tensorProduct_reesAlgebra_isNoetherian_of_fg [IsNoetherianRing (R ⧸ I)] (fg : I.FG) :
    IsNoetherianRing (TensorProduct R (R ⧸ I) (reesAlgebra I)) := by
  have : Algebra.FiniteType R (reesAlgebra I) := ⟨(reesAlgebra I).fg_top.mpr (reesAlgebra.fg fg)⟩
  have := this.baseChange (R ⧸ I)
  exact Algebra.FiniteType.isNoetherianRing (R ⧸ I) _

lemma reesAlgebra_quotient_isNoetherian [IsNoetherianRing (R ⧸ I)] (fg : I.FG) :
    IsNoetherianRing ((reesAlgebra I) ⧸ I.map (algebraMap R (reesAlgebra I))) := by
  have := tensorProduct_reesAlgebra_isNoetherian_of_fg I fg
  exact isNoetherianRing_of_ringEquiv  _
     (Algebra.TensorProduct.quotIdealMapEquivQuotTensor (reesAlgebra I) I).symm.toRingEquiv

open Polynomial

lemma Polynomial.monimial_mem_reesAlgebra (i : ℕ) {r : R} (mem : r ∈ I ^ i) :
    monomial i r ∈ reesAlgebra I := by
  refine (mem_reesAlgebra_iff _ _).mpr (fun n ↦ ?_)
  by_cases eqi : n = i
  · simpa [eqi]
  · simp [coeff_monomial_of_ne _ eqi]

lemma mem_map_algebraMap_reesAlgebra_iff (f : reesAlgebra I) :
    f ∈ I.map (algebraMap R (reesAlgebra I)) ↔ ∀ n, f.1.coeff n ∈ I ^ (n + 1) := by
  refine ⟨fun h n ↦ ?_, fun h ↦ ?_⟩
  · rw [← Submodule.restrictScalars_mem R, ← Ideal.smul_top_eq_map] at h
    induction h using Submodule.smul_induction_on' with
    | smul r hr m hm =>
      simpa [pow_succ'] using Ideal.mul_mem_mul hr ((mem_reesAlgebra_iff I _).mp m.2 n)
    | add x hx y hy memx memy => simpa using add_mem memx memy
  · have mem' (i : ℕ) {r : R} : r ∈ I ^ i → _ := fun mem ↦ monimial_mem_reesAlgebra I i mem
    have mem (i : ℕ) := monimial_mem_reesAlgebra I i ((mem_reesAlgebra_iff I _).mp f.2 i)
    have : f = ∑ i ∈ f.1.support, ⟨(Polynomial.monomial i) (f.1.coeff i), mem i⟩ :=
      SetCoe.ext (by simpa using f.1.as_sum_support)
    rw [this]
    apply sum_mem (fun i hi ↦ ?_)
    have {r : R} (h' : r ∈ I * I ^ i) : ⟨(Polynomial.monomial i) r,mem' i (Ideal.mul_le_left h')⟩
      ∈ I.map (algebraMap R (reesAlgebra I)) := by
      induction h' using Submodule.mul_induction_on' with
      | mem_mul_mem s hs t ht =>
        have : ⟨(Polynomial.monomial i) (s * t), mem' i (Ideal.mul_mem_left _ s ht)⟩ =
          s • (⟨(Polynomial.monomial i) t, mem' i ht⟩: reesAlgebra I) := by
          simp [Polynomial.smul_monomial]
        rw [this, Algebra.smul_def]
        exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hs)
      | add s1 hs1 s2 hs2 mem1 mem2 => simpa using add_mem mem1 mem2
    apply this
    simpa [pow_succ'] using h i

noncomputable abbrev reesAlgebraToAssociatedGraded :=
  Ideal.Quotient.mk (I.map (algebraMap R (reesAlgebra I)))

noncomputable abbrev Ideal.toAssociatedGraded (J I : Ideal R) :
    Ideal ((reesAlgebra I) ⧸ (I.map (algebraMap R (reesAlgebra I)))) :=
  ((J.map Polynomial.C).comap (reesAlgebra I).val).map (reesAlgebraToAssociatedGraded I)

lemma exists_monomial_span_of_fg (J : Ideal R) (fg : (J.toAssociatedGraded I).FG) :
    ∃ (ι : Type u) (f : ι → reesAlgebra I) (deg : ι → ℕ) (coeff : ι → R), Finite ι ∧
      (∀ i : ι, (f i).1 = monomial (deg i) (coeff i)) ∧ (∀ i : ι, coeff i ∈ J) ∧
        (Ideal.span (Set.range f)).map (reesAlgebraToAssociatedGraded I) =
          J.toAssociatedGraded I := by
  obtain ⟨s, hs⟩ := fg
  have smem : ∀ x ∈ s, x ∈ J.toAssociatedGraded I := fun x hx ↦ by
    simpa [← hs] using Ideal.subset_span hx
  have : (J.toAssociatedGraded I).comap (reesAlgebraToAssociatedGraded I) = _ :=
    (Ideal.comap_map_of_surjective' (reesAlgebraToAssociatedGraded I)
      Ideal.Quotient.mk_surjective ((J.map Polynomial.C).comap (reesAlgebra I).val)).trans
        (sup_comm _ _)
  let g : s → reesAlgebra I := fun x ↦ Classical.choose
    (Ideal.exists_of_comap_eq_ker_sup _ Ideal.Quotient.mk_surjective this (smem x.1 x.2))
  have g_spec (x : s) : g x ∈ _ ∧ reesAlgebraToAssociatedGraded I (g x) = x := Classical.choose_spec
    (Ideal.exists_of_comap_eq_ker_sup _ Ideal.Quotient.mk_surjective this (smem x.1 x.2))
  sorry

lemma exists_coeffs_sub_mem (n : ℕ) (J : Ideal R) (ι : Type u) [Fintype ι] (f : ι → reesAlgebra I)
    (deg : ι → ℕ) (coeff : ι → R) (eq : ∀ i : ι, (f i).1 = monomial (deg i) (coeff i))
    (memJ : ∀ i : ι, coeff i ∈ J) (span_eq : (Ideal.span (Set.range f)).map
      (reesAlgebraToAssociatedGraded I) = J.toAssociatedGraded I)
    (r : R) (rmem_J : r ∈ J) (rmem_pow : r ∈ I ^ n) : ∃ (coeff' : ι → R),
    (∀ i : ι, coeff' i ∈ I ^ (n - deg i)) ∧ (∀ i : ι, deg i > n → coeff' i = 0) ∧
      r - ∑ x : ι, coeff' x * coeff x ∈ I ^ (n + 1) := by
  sorry

lemma isNoetherianRing_of_isAdicComplete_of_fg [IsNoetherianRing (R ⧸ I)] (fg : I.FG)
    (complete : IsAdicComplete I R) : IsNoetherianRing R := by
  apply (isNoetherianRing_iff_ideal_fg R).mpr (fun J ↦ ?_)
  let J_rees := (J.map Polynomial.C).comap (reesAlgebra I).val
  let J_assoc := J_rees.map (Ideal.Quotient.mk (I.map (algebraMap R (reesAlgebra I))))

  sorry

lemma AdicCompletion.isNoetherianRing_of_fg [IsNoetherianRing (R ⧸ I)] (fg : I.FG) :
    IsNoetherianRing (AdicCompletion I R) := by
  have eq : I.map (algebraMap R (AdicCompletion I R)) = RingHom.ker (evalOneₐ I).toRingHom := by
    ext x
    refine (Iff.trans ?_ (Submodule.ext_iff.mp (pow_smul_top_eq_ker_eval fg (n := 1)) x)).trans ?_
    · simp
    · have eq : I ^ 1 * (⊤ : Ideal R) = I := by simp
      have inj : Function.Injective (Ideal.Quotient.factor (le_of_eq eq)) := by
        simp [RingHom.injective_iff_ker_eq_bot, Ideal.Quotient.factor_ker,
          Ideal.map_mk_eq_bot_of_le]
      simpa [← AdicCompletion.factorₐ_evalₐ_one, ← AdicCompletion.factor_eval_eq_evalₐ]
        using (map_eq_zero_iff _ inj).symm
  let e : (AdicCompletion I R) ⧸ I.map (algebraMap R (AdicCompletion I R)) ≃+* R ⧸ I :=
    (Ideal.quotEquivOfEq eq).trans
    (RingHom.quotientKerEquivOfSurjective (AdicCompletion.evalOneₐ_surjective I))
  have := isNoetherianRing_of_ringEquiv _ e.symm
  exact isNoetherianRing_of_isAdicComplete_of_fg _ (fg.map (algebraMap R (AdicCompletion I R)))
    (AdicCompletion.isAdicComplete_self I fg)

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
