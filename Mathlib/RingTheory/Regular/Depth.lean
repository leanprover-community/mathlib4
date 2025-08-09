/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Yi Song
-/
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Regular.Category
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Algebra.Category.Grp.Zero
/-!

# Hom(N,M) is subsingleton iff there exists a smul regular element of M in ann(N)

Let `M` and `N` be `R`-modules. In this section we prove that `Hom(N,M)` is subsingleton iff
there exist `r : R`, such that `IsSMulRegular M r` and `r ∈ ann(N)`.
This is the case if `Depth[I](M) = 0`.

# Main Results

* `IsSMulRegular.subsingleton_linearMap_iff` : for `R` module `N M`, `Hom(N, M) = 0`
  iff there is a `M`-regular in `Module.annihilator R N`.

-/

open IsLocalRing LinearMap Module

namespace IsSMulRegular

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

lemma linearMap_subsingleton_of_mem_annihilator {r : R} (reg : IsSMulRegular M r)
    (mem_ann : r ∈ Module.annihilator R N) : Subsingleton (N →ₗ[R] M) := by
  apply subsingleton_of_forall_eq 0 (fun f ↦ ext fun x ↦ ?_)
  have : r • (f x) = r • 0 := by
    rw [smul_zero, ← map_smul, Module.mem_annihilator.mp mem_ann x, map_zero]
  simpa using reg this

lemma subsingleton_linearMap_iff [IsNoetherianRing R] [Module.Finite R M] [Module.Finite R N] :
    Subsingleton (N →ₗ[R] M) ↔ ∃ r ∈ Module.annihilator R N, IsSMulRegular M r := by
  refine ⟨fun hom0 ↦ ?_, fun ⟨r, mem_ann, reg⟩ ↦
    linearMap_subsingleton_of_mem_annihilator reg mem_ann⟩
  by_cases htrivial : Subsingleton M
  · exact ⟨0, ⟨Submodule.zero_mem (Module.annihilator R N), IsSMulRegular.zero⟩⟩
  · let _ : Nontrivial M := not_subsingleton_iff_nontrivial.mp htrivial
    by_contra! h
    have hexist : ∃ p ∈ associatedPrimes R M, Module.annihilator R N ≤ p := by
      rcases associatedPrimes.nonempty R M with ⟨Ia, hIa⟩
      apply (Ideal.subset_union_prime_finite (associatedPrimes.finite R M) Ia Ia _).mp
      · rw [biUnion_associatedPrimes_eq_compl_regular R M]
        exact fun r hr ↦ h r hr
      · exact fun I hin _ _ ↦ IsAssociatedPrime.isPrime hin
    rcases hexist with ⟨p, pass, hp⟩
    let _ := pass.isPrime
    let p' : PrimeSpectrum R := ⟨p, pass.isPrime⟩
    have loc_ne_zero : p' ∈ Module.support R N := Module.mem_support_iff_of_finite.mpr hp
    rw [Module.mem_support_iff] at loc_ne_zero
    let Rₚ := Localization.AtPrime p
    let Nₚ := LocalizedModule p'.asIdeal.primeCompl N
    let Mₚ := LocalizedModule p'.asIdeal.primeCompl M
    let Nₚ' := Nₚ ⧸ (IsLocalRing.maximalIdeal (Localization.AtPrime p)) • (⊤ : Submodule Rₚ Nₚ)
    have ntr : Nontrivial Nₚ' :=
      Submodule.Quotient.nontrivial_of_lt_top _ (Ne.lt_top'
        (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
        (IsLocalRing.maximalIdeal_le_jacobson (Module.annihilator Rₚ Nₚ))))
    let Mₚ' := Mₚ ⧸ (IsLocalRing.maximalIdeal (Localization.AtPrime p)) • (⊤ : Submodule Rₚ Mₚ)
    let _ : Module p.ResidueField Nₚ' :=
      Module.instQuotientIdealSubmoduleHSMulTop Nₚ (maximalIdeal (Localization.AtPrime p))
    have := AssociatePrimes.mem_iff.mp
      (associatedPrimes.mem_associatePrimes_localizedModule_atPrime_of_mem_associated_primes pass)
    rcases this.2 with ⟨x, hx⟩
    have : Nontrivial (Module.Dual p.ResidueField Nₚ') := by simpa using ntr
    rcases exists_ne (α := Module.Dual p.ResidueField Nₚ') 0 with ⟨g, hg⟩
    let to_res' : Nₚ' →ₗ[Rₚ] p.ResidueField := {
      __ := g
      map_smul' r x := by
        simp only [AddHom.toFun_eq_coe, coe_toAddHom, RingHom.id_apply]
        convert g.map_smul (Ideal.Quotient.mk _ r) x }
    let to_res : Nₚ →ₗ[Rₚ] p.ResidueField :=
      to_res'.comp ((maximalIdeal (Localization.AtPrime p)) • (⊤ : Submodule Rₚ Nₚ)).mkQ
    let i : p.ResidueField →ₗ[Rₚ] Mₚ :=
      Submodule.liftQ _ (LinearMap.toSpanSingleton Rₚ Mₚ x) (le_of_eq hx)
    have inj1 : Function.Injective i :=
      LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ _ (le_of_eq hx.symm))
    let f := i.comp to_res
    have f_ne0 : f ≠ 0 := by
      intro eq0
      absurd hg
      apply LinearMap.ext
      intro np'
      induction' np' using Submodule.Quotient.induction_on with np
      change to_res np = 0
      apply inj1
      change f np = _
      simp [eq0]
    absurd hom0
    let _ := Module.finitePresentation_of_finite R N
    contrapose! f_ne0
    exact (Module.FinitePresentation.linearEquivMapExtendScalars
      p'.asIdeal.primeCompl).symm.map_eq_zero_iff.mp (Subsingleton.eq_zero _)

end IsSMulRegular

/-!

# The Rees theorem

In this section we proved the rees theorem for depth, which build the relation between
the vanishing order of `Ext` and maximal regular sequence.

# Main results

* `lemma222` : for `n : ℕ`, noetherian ring `R`, `I : Ideal R`,
  `M : ModuleCat R` finitely generated and nontrivial satisfying `IM < M`, we proved TFAE,
  · for any `N : ModuleCat R` finitely generated and nontrivial with support contained in the
    zerolucus of `I`, `∀ i < n, Ext N M i = 0`
  · `∀ i < n, Ext (A⧸I) M i = 0`
  · there exist a `N : ModuleCat R` finitely generated and nontrivial with support equal to the
    zerolucus of `I`, `∀ i < n, Ext N M i = 0`
  · there exist a `M`-regular sequence of length `n` with every element in `I`

-/

universe w v u

open IsLocalRing LinearMap
open RingTheory.Sequence Ideal CategoryTheory Abelian Limits

variable {R : Type u} [CommRing R] [Small.{v} R] [UnivLE.{v, w}]

local instance : CategoryTheory.HasExt.{w} (ModuleCat.{v} R) :=
  --CategoryTheory.HasExt.standard (ModuleCat.{v} R)
  CategoryTheory.hasExt_of_enoughProjectives.{w} (ModuleCat.{v} R)

open Pointwise ModuleCat IsSMulRegular

lemma lemma222_3_to_4 [IsNoetherianRing R] (I : Ideal R) (n : ℕ) :
    ∀ M : ModuleCat.{v} R, Nontrivial M → Module.Finite R M →
    I • (⊤ : Submodule R M) < ⊤ → (∃ N : ModuleCat.{v} R, Nontrivial N ∧ Module.Finite R N ∧
    Module.support R N = PrimeSpectrum.zeroLocus I ∧ ∀ i < n, Subsingleton (Ext N M i)) →
    ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ I) ∧ IsRegular M rs := by
  induction' n with n ih
  · intro M ntr M_fin smul_lt exist_N
    use []
    simp [isRegular_iff]
  · intro M ntrM M_fin smul_lt exist_N
    rcases exist_N with ⟨N, ntr, fin, h_supp, h_ext⟩
    have h_supp' := h_supp
    rw [Module.support_eq_zeroLocus, PrimeSpectrum.zeroLocus_eq_iff] at h_supp'
    have : Subsingleton (N →ₗ[R] M) :=
      let _ := h_ext 0 n.zero_lt_succ
      let _ : Subsingleton (N ⟶ M) := Ext.addEquiv₀.symm.subsingleton
      (ModuleCat.homAddEquiv (M := N) (N := M)).symm.subsingleton
    rcases subsingleton_linearMap_iff.mp this with ⟨x, mem_ann, hx⟩
    have := Ideal.le_radical mem_ann
    rw [h_supp', Ideal.mem_radical_iff] at this
    rcases this with ⟨k, hk⟩
    have hxk := IsSMulRegular.pow k hx
    let M' := QuotSMulTop (x ^ k) M
    have le_smul : x ^ k • (⊤ : Submodule R M) ≤ I • ⊤ := by
      rw [← Submodule.ideal_span_singleton_smul]
      exact (Submodule.smul_mono_left ((span_singleton_le_iff_mem I).mpr hk))
    have ntr' : Nontrivial M' :=
      Submodule.Quotient.nontrivial_of_lt_top _ (lt_of_lt_of_le' smul_lt le_smul)
    have smul_lt' : I • (⊤ : Submodule R M') < ⊤ := by
      rw [lt_top_iff_ne_top]
      by_contra eq
      absurd lt_top_iff_ne_top.mp smul_lt
      have := Submodule.smul_top_eq_comap_smul_top_of_surjective I
        (Submodule.mkQ ((x ^ k) • (⊤ : Submodule R M))) (Submodule.mkQ_surjective _)
      simpa [eq, le_smul] using this
    have exist_N' : (∃ N : ModuleCat R, Nontrivial N ∧ Module.Finite R N ∧
        Module.support R N = PrimeSpectrum.zeroLocus I ∧
          ∀ i < n, Subsingleton (Abelian.Ext N (ModuleCat.of R M') i)) := by
      use N
      simp only [ntr, fin, h_supp, true_and]
      intro i hi
      have zero1 : IsZero (AddCommGrp.of (Ext N M i)) :=
        @AddCommGrp.isZero_of_subsingleton _ (h_ext i (Nat.lt_add_right 1 hi))
      have zero2 : IsZero (AddCommGrp.of (Ext N M (i + 1))) :=
        @AddCommGrp.isZero_of_subsingleton _ (h_ext (i + 1) (Nat.add_lt_add_right hi 1))
      exact AddCommGrp.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
        ((Ext.covariant_sequence_exact₃' N hxk.smulShortComplex_shortExact) i (i + 1) rfl)
        (zero1.eq_zero_of_src _) (zero2.eq_zero_of_tgt _)
    rcases ih (ModuleCat.of R M') ntr'
      (Module.Finite.quotient R _) smul_lt' exist_N' with ⟨rs, len, mem, reg⟩
    use x ^ k :: rs
    simpa [len, hk] using ⟨mem, hxk, reg⟩

lemma mono_of_mono (a : R) {k : ℕ} (kpos : k > 0) (i : ℕ) {M N : ModuleCat.{v} R}
    (f_mono : Mono (AddCommGrp.ofHom ((Ext.mk₀ (smulShortComplex M a).f).postcomp
    N (add_zero i)))) : Mono (AddCommGrp.ofHom ((Ext.mk₀ (smulShortComplex M (a ^ k)).f).postcomp
    N (add_zero i))) := by
  induction' k with k ih
  · simp at kpos
  · rw [pow_succ]
    by_cases eq0 : k = 0
    · rw [eq0, pow_zero, one_mul]
      exact f_mono
    · have eq_comp :
        (AddCommGrp.ofHom ((Ext.mk₀ (smulShortComplex M (a ^ k * a)).f).postcomp N (add_zero i))) =
        (AddCommGrp.ofHom ((Ext.mk₀ (smulShortComplex M (a ^ k)).f).postcomp N (add_zero i))) ≫
        (AddCommGrp.ofHom ((Ext.mk₀ (smulShortComplex M a).f).postcomp N (add_zero i))) := by
        have : (a ^ k * a) • (LinearMap.id (R := R) (M := M)) =
          (a • (LinearMap.id (M := M))).comp ((a ^ k) • (LinearMap.id (M := M))) := by
          rw [LinearMap.comp_smul, LinearMap.smul_comp, smul_smul, LinearMap.id_comp]
        simp only [smulShortComplex, this, ModuleCat.ofHom_comp, ModuleCat.of_coe,
          ← extFunctorObj_map, (extFunctorObj N i).map_comp]
      rw [eq_comp]
      exact CategoryTheory.mono_comp' (ih (Nat.zero_lt_of_ne_zero eq0)) f_mono

lemma lemma222_4_to_1 [IsNoetherianRing R] (I : Ideal R) (n : ℕ) (N : ModuleCat.{v} R)
    (Nntr : Nontrivial N) (Nfin : Module.Finite R N)
    (Nsupp : Module.support R N ⊆ PrimeSpectrum.zeroLocus I) :
    ∀ M : ModuleCat.{v} R, Nontrivial M → Module.Finite R M → I • (⊤ : Submodule R M) < ⊤ →
    (∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ I) ∧ IsRegular M rs) →
    ∀ i < n, Subsingleton (Ext N M i) := by
  induction' n with n ih
  · simp
  · rintro M Mntr Mfin smul_lt ⟨rs, len, mem, reg⟩ i hi
    have le_rad := Nsupp
    rw [Module.support_eq_zeroLocus, PrimeSpectrum.zeroLocus_subset_zeroLocus_iff] at le_rad
    match rs with
    | [] =>
      absurd len
      simp
    | a :: rs' =>
      rcases le_rad (mem a List.mem_cons_self) with ⟨k, hk⟩
      have kpos : k > 0 := by
        by_contra h
        simp only [Nat.eq_zero_of_not_pos h, pow_zero, Module.mem_annihilator, one_smul] at hk
        absurd Nntr
        exact not_nontrivial_iff_subsingleton.mpr (subsingleton_of_forall_eq 0 hk)
      simp only [isRegular_cons_iff] at reg
      let M' := (QuotSMulTop a M)
      have le_smul : a • ⊤ ≤ I • (⊤ : Submodule R M) := by
        rw [← Submodule.ideal_span_singleton_smul]
        exact Submodule.smul_mono_left
          ((span_singleton_le_iff_mem I).mpr (mem a List.mem_cons_self))
      have Qntr : Nontrivial M' :=
        Submodule.Quotient.nontrivial_of_lt_top _ (lt_of_lt_of_le' smul_lt le_smul)
      have smul_lt' : I • (⊤ : Submodule R M') < ⊤ := by
        rw [lt_top_iff_ne_top]
        by_contra eq
        absurd lt_top_iff_ne_top.mp smul_lt
        have := Submodule.smul_top_eq_comap_smul_top_of_surjective I
          (Submodule.mkQ (a • (⊤ : Submodule R M))) (Submodule.mkQ_surjective _)
        simpa [eq, le_smul] using this
      have exist_reg' : ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ I) ∧
        IsRegular (ModuleCat.of R M') rs := by
        use rs'
        simp only [List.length_cons, Nat.add_left_inj] at len
        simp only [List.mem_cons, forall_eq_or_imp] at mem
        exact ⟨len, mem.2, reg.2⟩
      by_cases eq0 : i = 0
      · rw [eq0]
        have : Subsingleton (N →ₗ[R] M) := subsingleton_linearMap_iff.mpr
          ⟨a ^ k, hk, (IsSMulRegular.pow k reg.1)⟩
        have : Subsingleton (N ⟶ M) := ModuleCat.homEquiv.subsingleton
        exact Ext.addEquiv₀.subsingleton
      · have lt : i - 1 < n := by omega
        let g := (AddCommGrp.ofHom ((Ext.mk₀ (smulShortComplex M a).f).postcomp N (add_zero i)))
        have mono_g : Mono g := by
          apply ShortComplex.Exact.mono_g (CategoryTheory.Abelian.Ext.covariant_sequence_exact₁'
            N reg.1.smulShortComplex_shortExact (i - 1) i (by omega)) (IsZero.eq_zero_of_src _ _)
          exact @AddCommGrp.isZero_of_subsingleton _ (ih (ModuleCat.of R M') Qntr
            (Module.Finite.quotient R _) smul_lt' exist_reg' (i - 1) lt)
        let gk := (AddCommGrp.ofHom
          ((Ext.mk₀ (smulShortComplex M (a ^ k)).f).postcomp N (add_zero i)))
        have mono_gk : Mono gk := mono_of_mono a kpos i mono_g
        have zero_gk : gk = 0 := ext_hom_eq_zero_of_mem_ann hk i
        exact AddCommGrp.subsingleton_of_isZero (IsZero.of_mono_eq_zero _ zero_gk)

--lemma222 i.e. Rees theorem
lemma lemma222 [IsNoetherianRing R] (I : Ideal R) [Small.{v} (R ⧸ I)] (n : ℕ) (M : ModuleCat.{v} R)
    (Mntr : Nontrivial M) (Mfin : Module.Finite R M) (smul_lt : I • (⊤ : Submodule R M) < ⊤) :
  [∀ N : ModuleCat.{v} R, (Nontrivial N ∧ Module.Finite R N ∧
    Module.support R N ⊆ PrimeSpectrum.zeroLocus I) → ∀ i < n, Subsingleton (Ext N M i),
   ∀ i < n, Subsingleton (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M i),
   ∃ N : ModuleCat R, Nontrivial N ∧ Module.Finite R N ∧
    Module.support R N = PrimeSpectrum.zeroLocus I ∧ ∀ i < n, Subsingleton (Ext N M i),
    ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ I) ∧ RingTheory.Sequence.IsRegular M rs
    ].TFAE := by
  have ntrQ : Nontrivial (R ⧸ I) := by
    apply Submodule.Quotient.nontrivial_of_lt_top _ (lt_top_iff_ne_top.mpr _)
    by_contra eq
    absurd smul_lt
    simp [eq]
  have suppQ : Module.support R (R ⧸ I) = PrimeSpectrum.zeroLocus I := by
    have : I = (I • (⊤ : Ideal R)) := by simp only [smul_eq_mul, mul_top]
    rw [this, Module.support_quotient]
    have : Module.annihilator R R = ⊥ := by
      rw [Module.annihilator_eq_bot]
      exact (faithfulSMul_iff_algebraMap_injective R R).mpr fun ⦃a₁ a₂⦄ a ↦ a
    simp [Module.support_eq_zeroLocus, this]
  tfae_have 1 → 2 := by
    intro h1 i hi
    apply h1 (ModuleCat.of R (Shrink.{v} (R ⧸ I))) _ i hi
    simp_rw [instNontrivialShrink, Module.Finite.equiv (Shrink.linearEquiv R (R ⧸ I)).symm]
    rw [true_and, true_and, (Shrink.linearEquiv R _).support_eq, suppQ]
  tfae_have 2 → 3 := by
    intro h2
    use (ModuleCat.of R (Shrink.{v} (R ⧸ I)))
    simp only [instNontrivialShrink, Module.Finite.equiv (Shrink.linearEquiv R (R ⧸ I)).symm,
      true_and]
    refine ⟨?_, h2⟩
    rw [(Shrink.linearEquiv R _).support_eq, suppQ]
  tfae_have 3 → 4 := lemma222_3_to_4 I n M Mntr Mfin smul_lt
  tfae_have 4 → 1 := fun h4 N ⟨Nntr, Nfin, Nsupp⟩ i hi ↦
    lemma222_4_to_1 I n N Nntr Nfin Nsupp M Mntr Mfin smul_lt h4 i hi
  tfae_finish
