/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Yi Song
-/
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Regular.Category
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!

# Hom(N,M) is subsingleton iff exist smul regular element of M in ann(N)

In this section, we proved that for `R` modules `M N`, `Hom(N,M)` is subsingleton iff
there exist `r : R`, `IsSMulRegular M r` and `r ∈ ann(N)`.
This is the case for `Depth[I](M) = 0`.

-/

open IsLocalRing LinearMap

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

lemma Ideal.subset_union_prime_finite {R ι : Type*} [CommRing R] {s : Set ι}
    (hs : s.Finite) {f : ι → Ideal R} (a b : ι)
    (hp : ∀ i ∈ s, i ≠ a → i ≠ b → (f i).IsPrime) {I : Ideal R} :
    ((I : Set R) ⊆ ⋃ i ∈ s, f i) ↔ ∃ i ∈ s, I ≤ f i := by
  rcases Set.Finite.exists_finset hs with ⟨t, ht⟩
  have heq : ⋃ i ∈ s, f i = ⋃ i ∈ t, (f i : Set R) := by
    ext I
    simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop]
    apply exists_congr
    intro i
    simp only [ht i]
  have hmem_union : ((I : Set R) ⊆ ⋃ i ∈ s, f i) ↔ ((I : Set R) ⊆ ⋃ i ∈ (t : Set ι), f i) :=
    Eq.to_iff (congrArg (Subset ↑I) heq)
  have hexists_le: (∃ i ∈ t, I ≤ f i) ↔ ∃ i ∈ s, I ≤ f i := by
    apply exists_congr
    intro i
    simp only [ht i]
  rw [hmem_union,
    Ideal.subset_union_prime (R := R) a b (fun i hin ↦ hp i ((ht i).mp hin)) (I := I),
    hexists_le]

lemma mem_associatePrimes_of_comap_mem_associatePrimes_localization (S : Submonoid R)
    (p : Ideal (Localization S)) [p.IsPrime]
    (ass : p.comap (algebraMap R (Localization S)) ∈ associatedPrimes R M) :
    p ∈ associatedPrimes (Localization S) (LocalizedModule S M) := by
  rcases ass with ⟨hp, x, hx⟩
  constructor
  · --may be able to remove `p.IsPrime`
    trivial
  · use LocalizedModule.mkLinearMap S M x
    ext t
    induction' t using Localization.induction_on with a
    simp only [LocalizedModule.mkLinearMap_apply, LinearMap.mem_ker,
      LinearMap.toSpanSingleton_apply, LocalizedModule.mk_smul_mk, mul_one]
    rw [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.mk'_eq_zero']
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · use 1
      simp only [← LinearMap.toSpanSingleton_apply, one_smul, ← LinearMap.mem_ker, ← hx,
        Ideal.mem_comap, ← Localization.mk_one_eq_algebraMap]
      have : Localization.mk a.1 1 = Localization.mk a.1 a.2 * Localization.mk a.2.1 (1 : S) := by
        simp only [Localization.mk_mul, mul_one, ← sub_eq_zero, Localization.sub_mk,
          one_mul, sub_zero]
        simp [mul_comm, Localization.mk_zero]
      rw [this]
      exact Ideal.IsTwoSided.mul_mem_of_left _ h
    · rcases h with ⟨s, hs⟩
      have : s • a.1 • x = (s.1 * a.1) • x := smul_smul s.1 a.1 x
      rw [this, ← LinearMap.toSpanSingleton_apply, ← LinearMap.mem_ker, ← hx, Ideal.mem_comap,
        ← Localization.mk_one_eq_algebraMap] at hs
      have : Localization.mk a.1 a.2 =
        Localization.mk (s.1 * a.1) 1 * Localization.mk 1 (s * a.2) := by
        simp only [Localization.mk_mul, mul_one, one_mul, ← sub_eq_zero, Localization.sub_mk,
          Submonoid.coe_mul, sub_zero]
        simp [← mul_assoc, mul_comm s.1 a.2.1, Localization.mk_zero]
      rw [this]
      exact Ideal.IsTwoSided.mul_mem_of_left _ hs

lemma mem_associatePrimes_localizedModule_atPrime_of_mem_associated_primes {p : Ideal R} [p.IsPrime]
    (ass : p ∈ associatedPrimes R M) :
    maximalIdeal (Localization.AtPrime p) ∈
    associatedPrimes (Localization.AtPrime p) (LocalizedModule p.primeCompl M):= by
  apply mem_associatePrimes_of_comap_mem_associatePrimes_localization
  simpa [Localization.AtPrime.comap_maximalIdeal] using ass

--lemma_212_a
lemma hom_subsingleton_of_mem_ann_isSMulRegular {r : R} (reg : IsSMulRegular M r)
    (mem_ann : r ∈ Module.annihilator R N) : Subsingleton (N →ₗ[R] M) := by
  apply subsingleton_of_forall_eq 0 (fun f ↦ ext fun x ↦ ?_)
  have : r • (f x) = r • 0 := by
    rw [smul_zero, ← map_smul, Module.mem_annihilator.mp mem_ann x, map_zero]
  simpa using reg this

--lemma_212_b_nontrivial
lemma exist_mem_ann_isSMulRegular_of_hom_subsingleton_nontrivial [IsNoetherianRing R]
    [Module.Finite R M] [Module.Finite R N] [Nontrivial M] (hom0 : Subsingleton (N →ₗ[R] M)) :
    ∃ r ∈ Module.annihilator R N, IsSMulRegular M r := by
  by_contra! h
  have hexist : ∃ p ∈ associatedPrimes R M, Module.annihilator R N ≤ p := by
    rcases associatedPrimes.nonempty R M with ⟨Ia, hIa⟩
    apply (Ideal.subset_union_prime_finite (AssociatedPrimes.finite_of_noetherian R M) Ia Ia _).mp
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
    (mem_associatePrimes_localizedModule_atPrime_of_mem_associated_primes pass)
  rcases this.2 with ⟨x, hx⟩
  have : Nontrivial (Module.Dual p.ResidueField Nₚ') := by simpa using ntr
  rcases exists_ne (α := Module.Dual p.ResidueField Nₚ') 0 with ⟨g, hg⟩
  let to_res' : Nₚ' →ₗ[Rₚ] p.ResidueField := {
    __ := g
    map_smul' r x := by
      simp only [AddHom.toFun_eq_coe, coe_toAddHom, RingHom.id_apply]
      convert g.map_smul (Ideal.Quotient.mk _ r) x }
  let to_res : Nₚ →ₗ[Rₚ] p.ResidueField :=
    to_res'.comp ((IsLocalRing.maximalIdeal (Localization.AtPrime p)) • (⊤ : Submodule Rₚ Nₚ)).mkQ
  let i : p.ResidueField →ₗ[Rₚ] Mₚ :=
    Submodule.liftQ _ (LinearMap.toSpanSingleton Rₚ Mₚ x) (le_of_eq hx)
  have inj1 : Function.Injective i :=
    LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ _ (le_of_eq hx.symm))
  let f := i.comp to_res
  have f_ne0 : f ≠ 0 := by
    by_contra eq0
    absurd hg
    apply LinearMap.ext
    intro np'
    induction' np' using Submodule.Quotient.induction_on with np
    show to_res np = 0
    apply inj1
    show f np = _
    simp [eq0]
  absurd hom0
  let _ := Module.finitePresentation_of_finite R N
  contrapose! f_ne0
  exact (LinearEquiv.map_eq_zero_iff
    (Module.FinitePresentation.LinearEquiv_mapExtendScalars p'.asIdeal.primeCompl).symm).mp
      (Subsingleton.eq_zero _)

--lemma_212_b
lemma exist_mem_ann_isSMulRegular_of_hom_subsingleton [IsNoetherianRing R]
    [Module.Finite R M] [Module.Finite R N] (hom0 : Subsingleton (N →ₗ[R] M)) :
    ∃ r ∈ Module.annihilator R N, IsSMulRegular M r := by
  by_cases htrivial : Subsingleton M
  · use 0
    constructor
    · exact Submodule.zero_mem (Module.annihilator R N)
    · exact IsSMulRegular.zero
  · let _ : Nontrivial M := not_subsingleton_iff_nontrivial.mp htrivial
    exact exist_mem_ann_isSMulRegular_of_hom_subsingleton_nontrivial hom0

/-!

# The Rees theorem

-/

universe u v w

open IsLocalRing LinearMap
open RingTheory.Sequence Ideal CategoryTheory CategoryTheory.Abelian

variable {R : Type u} [CommRing R] [Small.{v} R] [UnivLE.{v, w}]

local instance : CategoryTheory.HasExt.{w} (ModuleCat.{v} R) :=
  --CategoryTheory.HasExt.standard (ModuleCat.{v} R)
  CategoryTheory.hasExt_of_enoughProjectives.{w} (ModuleCat.{v} R)

open Pointwise

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
      let _ : Subsingleton (N ⟶ M) := (homEquiv₀_hom N M).symm.subsingleton
      (ModuleCat.homAddEquiv (M := N) (N := M)).symm.subsingleton
    rcases exist_mem_ann_isSMulRegular_of_hom_subsingleton this with ⟨x, mem_ann, hx⟩
    have := Ideal.le_radical mem_ann
    rw [h_supp', Ideal.mem_radical_iff] at this
    rcases this with ⟨k, hk⟩
    have hxk := IsSMulRegular.pow k hx
    let M' := QuotSMulTop (x ^ k) M
    have le_smul : x ^ k • (⊤ : Submodule R M) ≤ I • ⊤ := by
      rw [← Submodule.ideal_span_singleton_smul]
      exact (Submodule.smul_mono_left ((span_singleton_le_iff_mem I).mpr hk))
    have ntr' : Nontrivial M' := by
      apply Submodule.Quotient.nontrivial_of_lt_top
      exact gt_of_gt_of_ge smul_lt le_smul
    have smul_lt' : I • (⊤ : Submodule R M') < ⊤ := by
      rw [lt_top_iff_ne_top]
      by_contra eq
      absurd lt_top_iff_ne_top.mp smul_lt
      have := Submodule.smul_top_eq_comap_smul_top_of_surjective I
        (Submodule.mkQ ((x ^ k) • (⊤ : Submodule R M))) (Submodule.mkQ_surjective _)
      simpa [eq, le_smul] using this
    have exist_N' : (∃ N : ModuleCat R, Nontrivial ↑N ∧ Module.Finite R ↑N ∧
        Module.support R ↑N = PrimeSpectrum.zeroLocus ↑I ∧
          ∀ i < n, Subsingleton (Abelian.Ext N (ModuleCat.of R M') i)) := by
      use N
      simp only [ntr, fin, h_supp, true_and]
      intro i hi
      have := subsingleton_of_subsingleton_subsingleton
        ((Ext.covariant_sequence_exact₃' N hxk.SMul_ShortComplex_exact) i (i + 1) rfl)
      exact this (h_ext i (Nat.lt_add_right 1 hi)) (h_ext (i + 1) (Nat.add_lt_add_right hi 1))
    rcases ih (ModuleCat.of R M') ntr'
      (Module.Finite.quotient R _) smul_lt' exist_N' with ⟨rs, len, mem, reg⟩
    use x ^ k :: rs
    simp only [List.length_cons, len, Nat.add_left_inj, List.mem_cons, forall_eq_or_imp, hk,
      true_and, isRegular_cons_iff]
    exact ⟨mem, hxk, reg⟩

lemma mono_of_mono (a : R) {k : ℕ} (kpos : k > 0) (i : ℕ) {M N : ModuleCat.{v} R}
    (f_mono : Mono (AddCommGrp.ofHom ((Ext.mk₀ (SMul_ShortComplex M a).f).postcomp
    N (add_zero i)))) : Mono (AddCommGrp.ofHom ((Ext.mk₀ (SMul_ShortComplex M (a ^ k)).f).postcomp
    N (add_zero i))) := by
  induction' k with k ih
  · simp at kpos
  · rw [pow_succ]
    by_cases eq0 : k = 0
    · rw [eq0, pow_zero, one_mul]
      exact f_mono
    · have := Nat.zero_lt_of_ne_zero eq0
      have eq_comp :
        (AddCommGrp.ofHom ((Ext.mk₀ (SMul_ShortComplex M (a ^ k * a)).f).postcomp N (add_zero i))) =
        (AddCommGrp.ofHom ((Ext.mk₀ (SMul_ShortComplex M (a ^ k)).f).postcomp N (add_zero i))) ≫
        (AddCommGrp.ofHom ((Ext.mk₀ (SMul_ShortComplex M a).f).postcomp N (add_zero i))) := by
        have : (a ^ k * a) • (LinearMap.id (R := R) (M := M)) =
          (a • (LinearMap.id (M := M))).comp ((a ^ k) • (LinearMap.id (M := M))) := by
          rw [LinearMap.comp_smul, LinearMap.smul_comp, smul_smul, LinearMap.id_comp]
        simp only [SMul_ShortComplex, this, ModuleCat.ofHom_comp, ModuleCat.of_coe,
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
      have reg_pow : IsSMulRegular M (a ^ k) := IsSMulRegular.pow k reg.1
      let M' := (QuotSMulTop a M)
      have le_smul : a • ⊤ ≤ I • (⊤ : Submodule R M) := by
        rw [← Submodule.ideal_span_singleton_smul]
        exact Submodule.smul_mono_left
          ((span_singleton_le_iff_mem I).mpr (mem a List.mem_cons_self))
      have Qntr : Nontrivial M' :=
        Submodule.Quotient.nontrivial_of_lt_top _ (gt_of_gt_of_ge smul_lt le_smul)
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
        have : Subsingleton (N →ₗ[R] M) := hom_subsingleton_of_mem_ann_isSMulRegular
          (IsSMulRegular.pow k reg.1) hk
        have : Subsingleton (N ⟶ M) := ModuleCat.homEquiv.subsingleton
        exact (homEquiv₀_hom N M).subsingleton
      · have lt : i - 1 < n := by omega
        let g := (AddCommGrp.ofHom ((Ext.mk₀ (SMul_ShortComplex M a).f).postcomp N (add_zero i)))
        have mono_g : Mono g := mono_of_subsingleton
          (CategoryTheory.Abelian.Ext.covariant_sequence_exact₁'
          N reg.1.SMul_ShortComplex_exact (i - 1) i (by omega))
          (ih (ModuleCat.of R M') Qntr (Module.Finite.quotient R _) smul_lt' exist_reg' (i - 1) lt)
        let gk := (AddCommGrp.ofHom
          ((Ext.mk₀ (SMul_ShortComplex M (a ^ k)).f).postcomp N (add_zero i)))
        have mono_gk : Mono gk := mono_of_mono a kpos i mono_g
        have zero_gk : gk = 0 := ext_hom_eq_zero_of_mem_ann hk i
        exact subsingleton_of_mono_zero mono_gk zero_gk

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
    simp_rw [instNontrivialShrink, Module.Finite.equiv (Shrink.linearEquiv (R ⧸ I) R).symm]
    rw [true_and, true_and, (Shrink.linearEquiv _ R).support_eq, suppQ]
  tfae_have 2 → 3 := by
    intro h2
    use (ModuleCat.of R (Shrink.{v} (R ⧸ I)))
    simp only [instNontrivialShrink, Module.Finite.equiv (Shrink.linearEquiv (R ⧸ I) R).symm,
      true_and]
    refine ⟨?_, h2⟩
    rw [(Shrink.linearEquiv _ R).support_eq, suppQ]
  tfae_have 3 → 4 := lemma222_3_to_4 I n M Mntr Mfin smul_lt
  tfae_have 4 → 1 := by
    intro h4 N ⟨Nntr, Nfin, Nsupp⟩ i hi
    exact lemma222_4_to_1 I n N Nntr Nfin Nsupp M Mntr Mfin smul_lt h4 i hi
  tfae_finish
