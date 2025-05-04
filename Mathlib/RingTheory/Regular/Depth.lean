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
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.RingTheory.KrullDimension.Module
import Mathlib.RingTheory.KrullDimension.Field
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
    ext r
    simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop]
    exact exists_congr (fun i ↦ (and_congr_left fun a ↦ ht i).symm)
  have hmem_union : ((I : Set R) ⊆ ⋃ i ∈ s, f i) ↔ ((I : Set R) ⊆ ⋃ i ∈ (t : Set ι), f i) :=
    (congrArg _ heq).to_iff
  have hexists_le: (∃ i ∈ t, I ≤ f i) ↔ ∃ i ∈ s, I ≤ f i :=
    exists_congr (fun i ↦ and_congr_left fun _ ↦ ht i)
  rw [hmem_union, Ideal.subset_union_prime a b (fun i hin ↦ hp i ((ht i).mp hin)), hexists_le]

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
  exact (Module.FinitePresentation.linearEquivMapExtendScalars
    p'.asIdeal.primeCompl).symm.map_eq_zero_iff.mp (Subsingleton.eq_zero _)

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
open RingTheory.Sequence Ideal CategoryTheory Abelian Limits

variable {R : Type u} [CommRing R] [Small.{v} R] [UnivLE.{v, w}]

local instance : CategoryTheory.HasExt.{w} (ModuleCat.{v} R) :=
  --CategoryTheory.HasExt.standard (ModuleCat.{v} R)
  CategoryTheory.hasExt_of_enoughProjectives.{w} (ModuleCat.{v} R)

open Pointwise ModuleCat

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
    simp only [List.length_cons, len, Nat.add_left_inj, List.mem_cons, forall_eq_or_imp, hk,
      true_and, isRegular_cons_iff]
    exact ⟨mem, hxk, reg⟩

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





section depth

instance [IsNoetherianRing R] (N M : ModuleCat.{v} R) (i : ℕ) : Module.Finite R (Ext N M i) := sorry

omit [UnivLE.{v, w}]

noncomputable def moduleDepth (N M : ModuleCat.{v} R) : ℕ∞ :=
  sSup {n : ℕ∞ | ∀ i : ℕ, i < n → Subsingleton (Ext.{max u v} N M i)}

noncomputable def Ideal.depth (I : Ideal R) (M : ModuleCat.{v} R) [Small.{v} (R ⧸ I)] : ℕ∞ :=
  moduleDepth (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M

noncomputable def IsLocalRing.depth [IsLocalRing R] (M : ModuleCat.{v} R)
    [Small.{v} (R ⧸ (IsLocalRing.maximalIdeal R))] : ℕ∞ :=
  (IsLocalRing.maximalIdeal R).depth M

open Classical in
lemma moduleDepth_eq_find (N M : ModuleCat.{v} R) (h : ∃ n, Nontrivial (Ext.{max u v} N M n)) :
    moduleDepth N M = Nat.find h := by
  apply le_antisymm
  · simp only [moduleDepth, sSup_le_iff, Set.mem_setOf_eq]
    intro n hn
    by_contra gt
    absurd Nat.find_spec h
    exact not_nontrivial_iff_subsingleton.mpr (hn (Nat.find h) (not_le.mp gt))
  · simp only [moduleDepth]
    apply le_sSup
    simp only [Set.mem_setOf_eq, Nat.cast_lt, Nat.lt_find_iff]
    intro i hi
    exact not_nontrivial_iff_subsingleton.mp (hi i (le_refl i))

lemma moduleDepth_eq_top_iff (N M : ModuleCat.{v} R) :
    moduleDepth N M = ⊤ ↔ ∀ i, Subsingleton (Ext.{max u v} N M i) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · by_contra! exist
    rw [moduleDepth_eq_find N M
      ((exists_congr (fun i ↦ not_subsingleton_iff_nontrivial)).mp exist)] at h
    simp at h
  · simp [moduleDepth]
    exact csSup_eq_top_of_top_mem (fun i _ ↦ h i)

lemma ext_subsingleton_of_lt_moduleDepth {N M : ModuleCat.{v} R} {i : ℕ}
    (lt : i < moduleDepth N M) : Subsingleton (Ext.{max u v} N M i) := by
  by_cases lttop : moduleDepth N M < ⊤
  · let _ : Nonempty {n : ℕ∞ | ∀ (i : ℕ), ↑i < n → Subsingleton (Ext.{max u v} N M i)} :=
      Nonempty.intro ⟨(0 : ℕ∞), by simp⟩
    exact ENat.sSup_mem_of_nonempty_of_lt_top lttop i lt
  · simp only [not_lt, top_le_iff, moduleDepth_eq_top_iff] at lttop
    exact lttop i

lemma moduleDepth_eq_sup_nat (N M : ModuleCat.{v} R) : moduleDepth N M =
    sSup {n : ℕ∞ | n < ⊤ ∧ ∀ i : ℕ, i < n → Subsingleton (Ext.{max u v} N M i)} := by
  simp only [moduleDepth]
  by_cases h : ⊤ ∈ {n : ℕ∞ | ∀ (i : ℕ), ↑i < n → Subsingleton (Ext.{max u v} N M i)}
  · rw [csSup_eq_top_of_top_mem h, eq_comm, ENat.eq_top_iff_forall_ge]
    intro m
    apply le_sSup
    simp only [Set.mem_setOf_eq, ENat.coe_lt_top, forall_const] at h
    simpa using fun i _ ↦ h i
  · congr
    ext n
    exact ⟨fun mem ↦ ⟨top_not_mem_iff.mp h n mem, mem⟩, fun mem ↦ mem.2⟩

lemma moduleDepth_eq_depth_of_supp_eq [IsNoetherianRing R] (I : Ideal R) [Small.{v, u} (R ⧸ I)]
    (N M : ModuleCat.{v} R) [Module.Finite R M] [Nfin : Module.Finite R N]
    [Nontrivial M] [Nntr : Nontrivial N]
    (smul_lt : I • (⊤ : Submodule R M) < ⊤)
    (hsupp : Module.support R N = PrimeSpectrum.zeroLocus I) :
    moduleDepth N M = I.depth M := by
  have (n : ℕ) : (∀ i < n, Subsingleton (Ext.{max u v} N M i)) ↔
    (∀ i < n, Subsingleton (Ext.{max u v} (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M i)) := by
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · have : ∃ N : ModuleCat.{v} R, Nontrivial N ∧ Module.Finite R N ∧
        Module.support R N = PrimeSpectrum.zeroLocus ↑I ∧
        ∀ i < n, Subsingleton (Ext.{max u v} N M i) := by
        use N
      exact ((lemma222.{u, v, max u v} I n M (by assumption) (by assumption) smul_lt).out 1 2).mpr
        this
    · have rees :=
        ((lemma222.{u, v, max u v} I n M (by assumption) (by assumption) smul_lt).out 0 1).mpr h
      apply rees N
      simp [Nfin, Nntr, hsupp]
  simp [Ideal.depth, moduleDepth_eq_sup_nat]
  congr
  ext n
  simp only [Set.mem_setOf_eq, and_congr_right_iff]
  intro lt_top
  convert this n.toNat
  <;> nth_rw 1 [← ENat.coe_toNat (LT.lt.ne_top lt_top), ENat.coe_lt_coe]

open Opposite in
lemma moduleDepth_eq_of_iso_fst (M : ModuleCat.{v} R) {N N' : ModuleCat.{v} R} (e : N ≅ N') :
    moduleDepth N M = moduleDepth N' M := by
  simp only [moduleDepth]
  congr
  ext n
  exact forall₂_congr fun i _ ↦
    (((extFunctor.{max u v} i).mapIso e.symm.op).app M).addCommGroupIsoToAddEquiv.subsingleton_congr

lemma moduleDepth_eq_of_iso_snd (N : ModuleCat.{v} R) {M M' : ModuleCat.{v} R} (e : M ≅ M') :
    moduleDepth N M = moduleDepth N M' := by
  simp only [moduleDepth]
  congr
  ext n
  exact forall₂_congr fun i _ ↦
    ((extFunctorObj N i).mapIso e).addCommGroupIsoToAddEquiv.subsingleton_congr

lemma moduleDepth_eq_zero_of_hom_nontrivial (N M : ModuleCat.{v} R) :
    moduleDepth N M = 0 ↔ Nontrivial (N →ₗ[R] M) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp [moduleDepth] at h
    have : 1 ∉ {n : ℕ∞ | ∀ (i : ℕ), ↑i < n → Subsingleton (Ext.{max u v} N M i)} := by
      by_contra mem
      absurd le_sSup mem
      simp [h]
    simp only [Set.mem_setOf_eq, Nat.cast_lt_one, forall_eq,
      not_subsingleton_iff_nontrivial, Ext.addEquiv₀.nontrivial_congr] at this
    exact (ModuleCat.homLinearEquiv (S := R)).nontrivial_congr.mp this
  · apply nonpos_iff_eq_zero.mp (sSup_le (fun n mem ↦ ?_))
    by_contra pos
    absurd mem 0 (lt_of_not_le pos)
    simpa [not_subsingleton_iff_nontrivial, Ext.addEquiv₀.nontrivial_congr]
      using (ModuleCat.homLinearEquiv (S := R)).nontrivial_congr.mpr h


lemma moduleDepth_ge_min_of_shortExact_fst
    (S : ShortComplex (ModuleCat.{v} R)) (hS : S.ShortExact)
    (N : ModuleCat.{v} R) : moduleDepth S.X₂ N ≥ moduleDepth S.X₁ N ⊓ moduleDepth S.X₃ N := by
  apply le_sSup
  simp only [Set.mem_setOf_eq, lt_inf_iff, and_imp]
  intro i hi1 hi3
  have zero1 : IsZero (AddCommGrp.of (Ext S.X₁ N i)) :=
      @AddCommGrp.isZero_of_subsingleton _ (ext_subsingleton_of_lt_moduleDepth hi1)
  have zero3 : IsZero (AddCommGrp.of (Ext S.X₃ N i)) :=
      @AddCommGrp.isZero_of_subsingleton _ (ext_subsingleton_of_lt_moduleDepth hi3)
  exact AddCommGrp.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
    (Ext.contravariant_sequence_exact₂' hS N i)
    (zero3.eq_zero_of_src _) (zero1.eq_zero_of_tgt _)

lemma moduleDepth_ge_min_of_shortExact_snd
    (N : ModuleCat.{v} R) (S : ShortComplex (ModuleCat.{v} R))
    (hS : S.ShortExact) : moduleDepth N S.X₂ ≥ moduleDepth N S.X₁ ⊓ moduleDepth N S.X₃ := by
  apply le_sSup
  simp only [Set.mem_setOf_eq, lt_inf_iff, and_imp]
  intro i hi1 hi3
  have zero1 : IsZero (AddCommGrp.of (Ext N S.X₁ i)) :=
      @AddCommGrp.isZero_of_subsingleton _ (ext_subsingleton_of_lt_moduleDepth hi1)
  have zero3 : IsZero (AddCommGrp.of (Ext N S.X₃ i)) :=
      @AddCommGrp.isZero_of_subsingleton _ (ext_subsingleton_of_lt_moduleDepth hi3)
  exact AddCommGrp.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
    (Ext.covariant_sequence_exact₂' N hS i)
    (zero1.eq_zero_of_src _) (zero3.eq_zero_of_tgt _)

variable (R) in
omit [Small.{v, u} R] in
lemma IsLocalRing.maximalIdeal_mem_support [IsLocalRing R] (M : Type*)
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M] :
    ⟨maximalIdeal R, IsMaximal.isPrime' (maximalIdeal R)⟩ ∈ Module.support R M:= by
  simp only [Module.support_eq_zeroLocus, PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
  apply IsLocalRing.le_maximalIdeal
  simpa [Module.annihilator_eq_top_iff.not, not_subsingleton_iff_nontrivial]

variable (R) in
omit [Small.{v, u} R] in
lemma zeroLocus_eq_singleton (m : Ideal R) [max : m.IsMaximal] :
    PrimeSpectrum.zeroLocus m = {⟨m, IsMaximal.isPrime' m⟩} := by
  rw [← PrimeSpectrum.closure_singleton ⟨m, IsMaximal.isPrime' m⟩]
  exact closure_eq_iff_isClosed.mpr
    ((PrimeSpectrum.isClosed_singleton_iff_isMaximal ⟨m, IsMaximal.isPrime' m⟩).mpr (by assumption))

omit [Small.{v, u} R] in
lemma quotSMulTop_nontrivial [IsLocalRing R] {x : R} (mem : x ∈ maximalIdeal R)
    (L : Type*) [AddCommGroup L] [Module R L] [Module.Finite R L] [Nontrivial L] :
    Nontrivial (QuotSMulTop x L) := by
  apply Submodule.Quotient.nontrivial_of_lt_top _ (Ne.lt_top' _)
  apply Submodule.top_ne_pointwise_smul_of_mem_jacobson_annihilator
  exact IsLocalRing.maximalIdeal_le_jacobson _ mem

theorem moduleDepth_ge_depth_sub_dim [IsNoetherianRing R] [IsLocalRing R] (M N : ModuleCat.{v} R)
    [Module.Finite R M] [Nfin : Module.Finite R N] [Nontrivial M] [Nntr : Nontrivial N]
    [Small.{v, u} (R ⧸ maximalIdeal R)] :
    moduleDepth N M ≥ IsLocalRing.depth M -
    (Module.supportDim R N).unbot (Module.supportDim_ne_bot_of_nontrivial R N) := by
  generalize dim :
    ((Module.supportDim R N).unbot (Module.supportDim_ne_bot_of_nontrivial R N)).toNat = r
  induction' r using Nat.strong_induction_on with r ihr generalizing N
  by_cases eq0 : r = 0
  · by_cases eqtop : (Module.supportDim R N).unbot (Module.supportDim_ne_bot_of_nontrivial R N) = ⊤
    · simp [eqtop]
    · rw [← ENat.coe_toNat eqtop, dim]
      show moduleDepth N M ≥ IsLocalRing.depth M - r
      simp only [eq0, ENat.toNat_eq_zero, WithBot.unbot_eq_iff, WithBot.coe_zero, eqtop,
        or_false] at dim
      have hsupp : Module.support R N = PrimeSpectrum.zeroLocus (maximalIdeal R) := by
        rw [zeroLocus_eq_singleton]
        apply le_antisymm
        · intro p hp
          by_contra nmem
          simp at nmem
          have : p < ⟨maximalIdeal R, IsMaximal.isPrime' (maximalIdeal R)⟩ :=
            lt_of_le_of_ne (IsLocalRing.le_maximalIdeal IsPrime.ne_top') nmem
          have := IsLocalRing.maximalIdeal_mem_support R N
          have : Module.supportDim R N > 0 := by
            simp [Module.supportDim, Order.krullDim_pos_iff]
            use p
            simp only [hp, true_and]
            use ⟨maximalIdeal R, IsMaximal.isPrime' (maximalIdeal R)⟩
          exact (ne_of_lt this) dim.symm
        · simpa using IsLocalRing.maximalIdeal_mem_support R N
      have smul_lt : (maximalIdeal R) • (⊤ : Submodule R M) < (⊤ : Submodule R M) :=
        Ne.lt_top' (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
          (IsLocalRing.maximalIdeal_le_jacobson (Module.annihilator R M)))
      simp [eq0, IsLocalRing.depth,
        moduleDepth_eq_depth_of_supp_eq (maximalIdeal R) N M smul_lt hsupp]
  · have eqr (n : ℕ∞) : n.toNat = r → n = r := by
      let _ : NeZero r := ⟨eq0⟩
      simp
    refine (IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime
      (motive := fun L ↦ (∀ (Lntr : Nontrivial L),
        (((Module.supportDim R L).unbot (Module.supportDim_ne_bot_of_nontrivial R L))).toNat = r →
        (moduleDepth (ModuleCat.of R L) M ≥ IsLocalRing.depth M -
        (Module.supportDim R L).unbot (Module.supportDim_ne_bot_of_nontrivial R L)))) R Nfin)
        ?_ ?_ ?_ Nntr dim
    · intro L _ _ _ Ltr Lntr
      absurd Ltr
      exact (not_subsingleton_iff_nontrivial.mpr Lntr)
    · intro L _ _ _ p e Lntr dim_eq
      rw [eqr _ dim_eq]
      obtain ⟨x, hx⟩ : ((maximalIdeal R : Set R) \ (p.asIdeal: Set R)).Nonempty  := by
        rw [Set.diff_nonempty]
        by_contra sub
        have := Ideal.IsMaximal.eq_of_le (maximalIdeal.isMaximal R) IsPrime.ne_top' sub
        have : Module.supportDim R (R ⧸ p.asIdeal) = 0 := by
          let _ : Field (R ⧸ maximalIdeal R) := Quotient.field (maximalIdeal R)
          rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator, ← this,
            Ideal.annihilator_quotient, ringKrullDim_eq_zero_of_field]
        absurd eqr _ dim_eq
        simpa only [Module.supportDim_eq_of_equiv R L (R ⧸ p.asIdeal) e, this, WithBot.unbot_zero,
          ← ENat.coe_zero, ENat.coe_inj, eq_comm] using eq0
      let S := (ModuleCat.of R L).smulShortComplex x
      have reg : IsSMulRegular (ModuleCat.of R L) x := by
        show Function.Injective (x • (LinearMap.id (R := R) (M := L)))
        rw [← LinearMap.ker_eq_bot]
        ext l
        simp only [mem_ker, smul_apply, id_coe, id_eq, Submodule.mem_bot]
        refine ⟨fun h ↦ ?_, fun h ↦ smul_eq_zero_of_right x h⟩
        apply e.injective
        have : (Ideal.Quotient.mk p.asIdeal x) * e l = 0 := by
          have : (Ideal.Quotient.mk p.asIdeal x) * e l = x • e l := rfl
          rw [this, ← map_smul, h, map_zero]
        rcases mul_eq_zero.mp this with xzero|zero
        · absurd xzero
          exact Ideal.Quotient.eq_zero_iff_mem.not.mpr (Set.not_mem_of_mem_diff hx)
        · rw [zero, map_zero]
      have hS := reg.smulShortComplex_shortExact
      apply le_sSup
      intro i hi
      have : Subsingleton (Ext.{max u v} (ModuleCat.of R (QuotSMulTop x L)) M (i + 1)) := by
        have ntr : Nontrivial (QuotSMulTop x L) := quotSMulTop_nontrivial (Set.mem_of_mem_diff hx) L
        have dimlt' : (Module.supportDim R (QuotSMulTop x L)).unbot
          (Module.supportDim_ne_bot_of_nontrivial R (QuotSMulTop x L)) < r := by
          have : (Module.supportDim R (QuotSMulTop x L)) + 1 ≤ Module.supportDim R L := by
            simp only [Module.supportDim_eq_ringKrullDim_quotient_annihilator]
            rw [LinearEquiv.annihilator_eq e, Ideal.annihilator_quotient]
            have ple : p.asIdeal ≤ Module.annihilator R (QuotSMulTop x L) := by
              rw [Submodule.annihilator_quotient, ← Ideal.annihilator_quotient (I := p.asIdeal),
                ← LinearEquiv.annihilator_eq e, ← Submodule.annihilator_top, ← Submodule.colon_bot]
              exact Submodule.colon_mono bot_le (le_refl ⊤)
            let f := Quotient.factor ple
            have mem_ann : x ∈ Module.annihilator R (QuotSMulTop x L) := by
              apply Module.mem_annihilator.mpr (fun l ↦ ?_)
              induction' l using Submodule.Quotient.induction_on with l
              simpa [← Submodule.Quotient.mk_smul] using
                Submodule.smul_mem_pointwise_smul l x ⊤ trivial
            have : Ideal.Quotient.mk p.asIdeal x ∈ nonZeroDivisors (R ⧸ p.asIdeal) := by
              simpa [Ideal.Quotient.eq_zero_iff_mem] using Set.not_mem_of_mem_diff hx
            exact ringKrullDim_succ_le_of_surjective (Quotient.factor ple)
              (Quotient.factor_surjective ple) this
              (by simpa [Quotient.eq_zero_iff_mem] using mem_ann)
          have succle : (Module.supportDim R (QuotSMulTop x L)).unbot
            (Module.supportDim_ne_bot_of_nontrivial R (QuotSMulTop x L)) + 1 ≤ r := by
            simpa [← eqr _ dim_eq, WithBot.le_unbot_iff] using this
          have : (Module.supportDim R (QuotSMulTop x L)).unbot
            (Module.supportDim_ne_bot_of_nontrivial R (QuotSMulTop x L)) ≠ ⊤ := by
            by_contra h
            simp [h] at succle
          exact (ENat.add_one_le_iff this).mp succle
        have dimlt : ((Module.supportDim R (QuotSMulTop x L)).unbot
          (Module.supportDim_ne_bot_of_nontrivial R (QuotSMulTop x L))).toNat < r := by
          rw [← ENat.coe_lt_coe, ENat.coe_toNat (ne_top_of_lt dimlt')]
          exact dimlt'
        apply ext_subsingleton_of_lt_moduleDepth
        refine lt_of_lt_of_le ?_ (ihr _ dimlt (ModuleCat.of R (QuotSMulTop x L)) rfl)
        rcases ENat.ne_top_iff_exists.mp (ne_top_of_lt dimlt') with ⟨m, hm⟩
        by_cases eqtop : IsLocalRing.depth M = ⊤
        · simp only [Nat.cast_add, eqtop, ← hm, ENat.top_sub_coe, ENat.add_lt_top,
            ENat.coe_lt_top, true_and]
        · rcases ENat.ne_top_iff_exists.mp eqtop with ⟨k, hk⟩
          have : (i + 1 : ℕ) ≤ IsLocalRing.depth M - r := by
            simpa [ENat.add_one_le_iff (ENat.coe_ne_top i)] using hi
          apply lt_of_le_of_lt this
          have le : r ≤ k := by
            simp only [← hk, ← ENat.coe_sub, Nat.cast_lt] at hi
            omega
          simp only [← hk, ← ENat.coe_sub, ← hm, Nat.cast_lt]
          simp only [← hm, Nat.cast_lt] at dimlt'
          omega
      have zero : IsZero
        (AddCommGrp.of (Ext.{max u v} (ModuleCat.of R (QuotSMulTop x L)) M (i + 1))) :=
        @AddCommGrp.isZero_of_subsingleton _ this
      have epi' : Function.Surjective
        (x • LinearMap.id (R := R) (M := (Ext.{max u v} (of R L) M i))) := by
        convert (AddCommGrp.epi_iff_surjective _).mp <| ShortComplex.Exact.epi_f
          (Ext.contravariant_sequence_exact₁' hS M i (i + 1) (Nat.add_comm 1 i))
          (zero.eq_zero_of_tgt _)
        ext a
        show x • a = Ext.bilinearCompOfLinear R _ _ _ _ _ _ (zero_add i)
          ((Ext.homEquiv₀_linearHom R).symm
          (ModuleCat.homLinearEquiv.symm (S := R) (x • LinearMap.id))) a
        simp only [map_smul, smul_apply]
        congr
        exact (Ext.mk₀_id_comp a).symm
      have range : LinearMap.range (x • LinearMap.id) =
        x • (⊤ : Submodule R (Ext.{max u v} (of R L) M i)) := by
        ext y
        simp [Submodule.mem_smul_pointwise_iff_exists]
      by_contra ntr
      rw [not_subsingleton_iff_nontrivial] at ntr
      have mem : x ∈ (Module.annihilator R (Ext.{max u v} (of R L) M i)).jacobson :=
        IsLocalRing.maximalIdeal_le_jacobson _ (Set.mem_of_mem_diff hx)
      absurd Submodule.top_ne_pointwise_smul_of_mem_jacobson_annihilator mem
      nth_rw 1 [← LinearMap.range_eq_top_of_surjective _ epi', ← range]
    · intro L1 _ _ _ L2 _ _ _ L3 _ _ _ f g inj surj exac ih1' ih3' L2ntr dim_eq
      rw [eqr _ dim_eq]
      by_cases ntr : Nontrivial L1 ∧ Nontrivial L3
      · let _ := ntr.1
        let _ := ntr.2
        have dimle1' : ((Module.supportDim R L1).unbot
          (Module.supportDim_ne_bot_of_nontrivial R L1)) ≤ r := by
          rw [← (eqr _ dim_eq), ← WithBot.coe_le_coe, WithBot.coe_unbot, WithBot.coe_unbot]
          exact Module.supportDim_le_of_injective R L1 L2 f inj
        have dimle3' : ((Module.supportDim R L3).unbot
          (Module.supportDim_ne_bot_of_nontrivial R L3)) ≤ r := by
          rw [← (eqr _ dim_eq), ← WithBot.coe_le_coe, WithBot.coe_unbot, WithBot.coe_unbot]
          exact Module.supportDim_le_of_surjective R L2 L3 g surj
        have ge1 : moduleDepth (of R L1) M ≥ IsLocalRing.depth M - ((Module.supportDim R L1).unbot
          (Module.supportDim_ne_bot_of_nontrivial R L1)) := by
          rcases lt_or_eq_of_le (ENat.toNat_le_of_le_coe dimle1') with lt|eq
          · exact ihr _ lt (ModuleCat.of.{v} R L1) rfl
          · exact ih1' ntr.1 eq
        have ge3 : moduleDepth (of R L3) M ≥ IsLocalRing.depth M - ((Module.supportDim R L3).unbot
          (Module.supportDim_ne_bot_of_nontrivial R L3)) := by
          rcases lt_or_eq_of_le (ENat.toNat_le_of_le_coe dimle3') with lt|eq
          · exact ihr _ lt (ModuleCat.of.{v} R L3) rfl
          · exact ih3' ntr.2 eq
        let S : ShortComplex (ModuleCat.{v} R) := {
          X₁ := ModuleCat.of R L1
          X₂ := ModuleCat.of R L2
          X₃ := ModuleCat.of R L3
          f := ModuleCat.ofHom f
          g := ModuleCat.ofHom g
          zero := by
            ext
            simp [Function.Exact.apply_apply_eq_zero exac] }
        have hS : S.ShortExact := {
          exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mpr exac
          mono_f := (ModuleCat.mono_iff_injective S.f).mpr inj
          epi_g := (ModuleCat.epi_iff_surjective S.g).mpr surj }
        exact ge_trans (moduleDepth_ge_min_of_shortExact_fst S hS M) (le_inf_iff.mpr
          ⟨le_trans (tsub_le_tsub_left dimle1' _) ge1, le_trans (tsub_le_tsub_left dimle3' _) ge3⟩)
      · have : Subsingleton L1 ∨ Subsingleton L3 := by
          simpa [← not_nontrivial_iff_subsingleton] using Classical.not_and_iff_not_or_not.mp ntr
        rcases this with sub1|sub3
        · have : Function.Injective g := by
            rw [← ker_eq_bot, exact_iff.mp exac, range_eq_bot, Subsingleton.eq_zero f]
          let eg : L2 ≃ₗ[R] L3 := LinearEquiv.ofBijective g ⟨this, surj⟩
          let L3ntr : Nontrivial L3 := Function.Injective.nontrivial this
          have dimeq3 : (((Module.supportDim R L3).unbot
            (Module.supportDim_ne_bot_of_nontrivial R L3))).toNat = r := by
            rw [← dim_eq]
            congr 2
            exact (Module.supportDim_eq_of_equiv R L2 L3 eg).symm
          rw [moduleDepth_eq_of_iso_fst M eg.toModuleIso, ← eqr _ dimeq3]
          exact ih3' L3ntr dimeq3
        · have : Function.Surjective f := by
            rw [← range_eq_top, ← exact_iff.mp exac, ker_eq_top, Subsingleton.eq_zero g]
          let ef : L1 ≃ₗ[R] L2 := LinearEquiv.ofBijective f ⟨inj, this⟩
          let L1ntr : Nontrivial L1 := Function.Surjective.nontrivial this
          have dimeq1 : (((Module.supportDim R L1).unbot
            (Module.supportDim_ne_bot_of_nontrivial R L1))).toNat = r := by
            rw [← dim_eq]
            congr 2
            exact Module.supportDim_eq_of_equiv R L1 L2 ef
          rw [← moduleDepth_eq_of_iso_fst M ef.toModuleIso, ← eqr _ dimeq1]
          exact ih1' L1ntr dimeq1

theorem depth_le_ringKrullDim_associatedPrime [IsNoetherianRing R] [IsLocalRing R]
    [Small.{v} (R ⧸ IsLocalRing.maximalIdeal R)]
    (M : ModuleCat.{v} R) [Module.Finite R M] [Nontrivial M]
    (P : associatedPrimes R M) : depth M ≤ ringKrullDim (R ⧸ P.1) := by

  sorry

/-
lemma has_finite_depth [IsNoetherianRing R] [IsLocalRing R] (M : ModuleCat.{v} R)
  [Module.Finite R M] [Small.{v} (R ⧸ (IsLocalRing.maximalIdeal R))]: Prop :=
  depth M ≠ ⊤
noncomputable def finite_depth [IsNoetherianRing R] [IsLocalRing R] (M : ModuleCat.{v} R)
    [Module.Finite R M] [Small.{v} (R ⧸ (IsLocalRing.maximalIdeal R))]
    (hfindep : has_finite_depth M): ℕ :=
  WithTop.untop (WithBot.unbot (depth M) (hfindep.1)) hfindep.2
theorem depth_le_ringKrullDim [IsNoetherianRing R] [IsLocalRing R] (M : ModuleCat.{v} R)
    [Module.Finite R M] [Nontrivial M] [Small.{v} (R ⧸ IsLocalRing.maximalIdeal R)] :
    depth M ≤ ringKrullDim R := sorry
theorem exist_nontrivial_ext [IsNoetherianRing R] [IsLocalRing R] (M : ModuleCat.{v} R)
    [Module.Finite R M] [Nontrivial M] [Small.{v} (R ⧸ IsLocalRing.maximalIdeal R)] : ∃ i : ℕ,
    Nontrivial (Ext.{v} (ModuleCat.of R (Shrink.{v} (R ⧸ IsLocalRing.maximalIdeal R))) M i) := sorry
theorem depth_eq_nat_find [IsNoetherianRing R] [IsLocalRing R] (M : ModuleCat.{v} R)
    [Module.Finite R M] [Nontrivial M] [Small.{v} (R ⧸ IsLocalRing.maximalIdeal R)] :
    depth M = Nat.find (exist_nontrivial_ext M) := sorry
 -/

end depth
