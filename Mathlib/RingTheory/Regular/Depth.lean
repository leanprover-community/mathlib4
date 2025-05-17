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
import Mathlib.Tactic.ENatToNat
/-!

# Hom(N,M) is subsingleton iff exist smul regular element of M in ann(N)

In this section, we proved that for `R` modules `M N`, `Hom(N,M)` is subsingleton iff
there exist `r : R`, `IsSMulRegular M r` and `r ∈ ann(N)`.
This is the case for `Depth[I](M) = 0`.

-/

open IsLocalRing LinearMap

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

lemma hom_subsingleton_of_mem_ann_isSMulRegular {r : R} (reg : IsSMulRegular M r)
    (mem_ann : r ∈ Module.annihilator R N) : Subsingleton (N →ₗ[R] M) := by
  apply subsingleton_of_forall_eq 0 (fun f ↦ ext fun x ↦ ?_)
  have : r • (f x) = r • 0 := by
    rw [smul_zero, ← map_smul, Module.mem_annihilator.mp mem_ann x, map_zero]
  simpa using reg this

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

universe w v u

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

lemma moduleDepth_lt_top_iff (N M : ModuleCat.{v} R) :
    moduleDepth N M < ⊤ ↔ ∃ n, Nontrivial (Ext.{max u v} N M n) := by
  convert (moduleDepth_eq_top_iff N M).not
  · exact lt_top_iff_ne_top
  · push_neg
    exact exists_congr (fun i ↦ not_subsingleton_iff_nontrivial.symm)

lemma moduleDepth_eq_iff (N M : ModuleCat.{v} R) (n : ℕ) : moduleDepth N M = n ↔
    Nontrivial (Ext.{max u v} N M n) ∧ ∀ i < n, Subsingleton (Ext.{max u v} N M i) := by
  classical
  refine ⟨fun h ↦ ?_, fun ⟨ntr, h⟩ ↦ ?_⟩
  · have exist := (moduleDepth_lt_top_iff N M).mp (by simp [h])
    simp only [moduleDepth_eq_find _ _ exist, Nat.cast_inj] at h
    refine ⟨h ▸ Nat.find_spec exist, fun i hi ↦ ?_⟩
    exact not_nontrivial_iff_subsingleton.mp (Nat.find_min exist (lt_of_lt_of_eq hi h.symm))
  · have exist : ∃ n, Nontrivial (Ext.{max u v} N M n) := by use n
    simp only [moduleDepth_eq_find _ _ exist, Nat.cast_inj, Nat.find_eq_iff, ntr, true_and]
    intro i hi
    exact not_nontrivial_iff_subsingleton.mpr (h i hi)

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
    [Nontrivial M] [Nntr : Nontrivial N] (smul_lt : I • (⊤ : Submodule R M) < ⊤)
    (hsupp : Module.support R N = PrimeSpectrum.zeroLocus I) :
    moduleDepth N M = I.depth M := by
  have (n : ℕ) : (∀ i < n, Subsingleton (Ext.{max u v} N M i)) ↔
    (∀ i < n, Subsingleton (Ext.{max u v} (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M i)) := by
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · have : ∃ N : ModuleCat.{v} R, Nontrivial N ∧ Module.Finite R N ∧
        Module.support R N = PrimeSpectrum.zeroLocus ↑I ∧
        ∀ i < n, Subsingleton (Ext.{max u v} N M i) := by
        use N
      exact ((lemma222 I n M (by assumption) (by assumption) smul_lt).out 1 2).mpr
        this
    · have rees :=
        ((lemma222 I n M (by assumption) (by assumption) smul_lt).out 0 1).mpr h
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

lemma moduleDepth_eq_sSup_length_regular [IsNoetherianRing R] (I : Ideal R) [Small.{v, u} (R ⧸ I)]
    (N M : ModuleCat.{v} R) [Module.Finite R M] [Nfin : Module.Finite R N]
    [Nontrivial M] [Nntr : Nontrivial N] (smul_lt : I • (⊤ : Submodule R M) < ⊤)
    (hsupp : Module.support R N = PrimeSpectrum.zeroLocus I) :
    moduleDepth N M = sSup {(List.length rs : ℕ∞) | (rs : List R)
    (_ : RingTheory.Sequence.IsRegular M rs) (_ : ∀ r ∈ rs, r ∈ I) } := by
  rw [moduleDepth_eq_sup_nat]
  congr
  ext m
  simp only [Set.mem_setOf_eq, exists_prop, exists_and_left]
  refine ⟨fun ⟨lt_top, h⟩ ↦ ?_, fun ⟨rs, reg, mem, len⟩ ↦ ?_⟩
  · rcases ENat.ne_top_iff_exists.mp (ne_top_of_lt lt_top) with ⟨n, hn⟩
    simp only [← hn, Nat.cast_lt, Nat.cast_inj] at h ⊢
    have : ∃ N : ModuleCat.{v} R, Nontrivial N ∧ Module.Finite R N ∧
      Module.support R N = PrimeSpectrum.zeroLocus ↑I ∧
      ∀ i < n, Subsingleton (Ext.{max u v} N M i) := by
      use N
    rcases ((lemma222 I n M (by assumption) (by assumption) smul_lt).out 2 3).mp
      this with ⟨rs, len, mem, reg⟩
    use rs
  · simp only [← len, ENat.coe_lt_top, Nat.cast_lt, true_and]
    have rees := ((lemma222 I rs.length M (by assumption) (by assumption)
      smul_lt).out 3 0).mp (by use rs)
    apply rees N
    simp [Nntr, Nfin, hsupp]

omit [Small.{v, u} R] in
lemma Submodule.comap_lt_top_of_lt_range {M N : Type* } [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (p : Submodule R N)
    (lt : p < LinearMap.range f) : Submodule.comap f p < ⊤ := by
  obtain ⟨x, ⟨y, hy⟩, nmem⟩ : ∃ x ∈ LinearMap.range f, x ∉ p := Set.exists_of_ssubset lt
  have : y ∉ Submodule.comap f p := by simpa [hy] using nmem
  exact lt_of_le_not_le (fun _ a ↦ trivial) fun a ↦ this (a trivial)

--universe invariant
lemma moduleDepth_eq_moduleDepth_shrink [IsNoetherianRing R] (I : Ideal R) [Small.{w, u} R]
    [Small.{v, u} (R ⧸ I)] [Small.{w, u} (R ⧸ I)]
    (N M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    [AddCommGroup N] [Module R N] [Nfin : Module.Finite R N] [Nntr : Nontrivial N]
    (smul_lt : I • (⊤ : Submodule R M) < ⊤)
    (hsupp : Module.support R N = PrimeSpectrum.zeroLocus I)
    [Small.{w} M] [Small.{w} N] :
    moduleDepth (ModuleCat.of R N) (ModuleCat.of R M) =
    moduleDepth (ModuleCat.of R (Shrink.{w} N)) (ModuleCat.of R (Shrink.{w} M)) := by
  rw [moduleDepth_eq_sSup_length_regular I (ModuleCat.of R N) (ModuleCat.of R M) smul_lt hsupp]
  let _ : Module.Finite R (Shrink.{w} M) :=
    Module.Finite.equiv (Shrink.linearEquiv.{v, w} M R).symm
  let _ : Module.Finite R (Shrink.{w} N) :=
    Module.Finite.equiv (Shrink.linearEquiv.{v, w} N R).symm
  have smul_lt' : I • (⊤ : Submodule R (Shrink.{w} M)) < ⊤ := by
    apply lt_of_le_of_lt (Submodule.smul_top_le_comap_smul_top I
      (Shrink.linearEquiv.{v, w} M R).toLinearMap) (Submodule.comap_lt_top_of_lt_range _ _ _)
    simpa using smul_lt
  have hsupp' : Module.support R (Shrink.{w} N) = PrimeSpectrum.zeroLocus I := by
    rw [LinearEquiv.support_eq (Shrink.linearEquiv.{v, w} N R), hsupp]
  rw [moduleDepth_eq_sSup_length_regular I
    (ModuleCat.of R (Shrink.{w} N)) (ModuleCat.of R (Shrink.{w} M)) smul_lt' hsupp']
  have : RingTheory.Sequence.IsRegular M =
    RingTheory.Sequence.IsRegular (R := R) (Shrink.{w, v} M) := by
    ext rs
    exact LinearEquiv.isRegular_congr (Shrink.linearEquiv.{v, w} M R).symm rs
  congr!

lemma ring_depth_invariant [IsNoetherianRing R] (I : Ideal R) (lt_top : I < ⊤)
    [Small.{v, u} (R ⧸ I)] :
    I.depth (ModuleCat.of R (Shrink.{v} R)) = I.depth (ModuleCat.of R R) := by
  simp only [Ideal.depth]
  let _ : Nontrivial (R ⧸ I) := Submodule.Quotient.nontrivial_of_lt_top I lt_top
  let _ : Nontrivial R := (Submodule.nontrivial_iff R).mp (nontrivial_of_lt I ⊤ lt_top)
  let e : (of R (Shrink.{u, u} (R ⧸ I))) ≅ (of R (R ⧸ I)) :=
    (Shrink.linearEquiv.{u, u} (R ⧸ I) R).toModuleIso
  rw [moduleDepth_eq_of_iso_fst _ e, eq_comm]
  have smul_lt : I • (⊤ : Submodule R R) < ⊤ := by simpa using lt_top
  apply moduleDepth_eq_moduleDepth_shrink I (R ⧸ I) R smul_lt
  simp [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]

lemma moduleDepth_quotSMulTop_succ_eq_moduleDepth (N M : ModuleCat.{v} R) (x : R)
    (reg : IsSMulRegular M x) (mem : x ∈ Module.annihilator R N) :
    moduleDepth N (ModuleCat.of R (QuotSMulTop x M)) + 1 = moduleDepth N M := by
  simp only [moduleDepth, add_comm]
  have iff (i : ℕ) : Subsingleton (Ext N (ModuleCat.of R (QuotSMulTop x M)) i) ↔
    (Subsingleton (Ext N M i) ∧ Subsingleton (Ext N M (i + 1))) := by
    refine ⟨fun h ↦ ?_, fun ⟨h1, h3⟩ ↦ ?_⟩
    · constructor
      · exact @Function.Injective.subsingleton _ _ _ ((AddCommGrp.mono_iff_injective _).mp
          (ShortComplex.Exact.mono_g
          (Ext.covariant_sequence_exact₂' N reg.smulShortComplex_shortExact i)
          (ext_hom_eq_zero_of_mem_ann mem i))) h
      · exact @Function.Surjective.subsingleton _ _ _ h ((AddCommGrp.epi_iff_surjective _).mp
          (ShortComplex.Exact.epi_f
          (Ext.covariant_sequence_exact₁' N reg.smulShortComplex_shortExact i (i + 1) rfl)
          (ext_hom_eq_zero_of_mem_ann mem (i + 1))))
    · exact AddCommGrp.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
        (Ext.covariant_sequence_exact₃' N reg.smulShortComplex_shortExact i (i + 1) rfl)
        ((@AddCommGrp.isZero_of_subsingleton _ h1).eq_zero_of_src _)
        ((@AddCommGrp.isZero_of_subsingleton _ h3).eq_zero_of_tgt _)
  apply le_antisymm
  · rw [ENat.add_sSup ⟨0, by simp⟩]
    apply iSup_le (fun n ↦ iSup_le (fun hn ↦ ?_))
    apply le_sSup
    intro i hi
    by_cases eq0 : i = 0
    · rw [eq0, Ext.addEquiv₀.subsingleton_congr, ModuleCat.homAddEquiv.subsingleton_congr]
      exact hom_subsingleton_of_mem_ann_isSMulRegular reg mem
    · have eq : i - 1 + 1 = i := Nat.sub_one_add_one eq0
      have : i - 1 < n := by
        enat_to_nat
        omega
      have := ((iff (i - 1)).mp (hn (i - 1) this)).2
      simpa only [eq] using this
  · apply sSup_le (fun n hn ↦ ?_)
    by_cases eq0 : n = 0
    · simp [eq0]
    · have : n - 1 + 1 = n := by
        enat_to_nat
        omega
      rw [add_comm, ← this]
      apply add_le_add_right
      apply le_sSup
      intro i hi
      have lt2 : i + 1 < n := by
        enat_to_nat
        omega
      have lt1 : i < n := lt_of_le_of_lt (self_le_add_right _ _) lt2
      exact (iff i).mpr ⟨hn i lt1, hn (i + 1) lt2⟩

lemma moduleDepth_quotient_regular_sequence_add_length_eq_moduleDepth (N M : ModuleCat.{v} R)
    (rs : List R) (reg : IsWeaklyRegular M rs) (h : ∀ r ∈ rs, r ∈ Module.annihilator R N) :
    moduleDepth N (ModuleCat.of R (M ⧸ (Ideal.ofList rs) • (⊤ : Submodule R M))) + rs.length =
    moduleDepth N M := by
  generalize len : rs.length = n
  induction' n with n hn generalizing M rs
  · rw [List.length_eq_zero_iff.mp len, Ideal.ofList_nil, Submodule.bot_smul]
    simpa using moduleDepth_eq_of_iso_snd N (Submodule.quotEquivOfEqBot ⊥ rfl).toModuleIso
  · match rs with
    | [] => simp at len
    | x :: rs' =>
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      simp only [List.length_cons, Nat.add_right_cancel_iff] at len
      have : IsSMulRegular M x := ((isWeaklyRegular_cons_iff M _ _).mp reg).1
      rw [moduleDepth_eq_of_iso_snd N
        (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M x rs').toModuleIso,
        ← moduleDepth_quotSMulTop_succ_eq_moduleDepth N M x this (h x List.mem_cons_self),
        ← hn (ModuleCat.of R (QuotSMulTop x M)) rs' ((isWeaklyRegular_cons_iff M _ _).mp reg).2
        (fun r hr ↦ h r (List.mem_cons_of_mem x hr)) len, add_assoc]

lemma ideal_depth_quotient_regular_sequence_add_length_eq_ideal_depth (I : Ideal R)
    [Small.{v} (R ⧸ I)] (M : ModuleCat.{v} R) (rs : List R) (reg : IsWeaklyRegular M rs)
    (h : ∀ r ∈ rs, r ∈ I) :
    I.depth (ModuleCat.of R (M ⧸ (Ideal.ofList rs) • (⊤ : Submodule R M))) + rs.length =
    I.depth M := by
  apply moduleDepth_quotient_regular_sequence_add_length_eq_moduleDepth _ M rs reg
  convert h
  rw [LinearEquiv.annihilator_eq (Shrink.linearEquiv (R ⧸ I) R), Ideal.annihilator_quotient]

lemma depth_quotient_regular_sequence_add_length_eq_depth [IsLocalRing R]
    [Small.{v} (R ⧸ maximalIdeal R)] (M : ModuleCat.{v} R) (rs : List R)
    (reg : IsRegular M rs) :
    IsLocalRing.depth (ModuleCat.of R (M ⧸ (Ideal.ofList rs) • (⊤ : Submodule R M))) + rs.length =
    IsLocalRing.depth M := by
  apply ideal_depth_quotient_regular_sequence_add_length_eq_ideal_depth _ M rs reg.toIsWeaklyRegular
  intro r hr
  simp only [mem_maximalIdeal, mem_nonunits_iff]
  by_contra isu
  absurd reg.2
  simp [eq_top_of_isUnit_mem (ofList rs) (Ideal.subset_span hr) isu]

end depth
