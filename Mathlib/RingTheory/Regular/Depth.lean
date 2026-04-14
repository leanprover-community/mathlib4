/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Yi Song
-/
module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import Mathlib.RingTheory.Regular.Category
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.Support

/-!

# The Rees theorem

In this file we prove the Rees theorem for depth, which relates the vanishing of
certain `Ext` groups and the length of a maximal regular sequence in a certain ideal.

## Main results

* `IsSMulRegular.subsingleton_linearMap_iff` : for finitely generated `R`-module `M, N`,
  `Hom(N, M) = 0` iff there is an `M`-regular element in `Module.annihilator R N`.
  This is the case for `n = 0` in the Rees theorem.

* `exists_isRegular_tfae` (Rees theorem) : For any `n : ℕ`, noetherian ring `R`, `I : Ideal R`, and
  finitely generated and nontrivial `R`-module `M` satisfying `IM < M`,
  the following are equivalent:
  · for any `N : ModuleCat R` finitely generated and nontrivial with support contained in the
    zero locus of `I`, `∀ i < n, Ext N M i = 0`
  · `∀ i < n, Ext (A⧸I) M i = 0`
  · there exists a `N : ModuleCat R` finitely generated and nontrivial with support equal to the
    zero locus of `I`, `∀ i < n, Ext N M i = 0`
  · there exists a `M`-regular sequence of length `n` with every element in `I`

-/

@[expose] public section

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
  cases subsingleton_or_nontrivial M
  · exact ⟨0, ⟨Submodule.zero_mem (Module.annihilator R N), IsSMulRegular.zero⟩⟩
  · by_contra! h
    obtain ⟨p, pass, hp⟩ : ∃ p ∈ associatedPrimes R M, Module.annihilator R N ≤ p := by
      rcases associatedPrimes.nonempty R M with ⟨Ia, hIa⟩
      apply (Ideal.subset_union_prime_finite (associatedPrimes.finite R M) Ia Ia _).mp
      · rw [biUnion_associatedPrimes_eq_compl_regular R M]
        exact fun r hr ↦ h r hr
      · exact fun I hin _ _ ↦ IsAssociatedPrime.isPrime hin
    have := pass.isPrime
    let p' : PrimeSpectrum R := ⟨p, pass.isPrime⟩
    have loc_ne_zero : p' ∈ Module.support R N := Module.mem_support_iff_of_finite.mpr hp
    rw [Module.mem_support_iff] at loc_ne_zero
    let Rₚ := Localization.AtPrime p
    let Nₚ := LocalizedModule.AtPrime p'.asIdeal N
    let Mₚ := LocalizedModule.AtPrime p'.asIdeal M
    let Nₚ' := Nₚ ⧸ (maximalIdeal (Localization.AtPrime p)) • (⊤ : Submodule Rₚ Nₚ)
    have ntr : Nontrivial Nₚ' := Submodule.Quotient.nontrivial_iff.mpr <|
      (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator (maximalIdeal_le_jacobson _)).symm
    let Mₚ' := Mₚ ⧸ (IsLocalRing.maximalIdeal (Localization.AtPrime p)) • (⊤ : Submodule Rₚ Mₚ)
    let : Module p.ResidueField Nₚ' :=
      Module.instQuotientIdealSubmoduleHSMulTop Nₚ (maximalIdeal (Localization.AtPrime p))
    have := isAssociatedPrime_iff.mp <| AssociatedPrimes.mem_iff.mp
      (associatedPrimes.mem_associatedPrimes_atPrime_of_mem_associatedPrimes pass)
    rcases this.2 with ⟨x, hx⟩
    rcases exists_ne (α := Module.Dual p.ResidueField Nₚ') 0 with ⟨g, hg⟩
    let to_res' : Nₚ' →ₗ[Rₚ] p.ResidueField := {
      __ := g
      map_smul' r x := g.map_smul (Ideal.Quotient.mk _ r) x }
    let to_res : Nₚ →ₗ[Rₚ] p.ResidueField :=
      to_res'.comp ((maximalIdeal (Localization.AtPrime p)) • (⊤ : Submodule Rₚ Nₚ)).mkQ
    replace hx : maximalIdeal (Localization.AtPrime p) = (toSpanSingleton _ _ x).ker :=
      hx.trans (by simp [SetLike.ext_iff])
    let i : p.ResidueField →ₗ[Rₚ] Mₚ :=
      Submodule.liftQ _ (LinearMap.toSpanSingleton Rₚ Mₚ x) (le_of_eq hx)
    have inj1 : Function.Injective i :=
      LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ _ (le_of_eq hx.symm))
    let f := i.comp to_res
    have f_ne0 : f ≠ 0 := by
      intro eq0
      absurd hg
      apply LinearMap.ext (fun np' ↦ ?_)
      induction np' using Submodule.Quotient.induction_on with | _ np
      have : f np = i 0 := by simp [eq0]
      exact inj1 this
    absurd hom0
    let _ := Module.finitePresentation_of_finite R N
    contrapose! f_ne0
    exact (Module.FinitePresentation.linearEquivMapExtendScalars
      p'.asIdeal.primeCompl).symm.map_eq_zero_iff.mp (Subsingleton.eq_zero _)

end IsSMulRegular

universe v u

open RingTheory.Sequence Ideal CategoryTheory Abelian Limits

variable {R : Type u} [CommRing R]

open Pointwise ModuleCat IsSMulRegular

variable [Small.{v} R]

lemma ModuleCat.exists_isRegular_of_exists_subsingleton_ext [IsNoetherianRing R] (I : Ideal R)
    (n : ℕ) (M : ModuleCat.{v} R) [Module.Finite R M] (smul_lt : I • (⊤ : Submodule R M) < ⊤)
    (exists_N : ∃ N : ModuleCat.{v} R, Nontrivial N ∧ Module.Finite R N ∧
      Module.support R N = PrimeSpectrum.zeroLocus I ∧ ∀ i < n, Subsingleton (Ext N M i)) :
    ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ I) ∧ IsRegular M rs := by
  induction n generalizing M with
  | zero =>
    let : Nontrivial M := (Submodule.nontrivial_iff R).mp (nontrivial_of_lt _ _ smul_lt)
    use []
    simp [isRegular_iff]
  | succ n ih =>
    rcases exists_N with ⟨N, ntr, fin, h_supp, h_ext⟩
    have h_supp' := h_supp
    rw [Module.support_eq_zeroLocus, PrimeSpectrum.zeroLocus_eq_iff] at h_supp'
    -- use `Ext N M 0` vanish to obtain an `M`-regular element `x` in `Ann(N)`
    have : Subsingleton (N ⟶ M) := Ext.addEquiv₀.subsingleton_congr.mp (h_ext 0 n.zero_lt_succ)
    have : Subsingleton (N →ₗ[R] M) := ModuleCat.homAddEquiv.symm.subsingleton
    rcases subsingleton_linearMap_iff.mp this with ⟨x, mem_ann, hx⟩
    -- take a power of it to make `xᵏ` fall into `I`
    rcases le_of_le_of_eq Ideal.le_radical h_supp' mem_ann with ⟨k, hk⟩
    -- prepare to apply induction hypotesis to `M ⧸ xᵏM`
    have ne : I • (⊤ : Submodule R (QuotSMulTop (x ^ k) M)) ≠ ⊤ := by
      by_contra eq
      absurd congrArg (Submodule.comap (Submodule.mkQ _)) eq
      simpa [Submodule.comap_smul_top_of_surjective I _ (Submodule.mkQ_surjective _),
        Submodule.smul_mono_left ((span_singleton_le_iff_mem I).mpr hk),
        ← Submodule.ideal_span_singleton_smul] using smul_lt.ne
    -- verify that `N` indeed make `M ⧸ xᵏM` satisfy the induction hypothesis
    have exists_N' : (∃ N : ModuleCat R, Nontrivial N ∧ Module.Finite R N ∧
        Module.support R N = PrimeSpectrum.zeroLocus I ∧
          ∀ i < n, Subsingleton (Abelian.Ext N (ModuleCat.of R (QuotSMulTop (x ^ k) M)) i)) := by
      use N
      simp only [ntr, fin, h_supp, true_and]
      intro i hi
      -- the vanishing of `Ext` is obtained from the (covariant) long exact sequence given by
      -- `M.smulShortComplex (x ^ k)`
      have zero1 : IsZero (AddCommGrpCat.of (Ext N M i)) :=
        @AddCommGrpCat.isZero_of_subsingleton _ (h_ext i (Nat.lt_add_right 1 hi))
      have zero2 : IsZero (AddCommGrpCat.of (Ext N M (i + 1))) :=
        @AddCommGrpCat.isZero_of_subsingleton _ (h_ext (i + 1) (Nat.add_lt_add_right hi 1))
      exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
        ((Ext.covariant_sequence_exact₃' N (hx.pow k).smulShortComplex_shortExact) i (i + 1) rfl)
        (zero1.eq_zero_of_src _) (zero2.eq_zero_of_tgt _)
    rcases ih (ModuleCat.of R (QuotSMulTop (x ^ k) M)) ne.lt_top exists_N' with ⟨rs, len, mem, reg⟩
    use x ^ k :: rs
    simpa [len, hk] using ⟨mem, hx.pow k, reg⟩

set_option backward.isDefEq.respectTransparency false in
lemma CategoryTheory.Abelian.Ext.pow_mono_of_mono (a : R) (k : ℕ) (i : ℕ) {M N : ModuleCat.{v} R}
    (f_mono : Mono (AddCommGrpCat.ofHom ((Ext.mk₀ (smulShortComplex M a).f).postcomp
    N (add_zero i)))) : Mono (AddCommGrpCat.ofHom ((Ext.mk₀ (smulShortComplex M (a ^ k)).f).postcomp
    N (add_zero i))) := by
  have (x : R) : Mono (AddCommGrpCat.ofHom ((Ext.mk₀ (smulShortComplex M x).f).postcomp
    N (add_zero i))) ↔ IsSMulRegular (Ext N M i) x := by
    simp only [IsSMulRegular, AddCommGrpCat.mono_iff_injective]
    congr!
    ext
    rw [smulShortComplex_f_eq_smul_id]
    simp [smulShortComplex, Ext.mk₀_smul]
  rw [this] at f_mono ⊢
  exact f_mono.pow k

lemma ModuleCat.subsingleton_ext_of_exists_isRegular [IsNoetherianRing R] (I : Ideal R) (n : ℕ)
    (N : ModuleCat.{v} R) [Nfin : Module.Finite R N]
    (Nsupp : Module.support R N ⊆ PrimeSpectrum.zeroLocus I)
    (M : ModuleCat.{v} R) [Module.Finite R M] (smul_lt : I • (⊤ : Submodule R M) < ⊤)
    (rs : List R) (len : rs.length = n) (mem : ∀ r ∈ rs, r ∈ I) (reg : IsRegular M rs) :
    ∀ i < n, Subsingleton (Ext N M i) := by
  induction n generalizing M rs with
  | zero => simp
  | succ n ih =>
    rintro i hi
    have le_rad := Nsupp
    rw [Module.support_eq_zeroLocus, PrimeSpectrum.zeroLocus_subset_zeroLocus_iff] at le_rad
    match rs with
    | [] =>
      absurd len
      simp
    | a :: rs' =>
      -- find a positive power of `a` lying in `Ann(N)`
      rcases le_rad (mem a List.mem_cons_self) with ⟨k, hk⟩
      simp only [isRegular_cons_iff] at reg
      simp only [List.mem_cons, forall_eq_or_imp] at mem
      simp only [List.length_cons, Nat.add_left_inj] at len
      -- prepare to apply induction hypothesis to `M/aM`
      have ne : I • (⊤ : Submodule R (QuotSMulTop a M)) ≠ ⊤ := by
        by_contra eq
        absurd congrArg (Submodule.comap (Submodule.mkQ _)) eq
        simpa [Submodule.comap_smul_top_of_surjective I _ (Submodule.mkQ_surjective _),
          Submodule.smul_mono_left ((span_singleton_le_iff_mem I).mpr mem.1),
          ← Submodule.ideal_span_singleton_smul] using smul_lt.ne
      by_cases eq0 : i = 0
      · -- vanishing of `Ext N M 0` follows from `aᵏ ∈ Ann(N)`
        rw [eq0]
        have : Subsingleton (N →ₗ[R] M) := subsingleton_linearMap_iff.mpr ⟨a ^ k, hk, reg.1.pow k⟩
        exact (Ext.addEquiv₀.trans ModuleCat.homAddEquiv).subsingleton
      · let g := (AddCommGrpCat.ofHom ((Ext.mk₀ (smulShortComplex M a).f).postcomp N (add_zero i)))
        -- from the (covariant) long exact sequence given by `M.smulShortComplex a`
        -- we obtain scalar multiple by `a` on `Ext N M i` is injective
        have mono_g : Mono g := by
          apply (Ext.covariant_sequence_exact₁' N reg.1.smulShortComplex_shortExact (i - 1) i
            (Nat.succ_pred_eq_of_ne_zero eq0)).mono_g (IsZero.eq_zero_of_src _ _)
          exact @AddCommGrpCat.isZero_of_subsingleton _
            (ih (ModuleCat.of R (QuotSMulTop a M)) ne.lt_top rs' len mem.2 reg.2 (i - 1) (by omega))
        let gk := AddCommGrpCat.ofHom
          ((Ext.mk₀ (M.smulShortComplex (a ^ k)).f).postcomp N (add_zero i))
        have mono_gk := Ext.pow_mono_of_mono a k i mono_g
        -- scalar multiple by `aᵏ` on `Ext N M i` is zero since `aᵏ ∈ Ann(N)`, so `Ext N M i` vanish
        have zero_gk : gk = 0 := Ext.smul_id_postcomp_eq_zero_of_mem_ann hk i
        exact AddCommGrpCat.subsingleton_of_isZero (IsZero.of_mono_eq_zero _ zero_gk)

/--
**The Rees theorem**
For any `n : ℕ`, Noetherian ring `R`, `I : Ideal R`, and finitely generated and nontrivial
`R`-module `M` satisfying `IM < M`, the following are equivalent:
· for any `N : ModuleCat R` finitely generated and nontrivial with support contained in the
  zero locus of `I`, `∀ i < n, Ext N M i = 0`
· `∀ i < n, Ext (A⧸I) M i = 0`
· there exists a `N : ModuleCat R` finitely generated and nontrivial with support equal to the
  zero locus of `I`, `∀ i < n, Ext N M i = 0`
· there exists a `M`-regular sequence of length `n` with every element in `I`
-/
lemma ModuleCat.exists_isRegular_tfae [IsNoetherianRing R] (I : Ideal R) (n : ℕ)
    (M : ModuleCat.{v} R) [Module.Finite R M] (smul_lt : I • (⊤ : Submodule R M) < ⊤) :
    [∀ N : ModuleCat.{v} R, Nontrivial N → Module.Finite R N →
      Module.support R N ⊆ PrimeSpectrum.zeroLocus I → ∀ i < n, Subsingleton (Ext N M i),
      ∀ i < n, Subsingleton (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M i),
      ∃ N : ModuleCat R, Nontrivial N ∧ Module.Finite R N ∧
      Module.support R N = PrimeSpectrum.zeroLocus I ∧ ∀ i < n, Subsingleton (Ext N M i),
      ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ I) ∧ RingTheory.Sequence.IsRegular M rs
      ].TFAE := by
  -- two main implications `3 → 4` and `4 → 1` are separated out, the rest are trivial
  have ntrQ : Nontrivial (R ⧸ I) := by
    apply Submodule.Quotient.nontrivial_iff.mpr
    by_contra eq
    simp [eq] at smul_lt
  have suppQ : Module.support R (Shrink.{v} (R ⧸ I)) = PrimeSpectrum.zeroLocus I := by
    rw [(Shrink.linearEquiv R _).support_eq, Module.support_eq_zeroLocus, annihilator_quotient]
  tfae_have 1 → 2 := fun h1 i hi ↦ h1 (ModuleCat.of R (Shrink.{v} (R ⧸ I)))
    inferInstance inferInstance suppQ.subset i hi
  tfae_have 2 → 3 := fun h2 ↦ ⟨(ModuleCat.of R (Shrink.{v} (R ⧸ I))),
    inferInstance, Module.Finite.equiv (Shrink.linearEquiv R (R ⧸ I)).symm, suppQ, h2⟩
  tfae_have 3 → 4 := exists_isRegular_of_exists_subsingleton_ext I n M smul_lt
  tfae_have 4 → 1 := fun ⟨rs, len, mem, reg⟩ N Nntr Nfin Nsupp i hi ↦
    subsingleton_ext_of_exists_isRegular I n N Nsupp M smul_lt rs len mem reg i hi
  tfae_finish
