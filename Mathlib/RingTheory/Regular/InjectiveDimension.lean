/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Algebra.Shrink
public import Mathlib.Algebra.FiveLemma
public import Mathlib.CategoryTheory.Abelian.Injective.Dimension
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.Baer
public import Mathlib.Algebra.Category.ModuleCat.Ext.Finite
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Regular.Category
public import Mathlib.RingTheory.Regular.IsSMulRegular

/-!

# The Definition of Gorenstein (Local) Ring

-/

@[expose] public section


section ENat

lemma WithBot.add_one_le_zero_iff_eq_bot' (a : WithBot ℕ∞) :
    a + 1 ≤ 0 ↔ a = ⊥ := by
  induction a with
  | bot => simp
  | coe a => simp [← WithBot.coe_one, ← WithBot.coe_add]

end ENat

universe v u

variable (R : Type u) [CommRing R]

open IsLocalRing

variable {R} in
lemma quotSMulTop_nontrivial'' [IsLocalRing R] {x : R} (mem : x ∈ maximalIdeal R)
    (L : Type*) [AddCommGroup L] [Module R L] [Module.Finite R L] [Nontrivial L] :
    Nontrivial (QuotSMulTop x L) := by
  apply Submodule.Quotient.nontrivial_iff.mpr (Ne.symm _)
  apply Submodule.top_ne_pointwise_smul_of_mem_jacobson_annihilator
  exact IsLocalRing.maximalIdeal_le_jacobson _ mem

lemma exist_nat_eq' [FiniteRingKrullDim R] : ∃ n : ℕ, ringKrullDim R = n := by
  have : (ringKrullDim R).unbot ringKrullDim_ne_bot ≠ ⊤ := by
    by_contra eq
    rw [← WithBot.coe_inj, WithBot.coe_unbot, WithBot.coe_top] at eq
    exact ringKrullDim_ne_top eq
  use ((ringKrullDim R).unbot ringKrullDim_ne_bot).toNat
  exact (WithBot.coe_unbot (ringKrullDim R) ringKrullDim_ne_bot).symm.trans
    (WithBot.coe_inj.mpr (ENat.coe_toNat this).symm)

variable {R} in
lemma IsLocalRing.ResidueField.map_injective [IsLocalRing R] {S : Type*} [CommRing S]
    [IsLocalRing S] (f : R →+* S) [IsLocalHom f] :
    Function.Injective (ResidueField.map f) := by
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
  intro x hx
  simpa only [map_eq_zero] using hx

variable {R} in
lemma IsLocalRing.ResidueField.map_bijective_of_surjective [IsLocalRing R] {S : Type*} [CommRing S]
    [IsLocalRing S] (f : R →+* S) (surj : Function.Surjective f) [IsLocalHom f] :
    Function.Bijective (ResidueField.map f) := by
  refine ⟨ResidueField.map_injective f, ?_⟩
  apply Ideal.Quotient.lift_surjective_of_surjective
  convert Function.Surjective.comp (Ideal.Quotient.mk_surjective (I := (maximalIdeal S))) surj

open CategoryTheory Abelian Module

section

variable {R} [IsLocalRing R] [IsNoetherianRing R] [Small.{v} R]

omit [IsLocalRing R] in
lemma ext_subsingleton_of_support_subset (N M : ModuleCat.{v} R) [Nfin : Module.Finite R N] (n : ℕ)
    (h : support R N ⊆ {p | Subsingleton (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ p.1))) M n)}) :
    Subsingleton (Ext N M n) := by
  refine (IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime
    (motive := fun L ↦ (support R L ⊆ {p | Subsingleton
      (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ p.1))) M n)} →
      Subsingleton (Ext (ModuleCat.of R L) M n))) R Nfin) ?_ ?_ ?_ h
  · intro N _ _ _ sub _
    let _ : HasProjectiveDimensionLT (ModuleCat.of R N) 0 :=
      (ModuleCat.isZero_of_iff_subsingleton.mpr sub).hasProjectiveDimensionLT_zero
    exact HasProjectiveDimensionLT.subsingleton (ModuleCat.of R N) 0 n n.zero_le M
  · intro N _ _ _ p e h
    have mem : p ∈ support R N := by
      rw [e.support_eq, Module.mem_support_iff_of_finite, Ideal.annihilator_quotient]
    let e' : ModuleCat.of R N ≅ ModuleCat.of R (Shrink.{v, u} (R ⧸ p.asIdeal)) :=
      (e.trans (Shrink.linearEquiv R _).symm).toModuleIso
    have := (((extFunctor n).mapIso e'.op).app M).addCommGroupIsoToAddEquiv.subsingleton_congr
    simp only [extFunctor, extFunctorObj_obj_coe] at this
    simpa [← this] using h mem
  · intro N₁ _ _ _ N₂ _ _ _ N₃ _ _ _ f g inj surj exac h1 h3 h2
    simp only [Module.support_of_exact exac inj surj, Set.union_subset_iff] at h2
    let S : ShortComplex (ModuleCat.{v} R) := {
      f := ModuleCat.ofHom f
      g := ModuleCat.ofHom g
      zero := by
        rw [← ModuleCat.ofHom_comp, exac.linearMap_comp_eq_zero]
        rfl }
    have S_exact : S.ShortExact := {
      exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mpr exac
      mono_f := (ModuleCat.mono_iff_injective S.f).mpr inj
      epi_g := (ModuleCat.epi_iff_surjective S.g).mpr surj }
    have := (Ext.contravariant_sequence_exact₂' S_exact M n).isZero_X₂
      ((@AddCommGrpCat.isZero_of_subsingleton _ (h3 h2.2)).eq_zero_of_src _)
      ((@AddCommGrpCat.isZero_of_subsingleton _ (h1 h2.1)).eq_zero_of_tgt _)
    exact AddCommGrpCat.subsingleton_of_isZero this

set_option backward.isDefEq.respectTransparency false in
lemma ext_subsingleton_of_all_gt (M : ModuleCat.{v} R) [Module.Finite R M] (n : ℕ)
    (p : Ideal R) [p.IsPrime] (ne : p ≠ maximalIdeal R) (h : ∀ q > p, q.IsPrime →
      Subsingleton (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ q))) M (n + 1))) :
    Subsingleton (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ p))) M n) := by
  have plt : p < maximalIdeal R :=  lt_of_le_of_ne (le_maximalIdeal_of_isPrime p) ne
  obtain ⟨x, hx, nmem⟩ : ∃ x ∈ maximalIdeal R, x ∉ p := Set.exists_of_ssubset plt
  let _ : Small.{v} (QuotSMulTop x (R ⧸ p)) :=
    small_of_surjective (Submodule.Quotient.mk_surjective _)
  let fin : Module.Finite R (Shrink.{v, u} (R ⧸ p)) :=
    Module.Finite.equiv (Shrink.linearEquiv R _).symm
  let _ : Nontrivial (QuotSMulTop x (Shrink.{v, u} (R ⧸ p))) :=
    quotSMulTop_nontrivial'' hx _
  have : Subsingleton (Ext (ModuleCat.of R (QuotSMulTop x (Shrink.{v, u} (R ⧸ p)))) M (n + 1)) := by
    apply ext_subsingleton_of_support_subset
    intro q hq
    apply h q.1 _ q.2
    simp only [support_quotSMulTop, (Shrink.linearEquiv R (R ⧸ p)).support_eq, Set.mem_inter_iff,
      PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe] at hq
    have : q.asIdeal ≠ p := ne_of_mem_of_not_mem' hq.2 nmem
    apply lt_of_le_of_ne _ (ne_of_mem_of_not_mem' hq.2 nmem).symm
    apply le_of_eq_of_le Ideal.annihilator_quotient.symm (Module.annihilator_le_of_mem_support hq.1)
  let S := (ModuleCat.of R (Shrink.{v, u} (R ⧸ p))).smulShortComplex x
  have reg : IsSMulRegular (Shrink.{v, u} (R ⧸ p)) x := by
    rw [(Shrink.linearEquiv.{v} R _).isSMulRegular_congr, isSMulRegular_iff_right_eq_zero_of_smul]
    intro r hr
    simpa [Algebra.smul_def, Ideal.Quotient.eq_zero_iff_mem, nmem] using hr
  have S_exact : S.ShortExact := IsSMulRegular.smulShortComplex_shortExact reg
  have exac := Ext.contravariant_sequence_exact₁' S_exact M n (n + 1) (add_comm 1 n)
  have epi := exac.epi_f ((@AddCommGrpCat.isZero_of_subsingleton _ this).eq_zero_of_tgt _)
  have : S.f = x • 𝟙 (ModuleCat.of R (Shrink.{v, u} (R ⧸ p))) := by
    ext
    simp [S]
  simp only [S, this, AddCommGrpCat.epi_iff_surjective, AddCommGrpCat.hom_ofHom] at epi
  have : x ∈ (Module.annihilator R (Ext S.X₂ M n)).jacobson :=
    (IsLocalRing.maximalIdeal_le_jacobson _) hx
  by_contra ntr
  let _ : Nontrivial (Ext S.X₂ M n) := not_subsingleton_iff_nontrivial.mp ntr
  let _ : Module.Finite R S.X₂ := fin
  absurd Submodule.top_ne_pointwise_smul_of_mem_jacobson_annihilator this
  rw [eq_comm, eq_top_iff]
  intro y hy
  rcases epi y with ⟨z, hz⟩
  simp only [ModuleCat.smulShortComplex_X₁, ModuleCat.smulShortComplex_X₂, Ext.mk₀_smul,
      Ext.bilinearComp_apply_apply, Ext.smul_comp, Ext.mk₀_id_comp] at hz
  simpa [← hz] using Submodule.smul_mem_pointwise_smul _ _ ⊤ trivial

lemma ext_vanish_of_residueField_vanish (M : ModuleCat.{v} R) (n : ℕ) [Module.Finite R M]
    (h : ∀ i ≥ n, Subsingleton (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R))) M i)) :
    ∀ i ≥ n, ∀ N : ModuleCat.{v} R, Subsingleton (Ext N M i) := by
  intro i hi N
  apply ModuleCat.ext_subsingleton_of_quotients
  intro I
  let _ := Module.Finite.equiv (Shrink.linearEquiv R (R ⧸ I)).symm
  apply ext_subsingleton_of_support_subset
  intro p foo
  clear foo
  simp only [Set.mem_setOf_eq]
  have (n : ℕ) : ringKrullDim (R ⧸ p.1) ≤ n →
    Subsingleton (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ p.asIdeal))) M i) := by
    induction n generalizing i hi p with
    | zero =>
      intro hp
      have : p.1 = maximalIdeal R := by
        rw [← isMaximal_iff, Ideal.Quotient.maximal_ideal_iff_isField_quotient]
        rw [← Ring.krullDimLE_iff] at hp
        exact Ring.KrullDimLE.isField_of_isDomain
      exact this ▸ h i hi
    | succ n ih =>
      intro hp
      by_cases hpm : p.1 = maximalIdeal R
      · rw [hpm]
        exact h i hi
      · apply ext_subsingleton_of_all_gt M i p.1 hpm
        intro q hqp hq
        let q : PrimeSpectrum R := ⟨q, hq⟩
        have : ringKrullDim (R ⧸ q.1) ≤ n := by
          rw [← ENat.WithBot.add_le_add_natCast_right_iff]
          apply le_trans _ hp
          obtain ⟨r, hrq, hrp⟩ := Set.exists_of_ssubset hqp
          apply ringKrullDim_succ_le_of_surjective (r := Ideal.Quotient.mk p.1 r)
            (Ideal.Quotient.factor hqp.le) (Ideal.Quotient.factor_surjective hqp.le)
          · simpa using Ideal.Quotient.eq_zero_iff_mem.not.mpr hrp
          · simpa using Ideal.Quotient.eq_zero_iff_mem.mpr hrq
        apply ih (i + 1) (Nat.le_add_right_of_le hi) this
  rcases exist_nat_eq' R with ⟨n, hn⟩
  apply this n
  simpa [← hn] using ringKrullDim_quotient_le p.1

set_option backward.isDefEq.respectTransparency false in
lemma injectiveDimension_eq_sInf_of_finite (M : ModuleCat.{v} R) [Module.Finite R M] :
    injectiveDimension M = sInf {n : WithBot ℕ∞ | ∀ (i : ℕ), n < i →
      Subsingleton (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R))) M i)} := by
  simp only [injectiveDimension]
  congr! 3
  rename_i n
  refine ⟨fun h i hi ↦ ?_, fun h i hi ↦ ?_⟩
  · let _ := h i hi
    exact HasInjectiveDimensionLT.subsingleton M i i (le_refl i) _
  · rw [hasInjectiveDimensionLT_iff]
    intro j hj N e
    refine @Subsingleton.eq_zero _ _ ?_ e
    apply ext_vanish_of_residueField_vanish M i _ j hj N
    intro k hk
    exact h k (lt_of_lt_of_le hi (Nat.cast_le.mpr hk))

set_option backward.isDefEq.respectTransparency false in
lemma injectiveDimension_lt_iff_of_finite (M : ModuleCat.{v} R) [Module.Finite R M] (n : ℕ) :
    injectiveDimension M < n ↔ ∀ (i : ℕ), n ≤ i →
      Subsingleton (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R))) M i) := by
  rw [injectiveDimension_eq_sInf_of_finite]
  refine ⟨fun h i hi ↦ ?_, fun h ↦ sInf_lt_iff.2 ?_⟩
  · have : sInf {n : WithBot ℕ∞ | ∀ (i : ℕ), n < ↑i →
      Subsingleton (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R))) M i)} ∈ _ :=
      csInf_mem ⟨⊤, by simp⟩
    exact this i (lt_of_lt_of_le h (Nat.cast_le.mpr hi))
  · obtain _ | n := n
    · exact ⟨⊥, fun i hi ↦ h i (Nat.zero_le i) , by decide⟩
    · exact ⟨n, fun i hi ↦ h i (Nat.cast_lt.mp hi), by simp [ENat.WithBot.lt_add_one_iff]⟩

end

section

variable {R}

section restrictScalars

universe u'

variable {R' : Type u'} [CommRing R'] (f : R →+* R')

instance ModuleCat.restrictScalars_additive :
    (ModuleCat.restrictScalars.{v} f).Additive where
  map_add := by simp

lemma ModuleCat.restrictScalars_map_exact' (S : ShortComplex (ModuleCat.{v} R')) (h : S.Exact) :
    (S.map (ModuleCat.restrictScalars.{v} f)).Exact := by
  rw [CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at h ⊢
  exact h

instance ModuleCat.restrictScalars_preservesFiniteLimits :
    Limits.PreservesFiniteLimits (ModuleCat.restrictScalars.{v} f) := by
  have := ((CategoryTheory.Functor.exact_tfae (ModuleCat.restrictScalars.{v} f)).out 1 3).mp
    (ModuleCat.restrictScalars_map_exact' f)
  exact this.1

instance ModuleCat.restrictScalars_preservesFiniteColimits :
    Limits.PreservesFiniteColimits (ModuleCat.restrictScalars.{v} f) := by
  have := ((CategoryTheory.Functor.exact_tfae (ModuleCat.restrictScalars.{v} f)).out 1 3).mp
    (ModuleCat.restrictScalars_map_exact' f)
  exact this.2

/-- Restricting scalar by surjective ring homomorphism is fully faithful. -/
def ModuleCat.restrictScalars_fullyFaithful_of_surjective (h : Function.Surjective f) :
    (ModuleCat.restrictScalars.{v} f).FullyFaithful where
  preimage {X Y} g := ofHom
    { __ := g.hom
      map_smul' r' x := by
        let _ := Module.compHom X f
        rcases h r' with ⟨r, hr⟩
        rw [← hr]
        exact map_smul g.hom r x }
  map_preimage g := by
    ext
    rfl
  preimage_map g := by
    ext
    rfl

end restrictScalars

set_option backward.isDefEq.respectTransparency false in
lemma hasProjectiveDimensionLE_finsupp_quotient_regular [Small.{v} R] (ι : Type v) {x : R}
    (regR : IsSMulRegular R x) :
    HasProjectiveDimensionLE (ModuleCat.of R (ι →₀ Shrink.{v} (R ⧸ Ideal.span {x}))) 1 := by
  let f' : Shrink.{v} R →ₗ[R] Shrink.{v} R := ((Shrink.linearEquiv R R).symm.toLinearMap.comp
    (x • LinearMap.id)).comp (Shrink.linearEquiv R R).toLinearMap
  let g' : Shrink.{v} R →ₗ[R] Shrink.{v} (R ⧸ Ideal.span {x}) :=
    ((Shrink.linearEquiv R _).symm.toLinearMap.comp
      (Ideal.Quotient.mkₐ R (Ideal.span {x})).toLinearMap).comp (Shrink.linearEquiv R R).toLinearMap
  have inj : Function.Injective f' := by simpa [f'] using regR
  have surj : Function.Surjective g' := by simpa [g'] using Ideal.Quotient.mk_surjective
  have exac : Function.Exact f' g' := by
    intro y
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, AlgHom.coe_toLinearMap,
      Ideal.Quotient.mkₐ_eq_mk, Function.comp_apply, EmbeddingLike.map_eq_zero_iff,
      EquivLike.range_comp, Set.mem_range, LinearMap.smul_apply, LinearMap.id_coe,
      LinearEquiv.symm_apply_eq, id_eq, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton', smul_eq_mul, mul_comm, g', f']
  let S : ShortComplex (ModuleCat.{v} R) := {
    X₁ := ModuleCat.of R (ι →₀ Shrink.{v} R)
    X₂ := ModuleCat.of R (ι →₀ Shrink.{v} R)
    X₃ := ModuleCat.of R (ι →₀ Shrink.{v} (R ⧸ Ideal.span {x}))
    f := ModuleCat.ofHom (Finsupp.mapRange.linearMap f')
    g := ModuleCat.ofHom (Finsupp.mapRange.linearMap g')
    zero := by
      rw [← ModuleCat.ofHom_comp, ← Finsupp.mapRange.linearMap_comp,
        exac.linearMap_comp_eq_zero]
      ext
      simp }
  have S_exact : S.ShortExact := {
    exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mpr (by
      simp [LinearMap.exact_iff, S, Finsupp.ker_mapRange, LinearMap.exact_iff.mp exac,
        Finsupp.range_mapRange_linearMap f' (LinearMap.ker_eq_bot.mpr inj)] )
    mono_f := (ModuleCat.mono_iff_injective _).mpr (Finsupp.mapRange_injective f' (map_zero _) inj)
    epi_g := (ModuleCat.epi_iff_surjective _).mpr
      (Finsupp.mapRange_surjective g' (map_zero _) surj) }
  have : Projective (ModuleCat.of R (ι →₀ Shrink.{v} R)) := ModuleCat.projective_of_free
    ⟨Finsupp.mapRange.linearEquiv (Shrink.linearEquiv R R)⟩
  exact S_exact.hasProjectiveDimensionLT_X₃ 1 inferInstance inferInstance

variable [Small.{v} R]

set_option backward.isDefEq.respectTransparency false in
open Limits in
lemma extClass_postcomp_bijective_of_isSMulRegular {M : ModuleCat.{v} R} {x : R}
    (regM : IsSMulRegular M x) (N : ModuleCat.{v} R) (ann : x • 𝟙 N = 0) :
    Function.Bijective (regM.smulShortComplex_shortExact.extClass.postcomp
    N (rfl : 0 + 1 = 0 + 1)) := by
  refine ⟨?_, fun y ↦ Ext.covariant_sequence_exact₁ _ regM.smulShortComplex_shortExact y ?_ rfl⟩
  · apply (AddCommGrpCat.mono_iff_injective _).mp ((Ext.covariant_sequence_exact₃' N
      regM.smulShortComplex_shortExact 0 1 (zero_add 1)).mono_g (IsZero.eq_zero_of_src ?_ _))
    apply @AddCommGrpCat.isZero_of_subsingleton _ ?_
    apply Ext.homEquiv₀.subsingleton_congr.mpr
    apply subsingleton_of_forall_eq 0 fun f ↦ ModuleCat.hom_ext (LinearMap.ext fun t ↦ regM ?_)
    have : (x • 𝟙 N) t = x • t := by simp
    simp [smul_zero, ← map_smul, ← this, ann, map_zero]
  · conv in ShortComplex.f ?_ => change x • (𝟙 M)
    rw [← Ext.mk₀_id_comp (y.comp (Ext.mk₀ (x • 𝟙 M)) rfl), Ext.mk₀_smul,
      Ext.comp_smul, Ext.comp_smul, ← Ext.smul_comp, ← Ext.mk₀_smul]
    simp [ann]

set_option backward.isDefEq.respectTransparency false in
/-- The map `Ext N (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x ↑M)) n →+
  Ext ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {x}))).obj N) M (n + 1)`
  is bijective. -/
theorem extClass_comp_mapExt_bijective {M : ModuleCat.{v} R} {x : R} (regR : IsSMulRegular R x)
    (regM : IsSMulRegular M x) (N : ModuleCat.{v} (R ⧸ Ideal.span {x})) (n : ℕ) :
    Function.Bijective ((regM.smulShortComplex_shortExact.extClass.postcomp
    ((ModuleCat.restrictScalars.{v} (Ideal.Quotient.mk (Ideal.span {x}))).obj N) rfl).comp
    ((ModuleCat.restrictScalars.{v} (Ideal.Quotient.mk (Ideal.span {x}))).mapExtAddHom N
    (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x M)) n)) := by
  let Fr := (ModuleCat.restrictScalars.{v} (Ideal.Quotient.mk (Ideal.span {x})))
  induction n generalizing N
  · simp only [ModuleCat.smulShortComplex_X₁, Nat.reduceAdd, AddMonoidHom.coe_comp]
    refine Function.Bijective.comp ?_ ?_
    · apply extClass_postcomp_bijective_of_isSMulRegular regM
      ext u
      simp
    · change Function.Bijective (Ext.mapExactFunctor _)
      rw [Ext.mapExactFunctor₀, Equiv.comp_bijective, Equiv.bijective_comp]
      apply Functor.FullyFaithful.map_bijective
      exact ModuleCat.restrictScalars_fullyFaithful_of_surjective _ Ideal.Quotient.mk_surjective
  · rename_i n ih
    let S := N.projectiveShortComplex
    have S_exact : S.ShortExact := N.shortExact_projectiveShortComplex
    let _ : HasProjectiveDimensionLT (S.map Fr).X₂ 2 :=
      hasProjectiveDimensionLE_finsupp_quotient_regular N regR
    let MxM := (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x M))
    let f : Ext S.X₂ MxM n →+ Ext S.X₁ MxM n := (Ext.mk₀ S.f).precomp MxM (zero_add n)
    let g : Ext S.X₁ MxM n →+ Ext S.X₃ MxM (n + 1) := S_exact.extClass.precomp MxM (add_comm 1 n)
    have exac1 : Function.Exact f g := (ShortComplex.ab_exact_iff_function_exact  _).mp
      (Ext.contravariant_sequence_exact₁' S_exact MxM n (n + 1) (add_comm 1 n))
    have surj1 : Function.Surjective g := precomp_extClass_surjective_of_projective_X₂ MxM S_exact n
    let f' : Ext (S.map Fr).X₂ M (n + 1) →+ Ext (S.map Fr).X₁ M (n + 1) :=
      (Ext.mk₀ (S.map Fr).f).precomp M (zero_add (n + 1))
    let g' : Ext (S.map Fr).X₁ M (n + 1) →+ Ext (S.map Fr).X₃ M (n + 2) :=
      (S_exact.map_of_exact Fr).extClass.precomp M (add_comm 1 (n + 1))
    have exac2 : Function.Exact f' g' :=
      (ShortComplex.ab_exact_iff_function_exact  _).mp (Ext.contravariant_sequence_exact₁'
      (S_exact.map_of_exact Fr) M (n + 1) (n + 2) (add_comm 1 (n + 1)))
    have isz2 : Limits.IsZero (AddCommGrpCat.of (Ext (S.map Fr).X₂ M (n + 2))) :=
      @AddCommGrpCat.isZero_of_subsingleton _ (HasProjectiveDimensionLT.subsingleton (S.map Fr).X₂
        2 (n + 2) (Nat.le_add_left _ n) M)
    have surj2 : Function.Surjective g' := (AddCommGrpCat.epi_iff_surjective _).mp
      ((Ext.contravariant_sequence_exact₃' (S_exact.map_of_exact Fr) M (n + 1) (n + 2)
        (add_comm 1 (n + 1))).epi_f (isz2.eq_zero_of_tgt _))
    let ft (N : ModuleCat.{v} (R ⧸ Ideal.span {x})) (m : ℕ) :=
      ((regM.smulShortComplex_shortExact.extClass.postcomp (Fr.obj N) rfl).comp
      (Fr.mapExtAddHom N (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x M)) m))
    apply AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact f g f' g'
      (ft S.X₂ n) (ft S.X₁ n) (ft S.X₃ (n + 1)) ?_ ?_
      exac1 exac2 (ih S.X₂).2 (ih S.X₁) surj1 surj2
    · ext z
      have : (Ext.mk₀ (Fr.map S.f)).comp (z.mapExactFunctor Fr) (zero_add n) =
        (((Ext.mk₀ S.f).comp z (zero_add n)).mapExactFunctor Fr) := by
        rw [Ext.mapExt_comp_eq_comp_mapExt, Ext.mapExt_mk₀_eq_mk₀_map]
      apply (Ext.comp_assoc _ _ _ (zero_add n) rfl (zero_add (n + 1))).symm.trans
      exact congrFun (congrFun (congrFun (congrArg Ext.comp this) _) (n + 1)) rfl
    · ext z
      have : (S_exact.map_of_exact Fr).extClass.comp (z.mapExactFunctor Fr) (add_comm 1 n) =
        (S_exact.extClass.comp z (add_comm 1 n)).mapExactFunctor Fr := by
        rw [Ext.mapExt_comp_eq_comp_mapExt, Ext.mapExt_extClass_eq_extClass_map]
      apply (Ext.comp_assoc _ _ _ (add_comm 1 n) rfl (add_comm 1 (n + 1))).symm.trans
      exact congrFun (congrFun (congrFun (congrArg Ext.comp this) _) (n + 2)) rfl

end

section

lemma Function.Bijective.subsingleton_congr {α β : Type*} {f : α → β} (bij : Function.Bijective f) :
    Subsingleton α ↔ Subsingleton β :=
  ⟨fun _ ↦ bij.2.subsingleton, fun _ ↦ bij.1.subsingleton⟩

variable {R} [IsLocalRing R]

section

variable [Small.{v} R]

set_option backward.isDefEq.respectTransparency false in
lemma ext_residueField_subsingleton_iff {M : ModuleCat.{v} R} {x : R}
    (regR : IsSMulRegular R x) (regM : IsSMulRegular M x) (mem : x ∈ maximalIdeal R) (n : ℕ) :
    letI : IsLocalRing (R ⧸ Ideal.span {x}) :=
      have : Nontrivial (R ⧸ Ideal.span {x}) :=
        Ideal.Quotient.nontrivial_iff.mpr (by simpa [← Submodule.ideal_span_singleton_smul])
      have : IsLocalHom (Ideal.Quotient.mk (Ideal.span {x})) :=
        IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
      IsLocalRing.of_surjective (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective
    Subsingleton (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R))) M (n + 1)) ↔
    Subsingleton (Ext (ModuleCat.of (R ⧸ Ideal.span {x})
    (Shrink.{v} ((R ⧸ Ideal.span {x}) ⧸ maximalIdeal (R ⧸ Ideal.span {x}))))
    (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x M)) n) := by
  let _ : Nontrivial (R ⧸ Ideal.span {x}) :=
      Ideal.Quotient.nontrivial_iff.mpr (by simpa [← Submodule.ideal_span_singleton_smul])
  let _ : IsLocalHom (Ideal.Quotient.mk (Ideal.span {x})) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  let _ : IsLocalRing (R ⧸ Ideal.span {x}) :=
    IsLocalRing.of_surjective (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective
  let k' := (ModuleCat.of (R ⧸ Ideal.span {x})
    (Shrink.{v} ((R ⧸ Ideal.span {x}) ⧸ maximalIdeal (R ⧸ Ideal.span {x}))))
  let e' : (R ⧸ maximalIdeal R) ≃ₗ[R] (R ⧸ Ideal.span {x}) ⧸ maximalIdeal (R ⧸ Ideal.span {x}) :=
    { __ := RingEquiv.ofBijective _ (ResidueField.map_bijective_of_surjective
        (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective)
      map_smul' r y := by
        simp only [RingEquiv.toEquiv_eq_coe, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
          Equiv.toFun_as_coe, EquivLike.coe_coe, map_mul, RingEquiv.coe_ofBijective,
          RingHom.id_apply, mul_eq_mul_right_iff]
        left
        rfl }
  let e : (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R))) ≅
    (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {x}))).obj k' :=
    (((Shrink.linearEquiv.{v} R _).trans e').trans (Shrink.linearEquiv.{v} R _).symm).toModuleIso
  exact ((extClass_comp_mapExt_bijective regR regM k' n).subsingleton_congr.trans
    (((extFunctor (n + 1)).mapIso e.op).app M).addCommGroupIsoToAddEquiv.subsingleton_congr).symm

end

local instance finite_QuotSMulTop' (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (x : R) : Module.Finite (R ⧸ Ideal.span {x}) (QuotSMulTop x M) := by
  let f : M →ₛₗ[Ideal.Quotient.mk (Ideal.span {x})] (QuotSMulTop x M) := {
    __ := Submodule.mkQ _
    map_smul' r m := rfl }
  exact Module.Finite.of_surjective f (Submodule.mkQ_surjective _)

set_option backward.isDefEq.respectTransparency false in
theorem injectiveDimension_quotSMulTop_succ_eq_injectiveDimension [Small.{v} R] [IsNoetherianRing R]
    {M : ModuleCat.{v} R} [Module.Finite R M] {x : R} (regR : IsSMulRegular R x)
    (regM : IsSMulRegular M x) (mem : x ∈ maximalIdeal R) :
    injectiveDimension (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x M)) + 1 =
    injectiveDimension M := by
  let _ : IsLocalRing (R ⧸ Ideal.span {x}) :=
    have : Nontrivial (R ⧸ Ideal.span {x}) :=
      Ideal.Quotient.nontrivial_iff.mpr (by simpa [← Submodule.ideal_span_singleton_smul])
    have : IsLocalHom (Ideal.Quotient.mk (Ideal.span {x})) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    IsLocalRing.of_surjective (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective
  have sub : Subsingleton M ↔ Subsingleton (QuotSMulTop x M) := by
    refine ⟨fun h ↦ inferInstance, fun h ↦ ?_⟩
    by_contra!
    exact (not_subsingleton_iff_nontrivial.mpr (quotSMulTop_nontrivial'' mem M)) h
  have aux (n : ℕ) :
    injectiveDimension (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x M)) + 1 ≤ n ↔
    injectiveDimension M ≤ n := by
    match n with
    | 0 =>
      simp only [CharP.cast_eq_zero, WithBot.add_one_le_zero_iff_eq_bot',
        injectiveDimension_eq_bot_iff, ModuleCat.isZero_of_iff_subsingleton, ← sub]
      rw [← ModuleCat.isZero_of_iff_subsingleton (R := R), ← injectiveDimension_eq_bot_iff]
      refine ⟨fun h ↦ by simp [h], fun h ↦ ?_⟩
      rw [← Nat.cast_zero, ← ENat.WithBot.lt_add_one_iff, Nat.cast_zero, zero_add, ← Nat.cast_one,
        injectiveDimension_lt_iff_of_finite.{v} M 1] at h
      apply WithBot.lt_coe_bot.mp
      simp only [ModuleCat.of_coe, bot_eq_zero', WithBot.coe_zero]
      apply (injectiveDimension_lt_iff_of_finite.{v} M 0).mpr (fun i _ ↦ ?_)
      by_cases eq0 : i = 0
      · rw [eq0, Ext.homEquiv₀.subsingleton_congr, ModuleCat.homEquiv.subsingleton_congr]
        apply subsingleton_of_forall_eq 0 (fun f ↦ ?_)
        ext y
        have : x ∈ Module.annihilator R (Shrink.{v} (R ⧸ maximalIdeal R)) := by
          simpa [(Shrink.linearEquiv R _).annihilator_eq, Ideal.annihilator_quotient] using mem
        apply IsSMulRegular.right_eq_zero_of_smul regM
        rw [← map_smul, Module.mem_annihilator.mp this, map_zero]
      · exact h i (Nat.one_le_iff_ne_zero.mpr eq0)
    | n + 1 =>
      rw [← Nat.cast_one, Nat.cast_add, ENat.WithBot.add_le_add_natCast_right_iff, ← Nat.cast_add,
        ← ENat.WithBot.lt_add_one_iff, ← ENat.WithBot.lt_add_one_iff, ← Nat.cast_one,
        ← Nat.cast_add, ← Nat.cast_add, injectiveDimension_lt_iff_of_finite.{v},
        injectiveDimension_lt_iff_of_finite.{v}]
      refine ⟨fun h i hi ↦ ?_, fun h i hi ↦ ?_⟩
      · have : i - 1 + 1 = i := by omega
        rw [← this, ext_residueField_subsingleton_iff regR regM mem (i - 1)]
        exact h (i - 1) (Nat.le_sub_one_of_lt hi)
      · rw [← ext_residueField_subsingleton_iff regR regM mem i]
        exact h (i + 1) (Nat.add_le_add_right hi 1)
  refine eq_of_forall_ge_iff (fun N ↦ ?_)
  induction N with
  | bot =>
    simp [injectiveDimension_eq_bot_iff, ModuleCat.isZero_of_iff_subsingleton,
      ModuleCat.isZero_of_iff_subsingleton (M := M), sub]
  | coe N =>
    induction N with
    | top => simp
    | coe n => simpa using aux n

end
