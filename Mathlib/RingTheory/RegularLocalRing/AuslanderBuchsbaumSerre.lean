/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
import Mathlib.RingTheory.GlobalDimension
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.Algebra.Module.SpanRank
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Regular.AuslanderBuchsbaum
import Mathlib.RingTheory.Regular.Ischebeck
import Mathlib.RingTheory.RegularLocalRing.Basic
/-!

# A Noetherian Local Ring is Regular if its Maximal Ideal has Finite Projective Dimension

-/

universe u v

variable (R : Type u) [CommRing R]

open IsLocalRing CategoryTheory RingTheory.Sequence

local instance [Small.{v} R] (I : Ideal R) : Small.{v} I :=
  small_of_injective I.subtype_injective

lemma quotSMulTop_nontrivial' [IsLocalRing R] {x : R} (mem : x ∈ maximalIdeal R)
    (L : Type*) [AddCommGroup L] [Module R L] [Module.Finite R L] [Nontrivial L] :
    Nontrivial (QuotSMulTop x L) := by
  apply Submodule.Quotient.nontrivial_of_lt_top _ (Ne.lt_top' _)
  apply Submodule.top_ne_pointwise_smul_of_mem_jacobson_annihilator
  exact IsLocalRing.maximalIdeal_le_jacobson _ mem

local instance small_quotient_ideal' [Small.{v} R] (I : Ideal R) : Small.{v} (R ⧸ I) :=
  small_of_surjective Ideal.Quotient.mk_surjective

local instance finite_QuotSMulTop (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (x : R) : Module.Finite (R ⧸ Ideal.span {x}) (QuotSMulTop x M) := by
  let f : M →ₛₗ[Ideal.Quotient.mk (Ideal.span {x})] (QuotSMulTop x M) := {
    __ := Submodule.mkQ _
    map_smul' r m := rfl }
  exact Module.Finite.of_surjective f (Submodule.mkQ_surjective _)

open Pointwise in
lemma ker_mapRange_eq_smul_top (I : Type*) [Fintype I] (x : R) :
    LinearMap.ker (Finsupp.mapRange.linearMap (Submodule.mkQ (Ideal.span {x}))) =
    x • (⊤ : Submodule R (I →₀ R)) := by
  ext y
  simp only [Finsupp.ker_mapRange, Submodule.ker_mkQ, Finsupp.mem_submodule_iff]
  refine ⟨fun h ↦ ?_, fun h i ↦ ?_⟩
  · simp only [Ideal.mem_span_singleton', mul_comm] at h
    rw [← Finsupp.univ_sum_single y]
    refine Submodule.sum_mem _ (fun i _ ↦ ?_)
    rcases h i with ⟨z, hz⟩
    simpa only [← hz, ← Finsupp.smul_single'] using
      Submodule.smul_mem_pointwise_smul (Finsupp.single i z) x ⊤ trivial
  · rcases (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h with ⟨z, _, eq⟩
    simpa [← eq] using
      Ideal.IsTwoSided.mul_mem_of_left (z i) (Ideal.mem_span_singleton_self x)

open Pointwise in
lemma free_iff_quotSMulTop_free [IsLocalRing R] [IsNoetherianRing R] (M : Type*) [AddCommGroup M]
    [Module R M] [Module.Finite R M] {x : R} (mem : x ∈ maximalIdeal R) (reg : IsSMulRegular M x) :
    Module.Free (R ⧸ Ideal.span {x}) (QuotSMulTop x M) ↔ Module.Free R M := by
  refine ⟨fun free ↦ ?_, fun free ↦ ?_⟩
  · let I := Module.Free.ChooseBasisIndex (R ⧸ Ideal.span {x}) (QuotSMulTop x M)
    let fin : Fintype I := Module.Free.ChooseBasisIndex.fintype _ _
    have : Module.Finite R (I →₀ R) := by simp [Fintype.finite fin]
    let b := Module.Free.chooseBasis (R ⧸ Ideal.span {x}) (QuotSMulTop x M)
    let b' : QuotSMulTop x M ≃ₗ[R] I →₀ R ⧸ Ideal.span {x} := {
      __ := b.1
      map_smul' r m := by simp}
    let f := b'.symm.toLinearMap.comp (Finsupp.mapRange.linearMap (Submodule.mkQ (Ideal.span {x})))
    rcases Module.projective_lifting_property (Submodule.mkQ (x • (⊤ : Submodule R M))) f
      (Submodule.mkQ_surjective _) with ⟨g, hg⟩
    have surjf : Function.Surjective f := by
      simpa [f] using Finsupp.mapRange_surjective _ rfl (Submodule.mkQ_surjective (Ideal.span {x}))
    have lejac : Ideal.span {x} ≤ (⊥ :Ideal R).jacobson :=
      le_trans ((Ideal.span_singleton_le_iff_mem (maximalIdeal R)).mpr mem)
      (IsLocalRing.maximalIdeal_le_jacobson _)
    have surjg : Function.Surjective g := by
      rw [← LinearMap.range_eq_top, ← top_le_iff]
      apply Submodule.le_of_le_smul_of_le_jacobson_bot (Module.finite_def.mp ‹_›) lejac
      rw [top_le_iff, sup_comm, ← Submodule.map_mkQ_eq_top, ← LinearMap.range_comp,
        Submodule.ideal_span_singleton_smul x ⊤, hg]
      exact LinearMap.range_eq_top_of_surjective f surjf
    have kerf : LinearMap.ker f = x • (⊤ : Submodule R (I →₀ R)) := by
      simpa only [LinearEquiv.ker_comp, f] using ker_mapRange_eq_smul_top R I x
    have injg : Function.Injective g := by
      rw [← LinearMap.ker_eq_bot]
      have fg : (LinearMap.ker g).FG := IsNoetherian.noetherian (LinearMap.ker g)
      apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {x}) _ fg _ lejac
      rw [Submodule.ideal_span_singleton_smul]
      intro y hy
      have : y ∈ x • (⊤ : Submodule R (I →₀ R)) := by simp [← kerf, ← hg, LinearMap.mem_ker.mp hy]
      rcases (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp this with ⟨z, _, hz⟩
      simp only [← hz, LinearMap.mem_ker, map_smul] at hy
      have := LinearMap.mem_ker.mpr (IsSMulRegular.right_eq_zero_of_smul reg hy)
      simpa [hz] using Submodule.smul_mem_pointwise_smul z x _ this
    exact Module.Free.of_equiv (LinearEquiv.ofBijective g ⟨injg, surjg⟩)
  · let I := Module.Free.ChooseBasisIndex R M
    let fin : Fintype I := Module.Free.ChooseBasisIndex.fintype _ _
    have : Module.Finite R (I →₀ R) := by simp [Fintype.finite fin]
    let b := Module.Free.chooseBasis R M
    let f : M →ₗ[R] I →₀ (R ⧸ Ideal.span {x}) :=
      (Finsupp.mapRange.linearMap (Submodule.mkQ (Ideal.span {x}))).comp b.1.toLinearMap
    have surjf : Function.Surjective f := by
      simpa only [f] using Function.Surjective.comp (Finsupp.mapRange_surjective _ rfl
        (Submodule.mkQ_surjective (Ideal.span {x}))) b.1.surjective
    have kerf : LinearMap.ker f = x • (⊤ : Submodule R M) := by
      simp only [f, LinearMap.ker_comp, ker_mapRange_eq_smul_top R I x]
      ext y
      simp only [Submodule.mem_comap, Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top,
        true_and]
      refine ⟨fun ⟨z, hz⟩ ↦ ?_, fun ⟨z, hz⟩ ↦ ?_⟩
      · use b.1.symm z
        apply b.1.injective
        simp only [map_smul, LinearEquiv.apply_symm_apply, hz]
        rfl
      · use b.1 z
        rw [← map_smul, hz]
        rfl
    let e' := LinearMap.quotKerEquivOfSurjective f surjf
    rw [kerf] at e'
    let e : QuotSMulTop x M ≃ₗ[R ⧸ Ideal.span {x}] I →₀ R ⧸ Ideal.span {x} := {
      __ := e'
      map_smul' r m := by
        rcases Ideal.Quotient.mk_surjective r with ⟨s, hs⟩
        simp only [← hs, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe]
        exact map_smul e' s m }
    exact Module.Free.of_equiv e.symm

section

variable {R} (x : R) {M N L : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup L]
    [Module R M] [Module R N] [Module R L]

def QuotSMulTop_map (f : M →ₗ[R] N) :
    QuotSMulTop x M →ₗ[R ⧸ Ideal.span {x}] QuotSMulTop x N where
  __ := Submodule.mapQ _ _ f (fun m hm ↦ by
    rcases (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hm with ⟨m', _, hm'⟩
    simpa [← hm'] using Submodule.smul_mem_pointwise_smul _ x ⊤ trivial)
  map_smul' r m := by
    rcases Ideal.Quotient.mk_surjective r with ⟨s, hs⟩
    simp only [← hs, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
    exact map_smul _ s m

lemma QuotSMulTop_map_surjective {f : M →ₗ[R] N} (surj : Function.Surjective f) :
    Function.Surjective (QuotSMulTop_map x f) := by
  intro y
  rcases Submodule.Quotient.mk_surjective _ y with ⟨y', hy'⟩
  rcases surj y' with ⟨z, hz⟩
  use Submodule.Quotient.mk z
  simp [QuotSMulTop_map, hz, hy']

lemma QuotSMulTop_map_exact {f : M →ₗ[R] N} {g : N →ₗ[R] L} (exact : Function.Exact f g)
    (surj : Function.Surjective g) :
    Function.Exact (QuotSMulTop_map x f) (QuotSMulTop_map x g) := by
  apply Function.Exact.of_comp_of_mem_range
  · have : g.comp f = 0 := by exact Function.Exact.linearMap_comp_eq_zero exact
    simp only [QuotSMulTop_map, LinearMap.coe_mk, LinearMap.coe_toAddHom, ← LinearMap.coe_comp]
    rw [← Submodule.mapQ_comp]
    simp only [Function.Exact.linearMap_comp_eq_zero exact, Submodule.mapQ_zero]
    rfl
  · intro y hy
    rcases Submodule.Quotient.mk_surjective _ y with ⟨y', hy'⟩
    simp only [QuotSMulTop_map, ← hy', LinearMap.coe_mk, LinearMap.coe_toAddHom,
      Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists,
      Submodule.mem_top, true_and] at hy
    rcases hy with ⟨l, hl⟩
    rcases surj l with ⟨y'', hy''⟩
    rw [← hy'', ← map_smul, ← LinearMap.sub_mem_ker_iff, exact.linearMap_ker_eq] at hl
    rcases LinearMap.mem_range.mp hl with ⟨m, hm⟩
    use Submodule.Quotient.mk (- m)
    simp only [QuotSMulTop_map, Submodule.Quotient.mk_neg, map_neg, LinearMap.coe_mk,
      LinearMap.coe_toAddHom, Submodule.mapQ_apply, hm, Submodule.Quotient.mk_sub,
      hy', neg_sub, sub_eq_self, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_pointwise_smul y'' x ⊤ trivial

end

open Ideal in
lemma projectiveDimension_eq_quotient [Small.{v} R] [IsLocalRing R] [IsNoetherianRing R]
    (M : ModuleCat.{v} R) [Module.Finite R M] (x : R)
    (reg1 : IsSMulRegular R x) (reg2 : IsSMulRegular M x)
    (mem : x ∈ maximalIdeal R) : projectiveDimension.{v} M =
    projectiveDimension.{v} (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x M)) := by
  have aux (n : ℕ): projectiveDimension M ≤ n ↔
    projectiveDimension.{v} (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x M)) ≤ n := by
    simp only [projectiveDimension_le_iff]
    induction n generalizing M
    · simp only [HasProjectiveDimensionLE, zero_add, ← projective_iff_hasProjectiveDimensionLT_one]
      rw [← IsProjective.iff_projective, ← IsProjective.iff_projective]
      refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
      · have := (free_iff_quotSMulTop_free R M mem reg2).mpr Module.free_of_flat_of_isLocalRing
        exact Module.Projective.of_free
      · let _ : IsLocalRing (R ⧸ Ideal.span {x}) :=
          have : Nontrivial (R ⧸ Ideal.span {x}) :=
            Quotient.nontrivial (by simpa [← Submodule.ideal_span_singleton_smul])
          have : IsLocalHom (Ideal.Quotient.mk (Ideal.span {x})) :=
            IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
          IsLocalRing.of_surjective _ Ideal.Quotient.mk_surjective
        have := (free_iff_quotSMulTop_free R M mem reg2).mp Module.free_of_flat_of_isLocalRing
        exact Module.Projective.of_free
    · rename_i n ih _
      rcases Module.Finite.exists_fin' R M with ⟨m, f', hf'⟩
      let f := f'.comp ((Finsupp.mapRange.linearEquiv (Shrink.linearEquiv.{v} R R)).trans
        (Finsupp.linearEquivFunOnFinite R R (Fin m))).1
      have surjf : Function.Surjective f := by simpa [f] using hf'
      let S : ShortComplex (ModuleCat.{v} R) := {
        f := ModuleCat.ofHom.{v} (LinearMap.ker f).subtype
        g := ModuleCat.ofHom.{v} f
        zero := by
          ext x
          simp }
      have S_exact' : Function.Exact (LinearMap.ker f).subtype f := by
        intro x
        simp
      have S_exact : S.ShortExact := {
        exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mpr S_exact'
        mono_f := (ModuleCat.mono_iff_injective S.f).mpr (LinearMap.ker f).injective_subtype
        epi_g := (ModuleCat.epi_iff_surjective S.g).mpr surjf}
      let _ : Module.Finite R S.X₂ := by
        simp [S, Module.Finite.equiv (Shrink.linearEquiv R R).symm, Finite.of_fintype (Fin m)]
      let _ : Module.Free R (Shrink.{v, u} R) :=  Module.Free.of_equiv (Shrink.linearEquiv R R).symm
      let free : Module.Free R S.X₂ := Module.Free.finsupp R (Shrink.{v, u} R) _
      have proj := ModuleCat.projective_of_categoryTheory_projective S.X₂
      have reg2'' : IsSMulRegular (Fin m →₀ Shrink.{v, u} R) x := by
        apply IsSMulRegular.of_right_eq_zero_of_smul (fun y hy ↦ ?_)
        ext i
        simp only [Finsupp.coe_zero, Pi.zero_apply, equivShrink_symm_zero]
        apply IsSMulRegular.right_eq_zero_of_smul reg1
        rw [← equivShrink_symm_smul, ← Finsupp.smul_apply, hy]
        exact equivShrink_symm_zero
      have reg2' : IsSMulRegular S.X₁ x := reg2''.submodule _ _
      have Sx_exact' := QuotSMulTop_map_exact x S_exact' surjf
      let Sx : ShortComplex (ModuleCat.{v} (R ⧸ Ideal.span {x})) := {
        f := ModuleCat.ofHom.{v} (QuotSMulTop_map x (LinearMap.ker f).subtype)
        g := ModuleCat.ofHom.{v} (QuotSMulTop_map x f)
        zero := by
          rw [← ModuleCat.ofHom_comp, Sx_exact'.linearMap_comp_eq_zero]
          rfl }
      have inj : Function.Injective (QuotSMulTop_map x (LinearMap.ker f).subtype) := by
        rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
        intro y hy
        rcases Submodule.Quotient.mk_surjective _ y with ⟨y', hy'⟩
        simp only [QuotSMulTop_map, ← hy', LinearMap.mem_ker, LinearMap.coe_mk,
          LinearMap.coe_toAddHom, Submodule.mapQ_apply, Submodule.subtype_apply,
          Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists] at hy
        rcases hy with ⟨z, _, hz⟩
        have := y'.2
        rw [← hz, LinearMap.mem_ker, map_smul] at this
        simp only [← hy', Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists,
          Submodule.mem_top, true_and, Subtype.exists, SetLike.mk_smul_mk, LinearMap.mem_ker]
        use z, IsSMulRegular.right_eq_zero_of_smul reg2 this
        exact Subtype.val_inj.mp hz
      have Sx_exact : Sx.ShortExact := {
        exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact Sx).mpr Sx_exact'
        mono_f := (ModuleCat.mono_iff_injective Sx.f).mpr inj
        epi_g := (ModuleCat.epi_iff_surjective Sx.g).mpr (QuotSMulTop_map_surjective x surjf)}
      let _ := (free_iff_quotSMulTop_free R (Fin m →₀ Shrink.{v, u} R) mem reg2'').mpr free
      have proj' := ModuleCat.projective_of_categoryTheory_projective Sx.X₂
      exact ((S_exact.hasProjectiveDimensionLT_X₃_iff n proj).trans (ih S.X₁ reg2')).trans
        (Sx_exact.hasProjectiveDimensionLT_X₃_iff n proj').symm
  refine eq_of_forall_ge_iff (fun N ↦ ?_)
  by_cases eqbot : N = ⊥
  · simp only [eqbot, le_bot_iff, projectiveDimension_eq_bot_iff,
      projectiveDimension_eq_bot_iff, ModuleCat.isZero_iff_subsingleton]
    refine ⟨fun h ↦ (Submodule.Quotient.mk_surjective _).subsingleton, fun h ↦ ?_⟩
    by_contra ntr
    have : Nontrivial M := not_subsingleton_iff_nontrivial.mp ntr
    exact (not_subsingleton_iff_nontrivial.mpr (quotSMulTop_nontrivial' R mem M)) h
  · by_cases eqtop : N.unbot eqbot = ⊤
    · have : N = ⊤ := (WithBot.coe_unbot _ eqbot).symm.trans (WithBot.coe_inj.mpr eqtop)
      simp [this]
    · let n := (N.unbot eqbot).toNat
      have : N = n := (WithBot.coe_unbot _ eqbot).symm.trans
        (WithBot.coe_inj.mpr (ENat.coe_toNat eqtop).symm)
      simpa only [this] using aux n

variable {R}

lemma exist_isSMulRegular_of_exist_hasProjectiveDimensionLE_aux [IsLocalRing R] [IsNoetherianRing R]
    [Small.{v} R] (nebot : maximalIdeal R ≠ ⊥)
    (h : ∃ n, HasProjectiveDimensionLE (ModuleCat.of R (Shrink.{v} (maximalIdeal R))) n) :
    ∃ x ∈ maximalIdeal R, IsSMulRegular R x := by
  let Sf := (Shrink.linearEquiv.{v} R R).symm.toLinearMap.comp
    ((maximalIdeal R).subtype.comp (Shrink.linearEquiv.{v} R (maximalIdeal R)).toLinearMap)
  let Sg := (Shrink.linearEquiv.{v} R (R ⧸ (maximalIdeal R))).symm.toLinearMap.comp
    ((Ideal.Quotient.mkₐ R (maximalIdeal R)).toLinearMap.comp
    (Shrink.linearEquiv.{v} R R).toLinearMap)
  have exac : Function.Exact Sf Sg := by
    intro x
    have (z : R) : z ∈ (maximalIdeal R) ↔ ∃ y, ((equivShrink (maximalIdeal R)).symm y) = z := by
      refine ⟨fun h ↦ ?_, fun ⟨y, hy⟩ ↦ by simp [← hy]⟩
      use (equivShrink (maximalIdeal R)) ⟨z, h⟩
      simp
    simpa [Sf, Sg, Ideal.Quotient.eq_zero_iff_mem, AddEquiv.symm_apply_eq]
      using this ((equivShrink R).symm x)
  have inj : Function.Injective Sf := by
    simpa [Sf] using LinearEquiv.injective (Shrink.linearEquiv R (maximalIdeal R))
  have surj : Function.Surjective Sg := by
    simpa [Sg] using Ideal.Quotient.mk_surjective
  let S : ShortComplex (ModuleCat.{v} R) := {
    f := ModuleCat.ofHom Sf
    g := ModuleCat.ofHom Sg
    zero := by
      ext x
      simp [Function.Exact.apply_apply_eq_zero exac] }
  have S_exact : S.ShortExact := {
    exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr exac
    mono_f := (ModuleCat.mono_iff_injective _).mpr inj
    epi_g := (ModuleCat.epi_iff_surjective _).mpr surj }
  rcases h with ⟨n, hn⟩
  let _ : Module.Free R (ModuleCat.of R (Shrink.{v, u} R)) :=
    Module.Free.of_equiv (Shrink.linearEquiv.{v} R R).symm
  have projdim := (S_exact.hasProjectiveDimensionLT_X₃_iff n
    (ModuleCat.projective_of_categoryTheory_projective S.X₂)).mpr hn
  have : Module.annihilator R (Shrink.{v} (R ⧸ maximalIdeal R)) = maximalIdeal R := by
    rw [(Shrink.linearEquiv.{v} R (R ⧸ maximalIdeal R)).annihilator_eq, Ideal.annihilator_quotient]
  let _ : Module.Finite R (Shrink.{v} (R ⧸ maximalIdeal R)) :=
    Module.Finite.equiv (Shrink.linearEquiv.{v} R (R ⧸ maximalIdeal R)).symm
  let _ : Module.Finite R (Shrink.{v, u} R) := Module.Finite.equiv (Shrink.linearEquiv.{v} R R).symm
  simp only [← this, (Shrink.linearEquiv.{v} R R).symm.isSMulRegular_congr]
  rw [← IsSMulRegular.subsingleton_linearMap_iff]
  by_contra h
  have eq0 : IsLocalRing.depth (ModuleCat.of R (Shrink.{v} R)) = 0 :=
    (moduleDepth_eq_zero_of_hom_nontrivial _ _).mpr (not_subsingleton_iff_nontrivial.mp h)
  have eq := AuslanderBuchsbaum (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R)))
    (ne_top_of_le_ne_top (WithBot.coe_inj.not.mpr (ENat.coe_ne_top _))
      ((projectiveDimension_le_iff _ _).mpr projdim))
  have : projectiveDimension (ModuleCat.of R (Shrink.{v, u} (R ⧸ maximalIdeal R))) ≤ 0 := by
    simpa [← WithBot.coe_zero, ← eq0, ← eq] using WithBot.le_self_add WithBot.coe_ne_bot _
  let _ := (projective_iff_hasProjectiveDimensionLT_one _).mpr
    ((projectiveDimension_le_iff _ _).mp this)
  let _ : Module.Projective R (Shrink.{v, u} (R ⧸ maximalIdeal R)) :=
    ModuleCat.projective_of_module_projective (ModuleCat.of R (Shrink.{v, u} (R ⧸ maximalIdeal R)))
  have : Module.Projective R (R ⧸ maximalIdeal R) :=
    Module.Projective.of_equiv (Shrink.linearEquiv.{v} R (R ⧸ maximalIdeal R))
  have : Module.Free R (R ⧸ maximalIdeal R) := Module.free_of_flat_of_isLocalRing
  let I := Module.Free.ChooseBasisIndex R (R ⧸ maximalIdeal R)
  let b := Module.Free.chooseBasis R (R ⧸ maximalIdeal R)
  have := b.1.annihilator_eq
  rw [Module.annihilator_finsupp, Ideal.annihilator_quotient] at this
  absurd nebot
  rw [this, Module.annihilator_eq_bot.mpr inferInstance]

lemma exist_isSMulRegular_of_exist_hasProjectiveDimensionLE [IsLocalRing R] [IsNoetherianRing R]
    [Small.{v} R] (nebot : maximalIdeal R ≠ ⊥)
    (h : ∃ n, HasProjectiveDimensionLE (ModuleCat.of R (Shrink.{v} (maximalIdeal R))) n) :
    ∃ x ∈ maximalIdeal R, x ∉ maximalIdeal R ^ 2 ∧ IsSMulRegular R x := by
  --use prime avoidance to `m^2` and associated primes of `R`
  obtain ⟨x, xmem, xnmem⟩ : ∃ x ∈ maximalIdeal R,
    x ∉ ⋃ I ∈ {(maximalIdeal R) ^ 2} ∪ associatedPrimes R R, I := by
    by_contra! h'
    have fin : ({(maximalIdeal R) ^ 2} ∪ associatedPrimes R R).Finite :=
      Set.Finite.union (Set.finite_singleton _) (associatedPrimes.finite R R)
    rcases (Ideal.subset_union_prime_finite fin ((maximalIdeal R) ^ 2) ((maximalIdeal R) ^ 2)
      (fun I hI ne _ ↦ IsAssociatedPrime.isPrime (by simpa [ne] using hI))).mp h' with
      ⟨I, hI, sub⟩
    simp only [Set.singleton_union, Set.mem_insert_iff] at hI
    rcases hI with eq|ass
    · have : IsField R := by
        simp only [← subsingleton_cotangentSpace_iff, Ideal.cotangent_subsingleton_iff,
          IsIdempotentElem]
        exact le_antisymm Ideal.mul_le_right (le_of_le_of_eq sub (eq.trans (pow_two _)))
      absurd nebot
      exact isField_iff_maximalIdeal_eq.mp this
    · let _ : I.IsPrime := IsAssociatedPrime.isPrime ass
      rw [le_antisymm (le_maximalIdeal_of_isPrime I) sub] at ass
      absurd exist_isSMulRegular_of_exist_hasProjectiveDimensionLE_aux nebot h
      simp only [not_exists, not_and]
      intro x hx
      change x ∈ {r : R | IsSMulRegular R r}ᶜ
      rw [← biUnion_associatedPrimes_eq_compl_regular]
      exact Set.mem_biUnion ass hx
  simp at xnmem
  use x
  simp only [xmem, xnmem.1, not_false_eq_true, true_and]
  change x ∈ {r : R | IsSMulRegular R r}
  rw [← Set.not_notMem, ← Set.mem_compl_iff, ← biUnion_associatedPrimes_eq_compl_regular]
  simpa using xnmem.2

lemma spanFinrank_maximalIdeal_quotient [IsLocalRing R] [IsNoetherianRing R] (x : R)
    (mem : x ∈ maximalIdeal R) (nmem : x ∉ (maximalIdeal R) ^ 2) :
    letI : IsLocalRing (R ⧸ Ideal.span {x}) :=
      have : Nontrivial (R ⧸ Ideal.span {x}) :=
        Ideal.Quotient.nontrivial (by simpa [← Submodule.ideal_span_singleton_smul])
      have : IsLocalHom (Ideal.Quotient.mk (Ideal.span {x})) :=
        IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
      IsLocalRing.of_surjective (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective
    (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank = (maximalIdeal R).spanFinrank - 1 := by
  let _ : Nontrivial (R ⧸ Ideal.span {x}) := Ideal.Quotient.nontrivial
    (by simpa [← Submodule.ideal_span_singleton_smul] using mem)
  let _ : IsLocalHom (Ideal.Quotient.mk (Ideal.span {x})) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  let _ : IsLocalRing (R ⧸ Ideal.span {x}) :=
    IsLocalRing.of_surjective _ Ideal.Quotient.mk_surjective
  let _ : IsNoetherianRing (R ⧸ Ideal.span {x}) :=
    isNoetherianRing_of_surjective _ _ _ Ideal.Quotient.mk_surjective
  have comapeq : Ideal.comap (Ideal.Quotient.mk (Ideal.span {x}))
      (maximalIdeal (R ⧸ Ideal.span {x})) = maximalIdeal R := ((local_hom_TFAE _).out 0 4).mp ‹_›
  let f := Ideal.mapCotangent (maximalIdeal R) (maximalIdeal (R ⧸ Ideal.span {x}))
      (Ideal.Quotient.mkₐ R (Ideal.span {x})) (fun x hx ↦ by simpa)
  have ker : (LinearMap.ker f : Set (maximalIdeal R).Cotangent) = (Submodule.span
    (ResidueField R) {(maximalIdeal R).toCotangent ⟨x, mem⟩}) := by
    simp only [ Submodule.coe_span_eq_span_of_surjective R (ResidueField R)
      IsLocalRing.residue_surjective, SetLike.coe_set_eq]
    ext y
    induction y using Submodule.Quotient.induction_on
    rename_i y
    simp only [Ideal.mapCotangent, LinearMap.mem_ker, f]
    change (maximalIdeal (R ⧸ Ideal.span {x})).toCotangent ⟨(Ideal.Quotient.mkₐ R
      (Ideal.span {x})) y, _⟩ = 0 ↔ (maximalIdeal R).toCotangent y ∈ _
    simp only [Ideal.Quotient.mkₐ_eq_mk, Ideal.toCotangent_eq_zero]
    have : maximalIdeal (R ⧸ Ideal.span {x}) = (maximalIdeal R).map (Ideal.Quotient.mk _) := by
      simp only [← comapeq, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
    rw [this, ← Ideal.map_pow, ← Ideal.mem_comap, ← Submodule.mem_comap,
      Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
      ← Set.image_singleton, ← Submodule.map_span, Submodule.comap_map_eq, sup_comm,
      ← Submodule.comap_map_eq_of_injective (maximalIdeal R).subtype_injective
      (Submodule.span R {⟨x, mem⟩} ⊔ LinearMap.ker (maximalIdeal R).toCotangent)]
    simp only [Submodule.map_sup, Submodule.map_subtype_span_singleton, Ideal.submodule_span_eq,
      Submodule.mem_comap, Submodule.subtype_apply]
    congr!
    exact (Ideal.map_toCotangent_ker (maximalIdeal R)).symm
  let Q := (CotangentSpace R) ⧸ (Submodule.span (ResidueField R)
    {(maximalIdeal R).toCotangent ⟨x, mem⟩})
  let f' : Q →+ (CotangentSpace (R ⧸ Ideal.span {x})) :=
    QuotientAddGroup.lift _ f
    (le_of_eq (AddSubgroup.ext (fun x ↦ (congrFun ker.symm x).to_iff)))
  have bij : Function.Bijective f' := by
    constructor
    · rw [← AddMonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      induction x using QuotientAddGroup.induction_on
      rename_i x
      have : x ∈ (LinearMap.ker f : Set (maximalIdeal R).Cotangent) := LinearMap.mem_ker.mpr hx
      rw [ker] at this
      exact AddSubgroup.mem_bot.mpr ((QuotientAddGroup.eq_zero_iff _).mpr this)
    · apply QuotientAddGroup.lift_surjective_of_surjective
      intro x
      rcases Ideal.toCotangent_surjective _ x with ⟨y, hy⟩
      rcases Ideal.Quotient.mk_surjective y.1 with ⟨z, hz⟩
      have : z ∈ maximalIdeal R := by simp [← comapeq, hz]
      use (maximalIdeal R).toCotangent ⟨z, this⟩
      simp [f, ← hy, hz]
  let e : Q ≃+ (CotangentSpace (R ⧸ Ideal.span {x})) :=
    AddEquiv.ofBijective f' bij
  have rk := rank_eq_of_equiv_equiv (ResidueField.map (Ideal.Quotient.mk (Ideal.span {x})))
    e (ResidueField.map_bijective_of_surjective _ Ideal.Quotient.mk_surjective) (fun r m ↦ by
      induction m using Submodule.Quotient.induction_on
      induction r using Submodule.Quotient.induction_on
      rw [← Submodule.Quotient.mk_smul]
      simp only [AddEquiv.ofBijective_apply, e, f']
      rename_i m r
      change f (r • m) = (ResidueField.map (Ideal.Quotient.mk (Ideal.span {x})))
        (IsLocalRing.residue R r) • (f m)
      simp only [map_smul]
      rfl)
  have frk : Module.finrank (ResidueField R) Q = Module.finrank
    (ResidueField (R ⧸ Ideal.span {x})) (CotangentSpace (R ⧸ Ideal.span {x})) := by
    simp only [Module.finrank, rk]
  rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace, ← frk,
    Submodule.finrank_quotient,
    finrank_span_singleton (by simpa [Ideal.toCotangent_eq_zero] using nmem),
    ← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]

set_option maxHeartbeats 250000 in
-- This theorem is just too big and hard to separate
open Pointwise in
theorem generate_by_regular_aux [IsLocalRing R] [IsNoetherianRing R] [Small.{v} R]
    (h : ∃ n, HasProjectiveDimensionLE (ModuleCat.of R (Shrink.{v} (maximalIdeal R))) n)
    (n : ℕ) : Submodule.spanFinrank (maximalIdeal R) = n →
    ∃ rs : List R, IsRegular R rs ∧ Ideal.ofList rs = maximalIdeal R := by
  induction n generalizing R
  · intro hrank
    have : (maximalIdeal R).FG := (isNoetherianRing_iff_ideal_fg R).mp ‹_› _
    have : Submodule.spanRank (maximalIdeal R) = 0 := by
      simp [Submodule.fg_iff_spanRank_eq_spanFinrank.mpr this, hrank]
    simp only [Submodule.spanRank_eq_zero_iff_eq_bot] at this
    use []
    simpa [this] using RingTheory.Sequence.IsRegular.nil R R
  · rename_i n ih _ _ _ _
    have fg : (maximalIdeal R).FG := (isNoetherianRing_iff_ideal_fg R).mp ‹_› _
    intro hrank
    have nebot : maximalIdeal R ≠ ⊥ := by
      simp [← Submodule.spanRank_eq_zero_iff_eq_bot, hrank,
        Submodule.fg_iff_spanRank_eq_spanFinrank.mpr fg]
    rcases exist_isSMulRegular_of_exist_hasProjectiveDimensionLE nebot h with
      ⟨x, mem, nmem, xreg⟩
    let R' := R ⧸ Ideal.span {x}
    let _ : Nontrivial (R ⧸ Ideal.span {x}) := Ideal.Quotient.nontrivial
      (by simpa [← Submodule.ideal_span_singleton_smul] using mem)
    let _ : IsLocalHom (Ideal.Quotient.mk (Ideal.span {x})) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    let _ : IsLocalRing (R ⧸ Ideal.span {x}) :=
      IsLocalRing.of_surjective _ Ideal.Quotient.mk_surjective
    let _ : IsNoetherianRing (R ⧸ Ideal.span {x}) :=
      isNoetherianRing_of_surjective _ _ _ Ideal.Quotient.mk_surjective
    have comapeq : Ideal.comap (Ideal.Quotient.mk (Ideal.span {x}))
      (maximalIdeal R') = maximalIdeal R := ((local_hom_TFAE _).out 0 4).mp ‹_›
    let xm' := (Submodule.span (ResidueField R) {(maximalIdeal R).toCotangent ⟨x, mem⟩})
    rcases xm'.exists_isCompl with ⟨J', ⟨inf, sup⟩⟩
    let g : (maximalIdeal R) →ₛₗ[residue R] (maximalIdeal R).Cotangent := {
      __ := (maximalIdeal R).toCotangent
      map_smul' r m := by
        simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, map_smul]
        rfl }
    have surjg : Function.Surjective g := (maximalIdeal R).toCotangent_surjective
    have supeq : (J'.comap g) ⊔ Submodule.span R {⟨x, mem⟩} = ⊤ := by
      let : RingHomSurjective (residue R) := ⟨residue_surjective⟩
      rw [sup_comm, ← sup_eq_left.mpr (LinearMap.ker_le_comap g), ← sup_assoc,
        ← Submodule.comap_map_eq, Submodule.map_sup, Submodule.map_span,
        Submodule.map_comap_eq_of_surjective surjg]
      simp only [LinearMap.coe_mk, LinearMap.coe_toAddHom, Set.image_singleton, g]
      rw [codisjoint_iff.mp sup, Submodule.comap_top]
    have infle : (J'.comap g) ⊓ Submodule.span R {⟨x, mem⟩} ≤
      x • (⊤ : Submodule R (maximalIdeal R)) := by
      intro y hy
      simp only [Submodule.mem_inf, Submodule.mem_comap] at hy
      rcases Submodule.mem_span_singleton.mp hy.2 with ⟨r, hr⟩
      rw [← hr, LinearMap.map_smulₛₗ] at hy
      simp only [LinearMap.coe_mk, LinearMap.coe_toAddHom, SetLike.mk_smul_mk, smul_eq_mul, g] at hy
      have := Submodule.mem_inf.mpr ⟨Submodule.mem_span_singleton.mpr (by use (residue R) r), hy.1⟩
      rw [disjoint_iff.mp inf, Submodule.mem_bot] at this
      have eq0 : r ∈ maximalIdeal R := (residue_eq_zero_iff _).mp
        ((smul_eq_zero_iff_left (by simpa [Ideal.toCotangent_eq_zero] using nmem)).mp this)
      simp only [SetLike.mk_smul_mk, smul_eq_mul, ← Subtype.val_inj] at hr
      have : y = x • ⟨r, eq0⟩ := by simpa [← Subtype.val_inj, mul_comm x r] using hr.symm
      simpa [this] using Submodule.smul_mem_pointwise_smul (⟨r, eq0⟩ : maximalIdeal R) x ⊤ trivial
    let f : maximalIdeal R →ₗ[R] maximalIdeal R' := {
      toFun m := ⟨Ideal.Quotient.mk (Ideal.span {x}) m,
        map_nonunit (Ideal.Quotient.mk (Ideal.span {x})) m.1 m.2⟩
      map_add' a b := by simp
      map_smul' r a := by simp [Algebra.smul_def, R']}
    have surjf : Function.Surjective f := by
      intro y
      rcases Ideal.Quotient.mk_surjective y.1 with ⟨z, hz⟩
      have : z ∈ maximalIdeal R := by
        rw [← comapeq, Ideal.mem_comap, hz]
        exact y.2
      use ⟨z, this⟩
      simp [f, hz]
    have kerf : LinearMap.ker f = Submodule.span R {⟨x, mem⟩} := by
      ext y
      simp only [LinearMap.mem_ker, LinearMap.coe_mk, AddHom.coe_mk, Submodule.mk_eq_zero, f]
      rw [Ideal.Quotient.eq_zero_iff_mem, ← Submodule.comap_map_eq_of_injective
        (maximalIdeal R).subtype_injective (Submodule.span R {⟨x, mem⟩})]
      simp
    let e1' := (Shrink.linearEquiv.{v} R (maximalIdeal R')).symm.toLinearMap.comp
      (f.comp ((J'.comap g) ⊔ (Submodule.span R {⟨x, mem⟩})).subtype)
    have surje1' : Function.Surjective e1' := by
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Submodule.coe_subtype,
        EquivLike.comp_surjective, e1']
      apply surjf.comp
      intro y
      use ⟨y, by simp [supeq]⟩
    let e1 : Shrink.{v, u} (maximalIdeal R') ≃ₗ[R] ↥((J'.comap g) ⊔ (Submodule.span R {⟨x, mem⟩})) ⧸
      (Submodule.span R {⟨x, mem⟩}).comap ((J'.comap g) ⊔ Submodule.span R {⟨x, mem⟩}).subtype :=
      ((Submodule.quotEquivOfEq _ _ (by simp [e1', LinearMap.ker_comp, kerf])).trans
      (LinearMap.quotKerEquivOfSurjective _ surje1')).symm
    let e2 := LinearMap.quotientInfEquivSupQuotient (J'.comap g) (Submodule.span R {⟨x, mem⟩})
    let i3 : (↥(J'.comap g) ⧸ (J'.comap g).comap (J'.comap g).subtype  ⊓
      Submodule.comap (J'.comap g).subtype (Submodule.span R {⟨x, mem⟩})) →ₗ[R]
      QuotSMulTop x (Shrink.{v, u} (maximalIdeal R)) :=
      Submodule.mapQ _ _ ((Shrink.linearEquiv.{v} R (maximalIdeal R)).symm.toLinearMap.comp
        (J'.comap g).subtype) (by
          rw [← Submodule.comap_inf, Submodule.comap_comp]
          apply Submodule.comap_mono (le_trans infle (fun y hy ↦ ?_))
          rcases (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hy with ⟨z, _, hz⟩
          simp only [Submodule.mem_comap, ← hz, map_smul]
          exact Submodule.smul_mem_pointwise_smul _ x ⊤ trivial)
    let i' : Shrink.{v, u} (maximalIdeal R') →ₗ[R]
      QuotSMulTop x (Shrink.{v, u} (maximalIdeal R)) := i3.comp (e1.trans e2.symm).toLinearMap
    let r' : QuotSMulTop x (Shrink.{v, u} (maximalIdeal R)) →ₗ[R]
      Shrink.{v, u} (maximalIdeal R') := Submodule.liftQ _
        ((Shrink.linearEquiv.{v} R (maximalIdeal R')).symm.toLinearMap.comp
      (f.comp (Shrink.linearEquiv.{v} R (maximalIdeal R)).toLinearMap)) (fun y hy ↦ by
      rcases (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hy with ⟨z, _, hz⟩
      simp [← hz, f, Algebra.smul_def, R'])
    have compid : r'.comp i' = LinearMap.id := by
      ext y
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        LinearEquiv.trans_apply, LinearMap.id_coe, id_eq, SetLike.coe_eq_coe,
        EmbeddingLike.apply_eq_iff_eq, i']
      rcases Submodule.Quotient.mk_surjective _ (e2.symm (e1 y)) with ⟨z, hz⟩
      have : e1.symm (e2 (e2.symm (e1 y))) = y := by simp
      apply Eq.trans _ this
      simp only [← hz, Submodule.mapQ_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
        Submodule.coe_subtype, Function.comp_apply, i3, Submodule.liftQ_apply, LinearMap.coe_comp,
        LinearEquiv.coe_coe, Function.comp_apply, r', e2,
        LinearMap.quotientInfEquivSupQuotient_apply_mk]
      simp only [LinearEquiv.trans_symm, LinearEquiv.symm_symm, LinearEquiv.trans_apply,
        Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk, e1,
        LinearMap.coe_comp, LinearEquiv.coe_coe, Submodule.coe_subtype,
        Function.comp_apply, Submodule.coe_inclusion, e1', LinearEquiv.apply_symm_apply]
    let _ : IsScalarTower R (R ⧸ Ideal.span {x}) (Shrink.{v, u} ↥(maximalIdeal R')) :=
      (equivShrink (maximalIdeal R')).symm.isScalarTower R _
    let r := (LinearMap.extendScalarsOfSurjective (Ideal.Quotient.mk_surjective
      (I := Ideal.span {x})) r')
    let i := (LinearMap.extendScalarsOfSurjective
      (Ideal.Quotient.mk_surjective (I := Ideal.span {x})) i')
    have compid' : r.comp i = LinearMap.id := by
      ext y
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.extendScalarsOfSurjective_apply,
        LinearMap.id_coe, id_eq, SetLike.coe_eq_coe, EmbeddingLike.apply_eq_iff_eq, r, i]
      rw [← LinearMap.comp_apply, compid, LinearMap.id_apply]
    have retr  : Retract (ModuleCat.of (R ⧸ Ideal.span {x}) (Shrink.{v} (maximalIdeal R')))
      (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x (Shrink.{v} (maximalIdeal R)))) := {
      i := ModuleCat.ofHom i
      r := ModuleCat.ofHom r
      retract := by rw [←  ModuleCat.ofHom_comp, compid', ModuleCat.ofHom_id]}
    have fin : ∃ n, HasProjectiveDimensionLE
      (ModuleCat.of R' (Shrink.{v, u} (maximalIdeal R'))) n := by
      rcases h with ⟨n, hn⟩
      let _ : Module.Finite R (ModuleCat.of R (Shrink.{v, u} (maximalIdeal R))) :=
        Module.Finite.equiv (Shrink.linearEquiv.{v} R (maximalIdeal R)).symm
      have xreg' : IsSMulRegular (Shrink.{v, u} (maximalIdeal R)) x :=
        ((Shrink.linearEquiv.{v} R (maximalIdeal R)).isSMulRegular_congr x).mpr (xreg.submodule _ x)
      rw [← projectiveDimension_le_iff, projectiveDimension_eq_quotient R
        (ModuleCat.of R (Shrink.{v} (maximalIdeal R))) x xreg xreg' mem,
        projectiveDimension_le_iff] at hn
      use n
      exact retr.hasProjectiveDimensionLT (n + 1)
    have rank : Submodule.spanFinrank (maximalIdeal R') = n := by
      rw [spanFinrank_maximalIdeal_quotient x mem nmem, hrank, Nat.add_sub_cancel]
    rcases ih fin rank with ⟨rs', reg, span⟩
    rcases List.map_surjective_iff.mpr Ideal.Quotient.mk_surjective rs' with ⟨rs, hrs⟩
    use x :: rs
    have eq : Ideal.span {x} ⊔ Ideal.ofList rs = maximalIdeal R := by
      rw [← Ideal.mk_ker (I := Ideal.span {x}), sup_comm,
        ← Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective,
        Ideal.map_ofList, hrs, span, comapeq]
    simp only [isRegular_cons_iff, xreg, true_and, Ideal.ofList_cons, eq, and_true]
    let e : QuotSMulTop x R ≃ₗ[R] (R ⧸ Ideal.span {x}) :=
      Submodule.quotEquivOfEq _ _ (by simp [← Submodule.ideal_span_singleton_smul])
    rw [LinearEquiv.isRegular_congr e]
    constructor
    · rw [← RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff (R ⧸ Ideal.span {x})]
      simpa [hrs] using reg.1
    · have : Ideal.ofList rs ≤ maximalIdeal R := by simp [← eq]
      apply (ne_top_of_le_ne_top _ (Submodule.smul_mono_left this)).symm
      simp only [Ideal.smul_top_eq_map, Ideal.Quotient.algebraMap_eq, ne_eq,
        Submodule.restrictScalars_eq_top_iff]
      have : Ideal.map (Ideal.Quotient.mk (Ideal.span {x})) (maximalIdeal R) ≤ maximalIdeal R' := by
        rw [Ideal.map_le_iff_le_comap, comapeq]
      exact ne_top_of_le_ne_top Ideal.IsPrime.ne_top' this

theorem generate_by_regular [IsLocalRing R] [IsNoetherianRing R] [Small.{v} R]
    (h : ∃ n, HasProjectiveDimensionLE (ModuleCat.of R (Shrink.{v} (maximalIdeal R))) n) :
    ∃ rs : List R, IsRegular R rs ∧ Ideal.ofList rs = maximalIdeal R :=
  generate_by_regular_aux  h (Submodule.spanFinrank (maximalIdeal R)) rfl

theorem IsRegularLocalRing.of_maximalIdeal_hasProjectiveDimensionLE
    [IsLocalRing R] [IsNoetherianRing R] [Small.{v} R]
    (h : ∃ n, HasProjectiveDimensionLE (ModuleCat.of R (Shrink.{v} (maximalIdeal R))) n) :
    IsRegularLocalRing R := by
  classical
  rcases generate_by_regular h with ⟨rs, reg, span⟩
  apply of_span_eq R rs.toFinset.toSet rs.toFinset.finite_toSet
    (by simpa only [List.coe_toFinset] using span)
  rw [Set.ncard_coe_finset rs.toFinset]
  apply le_trans (Nat.cast_le.mpr rs.toFinset_card_le)
  let _ : Module.Finite R (ModuleCat.of R (Shrink.{v, u} R)) :=
    Module.Finite.equiv (Shrink.linearEquiv.{v} R R).symm
  apply le_trans _ (depth_le_ringKrullDim (ModuleCat.of R (Shrink.{v, u} R)))
  have : (rs.length : WithBot ℕ∞) = (rs.length : ℕ∞) := rfl
  rw [IsLocalRing.depth_eq_sSup_length_regular, this, WithBot.coe_le_coe]
  apply le_sSup
  use rs, ((Shrink.linearEquiv.{v} R R).isRegular_congr rs).mpr reg
  simp only [← span, exists_prop, and_true]
  intro r hr
  exact Ideal.subset_span hr

theorem IsRegularLocalRing.of_globalDimension_lt_top [IsLocalRing R] [IsNoetherianRing R]
    [Small.{v} R] (h : globalDimension.{v} R < ⊤) : IsRegularLocalRing R := by
  apply IsRegularLocalRing.of_maximalIdeal_hasProjectiveDimensionLE
  rw [← projectiveDimension_ne_top_iff]
  by_contra eqtop
  absurd h
  simp only [globalDimension, ← eqtop, not_lt]
  exact le_iSup _ (ModuleCat.of R (Shrink.{v} (maximalIdeal R)))
