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
/-!

# Ferrand Vasconcelos Theorem

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
    · simp only [HasProjectiveDimensionLE, zero_add, ← hasProjectiveDimensionLT_one_iff]
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

lemma exist_isSMulRegular_of_exist_hasProjectiveDimensionLE [IsLocalRing R] [IsNoetherianRing R]
    [Small.{v} R] (I : Ideal R) (netop : I ≠ ⊤) (nebot : I ≠ ⊥)
    (h : ∃ n, HasProjectiveDimensionLE (ModuleCat.of R (Shrink.{v} I)) n) :
    ∃ x ∈ I, x ∉ maximalIdeal R * I ∧ IsSMulRegular R x := by
  --use prime avoidance to `mI` and associated primes of `R`
  --for `I` containing regular element, see https://stacks.math.columbia.edu/tag/00N1
  sorry

open Set in
lemma Ideal.spanFinrank_eq_finrank_quotient [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R) :
    I.spanFinrank = Module.finrank (R ⧸ maximalIdeal R)
      (I ⧸ maximalIdeal R • (⊤ : Submodule R I)) := by
  --IsLocalRing.map_mkQ_eq_top
  have eqtop (S : Set I) : Submodule.span R S = ⊤ ↔
    Submodule.span R ((Submodule.subtype I) '' S) = I := by
    simp only [← Submodule.map_span, ← I.range_subtype , ← Submodule.map_top,
      (Submodule.map_injective_of_injective I.injective_subtype).eq_iff]
  let f : I →ₛₗ[Ideal.Quotient.mk (maximalIdeal R)] (I ⧸ maximalIdeal R • (⊤ : Submodule R I)) := {
    __ := Submodule.mkQ _
    map_smul' r m := rfl }
  let fg : Module.Finite (R ⧸ maximalIdeal R) (I ⧸ maximalIdeal R • (⊤ : Submodule R I)) :=
    Module.Finite.of_surjective f (Submodule.mkQ_surjective _)
  let _ : Module.Free (R ⧸ maximalIdeal R) (I ⧸ maximalIdeal R • (⊤ : Submodule R I)) :=
    let _ : Field (R ⧸ maximalIdeal R) := Quotient.field (maximalIdeal R)
    Module.Free.of_divisionRing (R ⧸ maximalIdeal R) (↥I ⧸ maximalIdeal R • ⊤)
  let fg' : I.FG := (isNoetherianRing_iff_ideal_fg R).mp inferInstance _
  have : Submodule.spanFinrank (⊤ : Submodule (R ⧸ maximalIdeal R)
    (I ⧸ maximalIdeal R • (⊤ : Submodule R I))) = Module.rank (R ⧸ maximalIdeal R)
    (I ⧸ maximalIdeal R • (⊤ : Submodule R I)) := by
    rw [← Submodule.fg_iff_spanRank_eq_spanFinrank.mpr fg.1, Submodule.rank_eq_spanRank_of_free]
  simp only [← Module.finrank_eq_rank, Nat.cast_inj] at this
  rw [← this]
  apply le_antisymm
  · have span : Submodule.span R ((⊤ : Submodule (R ⧸ maximalIdeal R)
      (I ⧸ maximalIdeal R • (⊤ : Submodule R I))).generators.image Quotient.out) = ⊤ := by
      rw [← IsLocalRing.map_mkQ_eq_top, Submodule.map_span, ← Set.image_comp]
      simp only [Function.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_out, image_id']
      apply SetLike.coe_injective
      rw [← Submodule.coe_span_eq_span_of_surjective R (R ⧸ maximalIdeal R)
        Ideal.Quotient.mk_surjective, Submodule.span_generators]
      simp
    rw [eqtop, ← Set.image_comp] at span
    rw [← Submodule.FG.generators_ncard fg.1, ← congrArg Submodule.spanFinrank span]
    apply le_trans (Submodule.spanFinrank_span_le_ncard_of_finite
      (Finite.image _ fg.1.finite_generators)) (Set.ncard_image_le fg.1.finite_generators)
  · let G := ({x | ↑x ∈ I.generators} : Set I)
    have : Submodule.span R G = ⊤ := by
      simp only [eqtop, Submodule.subtype_apply, Ideal.submodule_span_eq, G]
      convert I.span_generators
      ext
      simpa using fun a ↦ Submodule.FG.generators_mem I a
    have fin : G.Finite := Set.Finite.of_injOn (by simp [MapsTo, G]) injOn_subtype_val
        (Submodule.FG.finite_generators fg')
    rw [← IsLocalRing.map_mkQ_eq_top, Submodule.map_span] at this
    have eqtop : Submodule.span (R ⧸ maximalIdeal R)
      ((maximalIdeal R • (⊤ : Submodule R I)).mkQ '' G) = ⊤ := by
      apply SetLike.coe_injective
      rw [Submodule.coe_span_eq_span_of_surjective R _ Ideal.Quotient.mk_surjective, this]
      simp only [Submodule.top_coe]
    rw [← Submodule.FG.generators_ncard fg', ← eqtop]
    apply le_trans (Submodule.spanFinrank_span_le_ncard_of_finite (Finite.image _ fin))
    exact le_trans (Set.ncard_image_le fin) (Set.ncard_le_ncard_of_injOn Subtype.val (by simp [G])
      injOn_subtype_val (Submodule.FG.finite_generators fg'))

open Pointwise in
theorem Ferrand_Vasconcelos_aux [IsLocalRing R] [IsNoetherianRing R] [Small.{v} R]
    {I : Ideal R} (netop : I ≠ ⊤)
    (h : ∃ n, HasProjectiveDimensionLE (ModuleCat.of R (Shrink.{v} I)) n)
    (free : Module.Free (R ⧸ I) I.Cotangent) (n : ℕ) : Submodule.spanFinrank I = n →
    ∃ rs : List R, IsRegular R rs ∧ Ideal.ofList rs = I := by
  induction n generalizing R I
  · intro hrank
    have : I.FG := (isNoetherianRing_iff_ideal_fg R).mp ‹_› I
    have : Submodule.spanRank I = 0 := by
      simp [Submodule.fg_iff_spanRank_eq_spanFinrank.mpr this, hrank]
    simp only [Submodule.spanRank_eq_zero_iff_eq_bot] at this
    use []
    simpa [this] using RingTheory.Sequence.IsRegular.nil R R
  · rename_i n ih _ _ _ _
    have fg : I.FG := (isNoetherianRing_iff_ideal_fg R).mp ‹_› I
    intro hrank
    have nebot : I ≠ ⊥ := by
      simp [← Submodule.spanRank_eq_zero_iff_eq_bot, hrank,
        Submodule.fg_iff_spanRank_eq_spanFinrank.mpr fg]
    rcases exist_isSMulRegular_of_exist_hasProjectiveDimensionLE I netop nebot h with
      ⟨x, mem, nmem, xreg⟩
    let R' := R ⧸ Ideal.span {x}
    let I' := I.map (Ideal.Quotient.mk (Ideal.span {x}))
    have netop' : I.map (Ideal.Quotient.mk (Ideal.span {x})) ≠ ⊤ := by
      by_contra eqtop
      absurd netop
      rw [← sup_eq_left.mpr ((Ideal.span_singleton_le_iff_mem I).mpr mem),
        ← Ideal.mk_ker (I := Ideal.span {x}),
        ← Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective]
      simp [eqtop]
    let _ : IsLocalRing (R ⧸ Ideal.span {x}) :=
      have : Nontrivial (R ⧸ Ideal.span {x}) := Ideal.Quotient.nontrivial
        (by simpa [← Submodule.ideal_span_singleton_smul] using le_maximalIdeal netop mem)
      have : IsLocalHom (Ideal.Quotient.mk (Ideal.span {x})) :=
        IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
      IsLocalRing.of_surjective _ Ideal.Quotient.mk_surjective
    let _ : IsNoetherianRing (R ⧸ Ideal.span {x}) :=
      isNoetherianRing_of_surjective _ _ _ Ideal.Quotient.mk_surjective
    have fin : ∃ n, HasProjectiveDimensionLE
      (ModuleCat.of (R ⧸ Ideal.span {x}) (Shrink.{v, u} I')) n := by
      rcases h with ⟨n, hn⟩
      let _ : Module.Finite R ↑(ModuleCat.of R (Shrink.{v, u} I)) :=
        Module.Finite.equiv (Shrink.linearEquiv.{v} R I).symm
      have xreg' : IsSMulRegular (Shrink.{v, u} I) x :=
        ((Shrink.linearEquiv.{v} R I).isSMulRegular_congr x).mpr (xreg.submodule I x)
      rw [← projectiveDimension_le_iff, projectiveDimension_eq_quotient R
        (ModuleCat.of R (Shrink.{v} I)) x xreg xreg' (le_maximalIdeal netop mem),
        projectiveDimension_le_iff] at hn
      use n
      have : Retract (ModuleCat.of (R ⧸ Ideal.span {x}) (Shrink.{v} I'))
        (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x (Shrink.{v} I))) := by
        sorry
      exact this.hasProjectiveDimensionLT (n + 1)
    have free : Module.Free ((R ⧸ Ideal.span {x}) ⧸ I') I'.Cotangent := by
      sorry
    have rank : Submodule.spanFinrank I' = n := by
      sorry
    rcases ih netop' fin free rank with ⟨rs', reg, span⟩
    rcases List.map_surjective_iff.mpr Ideal.Quotient.mk_surjective rs' with ⟨rs, hrs⟩
    use x :: rs
    have eq : Ideal.span {x} ⊔ Ideal.ofList rs = I := by
      rw [← Ideal.mk_ker (I := Ideal.span {x}), sup_comm,
        ← Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective,
        Ideal.map_ofList, hrs, span]
      simpa [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, I'] using
        (Ideal.span_singleton_le_iff_mem I).mpr mem
    simp only [isRegular_cons_iff, xreg, true_and, Ideal.ofList_cons, eq, and_true]
    let e : QuotSMulTop x R ≃ₗ[R] (R ⧸ Ideal.span {x}) :=
      Submodule.quotEquivOfEq _ _ (by simp [← Submodule.ideal_span_singleton_smul])
    rw [LinearEquiv.isRegular_congr e]
    constructor
    · rw [← RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff (R ⧸ Ideal.span {x})]
      simpa [hrs] using reg.1
    · have : Ideal.ofList rs ≤ I := by simp [← eq]
      apply (ne_top_of_le_ne_top _ (Submodule.smul_mono_left this)).symm
      simpa using netop'

theorem Ferrand_Vasconcelos [IsLocalRing R] [IsNoetherianRing R] [Small.{v} R]
    {I : Ideal R} (netop : I ≠ ⊤)
    (h : ∃ n, HasProjectiveDimensionLE (ModuleCat.of R (Shrink.{v} I)) n)
    (free : Module.Free (R ⧸ I) I.Cotangent) :
    ∃ rs : List R, IsRegular R rs ∧ Ideal.ofList rs = I :=
  Ferrand_Vasconcelos_aux  netop h free (Submodule.spanFinrank I) rfl
