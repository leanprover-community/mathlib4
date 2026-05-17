/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.RingTheory.Depth.AuslanderBuchsbaum
public import Mathlib.RingTheory.Depth.Ischebeck
public import Mathlib.RingTheory.GlobalDimension
public import Mathlib.RingTheory.Regular.Free
public import Mathlib.RingTheory.RegularLocalRing.Basic

/-!

# A Noetherian Local Ring is Regular if its Maximal Ideal has Finite Projective Dimension

-/

@[expose] public section

universe u v

variable (R : Type u) [CommRing R]

open IsLocalRing CategoryTheory RingTheory.Sequence

private instance finite_QuotSMulTop (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (x : R) : Module.Finite (R ⧸ Ideal.span {x}) (QuotSMulTop x M) :=
  Module.Finite.of_restrictScalars_finite R _ _

section

variable {R} (x : R) {M N L : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup L]
    [Module R M] [Module R N] [Module R L]

/-- The linear map `M⧸xM →ₗ[R] N⧸xN` induced by a linear map `M →ₗ[R] N`. -/
def QuotSMulTop_map (f : M →ₗ[R] N) :
    QuotSMulTop x M →ₗ[R ⧸ Ideal.span {x}] QuotSMulTop x N where
  __ := Submodule.mapQ _ _ f (fun m hm ↦ by
    rcases (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hm with ⟨m', _, hm'⟩
    simpa [← hm'] using Submodule.smul_mem_pointwise_smul _ x ⊤ trivial)
  map_smul' r m := by
    rcases Ideal.Quotient.mk_surjective r with ⟨s, rfl⟩
    exact map_smul (Submodule.mapQ _ _ f _) s m

lemma QuotSMulTop_map_surjective {f : M →ₗ[R] N} (surj : Function.Surjective f) :
    Function.Surjective (QuotSMulTop_map x f) :=
  QuotSMulTop.map_surjective x surj

lemma QuotSMulTop_map_exact {f : M →ₗ[R] N} {g : N →ₗ[R] L} (exact : Function.Exact f g)
    (surj : Function.Surjective g) :
    Function.Exact (QuotSMulTop_map x f) (QuotSMulTop_map x g) :=
  QuotSMulTop.map_exact x exact surj

end

variable {R} in
lemma IsSMulRegular.of_free {x : R} (reg : IsSMulRegular R x) (M : Type*) [AddCommGroup M]
    [Module R M] [free : Module.Free R M] : IsSMulRegular M x := by
  rcases free with ⟨⟨I, ⟨e⟩⟩⟩
  rw [e.isSMulRegular_congr]
  apply IsSMulRegular.of_right_eq_zero_of_smul (fun y hy ↦ ?_)
  ext i
  apply reg.right_eq_zero_of_smul
  rw [← Finsupp.smul_apply, hy, Finsupp.zero_apply]

open Ideal in
lemma projectiveDimension_eq_quotient [Small.{v} R] [IsLocalRing R] [IsNoetherianRing R]
    (M : ModuleCat.{v} R) [Module.Finite R M] (x : R)
    (reg1 : IsSMulRegular R x) (reg2 : IsSMulRegular M x)
    (mem : x ∈ maximalIdeal R) : projectiveDimension.{v} M =
    projectiveDimension.{v} (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x M)) := by
  have aux (n : ℕ): projectiveDimension M ≤ n ↔
    projectiveDimension.{v} (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x M)) ≤ n := by
    simp only [projectiveDimension_le_iff]
    induction n generalizing M with
    | zero =>
      simp only [HasProjectiveDimensionLE, zero_add, ← projective_iff_hasProjectiveDimensionLT_one]
      rw [← IsProjective.iff_projective, ← IsProjective.iff_projective]
      refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
      · have := (free_iff_quotSMulTop_free R M mem reg2).mpr Module.free_of_flat_of_isLocalRing
        exact Module.Projective.of_free
      · have : IsLocalRing (R ⧸ Ideal.span {x}) :=
          have : Nontrivial (R ⧸ Ideal.span {x}) :=
            Quotient.nontrivial_iff.mpr (by simpa [← Submodule.ideal_span_singleton_smul])
          IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
        have := (free_iff_quotSMulTop_free R M mem reg2).mp Module.free_of_flat_of_isLocalRing
        exact Module.Projective.of_free
    | succ n ih =>
      obtain ⟨N, _, _, _, _, f, surjf⟩ := Module.exists_finite_presentation R M
      let S := f.shortComplexKer
      have S_exact := LinearMap.shortExact_shortComplexKer surjf
      have proj := ModuleCat.projective_of_categoryTheory_projective S.X₂
      have reg2'' : IsSMulRegular S.X₂ x := reg1.of_free S.X₂
      have reg2' : IsSMulRegular S.X₁ x := reg2''.submodule _ _
      have Sx_exact' := QuotSMulTop_map_exact x f.exact_subtype_ker_map surjf
      let Sx := ModuleCat.shortComplexOfCompEqZero (QuotSMulTop_map x (LinearMap.ker f).subtype)
        (QuotSMulTop_map x f) Sx_exact'.linearMap_comp_eq_zero
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
        use z, reg2.right_eq_zero_of_smul this
        exact Subtype.val_inj.mp hz
      have Sx_exact := ModuleCat.shortComplex_shortExact Sx Sx_exact' inj
        (QuotSMulTop_map_surjective x surjf)
      have := (free_iff_quotSMulTop_free R N mem reg2'').mpr inferInstance
      exact ((S_exact.hasProjectiveDimensionLT_X₃_iff n proj).trans (ih S.X₁ reg2')).trans
        (Sx_exact.hasProjectiveDimensionLT_X₃_iff n inferInstance).symm
  refine eq_of_forall_ge_iff (fun N ↦ ?_)
  induction N with
  | bot =>
    simp only [le_bot_iff, projectiveDimension_eq_bot_iff,
      projectiveDimension_eq_bot_iff, ModuleCat.isZero_iff_subsingleton]
    refine ⟨fun h ↦ (Submodule.Quotient.mk_surjective _).subsingleton, fun h ↦ ?_⟩
    by_contra! ntr
    exact (not_subsingleton_iff_nontrivial.mpr (nontrivial_quotSMulTop_of_mem_maximalIdeal M mem)) h
  | coe N =>
    induction N with
    | top => simp
    | coe n => exact aux n

variable {R}

set_option backward.isDefEq.respectTransparency false in
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
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, AlgHom.coe_toLinearMap,
      Ideal.Quotient.mkₐ_eq_mk, Function.comp_apply, EmbeddingLike.map_eq_zero_iff,
      Submodule.coe_subtype, Set.mem_range, Ideal.Quotient.eq_zero_iff_mem, Sg, Sf]
    refine ⟨fun h ↦ ⟨(equivShrink (maximalIdeal R)) ⟨_, h⟩, by simp⟩, fun ⟨y, hy⟩ ↦ by simp [← hy]⟩
  have inj : Function.Injective Sf := by
    simpa [Sf] using LinearEquiv.injective (Shrink.linearEquiv R (maximalIdeal R))
  have surj : Function.Surjective Sg := by
    simpa [Sg] using Ideal.Quotient.mk_surjective
  let S := ModuleCat.shortComplexOfCompEqZero Sf Sg exac.linearMap_comp_eq_zero
  have S_exact := ModuleCat.shortComplex_shortExact S exac inj surj
  rcases h with ⟨n, hn⟩
  have projdim := (S_exact.hasProjectiveDimensionLT_X₃_iff n
    (ModuleCat.projective_of_categoryTheory_projective S.X₂)).mpr hn
  have : Module.annihilator R (Shrink.{v} (R ⧸ maximalIdeal R)) = maximalIdeal R := by
    rw [(Shrink.linearEquiv.{v} R (R ⧸ maximalIdeal R)).annihilator_eq, Ideal.annihilator_quotient]
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
  let := projective_iff_hasProjectiveDimensionLT_one.mpr ((projectiveDimension_le_iff _ _).mp this)
  let : Module.Projective R (Shrink.{v} (R ⧸ maximalIdeal R)) :=
    ModuleCat.projective_of_module_projective (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R)))
  have : Module.Projective R (R ⧸ maximalIdeal R) :=
    Module.Projective.of_equiv (Shrink.linearEquiv.{v} R (R ⧸ maximalIdeal R))
  have : Module.Free R (R ⧸ maximalIdeal R) := Module.free_of_flat_of_isLocalRing
  let b := Module.Free.chooseBasis R (R ⧸ maximalIdeal R)
  have := b.1.annihilator_eq
  rw [Module.annihilator_finsupp, Ideal.annihilator_quotient] at this
  absurd nebot
  rw [this, Module.annihilator_eq_bot.mpr inferInstance]

set_option backward.isDefEq.respectTransparency false in
lemma exist_isSMulRegular_of_exist_hasProjectiveDimensionLE [IsLocalRing R] [IsNoetherianRing R]
    [Small.{v} R] (nebot : maximalIdeal R ≠ ⊥)
    (h : ∃ n, HasProjectiveDimensionLE (ModuleCat.of R (Shrink.{v} (maximalIdeal R))) n) :
    ∃ x ∈ maximalIdeal R, x ∉ maximalIdeal R ^ 2 ∧ IsSMulRegular R x := by
  --use prime avoidance to `m²` and associated primes of `R`
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
    · have : I.IsPrime := IsAssociatedPrime.isPrime ass
      rw [le_antisymm (le_maximalIdeal_of_isPrime I) sub] at ass
      absurd exist_isSMulRegular_of_exist_hasProjectiveDimensionLE_aux nebot h
      simp only [not_exists, not_and]
      intro x hx
      have : x ∈ {r : R | IsSMulRegular R r}ᶜ := by
        simpa [← biUnion_associatedPrimes_eq_compl_regular] using Set.mem_biUnion ass hx
      exact this
  simp only [Set.singleton_union, Set.mem_insert_iff, Set.iUnion_iUnion_eq_or_left, Set.mem_union,
    SetLike.mem_coe, Set.mem_iUnion, exists_prop, not_or, not_exists, not_and] at xnmem
  use x
  have : x ∈ {r : R | IsSMulRegular R r} := by
    rw [← Set.not_notMem, ← Set.mem_compl_iff, ← biUnion_associatedPrimes_eq_compl_regular]
    simpa using xnmem.2
  simpa [xmem, xnmem.1]

lemma spanFinrank_maximalIdeal_quotient [IsLocalRing R] [IsNoetherianRing R] (x : R)
    (mem : x ∈ maximalIdeal R) (nmem : x ∉ (maximalIdeal R) ^ 2) :
    letI : IsLocalRing (R ⧸ Ideal.span {x}) :=
      have : Nontrivial (R ⧸ Ideal.span {x}) :=
        Ideal.Quotient.nontrivial_iff.mpr (by simpa [← Submodule.ideal_span_singleton_smul])
      IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective
    (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank = (maximalIdeal R).spanFinrank - 1 := by
  have : Nontrivial (R ⧸ Ideal.span {x}) := Ideal.Quotient.nontrivial_iff.mpr
    (by simpa [← Submodule.ideal_span_singleton_smul] using mem)
  have : IsLocalRing (R ⧸ Ideal.span {x}) :=
    IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have sub := Finset.singleton_subset_set_iff.mpr mem
  have li : LinearIndependent (ResidueField R)
    ((maximalIdeal R).toCotangent ∘ Set.inclusion sub) := by
    simp only [SetLike.coe_sort_coe, linearIndependent_subsingleton_index_iff, Function.comp_apply,
      ne_eq, Subtype.forall, Finset.mem_singleton, Set.inclusion_mk]
    intro r hr
    simpa [Ideal.toCotangent_eq_zero, hr]
  rw [← IsLocalRing.spanFinrank_maximalIdeal_quotient {x} sub li]
  simp only [Finset.card_singleton, add_tsub_cancel_right]
  let e : R ⧸ Ideal.span {x} ≃+* R ⧸ Ideal.span (({x} : Finset R) : Set R) :=
    Ideal.quotEquivOfEq (by rw [Finset.coe_singleton x])
  have := e.isLocalRing
  rw [← map_ringEquiv_maximalIdeal e, Ideal.spanFinrank_map_eq_of_ringEquiv]

open Pointwise in
theorem generate_by_regular_aux [IsLocalRing R] [IsNoetherianRing R] [Small.{v} R]
    (h : ∃ n, HasProjectiveDimensionLE (ModuleCat.of R (Shrink.{v} (maximalIdeal R))) n)
    (n : ℕ) : Submodule.spanFinrank (maximalIdeal R) = n →
    ∃ rs : List R, IsRegular R rs ∧ Ideal.ofList rs = maximalIdeal R := by
  induction n generalizing R with
  | zero =>
    intro hrank
    have : (maximalIdeal R) = ⊥ := by
      simp [← Submodule.spanRank_eq_zero_iff_eq_bot, hrank,
        Submodule.fg_iff_spanRank_eq_spanFinrank.mpr (maximalIdeal R).fg_of_isNoetherianRing]
    use []
    simpa [this] using RingTheory.Sequence.IsRegular.nil R R
  | succ n ih =>
    have fg : (maximalIdeal R).FG := (maximalIdeal R).fg_of_isNoetherianRing
    intro hrank
    have nebot : maximalIdeal R ≠ ⊥ := by
      simp [← Submodule.spanRank_eq_zero_iff_eq_bot, hrank,
        Submodule.fg_iff_spanRank_eq_spanFinrank.mpr fg]
    rcases exist_isSMulRegular_of_exist_hasProjectiveDimensionLE nebot h with ⟨x, mem, nmem, xreg⟩
    let R' := R ⧸ Ideal.span {x}
    have : Nontrivial (R ⧸ Ideal.span {x}) := Ideal.Quotient.nontrivial_iff.mpr
      (by simpa [← Submodule.ideal_span_singleton_smul] using mem)
    have : IsLocalHom (Ideal.Quotient.mk (Ideal.span {x})) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    have : IsLocalRing (R ⧸ Ideal.span {x}) :=
      IsLocalRing.of_surjective _ Ideal.Quotient.mk_surjective
    let xm' := (Submodule.span (ResidueField R) {(maximalIdeal R).toCotangent ⟨x, mem⟩})
    rcases xm'.exists_isCompl with ⟨J', ⟨inf, sup⟩⟩
    let g : (maximalIdeal R) →ₛₗ[residue R] (maximalIdeal R).Cotangent := {
      __ := (maximalIdeal R).toCotangent
      map_smul' r m := map_smul (maximalIdeal R).toCotangent r m }
    have surjg : Function.Surjective g := (maximalIdeal R).toCotangent_surjective
    have supeq : (J'.comap g) ⊔ Submodule.span R {⟨x, mem⟩} = ⊤ := by
      have : RingHomSurjective (residue R) := ⟨residue_surjective⟩
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
        simp [← maximalIdeal_comap (Ideal.Quotient.mk (Ideal.span {x})), hz]
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
    let i3 : ((J'.comap g) ⧸ (J'.comap g).comap (J'.comap g).subtype  ⊓
      Submodule.comap (J'.comap g).subtype (Submodule.span R {⟨x, mem⟩})) →ₗ[R]
      QuotSMulTop x (Shrink.{v} (maximalIdeal R)) :=
      Submodule.mapQ _ _ ((Shrink.linearEquiv.{v} R (maximalIdeal R)).symm.toLinearMap.comp
        (J'.comap g).subtype) (by
          rw [← Submodule.comap_inf, Submodule.comap_comp]
          apply Submodule.comap_mono (le_trans infle (fun y hy ↦ ?_))
          rcases (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hy with ⟨z, _, hz⟩
          simp only [Submodule.mem_comap, ← hz, map_smul]
          exact Submodule.smul_mem_pointwise_smul _ x ⊤ trivial)
    let i' : Shrink.{v} (maximalIdeal R') →ₗ[R] QuotSMulTop x (Shrink.{v} (maximalIdeal R)) :=
      i3.comp (e1.trans e2.symm).toLinearMap
    let r' : QuotSMulTop x (Shrink.{v} (maximalIdeal R)) →ₗ[R] Shrink.{v} (maximalIdeal R') :=
      Submodule.liftQ _ ((Shrink.linearEquiv.{v} R (maximalIdeal R')).symm.toLinearMap.comp
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
      simp [e1, e1']
    have : IsScalarTower R (R ⧸ Ideal.span {x}) (Shrink.{v} (maximalIdeal R')) :=
      (equivShrink (maximalIdeal R')).symm.isScalarTower R _
    let r := r'.extendScalarsOfSurjective (Ideal.Quotient.mk_surjective (I := Ideal.span {x}))
    let i := i'.extendScalarsOfSurjective (Ideal.Quotient.mk_surjective (I := Ideal.span {x}))
    have compid' : r.comp i = LinearMap.id := by
      apply LinearMap.ext (fun y ↦ ?_)
      simpa using LinearMap.ext_iff.mp compid y
    have retr  : Retract (ModuleCat.of (R ⧸ Ideal.span {x}) (Shrink.{v} (maximalIdeal R')))
      (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x (Shrink.{v} (maximalIdeal R)))) := {
      i := ModuleCat.ofHom i
      r := ModuleCat.ofHom r
      retract := by rw [← ModuleCat.ofHom_comp, compid', ModuleCat.ofHom_id]}
    have fin : ∃ n, HasProjectiveDimensionLE
      (ModuleCat.of R' (Shrink.{v, u} (maximalIdeal R'))) n := by
      rcases h with ⟨n, hn⟩
      have xreg' : IsSMulRegular (Shrink.{v} (maximalIdeal R)) x :=
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
        Ideal.map_ofList, hrs, span, maximalIdeal_comap (Ideal.Quotient.mk (Ideal.span {x}))]
    simp only [isRegular_cons_iff, xreg, true_and, Ideal.ofList_cons, eq, and_true]
    let e : QuotSMulTop x R ≃ₗ[R] (R ⧸ Ideal.span {x}) :=
      Submodule.quotEquivOfEq _ _ (by simp [← Submodule.ideal_span_singleton_smul])
    rw [e.isRegular_congr]
    constructor
    · rw [← RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff (R ⧸ Ideal.span {x})]
      simpa [hrs] using reg.1
    · have : Ideal.ofList rs ≤ maximalIdeal R := by simp [← eq]
      apply (ne_top_of_le_ne_top _ (Submodule.smul_mono_left this)).symm
      simp only [Ideal.smul_top_eq_map, Ideal.Quotient.algebraMap_eq, ne_eq,
        Submodule.restrictScalars_eq_top_iff]
      have : Ideal.map (Ideal.Quotient.mk (Ideal.span {x})) (maximalIdeal R) ≤ maximalIdeal R' := by
        rw [Ideal.map_le_iff_le_comap, maximalIdeal_comap (Ideal.Quotient.mk (Ideal.span {x}))]
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
  apply of_spanFinrank_maximalIdeal_le
  have spaneq : Ideal.span (rs.toFinset : Set R) = maximalIdeal R := by simp [← span]
  nth_rw 1 [← spaneq]
  apply le_trans (Nat.cast_le.mpr
    (Submodule.spanFinrank_span_le_ncard_of_finite rs.toFinset.finite_toSet))
  rw [Set.ncard_coe_finset rs.toFinset]
  apply le_trans (Nat.cast_le.mpr rs.toFinset_card_le)
  apply le_trans _ (depth_le_ringKrullDim (ModuleCat.of R R))
  have : (rs.length : WithBot ℕ∞) = (rs.length : ℕ∞) := rfl
  rw [IsLocalRing.depth_eq_sSup_length_regular, this, WithBot.coe_le_coe]
  apply le_sSup
  use rs, reg
  simp only [← span, exists_prop, and_true]
  exact fun r hr ↦ Ideal.subset_span hr

theorem IsRegularLocalRing.of_globalDimension_lt_top [IsLocalRing R] [IsNoetherianRing R]
    [Small.{v} R] (h : globalDimension.{v} R < ⊤) : IsRegularLocalRing R := by
  apply IsRegularLocalRing.of_maximalIdeal_hasProjectiveDimensionLE
  rw [← projectiveDimension_ne_top_iff]
  by_contra eqtop
  absurd h
  simp only [globalDimension, ← eqtop, not_lt]
  exact le_iSup _ (ModuleCat.of R (Shrink.{v} (maximalIdeal R)))
