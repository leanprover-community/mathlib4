/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.Ext.Finite
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Regular.Category
public import Mathlib.RingTheory.Regular.RegularSequence

/-!

# ProjectiveDimension of quotient by regular element

For `M` a finitely generated module over Noetherian local ring `R` and an `R`-regular element `x`,
`projdim(M/xM) = projdim(M) + 1`

-/

@[expose] public section

section ENat

lemma WithBot.add_le_add_right_iff (a b : WithBot ℕ∞) (c : ℕ) :
    a + c ≤ b + c ↔ a ≤ b := by
  induction a with
  | bot => simp
  | coe a =>
    induction b with
    | bot => simp
    | coe b =>
      norm_cast
      exact WithTop.add_le_add_iff_right (ENat.coe_ne_top c)

lemma WithBot.add_one_le_zero_iff_eq_bot (a : WithBot ℕ∞) :
    a + 1 ≤ 0 ↔ a = ⊥ := by
  induction a with
  | bot => simp
  | coe a => simp [← WithBot.coe_one, ← WithBot.coe_add]

end ENat

universe v u

variable (R : Type u) [CommRing R]

local instance small_of_quotient' [Small.{v} R] (I : Ideal R) : Small.{v} (R ⧸ I) :=
  small_of_surjective Ideal.Quotient.mk_surjective

open CategoryTheory Abelian IsLocalRing Module RingTheory.Sequence

variable {R} in
lemma mem_quotSMulTop_annihilator (x : R) (M : Type*) [AddCommGroup M] [Module R M] :
    x ∈ Module.annihilator R (QuotSMulTop x M) := by
  refine mem_annihilator.mpr (fun m ↦ ?_)
  rcases Submodule.Quotient.mk_surjective _ m with ⟨m', hm'⟩
  simpa [← hm', ← Submodule.Quotient.mk_smul] using Submodule.smul_mem_pointwise_smul m' x ⊤ trivial

variable {R} in
lemma quotSMulTop_nontrivial' [IsLocalRing R] {x : R} (mem : x ∈ maximalIdeal R)
    (L : Type*) [AddCommGroup L] [Module R L] [Module.Finite R L] [Nontrivial L] :
    Nontrivial (QuotSMulTop x L) := by
  apply Submodule.Quotient.nontrivial_iff.mpr (Ne.symm _)
  apply Submodule.top_ne_pointwise_smul_of_mem_jacobson_annihilator
  exact IsLocalRing.maximalIdeal_le_jacobson _ mem

section

variable {R}

variable [IsNoetherianRing R] [Small.{v} R]

lemma ext_vanish_of_for_all_finite (M : ModuleCat.{v} R) (n : ℕ) [Module.Finite R M]
    (h : ∀ L : ModuleCat.{v} R, Module.Finite R L →  Subsingleton (Ext M L n)) :
    ∀ N : ModuleCat.{v} R, Subsingleton (Ext M N n) := by
  induction n generalizing M
  · let _ := h M ‹_›
    let _ : Subsingleton (M ⟶ M) := Ext.homEquiv₀.symm.subsingleton
    have : Limits.IsZero M := (Limits.IsZero.iff_id_eq_zero M).mpr (Subsingleton.eq_zero (𝟙 M))
    intro N
    rw [Ext.homEquiv₀.subsingleton_congr]
    exact subsingleton_of_forall_eq 0 (fun f ↦ this.eq_zero_of_src f)
  · rename_i n hn _
    rcases Module.exists_finite_presentation R M with ⟨_, _, _, _, _, f, surjf⟩
    let S : ShortComplex (ModuleCat.{v} R) := f.shortComplexKer
    have S_exact : S.ShortExact := LinearMap.shortExact_shortComplexKer surjf
    match n with
    | 0 =>
      simp only [zero_add, ← projective_iff_subsingleton_ext_one]
      have : Subsingleton (Ext M S.X₁ 1) := h S.X₁ inferInstance
      rcases Ext.covariant_sequence_exact₃ M S_exact (Ext.mk₀ (𝟙 M)) (zero_add 1)
        (Subsingleton.eq_zero _) with ⟨f', hf'⟩
      rcases (Ext.mk₀_bijective M S.X₂).2 f' with ⟨f, hf⟩
      rw [← hf, Ext.mk₀_comp_mk₀, (Ext.mk₀_bijective _ _).1.eq_iff] at hf'
      exact (Retract.mk f S.g hf').projective
    | n + 1 =>
      have (L : ModuleCat.{v} R) : Subsingleton (Ext S.X₁ L (n + 1)) ↔
        Subsingleton (Ext M L (n + 2)) := by
        let _ (m : ℕ) : Subsingleton (Ext S.X₂ L (m + 1)) :=
          subsingleton_of_forall_eq 0 (fun y ↦ Ext.eq_zero_of_projective y)
        have isi := (Ext.contravariantSequence_exact S_exact L (n + 1) (n + 2)
          (add_comm 1 _)).isIso_map' 1 (by decide)
          ((AddCommGrpCat.of _).isZero_of_subsingleton.eq_zero_of_src _)
          ((AddCommGrpCat.of _).isZero_of_subsingleton.eq_zero_of_tgt _)
        exact (@asIso _ _ _ _ _ isi).addCommGroupIsoToAddEquiv.subsingleton_congr
      simp only [← this]
      apply hn S.X₁
      simpa [this] using h

end

variable {R} [IsLocalRing R] [IsNoetherianRing R]

lemma projectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular [Small.{v} R] (M : ModuleCat.{v} R)
    [Module.Finite R M] (x : R) (reg : IsSMulRegular M x) (mem : x ∈ maximalIdeal R) :
    projectiveDimension (ModuleCat.of R (QuotSMulTop x M)) = projectiveDimension M + 1 := by
  have sub : Subsingleton M ↔ Subsingleton (QuotSMulTop x M) := by
    refine ⟨fun h ↦ inferInstance, fun h ↦ ?_⟩
    by_contra!
    exact (not_subsingleton_iff_nontrivial.mpr (quotSMulTop_nontrivial' mem M)) h
  have aux (n : ℕ) : projectiveDimension (ModuleCat.of R (QuotSMulTop x M)) ≤ n ↔
    projectiveDimension M + 1 ≤ n := by
    match n with
    | 0 =>
      have : projectiveDimension M + 1 ≤ 0 ↔ projectiveDimension M = ⊥ :=
        WithBot.add_one_le_zero_iff_eq_bot (projectiveDimension M)
      rw [projectiveDimension_le_iff]
      simp only [HasProjectiveDimensionLE, zero_add, ← projective_iff_hasProjectiveDimensionLT_one,
        CharP.cast_eq_zero, this, projectiveDimension_eq_bot_iff,
        ModuleCat.isZero_iff_subsingleton, sub, ← IsProjective.iff_projective]
      refine ⟨fun h ↦ ?_, fun h ↦ Projective.of_free⟩
      have : Module.Free R (QuotSMulTop x M) := Module.free_of_flat_of_isLocalRing
      by_contra ntr
      let _ := not_subsingleton_iff_nontrivial.mp ntr
      have := mem_quotSMulTop_annihilator x M
      simp only [annihilator_eq_bot.mpr inferInstance, Submodule.mem_bot] at this
      simp only [this, IsSMulRegular.zero_iff_subsingleton] at reg
      absurd ntr
      infer_instance
    | n + 1 =>
      nth_rw 2 [← Nat.cast_one, Nat.cast_add]
      rw [WithBot.add_le_add_right_iff _ _ 1, projectiveDimension_le_iff,
        projectiveDimension_le_iff]
      let S := M.smulShortComplex x
      have S_exact : S.ShortExact := reg.smulShortComplex_shortExact
      refine ⟨fun h ↦ ?_, fun h ↦ S_exact.hasProjectiveDimensionLT_X₃ (n + 1) h
          (hasProjectiveDimensionLT_of_ge M (n + 1) (n + 1 + 1) (Nat.le_add_right _ 1))⟩
      simp only [HasProjectiveDimensionLE, hasProjectiveDimensionLT_iff]
      intro i hi
      have : ∀ N : ModuleCat.{v} R, Subsingleton (Ext M N i) := by
        apply ext_vanish_of_for_all_finite M _
        intro L _
        have zero := HasProjectiveDimensionLT.subsingleton (ModuleCat.of R (QuotSMulTop x M))
          (n + 1 + 1) (i + 1) (Nat.add_le_add_right hi 1) L
        have exac := Ext.contravariant_sequence_exact₁' S_exact L i (i + 1) (add_comm 1 i)
        have epi := exac.epi_f ((@AddCommGrpCat.isZero_of_subsingleton _ zero).eq_zero_of_tgt _)
        have : S.f = x • 𝟙 M := rfl
        simp only [S, this, AddCommGrpCat.epi_iff_surjective, AddCommGrpCat.hom_ofHom] at epi
        by_contra ntr
        let _ : Nontrivial (Ext M L i) := not_subsingleton_iff_nontrivial.mp ntr
        have : x ∈ (Module.annihilator R (Ext M L i)).jacobson :=
          (IsLocalRing.maximalIdeal_le_jacobson _) mem
        absurd Submodule.top_ne_pointwise_smul_of_mem_jacobson_annihilator this
        rw [eq_comm, eq_top_iff]
        intro y hy
        rcases epi y with ⟨z, hz⟩
        simp only [ModuleCat.smulShortComplex_X₁, ModuleCat.smulShortComplex_X₂, Ext.mk₀_smul,
          Ext.bilinearComp_apply_apply, Ext.smul_comp, Ext.mk₀_id_comp] at hz
        simpa [← hz] using Submodule.smul_mem_pointwise_smul _ _ ⊤ trivial
      intro N e
      exact (this N).eq_zero e
  refine eq_of_forall_ge_iff (fun N ↦ ?_)
  induction N with
  | bot =>
    simpa only [le_bot_iff, projectiveDimension_eq_bot_iff,
      ModuleCat.isZero_iff_subsingleton, WithBot.add_eq_bot, WithBot.one_ne_bot, or_false]
      using sub.symm
  | coe N =>
    induction N with
    | top => simp
    | coe n => simpa using aux n

lemma projectiveDimension_quotient_regular_sequence [Small.{v} R] (M : ModuleCat.{v} R)
    [Nontrivial M] [Module.Finite R M] (rs : List R) (reg : IsWeaklyRegular M rs)
    (mem : ∀ r ∈ rs, r ∈ maximalIdeal R) :
    projectiveDimension (ModuleCat.of R (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M))) =
    projectiveDimension M + rs.length := by
  generalize len : rs.length = n
  induction n generalizing M rs
  · rw [List.length_eq_zero_iff.mp len, Ideal.ofList_nil, Submodule.bot_smul]
    simpa using projectiveDimension_eq_of_iso (Submodule.quotEquivOfEqBot ⊥ rfl).toModuleIso
  · rename_i n hn _ _
    match rs with
    | [] => simp at len
    | x :: rs' =>
      simp only [List.mem_cons, forall_eq_or_imp] at mem
      let _ : Nontrivial (QuotSMulTop x M) := quotSMulTop_nontrivial' mem.1 M
      simp only [Nat.cast_add, Nat.cast_one]
      simp only [List.length_cons, Nat.add_right_cancel_iff] at len
      have : IsSMulRegular M x := ((isWeaklyRegular_cons_iff M _ _).mp reg).1
      rw [projectiveDimension_eq_of_iso
        (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M x rs').toModuleIso, add_comm _ 1,
        ← add_assoc, ← projectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular M x this mem.1,
        ← hn (ModuleCat.of R (QuotSMulTop x M)) rs' ((isWeaklyRegular_cons_iff M _ _).mp reg).2
          mem.2 len]

omit [IsLocalRing R] [IsNoetherianRing R] in
lemma projectiveDimension_eq_zero_of_projective (M : ModuleCat.{v} R) [Projective M]
    [Nontrivial M] : projectiveDimension M = 0 := by
  apply le_antisymm
  · rw [← Nat.cast_zero, projectiveDimension_le_iff M 0]
    infer_instance
  · rw [← Nat.cast_zero, projectiveDimension_ge_iff M 0, hasProjectiveDimensionLT_zero_iff_isZero,
      ModuleCat.isZero_iff_subsingleton, not_subsingleton_iff_nontrivial]
    assumption

section

variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The linear map `M/IM → N/IN` induced by `M → N`. -/
def Ideal.smulTopLinearMap (I : Ideal R) (f : M →ₗ[R] N) :
    M ⧸ I • (⊤ : Submodule R M) →ₗ[R] N ⧸ I • (⊤ : Submodule R N) :=
  Submodule.mapQ _ _ f (Submodule.smul_top_le_comap_smul_top I f)

/-- The linear map `M/IM ≃ N/IN` induced by `M ≃ N`. -/
def Ideal.smulTopLinearEquiv (I : Ideal R) (e : M ≃ₗ[R] N) :
    (M ⧸ I • (⊤ : Submodule R M)) ≃ₗ[R] (N ⧸ I • (⊤ : Submodule R N)) where
  __ := Ideal.smulTopLinearMap I e
  invFun := Ideal.smulTopLinearMap I e.symm
  left_inv y := by
    induction y using Submodule.Quotient.induction_on
    simp [smulTopLinearMap]
  right_inv y := by
    induction y using Submodule.Quotient.induction_on
    simp [smulTopLinearMap]

end

variable [Small.{v} R]

lemma projectiveDimension_quotient_eq_length (rs : List R) (reg : IsRegular R rs) :
    projectiveDimension (ModuleCat.of R (Shrink.{v} (R ⧸ Ideal.ofList rs))) = rs.length := by
  have mem_max : ∀ x ∈ rs, x ∈ maximalIdeal R := by
    intro x hx
    apply IsLocalRing.le_maximalIdeal reg.2.symm
    simpa using (Ideal.mem_span x).mpr fun p a ↦ a hx
  let e : (Shrink.{v} (R ⧸ Ideal.ofList rs)) ≃ₗ[R]
    (Shrink.{v} R) ⧸ Ideal.ofList rs • (⊤ : Submodule R (Shrink.{v} R)) :=
    ((Shrink.linearEquiv R _).trans (Submodule.quotEquivOfEq _ _ (by simp))).trans
    ((Ideal.ofList rs).smulTopLinearEquiv (Shrink.linearEquiv R R).symm)
  rw [projectiveDimension_eq_of_iso e.toModuleIso,
    projectiveDimension_quotient_regular_sequence (ModuleCat.of R (Shrink.{v} R)) rs
    (((Shrink.linearEquiv R R).isWeaklyRegular_congr rs).mpr reg.1) mem_max,
    projectiveDimension_eq_zero_of_projective, zero_add]
