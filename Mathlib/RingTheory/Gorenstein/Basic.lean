/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
import Mathlib.CategoryTheory.Abelian.Injective.Dimension
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.BaseChange
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.RingTheory.CohenMacaulay.Basic
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.GlobalDimension
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.RingTheory.RingHom.Flat
/-!

# The Definition of Gorenstein (Local) Ring

-/

section ENat

lemma ENat.add_le_add_right_iff (a b : ℕ∞) (c : ℕ) :
    a + c ≤ b + c ↔ a ≤ b := by
  induction a with
  | top => simpa only [_root_.top_add, top_le_iff] using WithTop.add_coe_eq_top_iff
  | coe a => induction b with
    | top => simp
    | coe b => simp [← Nat.cast_add]

lemma WithBot.add_le_add_right_iff (a b : WithBot ℕ∞) (c : ℕ) :
    a + c ≤ b + c ↔ a ≤ b := by
  induction a with
  | bot => simp
  | coe a =>
    induction b with
    | bot => simp
    | coe b =>
      norm_cast
      exact ENat.add_le_add_right_iff a b c

lemma WithBot.add_one_le_zero_iff_eq_bot (a : WithBot ℕ∞) :
    a + 1 ≤ 0 ↔ a = ⊥ := by
  induction a with
  | bot => simp
  | coe a => simp [← WithBot.coe_one, ← WithBot.coe_add]

end ENat

universe v u

variable (R : Type u) [CommRing R]

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

lemma exist_nat_eq' [FiniteRingKrullDim R] : ∃ n : ℕ, ringKrullDim R = n := by
  have : (ringKrullDim R).unbot ringKrullDim_ne_bot ≠ ⊤ := by
    by_contra eq
    rw [← WithBot.coe_inj, WithBot.coe_unbot, WithBot.coe_top] at eq
    exact ringKrullDim_ne_top eq
  use ((ringKrullDim R).unbot ringKrullDim_ne_bot).toNat
  exact (WithBot.coe_unbot (ringKrullDim R) ringKrullDim_ne_bot).symm.trans
    (WithBot.coe_inj.mpr (ENat.coe_toNat this).symm)

local instance small_of_quotient' [Small.{v} R] (I : Ideal R) : Small.{v} (R ⧸ I) :=
  small_of_surjective Ideal.Quotient.mk_surjective

open CategoryTheory Abelian IsLocalRing Module RingTheory.Sequence

variable {R} in
lemma mem_quotSMulTop_annihilator (x : R) (M : Type*) [AddCommGroup M] [Module R M] :
    x ∈ Module.annihilator R (QuotSMulTop x M) := by
  refine mem_annihilator.mpr (fun m ↦ ?_)
  rcases Submodule.Quotient.mk_surjective _ m with ⟨m', hm'⟩
  simpa [← hm', ← Submodule.Quotient.mk_smul] using Submodule.smul_mem_pointwise_smul m' x ⊤ trivial

section

universe w

variable [UnivLE.{v, w}]

instance hasExt_of_small' [Small.{v} R] : CategoryTheory.HasExt.{w} (ModuleCat.{v} R) :=
  CategoryTheory.hasExt_of_enoughProjectives.{w} (ModuleCat.{v} R)

instance [Small.{v} R] [IsNoetherianRing R] (N M : ModuleCat.{v} R)
    [Module.Finite R N] [Module.Finite R M] (i : ℕ) : Module.Finite R (Ext.{w} N M i) := by
  induction i generalizing N
  · exact Module.Finite.equiv ((Ext.linearEquiv₀ (R := R)).trans ModuleCat.homLinearEquiv).symm
  · rename_i n ih _
    rcases Module.Finite.exists_fin' R N with ⟨m, f', hf'⟩
    let f := f'.comp ((Finsupp.mapRange.linearEquiv (Shrink.linearEquiv.{v} R R)).trans
      (Finsupp.linearEquivFunOnFinite R R (Fin m))).1
    have surjf : Function.Surjective f := by simpa [f] using hf'
    let S : ShortComplex (ModuleCat.{v} R) := {
      f := ModuleCat.ofHom.{v} (LinearMap.ker f).subtype
      g := ModuleCat.ofHom.{v} f
      zero := by
        ext x
        simp }
    have S_exact' : Function.Exact (ConcreteCategory.hom S.f) (ConcreteCategory.hom S.g) := by
      intro x
      simp [S]
    have S_exact : S.ShortExact := {
      exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mpr S_exact'
      mono_f := (ModuleCat.mono_iff_injective S.f).mpr (LinearMap.ker f).injective_subtype
      epi_g := (ModuleCat.epi_iff_surjective S.g).mpr surjf}
    let _ : Module.Finite R S.X₂ := by
      simp [S, Module.Finite.equiv (Shrink.linearEquiv R R).symm, Finite.of_fintype (Fin m)]
    let _ : Module.Free R (Shrink.{v, u} R) :=  Module.Free.of_equiv (Shrink.linearEquiv R R).symm
    let _ : Module.Free R S.X₂ := Module.Free.finsupp R (Shrink.{v, u} R) _
    have proj := ModuleCat.projective_of_categoryTheory_projective S.X₂
    have : Subsingleton (Ext S.X₂ M (n + 1)) :=
      subsingleton_of_forall_eq 0 Ext.eq_zero_of_projective
    have epi := (Ext.contravariant_sequence_exact₃' S_exact M n (n + 1) (add_comm 1 n)).epi_f
      ((AddCommGrpCat.of (Ext S.X₂ M (n + 1))).isZero_of_subsingleton.eq_zero_of_tgt _)
    have surj : Function.Surjective (S_exact.extClass.precomp M (add_comm 1 n)) :=
      (AddCommGrpCat.epi_iff_surjective _).mp epi
    let f : Ext S.X₁ M n →ₗ[R] Ext S.X₃ M (n + 1) := {
      __ := S_exact.extClass.precomp M (add_comm 1 n)
      map_smul' r x := by simp }
    exact Module.Finite.of_surjective f surj

variable {R}

variable [IsNoetherianRing R] [Small.{v} R]

lemma ext_vanish_of_for_all_finite (M : ModuleCat.{v} R) (n : ℕ) [Module.Finite R M]
    (h : ∀ L : ModuleCat.{v} R, Module.Finite R L →  Subsingleton (Ext.{w} M L n)) :
    ∀ N : ModuleCat.{v} R, Subsingleton (Ext.{w} M N n) := by
  induction n generalizing M
  · let _ := h M ‹_›
    let _ : Subsingleton (M ⟶ M) := Ext.homEquiv₀.symm.subsingleton
    have : Limits.IsZero M := (Limits.IsZero.iff_id_eq_zero M).mpr (Subsingleton.eq_zero (𝟙 M))
    intro N
    rw [Ext.homEquiv₀.subsingleton_congr]
    exact subsingleton_of_forall_eq 0 (fun f ↦ this.eq_zero_of_src f)
  · rename_i n hn _
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
    have S_exact' : Function.Exact (ConcreteCategory.hom S.f) (ConcreteCategory.hom S.g) := by
      intro x
      simp [S]
    have S_exact : S.ShortExact := {
      exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mpr S_exact'
      mono_f := (ModuleCat.mono_iff_injective S.f).mpr (LinearMap.ker f).injective_subtype
      epi_g := (ModuleCat.epi_iff_surjective S.g).mpr surjf}
    let _ : Module.Finite R S.X₂ := by
      simp [S, Module.Finite.equiv (Shrink.linearEquiv R R).symm, Finite.of_fintype (Fin m)]
    let _ : Module.Free R (Shrink.{v, u} R) :=  Module.Free.of_equiv (Shrink.linearEquiv R R).symm
    let _ : Module.Free R S.X₂ := Module.Free.finsupp R (Shrink.{v, u} R) _
    have proj := ModuleCat.projective_of_categoryTheory_projective S.X₂
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
        have isi := ComposableArrows.Exact.isIso_map' (Ext.contravariantSequence_exact S_exact L
            (n + 1) (n + 2) (add_comm 1 _)) 1 (by decide)
          (((AddCommGrpCat.of (Ext S.X₂ L (n + 1))).isZero_of_subsingleton).eq_zero_of_src _)
          (((AddCommGrpCat.of (Ext S.X₂ L (n + 2))).isZero_of_subsingleton).eq_zero_of_tgt _)
        exact (@CategoryTheory.asIso _ _ _ _ _ isi).addCommGroupIsoToAddEquiv.subsingleton_congr
      simp only [← this]
      apply hn S.X₁
      simpa [this] using h

end

variable {R} [IsLocalRing R] [IsNoetherianRing R]

lemma projectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular [Small.{v} R] (M : ModuleCat.{v} R)
    [Module.Finite R M] (x : R) (reg : IsSMulRegular M x) (mem : x ∈ maximalIdeal R) :
    projectiveDimension (ModuleCat.of R (QuotSMulTop x M)) = projectiveDimension M + 1 := by
  letI := HasExt.standard (ModuleCat.{v} R)
  have sub : Subsingleton M ↔ Subsingleton (QuotSMulTop x M) := by
    refine ⟨fun h ↦ inferInstance, fun h ↦ ?_⟩
    by_contra!
    exact (not_subsingleton_iff_nontrivial.mpr (quotSMulTop_nontrivial mem M)) h
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
        apply ext_vanish_of_for_all_finite
        intro L _
        have zero := HasProjectiveDimensionLT.subsingleton (ModuleCat.of R (QuotSMulTop x M))
          (n + 1 + 1) (i + 1) (Nat.add_le_add_right hi 1) L
        have exac := Ext.contravariant_sequence_exact₁' S_exact L i (i + 1) (add_comm 1 i)
        have epi := exac.epi_f ((@AddCommGrpCat.isZero_of_subsingleton _ zero).eq_zero_of_tgt _)
        have : S.f = x • 𝟙 M := by
          ext
          simp [S]
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
  by_cases eqbot : N = ⊥
  · simpa only [eqbot, le_bot_iff, projectiveDimension_eq_bot_iff,
      ModuleCat.isZero_iff_subsingleton, WithBot.add_eq_bot, WithBot.one_ne_bot, or_false]
      using sub.symm
  · by_cases eqtop : N.unbot eqbot = ⊤
    · have : N = ⊤ := (WithBot.coe_unbot _ eqbot).symm.trans (WithBot.coe_inj.mpr eqtop)
      simp [this]
    · let n := (N.unbot eqbot).toNat
      have : N = n := (WithBot.coe_unbot _ eqbot).symm.trans
        (WithBot.coe_inj.mpr (ENat.coe_toNat eqtop).symm)
      simpa only [this] using aux n

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
      let _ : Nontrivial (QuotSMulTop x M) := quotSMulTop_nontrivial mem.1 M
      simp only [Nat.cast_add, Nat.cast_one]
      simp only [List.length_cons, Nat.add_right_cancel_iff] at len
      have : IsSMulRegular M x := ((isWeaklyRegular_cons_iff M _ _).mp reg).1
      rw [projectiveDimension_eq_of_iso
        (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M x rs').toModuleIso, add_comm _ 1,
        ← add_assoc, ← projectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular M x this mem.1,
        ← hn (ModuleCat.of R (QuotSMulTop x M)) rs' ((isWeaklyRegular_cons_iff M _ _).mp reg).2
          mem.2 len]

section

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

def quotSMulTopLinearMap (x : R) (f : M →ₗ[R] N) : QuotSMulTop x M →ₗ[R] QuotSMulTop x N :=
  Submodule.mapQ _ _ f (fun m hm ↦ by
    rcases (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hm with ⟨m', _, hm'⟩
    simpa [← hm'] using Submodule.smul_mem_pointwise_smul _ x ⊤ trivial)

def quotSMulTopLinearEquiv (x : R) (e : M ≃ₗ[R] N) :
    (QuotSMulTop x M) ≃ₗ[R] (QuotSMulTop x N) where
  __ := quotSMulTopLinearMap x e.toLinearMap
  invFun := quotSMulTopLinearMap x e.symm.toLinearMap
  left_inv y := by
    induction y using Submodule.Quotient.induction_on
    simp [quotSMulTopLinearMap]
  right_inv y := by
    induction y using Submodule.Quotient.induction_on
    simp [quotSMulTopLinearMap]

def Ideal.smulTopLinearMap (I : Ideal R) (f : M →ₗ[R] N) :
    M ⧸ I • (⊤ : Submodule R M) →ₗ[R] N ⧸ I • (⊤ : Submodule R N) :=
  Submodule.mapQ _ _ f (Submodule.smul_top_le_comap_smul_top I f)

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

omit [IsLocalRing R] [IsNoetherianRing R] in
lemma Ideal.ofList_reverse (rs : List R) : Ideal.ofList rs.reverse = Ideal.ofList rs := by
  simp [Ideal.ofList]

variable (M) in
def Submodule.quotOfListSMulTopEquivQuotSMulTopOuter {rs rs' : List R} {a : R}
    (eq : rs = rs' ++ [a]) : (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M)) ≃ₗ[R]
    QuotSMulTop a (M ⧸ Ideal.ofList rs' • (⊤ : Submodule R M)) :=
  ((Submodule.quotEquivOfEq _ _ (by simp [eq, sup_comm, Ideal.ofList_reverse])).trans
    (Submodule.quotOfListConsSMulTopEquivQuotSMulTopOuter M a rs'.reverse)).trans
    (quotSMulTopLinearEquiv a (Submodule.quotEquivOfEq _ _ (by simp [Ideal.ofList_reverse])))

def Ideal.quotOfListSMulTopEquivQuotSMulTopOuter {rs rs' : List R} {a : R}
    (eq : rs = rs' ++ [a]) : (R ⧸ Ideal.ofList rs) ≃ₗ[R]
    QuotSMulTop a (R ⧸ Ideal.ofList rs') :=
    ((Submodule.quotEquivOfEq _ _ (by simp)).trans
    (Submodule.quotOfListSMulTopEquivQuotSMulTopOuter R eq)).trans
    (quotSMulTopLinearEquiv a (Submodule.quotEquivOfEq _ _ (by simp)))

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
  rw [projectiveDimension_eq_of_iso e.toModuleIso]
  let _ : Module.Finite R (Shrink.{v} R) := Module.Finite.equiv (Shrink.linearEquiv R _).symm
  let _ : Module.Free R (Shrink.{v} R) := Module.Free.of_equiv (Shrink.linearEquiv R _).symm
  rw [projectiveDimension_quotient_regular_sequence (ModuleCat.of R (Shrink.{v} R)) rs
    (((Shrink.linearEquiv R R).isWeaklyRegular_congr rs).mpr reg.1) mem_max]
  rw [projectiveDimension_eq_zero_of_projective, zero_add]

universe w

variable [UnivLE.{v, w}]

instance hasExt_of_small'' [Small.{v} R] : CategoryTheory.HasExt.{w} (ModuleCat.{v} R) :=
  CategoryTheory.hasExt_of_enoughProjectives.{w} (ModuleCat.{v} R)

open Pointwise

noncomputable def quotSMulTop_ext_equiv_ext_quotSMulTop (M : ModuleCat.{v} R) (n : ℕ)
    [HasProjectiveDimensionLE M n] (a : R) (reg : IsSMulRegular M a) (N : ModuleCat.{v} R) :
    QuotSMulTop a (Ext.{w} M N n) ≃ₗ[R] Ext (ModuleCat.of R (QuotSMulTop a M)) N (n + 1) := by
  let S := M.smulShortComplex a
  have S_exact : S.ShortExact := reg.smulShortComplex_shortExact
  let f : Ext M N n →ₗ[R] Ext (ModuleCat.of R (QuotSMulTop a M)) N (n + 1) := {
    toFun := S_exact.extClass.precomp N (add_comm 1 n)
    map_add' := by simp
    map_smul' := by simp }
  have surj : Function.Surjective f := by
    have exac := Ext.contravariant_sequence_exact₃' S_exact N n (n + 1) (add_comm 1 n)
    have : Subsingleton (Ext M N (n + 1)) :=
      HasProjectiveDimensionLT.subsingleton M (n + 1) (n + 1) (le_refl _) N
    exact (AddCommGrpCat.epi_iff_surjective _).mp
      (exac.epi_f ((@AddCommGrpCat.isZero_of_subsingleton _ this).eq_zero_of_tgt _))
  have ker : LinearMap.ker f = a • (⊤ : Submodule R _) := by
    have exac := Ext.contravariant_sequence_exact₁' S_exact N n (n + 1) (add_comm 1 n)
    have exac' : Function.Exact (a • LinearMap.id (R := R) (M := (Ext M N n))) f := by
      convert (ShortComplex.ab_exact_iff_function_exact _).mp exac
      have : S.f = a • 𝟙 _ := by
        ext
        simp [S]
      ext x
      simp [this, Ext.mk₀_smul]
    rw [LinearMap.exact_iff.mp exac']
    ext y
    simp [Submodule.mem_smul_pointwise_iff_exists]
  exact (Submodule.quotEquivOfEq _ _ ker.symm).trans (f.quotKerEquivOfSurjective surj)

noncomputable def ext_quotient_regular_sequence_length (M : ModuleCat.{v} R) [Nontrivial M]
    [Module.Finite R M] (rs : List R) (reg : IsRegular R rs) :
    (Ext.{w} (ModuleCat.of R (Shrink.{v} (R ⧸ Ideal.ofList rs))) M rs.length) ≃ₗ[R]
    M ⧸ Ideal.ofList rs • (⊤ : Submodule R M) := by
  generalize len : rs.length = n
  induction n generalizing rs
  · rw [List.length_eq_zero_iff.mp len, Ideal.ofList_nil, Submodule.bot_smul]
    let e₀ := (Shrink.linearEquiv R (R ⧸ (⊥ : Ideal R))).trans
      (AlgEquiv.quotientBot R R).toLinearEquiv
    exact ((Ext.linearEquiv₀.trans (ModuleCat.homLinearEquiv.trans (e₀.congrLeft M R))).trans
      (LinearMap.ringLmapEquivSelf R R M)).trans (Submodule.quotEquivOfEqBot ⊥ rfl).symm
  · rename_i n hn
    let a := rs[n]
    let rs' := rs.take n
    have mem_max : ∀ x ∈ rs, x ∈ maximalIdeal R := by
      intro x hx
      apply IsLocalRing.le_maximalIdeal reg.2.symm
      simpa using (Ideal.mem_span x).mpr fun p a ↦ a hx
    have mem_max' : ∀ x ∈ rs', x ∈ maximalIdeal R := fun x hx ↦ mem_max x (List.mem_of_mem_take hx)
    have rs'reg : RingTheory.Sequence.IsRegular R rs' := by
      refine ⟨⟨fun i hi ↦ ?_⟩, ?_⟩
      · simp only [List.length_take, len, le_add_iff_nonneg_right, zero_le, inf_of_le_left,
          List.getElem_take, rs'] at hi ⊢
        rw [List.take_take, min_eq_left_of_lt hi]
        exact reg.1.1 i (lt_of_lt_of_eq (Nat.lt_add_right 1 hi) len.symm)
      · simpa using (ne_top_of_le_ne_top Ideal.IsPrime.ne_top' (Ideal.span_le.mpr mem_max')).symm
    have eqapp : rs = rs' ++ [a] := by simp [rs', a, len]
    have reg' : IsSMulRegular (R ⧸ Ideal.ofList rs' • (⊤ : Submodule R R)) a :=
      reg.1.1 n (lt_of_lt_of_eq (lt_add_one n) len.symm)
    have reg'' : IsSMulRegular (ModuleCat.of R (Shrink.{v} (R ⧸ Ideal.ofList rs'))) a := by
      rw [(Shrink.linearEquiv R _).isSMulRegular_congr, ← Ideal.mul_top (Ideal.ofList rs')]
      simpa using reg'
    let e1' : QuotSMulTop a (Shrink.{v} (R ⧸ Ideal.ofList rs')) ≃ₗ[R]
      (Shrink.{v} (R ⧸ Ideal.ofList rs)) :=
      ((quotSMulTopLinearEquiv a (Shrink.linearEquiv R (R ⧸ Ideal.ofList rs'))).trans
      (Ideal.quotOfListSMulTopEquivQuotSMulTopOuter eqapp).symm).trans (Shrink.linearEquiv R _).symm
    let e1 : Ext (ModuleCat.of R (Shrink.{v} (R ⧸ Ideal.ofList rs))) M (n + 1) ≃ₗ[R]
      Ext (ModuleCat.of R (QuotSMulTop a (Shrink.{v} (R ⧸ Ideal.ofList rs')))) M (n + 1) := {
      __ := (((extFunctor.{w} (n + 1)).mapIso e1'.toModuleIso.op).app M).addCommGroupIsoToAddEquiv
      map_smul' r x := by simp [Iso.addCommGroupIsoToAddEquiv] }
    let _ : HasProjectiveDimensionLE (ModuleCat.of R (Shrink.{v} (R ⧸ Ideal.ofList rs'))) n :=
      have : projectiveDimension (ModuleCat.of R (Shrink.{v} (R ⧸ Ideal.ofList rs'))) = n := by
        simp [projectiveDimension_quotient_eq_length rs' rs'reg, rs', len]
      (projectiveDimension_le_iff _ n).mp (le_of_eq this)
    let e2 : QuotSMulTop a (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ Ideal.ofList rs'))) M n) ≃ₗ[R]
      Ext (ModuleCat.of R (QuotSMulTop a (Shrink.{v} (R ⧸ Ideal.ofList rs')))) M (n + 1) :=
      quotSMulTop_ext_equiv_ext_quotSMulTop (ModuleCat.of R (Shrink.{v} (R ⧸ Ideal.ofList rs')))
        n a reg'' M
    exact ((e1.trans e2.symm).trans
      (quotSMulTopLinearEquiv a (hn rs' rs'reg (by simp [rs', len])))).trans
      (Submodule.quotOfListSMulTopEquivQuotSMulTopOuter M eqapp).symm

omit [IsLocalRing R] in
lemma ext_subsingleton_of_support_subset (N M : ModuleCat.{v} R) [Nfin : Module.Finite R N] (n : ℕ)
    (h : support R N ⊆ {p | Subsingleton (Ext.{w} (ModuleCat.of R (Shrink.{v} (R ⧸ p.1))) M n)}) :
    Subsingleton (Ext.{w} N M n) := by
  refine (IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime
    (motive := fun L ↦ (support R L ⊆ {p | Subsingleton
      (Ext.{w} (ModuleCat.of R (Shrink.{v} (R ⧸ p.1))) M n)} →
      Subsingleton (Ext.{w} (ModuleCat.of R L) M n))) R Nfin) ?_ ?_ ?_ h
  · intro N _ _ _ sub _
    let _ : HasProjectiveDimensionLT (ModuleCat.of R N) 0 :=
      (ModuleCat.isZero_of_iff_subsingleton.mpr sub).hasProjectiveDimensionLT_zero
    exact HasProjectiveDimensionLT.subsingleton (ModuleCat.of R N) 0 n n.zero_le M
  · intro N _ _ _ p e h
    have mem : p ∈ support R N := by
      rw [e.support_eq, Module.mem_support_iff_of_finite, Ideal.annihilator_quotient]
    let e' : ModuleCat.of R N ≅ ModuleCat.of R (Shrink.{v, u} (R ⧸ p.asIdeal)) :=
      (e.trans (Shrink.linearEquiv R _).symm).toModuleIso
    have := (((extFunctor.{w} n).mapIso e'.op).app M).addCommGroupIsoToAddEquiv.subsingleton_congr
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

lemma ext_subsingleton_of_all_gt (M : ModuleCat.{v} R) [Module.Finite R M] (n : ℕ)
    (p : Ideal R) [p.IsPrime] (ne : p ≠ maximalIdeal R) (h : ∀ q > p, q.IsPrime →
      Subsingleton (Ext.{w} (ModuleCat.of R (Shrink.{v} (R ⧸ q))) M (n + 1))) :
    Subsingleton (Ext.{w} (ModuleCat.of R (Shrink.{v} (R ⧸ p))) M n) := by
  have plt : p < maximalIdeal R :=  lt_of_le_of_ne (le_maximalIdeal_of_isPrime p) ne
  obtain ⟨x, hx, nmem⟩ : ∃ x ∈ maximalIdeal R, x ∉ p := Set.exists_of_ssubset plt
  let _ : Small.{v} (QuotSMulTop x (R ⧸ p)) :=
    small_of_surjective (Submodule.Quotient.mk_surjective _)
  let fin : Module.Finite R (Shrink.{v, u} (R ⧸ p)) :=
    Module.Finite.equiv (Shrink.linearEquiv R _).symm
  let _ : Nontrivial (QuotSMulTop x (Shrink.{v, u} (R ⧸ p))) :=
    quotSMulTop_nontrivial hx _
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
    rw [(Shrink.linearEquiv R _).isSMulRegular_congr, isSMulRegular_iff_right_eq_zero_of_smul]
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
    (h : ∀ i ≥ n, Subsingleton (Ext.{w} (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R))) M i)) :
    ∀ i ≥ n, ∀ N : ModuleCat.{v} R, Subsingleton (Ext.{w} N M i) := by
  intro i hi N
  apply ext_subsingleton_of_quotients
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
          rw [← WithBot.add_le_add_right_iff _ _ 1]
          apply le_trans _ hp
          obtain ⟨r, hrq, hrp⟩ := Set.exists_of_ssubset hqp
          apply ringKrullDim_succ_le_of_surjective (r := Ideal.Quotient.mk p.1 r)
            (Ideal.Quotient.factor hqp.le) (Ideal.Quotient.factor_surjective hqp.le)
          · simpa [Ideal.Quotient.eq_zero_iff_mem] using hrp
          · simpa [Ideal.Quotient.eq_zero_iff_mem] using hrq
        apply ih (i + 1) (Nat.le_add_right_of_le hi) this
  rcases exist_nat_eq' R with ⟨n, hn⟩
  apply this n
  simpa [← hn] using ringKrullDim_quotient_le p.1

lemma injectiveDimension_eq_sInf (M : ModuleCat.{v} R) [Module.Finite R M] :
    injectiveDimension M = sInf {n : WithBot ℕ∞ | ∀ (i : ℕ), n < i →
      Subsingleton (Ext.{w} (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R))) M i)} := by
  simp only [injectiveDimension]
  congr! 3
  rename_i n
  refine ⟨fun h i hi ↦ ?_, fun h i hi ↦ ?_⟩
  · let _ := h i hi
    exact HasInjectiveDimensionLT.subsingleton M i i (le_refl i) _
  · rw [hasInjectiveDimensionLT_iff]
    intro j hj N e
    apply @Subsingleton.eq_zero _ _ ?_ e
    apply ext_vanish_of_residueField_vanish M i _ j hj N
    intro k hk
    exact h k (lt_of_lt_of_le hi (Nat.cast_le.mpr hk))

end

section injdim

omit [IsLocalRing R] [IsNoetherianRing R] in
lemma nontrivial_of_islocalizedModule {S : Submonoid R} {M MS : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup MS] [Module R MS] {f : M →ₗ[R] MS} (isl : IsLocalizedModule S f)
    (h : Nontrivial MS) : Nontrivial M := by
  by_contra!
  absurd h
  exact not_nontrivial_iff_subsingleton.mpr
    (IsLocalizedModule.linearEquiv S f (LocalizedModule.mkLinearMap S M)).subsingleton

section

omit [IsLocalRing R]

omit [IsNoetherianRing R] in
noncomputable def isLocalization_map_of_disjoint_map (S : Submonoid R) (A : Type*) [CommRing A]
    [Algebra R A] [IsLocalization S A] (p : Ideal A) [p.IsPrime] {M : Type*} [AddCommGroup M]
    [Module R M] {MS : Type*} [AddCommGroup MS] [Module R MS] (f : M →ₗ[R] MS)
    [IsLocalizedModule S f] [Module A MS] [IsScalarTower R A MS] {Mp : Type*} [AddCommGroup Mp]
    [Module R Mp] (g : M →ₗ[R] Mp) [IsLocalizedModule.AtPrime (p.comap (algebraMap R A)) g]
    [Module A Mp] [IsScalarTower R A Mp] : MS →ₗ[A] Mp :=
  have (s : S) : IsUnit ((algebraMap R (Module.End R Mp)) s.1) :=
    have : s.1 ∈ (p.comap (algebraMap R A)).primeCompl :=
      ((IsLocalization.disjoint_comap_iff S A p).mpr Ideal.IsPrime.ne_top').le_compl_right s.2
    IsLocalizedModule.map_units g ⟨s.1, this⟩
  (IsLocalizedModule.lift S f g this).extendScalarsOfIsLocalization S A

omit [IsNoetherianRing R] in
lemma isLocalization_map_of_disjoint (S : Submonoid R) (A : Type*) [CommRing A] [Algebra R A]
    [IsLocalization S A] (p : Ideal A) [p.IsPrime] {M : Type*} [AddCommGroup M] [Module R M]
    {MS : Type*} [AddCommGroup MS] [Module R MS] (f : M →ₗ[R] MS) [IsLocalizedModule S f]
    [Module A MS] [IsScalarTower R A MS] {Mp : Type*} [AddCommGroup Mp] [Module R Mp]
    (g : M →ₗ[R] Mp) [IsLocalizedModule.AtPrime (p.comap (algebraMap R A)) g]
    [Module A Mp] [IsScalarTower R A Mp] :
    IsLocalizedModule.AtPrime p (isLocalization_map_of_disjoint_map S A p f g) where
  map_units x := by
    rcases IsLocalization.mk'_surjective S x.1 with ⟨r, s, hrs⟩
    rw [← hrs, IsLocalization.mk'_eq_mul_mk'_one, map_mul, ← IsScalarTower.algebraMap_apply]
    apply IsUnit.mul _ ((isUnit_of_invertible (IsLocalization.mk' A 1 s)).map _)
    have nmem : r ∈ (p.comap (algebraMap R A)).primeCompl := by
      by_contra mem
      simp only [Ideal.mem_primeCompl_iff, Ideal.mem_comap, not_not,
        ← IsLocalization.mk'_mem_iff (y := s), hrs] at mem
      exact x.2 mem
    rcases (IsLocalizedModule.map_units g ⟨r, nmem⟩).exists_right_inv with ⟨r', hr'⟩
    rw [isUnit_iff_exists]
    use r'.extendScalarsOfIsLocalization S A
    constructor
    · ext y
      simpa using LinearMap.congr_fun hr' y
    · ext y
      simpa using LinearMap.congr_fun hr' y
  surj y := by
    rcases IsLocalizedModule.surj (p.comap (algebraMap R A)).primeCompl g y with ⟨⟨m, r⟩, hmr⟩
    have mem : (algebraMap R A) r ∈ p.primeCompl := by
      simpa [← Ideal.mem_comap] using Ideal.mem_primeCompl_iff.mp r.2
    use ⟨f m, ⟨(algebraMap R A) r, mem⟩⟩
    simpa [isLocalization_map_of_disjoint_map] using hmr
  exists_of_eq {z1 z2} eq := by
    rcases IsLocalizedModule.surj S f z1 with ⟨⟨m1, r1⟩, hmr1⟩
    rcases IsLocalizedModule.surj S f z2 with ⟨⟨m2, r2⟩, hmr2⟩
    have eq' : (isLocalization_map_of_disjoint_map S A p f g) (r2 • r1 • z1) =
      (isLocalization_map_of_disjoint_map S A p f g) (r1 • r2 • z2) := by
      simp [smul_smul, mul_comm r1 r2, eq]
    simp only [isLocalization_map_of_disjoint_map, hmr1, LinearMap.map_smul_of_tower,
      LinearMap.extendScalarsOfIsLocalization_apply', IsLocalizedModule.lift_apply, hmr2] at eq'
    rw [← LinearMap.map_smul_of_tower, ← LinearMap.map_smul_of_tower] at eq'
    rcases IsLocalizedModule.exists_of_eq (S := (p.comap (algebraMap R A)).primeCompl) eq' with
      ⟨r3, hr3⟩
    have : (algebraMap R A) (r3 * (r2 * r1).1) ∈ p.primeCompl := by
      rw [map_mul]
      apply mul_mem
      · simpa [← Ideal.mem_comap] using Ideal.mem_primeCompl_iff.mp r3.2
      · simp only [Ideal.mem_primeCompl_iff]
        by_contra mem
        absurd Ideal.eq_top_of_isUnit_mem _ mem (IsLocalization.map_units A (r2 * r1))
        exact Ideal.IsPrime.ne_top'
    use ⟨(algebraMap R A) (r3 * (r2 * r1)), this⟩
    simp only [map_mul, Submonoid.mk_smul]
    nth_rw 2 [mul_comm ((algebraMap R A) r2)]
    simp only [← smul_smul, algebraMap_smul]
    change r3.1 • r2.1 • r1 • z1 = r3.1 • r1.1 • r2 • z2
    rw [hmr1, hmr2, ← map_smul, ← map_smul, ← map_smul, ← map_smul]
    exact LinearMap.congr_arg hr3

universe w

variable [Small.{v} R] [UnivLE.{v, w}]

instance (S : Submonoid R) : Small.{v} (Localization S) :=
  small_of_surjective Localization.mkHom_surjective

instance (p : Ideal R) [p.IsPrime] : Small.{v} p.ResidueField :=
  small_of_surjective Ideal.Quotient.mk_surjective

noncomputable local instance [Small.{v} R] (M : ModuleCat.{v} R) (S : Submonoid R) :
    Module R (M.localizedModule S) :=
  inferInstanceAs (Module R (Shrink.{v} (LocalizedModule S M)))

set_option maxHeartbeats 250000 in
--the application of base change is too complicated
lemma ext_succ_nontrivial_of_eq_of_le (M : ModuleCat.{v} R) [Module.Finite R M] [Nontrivial M]
    {p q : PrimeSpectrum R} (lt : p < q) (eq_of_le : ∀ r : PrimeSpectrum R, p < r → r ≤ q → r = q)
    (i : ℕ) (ntr : Nontrivial (Ext.{w} (ModuleCat.of (Localization p.1.primeCompl)
      (Shrink.{v} p.1.ResidueField)) (M.localizedModule p.1.primeCompl) i)) :
    Nontrivial (Ext.{w} (ModuleCat.of (Localization q.1.primeCompl)
      (Shrink.{v} q.1.ResidueField)) (M.localizedModule q.1.primeCompl) (i + 1)) := by
  by_contra! sub
  let _ : Module.Finite (Localization q.1.primeCompl) (M.localizedModule q.1.primeCompl) :=
    Module.Finite.equiv (Shrink.linearEquiv (Localization q.1.primeCompl) _).symm
  let f := (algebraMap R (Localization q.1.primeCompl))
  let Rq := (Localization q.1.primeCompl)
  let Rp := (Localization p.1.primeCompl)
  have disj : Disjoint (q.1.primeCompl : Set R) p.asIdeal := by
    rw [← le_compl_iff_disjoint_left]
    intro r hr
    simpa using le_of_lt lt hr
  let _ : (p.1.map f).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint q.1.primeCompl _ _ p.2 disj
  have ne : p.1.map f ≠ maximalIdeal (Localization q.1.primeCompl) := by
    by_contra eq
    absurd ne_of_lt lt
    rw [PrimeSpectrum.ext_iff, ← IsLocalization.comap_map_of_isPrime_disjoint q.1.primeCompl Rq
      p.1 p.2 disj, eq, Localization.AtPrime.comap_maximalIdeal]
  have sub' : Subsingleton (Ext (ModuleCat.of (Localization q.1.primeCompl) (Shrink.{v}
    (Localization q.1.primeCompl ⧸ (p.1.map f)))) (M.localizedModule q.1.primeCompl) i) := by
    apply ext_subsingleton_of_all_gt (M.localizedModule q.1.primeCompl) i (p.1.map f) ne
    intro r rgt hr
    have cgt : r.comap f > p.1 := by
      rw [← IsLocalization.comap_map_of_isPrime_disjoint q.1.primeCompl
        (Localization q.1.primeCompl) p.1 p.2 disj]
      apply lt_of_le_of_ne (Ideal.comap_mono (le_of_lt rgt))
      apply ne_of_apply_ne (Ideal.map f)
      rw [IsLocalization.map_comap q.1.primeCompl, IsLocalization.map_comap q.1.primeCompl]
      exact ne_of_lt rgt
    have cle : r.comap f ≤ q.1 := le_of_le_of_eq (Ideal.comap_mono (le_maximalIdeal_of_isPrime r))
        (IsLocalization.AtPrime.comap_maximalIdeal (Localization q.1.primeCompl) q.1)
    have ceq : r.comap f = q.1 := by simp [← eq_of_le ⟨r.comap f, r.comap_isPrime f⟩ cgt cle]
    rw [← IsLocalization.map_comap q.1.primeCompl _ r, ceq,
      Localization.AtPrime.map_eq_maximalIdeal]
    exact sub
  have le' : q.1.primeCompl ≤ p.1.primeCompl := by simpa [Ideal.primeCompl] using le_of_lt lt
  let _ : Algebra Rq Rp := IsLocalization.localizationAlgebraOfSubmonoidLe Rq Rp _ _ le'
  let _ := IsLocalization.localization_isScalarTower_of_submonoid_le Rq Rp _ _ le'
  have isl0 : IsLocalization.AtPrime Rp (p.1.map f) := by
    have : IsLocalization.AtPrime (Localization.AtPrime (p.1.map f)) p.1 := by
      convert IsLocalization.isLocalization_atPrime_localization_atPrime q.1.primeCompl (p.1.map f)
      rw [IsLocalization.comap_map_of_isPrime_disjoint q.1.primeCompl Rq p.1 p.2 disj]
    let e := IsLocalization.algEquiv p.1.primeCompl Rp (Localization.AtPrime (p.1.map f))
    exact IsLocalization.isLocalization_of_algEquiv (p.1.map f).primeCompl (AlgEquiv.ofLinearEquiv
      (e.toLinearEquiv.extendScalarsOfIsLocalization q.1.primeCompl Rq) (by simp) (by simp)).symm
  let _ : IsLocalizedModule.AtPrime (p.1.map f) (Algebra.linearMap Rq Rp) :=
    (isLocalizedModule_iff_isLocalization' _ _).mpr isl0
  let _ : IsScalarTower Rq Rp (Shrink.{v, u} p.asIdeal.ResidueField) :=
    Equiv.isScalarTower Rq Rp (equivShrink p.asIdeal.ResidueField).symm
  let f1' := Submodule.toLocalizedQuotient' Rp (p.1.map f).primeCompl (Algebra.linearMap Rq Rp)
    (p.1.map f)
  have eqm : Submodule.localized' Rp (p.1.map f).primeCompl (Algebra.linearMap Rq Rp)
    (p.1.map f) = maximalIdeal Rp := by
    rw [Ideal.localized'_eq_map, Ideal.map_map, ← IsScalarTower.algebraMap_eq,
      Localization.AtPrime.map_eq_maximalIdeal]
  let e := ((Submodule.quotEquivOfEq _ _ eqm).restrictScalars Rq).trans
    (Shrink.linearEquiv.{v} Rq _).symm
  let f1 : (ModuleCat.of Rq (Shrink.{v} (Rq ⧸ p.1.map f))) →ₗ[Rq]
      (ModuleCat.of Rp (Shrink.{v} p.1.ResidueField)) :=
      e.toLinearMap.comp (f1'.comp (Shrink.linearEquiv.{v} Rq _).toLinearMap)
  have isl1 : IsLocalizedModule (p.1.map f).primeCompl f1 :=
    let _ := IsLocalizedModule.of_linearEquiv_right (p.1.map f).primeCompl f1'
      (Shrink.linearEquiv.{v} Rq _)
    IsLocalizedModule.of_linearEquiv (p.1.map f).primeCompl
      (f1'.comp (Shrink.linearEquiv.{v} Rq _).toLinearMap) e
  let _ : Module Rq (M.localizedModule p.1.primeCompl) :=
    ModuleCat.Algebra.instModuleCarrier
  let _ : IsScalarTower Rq Rp (M.localizedModule p.asIdeal.primeCompl) :=
    ModuleCat.Algebra.instIsScalarTowerCarrier
  let _ : IsLocalizedModule.AtPrime ((p.1.map f).comap f)
    (M.localizedModule_mkLinearMap p.1.primeCompl) := by
    convert M.localizedModule_isLocalizedModule p.1.primeCompl
    exact IsLocalization.comap_map_of_isPrime_disjoint q.1.primeCompl Rq p.1 p.2 disj
  let _ : IsScalarTower R Rq (M.localizedModule p.1.primeCompl) := {
    smul_assoc r s z := by
      nth_rw 2 [← algebraMap_smul Rp r]
      rw [← algebraMap_smul Rp s, smul_smul, Algebra.smul_def, ← algebraMap_smul Rp, map_mul,
        ← IsScalarTower.algebraMap_apply] }
  let f2 : (M.localizedModule q.1.primeCompl) →ₗ[Rq] (M.localizedModule p.asIdeal.primeCompl) :=
    isLocalization_map_of_disjoint_map q.1.primeCompl Rq (p.1.map f)
    (M.localizedModule_mkLinearMap q.1.primeCompl) (M.localizedModule_mkLinearMap p.1.primeCompl)
  have isl2 : IsLocalizedModule (p.1.map f).primeCompl f2 :=
    isLocalization_map_of_disjoint q.1.primeCompl Rq (p.1.map f)
    (M.localizedModule_mkLinearMap q.1.primeCompl) (M.localizedModule_mkLinearMap p.1.primeCompl)
  let _ : Module.Finite Rq (Shrink.{v} (Rq ⧸ Ideal.map f p.asIdeal)) :=
    Module.Finite.equiv (Shrink.linearEquiv Rq _).symm
  have isl := Ext.isLocalizedModule'.{v, v, u, u, w, w} (p.1.map f).primeCompl Rp f1 isl1 f2 isl2 i
  absurd nontrivial_of_islocalizedModule isl ntr
  exact not_nontrivial_iff_subsingleton.mpr sub'

end

variable [Small.{v} R]

section

open ModuleCat.Algebra

--set_option pp.universes true in
open associatedPrimes in
lemma supportDim_le_injectiveDimension (M : ModuleCat.{v} R) [Module.Finite R M] [Nontrivial M] :
    supportDim R M ≤ injectiveDimension M := by
  obtain ⟨q, hq⟩ : ∃ q : LTSeries (Module.support R M), q.length = supportDim R M := by
    have (n : ℕ) : (n : WithBot ℕ∞) = (n : ℕ∞) := rfl
    simp only [this, supportDim, Order.krullDim_eq_iSup_length, WithBot.coe_inj]
    apply ENat.exists_eq_iSup_of_lt_top
    rw [← WithBot.coe_lt_coe, ← Order.krullDim_eq_iSup_length, WithBot.coe_top, lt_top_iff_ne_top]
    apply ne_top_of_le_ne_top ringKrullDim_ne_top (Module.supportDim_le_ringKrullDim R M)
  have eq_of_le (i : Fin q.length) :
    ∀ r : PrimeSpectrum R, q i.castSucc < r → r ≤ q i.succ → r = q i.succ := by
    intro r ltr rle
    by_contra ne
    let q' := q.insertNth i ⟨r, Module.mem_support_mono (le_of_lt ltr) (q i.castSucc).2⟩ ltr
      (lt_of_le_of_ne rle ne)
    have : q'.length > q.length := by simp [q']
    absurd this
    simp only [gt_iff_lt, not_lt, ← Nat.cast_le (α := WithBot ℕ∞),
      hq, supportDim, Order.krullDim]
    exact le_iSup_iff.mpr fun b a ↦ a q'
  have tail_eq : (q ⟨q.length, lt_add_one q.length⟩).1.1 = maximalIdeal R := by
    by_contra! ne
    let _ := (q ⟨q.length, lt_add_one q.length⟩).1.2
    have lt := ne.lt_of_le (IsLocalRing.le_maximalIdeal_of_isPrime _)
    let q' := q.snoc ⟨IsLocalRing.closedPoint R, closedPoint_mem_support R M⟩ lt
    have : q'.length > q.length := by simp [q']
    absurd this
    simp only [gt_iff_lt, not_lt, ← Nat.cast_le (α := WithBot ℕ∞),
      hq, supportDim, Order.krullDim]
    exact le_iSup_iff.mpr fun b a ↦ a q'
  have head_min : (q 0).1.1 ∈ (Module.annihilator R M).minimalPrimes := by
    rcases Ideal.exists_minimalPrimes_le (annihilator_le_of_mem_support (q 0).2) with ⟨p, min, ple⟩
    rcases lt_or_eq_of_le ple with lt|eq
    · have pp : p.IsPrime := Ideal.minimalPrimes_isPrime min
      have : ⟨p, pp⟩ ∈ Module.support R M := by
        simpa [Module.mem_support_iff_of_finite] using min.1.2
      let q' := q.cons ⟨⟨p, pp⟩, this⟩ lt
      have : q'.length > q.length := by simp [q']
      absurd this
      simp only [gt_iff_lt, not_lt, ← Nat.cast_le (α := WithBot ℕ∞),
        hq, supportDim, Order.krullDim]
      exact le_iSup_iff.mpr fun b a ↦ a q'
    · simpa [← eq] using min
  have lem' (i : ℕ) (h : i ≤ q.length) : Nontrivial (Ext.{v}
    (ModuleCat.of (Localization (q.toFun ⟨i, Nat.lt_succ.mpr h⟩).1.1.primeCompl)
      (Shrink.{v, u} (q.toFun ⟨i, Nat.lt_succ.mpr h⟩).1.1.ResidueField))
    (M.localizedModule (q.toFun ⟨i, Nat.lt_succ.mpr h⟩).1.1.primeCompl) i) := by
    induction i
    · simp only [Fin.zero_eta, Ext.homEquiv₀.nontrivial_congr, ModuleCat.localizedModule]
      rw [ModuleCat.homAddEquiv.nontrivial_congr, ((Shrink.linearEquiv.{v} _ _).congrLeft _
        (Localization (q 0).1.1.primeCompl)).nontrivial_congr,
        (Shrink.linearEquiv.{v} _ _).congrRight.nontrivial_congr]
      have ass := minimalPrimes_annihilator_subset_associatedPrimes R M head_min
      simp only [AssociatePrimes.mem_iff] at ass
      have := mem_associatePrimes_localizedModule_atPrime_of_mem_associatedPrimes ass
      simp only [AssociatePrimes.mem_iff, isAssociatedPrime_iff_exists_injective_linearMap] at this
      rcases this with ⟨_, f, hf⟩
      exact nontrivial_of_ne f 0  (LinearMap.ne_zero_of_injective hf)
    · rename_i i ih
      exact ext_succ_nontrivial_of_eq_of_le.{v, u, v} M (q.step ⟨i, h⟩) (eq_of_le ⟨i, h⟩) i
        (ih (Nat.le_of_succ_le h))
  have ntr : Nontrivial (Ext.{v} (ModuleCat.of R (Shrink.{v, u} (R ⧸ maximalIdeal R))) M
    q.length) := by
    let qq := q ⟨q.length, Nat.lt_succ.mpr (le_refl q.length)⟩
    have qqeq : qq.1.1 = maximalIdeal R := tail_eq
    have ntr' : Nontrivial (Ext.{v} (ModuleCat.of (Localization qq.1.1.primeCompl)
      (Shrink.{v, u} qq.1.1.ResidueField)) (M.localizedModule qq.1.1.primeCompl) q.length) :=
      lem' q.length (le_refl _)
    let _ : Module.Finite R (Shrink.{v} (R ⧸ maximalIdeal R)) :=
      Module.Finite.equiv (Shrink.linearEquiv.{v} R (R ⧸ maximalIdeal R)).symm
    let _ : IsScalarTower R (Localization qq.1.1.primeCompl) (Shrink.{v} qq.1.1.ResidueField) :=
      Equiv.isScalarTower R (Localization qq.1.1.primeCompl) (equivShrink qq.1.1.ResidueField).symm
    let _ : IsLocalization qq.1.1.primeCompl R :=
      IsLocalization.at_units _ (fun x hx ↦ by simpa [qqeq] using hx)
    have surj : Function.Surjective (algebraMap R (Localization qq.1.1.primeCompl)) :=
      (IsLocalization.bijective qq.1.1.primeCompl
        (algebraMap R (Localization qq.1.1.primeCompl)) rfl).2
    let _ : IsLocalHom (algebraMap R (Localization qq.1.1.primeCompl)) :=
      IsLocalHom.of_surjective _ surj
    let e' : (R ⧸ maximalIdeal R) →ₗ[R] qq.1.1.ResidueField :=
      { __ := ResidueField.map (algebraMap R (Localization qq.1.1.primeCompl))
        map_smul' r x := by
          simp only [RingHom.toMonoidHom_eq_coe, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
            OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe, map_mul,
            RingHom.id_apply, mul_eq_mul_right_iff, map_eq_zero]
          left
          rw [IsScalarTower.algebraMap_eq R (Localization qq.1.1.primeCompl) qq.1.1.ResidueField,
            ResidueField.algebraMap_eq, ← ResidueField.map_comp_residue]
          rfl }
    have bij : Function.Bijective e' :=
      ResidueField.map_bijective_of_surjective _ surj
    let e : (R ⧸ maximalIdeal R) ≃ₗ[R] qq.1.1.ResidueField :=
      LinearEquiv.ofBijective e' bij
    let f : ModuleCat.of R (Shrink.{v, u} (R ⧸ maximalIdeal R)) ≃ₗ[R]
      (ModuleCat.of (Localization qq.1.1.primeCompl) (Shrink.{v, u} qq.1.1.ResidueField)) :=
      ((Shrink.linearEquiv R (R ⧸ maximalIdeal R)).trans e).trans
        (Shrink.linearEquiv R qq.1.1.ResidueField).symm
    have isl1 : IsLocalizedModule qq.1.1.primeCompl f.toLinearMap := by
      let _ := isLocalizedModule_id qq.1.1.primeCompl (Shrink.{v, u} (R ⧸ maximalIdeal R)) R
      exact IsLocalizedModule.of_linearEquiv qq.1.1.primeCompl LinearMap.id f
    have isl := Ext.isLocalizedModule'.{v, v, u, u, v, v} qq.1.1.primeCompl
      (Localization qq.1.1.primeCompl) f.toLinearMap isl1
      (M.localizedModule_mkLinearMap qq.1.1.primeCompl)
      (M.localizedModule_isLocalizedModule qq.1.1.primeCompl) q.length
    exact nontrivial_of_islocalizedModule isl ntr'
  simp only [← hq, injectiveDimension_eq_sInf.{v, u, v} M, le_sInf_iff, Set.mem_setOf_eq]
  intro b hb
  by_contra! lt
  exact (not_subsingleton_iff_nontrivial.mpr ntr) (hb q.length lt)

end

open Limits in
lemma injectiveDimension_eq_depth
    (M : ModuleCat.{v} R) (h : injectiveDimension M ≠ ⊤) [Module.Finite R M] [Nontrivial M] :
    injectiveDimension M = IsLocalRing.depth (ModuleCat.of R (Shrink.{v} R)) := by
  let := Module.Finite.equiv (Shrink.linearEquiv R R).symm
  have lttop := depth_ne_top (ModuleCat.of R (Shrink.{v} R))
  rw [IsLocalRing.depth_eq_sSup_length_regular (ModuleCat.of R (Shrink.{v} R))] at lttop ⊢
  obtain ⟨rs, reg', mem, len⟩ := @ENat.sSup_mem_of_nonempty_of_lt_top _ (by
    use 0, []
    simpa using IsRegular.nil _ _) lttop.symm.lt_top'
  rw [← len]
  have reg : IsRegular R rs := ((Shrink.linearEquiv.{v} R R).isRegular_congr rs).mp reg'
  apply le_antisymm
  · obtain ⟨r, hr⟩ : ∃ n : ℕ, injectiveDimension M = n := by
      generalize hd : injectiveDimension M = d
      induction d with
      | bot =>
        absurd not_nontrivial_iff_subsingleton.mpr
          (ModuleCat.isZero_iff_subsingleton.mp ((injectiveDimension_eq_bot_iff M).mp hd))
        assumption
      | coe d =>
        induction d with
        | top => simp [hd] at h
        | coe d =>
          use d
          rfl
    rw [hr]
    apply Nat.cast_le.mpr
    have projdim : projectiveDimension (ModuleCat.of R
      ((Shrink.{v} R) ⧸ Ideal.ofList rs • (⊤ : Submodule R (Shrink.{v} R)))) = rs.length := by
      let _ : Module.Free R (Shrink.{v} R) := Module.Free.of_equiv (Shrink.linearEquiv R R).symm
      have : projectiveDimension (ModuleCat.of R (Shrink.{v} R)) = 0 := by
        apply le_antisymm
        · apply (projectiveDimension_le_iff _ 0).mpr
          simpa [HasProjectiveDimensionLE, ← projective_iff_hasProjectiveDimensionLT_one]
            using ModuleCat.projective_of_categoryTheory_projective _
        · have : projectiveDimension (ModuleCat.of R (Shrink.{v, u} R)) ≠ ⊥ := by
            simpa [projectiveDimension_eq_bot_iff] using not_subsingleton (Shrink.{v, u} R)
          rw [← WithBot.coe_unbot _ this, ← WithBot.coe_zero, WithBot.coe_le_coe]
          exact zero_le _
      simp [projectiveDimension_quotient_regular_sequence (ModuleCat.of R (Shrink.{v} R)) rs
        reg'.1 mem, this]
    have ntr : Nontrivial (Ext.{v} (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R))) M r) := by
      by_contra! sub
      have (i : ℕ) (lt : r < i) :
        Subsingleton (Ext.{v} (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R))) M i) := by
        let _ := (injectiveDimension_le_iff _ r).mp (le_of_eq hr)
        exact HasInjectiveDimensionLT.subsingleton M (r + 1) i lt _
      let _ := (injectiveDimension_le_iff _ r).mp (le_of_eq hr)
      match r with
      | 0 =>
        have : injectiveDimension M ≤ ⊥ := by
          rw [injectiveDimension_eq_sInf.{v, u, v} M]
          apply sInf_le
          intro i _
          match i with
          | 0 => exact sub
          | i + 1 => exact this (i + 1) (Nat.zero_lt_succ i)
        simp [hr] at this
      | s + 1 =>
        have : injectiveDimension M ≤ s := by
          rw [injectiveDimension_eq_sInf.{v, u, v} M]
          apply sInf_le
          intro i hi
          have le : s + 1 ≤ i := Nat.cast_lt.mp hi
          rcases eq_or_lt_of_le le with eq|lt
          · simpa [← eq] using sub
          · exact this i lt
        rw [hr, Nat.cast_le] at this
        simp at this
    by_contra! lt
    let _ := projectiveDimension_lt_iff.mp (lt_of_eq_of_lt projdim (Nat.cast_lt.mpr lt))
    have sub := HasProjectiveDimensionLT.subsingleton.{v} (ModuleCat.of R
      ((Shrink.{v} R) ⧸ Ideal.ofList rs • (⊤ : Submodule R (Shrink.{v} R)))) r r (le_refl r) M
    absurd not_nontrivial_iff_subsingleton.mpr sub
    have depth_zero : IsLocalRing.depth (ModuleCat.of R
      ((Shrink.{v} R) ⧸ Ideal.ofList rs • (⊤ : Submodule R (Shrink.{v} R)))) = 0 := by
      have := depth_quotient_regular_sequence_add_length_eq_depth (ModuleCat.of R (Shrink.{v} R))
        rs reg'
      rw [IsLocalRing.depth_eq_sSup_length_regular (ModuleCat.of R (Shrink.{v} R)), ← len] at this
      nth_rw 2 [← zero_add (rs.length : ℕ∞)] at this
      exact (ENat.add_right_cancel_iff _ _ _ (ENat.coe_ne_top rs.length)).mp this
    have := (moduleDepth_eq_zero_of_hom_nontrivial _ _).mp depth_zero
    rcases (nontrivial_iff_exists_ne 0).mp this with ⟨f, hf⟩
    have injf : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro x hx
      by_contra ne
      absurd hf
      ext y
      let e := Shrink.algEquiv R (R ⧸ maximalIdeal R)
      let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field (maximalIdeal R)
      calc
      _ = f (e.symm (e y * (e x)⁻¹ * (e x))) := by
        simp [AddEquivClass.map_ne_zero_iff.mpr ne]
      _ = _ := by
        rcases Ideal.Quotient.mk_surjective (e y * (e x)⁻¹) with ⟨r, hr⟩
        rw [← hr, ← Ideal.Quotient.algebraMap_eq, ← Algebra.smul_def]
        simp [LinearMap.mem_ker.mp hx]
    let g : ModuleCat.of R (Shrink.{v, u} (R ⧸ maximalIdeal R)) ⟶
      ModuleCat.of R (Shrink.{v, u} R ⧸ Ideal.ofList rs • (⊤ : Submodule R (Shrink.{v} R))) :=
      ModuleCat.ofHom f
    let S := ShortComplex.mk g (cokernel.π g) (cokernel.condition g)
    have S_exact : S.ShortExact := {
      exact := ShortComplex.exact_cokernel g
      mono_f := (ModuleCat.mono_iff_injective g).mpr injf
      epi_g := coequalizer.π_epi}
    have exac := Ext.contravariant_sequence_exact₁'.{v} S_exact M r (r + 1) (add_comm 1 r)
    have : IsZero (AddCommGrpCat.of (Ext.{v} S.X₃ M (r + 1))) := by
      apply @AddCommGrpCat.isZero_of_subsingleton _ ?_
      let _ := (injectiveDimension_le_iff M r).mp (le_of_eq hr)
      exact HasInjectiveDimensionLT.subsingleton M (r + 1) (r + 1) (le_refl _) _
    have surj : Function.Surjective ((Ext.mk₀.{v} S.f).precomp M (zero_add r)) :=
      (AddCommGrpCat.epi_iff_surjective _).mp (exac.epi_f (this.eq_zero_of_tgt _))
    exact surj.nontrivial
  · simp only [injectiveDimension, le_sInf_iff, Set.mem_setOf_eq]
    intro b hb
    by_contra! lt
    let _ := hb rs.length lt
    absurd HasInjectiveDimensionLT.subsingleton.{v} M rs.length rs.length (le_refl _)
      (ModuleCat.of R (Shrink.{v, u} (R ⧸ Ideal.ofList rs)))
    apply not_subsingleton_iff_nontrivial.mpr
    rw [(ext_quotient_regular_sequence_length.{v, u, v} M rs reg).nontrivial_congr]
    apply Submodule.Quotient.nontrivial_of_lt_top _ (lt_top_iff_ne_top.mpr _)
    apply (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator _).symm
    exact le_trans (Ideal.span_le.mpr mem) (maximalIdeal_le_jacobson _)

end injdim

variable (R)

class IsGorensteinLocalRing : Prop extends IsLocalRing R, IsNoetherianRing R where
  injdim : injectiveDimension (ModuleCat.of R R) ≠ ⊤

lemma isGorensteinLocalRing_def :
    IsGorensteinLocalRing R ↔ injectiveDimension (ModuleCat.of R R) ≠ ⊤ :=
  ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩

theorem isCohenMacaulayLocalRing_of_isGorensteinLocalRing [IsGorensteinLocalRing R] :
    IsCohenMacaulayLocalRing R := by
  have := (isGorensteinLocalRing_def R).mp ‹_›
  have eq := injectiveDimension_eq_depth (ModuleCat.of R R) this
  have le := supportDim_le_injectiveDimension (ModuleCat.of R R)
  rw [Module.supportDim_self_eq_ringKrullDim, eq] at le
  apply isCohenMacaulayLocalRing_of_ringKrullDim_le_depth R (le_of_le_of_eq le _)
  simp [IsLocalRing.depth_eq_of_iso (Shrink.linearEquiv.{u} R R).toModuleIso]


/-
variable {R} in
class Ideal.isIrreducible (I : Ideal R) : Prop where
  irr : ∀ {J₁ J₂ : Ideal R}, J₁ ⊓ J₂ = I → (J₁ = I ∨ J₂ = I)

local instance hasExt_self : CategoryTheory.HasExt.{u} (ModuleCat.{u} R) :=
  CategoryTheory.hasExt_of_enoughProjectives.{u} (ModuleCat.{u} R)

variable [IsLocalRing R] [IsNoetherianRing R]

lemma injectiveDimension_self_eq_ringKrullDim_of_ne_top
    (h : injectiveDimension (ModuleCat.of R R) ≠ ⊤) :
    injectiveDimension (ModuleCat.of R R) = ringKrullDim R := by
  sorry

lemma ext_subsingleton_or_isPrincipal_of_injectiveDimension_eq_ringKrullDim (n : ℕ)
    (h : injectiveDimension (ModuleCat.of R R) = ringKrullDim R) (h : ringKrullDim R = n) :
    (∀ i ≠ n, Subsingleton (Ext.{u} (ModuleCat.of R (R ⧸ maximalIdeal R)) (ModuleCat.of R R) i)) ∧
     (⊤ : Submodule R (Ext.{u} (ModuleCat.of R (R ⧸ maximalIdeal R)) (ModuleCat.of R R)
      n)).IsPrincipal := by
  sorry

lemma isGorensteinLocalRing_of_exist_ext_vanish (n : ℕ) (h : ringKrullDim R = n) (h : ∃ i > n,
    Subsingleton (Ext (ModuleCat.of R (R ⧸ maximalIdeal R)) (ModuleCat.of R R) i)) :
    IsGorensteinLocalRing R := by
  sorry

theorem isGroensteinLocalRing_tfae (n : ℕ) (h : ringKrullDim R = n) :
    [IsGorensteinLocalRing R, injectiveDimension (ModuleCat.of R R) = n,
     (∀ i ≠ n, Subsingleton (Ext.{u} (ModuleCat.of R (R ⧸ maximalIdeal R)) (ModuleCat.of R R) i)) ∧
     (⊤ : Submodule R (Ext.{u} (ModuleCat.of R (R ⧸ maximalIdeal R)) (ModuleCat.of R R)
      n)).IsPrincipal,
     ∃ i > n, Subsingleton (Ext.{u} (ModuleCat.of R (R ⧸ maximalIdeal R)) (ModuleCat.of R R) i),
     (∀ i < n, Subsingleton (Ext.{u} (ModuleCat.of R (R ⧸ maximalIdeal R)) (ModuleCat.of R R) i)) ∧
     (⊤ : Submodule R (Ext.{u} (ModuleCat.of R (R ⧸ maximalIdeal R)) (ModuleCat.of R R)
      n)).IsPrincipal,
     IsCohenMacaulayLocalRing R ∧ (⊤ : Submodule R (Ext.{u} (ModuleCat.of R (R ⧸ maximalIdeal R))
      (ModuleCat.of R R) n)).IsPrincipal,
     IsCohenMacaulayLocalRing R ∧ ∀ {J : Ideal R}, maximalIdeal R ∈ J.minimalPrimes →
      J.spanFinrank = n → J.isIrreducible,
     IsCohenMacaulayLocalRing R ∧ ∃ J : Ideal R, maximalIdeal R ∈ J.minimalPrimes ∧
      J.spanFinrank = n ∧ J.isIrreducible
     ].TFAE := by
  tfae_have 1 → 2 := by

    sorry
  tfae_have 2 → 3 := by

    sorry
  tfae_have 3 → 4 := by
    --trivial
    sorry
  tfae_have 4 → 1 := by

    sorry
  tfae_have 3 → 5 := by
    --trivial
    sorry
  tfae_have 5 → 6 := by
    --CM basic
    sorry
  tfae_have 6 → 7 := by

    sorry
  tfae_have 7 → 8 := by
    --trivial
    sorry
  tfae_have 8 → 3 := by

    sorry
  sorry
-/
