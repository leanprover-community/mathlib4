/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
import Mathlib.CategoryTheory.Abelian.Injective.Dimension
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
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
/-!

# The Definition of Gorenstein (Local) Ring

-/

section ENat

lemma ENat.add_le_add_right_iff (a b : ℕ∞) (c : ℕ) :
    a + c ≤ b + c ↔ a ≤ b := by
  induction a with
  | top => simp only [_root_.top_add, top_le_iff]; exact WithTop.add_coe_eq_top_iff
  | coe a => induction b with
    | top => simp
    | coe b => norm_cast; exact Nat.add_le_add_iff_right

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
  | coe a =>
    norm_cast
    simp

end ENat

universe v u

variable (R : Type u) [CommRing R]

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

local instance hasExt_of_small' [Small.{v} R] : CategoryTheory.HasExt.{w} (ModuleCat.{v} R) :=
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
      (Limits.IsZero.eq_zero_of_tgt (AddCommGrp.of (Ext S.X₂ M (n + 1))).isZero_of_subsingleton _)
    have surj : Function.Surjective (S_exact.extClass.precomp M (add_comm 1 n)) :=
      (AddCommGrp.epi_iff_surjective _).mp epi
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
          (((AddCommGrp.of (Ext S.X₂ L (n + 1))).isZero_of_subsingleton).eq_zero_of_src _)
          (((AddCommGrp.of (Ext S.X₂ L (n + 2))).isZero_of_subsingleton).eq_zero_of_tgt _)
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
    rw [not_subsingleton_iff_nontrivial] at this
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
        have epi := exac.epi_f ((@AddCommGrp.isZero_of_subsingleton _ zero).eq_zero_of_tgt _)
        have : S.f = x • 𝟙 M := by
          ext
          simp [S]
        simp only [S, this, AddCommGrp.epi_iff_surjective, AddCommGrp.hom_ofHom] at epi
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

universe w

variable [Small.{v} R] [UnivLE.{v, w}]

local instance hasExt_of_small'' [Small.{v} R] : CategoryTheory.HasExt.{w} (ModuleCat.{v} R) :=
  CategoryTheory.hasExt_of_enoughProjectives.{w} (ModuleCat.{v} R)

noncomputable def ext_quotient_regular_sequence_length (M : ModuleCat.{v} R) [Nontrivial M]
    [Module.Finite R M] (rs : List R) :
    (Ext.{w} (ModuleCat.of R (Shrink.{v} (R ⧸ Ideal.ofList rs))) M rs.length) ≃ₗ[R]
    M ⧸ Ideal.ofList rs • (⊤ : Submodule R M) := by
  generalize len : rs.length = n
  induction n generalizing M rs
  · rw [List.length_eq_zero_iff.mp len, Ideal.ofList_nil, Submodule.bot_smul]
    let e₀ := (Shrink.linearEquiv R (R ⧸ (⊥ : Ideal R))).trans
      (AlgEquiv.quotientBot R R).toLinearEquiv
    let φ := Ext.linearEquiv₀ (R := R) (X := ModuleCat.of R (Shrink (R ⧸ (⊥ : Ideal R)))) (Y := M)

    sorry
  · rename_i n hn _ _
    match rs with
    | [] => simp at len
    | x :: rs' =>

      sorry

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
      ((@AddCommGrp.isZero_of_subsingleton _ (h3 h2.2)).eq_zero_of_src _)
      ((@AddCommGrp.isZero_of_subsingleton _ (h1 h2.1)).eq_zero_of_tgt _)
    exact AddCommGrp.subsingleton_of_isZero this

open Pointwise in
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
  have epi := exac.epi_f ((@AddCommGrp.isZero_of_subsingleton _ this).eq_zero_of_tgt _)
  have : S.f = x • 𝟙 (ModuleCat.of R (Shrink.{v, u} (R ⧸ p))) := by
    ext
    simp [S]
  simp only [S, this, AddCommGrp.epi_iff_surjective, AddCommGrp.hom_ofHom] at epi
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

lemma ext_vanish_of_residueField_vanish (M : ModuleCat.{v} R) (n : ℕ)
    (h : ∀ i > n, Subsingleton (Ext.{w} (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R))) M i)) :
    ∀ i > n, ∀ N : ModuleCat.{v} R, Subsingleton (Ext.{w} N M i) := by
  intro i hi N
  have : i = i - 1 + 1 := by omega
  rw [this]
  apply ext_subsingleton_of_quotients
  rw [← this]
  intro I
  let _ : Module.Finite R (Shrink.{v, u} (R ⧸ I)) := sorry
  apply ext_subsingleton_of_support_subset
  intro p _
  simp only [Set.mem_setOf_eq]
  have (n : ℕ) : ringKrullDim (R ⧸ p.1) ≤ n →
    Subsingleton (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ p.asIdeal))) M i) := by
    induction n
    · --p = maximalIdeal R
      --fym
      sorry
    · --fym
      sorry
  rcases exist_nat_eq' R with ⟨n, hn⟩
  apply this n
  rw [← hn]
  exact ringKrullDim_le_of_surjective _ Ideal.Quotient.mk_surjective

lemma injectiveDimension_eq_sSup (M : ModuleCat.{v} R) :
    injectiveDimension M = sInf {n : WithBot ℕ∞ | ∀ (i : ℕ), n < i →
      Subsingleton (Ext.{w} (ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R))) M i)} := by

  sorry

end

section

variable [Small.{v} R]

lemma supportDim_le_injectiveDimension (M : ModuleCat.{v} R)
    (h : injectiveDimension M ≠ ⊤) : supportDim R M ≤ injectiveDimension M := by

  sorry

lemma injectiveDimension_eq_depth (M : ModuleCat.{v} R) (h : injectiveDimension M ≠ ⊤) :
    injectiveDimension M = IsLocalRing.depth (ModuleCat.of R (Shrink.{v} R)) := by

  sorry

end

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
  have le := supportDim_le_injectiveDimension (ModuleCat.of R R) this
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
