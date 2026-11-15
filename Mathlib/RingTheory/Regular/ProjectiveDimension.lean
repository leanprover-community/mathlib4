/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Ext.Finite
public import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
public import Mathlib.Data.ENat.WithBot
public import Mathlib.RingTheory.Regular.Free
public import Mathlib.RingTheory.Regular.RegularSequence

import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Regular.Category

/-!
# ProjectiveDimension of quotient by regular element

For `M` a finitely generated module over Noetherian local ring `R` and an `M`-regular element `x`
contained in the unique maximal ideal of `R`, `projdim(M/xM) = projdim(M) + 1`.
The analogous version for quotient regular sequence is also provided.

## Main Results

* `ModuleCat.projectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular` : For `M` a finitely
  generated module over Noetherian local ring `R` and an `M`-regular element `x` contained in
  the unique maximal ideal of `R`, `projdim(M/xM) = projdim(M) + 1`
-/

public section

universe v u

variable {R : Type u} [CommRing R]

open CategoryTheory Abelian IsLocalRing Module RingTheory.Sequence

namespace ModuleCat

variable [Small.{v} R]

section

variable [IsNoetherianRing R]

lemma hasProjectiveDimensionLT_of_forall_finite (M : ModuleCat.{v} R) [Module.Finite R M] (n : ℕ)
    (h : ∀ L : ModuleCat.{v} R, Module.Finite R L → Subsingleton (Ext M L n)) :
    HasProjectiveDimensionLT M n := by
  induction n generalizing M with
  | zero =>
    have : Subsingleton (M ⟶ M) := Ext.homEquiv₀.subsingleton_congr.mp (h M ‹_›)
    have : Limits.IsZero M := (Limits.IsZero.iff_id_eq_zero M).mpr (Subsingleton.eq_zero (𝟙 M))
    exact this.hasProjectiveDimensionLT_zero
  | succ n hn =>
    rcases Module.exists_finite_presentation R M with ⟨_, _, _, _, _, f, surjf⟩
    let S : ShortComplex (ModuleCat.{v} R) := f.shortComplexKer
    have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer surjf
    match n with
    | 0 =>
      simp only [zero_add, ← projective_iff_hasProjectiveDimensionLT_one]
      have : Subsingleton (Ext M S.X₁ 1) := h S.X₁ inferInstance
      rcases Ext.covariant_sequence_exact₃ M hS (Ext.mk₀ (𝟙 M)) (zero_add 1)
        (Subsingleton.eq_zero _) with ⟨f', hf'⟩
      rcases (Ext.mk₀_bijective M S.X₂).2 f' with ⟨f, hf⟩
      rw [← hf, Ext.mk₀_comp_mk₀, (Ext.mk₀_bijective _ _).1.eq_iff] at hf'
      exact (Retract.mk f S.g hf').projective
    | n + 1 =>
      rw [hS.hasProjectiveDimensionLT_X₃_iff n inferInstance]
      have (L : ModuleCat.{v} R) : Subsingleton (Ext S.X₁ L (n + 1)) ↔
        Subsingleton (Ext M L (n + 2)) := by
        have (m : ℕ) : Subsingleton (Ext S.X₂ L (m + 1)) := Ext.subsingleton_of_projective S.X₂ L m
        have isi : IsIso (AddCommGrpCat.ofHom (hS.extClass.precomp L (add_comm 1 _))) :=
          (Ext.contravariantSequence_exact hS L (n + 1) (n + 2)
            (add_comm 1 _)).isIso_map' 1 (by decide)
              ((AddCommGrpCat.of _).isZero_of_subsingleton.eq_zero_of_src _)
                ((AddCommGrpCat.of _).isZero_of_subsingleton.eq_zero_of_tgt _)
        exact (asIso (AddCommGrpCat.ofHom (hS.extClass.precomp L
          (add_comm 1 _)))).addCommGroupIsoToAddEquiv.subsingleton_congr
      apply hn S.X₁
      simpa [this] using h

end

variable [IsLocalRing R] [IsNoetherianRing R]

lemma projectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular (M : ModuleCat.{v} R)
    [Module.Finite R M] (x : R) (reg : IsSMulRegular M x) (mem : x ∈ maximalIdeal R) :
    projectiveDimension (ModuleCat.of R (QuotSMulTop x M)) = projectiveDimension M + 1 := by
  have sub : Subsingleton M ↔ Subsingleton (QuotSMulTop x M) := by
    refine ⟨fun h ↦ inferInstance, fun h ↦ ?_⟩
    contrapose! h
    exact (nontrivial_quotSMulTop_of_mem_maximalIdeal M mem)
  have aux (n : ℕ) : projectiveDimension (ModuleCat.of R (QuotSMulTop x M)) ≤ n ↔
    projectiveDimension M + 1 ≤ n := by
    match n with
    | 0 =>
      rw [projectiveDimension_le_iff]
      simp only [HasProjectiveDimensionLE, zero_add, ← projective_iff_hasProjectiveDimensionLT_one,
        CharP.cast_eq_zero, ENat.WithBot.add_one_le_zero_iff, projectiveDimension_eq_bot_iff,
        ModuleCat.isZero_iff_subsingleton, sub, ← IsProjective.iff_projective]
      refine ⟨fun h ↦ ?_, fun h ↦ Projective.of_free⟩
      have : Module.Free R (QuotSMulTop x M) := Module.free_of_flat_of_isLocalRing
      by_contra! ntr
      have := QuotSMulTop.mem_annihilator M x
      simp only [annihilator_eq_bot.mpr inferInstance, Submodule.mem_bot] at this
      simp only [this, IsSMulRegular.zero_iff_subsingleton] at reg
      absurd not_subsingleton_iff_nontrivial.mpr ntr
      infer_instance
    | n + 1 =>
      nth_rw 2 [← Nat.cast_one, Nat.cast_add]
      simp only [ENat.WithBot.add_le_add_natCast_right_iff, projectiveDimension_le_iff]
      let S := M.smulShortComplex x
      have hS : S.ShortExact := reg.smulShortComplex_shortExact
      refine ⟨fun h ↦ ?_, fun h ↦ hS.hasProjectiveDimensionLT_X₃ (n + 1) h
        (hasProjectiveDimensionLT_of_ge M (n + 1) (n + 2) (Nat.le_add_right _ 1))⟩
      apply hasProjectiveDimensionLT_of_forall_finite
      intro L _
      have zero := HasProjectiveDimensionLT.subsingleton ↧(QuotSMulTop x M)
        (n + 2) _ (le_refl _) L
      have exac := Ext.contravariant_sequence_exact₁' hS L (n + 1) (n + 2) (add_comm 1 (n + 1))
      have epi := exac.epi_f ((@AddCommGrpCat.isZero_of_subsingleton _ zero).eq_zero_of_tgt _)
      have : S.f = x • 𝟙 M := rfl
      simp only [S, this, AddCommGrpCat.epi_iff_surjective, AddCommGrpCat.hom_ofHom] at epi
      by_contra! ntr
      have : x ∈ (Module.annihilator R (Ext M L (n + 1))).jacobson :=
        (IsLocalRing.maximalIdeal_le_jacobson _) mem
      absurd Submodule.top_ne_pointwise_smul_of_mem_jacobson_annihilator this
      rw [eq_comm, eq_top_iff]
      intro y hy
      rcases epi y with ⟨z, hz⟩
      simp only [ModuleCat.smulShortComplex, Ext.mk₀_smul,
        Ext.bilinearComp_apply_apply, Ext.smul_comp, Ext.mk₀_id_comp] at hz
      simpa [← hz] using Submodule.smul_mem_pointwise_smul _ _ ⊤ trivial
  refine eq_of_forall_ge_iff (fun N ↦ ?_)
  induction N with
  | top => simp
  | bot =>
    simpa [projectiveDimension_eq_bot_iff, ModuleCat.isZero_iff_subsingleton] using sub.symm
  | coe n => simpa using aux n

lemma projectiveDimension_quotient_eq_add_length_of_isWeaklyRegular (M : ModuleCat.{v} R)
    [Nontrivial M] [Module.Finite R M] (rs : List R) (reg : IsWeaklyRegular M rs)
    (mem : ∀ r ∈ rs, r ∈ maximalIdeal R) :
    projectiveDimension (ModuleCat.of R (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M))) =
    projectiveDimension M + rs.length := by
  generalize len : rs.length = n
  induction n generalizing M rs with
  | zero =>
    rw [List.length_eq_zero_iff.mp len, Ideal.ofList_nil, Submodule.bot_smul]
    simpa using projectiveDimension_eq_of_iso (Submodule.quotEquivOfEqBot ⊥ rfl).toModuleIso
  | succ n hn =>
    match rs with
    | [] => simp at len
    | x :: rs' =>
      simp only [List.mem_cons, forall_eq_or_imp] at mem
      simp only [isWeaklyRegular_cons_iff] at reg
      have := nontrivial_quotSMulTop_of_mem_maximalIdeal M mem.1
      simp only [List.length_cons, Nat.add_right_cancel_iff] at len
      rw [Nat.cast_add, Nat.cast_one, projectiveDimension_eq_of_iso
        (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M x rs').toModuleIso, add_comm _ 1,
        ← add_assoc, ← projectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular M x reg.1 mem.1,
        ← hn ↧(QuotSMulTop x M) rs' reg.2 mem.2 len]

lemma projectiveDimension_quotient_eq_length (rs : List R) (reg : IsRegular R rs) :
    projectiveDimension (ModuleCat.of R (Shrink.{v} (R ⧸ Ideal.ofList rs))) = rs.length := by
  have mem_max : ∀ x ∈ rs, x ∈ maximalIdeal R := by
    intro x hx
    apply IsLocalRing.le_maximalIdeal reg.2.symm
    simpa using (Ideal.mem_span x).mpr fun p a ↦ a hx
  let e : (Shrink.{v} (R ⧸ Ideal.ofList rs)) ≃ₗ[R]
    (Shrink.{v} R) ⧸ Ideal.ofList rs • (⊤ : Submodule R (Shrink.{v} R)) :=
    ((Shrink.linearEquiv R _).trans (Submodule.Quotient.equiv _ _ (Shrink.linearEquiv R R).symm (by
      nth_rw 1 [← (Ideal.ofList rs).mul_top, ← smul_eq_mul, Submodule.map_smul'']
      simp )))
  rw [projectiveDimension_eq_of_iso e.toModuleIso,
    projectiveDimension_quotient_eq_add_length_of_isWeaklyRegular ↧(Shrink.{v} R) rs
    (((Shrink.linearEquiv R R).isWeaklyRegular_congr rs).mpr reg.1) mem_max,
    ModuleCat.projectiveDimension_eq_zero_of_projective, zero_add]

end ModuleCat

namespace ModuleCat

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
      have := Module.finitePresentation_of_finite R M
      have := Module.Finite.of_restrictScalars_finite R (R ⧸ Ideal.span {x}) (QuotSMulTop x M)
      have mem' : x ∈ Ring.jacobson R := by simpa [IsLocalRing.ringJacobson_eq_maximalIdeal]
      refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
      · have := (Module.free_quotSMulTop_iff_free R M mem' reg2).mpr
          Module.free_of_flat_of_isLocalRing
        exact Module.Projective.of_free
      · have : IsLocalRing (R ⧸ Ideal.span {x}) :=
          have : Nontrivial (R ⧸ Ideal.span {x}) :=
            Quotient.nontrivial_iff.mpr (by simpa [← Submodule.ideal_span_singleton_smul])
          IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
        have := (Module.free_quotSMulTop_iff_free R M mem' reg2).mp
          Module.free_of_flat_of_isLocalRing
        exact Module.Projective.of_free
    | succ n ih =>
      obtain ⟨N, _, _, _, _, f, surjf⟩ := Module.exists_finite_presentation R M
      let S := f.shortComplexKer
      have S_exact := LinearMap.shortExact_shortComplexKer surjf
      have proj := ModuleCat.projective_of_categoryTheory_projective S.X₂
      have reg2'' : IsSMulRegular S.X₂ x := (isLeftRegular_iff_isRegular.mp reg1).isSMulRegular
      have reg2' : IsSMulRegular S.X₁ x := reg2''.submodule _ _
      have surj := Ideal.Quotient.mk_surjective (I := Ideal.span {x})
      let g := (QuotSMulTop.map x (LinearMap.ker f).subtype).extendScalarsOfSurjective surj
      let h := (QuotSMulTop.map x f).extendScalarsOfSurjective surj
      have Sx_exact' : Function.Exact g h :=
        QuotSMulTop.map_exact x f.exact_subtype_ker_map surjf
      let Sx := ModuleCat.shortComplexOfCompEqZero g h Sx_exact'.linearMap_comp_eq_zero
      have inj : Function.Injective (QuotSMulTop.map x (LinearMap.ker f).subtype) := by
        rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
        intro y hy
        rcases Submodule.Quotient.mk_surjective _ y with ⟨y', rfl⟩
        simp only [LinearMap.mem_ker, QuotSMulTop.map_apply_mk, Submodule.subtype_apply,
          Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top,
          true_and] at hy
        rcases hy with ⟨z, hz⟩
        have := y'.2
        rw [← hz, LinearMap.mem_ker, map_smul] at this
        simp only [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists,
          Submodule.mem_top, true_and, Subtype.exists, SetLike.mk_smul_mk, LinearMap.mem_ker]
        use z, reg2.right_eq_zero_of_smul this
        exact Subtype.val_inj.mp hz
      have Sx_exact := ModuleCat.shortComplex_shortExact Sx Sx_exact' inj
        (QuotSMulTop.map_surjective x surjf)
      have := Module.finitePresentation_of_finite R N
      exact ((S_exact.hasProjectiveDimensionLT_X₃_iff n proj).trans (ih S.X₁ reg2')).trans
        (Sx_exact.hasProjectiveDimensionLT_X₃_iff n inferInstance).symm
  refine eq_of_forall_ge_iff (fun N ↦ ?_)
  induction N with
  | top => simp
  | bot =>
    simp only [le_bot_iff, projectiveDimension_eq_bot_iff,
      projectiveDimension_eq_bot_iff, ModuleCat.isZero_iff_subsingleton]
    refine ⟨fun h ↦ (Submodule.Quotient.mk_surjective _).subsingleton, fun h ↦ ?_⟩
    by_contra! ntr
    exact (not_subsingleton_iff_nontrivial.mpr (nontrivial_quotSMulTop_of_mem_maximalIdeal M mem)) h
  | coe n => exact aux n

end ModuleCat
