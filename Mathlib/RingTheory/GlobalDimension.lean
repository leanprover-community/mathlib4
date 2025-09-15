/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.Data.ENat.Lattice
import Mathlib.RingTheory.Spectrum.Maximal.Defs
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Regular.Category
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.RingTheory.Localization.Module
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
/-!
# The Global Dimension of a Ring
-/

--set_option pp.universes true

universe v u

variable (R : Type u) [CommRing R]

open CategoryTheory IsLocalRing RingTheory.Sequence

section ProjectiveDimension

variable {C : Type u} [Category.{v, u} C] [Abelian C]

--projectiveDimension should be `-∞` when `X = 0`

noncomputable def projectiveDimension (X : C) : WithBot ℕ∞ :=
  sInf {n : WithBot ℕ∞ | ∀ (i : ℕ), n < i → HasProjectiveDimensionLT X i}

/-
noncomputable def nonnegProjectiveDimension (X : C) : ℕ∞ :=
  sInf (({(n : ℕ) | HasProjectiveDimensionLT X n}).image WithTop.some)
-/

lemma projectiveDimension_eq_of_iso {X Y : C} (e : X ≅ Y) :
    projectiveDimension X = projectiveDimension Y := by
  simp only [projectiveDimension]
  congr! 5
  exact ⟨fun h ↦ hasProjectiveDimensionLT_of_iso e _,
    fun h ↦ hasProjectiveDimensionLT_of_iso e.symm _⟩

lemma hasProjectiveDimensionLT_of_projectiveDimension_lt (X : C) (n : ℕ)
    (h : projectiveDimension X < n) : HasProjectiveDimensionLT X n := by
  have : projectiveDimension X ∈ _ := csInf_mem (by
    use ⊤
    simp)
  simp only [Set.mem_setOf_eq] at this
  exact this n h

lemma projectiveDimension_le_iff (X : C) (n : ℕ) : projectiveDimension X ≤ n ↔
    HasProjectiveDimensionLE X n := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · apply hasProjectiveDimensionLT_of_projectiveDimension_lt X (n + 1)
    exact lt_of_le_of_lt h (Nat.cast_lt.mpr (lt_add_one n))
  · apply sInf_le
    simp only [Set.mem_setOf_eq, Nat.cast_lt]
    intro i hi
    exact hasProjectiveDimensionLT_of_ge X (n + 1) i hi

lemma projectiveDimension_ge_iff (X : C) (n : ℕ) : n ≤ projectiveDimension X  ↔
    ¬ HasProjectiveDimensionLT X n := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp only [projectiveDimension, le_sInf_iff, Set.mem_setOf_eq] at h
    by_contra lt
    by_cases eq0 : n = 0
    · have := h ⊥ (fun i _ ↦ (hasProjectiveDimensionLT_of_ge X n i (by simp [eq0])))
      simp [eq0] at this
    · have : ∀ (i : ℕ), (n - 1 : ℕ) < (i : WithBot ℕ∞) → HasProjectiveDimensionLT X i := by
        intro i hi
        exact hasProjectiveDimensionLT_of_ge X n i (Nat.le_of_pred_lt (Nat.cast_lt.mp hi))
      have not := Nat.cast_le.mp (h (n - 1 : ℕ) this)
      omega
  · simp only [projectiveDimension, le_sInf_iff, Set.mem_setOf_eq]
    intro m hm
    by_contra nle
    exact h (hm _ (lt_of_not_ge nle))

lemma projectiveDimension_eq_bot_iff (X : C) : projectiveDimension X = ⊥ ↔
    Limits.IsZero X := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have : HasProjectiveDimensionLT X 0 := by
      apply hasProjectiveDimensionLT_of_projectiveDimension_lt X 0
      simp [h, bot_lt_iff_ne_bot]
    exact isZero_of_hasProjectiveDimensionLT_zero X
  · rw [eq_bot_iff]
    apply sInf_le
    intro i _
    have := h.hasProjectiveDimensionLT_zero
    apply hasProjectiveDimensionLT_of_ge X 0 i (Nat.zero_le i)

lemma projectiveDimension_eq_find (X : C) (h : ∃ n, HasProjectiveDimensionLE X n)
    (nzero : ¬ Limits.IsZero X) [DecidablePred (HasProjectiveDimensionLE X)] :
    projectiveDimension X = Nat.find h := by
  apply le_antisymm ((projectiveDimension_le_iff _ _).mpr (Nat.find_spec h))
  apply (projectiveDimension_ge_iff _ _).mpr
  by_cases eq0 : Nat.find h = 0
  · simp only [eq0]
    by_contra
    exact nzero (isZero_of_hasProjectiveDimensionLT_zero X)
  · rw [← Nat.succ_pred_eq_of_ne_zero eq0]
    exact (Nat.find_min h (Nat.sub_one_lt eq0))

/-
lemma projectiveDimension_eq_nonnegProjectiveDimension_of_not_zero (X : C) (h : ¬ Limits.IsZero X) :
    nonnegProjectiveDimension X = projectiveDimension X :=  by
  sorry
-/

lemma projectiveDimension_ne_top_iff (X : C) : projectiveDimension X ≠ ⊤ ↔
    ∃ n, HasProjectiveDimensionLE X n := by
  simp only [projectiveDimension, ne_eq, sInf_eq_top, Set.mem_setOf_eq, not_forall]
  refine ⟨fun ⟨x, hx, ne⟩ ↦ ?_, fun ⟨n, hn⟩ ↦ ?_⟩
  · by_cases eqbot : x = ⊥
    · use 0
      have := hx 0 (by simp [eqbot, bot_lt_iff_ne_bot])
      exact instHasProjectiveDimensionLTSucc X 0
    · have : x.unbot eqbot ≠ ⊤ := by
        by_contra eq
        rw [← WithBot.coe_inj, WithBot.coe_unbot, WithBot.coe_top] at eq
        exact ne eq
      use (x.unbot eqbot).toNat
      have eq : x = (x.unbot eqbot).toNat := (WithBot.coe_unbot x eqbot).symm.trans
        (WithBot.coe_inj.mpr (ENat.coe_toNat this).symm)
      have : x < ((x.unbot eqbot).toNat + 1 : ℕ) := by
        nth_rw 1 [eq]
        exact Nat.cast_lt.mpr (lt_add_one _)
      exact hx ((x.unbot eqbot).toNat + 1 : ℕ) this
  · use n
    simpa using ⟨fun i hi ↦ hasProjectiveDimensionLT_of_ge X (n + 1) i hi,
      WithBot.coe_inj.not.mpr (ENat.coe_ne_top n)⟩

/-
lemma nonnegProjectiveDimension_ne_top_iff (X : C) : nonnegProjectiveDimension X ≠ ⊤ ↔
    ∃ n, HasProjectiveDimensionLE X n := by
  sorry
-/

open Limits Abelian in
lemma hasProjectiveDimensionLT_one_iff (X : C) :
    Projective X ↔ HasProjectiveDimensionLT X 1 := by
  letI := HasExt.standard C
  refine ⟨fun h ↦ inferInstance, fun ⟨h⟩ ↦ ⟨?_⟩⟩
  intro Z Y f g epi
  let S := ShortComplex.mk (kernel.ι g) g (kernel.condition g)
  have S_exact : S.ShortExact := {
    exact := ShortComplex.exact_kernel g
    mono_f := equalizer.ι_mono
    epi_g := epi}
  have : IsZero (AddCommGrp.of (Ext X S.X₁ 1)) := by
    let _ := h 1 (le_refl 1) (Y := S.X₁)
    exact AddCommGrp.isZero_of_subsingleton _
  have exac := Ext.covariant_sequence_exact₃' X S_exact 0 1 (zero_add 1)
  have surj: Function.Surjective ((Ext.mk₀ S.g).postcomp X (add_zero 0)) :=
    (AddCommGrp.epi_iff_surjective _).mp (exac.epi_f (this.eq_zero_of_tgt _))
  rcases surj (Ext.mk₀ f) with ⟨f', hf'⟩
  use Ext.addEquiv₀ f'
  simp only [AddMonoidHom.flip_apply, Ext.bilinearComp_apply_apply] at hf'
  rw [← Ext.mk₀_addEquiv₀_apply f', Ext.mk₀_comp_mk₀] at hf'
  exact (Ext.mk₀_bijective X Y).1 hf'

end ProjectiveDimension

section GlobalDimension

variable (R : Type u) [CommRing R]

open Abelian

local instance small_of_quotient [Small.{v} R] (I : Ideal R) : Small.{v} (R ⧸ I) :=
  small_of_surjective Ideal.Quotient.mk_surjective


section

universe w

variable [UnivLE.{v, w}]

local instance hasExt_of_small [Small.{v} R] : CategoryTheory.HasExt.{w} (ModuleCat.{v} R) :=
  CategoryTheory.hasExt_of_enoughProjectives.{w} (ModuleCat.{v} R)

open Limits in
lemma injective_of_quotients_ext_one_subsingleton [Small.{v} R] (M : ModuleCat.{v} R)
    (h : ∀ (I : Ideal R), Subsingleton (Ext.{w} (ModuleCat.of R (Shrink.{v, u} (R ⧸ I))) M 1)) :
    Injective M := by
  rw [← Module.injective_iff_injective_object, ← Module.Baer.iff_injective]
  intro I g
  let Sf := (Shrink.linearEquiv.{v} R R).symm.toLinearMap.comp
    (I.subtype.comp (Shrink.linearEquiv.{v} R I).toLinearMap)
  let Sg := (Shrink.linearEquiv.{v} R (R ⧸ I)).symm.toLinearMap.comp
    ((Ideal.Quotient.mkₐ R I).toLinearMap.comp (Shrink.linearEquiv.{v} R R).toLinearMap)
  have exac : Function.Exact Sf Sg := by
    intro x
    have (z : R) : z ∈ I ↔ ∃ y, ↑((equivShrink ↥I).symm y) = z := by
      refine ⟨fun h ↦ ?_, fun ⟨y, hy⟩ ↦ by simp [← hy]⟩
      use (equivShrink I) ⟨z, h⟩
      simp
    simpa [Sf, Sg, Ideal.Quotient.eq_zero_iff_mem, AddEquiv.symm_apply_eq]
      using this ((equivShrink R).symm x)
  have inj : Function.Injective Sf := by
    simpa [Sf] using LinearEquiv.injective (Shrink.linearEquiv R I)
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
  have : IsZero (AddCommGrp.of (Ext (ModuleCat.of R (Shrink.{v, u} (R ⧸ I))) M 1)) := by
    let _ := h I
    exact AddCommGrp.isZero_of_subsingleton _
  have exac := Ext.contravariant_sequence_exact₁' S_exact M 0 1 rfl
  have surj : Function.Surjective ((Ext.mk₀ S.f).precomp M (add_zero 0)) :=
    (AddCommGrp.epi_iff_surjective _).mp (exac.epi_f (this.eq_zero_of_tgt _))
  let f := g.comp (Shrink.linearEquiv R I).toLinearMap
  rcases surj (Ext.mk₀ (ModuleCat.ofHom f)) with ⟨f', hf'⟩
  simp only [Ext.bilinearComp_apply_apply] at hf'
  rw [← Ext.mk₀_addEquiv₀_apply f', Ext.mk₀_comp_mk₀] at hf'
  have eqcomp := congrArg ModuleCat.Hom.hom ((Ext.mk₀_bijective _ _).1 hf')
  simp only [← LinearMap.comp_assoc, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
    LinearEquiv.eq_comp_toLinearMap_iff, S, Sf, f] at eqcomp
  use (ModuleCat.Hom.hom (Ext.addEquiv₀ f')).comp (Shrink.linearEquiv R R).symm.toLinearMap
  intro x hx
  simp only [LinearMap.coe_comp, Function.comp_apply, ← eqcomp, LinearEquiv.coe_coe,
    Submodule.coe_subtype]
  congr

open Limits in
lemma ext_subsingleton_of_quotients [Small.{v} R] (M : ModuleCat.{v} R) (n : ℕ)
    (h : ∀ I : Ideal R, Subsingleton (Ext.{w} (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M (n + 1))) :
    ∀ N : ModuleCat.{v} R, Subsingleton (Ext.{w} N M (n + 1)) := by
  induction' n with n ih generalizing M
  · have : Injective M := injective_of_quotients_ext_one_subsingleton R M h
    intro N
    exact subsingleton_of_forall_eq 0 (fun e ↦ Ext.eq_zero_of_injective e)
  · let ei : EnoughInjectives (ModuleCat R) := inferInstance
    rcases ei.1 M with ⟨⟨I, inj, f, mono⟩⟩
    let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
    have S_exact : S.ShortExact := {
      exact := ShortComplex.exact_cokernel f
      mono_f := ‹_›
      epi_g := coequalizer.π_epi}
    have (N : ModuleCat R) : Subsingleton (Ext N M (n + 1 + 1)) ↔
      Subsingleton (Ext N (cokernel f) (n + 1)) := by
      have (m : ℕ) : Subsingleton (AddCommGrp.of (Ext N S.X₂ (m + 1))) :=
        subsingleton_of_forall_eq 0 Ext.eq_zero_of_injective
      have := ComposableArrows.Exact.isIso_map'
        (Ext.covariantSequence_exact N S_exact (n + 1) (n + 1 + 1) rfl) 1 (by decide)
        (IsZero.eq_zero_of_src (AddCommGrp.of (Ext N S.X₂ (n + 1))).isZero_of_subsingleton _)
        (IsZero.eq_zero_of_tgt (AddCommGrp.of (Ext N S.X₂ (n + 1 + 1))).isZero_of_subsingleton _)
      exact (@asIso _ _ _ _ _ this).addCommGroupIsoToAddEquiv.subsingleton_congr.symm
    simp only [this] at h ⊢
    exact ih (cokernel f) h

end

noncomputable def globalDimension : WithBot ℕ∞ :=
  ⨆ (M : ModuleCat.{v} R), projectiveDimension.{v} M

lemma globalDimension_eq_bot_iff [Small.{v} R] : globalDimension.{v} R = ⊥ ↔ Subsingleton R := by
  simp only [globalDimension, iSup_eq_bot, projectiveDimension_eq_bot_iff,
    ModuleCat.isZero_iff_subsingleton]
  refine ⟨fun h ↦ ?_, fun h M ↦ Module.subsingleton R M⟩
  let _ := h (ModuleCat.of R (Shrink.{v} R))
  exact (equivShrink.{v} R).subsingleton

lemma globalDimension_le_iff (n : ℕ) : globalDimension.{v} R ≤ n ↔
    ∀ M : ModuleCat.{v} R, HasProjectiveDimensionLE M n := by
  simp [globalDimension, projectiveDimension_le_iff]

local instance hasExt_standard : HasExt.{max (max (v + 1) u) v, v, max (v + 1) u} (ModuleCat.{v} R) :=
  CategoryTheory.HasExt.standard (ModuleCat.{v} R)

lemma globalDimension_le_tfae [Small.{v} R] (n : ℕ) : [globalDimension.{v} R ≤ n,
    ∀ M : ModuleCat.{v} R, Module.Finite R M → HasProjectiveDimensionLE M n,
    ∀ m ≥ n + 1, ∀ (N M : ModuleCat.{v} R), Subsingleton (Ext N M m)].TFAE := by
  tfae_have 1 → 2 := by
    simpa only [globalDimension, iSup_le_iff, projectiveDimension_le_iff]
      using fun h M _ ↦ h M
  tfae_have 2 → 3 := by
    intro h m ge N M
    have eq : m - 1 + 1 = m := by omega
    have (I : Ideal R) :
      Subsingleton (Ext (ModuleCat.of R (Shrink.{v, u} (R ⧸ I))) M (m - 1 + 1)) := by
      simpa only [eq] using (h (ModuleCat.of R (Shrink.{v, u} (R ⧸ I)))
        (Module.Finite.equiv (Shrink.linearEquiv R (R ⧸ I)).symm)).1 m ge (Y := M)
    rw [← eq]
    exact ext_subsingleton_of_quotients.{v, u, max u (v + 1)} R M (m - 1) this N
  tfae_have 3 → 1 := by
    intro h
    simp only [globalDimension, iSup_le_iff, projectiveDimension_le_iff]
    intro M
    exact ⟨fun m hm {N} ↦ h m hm M N⟩
  tfae_finish

lemma globalDimension_eq_sup_projectiveDimension_finite [Small.{v, u} R] : globalDimension.{v} R =
    ⨆ (M : ModuleCat.{v} R), ⨆ (_ : Module.Finite R M), projectiveDimension.{v} M := by
  have aux (n : ℕ): globalDimension.{v} R ≤ n ↔
    ⨆ (M : ModuleCat.{v} R), ⨆ (_ : Module.Finite R M), projectiveDimension.{v} M ≤ n := by
    simpa only [iSup_le_iff, projectiveDimension_le_iff] using (globalDimension_le_tfae R n).out 0 1
  refine eq_of_forall_ge_iff (fun N ↦ ?_)
  by_cases eqbot : N = ⊥
  · simp only [eqbot, le_bot_iff, globalDimension_eq_bot_iff, iSup_eq_bot,
      projectiveDimension_eq_bot_iff, ModuleCat.isZero_iff_subsingleton]
    refine ⟨fun h M _ ↦ Module.subsingleton R M, fun h ↦ ?_⟩
    let _ := h (ModuleCat.of R (Shrink.{v} R)) (Module.Finite.equiv (Shrink.linearEquiv R R).symm)
    exact (equivShrink.{v} R).subsingleton
  · by_cases eqtop : N.unbot eqbot = ⊤
    · have : N = ⊤ := (WithBot.coe_unbot _ eqbot).symm.trans (WithBot.coe_inj.mpr eqtop)
      simp [this]
    · let n := (N.unbot eqbot).toNat
      have : N = n := (WithBot.coe_unbot _ eqbot).symm.trans
        (WithBot.coe_inj.mpr (ENat.coe_toNat eqtop).symm)
      simpa only [this] using aux n

end GlobalDimension
