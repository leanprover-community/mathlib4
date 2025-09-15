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

end GlobalDimension
