/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Localization
public import Mathlib.CategoryTheory.Abelian.Injective.Dimension
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Defs
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Logic.Small.Basic
import Mathlib.RingTheory.LocalProperties.Injective
import Mathlib.RingTheory.LocalProperties.Submodule
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!

# Relation of Injective Dimension with Localizations

-/

@[expose] public section

universe v u

namespace ModuleCat

variable {R : Type u} [CommRing R]

open CategoryTheory Limits

set_option backward.isDefEq.respectTransparency false in
instance [Small.{v} R] [IsNoetherianRing R] (S : Submonoid R) :
    (ModuleCat.localizedModuleFunctor.{v} S).PreservesInjectiveObjects where
  injective_obj X {inj} := by
    let _ : Small.{v, u} (Localization S) := small_of_surjective Localization.mkHom_surjective
    rw [← Module.injective_iff_injective_object] at inj ⊢
    simpa [ModuleCat.localizedModuleFunctor] using
      Module.injective_of_isLocalizedModule S (X.localizedModuleMkLinearMap S)

lemma localizedModule_hasInjectiveDimensionLE [Small.{v, u} R] [IsNoetherianRing R] (n : ℕ)
    (S : Submonoid R) (M : ModuleCat.{v} R) [HasInjectiveDimensionLE M n] :
    HasInjectiveDimensionLE (M.localizedModule S) n := by
  have : Small.{v} (Localization S) := small_of_surjective Localization.mkHom_surjective
  induction n generalizing M with
  | zero =>
    have injle : HasInjectiveDimensionLE M 0 := ‹_›
    simp only [HasInjectiveDimensionLE, zero_add, ← injective_iff_hasInjectiveDimensionLT_one]
      at injle ⊢
    rw [← Module.injective_iff_injective_object] at injle ⊢
    exact Module.injective_of_isLocalizedModule S (M.localizedModuleMkLinearMap S)
  | succ n ih =>
    have ei : EnoughInjectives (ModuleCat.{v} R) := inferInstance
    rcases ei.1 M with ⟨I, inj, f, monof⟩
    let T := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
    have T_exact : T.ShortExact := { exact := ShortComplex.exact_cokernel f }
    have T_exact' : Function.Exact (ConcreteCategory.hom T.f) (ConcreteCategory.hom T.g) :=
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp T_exact.1
    have TS_exact' := IsLocalizedModule.map_exact S (T.X₁.localizedModuleMkLinearMap S)
      (T.X₂.localizedModuleMkLinearMap S) (T.X₃.localizedModuleMkLinearMap S) _ _ T_exact'
    let TS := T.map (ModuleCat.localizedModuleFunctor S)
    have TS_exact : TS.ShortExact := T_exact.map_of_exact (ModuleCat.localizedModuleFunctor S)
    let _ := (T_exact.hasInjectiveDimensionLT_X₃_iff n ‹_›).mpr ‹_›
    let _ : Injective TS.X₂ := (ModuleCat.localizedModuleFunctor.{v} S).injective_obj _
    exact (TS_exact.hasInjectiveDimensionLT_X₃_iff n ‹_›).mp (ih T.X₃)

open Limits in
lemma injectiveDimension_le_injectiveDimension_of_isLocalizedModule [Small.{v, u} R]
    [IsNoetherianRing R] (S : Submonoid R) (M : ModuleCat.{v} R) :
    injectiveDimension (M.localizedModule S) ≤ injectiveDimension M := by
  have aux (n : ℕ) : injectiveDimension M ≤ n → injectiveDimension (M.localizedModule S) ≤ n := by
    simp only [injectiveDimension_le_iff]
    intro h
    exact M.localizedModule_hasInjectiveDimensionLE n S
  refine le_of_forall_ge (fun N ↦ ?_)
  induction N with
  | bot =>
    simp only [le_bot_iff, injectiveDimension_eq_bot_iff, ModuleCat.isZero_iff_subsingleton,
      ModuleCat.localizedModule, ← Equiv.subsingleton_congr (equivShrink _)]
    intro _
    apply LocalizedModule.instSubsingleton _
  | coe N =>
    induction N with
    | top => simp
    | coe n => simpa using aux n

lemma hasInjectiveDimensionLE_iff_forall_maximalSpectrum [Small.{v, u} R] [IsNoetherianRing R]
    (n : ℕ) (M : ModuleCat.{v} R) : HasInjectiveDimensionLE M n ↔
    ∀ (m : MaximalSpectrum R), HasInjectiveDimensionLE (M.localizedModule m.1.primeCompl) n := by
  induction n generalizing M with
  | zero =>
    simp only [HasInjectiveDimensionLE, zero_add, ← injective_iff_hasInjectiveDimensionLT_one]
    refine ⟨fun h m ↦ ?_, fun h ↦ ?_⟩
    · let _ : Small.{v} (Localization m.1.primeCompl) :=
        small_of_surjective Localization.mkHom_surjective
      let _ : Module.Injective R M := Module.injective_module_of_injective_object R M
      rw [← Module.injective_iff_injective_object]
      exact Module.injective_of_isLocalizedModule m.1.primeCompl
        (M.localizedModuleMkLinearMap m.1.primeCompl)
    · rw [← Module.injective_iff_injective_object]
      apply Module.injective_of_localization_maximal (fun p hp ↦ ?_)
      let : Small.{v} (Localization.AtPrime p) := small_of_surjective Localization.mkHom_surjective
      have : Module.Injective (Localization.AtPrime p) (M.localizedModule p.primeCompl) := by
        simpa [Module.injective_iff_injective_object] using h ⟨p, hp⟩
      rw [← Module.Baer.iff_injective] at this ⊢
      exact Module.Baer.of_equiv (LinearEquiv.extendScalarsOfIsLocalization p.primeCompl
        (Localization.AtPrime p) (IsLocalizedModule.linearEquiv p.primeCompl
        (M.localizedModuleMkLinearMap p.primeCompl)
        (LocalizedModule.mkLinearMap p.primeCompl M))) this
  | succ n ih =>
    have ei : EnoughInjectives (ModuleCat.{v} R) := inferInstance
    rcases ei.1 M with ⟨I, inj, f, monof⟩
    let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
    have S_exact : S.ShortExact := { exact := ShortComplex.exact_cokernel f }
    let Sp (m : MaximalSpectrum R) := S.map (ModuleCat.localizedModuleFunctor m.1.primeCompl)
    have Sp_exact (m : MaximalSpectrum R) : (Sp m).ShortExact :=
      S_exact.map_of_exact (ModuleCat.localizedModuleFunctor m.1.primeCompl)
    have ih' := ih S.X₃
    simp only [HasInjectiveDimensionLE] at ih' ⊢
    rw [← S_exact.hasInjectiveDimensionLT_X₃_iff n inj, ih']
    have injp (m : MaximalSpectrum R) : Injective (Sp m).X₂ :=
      (ModuleCat.localizedModuleFunctor.{v} m.1.primeCompl).injective_obj _
    exact (forall_congr' (fun p ↦ (Sp_exact p).hasInjectiveDimensionLT_X₃_iff n (injp p)))

lemma hasInjectiveDimensionLE_iff_forall_primeSpectrum [Small.{v, u} R] [IsNoetherianRing R]
    (n : ℕ) (M : ModuleCat.{v} R) : HasInjectiveDimensionLE M n ↔
    ∀ (p : PrimeSpectrum R), HasInjectiveDimensionLE (M.localizedModule p.1.primeCompl) n :=
  ⟨fun _ p ↦ M.localizedModule_hasInjectiveDimensionLE n p.1.primeCompl,
    fun h ↦ (M.hasInjectiveDimensionLE_iff_forall_maximalSpectrum n).mpr
    fun m ↦ h ⟨m.1, Ideal.IsMaximal.isPrime' m.1⟩⟩

lemma injectiveDimension_eq_iSup_localizedModule_prime [Small.{v, u} R] [IsNoetherianRing R]
    (M : ModuleCat.{v} R) : injectiveDimension M =
    ⨆ (p : PrimeSpectrum R), injectiveDimension (M.localizedModule p.1.primeCompl) := by
  have aux (n : ℕ) : injectiveDimension M ≤ n ↔ ⨆ (p : PrimeSpectrum R), injectiveDimension
    (M.localizedModule p.1.primeCompl) ≤ n := by
    simp only [injectiveDimension_le_iff, iSup_le_iff]
    exact M.hasInjectiveDimensionLE_iff_forall_primeSpectrum n
  refine eq_of_forall_ge_iff (fun N ↦ ?_)
  induction N with
  | bot =>
    simp only [le_bot_iff, injectiveDimension_eq_bot_iff, ModuleCat.isZero_iff_subsingleton,
      iSup_eq_bot, ModuleCat.localizedModule, ← Equiv.subsingleton_congr (equivShrink _)]
    refine ⟨fun h p ↦ LocalizedModule.instSubsingleton _, fun h ↦ ?_⟩
    apply Module.subsingleton_of_localization_maximal (R := R)
      (fun p ↦ LocalizedModule p.primeCompl M) (fun p ↦ LocalizedModule.mkLinearMap p.primeCompl M)
    intro p hp
    exact h ⟨p, hp.isPrime⟩
  | coe N =>
    induction N with
    | top => simp
    | coe n => simpa using aux n

lemma injectiveDimension_eq_iSup_localizedModule_maximal [Small.{v, u} R] [IsNoetherianRing R]
    (M : ModuleCat.{v} R) : injectiveDimension M =
    ⨆ (p : MaximalSpectrum R), injectiveDimension (M.localizedModule p.1.primeCompl) := by
  have aux (n : ℕ) : injectiveDimension M ≤ n ↔ ⨆ (m : MaximalSpectrum R), injectiveDimension
    (M.localizedModule m.1.primeCompl) ≤ n := by
    simp only [injectiveDimension_le_iff, iSup_le_iff]
    exact M.hasInjectiveDimensionLE_iff_forall_maximalSpectrum n
  refine eq_of_forall_ge_iff (fun N ↦ ?_)
  induction N with
  | bot =>
    simp only [le_bot_iff, injectiveDimension_eq_bot_iff, ModuleCat.isZero_iff_subsingleton,
      iSup_eq_bot, ModuleCat.localizedModule, ← Equiv.subsingleton_congr (equivShrink _)]
    refine ⟨fun h p ↦ LocalizedModule.instSubsingleton _, fun h ↦ ?_⟩
    apply Module.subsingleton_of_localization_maximal (R := R)
      (fun p ↦ LocalizedModule p.primeCompl M) (fun p ↦ LocalizedModule.mkLinearMap p.primeCompl M)
    intro p hp
    exact h ⟨p, hp⟩
  | coe N =>
    induction N with
    | top => simp
    | coe n => simpa using aux n

end ModuleCat
