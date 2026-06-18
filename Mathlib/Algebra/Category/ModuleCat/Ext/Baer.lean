/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Abelian.Injective.Dimension
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-!

# Baer's criterion for injective dimension

Baer's criterion says that an `R`-module `M` is injective iff every `R`-linear map
`I →ₗ[R] M` from an ideal `I` of `R` extends to a map `R →ₗ[R] M`.

This file reformulates that extension condition as the vanishing of `Ext (R ⧸ I) M 1`.
It then uses dimension shifting to give a criterion for injective dimension: to prove that
`M` has injective dimension `< n`, it suffices to show that `Ext (R ⧸ I) M n` vanishes for
all ideals `I`.

The statements use `Shrink` because `R`, its ideals, and its quotients may live in a larger
universe than `ModuleCat.{v} R`.

## Main results

* `ModuleCat.ext_quotient_one_subsingleton_iff`: `Ext (R ⧸ I) M 1` vanishes iff every
  linear map `I →ₗ[R] M` extends to `R →ₗ[R] M`.
* `ModuleCat.injective_of_subsingleton_ext_quotient_one`: if `Ext (R ⧸ I) M 1` vanishes
  for all ideals `I`, then `M` is injective.
* `ModuleCat.hasInjectiveDimensionLT_of_quotients`: if `Ext (R ⧸ I) M n` vanishes for all
  ideals `I`, then `M` has injective dimension `< n`.

-/

@[expose] public section

universe u v

variable {R : Type u} [CommRing R]

open CategoryTheory Abelian

namespace ModuleCat

/-- The vanishing of `Ext (R ⧸ I) M 1` is equivalent to Baer's extension property
for maps `I →ₗ[R] M`. -/
lemma ext_quotient_one_subsingleton_iff [Small.{v} R] (M : ModuleCat.{v} R) (I : Ideal R) :
    Subsingleton (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M 1) ↔
    ∀ g : I →ₗ[R] M, ∃ g' : R →ₗ[R] M,
      ∀ (x : R) (mem : x ∈ I), g' x = g ⟨x, mem⟩ := by
  -- The short complex `I → R → R ⧸ I`, with all three terms moved into universe `v`.
  -- This avoids universe issues when comparing it with `Ext` in `ModuleCat.{v} R`.
  have exact : Function.Exact I.subtype I.mkQ := LinearMap.exact_subtype_mkQ I
  let S := ModuleCat.shortComplexOfConj (Shrink.linearEquiv R I) (Shrink.linearEquiv R R)
    (Shrink.linearEquiv R (R ⧸ I)) _ _ exact.linearMap_comp_eq_zero
  -- The complex `I → R → R ⧸ I` is short exact, after shrinking universes.
  have S_exact : S.ShortExact :=
    ModuleCat.shortComplexOfConj_shortExact _ _ _ _ _ exact I.subtype_injective I.mkQ_surjective
  rw [Ext.one_subsingleton_iff_of_projective M S S_exact (by dsimp [S]; infer_instance)]
  -- Reduce the vanishing of `Ext (R ⧸ I) M 1` to surjectivity of
  -- `Ext R M 0 → Ext I M 0`, keeping track of the universe-shrinking equivalences.
  refine ⟨fun h ↦ fun g ↦ ?_, fun h ↦ fun e ↦ ?_⟩
  · -- Interpret `g` as an element of `Ext I M 0` and lift it across `Ext R M 0 → Ext I M 0`.
    obtain ⟨f', hf'⟩ := h
      (Ext.mk₀ (ModuleCat.ofHom (g.comp (Shrink.linearEquiv R I).toLinearMap)))
    rw [Ext.bilinearComp_apply_apply, ← Ext.mk₀_addEquiv₀_apply f',
      Ext.mk₀_comp_mk₀] at hf'
    use (Ext.addEquiv₀ f').hom.comp (Shrink.linearEquiv R R).symm.toLinearMap
    intro x hx
    have := ConcreteCategory.congr_hom ((Ext.mk₀_bijective _ _).1 hf')
      ((Shrink.linearEquiv R I).symm ⟨x, hx⟩)
    simpa [S]
  · -- Conversely, extend the map represented by `e` and turn the extension back into `Ext⁰`.
    obtain ⟨g', hg'⟩ := h
      ((Ext.addEquiv₀ e).hom.comp (Shrink.linearEquiv R I).symm.toLinearMap)
    use Ext.mk₀ (ModuleCat.ofHom (g'.comp (Shrink.linearEquiv R R).toLinearMap))
    rw [Ext.bilinearComp_apply_apply, Ext.mk₀_comp_mk₀, ← Ext.mk₀_addEquiv₀_apply e]
    congr
    ext x
    simp_all [S]

/-- Baer's criterion in Ext form: if `Ext (R ⧸ I) M 1` vanishes for every ideal `I`,
then `M` is injective. -/
lemma injective_of_subsingleton_ext_quotient_one [Small.{v} R] (M : ModuleCat.{v} R)
    (h : ∀ (I : Ideal R), Subsingleton (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M 1)) :
    Injective M := by
  rw [← Module.injective_iff_injective_object, ← Module.Baer.iff_injective]
  exact fun I ↦ (ext_quotient_one_subsingleton_iff M I).mp (h I)

attribute [local instance] Ext.subsingleton_of_injective in
open Limits in
/-- If `Ext (R ⧸ I) M (n + 1)` vanishes for every ideal `I`, then `M` has injective
dimension at most `n`. -/
lemma hasInjectiveDimensionLE_of_quotients [Small.{v} R] (M : ModuleCat.{v} R) (n : ℕ)
    (h : ∀ I : Ideal R, Subsingleton (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M (n + 1))) :
    HasInjectiveDimensionLE M n := by
  induction n generalizing M with
  | zero =>
    -- The case `n = 0` is exactly the Ext form of Baer's criterion.
    have : Injective M := injective_of_subsingleton_ext_quotient_one M h
    infer_instance
  | succ n ih =>
    -- Dimension shifting reduces the statement for `M` to
    -- the cokernel of an injective presentation.
    let ip : InjectivePresentation M := Classical.arbitrary _
    refine ip.shortExact_shortComplex.hasInjectiveDimensionLT_X₁ _
      (ih _ (fun I ↦ subsingleton_of_forall_eq 0 (fun x₃ ↦ ?_))) inferInstance
    obtain ⟨x₂, rfl⟩ := Ext.covariant_sequence_exact₃ _ ip.shortExact_shortComplex x₃ rfl
      (by subsingleton)
    simp [Subsingleton.elim x₂ 0]

/-- The zeroth Ext group from `R ⧸ ⊥` is canonically equivalent to the underlying module. -/
private noncomputable def extQuotientBotZeroEquiv [Small.{v} R] (M : ModuleCat.{v} R) :
    (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ (⊥ : Ideal R)))) M 0) ≃ M :=
  (Ext.homEquiv₀.trans ModuleCat.homEquiv).trans ((((Shrink.linearEquiv _ _).trans
    (Submodule.quotEquivOfEqBot _ rfl)).congrLeft M R).trans
      (LinearMap.ringLmapEquivSelf R R M)).toEquiv

/-- If `Ext⁰(R ⧸ ⊥, M)` is a subsingleton, then `M` is a subsingleton. -/
private lemma subsingleton_of_ext_quotient_bot_zero [Small.{v} R] (M : ModuleCat.{v} R)
    (h : Subsingleton (Ext (of R (Shrink.{v} (R ⧸ (⊥ : Ideal R)))) M 0)) :
    Subsingleton M := by
  rw [← (extQuotientBotZeroEquiv (R := R) M).subsingleton_congr]
  exact h

/-- If `Ext (R ⧸ I) M n` vanishes for every ideal `I`, then `M` has injective dimension
strictly less than `n`. -/
lemma hasInjectiveDimensionLT_of_quotients [Small.{v} R] (M : ModuleCat.{v} R) (n : ℕ)
    (h : ∀ I : Ideal R, Subsingleton (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M n)) :
    HasInjectiveDimensionLT M n := by
  match n with
  | 0 =>
    apply Limits.IsZero.hasInjectiveDimensionLT_zero
    rw [ModuleCat.isZero_iff_subsingleton]
    exact subsingleton_of_ext_quotient_bot_zero M (h ⊥)
  | n + 1 => exact hasInjectiveDimensionLE_of_quotients M n h

end ModuleCat
