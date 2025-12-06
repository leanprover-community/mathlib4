/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.RingTheory.Noetherian.Basic

/-!

# Dimension Shifting

-/

@[expose] public section

universe w v u

variable (R : Type u) [CommRing R]

variable (M : Type v) [AddCommGroup M] [Module R M] (N : Type v) [AddCommGroup N] [Module R N]

open CategoryTheory Abelian

instance Module.free_shrink [Module.Free R M] [Small.{w} M] : Module.Free R (Shrink.{w} M) :=
  Module.Free.of_equiv (Shrink.linearEquiv R M).symm

instance Module.finite_shrink [Module.Finite R M] [Small.{w} M] : Module.Finite R (Shrink.{w} M) :=
  Module.Finite.equiv (Shrink.linearEquiv R M).symm

theorem Module.exists_finite_presentation [Small.{v} R] (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] :
    ∃ (P : Type v) (_ : AddCommGroup P) (_ : Module R P) (_ : Module.Free R P)
      (_ : Module.Finite R P) (f : P →ₗ[R] M), Function.Surjective f := by
  rcases Module.Finite.exists_fin' R M with ⟨m, f', hf'⟩
  let f := f'.comp ((Finsupp.mapRange.linearEquiv (Shrink.linearEquiv.{v} R R)).trans
      (Finsupp.linearEquivFunOnFinite R R (Fin m))).1
  use (Fin m →₀ Shrink.{v, u} R), inferInstance, inferInstance, inferInstance, inferInstance, f
  simpa [f] using hf'

variable {R M N}

/-- Given a linear map `f : M → N`, we can obtain a short complex `ker(f) → M → N`. -/
abbrev LinearMap.shortComplexKer (f : M →ₗ[R] N) : ShortComplex (ModuleCat.{v} R) where
  f := ModuleCat.ofHom.{v} (LinearMap.ker f).subtype
  g := ModuleCat.ofHom.{v} f
  zero := by ext; simp

theorem LinearMap.shortExact_shortComplexKer {f : M →ₗ[R] N} (h : Function.Surjective f) :
    f.shortComplexKer.ShortExact where
  exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    fun _ ↦ by simp [shortComplexKer]
  mono_f := (ModuleCat.mono_iff_injective _).mpr (LinearMap.ker f).injective_subtype
  epi_g := (ModuleCat.epi_iff_surjective _).mpr h

/-- The standard short complex `N → P → M` with `P` projective. -/
noncomputable abbrev ModuleCat.projective_shortComplex [Small.{v} R] (M : ModuleCat.{v} R) :
    ShortComplex (ModuleCat.{v} R) :=
  let e : Module.Basis M R (M →₀ Shrink.{v} R) :=
    ⟨Finsupp.mapRange.linearEquiv (Shrink.linearEquiv.{v} R R)⟩
  (e.constr ℕ id).shortComplexKer

theorem ModuleCat.projective_shortComplex_shortExact [Small.{v} R] (M : ModuleCat.{v} R) :
    M.projective_shortComplex.ShortExact := by
  apply LinearMap.shortExact_shortComplexKer
  refine fun m ↦ ⟨Finsupp.single m 1, ?_⟩
  simp [Module.Basis.constr_apply]

instance [Small.{v} R] (M : ModuleCat.{v} R) : Module.Free R M.projective_shortComplex.X₂ :=
  Module.Free.finsupp R _ _

/-- The standard short complex `N → P → M` with `P` projective. -/
noncomputable abbrev CategoryTheory.InjectivePresentation.shortComplex
    {M : ModuleCat.{v} R} (ip : InjectivePresentation M) : ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.mk ip.3 (Limits.cokernel.π ip.3) (Limits.cokernel.condition ip.3)

theorem CategoryTheory.InjectivePresentation.shortComplex_shortExact {M : ModuleCat.{v} R}
    (ip : InjectivePresentation M) : ip.shortComplex.ShortExact :=
  { exact := ShortComplex.exact_cokernel ip.3
    mono_f := ip.4
    epi_g := Limits.coequalizer.π_epi }

instance {M : ModuleCat.{v} R} (ip : InjectivePresentation M) : Injective ip.shortComplex.X₂ := ip.2

/-- The connection maps in the contravariant long exact sequence of `Ext` are surjective if
the middle term of the short exact sequence is projective. -/
theorem extClass_precomp_surjective_of_projective_X₂ [Small.{v} R]
    (M : ModuleCat.{v} R) {S : ShortComplex (ModuleCat.{v} R)} (h : S.ShortExact) (n : ℕ)
    [Projective S.X₂] : Function.Surjective (h.extClass.precomp M (add_comm 1 n)) := by
  let _ := Ext.subsingleton_of_projective S.X₂ M
  have epi := (Ext.contravariant_sequence_exact₃' h M n (n + 1) (add_comm 1 n)).epi_f
    ((AddCommGrpCat.of (Ext S.X₂ M (n + 1))).isZero_of_subsingleton.eq_zero_of_tgt _)
  exact (AddCommGrpCat.epi_iff_surjective _).mp epi

/-- The connection maps in the covariant long exact sequence of `Ext` are surjective if
the middle term of the short exact sequence is injective. -/
theorem extClass_postcomp_surjective_of_projective_X₂ [Small.{v} R]
    {S : ShortComplex (ModuleCat.{v} R)} (h : S.ShortExact) (M : ModuleCat.{v} R) (n : ℕ)
    [Injective S.X₂] : Function.Surjective (h.extClass.postcomp M (rfl : n + 1 = n + 1)) := by
  let _ := Ext.subsingleton_of_injective M S.X₂
  have epi := (Ext.covariant_sequence_exact₁' M h n (n + 1) rfl).epi_f
    ((AddCommGrpCat.of (Ext M S.X₂ (n + 1))).isZero_of_subsingleton.eq_zero_of_tgt _)
  exact (AddCommGrpCat.epi_iff_surjective _).mp epi
