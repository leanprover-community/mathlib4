/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
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
abbrev LinearMap.shortComplexG (f : M →ₗ[R] N) : ShortComplex (ModuleCat.{v} R) where
  f := ModuleCat.ofHom.{v} (LinearMap.ker f).subtype
  g := ModuleCat.ofHom.{v} f
  zero := by ext; simp

theorem LinearMap.shortExact_shortComplexG {f : M →ₗ[R] N} (h : Function.Surjective f) :
    f.shortComplexG.ShortExact where
  exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    fun _ ↦ by simp [shortComplexG]
  mono_f := (ModuleCat.mono_iff_injective _).mpr (LinearMap.ker f).injective_subtype
  epi_g := (ModuleCat.epi_iff_surjective _).mpr h

instance [UnivLE.{v, w}] [Small.{v} R] (M N : ModuleCat.{v} R) [Projective M] (n : ℕ) :
    Subsingleton (Ext.{w} M N (n + 1)) :=
  subsingleton_of_forall_eq 0 Ext.eq_zero_of_projective

/-- The connection maps in the contravariant long exact sequence of `Ext` are surjective if
the middle term of the short exact sequence is projective. -/
theorem extClass_precomp_surjective_of_projective_X₂ [UnivLE.{v, w}] [Small.{v} R]
    (M : ModuleCat.{v} R) {S : ShortComplex (ModuleCat.{v} R)} (h : S.ShortExact) (n : ℕ)
    [Projective S.X₂] : Function.Surjective (h.extClass.precomp M (add_comm 1 n)) := by
  have epi := (Ext.contravariant_sequence_exact₃' h M n (n + 1) (add_comm 1 n)).epi_f
    ((AddCommGrpCat.of (Ext S.X₂ M (n + 1))).isZero_of_subsingleton.eq_zero_of_tgt _)
  exact (AddCommGrpCat.epi_iff_surjective _).mp epi
