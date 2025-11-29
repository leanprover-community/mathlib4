/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.RingTheory.Noetherian.Basic

/-!

# Ext Between Finitely Generated Module over Noetherian Ring is Finitely Generated

-/

@[expose] public section

universe v u

variable (R : Type u) [CommRing R]

open CategoryTheory Abelian

universe w

variable [UnivLE.{v, w}]

private instance [Small.{v} R] : CategoryTheory.HasExt.{w} (ModuleCat.{v} R) :=
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
    let S : ShortComplex (ModuleCat.{v} R) :=
    { f := ModuleCat.ofHom.{v} (LinearMap.ker f).subtype
      g := ModuleCat.ofHom.{v} f
      zero := by
        ext x
        simp }
    have S_exact' : Function.Exact S.f S.g := by
      intro x
      simp [S]
    have S_exact : S.ShortExact :=
    { exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mpr S_exact'
      mono_f := (ModuleCat.mono_iff_injective S.f).mpr (LinearMap.ker f).injective_subtype
      epi_g := (ModuleCat.epi_iff_surjective S.g).mpr surjf}
    let _ : Module.Finite R S.X₂ := by
      simp [S, Module.Finite.equiv (Shrink.linearEquiv R R).symm, Finite.of_fintype (Fin m)]
    let _ : Module.Free R (Shrink.{v, u} R) :=  Module.Free.of_equiv (Shrink.linearEquiv R R).symm
    let _ : Module.Free R S.X₂ := Module.Free.finsupp R (Shrink.{v, u} R) _
    have : Subsingleton (Ext S.X₂ M (n + 1)) :=
      subsingleton_of_forall_eq 0 Ext.eq_zero_of_projective
    have epi := (Ext.contravariant_sequence_exact₃' S_exact M n (n + 1) (add_comm 1 n)).epi_f
      ((AddCommGrpCat.of (Ext S.X₂ M (n + 1))).isZero_of_subsingleton.eq_zero_of_tgt _)
    have surj : Function.Surjective (S_exact.extClass.precomp M (add_comm 1 n)) :=
      (AddCommGrpCat.epi_iff_surjective _).mp epi
    let f : Ext S.X₁ M n →ₗ[R] Ext S.X₃ M (n + 1) :=
    { __ := S_exact.extClass.precomp M (add_comm 1 n)
      map_smul' r x := by simp }
    exact Module.Finite.of_surjective f surj
