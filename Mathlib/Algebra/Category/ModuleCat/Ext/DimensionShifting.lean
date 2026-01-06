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

universe v u

variable {R : Type u} [CommRing R]

variable {M : Type v} [AddCommGroup M] [Module R M] {N : Type v} [AddCommGroup N] [Module R N]

open CategoryTheory Abelian

/-- The standard short complex `0 → N → P → M → 0` with `P= R^{⊕M}` free. -/
noncomputable abbrev ModuleCat.projectiveShortComplex [Small.{v} R] (M : ModuleCat.{v} R) :
    ShortComplex (ModuleCat.{v} R) :=
  let e : Module.Basis M R (M →₀ Shrink.{v} R) :=
    ⟨Finsupp.mapRange.linearEquiv (Shrink.linearEquiv.{v} R R)⟩
  (e.constr ℕ id).shortComplexKer

theorem ModuleCat.shortExact_projectiveShortComplex [Small.{v} R] (M : ModuleCat.{v} R) :
    M.projectiveShortComplex.ShortExact := by
  apply LinearMap.shortExact_shortComplexKer
  refine fun m ↦ ⟨Finsupp.single m 1, ?_⟩
  simp [Module.Basis.constr_apply]

instance [Small.{v} R] (M : ModuleCat.{v} R) : Module.Free R M.projectiveShortComplex.X₂ :=
  Module.Free.finsupp R _ _

/-- Given an injective presentaion `M → I`, the short complex `0 → M → I → N → 0`. -/
noncomputable abbrev CategoryTheory.InjectivePresentation.shortComplex
    {M : ModuleCat.{v} R} (ip : InjectivePresentation M) : ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.mk ip.3 (Limits.cokernel.π ip.3) (Limits.cokernel.condition ip.3)

theorem CategoryTheory.InjectivePresentation.shortExact_shortComplex {M : ModuleCat.{v} R}
    (ip : InjectivePresentation M) : ip.shortComplex.ShortExact :=
  { exact := ShortComplex.exact_cokernel ip.3
    mono_f := ip.4
    epi_g := Limits.coequalizer.π_epi }

instance {M : ModuleCat.{v} R} (ip : InjectivePresentation M) : Injective ip.shortComplex.X₂ := ip.2

/-- The connection maps in the contravariant long exact sequence of `Ext` are surjective if
the middle term of the short exact sequence is projective. -/
theorem precomp_extClass_surjective_of_projective_X₂ [Small.{v} R]
    (M : ModuleCat.{v} R) {S : ShortComplex (ModuleCat.{v} R)} (h : S.ShortExact) (n : ℕ)
    [Projective S.X₂] : Function.Surjective (h.extClass.precomp M (add_comm 1 n)) := by
  let _ := Ext.subsingleton_of_projective S.X₂ M
  have epi := (Ext.contravariant_sequence_exact₃' h M n (n + 1) (add_comm 1 n)).epi_f
    ((AddCommGrpCat.of (Ext S.X₂ M (n + 1))).isZero_of_subsingleton.eq_zero_of_tgt _)
  exact (AddCommGrpCat.epi_iff_surjective _).mp epi

/-- The connection maps in the covariant long exact sequence of `Ext` are surjective if
the middle term of the short exact sequence is injective. -/
theorem postcomp_extClass_surjective_of_projective_X₂ [Small.{v} R]
    {S : ShortComplex (ModuleCat.{v} R)} (h : S.ShortExact) (M : ModuleCat.{v} R) (n : ℕ)
    [Injective S.X₂] : Function.Surjective (h.extClass.postcomp M (rfl : n + 1 = n + 1)) := by
  let _ := Ext.subsingleton_of_injective M S.X₂
  have epi := (Ext.covariant_sequence_exact₁' M h n (n + 1) rfl).epi_f
    ((AddCommGrpCat.of (Ext M S.X₂ (n + 1))).isZero_of_subsingleton.eq_zero_of_tgt _)
  exact (AddCommGrpCat.epi_iff_surjective _).mp epi
