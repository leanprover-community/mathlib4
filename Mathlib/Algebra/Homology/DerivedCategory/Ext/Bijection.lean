/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.FiveLemma
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
/-!

# Bijections Between Ext

In this file, we prove that map between `Ext` induced by fully faithful exact functor with certain
conditions added is bijection.

-/

universe w w' u u' v v'

namespace CategoryTheory

open Limits Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

lemma Abelian.Ext.mapExt_zero [HasExt.{w} C] [HasExt.{w'} D] (X Y : C) :
    F.mapExt X Y 0 = Ext.homEquiv₀.symm ∘ F.map ∘ Ext.homEquiv₀ := by
  ext x
  rcases (Ext.mk₀_bijective X Y).2 x with ⟨y, hy⟩
  simp [← hy, Ext.mapExt_mk₀_eq_mk₀_map, Ext.homEquiv₀]

open Ext

lemma bijective_of_preservesProjectiveObjects (h : F.FullyFaithful) [HasExt.{w} C] [HasExt.{w'} D]
    [EnoughProjectives C] [F.PreservesProjectiveObjects] (X Y : C) (n : ℕ) :
    Function.Bijective (F.mapExt X Y n) := by
  induction n generalizing X
  · simpa [Ext.mapExt_zero] using Functor.FullyFaithful.map_bijective h X Y
  · rename_i n bij
    rcases EnoughProjectives.presentation X with ⟨⟨P, p⟩⟩
    let S := ShortComplex.mk (kernel.ι p) p (kernel.condition p)
    have S_exact : S.ShortExact := {
      exact := ShortComplex.exact_kernel p
      mono_f := equalizer.ι_mono }
    have FS_exact : (S.map F).ShortExact := S_exact.map_of_exact F
    let _ : Projective (S.map F).X₂ := Functor.PreservesProjectiveObjects.projective_obj ‹_›
    let f : Ext S.X₂ Y n →+ Ext S.X₁ Y n := (mk₀ S.f).precomp Y (zero_add n)
    let g : Ext S.X₁ Y n →+ Ext S.X₃ Y (n + 1) := S_exact.extClass.precomp Y (add_comm 1 n)
    have exac1 : Function.Exact f g := (ShortComplex.ab_exact_iff_function_exact  _).mp
      (Ext.contravariant_sequence_exact₁' S_exact Y n (n + 1) (add_comm 1 n))
    have isz1 : Limits.IsZero (AddCommGrpCat.of (Ext S.X₂ Y (n + 1))) :=
      @AddCommGrpCat.isZero_of_subsingleton _
        (subsingleton_of_forall_eq 0 Ext.eq_zero_of_projective)
    have surj1 : Function.Surjective g := (AddCommGrpCat.epi_iff_surjective _).mp
      ((Ext.contravariant_sequence_exact₃' S_exact Y n (n + 1) (add_comm 1 n)).epi_f
      (isz1.eq_zero_of_tgt _))
    let f' : Ext (S.map F).X₂ (F.obj Y) n →+ Ext (S.map F).X₁ (F.obj Y) n :=
      (mk₀ (S.map F).f).precomp (F.obj Y) (zero_add n)
    let g' : Ext (S.map F).X₁ (F.obj Y) n →+ Ext (S.map F).X₃ (F.obj Y) (n + 1) :=
      FS_exact.extClass.precomp (F.obj Y) (add_comm 1 n)
    have exac2 : Function.Exact f' g' := (ShortComplex.ab_exact_iff_function_exact  _).mp
      (Ext.contravariant_sequence_exact₁' FS_exact (F.obj Y) n (n + 1) (add_comm 1 n))
    have isz2 : Limits.IsZero (AddCommGrpCat.of (Ext (S.map F).X₂ (F.obj Y) (n + 1))) :=
      @AddCommGrpCat.isZero_of_subsingleton _
        (subsingleton_of_forall_eq 0 Ext.eq_zero_of_projective)
    have surj2 : Function.Surjective g' := (AddCommGrpCat.epi_iff_surjective _).mp
      ((Ext.contravariant_sequence_exact₃' FS_exact (F.obj Y) n (n + 1) (add_comm 1 n)).epi_f
      (isz2.eq_zero_of_tgt _))
    apply AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact f g f' g'
      (F.mapExtAddHom S.X₂ Y n) (F.mapExtAddHom S.X₁ Y n) (F.mapExtAddHom S.X₃ Y (n + 1)) _ _
      exac1 exac2 (bij S.X₂).2 (bij S.X₁) surj1 surj2
    · ext x
      simp [f, f', Ext.mapExt_comp_eq_comp_mapExt, Ext.mapExt_mk₀_eq_mk₀_map]
    · ext x
      simp [g, g', Ext.mapExt_comp_eq_comp_mapExt, Ext.mapExt_extClass_eq_extClass_map]

lemma bijective_of_preservesInjectiveObjects (h : F.FullyFaithful) [HasExt.{w} C] [HasExt.{w'} D]
    [EnoughInjectives C] [F.PreservesInjectiveObjects] (X Y : C) (n : ℕ) :
    Function.Bijective (F.mapExt X Y n) := by
  induction n generalizing Y
  · simpa [Ext.mapExt_zero] using Functor.FullyFaithful.map_bijective h X Y
  · rename_i n bij
    rcases EnoughInjectives.presentation Y with ⟨⟨I, _, i⟩⟩
    let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
    have S_exact : S.ShortExact := {
      exact := ShortComplex.exact_cokernel i
      epi_g := coequalizer.π_epi }
    have FS_exact : (S.map F).ShortExact := S_exact.map_of_exact F
    let _ : Injective (S.map F).X₂ := Functor.PreservesInjectiveObjects.injective_obj ‹_›
    let f : Ext X S.X₂ n →+ Ext X S.X₃ n := (mk₀ S.g).postcomp X (add_zero n)
    let g : Ext X S.X₃ n →+ Ext X S.X₁ (n + 1) := S_exact.extClass.postcomp X rfl
    have exac1 : Function.Exact f g := (ShortComplex.ab_exact_iff_function_exact  _).mp
      (Ext.covariant_sequence_exact₃' X S_exact n (n + 1) rfl)
    have isz1 : Limits.IsZero (AddCommGrpCat.of (Ext X S.X₂ (n + 1))) :=
      @AddCommGrpCat.isZero_of_subsingleton _
        (subsingleton_of_forall_eq 0 Ext.eq_zero_of_injective)
    have surj1 : Function.Surjective g := (AddCommGrpCat.epi_iff_surjective _).mp
      ((Ext.covariant_sequence_exact₁' X S_exact n (n + 1) rfl).epi_f
      (isz1.eq_zero_of_tgt _))
    let f' : Ext (F.obj X) (S.map F).X₂ n →+ Ext (F.obj X) (S.map F).X₃ n :=
      (mk₀ (S.map F).g).postcomp (F.obj X) (add_zero n)
    let g' : Ext (F.obj X) (S.map F).X₃ n →+ Ext (F.obj X) (S.map F).X₁ (n + 1) :=
      FS_exact.extClass.postcomp (F.obj X) rfl
    have exac2 : Function.Exact f' g' := (ShortComplex.ab_exact_iff_function_exact  _).mp
      (Ext.covariant_sequence_exact₃' (F.obj X) FS_exact n (n + 1) rfl)
    have isz2 : Limits.IsZero (AddCommGrpCat.of (Ext (F.obj X) (S.map F).X₂ (n + 1))) :=
      @AddCommGrpCat.isZero_of_subsingleton _
        (subsingleton_of_forall_eq 0 Ext.eq_zero_of_injective)
    have surj2 : Function.Surjective g' := (AddCommGrpCat.epi_iff_surjective _).mp
      ((Ext.covariant_sequence_exact₁' (F.obj X) FS_exact n (n + 1) rfl).epi_f
      (isz2.eq_zero_of_tgt _))
    apply AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact f g f' g'
      (F.mapExtAddHom X S.X₂ n) (F.mapExtAddHom X S.X₃ n) (F.mapExtAddHom X S.X₁ (n + 1)) _ _
      exac1 exac2 (bij S.X₂).2 (bij S.X₃) surj1 surj2
    · ext x
      simp [f, f', Ext.mapExt_comp_eq_comp_mapExt, Ext.mapExt_mk₀_eq_mk₀_map]
    · ext x
      simp [g, g', Ext.mapExt_comp_eq_comp_mapExt, Ext.mapExt_extClass_eq_extClass_map]

end CategoryTheory
