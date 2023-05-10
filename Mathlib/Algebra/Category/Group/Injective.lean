/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang

! This file was ported from Lean 3 source module algebra.category.Group.injective
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Category.Group.EpiMono
import Mathbin.Algebra.Category.Module.EpiMono
import Mathbin.Algebra.Module.Injective
import Mathbin.CategoryTheory.Preadditive.Injective
import Mathbin.GroupTheory.Divisible
import Mathbin.RingTheory.PrincipalIdealDomain

/-!
# Injective objects in the category of abelian groups

In this file we prove that divisible groups are injective object in category of (additive) abelian
groups.

-/


open CategoryTheory

open Pointwise

universe u

variable (A : Type u) [AddCommGroup A]

namespace AddCommGroupCat

theorem injective_of_injective_as_module [Injective (⟨A⟩ : ModuleCat ℤ)] :
    CategoryTheory.Injective (⟨A⟩ : AddCommGroupCat) :=
  {
    Factors := fun X Y g f m => by
      skip
      let G : (⟨X⟩ : ModuleCat ℤ) ⟶ ⟨A⟩ :=
        { g with
          map_smul' := by
            intros
            rw [RingHom.id_apply, g.to_fun_eq_coe, map_zsmul] }
      let F : (⟨X⟩ : ModuleCat ℤ) ⟶ ⟨Y⟩ :=
        { f with
          map_smul' := by
            intros
            rw [RingHom.id_apply, f.to_fun_eq_coe, map_zsmul] }
      have : mono F := by
        refine' ⟨fun Z α β eq1 => _⟩
        let α' : AddCommGroupCat.of Z ⟶ X := α.to_add_monoid_hom
        let β' : AddCommGroupCat.of Z ⟶ X := β.to_add_monoid_hom
        have eq2 : α' ≫ f = β' ≫ f := by
          ext
          simp only [CategoryTheory.comp_apply, LinearMap.toAddMonoidHom_coe]
          simpa only [ModuleCat.coe_comp, LinearMap.coe_mk, Function.comp_apply] using
            FunLike.congr_fun eq1 x
        rw [cancel_mono] at eq2
        ext
        simpa only using FunLike.congr_fun eq2 x
      refine' ⟨(injective.factor_thru G F).toAddMonoidHom, _⟩
      ext
      convert FunLike.congr_fun (injective.comp_factor_thru G F) x }
#align AddCommGroup.injective_of_injective_as_module AddCommGroupCat.injective_of_injective_as_module

theorem injective_as_module_of_injective_as_Ab [Injective (⟨A⟩ : AddCommGroupCat)] :
    Injective (⟨A⟩ : ModuleCat ℤ) :=
  {
    Factors := fun X Y g f m => by
      skip
      let G : (⟨X⟩ : AddCommGroupCat) ⟶ ⟨A⟩ := g.to_add_monoid_hom
      let F : (⟨X⟩ : AddCommGroupCat) ⟶ ⟨Y⟩ := f.to_add_monoid_hom
      have : mono F := by
        rw [mono_iff_injective]
        intro _ _ h
        exact ((ModuleCat.mono_iff_injective f).mp m) h
      refine' ⟨{ injective.factor_thru G F with map_smul' := _ }, _⟩
      · intro m x
        rw [AddMonoidHom.toFun_eq_coe, RingHom.id_apply]
        induction' m using Int.induction_on with n hn n hn
        · rw [zero_smul]
          convert map_zero _
          convert zero_smul _ x
        · simp only [add_smul, map_add, hn, one_smul]
        · simp only [sub_smul, map_sub, hn, one_smul]
      ext
      convert FunLike.congr_fun (injective.comp_factor_thru G F) x }
#align AddCommGroup.injective_as_module_of_injective_as_Ab AddCommGroupCat.injective_as_module_of_injective_as_Ab

instance injective_of_divisible [DivisibleBy A ℤ] :
    CategoryTheory.Injective (⟨A⟩ : AddCommGroupCat) :=
  @injective_of_injective_as_module A _ <|
    @Module.injective_object_of_injective_module ℤ _ A _ _ <|
      Module.Baer.injective fun I g =>
        by
        rcases IsPrincipalIdealRing.principal I with ⟨m, rfl⟩
        by_cases m_eq_zero : m = 0
        · subst m_eq_zero
          refine'
            ⟨{  toFun := _
                map_add' := _
                map_smul' := _ }, fun n hn => _⟩
          · intro n
            exact g 0
          · intro n1 n2
            simp only [map_zero, add_zero]
          · intro n1 n2
            simp only [map_zero, smul_zero]
          · rw [submodule.span_singleton_eq_bot.mpr rfl, Submodule.mem_bot] at hn
            simp only [hn, map_zero]
            symm
            convert map_zero _
        · set gₘ := g ⟨m, Submodule.subset_span (Set.mem_singleton _)⟩ with gm_eq
          refine'
            ⟨{  toFun := _
                map_add' := _
                map_smul' := _ }, fun n hn => _⟩
          · intro n
            exact n • DivisibleBy.div gₘ m
          · intro n1 n2
            simp only [add_smul]
          · intro n1 n2
            rw [RingHom.id_apply, smul_eq_mul, mul_smul]
          · rw [Submodule.mem_span_singleton] at hn
            rcases hn with ⟨n, rfl⟩
            simp only [gm_eq, Algebra.id.smul_eq_mul, LinearMap.coe_mk]
            rw [mul_smul, DivisibleBy.div_cancel (g ⟨m, _⟩) m_eq_zero, ← LinearMap.map_smul]
            congr
#align AddCommGroup.injective_of_divisible AddCommGroupCat.injective_of_divisible

end AddCommGroupCat

