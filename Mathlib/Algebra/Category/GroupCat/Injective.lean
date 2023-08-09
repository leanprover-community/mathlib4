/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathlib.Algebra.Category.GroupCat.EpiMono
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Module.Injective
import Mathlib.CategoryTheory.Preadditive.Injective
import Mathlib.GroupTheory.Divisible
import Mathlib.RingTheory.PrincipalIdealDomain

#align_import algebra.category.Group.injective from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Injective objects in the category of abelian groups

In this file we prove that divisible groups are injective object in category of (additive) abelian
groups.

-/


open CategoryTheory

open Pointwise

universe u

variable (A : Type u) [AddCommGroup A]

set_option linter.uppercaseLean3 false

namespace AddCommGroupCat

theorem injective_of_injective_as_module [Injective (⟨A⟩ : ModuleCat ℤ)] :
    CategoryTheory.Injective (⟨A,inferInstance⟩ : AddCommGroupCat) :=
  { factors := fun {X} {Y} g f m => by
      let G : (⟨X⟩ : ModuleCat ℤ) ⟶ ⟨A⟩ :=
        { g with
          map_smul' := by
            intros
            dsimp
            rw [map_zsmul] }
      let F : (⟨X⟩ : ModuleCat ℤ) ⟶ ⟨Y⟩ :=
        { f with
          map_smul' := by
            intros
            dsimp
            rw [map_zsmul] }
      have : Mono F := by
        refine' ⟨fun {Z} α β eq1 => _⟩
        -- Porting note: trouble getting to ℤ-module from ModuleCat ℤ
        -- AddCommGroup.intModule not defeq to .isModule
        let α' : AddCommGroupCat.of Z ⟶ X := @LinearMap.toAddMonoidHom _ _ _ _ _ _ _ _ (_) _ _ α
        let β' : AddCommGroupCat.of Z ⟶ X := @LinearMap.toAddMonoidHom _ _ _ _ _ _ _ _ (_) _ _ β
        have eq2 : α' ≫ f = β' ≫ f := by
          ext x
          simp only [CategoryTheory.comp_apply, LinearMap.toAddMonoidHom_coe]
          simpa only [ModuleCat.coe_comp, LinearMap.coe_mk, Function.comp_apply] using
            FunLike.congr_fun eq1 x
        rw [cancel_mono] at eq2
        have : ⇑α' = ⇑β' := congrArg _ eq2
        ext x
        apply congrFun this _
      refine' ⟨(Injective.factorThru G F).toAddMonoidHom, _⟩
      ext x
      convert FunLike.congr_fun (Injective.comp_factorThru G F) x}
#align AddCommGroup.injective_of_injective_as_module AddCommGroupCat.injective_of_injective_as_module

theorem injective_as_module_of_injective_as_Ab [Injective (⟨A,inferInstance⟩ : AddCommGroupCat)] :
    Injective (⟨A⟩ : ModuleCat ℤ) :=
  { factors := fun {X} {Y} g f m => by
      let G : (⟨X,inferInstance⟩ : AddCommGroupCat) ⟶ ⟨A,inferInstance⟩ :=
        @LinearMap.toAddMonoidHom _ _ _ _ _ _ _ _ (_) _ _ g
      let F : (⟨X,inferInstance⟩ : AddCommGroupCat) ⟶ ⟨Y,inferInstance⟩ :=
        @LinearMap.toAddMonoidHom _ _ _ _ _ _ _ _ (_) (_) _ f
      have : Mono F := by
        rw [mono_iff_injective]
        intro _ _ h
        exact ((ModuleCat.mono_iff_injective f).mp m) h
      refine ⟨ @LinearMap.mk _ _ _ _ _ _ _ _ _ (_) _ (Injective.factorThru G F).toAddHom ?_ , ?_⟩
      change ∀ r, ∀ x, (Injective.factorThru G F).toFun _ = _ • (Injective.factorThru G F).toFun _
      · intro m x
        rw [AddMonoidHom.toFun_eq_coe, RingHom.id_apply]
        induction' m using Int.induction_on with n hn n hn
        · rw [zero_smul]
          convert map_zero (M := Y) (N := A) (F := Y →+ A) _
          -- Porting note: hell of non-defeq instances; somehow this worked
          refine @zero_smul ℤ Y (MonoidWithZero.toZero) (AddMonoid.toZero) ?_ x
          -- Porting note: was simp only [add_smul, map_add, hn, one_smul]
        · conv_rhs => rw [add_smul]
          rw [← hn, one_smul, ←map_add]
          congr
          convert @add_smul ℤ Y _ _ ?_ n 1 x
          refine @one_smul ℤ Y _ ?_ x|>.symm
          -- Porting note: was simp only [add_smul, map_add, hn, one_smul]
        · conv_rhs => rw [sub_smul]
          rw [← hn, one_smul, ←map_sub]
          congr
          convert @sub_smul ℤ Y _ _ ?_ (-n) 1 x
          refine @one_smul ℤ Y _ ?_ x|>.symm
      ext x
      have := congrFun (congrArg (fun H => H.toFun) (Injective.comp_factorThru G F)) x
      simp only [ModuleCat.coe_comp, Function.comp_apply] at this
      apply this }
#align AddCommGroup.injective_as_module_of_injective_as_Ab AddCommGroupCat.injective_as_module_of_injective_as_Ab

instance injective_of_divisible [DivisibleBy A ℤ] :
    CategoryTheory.Injective (⟨A,inferInstance⟩ : AddCommGroupCat) :=
  @injective_of_injective_as_module A _ <|
    @Module.injective_object_of_injective_module ℤ _ A _ _ <|
      Module.Baer.injective fun I g => by
        rcases IsPrincipalIdealRing.principal I with ⟨m, rfl⟩
        by_cases m_eq_zero : m = 0
        · subst m_eq_zero
          refine'
            ⟨{  toFun := _
                map_add' := _
                map_smul' := _ }, fun n hn => _⟩
          · intro _
            exact g 0
          · intro _ _
            simp only [map_zero, add_zero]
          · intro n1 _
            simp only [map_zero, smul_zero]
          · rw [Submodule.span_singleton_eq_bot.mpr rfl, Submodule.mem_bot] at hn
            simp only [hn, map_zero]
            symm
            convert map_zero g
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
            dsimp
            rw [mul_smul]
          · rw [Submodule.mem_span_singleton] at hn
            rcases hn with ⟨n, rfl⟩
            simp only [gm_eq, Algebra.id.smul_eq_mul, LinearMap.coe_mk]
            dsimp
            rw [mul_smul]
            -- Porting note: used to be able to just rw [Div...]
            have s := congrArg (fun l => n • l) <| DivisibleBy.div_cancel gₘ m_eq_zero
            dsimp at s
            rw [s, ← LinearMap.map_smul]
            congr
#align AddCommGroup.injective_of_divisible AddCommGroupCat.injective_of_divisible

end AddCommGroupCat
