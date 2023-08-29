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
      -- ⊢ f ≫ LinearMap.toAddMonoidHom (Injective.factorThru G F) = g
      ext x
      -- ⊢ ↑(f ≫ LinearMap.toAddMonoidHom (Injective.factorThru G F)) x = ↑g x
      convert FunLike.congr_fun (Injective.comp_factorThru G F) x}
      -- 🎉 no goals
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
      -- ⊢ ∀ (r : ℤ) (x : ↑Y), AddHom.toFun (↑(Injective.factorThru G F)) (r • x) = ↑(R …
      change ∀ r, ∀ x, (Injective.factorThru G F).toFun _ = _ • (Injective.factorThru G F).toFun _
      -- ⊢ ∀ (r : ℤ) (x : ↑Y), ZeroHom.toFun (↑(Injective.factorThru G F)) (r • x) = ↑( …
      · intro m x
        -- ⊢ ZeroHom.toFun (↑(Injective.factorThru G F)) (m • x) = ↑(RingHom.id ℤ) m • Ze …
        rw [AddMonoidHom.toFun_eq_coe, RingHom.id_apply]
        -- ⊢ ↑(Injective.factorThru G F) (m • x) = m • ↑(Injective.factorThru G F) x
        induction' m using Int.induction_on with n hn n hn
        · rw [zero_smul]
          -- ⊢ ↑(Injective.factorThru G F) (0 • x) = 0
          convert map_zero (M := Y) (N := A) (F := Y →+ A) _
          -- ⊢ 0 • x = 0
          -- Porting note: hell of non-defeq instances; somehow this worked
          refine @zero_smul ℤ Y (MonoidWithZero.toZero) (AddMonoid.toZero) ?_ x
          -- 🎉 no goals
          -- Porting note: was simp only [add_smul, map_add, hn, one_smul]
        · conv_rhs => rw [add_smul]
          -- ⊢ ↑(Injective.factorThru G F) ((↑n + 1) • x) = ↑n • ↑(Injective.factorThru G F …
          rw [← hn, one_smul, ←map_add]
          -- ⊢ ↑(Injective.factorThru G F) ((↑n + 1) • x) = ↑(Injective.factorThru G F) (↑n …
          congr
          -- ⊢ (↑n + 1) • x = ↑n • x + x
          convert @add_smul ℤ Y _ _ ?_ n 1 x
          -- ⊢ x = 1 • x
          refine @one_smul ℤ Y _ ?_ x|>.symm
          -- 🎉 no goals
          -- Porting note: was simp only [add_smul, map_add, hn, one_smul]
        · conv_rhs => rw [sub_smul]
          -- ⊢ ↑(Injective.factorThru G F) ((-↑n - 1) • x) = -↑n • ↑(Injective.factorThru G …
          rw [← hn, one_smul, ←map_sub]
          -- ⊢ ↑(Injective.factorThru G F) ((-↑n - 1) • x) = ↑(Injective.factorThru G F) (- …
          congr
          -- ⊢ (-↑n - 1) • x = -↑n • x - x
          convert @sub_smul ℤ Y _ _ ?_ (-n) 1 x
          -- ⊢ x = 1 • x
          refine @one_smul ℤ Y _ ?_ x|>.symm
          -- 🎉 no goals
      ext x
      -- ⊢ ↑(f ≫ { toAddHom := ↑(Injective.factorThru G F), map_smul' := (_ : ∀ (r : ℤ) …
      have := congrFun (congrArg (fun H => H.toFun) (Injective.comp_factorThru G F)) x
      -- ⊢ ↑(f ≫ { toAddHom := ↑(Injective.factorThru G F), map_smul' := (_ : ∀ (r : ℤ) …
      simp only [ModuleCat.coe_comp, Function.comp_apply] at this
      -- ⊢ ↑(f ≫ { toAddHom := ↑(Injective.factorThru G F), map_smul' := (_ : ∀ (r : ℤ) …
      apply this }
      -- 🎉 no goals
#align AddCommGroup.injective_as_module_of_injective_as_Ab AddCommGroupCat.injective_as_module_of_injective_as_Ab

instance injective_of_divisible [DivisibleBy A ℤ] :
    CategoryTheory.Injective (⟨A,inferInstance⟩ : AddCommGroupCat) :=
  @injective_of_injective_as_module A _ <|
    @Module.injective_object_of_injective_module ℤ _ A _ _ <|
      Module.Baer.injective fun I g => by
        rcases IsPrincipalIdealRing.principal I with ⟨m, rfl⟩
        -- ⊢ ∃ g', ∀ (x : ℤ) (mem : x ∈ Submodule.span ℤ {m}), ↑g' x = ↑g { val := x, pro …
        by_cases m_eq_zero : m = 0
        -- ⊢ ∃ g', ∀ (x : ℤ) (mem : x ∈ Submodule.span ℤ {m}), ↑g' x = ↑g { val := x, pro …
        · subst m_eq_zero
          -- ⊢ ∃ g', ∀ (x : ℤ) (mem : x ∈ Submodule.span ℤ {0}), ↑g' x = ↑g { val := x, pro …
          refine'
            ⟨{  toFun := _
                map_add' := _
                map_smul' := _ }, fun n hn => _⟩
          · intro _
            -- ⊢ A
            exact g 0
            -- 🎉 no goals
          · intro _ _
            -- ⊢ ↑g 0 = ↑g 0 + ↑g 0
            simp only [map_zero, add_zero]
            -- 🎉 no goals
          · intro n1 _
            -- ⊢ AddHom.toFun { toFun := fun a => ↑g 0, map_add' := (_ : ℤ → ℤ → ↑g 0 = ↑g 0  …
            simp only [map_zero, smul_zero]
            -- 🎉 no goals
          · rw [Submodule.span_singleton_eq_bot.mpr rfl, Submodule.mem_bot] at hn
            -- ⊢ ↑{ toAddHom := { toFun := fun a => ↑g 0, map_add' := (_ : ℤ → ℤ → ↑g 0 = ↑g  …
            simp only [hn, map_zero]
            -- ⊢ 0 = ↑g { val := 0, property := (_ : (fun x => x ∈ Submodule.span ℤ {0}) 0) }
            symm
            -- ⊢ ↑g { val := 0, property := (_ : (fun x => x ∈ Submodule.span ℤ {0}) 0) } = 0
            convert map_zero g
            -- 🎉 no goals
        · set gₘ := g ⟨m, Submodule.subset_span (Set.mem_singleton _)⟩ with gm_eq
          -- ⊢ ∃ g', ∀ (x : ℤ) (mem : x ∈ Submodule.span ℤ {m}), ↑g' x = ↑g { val := x, pro …
          refine'
            ⟨{  toFun := _
                map_add' := _
                map_smul' := _ }, fun n hn => _⟩
          · intro n
            -- ⊢ A
            exact n • DivisibleBy.div gₘ m
            -- 🎉 no goals
          · intro n1 n2
            -- ⊢ (n1 + n2) • DivisibleBy.div gₘ m = n1 • DivisibleBy.div gₘ m + n2 • Divisibl …
            simp only [add_smul]
            -- 🎉 no goals
          · intro n1 n2
            -- ⊢ AddHom.toFun { toFun := fun n => n • DivisibleBy.div gₘ m, map_add' := (_ :  …
            dsimp
            -- ⊢ (n1 * n2) • DivisibleBy.div (↑g { val := m, property := (_ : m ∈ ↑(Submodule …
            rw [mul_smul]
            -- 🎉 no goals
          · rw [Submodule.mem_span_singleton] at hn
            -- ⊢ ↑{ toAddHom := { toFun := fun n => n • DivisibleBy.div gₘ m, map_add' := (_  …
            rcases hn with ⟨n, rfl⟩
            -- ⊢ ↑{ toAddHom := { toFun := fun n => n • DivisibleBy.div gₘ m, map_add' := (_  …
            simp only [gm_eq, Algebra.id.smul_eq_mul, LinearMap.coe_mk]
            -- ⊢ ↑{ toFun := fun n => n • DivisibleBy.div (↑g { val := m, property := (_ : m  …
            dsimp
            -- ⊢ (n * m) • DivisibleBy.div (↑g { val := m, property := (_ : m ∈ ↑(Submodule.s …
            rw [mul_smul]
            -- ⊢ n • m • DivisibleBy.div (↑g { val := m, property := (_ : m ∈ ↑(Submodule.spa …
            -- Porting note: used to be able to just rw [Div...]
            have s := congrArg (fun l => n • l) <| DivisibleBy.div_cancel gₘ m_eq_zero
            -- ⊢ n • m • DivisibleBy.div (↑g { val := m, property := (_ : m ∈ ↑(Submodule.spa …
            dsimp at s
            -- ⊢ n • m • DivisibleBy.div (↑g { val := m, property := (_ : m ∈ ↑(Submodule.spa …
            rw [s, ← LinearMap.map_smul]
            -- ⊢ ↑g (n • { val := m, property := (_ : m ∈ ↑(Submodule.span ℤ {m})) }) = ↑g {  …
            congr
            -- 🎉 no goals
#align AddCommGroup.injective_of_divisible AddCommGroupCat.injective_of_divisible

end AddCommGroupCat
