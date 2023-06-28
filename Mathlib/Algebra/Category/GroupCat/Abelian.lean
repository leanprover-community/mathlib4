/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel

! This file was ported from Lean 3 source module algebra.category.Group.abelian
! leanprover-community/mathlib commit f7baecbb54bd0f24f228576f97b1752fc3c9b318
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Category.GroupCat.ZModuleEquivalence
import Mathlib.Algebra.Category.GroupCat.Limits
import Mathlib.Algebra.Category.GroupCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Limits.ConcreteCategory
import Mathlib.CategoryTheory.Abelian.Basic
/-!
# The category of abelian groups is abelian
-/


open CategoryTheory

open CategoryTheory.Limits

universe u

noncomputable section

namespace AddCommGroupCat

section

variable {X Y : ModuleCat ℤ } (f : X ⟶ Y)

/-- In the category of abelian groups, every monomorphism is normal. -/
def normalMono (_ : Mono f) : NormalMono f :=
  equivalenceReflectsNormalMono (forget₂ (ModuleCat.{u} ℤ) AddCommGroupCat.{u}).inv <|
    ModuleCat.normalMono _ inferInstance
set_option linter.uppercaseLean3 false in
#align AddCommGroup.normal_mono AddCommGroupCat.normalMono

/-- In the category of abelian groups, every epimorphism is normal. -/
def normalEpi (_ : Epi f) : NormalEpi f :=
  equivalenceReflectsNormalEpi (forget₂ (ModuleCat.{u} ℤ) AddCommGroupCat.{u}).inv <|
    ModuleCat.normalEpi _ inferInstance
set_option linter.uppercaseLean3 false in
#align AddCommGroup.normal_epi AddCommGroupCat.normalEpi

end

/-- The category of abelian groups is abelian. -/
instance : Abelian AddCommGroupCat.{u} where
  has_finite_products := ⟨by infer_instance⟩
  normalMonoOfMono := normalMono
  normalEpiOfEpi := normalEpi
  add_comp := by
    intros
    simp only [Preadditive.add_comp]
  comp_add := by
    intros
    simp only [Preadditive.comp_add]

variable {J : Type u} [SmallCategory J] [IsFiltered J]


theorem exact_iff {X Y Z : ModuleCat ℤ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Exact f g ↔ g.ker = f.range := by
  rw [Abelian.exact_iff' f g _ _]
  rotate_left 4

  exact ModuleCat.cokernelIsColimit (R := ℤ) ( M := X) (N := Y) f
  split
  · rintro ⟨hfg, h⟩
    ext x
    split
    · rintro ⟨x, rfl⟩
      exact AddMonoidHom.congr_fun hfg x
    · intro hx
      rw [← QuotientAddGroup.eq_zero_iff]
      exact AddMonoidHom.congr_fun h ⟨x, hx⟩
  · intro h
    split
    · ext x
      show f x ∈ g.ker
      rw [←h]
      simp only [AddMonoidHom.mem_range, exists_apply_eq_apply]
    · ext ⟨x, hx⟩
      dsimp [kernel_cone, cokernel_cocone]
      simpa only [comp_apply, add_subgroup.coe_subtype, add_subgroup.coe_mk
        QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, h] using hx

instance : HasLimits (ModuleCat ℤ) := by infer_instance
instance : HasColimits (ModuleCat ℤ) := by sorry

theorem exact_iff' {X Y Z : AddCommGroupCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Exact f g ↔ f ≫ g = 0 ∧ g.ker ≤ f.range := by
  rw [exact_iff, le_antisymm_iff]
  refine' and_congr _ Iff.rfl
  constructor
  · intro h
    ext x
    exact h (AddMonoidHom.mem_range.mpr ⟨x, rfl⟩)
  · rintro h _ ⟨x, rfl⟩
    exact FunLike.congr_fun h x


-- Axiom AB5 for `AddCommGroup`
theorem exact_colim_of_exact_of_is_filtered
  (F G H : J ⥤ ModuleCat ℤ) (η : F ⟶ G) (γ : G ⟶ H) :
  (∀ j, Exact (η.app j) (γ.app j)) → Exact (Limits.colimMap η) (Limits.colimMap γ) := by
  intros h
  rw [CategoryTheory.Abelian.exact_iff_image_eq_kernel]
  constructor
  · refine colimit.hom_ext  (fun j => ?_)
    simp [reassoc_of% (h j).1]
  · rintro x (hx :  _ = _)
    obtain ⟨j,y,rfl⟩ := Limits.Concrete.colimit_exists_rep _ (x)
    erw [← comp_apply, Limits.colimit.ι_desc] at hx
    dsimp at hx
    rw [comp_apply] at hx
    have : (0 : Limits.colimit H) = Limits.colimit.ι H j 0 := by
      simp
    rw [this] at hx
    clear this
    obtain ⟨k,e₁,e₂,hk⟩ := Limits.Concrete.colimit_exists_of_rep_eq _ _ _ hx
    simp only [map_zero, ← comp_apply, ← nat_trans.naturality] at hk, rw comp_apply at hk
    obtain ⟨t,ht⟩ := ((AddCommGroupCat.exact_iff' _ _).1 (h k)).2 hk
    use Limits.colimit.ι F k t
    erw [← comp_apply, Limits.colimit.ι_map, comp_apply, ht, ← comp_apply]
    congr' 1
    simp
  · sorry
  · sorry
  · sorry
  · sorry
end AddCommGroupCat
