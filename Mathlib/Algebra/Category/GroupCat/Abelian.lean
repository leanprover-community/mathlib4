/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel

! This file was ported from Lean 3 source module algebra.category.Group.abelian
! leanprover-community/mathlib commit f7baecbb54bd0f24f228576f97b1752fc3c9b318
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Category.GroupCat.Colimits
import Mathlib.Algebra.Category.GroupCat.FilteredColimits
import Mathlib.Algebra.Category.GroupCat.Kernels
import Mathlib.Algebra.Category.GroupCat.Limits
import Mathlib.Algebra.Category.GroupCat.ZModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Limits.ConcreteCategory

/-!
# The category of abelian groups is abelian
-/

open CategoryTheory Limits

universe u

noncomputable section

namespace AddCommGroupCat

variable {X Y Z : AddCommGroupCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

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

/-- The category of abelian groups is abelian. -/
instance : Abelian AddCommGroupCat.{u} where
  has_finite_products := ⟨HasFiniteProducts.out⟩
  normalMonoOfMono := normalMono
  normalEpiOfEpi := normalEpi
  add_comp := by exact Preadditive.add_comp
  comp_add := by exact Preadditive.comp_add

variable {X Y Z : AddCommGroupCat.{u}}

theorem exact_iff : Exact f g ↔ f.range = g.ker := by
  rw [Abelian.exact_iff' f g (kernelIsLimit _) (cokernelIsColimit _)]
  exact
    ⟨fun h => le_antisymm (range_le_ker_iff.mpr h.left) (ker_le_range_iff.mpr h.right),
      fun h => ⟨range_le_ker_iff.mp <| le_of_eq h, ker_le_range_iff.mp <| le_of_eq h.symm⟩⟩

theorem exact_iff' : Exact f g ↔ f ≫ g = 0 ∧ g.ker ≤ f.range := by
  rw [exact_iff, le_antisymm_iff]
  exact and_congr ⟨fun h => ext fun x => h (AddMonoidHom.mem_range.mpr ⟨x, rfl⟩),
    by rintro h _ ⟨x, rfl⟩; exact FunLike.congr_fun h x⟩ Iff.rfl

lemma exact_of_exact_functor {F G H : J ⥤ AddCommGroupCat.{u}} {η : F ⟶ G} {γ : G ⟶ H}
    (h : Exact η γ) (j : J) : Exact (η.app j) (γ.app j) := by
  sorry

/-- The category of abelian groups is a Grothendieck category. -/
instance : PreservesFiniteLimits <| colim (J := J) (C := AddCommGroupCat.{u}) := by
  apply Functor.preservesFiniteLimitsOfMapExact
  intro F G H η γ h
  replace h := exact_of_exact_functor h
  rw [exact_iff']
  constructor
  · refine colimit.hom_ext  (fun j => ?_)
    simp [reassoc_of% (h j).1]
  · rintro x (hx :  _ = _)
    let x' : (forget AddCommGroupCat).obj (colimit G) := x
    obtain ⟨j,y,rfl⟩ := Limits.Concrete.colimit_exists_rep G x'
    erw [← comp_apply, Limits.colimit.ι_desc] at hx
    dsimp at hx
    rw [comp_apply] at hx
    have : 0 = Limits.colimit.ι H j 0 := by
      simp
    rw [this] at hx
    clear this
    obtain ⟨k,e₁,e₂,hk⟩ := Limits.Concrete.colimit_exists_of_rep_eq _ _ _ hx
    let temp : H.obj j →+ H.obj k := H.map e₂
    change _ = temp 0 at hk
    rw [temp.map_zero] at hk
    rw [← comp_apply, ← NatTrans.naturality] at hk
    rw [comp_apply] at hk
    have hk' : (G.map e₁ y) ∈ AddMonoidHom.ker (γ.app k) := by
      rw [AddMonoidHom.mem_ker]
      convert hk
    obtain ⟨t, ht⟩ := ((AddCommGroupCat.exact_iff' (η.app k) (γ.app k)).1 (h k)).2 hk'
    use Limits.colimit.ι F k t
    erw [← comp_apply, Limits.colimit.ι_map, comp_apply, ht, ← comp_apply]
    congr 1
    simp

end AddCommGroupCat
