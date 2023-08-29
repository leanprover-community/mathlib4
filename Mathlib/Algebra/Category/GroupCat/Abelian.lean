/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.Algebra.Category.GroupCat.Colimits
import Mathlib.Algebra.Category.GroupCat.FilteredColimits
import Mathlib.Algebra.Category.GroupCat.Kernels
import Mathlib.Algebra.Category.GroupCat.Limits
import Mathlib.Algebra.Category.GroupCat.ZModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Limits.ConcreteCategory

#align_import algebra.category.Group.abelian from "leanprover-community/mathlib"@"f7baecbb54bd0f24f228576f97b1752fc3c9b318"

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

theorem exact_iff : Exact f g ↔ f.range = g.ker := by
  rw [Abelian.exact_iff' f g (kernelIsLimit _) (cokernelIsColimit _)]
  -- ⊢ f ≫ g = 0 ∧ Fork.ι (kernelCone g) ≫ Cofork.π (cokernelCocone f) = 0 ↔ AddMon …
  exact
    ⟨fun h => ((AddMonoidHom.range_le_ker_iff _ _).mpr h.left).antisymm
        ((QuotientAddGroup.ker_le_range_iff _ _).mpr h.right),
      fun h => ⟨(AddMonoidHom.range_le_ker_iff _ _).mp h.le,
          (QuotientAddGroup.ker_le_range_iff _ _).mp h.symm.le⟩⟩

/-- The category of abelian groups satisfies Grothedieck's Axiom AB5. -/
instance {J : Type u} [SmallCategory J] [IsFiltered J] :
    PreservesFiniteLimits <| colim (J := J) (C := AddCommGroupCat.{u}) := by
  refine Functor.preservesFiniteLimitsOfMapExact _
    fun F G H η γ h => (exact_iff _ _).mpr (le_antisymm ?_ ?_)
  all_goals replace h : ∀ j : J, Exact (η.app j) (γ.app j) :=
    fun j => Functor.map_exact ((evaluation _ _).obj j) η γ h
  · rw [AddMonoidHom.range_le_ker_iff, ← comp_def]
    -- ⊢ colim.map η ≫ colim.map γ = 0
    exact colimit.hom_ext fun j => by simp [reassoc_of% (h j).w]
    -- 🎉 no goals
  · intro x (hx : _ = _)
    -- ⊢ x ∈ AddMonoidHom.range (colim.map η)
    rcases Concrete.colimit_exists_rep G x with ⟨j, y, rfl⟩
    -- ⊢ ↑(colimit.ι G j) y ∈ AddMonoidHom.range (colim.map η)
    erw [← comp_apply, colimit.ι_map, comp_apply,
      ← map_zero (by exact colimit.ι H j : H.obj j →+ ↑(colimit H))] at hx
    rcases Concrete.colimit_exists_of_rep_eq H _ _ hx with ⟨k, e₁, e₂, hk : _ = H.map e₂ 0⟩
    -- ⊢ ↑(colimit.ι G j) y ∈ AddMonoidHom.range (colim.map η)
    rw [map_zero, ← comp_apply, ← NatTrans.naturality, comp_apply] at hk
    -- ⊢ ↑(colimit.ι G j) y ∈ AddMonoidHom.range (colim.map η)
    rcases ((exact_iff _ _).mp <| h k).ge hk with ⟨t, ht⟩
    -- ⊢ ↑(colimit.ι G j) y ∈ AddMonoidHom.range (colim.map η)
    use colimit.ι F k t
    -- ⊢ ↑(colim.map η) (↑(colimit.ι F k) t) = ↑(colimit.ι G j) y
    erw [← comp_apply, colimit.ι_map, comp_apply, ht]
    -- ⊢ ↑(colimit.ι G k) (↑(G.map e₁) y) = ↑(colimit.ι G j) y
    exact colimit.w_apply G e₁ y
    -- 🎉 no goals

end AddCommGroupCat
