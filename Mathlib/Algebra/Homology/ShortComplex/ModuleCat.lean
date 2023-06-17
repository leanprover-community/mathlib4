import Mathlib.Algebra.Homology.ShortComplex.ConcreteCategory
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Colimits

universe v u

variable {R : Type u} [Ring R]

namespace CategoryTheory

open Limits

@[simps!]
def AddCommGroupCat.cokernelCocone {M N : AddCommGroupCat.{u}} (f : M ⟶ N) :
    CokernelCofork f :=
  @CokernelCofork.ofπ _ _ _ _ _ f (AddCommGroupCat.of (N ⧸ AddMonoidHom.range f))
    (QuotientAddGroup.mk' (AddMonoidHom.range f)) (by
    ext x
    simp only [AddCommGroupCat.coe_comp, Function.comp_apply, AddCommGroupCat.zero_apply]
    erw [QuotientAddGroup.eq_zero_iff]
    simp only [AddMonoidHom.mem_range, exists_apply_eq_apply])

noncomputable def AddCommGroupCat.cokernelIsCokernel {M N : AddCommGroupCat.{u}} (f : M ⟶ N) :
    IsColimit (cokernelCocone f) :=
  IsColimit.ofIsoColimit (Limits.cokernelIsCokernel f)
    (Iso.symm (Cofork.ext (AddCommGroupCat.cokernelIsoQuotient f).symm (by aesop_cat)))

noncomputable instance {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    PreservesColimit (parallelPair f 0) (forget₂ (ModuleCat.{v} R) Ab) :=
  preservesColimitOfPreservesColimitCocone (ModuleCat.cokernelIsColimit f) (by
    let e : parallelPair ((forget₂ (ModuleCat.{v} R) Ab).map f) 0 ≅
        parallelPair f 0 ⋙ forget₂ _ _ :=
      parallelPair.ext (Iso.refl _) (Iso.refl _) (by aesop_cat) (by aesop_cat)
    refine' IsColimit.precomposeHomEquiv e _ _
    refine' IsColimit.ofIsoColimit
      (AddCommGroupCat.cokernelIsCokernel ((forget₂ (ModuleCat.{v} R) Ab).map f)) _
    refine' Cofork.ext (Iso.refl _) (by aesop_cat))

namespace ShortComplex

variable (S : ShortComplex (ModuleCat.{v} R))

noncomputable instance : (forget₂ (ModuleCat.{v} R) Ab).PreservesHomology where

lemma moduleCat_exact_iff :
    S.Exact ↔ ∀ (x₂ : S.X₂) (_ : S.g x₂ = 0), ∃ (x₁ : S.X₁), S.f x₁ = x₂ :=
  S.exact_iff_of_concrete_category

end ShortComplex

end CategoryTheory
