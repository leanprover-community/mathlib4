/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.Monoidal.Opposite
import Mathlib.CategoryTheory.Monoidal.Mon_

/-!
# Monoid objects internal to monoidal opposites

In this file, we record the equivalence between `Mon_ C` and `Mon Cᴹᵒᵖ`.
-/

namespace Mon_Class

open CategoryTheory MonoidalCategory MonoidalOpposite

universe v u

variable {C : Type*} [Category C] [MonoidalCategory C]

section mop

variable (M : C) [Mon_Class M]

@[simps!]
instance mopMon_Class : Mon_Class (mop M) where
  mul := Mon_Class.mul.mop
  one := Mon_Class.one.mop
  mul_one' := by
    apply mopEquiv C|>.fullyFaithfulInverse.map_injective
    simp
  one_mul' := by
    apply mopEquiv C|>.fullyFaithfulInverse.map_injective
    simp
  mul_assoc' := by
    apply mopEquiv C|>.fullyFaithfulInverse.map_injective
    simp

variable {M} in
instance mop_isMon_Hom {N : C} [Mon_Class N]
    (f : M ⟶ N) [IsMon_Hom f] : IsMon_Hom f.mop where
  mul_hom := by
    apply mopEquiv C|>.fullyFaithfulInverse.map_injective
    simpa [-IsMon_Hom.mul_hom] using IsMon_Hom.mul_hom f
  one_hom := by
    apply mopEquiv C|>.fullyFaithfulInverse.map_injective
    simpa [-IsMon_Hom.one_hom] using IsMon_Hom.one_hom f

end mop

section unmop

variable (M : Cᴹᵒᵖ) [Mon_Class M]

@[simps -isSimp] -- removing isSimp causes a loop.
instance unmopMon_Class : Mon_Class (unmop M) where
  mul := Mon_Class.mul.unmop
  one := Mon_Class.one.unmop
  mul_one' := by
    apply mopEquiv C|>.fullyFaithfulFunctor.map_injective
    simp
  one_mul' := by
    apply mopEquiv C|>.fullyFaithfulFunctor.map_injective
    simp
  mul_assoc' := by
    apply mopEquiv C|>.fullyFaithfulFunctor.map_injective
    simp

variable {M} in
instance unmop_isMon_Hom {N : Cᴹᵒᵖ} [Mon_Class N]
    (f : M ⟶ N) [IsMon_Hom f] : IsMon_Hom f.unmop where
  mul_hom := by
    apply mopEquiv C|>.fullyFaithfulFunctor.map_injective
    simpa [-IsMon_Hom.mul_hom] using IsMon_Hom.mul_hom f
  one_hom := by
    apply mopEquiv C|>.fullyFaithfulFunctor.map_injective
    simpa [-IsMon_Hom.one_hom] using IsMon_Hom.one_hom f

end unmop

variable (C) in

@[simps!]
def mopEquiv : Mon_ C ≌ Mon_ Cᴹᵒᵖ where
  functor :=
    { obj M := ⟨mop M.X⟩
      map f := ⟨f.hom.mop⟩ }
  inverse :=
    { obj M := ⟨unmop M.X⟩
      map f := ⟨f.hom.unmop⟩ }
  unitIso := .refl _
  counitIso := .refl _

@[simps!]
def mopEquivCompForgetIso :
    (mopEquiv C).functor ⋙ Mon_.forget Cᴹᵒᵖ ≅
    Mon_.forget C ⋙ (MonoidalOpposite.mopEquiv C).functor :=
  .refl _

end Mon_Class
