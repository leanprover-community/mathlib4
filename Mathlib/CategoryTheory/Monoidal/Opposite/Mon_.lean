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

namespace MonObj

open CategoryTheory MonoidalCategory MonoidalOpposite

variable {C : Type*} [Category C] [MonoidalCategory C]

section mop

variable (M : C) [MonObj M]

/-- If `M : C` is a monoid object, then `mop M : Cᴹᵒᵖ` too. -/
@[simps!]
instance mopMonObj : MonObj (mop M) where
  mul := MonObj.mul.mop
  one := MonObj.one.mop
  mul_one := by
    apply mopEquiv C|>.fullyFaithfulInverse.map_injective
    simp
  one_mul := by
    apply mopEquiv C|>.fullyFaithfulInverse.map_injective
    simp
  mul_assoc := by
    apply mopEquiv C|>.fullyFaithfulInverse.map_injective
    simp

variable {M} in
/-- If `f` is a morphism of monoid objects internal to `C`,
then `f.mop` is a morphism of monoid objects internal to `Cᴹᵒᵖ`. -/
instance mop_isMon_Hom {N : C} [MonObj N]
    (f : M ⟶ N) [IsMon_Hom f] : IsMon_Hom f.mop where
  mul_hom := by
    apply mopEquiv C|>.fullyFaithfulInverse.map_injective
    simpa [-IsMon_Hom.mul_hom] using IsMon_Hom.mul_hom f
  one_hom := by
    apply mopEquiv C|>.fullyFaithfulInverse.map_injective
    simpa [-IsMon_Hom.one_hom] using IsMon_Hom.one_hom f

end mop

section unmop

variable (M : Cᴹᵒᵖ) [MonObj M]

/-- If `M : Cᴹᵒᵖ` is a monoid object, then `unmop M : C` too. -/
@[simps -isSimp] -- not making them simp because it causes a loop.
instance unmopMonObj : MonObj (unmop M) where
  mul := MonObj.mul.unmop
  one := MonObj.one.unmop
  mul_one := by
    apply mopEquiv C|>.fullyFaithfulFunctor.map_injective
    simp
  one_mul := by
    apply mopEquiv C|>.fullyFaithfulFunctor.map_injective
    simp
  mul_assoc := by
    apply mopEquiv C|>.fullyFaithfulFunctor.map_injective
    simp

variable {M} in
/-- If `f` is a morphism of monoid objects internal to `Cᴹᵒᵖ`,
so is `f.unmop`. -/
instance unmop_isMon_Hom {N : Cᴹᵒᵖ} [MonObj N]
    (f : M ⟶ N) [IsMon_Hom f] : IsMon_Hom f.unmop where
  mul_hom := by
    apply mopEquiv C|>.fullyFaithfulFunctor.map_injective
    simpa [-IsMon_Hom.mul_hom] using IsMon_Hom.mul_hom f
  one_hom := by
    apply mopEquiv C|>.fullyFaithfulFunctor.map_injective
    simpa [-IsMon_Hom.one_hom] using IsMon_Hom.one_hom f

end unmop

variable (C) in

/-- The equivalence of categories between monoids internal to `C`
and monoids internal to the monoidal opposite of `C`. -/
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

/-- The equivalence of categories between monoids internal to `C`
and monoids internal to the monoidal opposite of `C` lies over
the equivalence `C ≌ Cᴹᵒᵖ` via the forgetful functors. -/
@[simps!]
def mopEquivCompForgetIso :
    (mopEquiv C).functor ⋙ Mon_.forget Cᴹᵒᵖ ≅
    Mon_.forget C ⋙ (MonoidalOpposite.mopEquiv C).functor :=
  .refl _

end MonObj
