/-
Copyright (c) 2026 Daniel Carranza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Carranza
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# The currying-uncurrying isomorphism between internal homs of a closed monoidal category

For a closed monoidal category `C`, we construct the isomorphism of internal hom objects
`C(x ⊗ y, z) ≅ C(y, C(x, z))` for any triple of objects `x y z : C`.

-/

@[expose] public section

universe u v

namespace CategoryTheory

open Category MonoidalCategory

namespace MonoidalClosed

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The currying operation taking a morphism `(z ⊗ y) ⟶ x` to a morphism `y ⟶ C(z, x)`,
  constructed as a morphism in `C` between internal homs. -/
def internalHomCurry (x y z : C) [Closed x] [Closed y] [Closed (x ⊗ y)] :
    (ihom (x ⊗ y)).obj z ⟶ (ihom y).obj ((ihom x).obj z) :=
  curry (curry ((α_ x y _).inv ≫ (ihom.ev _).app z))

lemma internalHomCurry_uncurry_eq (x y z : C) [Closed x] [Closed y] [Closed (x ⊗ y)] :
    uncurry (internalHomCurry x y z) = curry ((α_ x y _).inv ≫ (ihom.ev _).app z) :=
  uncurry_curry _

lemma internalHomCurry_uncurry_uncurry_eq (x y z : C) [Closed x] [Closed y] [Closed (x ⊗ y)] :
    uncurry (uncurry (internalHomCurry x y z)) = (α_ x y _).inv ≫ (ihom.ev _).app z := by
  simp only [internalHomCurry_uncurry_eq, uncurry_curry]

/-- The uncurrying operation taking a morphism `y ⟶ C(x, z)` to a morphism `(x ⊗ y) ⟶ z`,
  constructed as a morphism in `C` between internal homs. -/
def internalHomUncurry (x y z : C) [Closed x] [Closed y] [Closed (x ⊗ y)] :
    (ihom y).obj ((ihom x).obj z) ⟶ (ihom (x ⊗ y)).obj z :=
  curry ((α_ x y _).hom ≫ x ◁ (ihom.ev y).app ((ihom x).obj z) ≫ (ihom.ev x).app z)

lemma internalHomUncurry_uncurry_eq (x y z : C) [Closed x] [Closed y] [Closed (x ⊗ y)] :
    uncurry (internalHomUncurry x y z) =
    (α_ x y _).hom ≫ x ◁ (ihom.ev y).app ((ihom x).obj z) ≫ (ihom.ev x).app z :=
  uncurry_curry _

theorem internalHom_uncurry_curry (x y z : C) [Closed x] [Closed y] [Closed (x ⊗ y)] :
    internalHomUncurry x y z ≫ internalHomCurry x y z = 𝟙 _ := by
  apply uncurry_injective
  apply uncurry_injective
  simp only [uncurry_natural_left, uncurry_id_eq_ev, internalHomCurry_uncurry_uncurry_eq]
  rw [associator_inv_naturality_right_assoc, ← uncurry_eq, internalHomUncurry_uncurry_eq,
    Iso.inv_hom_id_assoc]
  exact rfl

theorem internalHom_curry_uncurry (x y z : C) [Closed x] [Closed y] [Closed (x ⊗ y)] :
    internalHomCurry x y z ≫ internalHomUncurry x y z = 𝟙 _ := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_id_eq_ev, internalHomUncurry_uncurry_eq,
    associator_naturality_right_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, ← uncurry_eq,
    ← uncurry_eq, internalHomCurry_uncurry_uncurry_eq, Iso.hom_inv_id_assoc _ _]

/-- The internal currying-uncurrying isomorphism `C(x ⊗ y, z) ≅ C(y, C(x, z))`. -/
@[simps]
def internalHomCurryIso (x y z : C) [Closed x] [Closed y] [Closed (x ⊗ y)] :
    (ihom (x ⊗ y)).obj z ≅ (ihom y).obj ((ihom x).obj z) where
  hom := internalHomCurry x y z
  inv := internalHomUncurry x y z
  hom_inv_id := internalHom_curry_uncurry x y z
  inv_hom_id := internalHom_uncurry_curry x y z

end CategoryTheory.MonoidalClosed

end
