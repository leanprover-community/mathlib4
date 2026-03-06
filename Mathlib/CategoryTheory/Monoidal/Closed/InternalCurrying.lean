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
-- TODO: Prove naturality of this morphism (requires the appropriate instances of `[Closed _]` for
-- objects in `C`).
def ihomCurry (x y z : C) [Closed x] [Closed y] [Closed (x ⊗ y)] :
    (ihom (x ⊗ y)).obj z ⟶ (ihom y).obj ((ihom x).obj z) :=
  curry (curry ((α_ x y _).inv ≫ (ihom.ev _).app z))

lemma uncurry_ihomCurry (x y z : C) [Closed x] [Closed y] [Closed (x ⊗ y)] :
    uncurry (ihomCurry x y z) = curry ((α_ x y _).inv ≫ (ihom.ev _).app z) :=
  uncurry_curry _

lemma uncurry_uncurry_ihomCurry (x y z : C) [Closed x] [Closed y] [Closed (x ⊗ y)] :
    uncurry (uncurry (ihomCurry x y z)) = (α_ x y _).inv ≫ (ihom.ev _).app z := by
  simp only [uncurry_ihomCurry, uncurry_curry]

/-- The uncurrying operation taking a morphism `y ⟶ C(x, z)` to a morphism `(x ⊗ y) ⟶ z`,
  constructed as a morphism in `C` between internal homs. -/
-- TODO: Prove naturality of this morphism (requires the appropriate instances of `[Closed _]` for
-- objects in `C`).
def ihomUncurry (x y z : C) [Closed x] [Closed y] [Closed (x ⊗ y)] :
    (ihom y).obj ((ihom x).obj z) ⟶ (ihom (x ⊗ y)).obj z :=
  curry ((α_ x y _).hom ≫ x ◁ (ihom.ev y).app ((ihom x).obj z) ≫ (ihom.ev x).app z)

lemma uncurry_ihomUncurry (x y z : C) [Closed x] [Closed y] [Closed (x ⊗ y)] :
    uncurry (ihomUncurry x y z) = (α_ x y _).hom ≫ x ◁ (ihom.ev y).app ((ihom x).obj z) ≫
    (ihom.ev x).app z :=
  uncurry_curry _

@[reassoc (attr := simp)]
theorem ihomUncurry_ihomCurry (x y z : C) [Closed x] [Closed y] [Closed (x ⊗ y)] :
    ihomUncurry x y z ≫ ihomCurry x y z = 𝟙 _ := by
  apply uncurry_injective
  apply uncurry_injective
  simp only [uncurry_natural_left, uncurry_id_eq_ev, uncurry_uncurry_ihomCurry]
  rw [associator_inv_naturality_right_assoc, ← uncurry_eq, uncurry_ihomUncurry,
    Iso.inv_hom_id_assoc]
  exact rfl

@[reassoc (attr := simp)]
theorem ihomCurry_ihomUncurry (x y z : C) [Closed x] [Closed y] [Closed (x ⊗ y)] :
    ihomCurry x y z ≫ ihomUncurry x y z = 𝟙 _ := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_id_eq_ev, uncurry_ihomUncurry,
    associator_naturality_right_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, ← uncurry_eq,
    ← uncurry_eq, uncurry_uncurry_ihomCurry, Iso.hom_inv_id_assoc _ _]

/-- The internal currying-uncurrying isomorphism `C(x ⊗ y, z) ≅ C(y, C(x, z))`. -/
@[simps]
def ihomCurryIso (x y z : C) [Closed x] [Closed y] [Closed (x ⊗ y)] :
    (ihom (x ⊗ y)).obj z ≅ (ihom y).obj ((ihom x).obj z) where
  hom := ihomCurry x y z
  inv := ihomUncurry x y z
  hom_inv_id := ihomCurry_ihomUncurry x y z
  inv_hom_id := ihomUncurry_ihomCurry x y z

end CategoryTheory.MonoidalClosed

end
