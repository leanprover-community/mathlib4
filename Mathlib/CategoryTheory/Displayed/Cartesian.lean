/-
Copyright (c) 2024 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/

import Mathlib.CategoryTheory.Displayed.Fiber
import Mathlib.CategoryTheory.Displayed.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Cartesian lifts

We introduce the structures `Display.Cartesian` and `Display.CoCartesian`
carrying data witnessing that a given lift is cartesian and cocartesian, respectively.

Specialized to the display category structure of a functor `P : E ⥤ C`,
we obtain the class `CartMor` of cartesian morphisms in `E`.
The type `CartMor P` is defined in terms of the predicate `isCartesianMorphism`.

Given a displayed category structure on a type family `F : C → Type`, and an object `I : C`, we shall refer to
the type `F I` as the "fiber" of `F` at `I`. For a morphism `f : I ⟶ J` in `C`, and objects
`X : F I` and `Y : F J`, we shall refer to a hom-over `g : X ⟶[f] Y` as a "lift" of  `f` to `X` and `Y`.

We prove the following closure properties of the class `CartMor` of cartesian morphisms:
- `cart_id` proves that the identity morphism is cartesian.
- `cart_comp` proves that the composition of cartesian morphisms is cartesian.
- `cart_iso_closed` proves that the class of cartesian morphisms is closed under isomorphisms.
- `cart_pullback` proves that, if `P` preserves pullbacks, then
the pullback of a cartesian morphism is cartesian.

`instCatCart` provides a category instance for the class of cartesian morphisms,
and `Cart.forget` provides the forgetful functor from the category of cartesian morphisms
to the domain category `E`.

## Main declarations

- `CartLift f Y` is the type of cartesian lifts of a morphism `f` with fixed target `Y`.
- `CoCartLift f X` is the type of cocartesian lifts of a morphism `f` with fixed source `X`.

Given `g : CartLift f Y`, we have
- `g.1` is the lift of `f` to `Y`.
- `g.homOver : CartLift.toLift.src ⟶[f] Y` is a morphism over `f`.
- `g.homOver.hom` is the underlying morphism of `g.homOver`.
- `g.is_cart` is the proof that `g.homOver` is cartesian.

Similarly, given `g : CoCartLift f X`, we have
- `g.1` is the lift of `f` from `X`.
- `g.homOver : X ⟶[f] CoCartLift.toCoLift.tgt` is a morphism over `f`.
- `g.homOver.hom` is the underlying morphism of `g.homOver`.
- `g.is_cocart` is the proof that `g.homOver` is cocartesian.
-/

set_option autoImplicit true

namespace CategoryTheory

open Category Opposite Functor Limits Cones

variable {C E : Type*} [Category C] {F : C → Type*} [Display F]

namespace Display

variable {I J : C} {f : I ⟶ J} {X : F I} {Y : F J}

/-- A lift `g : X ⟶[f] Y` is cartesian if for every morphism `u : K ⟶ I`
in the base and every hom-over `g' : Z ⟶[u ≫ f] Y` over the composite
 `u ≫ f`, there is a unique morphism `k : Z ⟶[u] X` over `u` such that
 `k ≫ g = g'`.
```
       _ _ _ _ _ _ _ _ _ _ _
      /           g'        \
     |                      v
     Z - - - - > X --------> Y
     _   ∃!k     _   g       _
     |           |           |
     |           |           |
     v           v           v
     K --------> I --------> J
          u            f
```
-/
class Cartesian (g : X ⟶[f] Y) where
  uniq_lift : ∀ ⦃K : C⦄ ⦃Z : F K⦄ (u : K ⟶ I) (g' : Z ⟶[u ≫ f] Y),
  Unique {k : Z ⟶[u] X // (k ≫ₒ g) = g'}

class Cartesian' [Category E] {P : E ⥤ C} {X Y : E} (g : X ⟶ Y) where
  uniq_lift : ∀ ⦃Z : E⦄ (u : P.obj Z ⟶ P.obj X) (g' : Z ⟶ Y),
    Unique {k : Z ⟶ X // (k ≫ g) = g' ∧ P.map k = u}

/-- A lift `g : X ⟶[f] Y` is cocartesian if for all morphisms `u` in the
base and `g' : X ⟶[f ≫ u] Z`, there is a unique morphism
`k : Y ⟶[u] Z` over `u` such that `g ≫ k = g'`.
```
       _ _ _ _ _ _ _ _ _ _ _
      /          g'         \
     |                      v
     X ------- > Y - - - - > Z
     _    g      _    ∃!k    _
     |           |           |
     |           |           |
     v           v           v
     I --------> J --------> K
          f            u
```
-/
class CoCartesian (g : X ⟶[f] Y) where
  uniq_lift : ∀ ⦃K : C⦄ ⦃Z : F K⦄ (u : J ⟶ K) (g' : X ⟶[f ≫ u] Z),
  Unique {k :  Y ⟶[u] Z // (g ≫ₒ k) = g'}

namespace Cartesian

open Display

variable (g : X ⟶[f] Y) [Cartesian g] {K : C} {Z : F K}

/-- `gap g u g'` is the canonical map from a lift `g' : Z ⟶[u ≫ f] X` to a
cartesian lift `g` of `f`. -/
def gap {u : K ⟶ I} (g' : Z ⟶[u ≫ f] Y) : Z ⟶[u] X :=
  (Cartesian.uniq_lift (g:= g) (Z:= Z) u g').default.val

/-- A variant of `gaplift` for `g' : Z ⟶[f'] Y` with casting along `f' = u ≫ f`
baked into the definition. -/
def gapCast (u : K ⟶ I) {f' : K ⟶ J} (g' : Z ⟶[f'] Y) (w : f' = u ≫ f) :
    Z ⟶[u] X :=
  (Cartesian.uniq_lift (g:= g) (Z:= Z) u (w ▸ g')).default.val

@[simp]
lemma gap_cast (u : K ⟶ I) {f' : K ⟶ J} (g' : Z ⟶[f'] Y)
    (w : f' = u ≫ f) : gapCast g u g' w = gap g (w ▸ g') := rfl

/-- The composition of the gap lift and the cartesian hom-over is the given hom-over. -/
@[simp]
lemma gap_prop (u : K ⟶ I) (g' : Z ⟶[u ≫ f] Y) :
    ((gap g g') ≫ₒ g) = g' :=
  (Cartesian.uniq_lift (f:= f) (g:= g) (Z := Z) u g').default.property

/-- The uniqueness part of the universal property of the gap lift. -/
@[simp]
lemma gaplift_uniq {u : K ⟶ I} (g' : Z ⟶[u ≫ f] Y) (v : Z ⟶[u] X)
    (hv : v ≫ₒ g = g') : v = gap g g' := by
  rw [gap, ← (Cartesian.uniq_lift u g').uniq ⟨v,hv⟩]

/-- The identity hom-over is cartesian. -/
instance instId {X : F I} : Cartesian (𝟙ₒ X) where
  uniq_lift := fun K Z u g' => {
    default := ⟨(comp_id u) ▸ g', by simp⟩
    uniq := by aesop
  }

/-- Cartesian based-lifts are closed under composition. -/
instance instComp {X : F I} {Y : F J} {Z : F K} {f₁ : I ⟶ J} {f₂ : J ⟶ K}
    (g₁ : X ⟶[f₁] Y) [Cartesian g₁] (g₂ : Y ⟶[f₂] Z) [Cartesian g₂] :
  Cartesian (g₁ ≫ₒ g₂) where
  uniq_lift := fun I' W u g' => {
    default := ⟨gap g₁ (gap g₂ (assoc u f₁ f₂ ▸ g')), by
      rw [← Display.cast_assoc_symm, gap_prop g₁ _ _, gap_prop g₂ _ _]
      simp⟩
    uniq := by
      intro ⟨l, hl⟩
      rw [Subtype.mk.injEq]
      apply gaplift_uniq _ _ _ (gaplift_uniq _ _ _ _)
      simp [assoc_cast, hl] }

end Cartesian

/-- The type of cartesian lifts of a morphism `f` with fixed target. -/
class CartLift (f : I ⟶ J) (tgt : F J) extends Lift f tgt where
  is_cart : Cartesian homOver

/--Mere existence of a cartesian lift with fixed target. -/
def HasCartLift (f : I ⟶ J) (tgt : F J) := Nonempty (CartLift f tgt)

/-- The type of cocartesian lifts of a morphism `f` with fixed source. -/
class CoCartLift (f : I ⟶ J) (src : F I) extends CoLift f src where
  is_cocart : CoCartesian homOver

def HasCoCartLift (f : I ⟶ J) (src : F I) := Nonempty (CoCartLift f src)

end Display

end CategoryTheory
