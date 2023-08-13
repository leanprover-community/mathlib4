/-
Copyright (c) 2023 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import Mathlib.CategoryTheory.Bicategory.Basic

/-!
# Extensions and lifts in bicategories

We introduce the concept of extensions and lifts within the bicategorical framework. These concepts
are defined by commutative diagrams in the (1-)categorical context. Within the bicategorical
framework, commutative diagrams are replaced by 2-morphisms. Depending on the orientation of the
2-morphisms, we define both left and right extensions (likewise for lifts).

The use of left and right here is a common one in the theory of Kan extensions.

## References
* https://ncatlab.org/nlab/show/lifts+and+extensions
* https://ncatlab.org/nlab/show/Kan+extension

## Todo
API for left lifts, right extensions, and right lifts
-/

namespace CategoryTheory

namespace Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B] {a b c : B}

/-- Triangle diagrams for (left) extensions.
```
  b
  △ \
  |   \ extension  △
f |     \          | unit
  |       ◿
  a - - - ▷ c
      g
```
-/
structure LeftExtension (f : a ⟶ b) (g : a ⟶ c) where
  /-- The extension of `g` along `f`. -/
  extension : b ⟶ c
  /-- The 2-morphism filling the triangle diagram. -/
  unit : g ⟶ f ≫ extension

/-- Triangle diagrams for (left) lifts.
```
            b
          ◹ |
   lift /   |      △
      /     | f    | unit
    /       ▽
  c - - - ▷ a
       g
```
-/
structure LeftLift (f : b ⟶ a) (g : c ⟶ a) where
  /-- The lift of `g` along `f`. -/
  lift : c ⟶ b
  /-- The 2-morphism filling the triangle diagram. -/
  unit : g ⟶ lift ≫ f

/-- Triangle diagrams for (right) extensions.
```
  b
  △ \
  |   \ extension  | counit
f |     \          ▽
  |       ◿
  a - - - ▷ c
      g
```
-/
structure RightExtension (f : a ⟶ b) (g : a ⟶ c) where
  /-- The extension of `g` along `f`. -/
  extension : b ⟶ c
  /-- The 2-morphism filling the triangle diagram. -/
  counit : f ≫ extension ⟶ g

/-- Triangle diagrams for (right) lifts.
```
            b
          ◹ |
   lift /   |      | counit
      /     | f    ▽
    /       ▽
  c - - - ▷ a
       g
```
-/
structure RightLift (f : b ⟶ a) (g : c ⟶ a) where
  /-- The lift of `g` along `f`. -/
  lift : c ⟶ b
  /-- The 2-morphism filling the triangle diagram. -/
  counit : lift ≫ f ⟶ g

namespace LeftExtension

variable {f : a ⟶ b} {g : a ⟶ c}

/-- The left extension along the identity. -/
def alongId (g : a ⟶ c) : LeftExtension (𝟙 a) g where
  extension := g
  unit := (λ_ g).inv

instance : Inhabited (LeftExtension (𝟙 a) g) := ⟨alongId g⟩

/-- Morphisms between left extensions. -/
structure Hom (s t : LeftExtension f g) where
  /-- The underlying 2-morphism between left extensions. -/
  hom : s.extension ⟶ t.extension
  /-- The units in the two triangle diagrams and `hom` commutes. -/
  w : s.unit ≫ f ◁ hom = t.unit := by aesop_cat

attribute [reassoc (attr := simp)] Hom.w

/-- The category of left extensions. -/
@[simps]
instance : Category (LeftExtension f g) where
  Hom := Hom
  id X := { hom := 𝟙 _ }
  comp P Q := { hom := P.hom ≫ Q.hom }

variable {s t : LeftExtension f g}

instance : Inhabited (Hom t t) := ⟨𝟙 t⟩

@[ext]
theorem hom_ext  (η θ : s ⟶ t) (w : η.hom = θ.hom) : η = θ := by
  cases η
  cases θ
  congr

@[simp]
theorem hom_eq_iff (η θ : s ⟶ t) : η = θ ↔ η.hom = θ.hom :=
  ⟨fun h ↦ by rw [h], hom_ext _ _⟩

end LeftExtension

end Bicategory

end CategoryTheory
