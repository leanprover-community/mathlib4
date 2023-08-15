/-
Copyright (c) 2023 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import Mathlib.CategoryTheory.Bicategory.Basic
import Mathlib.CategoryTheory.StructuredArrow

/-!
# Extensions and lifts in bicategories

We introduce the concept of extensions and lifts within the bicategorical framework. These concepts
are defined by commutative diagrams in the (1-)categorical context. Within the bicategorical
framework, commutative diagrams are replaced by 2-morphisms. Depending on the orientation of the
2-morphisms, we define both left and right extensions (likewise for lifts).

The use of left and right here is a common one in the theory of Kan extensions.

## Implementation notes
We define extensions and lifts as objects in certain comma categories.

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
abbrev LeftExtension (f : a ⟶ b) (g : a ⟶ c) := StructuredArrow g (precomp _ f)

namespace LeftExtension

variable {f : a ⟶ b} {g : a ⟶ c}

/-- The extension of `g` along `f`. -/
abbrev extension (t : LeftExtension f g) : b ⟶ c := t.right

/-- The 2-morphism filling the triangle diagram. -/
abbrev unit (t : LeftExtension f g) : g ⟶ f ≫ t.extension := t.hom

/-- The left extension along the identity. -/
def alongId (g : a ⟶ c) : LeftExtension (𝟙 a) g := StructuredArrow.mk (λ_ g).inv

instance : Inhabited (LeftExtension (𝟙 a) g) := ⟨alongId g⟩

/-- Whisker an extension by a 1-morphism.
```
  b
  △ \
  |   \ extension  △
f |     \          | unit
  |       ◿
  a - - - ▷ c - - - ▷ x
      g         h
```
-/
@[simps!]
def whisker (t : LeftExtension f g) {x : B} (h : c ⟶ x) : LeftExtension f (g ≫ h) :=
  StructuredArrow.mk <| t.unit ▷ h ≫ (α_ _ _ _).hom

/-- Whiskering by a 1-morphism is a functor. -/
@[simps]
def whiskering {x : B} (h : c ⟶ x) : LeftExtension f g ⥤ LeftExtension f (g ≫ h) where
  obj t := t.whisker h
  map η := StructuredArrow.homMk (η.right ▷ h) <| by
    simp [Functor.const_obj_obj, whisker_right, precomp_obj, whisker_hom, precomp_map,
      Category.assoc, ← StructuredArrow.w η, comp_whiskerRight, whisker_assoc, Iso.inv_hom_id,
      Category.comp_id]

/-- Define a morphism between left extensions by cancelling the whiskered identities. -/
@[simps!]
def whiskerIdCancel {s t : LeftExtension f g} (τ : s.whisker (𝟙 c) ⟶ t.whisker (𝟙 c)) :
    s ⟶ t :=
  StructuredArrow.homMk ((ρ_ _).inv ≫ τ.right ≫ (ρ_ _).hom) <| by
    have := StructuredArrow.w τ
    simp at this
    simp [reassoc_of% this]

end LeftExtension

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
abbrev LeftLift (f : b ⟶ a) (g : c ⟶ a) := StructuredArrow g (postcomp _ f)

namespace LeftLift

variable {f : b ⟶ a} {g : c ⟶ a}

/-- The lift of `g` along `f`. -/
abbrev lift (t : LeftLift f g) : c ⟶ b := t.right

/-- The 2-morphism filling the triangle diagram. -/
abbrev unit (t : LeftLift f g) : g ⟶ t.lift ≫ f := t.hom

end LeftLift

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
abbrev RightExtension (f : a ⟶ b) (g : a ⟶ c) := CostructuredArrow (precomp _ f) g

namespace RightExtension

variable {f : a ⟶ b} {g : a ⟶ c}

/-- The extension of `g` along `f`. -/
abbrev extension (t : RightExtension f g) : b ⟶ c := t.left

/-- The 2-morphism filling the triangle diagram. -/
abbrev counit (t : RightExtension f g) : f ≫ t.extension ⟶ g := t.hom

end RightExtension

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
abbrev RightLift (f : b ⟶ a) (g : c ⟶ a) := CostructuredArrow (postcomp _ f) g

namespace RightLift

variable {f : b ⟶ a} {g : c ⟶ a}

/-- The lift of `g` along `f`. -/
abbrev lift (t : RightLift f g) : c ⟶ b := t.left

/-- The 2-morphism filling the triangle diagram. -/
abbrev counit (t : RightLift f g) : t.lift ≫ f ⟶ g := t.hom

end RightLift

end Bicategory

end CategoryTheory
