/-
Copyright (c) 2023 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import Mathlib.CategoryTheory.Bicategory.Basic
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.Tactic.CategoryTheory.CancelIso

/-!
# Extensions and lifts in bicategories

We introduce the concept of extensions and lifts within the bicategorical framework. These concepts
are defined by commutative diagrams in the (1-)categorical context. Within the bicategorical
framework, commutative diagrams are replaced by 2-morphisms. Depending on the orientation of the
2-morphisms, we define both left and right extensions (likewise for lifts). The use of left and
right here is a common one in the theory of Kan extensions.

## Implementation notes
We define extensions and lifts as objects in certain comma categories (`StructuredArrow` for left,
and `CostructuredArrow` for right). See the file `CategoryTheory.StructuredArrow` for properties
about these categories. We introduce some intuitive aliases. For example, `LeftExtension.extension`
is an alias for `Comma.right`.

## References
* https://ncatlab.org/nlab/show/lifts+and+extensions
* https://ncatlab.org/nlab/show/Kan+extension

-/

@[expose] public section

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

/-- Construct a left extension from a 1-morphism and a 2-morphism. -/
abbrev mk (h : b ⟶ c) (unit : g ⟶ f ≫ h) : LeftExtension f g :=
  StructuredArrow.mk unit

variable {s t : LeftExtension f g}

/-- To construct a morphism between left extensions, we need a 2-morphism between the extensions,
and to check that it is compatible with the units. -/
abbrev homMk (η : s.extension ⟶ t.extension) (w : s.unit ≫ f ◁ η = t.unit := by cat_disch) :
    s ⟶ t :=
  StructuredArrow.homMk η w

@[reassoc (attr := simp)]
theorem w (η : s ⟶ t) : s.unit ≫ f ◁ η.right = t.unit :=
  StructuredArrow.w η

/-- The left extension along the identity. -/
def alongId (g : a ⟶ c) : LeftExtension (𝟙 a) g := .mk _ (λ_ g).inv

instance : Inhabited (LeftExtension (𝟙 a) g) := ⟨alongId g⟩

/-- Construct a left extension of `g : a ⟶ c` from a left extension of `g ≫ 𝟙 c`. -/
@[simps!]
def ofCompId (t : LeftExtension f (g ≫ 𝟙 c)) : LeftExtension f g :=
  mk (extension t) ((ρ_ g).inv ≫ unit t)

/-- Whisker a 1-morphism to an extension.
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
def whisker (t : LeftExtension f g) {x : B} (h : c ⟶ x) : LeftExtension f (g ≫ h) :=
  .mk _ <| t.unit ▷ h ≫ (α_ _ _ _).hom

@[simp]
theorem whisker_extension (t : LeftExtension f g) {x : B} (h : c ⟶ x) :
    (t.whisker h).extension = t.extension ≫ h :=
  rfl

@[simp]
theorem whisker_unit (t : LeftExtension f g) {x : B} (h : c ⟶ x) :
    (t.whisker h).unit = t.unit ▷ h ≫ (α_ f t.extension h).hom :=
  rfl

/-- Whiskering a 1-morphism is a functor. -/
@[simps]
def whiskering {x : B} (h : c ⟶ x) : LeftExtension f g ⥤ LeftExtension f (g ≫ h) where
  obj t := t.whisker h
  map η := LeftExtension.homMk (η.right ▷ h) <| by
    simp [-LeftExtension.w, ← LeftExtension.w η]

set_option backward.isDefEq.respectTransparency false in
/-- Define a morphism between left extensions by cancelling the whiskered identities. -/
@[simps! right]
def whiskerIdCancel
    (s : LeftExtension f (g ≫ 𝟙 c)) {t : LeftExtension f g} (τ : s ⟶ t.whisker (𝟙 c)) :
    s.ofCompId ⟶ t :=
  LeftExtension.homMk (τ.right ≫ (ρ_ _).hom)

set_option backward.isDefEq.respectTransparency false in
/-- Construct a morphism between whiskered extensions. -/
@[simps! right]
def whiskerHom (i : s ⟶ t) {x : B} (h : c ⟶ x) :
    s.whisker h ⟶ t.whisker h :=
  StructuredArrow.homMk (i.right ▷ h) <| by
    rw [← cancel_mono (α_ _ _ _).inv]
    calc
      _ = (unit s ≫ f ◁ i.right) ▷ h := by simp [-LeftExtension.w]
      _ = unit t ▷ h := congrArg (· ▷ h) (LeftExtension.w i)
      _ = _ := by simp

/-- Construct an isomorphism between whiskered extensions. -/
def whiskerIso (i : s ≅ t) {x : B} (h : c ⟶ x) :
    s.whisker h ≅ t.whisker h :=
  Iso.mk (whiskerHom i.hom h) (whiskerHom i.inv h)
    (StructuredArrow.hom_ext _ _ <|
      calc
        _ = (i.hom ≫ i.inv).right ▷ h := by simp [-Iso.hom_inv_id]
        _ = 𝟙 _ := by simp [Iso.hom_inv_id])
    (StructuredArrow.hom_ext _ _ <|
      calc
        _ = (i.inv ≫ i.hom).right ▷ h := by simp [-Iso.inv_hom_id]
        _ = 𝟙 _ := by simp [Iso.inv_hom_id])

set_option backward.defeqAttrib.useBackward true in
/-- The isomorphism between left extensions induced by a right unitor. -/
@[simps! hom_right inv_right]
def whiskerOfCompIdIsoSelf (t : LeftExtension f g) : (t.whisker (𝟙 c)).ofCompId ≅ t :=
  StructuredArrow.isoMk (ρ_ (t.extension))

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

/-- Construct a left lift from a 1-morphism and a 2-morphism. -/
abbrev mk (h : c ⟶ b) (unit : g ⟶ h ≫ f) : LeftLift f g :=
  StructuredArrow.mk unit

variable {s t : LeftLift f g}

/-- To construct a morphism between left lifts, we need a 2-morphism between the lifts,
and to check that it is compatible with the units. -/
abbrev homMk (η : s.lift ⟶ t.lift) (w : s.unit ≫ η ▷ f = t.unit := by cat_disch) :
    s ⟶ t :=
  StructuredArrow.homMk η w

@[reassoc (attr := simp)]
theorem w (h : s ⟶ t) : s.unit ≫ h.right ▷ f = t.unit :=
  StructuredArrow.w h

/-- The left lift along the identity. -/
def alongId (g : c ⟶ a) : LeftLift (𝟙 a) g := .mk _ (ρ_ g).inv

instance : Inhabited (LeftLift (𝟙 a) g) := ⟨alongId g⟩

/-- Construct a left lift along `g : c ⟶ a` from a left lift along `𝟙 c ≫ g`. -/
@[simps!]
def ofIdComp (t : LeftLift f (𝟙 c ≫ g)) : LeftLift f g :=
  mk (lift t) ((λ_ _).inv ≫ unit t)

/-- Whisker a 1-morphism to a lift.
```
                    b
                  ◹ |
           lift /   |      △
              /     | f    | unit
            /       ▽
x - - - ▷ c - - - ▷ a
     h         g
```
-/
def whisker (t : LeftLift f g) {x : B} (h : x ⟶ c) : LeftLift f (h ≫ g) :=
  .mk _ <| h ◁ t.unit ≫ (α_ _ _ _).inv

@[simp]
theorem whisker_lift (t : LeftLift f g) {x : B} (h : x ⟶ c) :
    (t.whisker h).lift = h ≫ t.lift :=
  rfl

@[simp]
theorem whisker_unit (t : LeftLift f g) {x : B} (h : x ⟶ c) :
    (t.whisker h).unit = h ◁ t.unit ≫ (α_ h t.lift f).inv :=
  rfl

/-- Whiskering a 1-morphism is a functor. -/
@[simps]
def whiskering {x : B} (h : x ⟶ c) : LeftLift f g ⥤ LeftLift f (h ≫ g) where
  obj t := t.whisker h
  map η := LeftLift.homMk (h ◁ η.right) <| by
    dsimp only [whisker_lift, whisker_unit]
    rw [← LeftLift.w η]
    simp [-LeftLift.w]

set_option backward.isDefEq.respectTransparency false in
/-- Define a morphism between left lifts by cancelling the whiskered identities. -/
@[simps! right]
def whiskerIdCancel
    (s : LeftLift f (𝟙 c ≫ g)) {t : LeftLift f g} (τ : s ⟶ t.whisker (𝟙 c)) :
    s.ofIdComp ⟶ t :=
  LeftLift.homMk (τ.right ≫ (λ_ _).hom)

set_option backward.isDefEq.respectTransparency false in
/-- Construct a morphism between whiskered lifts. -/
@[simps! right]
def whiskerHom (i : s ⟶ t) {x : B} (h : x ⟶ c) :
    s.whisker h ⟶ t.whisker h :=
  StructuredArrow.homMk (h ◁ i.right) <| by
    rw [← cancel_mono (α_ h _ _).hom]
    calc
      _ = h ◁ (unit s ≫ i.right ▷ f) := by simp [-LeftLift.w]
      _ = h ◁ unit t := congrArg (h ◁ ·) (LeftLift.w i)
      _ = _ := by simp

/-- Construct an isomorphism between whiskered lifts. -/
def whiskerIso (i : s ≅ t) {x : B} (h : x ⟶ c) :
    s.whisker h ≅ t.whisker h :=
  Iso.mk (whiskerHom i.hom h) (whiskerHom i.inv h)
    (StructuredArrow.hom_ext _ _ <|
      calc
        _ = h ◁ (i.hom ≫ i.inv).right := by simp [-Iso.hom_inv_id]
        _ = 𝟙 _ := by simp [Iso.hom_inv_id])
    (StructuredArrow.hom_ext _ _ <|
      calc
        _ = h ◁ (i.inv ≫ i.hom).right := by simp [-Iso.inv_hom_id]
        _ = 𝟙 _ := by simp [Iso.inv_hom_id])

set_option backward.defeqAttrib.useBackward true in
/-- The isomorphism between left lifts induced by a left unitor. -/
@[simps! hom_right inv_right]
def whiskerOfIdCompIsoSelf (t : LeftLift f g) : (t.whisker (𝟙 c)).ofIdComp ≅ t :=
  StructuredArrow.isoMk (λ_ (lift t))

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

/-- Construct a right extension from a 1-morphism and a 2-morphism. -/
abbrev mk (h : b ⟶ c) (counit : f ≫ h ⟶ g) : RightExtension f g :=
  CostructuredArrow.mk counit

/-- To construct a morphism between right extensions, we need a 2-morphism between the extensions,
and to check that it is compatible with the counits. -/
abbrev homMk {s t : RightExtension f g} (η : s.extension ⟶ t.extension)
    (w : f ◁ η ≫ t.counit = s.counit) : s ⟶ t :=
  CostructuredArrow.homMk η w

@[reassoc (attr := simp)]
theorem w {s t : RightExtension f g} (η : s ⟶ t) :
    f ◁ η.left ≫ t.counit = s.counit :=
  CostructuredArrow.w η

/-- The right extension along the identity. -/
def alongId (g : a ⟶ c) : RightExtension (𝟙 a) g := .mk _ (λ_ g).hom

instance : Inhabited (RightExtension (𝟙 a) g) := ⟨alongId g⟩

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

/-- Construct a right lift from a 1-morphism and a 2-morphism. -/
abbrev mk (h : c ⟶ b) (counit : h ≫ f ⟶ g) : RightLift f g :=
  CostructuredArrow.mk counit

/-- To construct a morphism between right lifts, we need a 2-morphism between the lifts,
and to check that it is compatible with the counits. -/
abbrev homMk {s t : RightLift f g} (η : s.lift ⟶ t.lift) (w : η ▷ f ≫ t.counit = s.counit) :
    s ⟶ t :=
  CostructuredArrow.homMk η w

@[reassoc (attr := simp)]
theorem w {s t : RightLift f g} (h : s ⟶ t) :
    h.left ▷ f ≫ t.counit = s.counit :=
  CostructuredArrow.w h

/-- The right lift along the identity. -/
def alongId (g : c ⟶ a) : RightLift (𝟙 a) g := .mk _ (ρ_ g).hom

instance : Inhabited (RightLift (𝟙 a) g) := ⟨alongId g⟩

end RightLift

end Bicategory

end CategoryTheory
