/-
Copyright (c) 2023 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import Mathlib.CategoryTheory.Bicategory.Extension

/-!
# Kan extensions and Kan lifts in bicategories

The left Kan extension of a 1-morphism `g : a ⟶ c` along a 1-morphism `f : a ⟶ b` is the initial
object in the category of left extensions `LeftExtension f g`.

We introduce a structure `LeftExtension.IsKan t` for an extension `t : LeftExtension f g`. This
structure consists of a family of 2-morphisms out of `t` together with the fact that such a family
of 2-morphisms is unique. We have the following definition and lemmas:
* `LeftExtension.IsKan.desc`: the family of 2-morphisms out of the left Kan extension.
* `LeftExtension.IsKan.fac`: the unit of any left extension factors through the left Kan extension.
* `LeftExtension.IsKan.hom_ext`: two 2-morphisms out of a left Kan extension are equal if their
  compositions with each unit are equal.

## Implementation Notes
We use the Is-Has design pattern, which is used for the implementation of limits and colimits in
the category theory library. This means that `is_Kan t` is a structure containing the data of
2-morphisms which ensure that `t` is a Kan extension, while `HasKan f g` (to be implemented in
the near future) is a `Prop`-valued typeclass asserting that a Kan extension of `g` along `f`
exists.

## References
https://ncatlab.org/nlab/show/Kan+extension

## Todo
left Kan lifts, right Kan extensions, and right Kan lifts
-/

namespace CategoryTheory

namespace Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B] {a b c : B}

namespace LeftExtension

variable {f : a ⟶ b} {g : a ⟶ c}

/-- A left Kan extension of `g` along `f` is an initial object in `LeftExtension f g`. -/
abbrev IsKan (t : LeftExtension f g) := t.IsUniversal

end LeftExtension

end Bicategory

end CategoryTheory
