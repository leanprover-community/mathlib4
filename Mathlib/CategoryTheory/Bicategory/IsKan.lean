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
structure IsKan (t : LeftExtension f g) where
  /-- The family of morphisms out of a left Kan extension. -/
  descHom : ∀ s : LeftExtension f g, t ⟶ s
  /-- The uniqueness of the family of morphisms out of a left Kan extension. -/
  uniq : ∀ (s : LeftExtension f g) (τ : t ⟶ s), τ = descHom s

attribute [nolint simpNF] IsKan.mk.injEq

namespace IsKan

variable {s t : LeftExtension f g}

instance : Subsingleton (IsKan t) :=
  ⟨by intro P Q; cases P; cases Q; aesop_cat⟩

/-- The family of 2-morphisms out of a left Kan extension. -/
def desc (H : IsKan t) (s : LeftExtension f g) : t.extension ⟶ s.extension :=
  (H.descHom s).hom

@[simp]
theorem descHom_hom (H : IsKan t) (s : LeftExtension f g) :
    (H.descHom s).hom = H.desc s :=
  rfl

/-- The unit of any left extension factors through the left Kan extension. -/
@[reassoc (attr := simp)]
theorem fac (H : IsKan t) (s : LeftExtension f g) :
    t.unit ≫ f ◁ H.desc s = s.unit :=
  (H.descHom s).w

theorem uniq_LeftExtensionHom (H : IsKan t) (τ τ' : t ⟶ s) : τ = τ' :=
  (H.uniq s τ).trans (H.uniq s τ').symm

theorem hom_desc (H : IsKan t) {k : b ⟶ c} (τ : t.extension ⟶ k) :
    τ = H.desc ⟨k, t.unit ≫ f ◁ τ⟩ :=
  congrArg LeftExtension.Hom.hom (H.uniq ⟨k, t.unit ≫ f ◁ τ⟩ ⟨τ, rfl⟩)

/-- Two 2-morphisms out of a left Kan extension are equal if their compositions with
  each unit 2-morphism are equal. -/
theorem hom_ext (H : IsKan t) {k : b ⟶ c} {τ τ' : t.extension ⟶ k}
    (w : t.unit ≫ f ◁ τ = t.unit ≫ f ◁ τ') : τ = τ' := by
  rw [H.hom_desc τ, H.hom_desc τ']; congr

theorem existsUnique (H : IsKan t) (s : LeftExtension f g) :
    ∃! τ : t.extension ⟶ s.extension, t.unit ≫ f ◁ τ = s.unit :=
  ⟨H.desc s, H.fac s, fun τ w ↦ H.hom_ext <| by simp [w]⟩

end IsKan

end LeftExtension

end Bicategory

end CategoryTheory
