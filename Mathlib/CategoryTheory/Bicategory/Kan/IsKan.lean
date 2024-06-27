/-
Copyright (c) 2023 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import Mathlib.CategoryTheory.Bicategory.Extension

/-!
# Kan extensions and Kan lifts in bicategories

The left Kan extension of a 1-morphism `g : a ⟶ c` along a 1-morphism `f : a ⟶ b` is the initial
object in the category of left extensions `LeftExtension f g`. The universal property can be
accessed by the following definition and lemmas:
* `LeftExtension.IsKan.desc`: the family of 2-morphisms out of the left Kan extension.
* `LeftExtension.IsKan.fac`: the unit of any left extension factors through the left Kan extension.
* `LeftExtension.IsKan.hom_ext`: two 2-morphisms out of the left Kan extension are equal if their
  compositions with each unit are equal.

We also define left Kan lifts, right Kan extensions, and right Kan lifts.

## Implementation Notes

We use the Is-Has design pattern, which is used for the implementation of limits and colimits in
the category theory library. This means that `IsKan t` is a structure containing the data of
2-morphisms which ensure that `t` is a Kan extension, while `HasKan f g` (to be implemented in
the near future) is a `Prop`-valued typeclass asserting that a Kan extension of `g` along `f`
exists.

We define `LeftExtension.IsKan t` for an extension `t : LeftExtension f g` (which is an
abbreviation of `t : StructuredArrow g (precomp _ f)`) to be an abbreviation for
`StructuredArrow.IsUniversal t`. This means that we can use the definitions and lemmas living
in the namespace `StructuredArrow.IsUniversal`.

## References
https://ncatlab.org/nlab/show/Kan+extension

-/

namespace CategoryTheory

namespace Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B] {a b c : B}

namespace LeftExtension

variable {f : a ⟶ b} {g : a ⟶ c}

/-- A left Kan extension of `g` along `f` is an initial object in `LeftExtension f g`. -/
abbrev IsKan (t : LeftExtension f g) := t.IsUniversal

/-- An absolute left Kan extension is a Kan extension that commutes with any 1-morphism. -/
abbrev IsAbsKan (t : LeftExtension f g) :=
  ∀ {x : B} (h : c ⟶ x), IsKan (t.whisker h)

namespace IsKan

variable {s t : LeftExtension f g}

/-- To show that a left extension `t` is a Kan extension, we need to show that for every left
extension `s` there is a unique morphism `t ⟶ s`. -/
abbrev mk (desc : ∀ s, t ⟶ s) (w : ∀ s τ, τ = desc s) :
    IsKan t :=
  .ofUniqueHom desc w

/-- The family of 2-morphisms out of a left Kan extension. -/
abbrev desc (H : IsKan t) (s : LeftExtension f g) : t.extension ⟶ s.extension :=
  StructuredArrow.IsUniversal.desc H s

@[reassoc (attr := simp)]
theorem fac (H : IsKan t) (s : LeftExtension f g) :
    t.unit ≫ f ◁ H.desc s = s.unit :=
  StructuredArrow.IsUniversal.fac H s

/-- Two 2-morphisms out of a left Kan extension are equal if their compositions with
each triangle 2-morphism are equal. -/
theorem hom_ext (H : IsKan t) {k : b ⟶ c} {τ τ' : t.extension ⟶ k}
    (w : t.unit ≫ f ◁ τ = t.unit ≫ f ◁ τ') : τ = τ' :=
  StructuredArrow.IsUniversal.hom_ext H w

end IsKan

namespace IsAbsKan

variable {t : LeftExtension f g}

/-- The family of 2-morphisms out of an absolute left Kan extension. -/
abbrev desc (H : IsAbsKan t) {x : B} {h : c ⟶ x} (s : LeftExtension f (g ≫ h)) :
    t.extension ≫ h ⟶ s.extension :=
  (H h).desc s

variable {x : B} {h : c ⟶ x} {s : LeftExtension f (g ≫ h)}

/-- An absolute left Kan extension is a left Kan extension. -/
def isKan (H : IsAbsKan t) : IsKan t :=
  .mk (fun s ↦ LeftExtension.whiskerIdCancel <| (H (𝟙 _)).to _) <| by
    intro s τ
    ext
    apply (cancel_epi (ρ_ _).hom).mp
    apply (cancel_mono (ρ_ _).inv).mp
    simpa using (H (𝟙 _)).uniq ((LeftExtension.whiskering (𝟙 _)).map τ)

end IsAbsKan

end LeftExtension

namespace LeftLift

variable {f : b ⟶ a} {g : c ⟶ a}

/-- A left Kan lift of `g` along `f` is an initial object in `LeftLift f g`. -/
abbrev IsKan (t : LeftLift f g) := t.IsUniversal

/-- An absolute left Kan lift is a Kan lift such that every 1-morphism commutes with it. -/
abbrev IsAbsKan (t : LeftLift f g) :=
  ∀ {x : B} (h : x ⟶ c), IsKan (t.whisker h)

namespace IsKan

variable {s t : LeftLift f g}

/-- To show that a left lift `t` is a Kan lift, we need to show that for every left lift `s`
there is a unique morphism `t ⟶ s`. -/
abbrev mk (desc : ∀ s, t ⟶ s) (w : ∀ s τ, τ = desc s) :
    IsKan t :=
  .ofUniqueHom desc w

/-- The family of 2-morphisms out of a left Kan lift. -/
abbrev desc (H : IsKan t) (s : LeftLift f g) : t.lift ⟶ s.lift :=
  StructuredArrow.IsUniversal.desc H s

@[reassoc (attr := simp)]
theorem fac (H : IsKan t) (s : LeftLift f g) :
    t.unit ≫ H.desc s ▷ f = s.unit :=
  StructuredArrow.IsUniversal.fac H s

/-- Two 2-morphisms out of a left Kan lift are equal if their compositions with
each triangle 2-morphism are equal. -/
theorem hom_ext (H : IsKan t) {k : c ⟶ b} {τ τ' : t.lift ⟶ k}
    (w : t.unit ≫ τ ▷ f = t.unit ≫ τ' ▷ f) : τ = τ' :=
  StructuredArrow.IsUniversal.hom_ext H w

end IsKan

namespace IsAbsKan

variable {t : LeftLift f g}

/-- The family of 2-morphisms out of an absolute left Kan lift. -/
abbrev desc (H : IsAbsKan t) {x : B} {h : x ⟶ c} (s : LeftLift f (h ≫ g)) :
    h ≫ t.lift ⟶ s.lift :=
  (H h).desc s

variable {x : B} {h : x ⟶ c} {s : LeftLift f (h ≫ g)}

/-- An absolute left Kan lift is a left Kan lift. -/
def isKan (H : IsAbsKan t) : IsKan t :=
  .mk (fun s ↦ LeftLift.whiskerIdCancel <| (H (𝟙 _)).to _) <| by
    intro s τ
    ext
    apply (cancel_epi (λ_ _).hom).mp
    apply (cancel_mono (λ_ _).inv).mp
    simpa using (H (𝟙 _)).uniq ((LeftLift.whiskering (𝟙 _)).map τ)

end IsAbsKan

end LeftLift

namespace RightExtension

variable {f : a ⟶ b} {g : a ⟶ c}

/-- A right Kan extension of `g` along `f` is a terminal object in `RightExtension f g`. -/
abbrev IsKan (t : RightExtension f g) := t.IsUniversal

end RightExtension

namespace RightLift

variable {f : b ⟶ a} {g : c ⟶ a}

/-- A right Kan lift of `g` along `f` is a terminal object in `RightLift f g`. -/
abbrev IsKan (t : RightLift f g) := t.IsUniversal

end RightLift

end Bicategory

end CategoryTheory
