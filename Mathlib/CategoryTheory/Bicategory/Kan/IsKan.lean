/-
Copyright (c) 2023 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Bicategory.Extension
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.Tactic.CategoryTheory.Bicategory.Basic

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
2-morphisms which ensure that `t` is a Kan extension, while `HasLeftKanExtension f g`
(and similarly for lifts) defined in `CategoryTheory.Bicategory.Kan.HasKan`
is a `Prop`-valued typeclass asserting that a Kan extension of `g` along `f` exists.

We define `LeftExtension.IsKan t` for an extension `t : LeftExtension f g` (which is an
abbreviation of `t : StructuredArrow g (precomp _ f)`) to be an abbreviation for
`StructuredArrow.IsUniversal t`. This means that we can use the definitions and lemmas living
in the namespace `StructuredArrow.IsUniversal`.

## References
https://ncatlab.org/nlab/show/Kan+extension

-/

@[expose] public section

namespace CategoryTheory

namespace Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B] {a b c d : B}

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

/-- Kan extensions on `g` along `f` are unique up to isomorphism. -/
def uniqueUpToIso (P : IsKan s) (Q : IsKan t) : s ≅ t :=
  Limits.IsInitial.uniqueUpToIso P Q

@[simp]
theorem uniqueUpToIso_hom_right (P : IsKan s) (Q : IsKan t) :
    (uniqueUpToIso P Q).hom.right = P.desc t := rfl

@[simp]
theorem uniqueUpToIso_inv_right (P : IsKan s) (Q : IsKan t) :
    (uniqueUpToIso P Q).inv.right = Q.desc s := rfl

/-- Transport evidence that a left extension is a Kan extension across an isomorphism
of extensions. -/
def ofIsoKan (P : IsKan s) (i : s ≅ t) : IsKan t :=
  Limits.IsInitial.ofIso P i

set_option backward.isDefEq.respectTransparency false in
/-- If `t : LeftExtension f (g ≫ 𝟙 c)` is a Kan extension, then `t.ofCompId : LeftExtension f g`
is also a Kan extension. -/
def ofCompId (t : LeftExtension f (g ≫ 𝟙 c)) (P : IsKan t) : IsKan t.ofCompId :=
  .mk (fun s ↦ t.whiskerIdCancel <| P.to (s.whisker (𝟙 c))) <| by
    intro s τ
    ext
    apply P.hom_ext
    simp [← LeftExtension.w τ]

/-- If `s ≅ t` and `IsKan (s.whisker h)`, then `IsKan (t.whisker h)`. -/
def whiskerOfCommute (s t : LeftExtension f g) (i : s ≅ t) {x : B} (h : c ⟶ x)
    (P : IsKan (s.whisker h)) :
    IsKan (t.whisker h) :=
  P.ofIsoKan <| whiskerIso i h

/-- `LeftExtension.ofIso` preserves Kan extensions. -/
noncomputable def ofIso {f' : a ⟶ b} {g' : a ⟶ c} (H : IsKan t) (ef : f ≅ f') (eg : g ≅ g') :
    IsKan (t.ofIso ef eg) :=
  Limits.IsInitial.isInitialObj (LeftExtension.mapIso ef eg).functor t H

end IsKan

namespace IsAbsKan

variable {s t : LeftExtension f g}

/-- The family of 2-morphisms out of an absolute left Kan extension. -/
abbrev desc (H : IsAbsKan t) {x : B} {h : c ⟶ x} (s : LeftExtension f (g ≫ h)) :
    t.extension ≫ h ⟶ s.extension :=
  (H h).desc s

/-- An absolute left Kan extension is a left Kan extension. -/
def isKan (H : IsAbsKan t) : IsKan t :=
  ((H (𝟙 c)).ofCompId _).ofIsoKan <| whiskerOfCompIdIsoSelf t

/-- Transport evidence that a left extension is a Kan extension across an isomorphism
of extensions. -/
def ofIsoAbsKan (P : IsAbsKan s) (i : s ≅ t) : IsAbsKan t :=
  fun h ↦ (P h).ofIsoKan (whiskerIso i h)

/-- `LeftExtension.ofIso` preserves absolute left Kan extensions. -/
noncomputable def ofIso {f' : a ⟶ b} {g' : a ⟶ c} (H : IsAbsKan t) (ef : f ≅ f') (eg : g ≅ g') :
    IsAbsKan (t.ofIso ef eg) :=
  fun h ↦ ((H h).ofIso ef (whiskerRightIso eg h)).ofIsoKan (whiskerOfIso ef eg t h)

end IsAbsKan

section Paste

variable {f : a ⟶ b} {g : a ⟶ c} {h : b ⟶ d}
variable {t : LeftExtension f g} {s : LeftExtension h t.extension}

/-- Given a left Kan extension `t` of `g` along `f`, a left extension `u` of `g` along `f ≫ h`
induces, via the universal property of `t`, a left extension of `t.extension` along `h`. -/
def IsKan.ofIsKanTop (Ht : IsKan t) (u : LeftExtension (f ≫ h) g) : LeftExtension h t.extension :=
  .mk u.extension (Ht.desc (.mk (h ≫ u.extension) (u.unit ≫ (α_ f h u.extension).hom)))

@[simp]
theorem IsKan.ofIsKanTop_extension (Ht : IsKan t) (u : LeftExtension (f ≫ h) g) :
    (Ht.ofIsKanTop u).extension = u.extension :=
  rfl

theorem IsKan.ofIsKanTop_fac (Ht : IsKan t) (u : LeftExtension (f ≫ h) g) :
    t.unit ≫ f ◁ (Ht.ofIsKanTop u).unit = u.unit ≫ (α_ f h u.extension).hom := by
  simpa [IsKan.ofIsKanTop] using
    Ht.fac (.mk (h ≫ u.extension) (u.unit ≫ (α_ f h u.extension).hom))

set_option backward.isDefEq.respectTransparency false in
/-- Pasting of left extensions preserves being Kan. -/
def IsKan.paste (Ht : IsKan t) (Hs : IsKan s) : IsKan (t.paste s) :=
  IsKan.mk
    (fun u ↦
      LeftExtension.homMk (Hs.desc (Ht.ofIsKanTop u)) <| by
        rw [paste_unit, ← cancel_mono (α_ f h u.extension).hom, ← Ht.ofIsKanTop_fac,
          ← Hs.fac (Ht.ofIsKanTop u)]
        bicategory)
    (fun u τ ↦ by
      ext
      apply Hs.hom_ext
      apply Ht.hom_ext
      rw [homMk_right, Hs.fac, Ht.ofIsKanTop_fac, ← LeftExtension.w τ, paste_unit]
      bicategory)

set_option backward.isDefEq.respectTransparency false in
/-- Given a left extension `t` of `g` along `f` and a left extension `s` of `t` along `h`, if `t`
and `t.paste s` are Kan, then so is `s`. -/
def IsKan.ofPaste (Ht : IsKan t) (Hp : IsKan (t.paste s)) : IsKan s :=
  IsKan.mk
    (fun v ↦
      LeftExtension.homMk (Hp.desc (t.paste v)) <| Ht.hom_ext <| by
        rw [← cancel_mono (α_ f h v.extension).inv, Category.assoc, Category.assoc, ← paste_unit,
          ← Hp.fac (t.paste v), paste_unit]
        bicategory)
    (fun v τ ↦ by
      ext
      apply Hp.hom_ext
      rw [homMk_right, Hp.fac, paste_unit, paste_unit, ← LeftExtension.w τ]
      bicategory)

/-- Let `t` be a left Kan extension of `g` along `f` and `s` a left extension of `t` along `h`. Then
`s` is Kan if and only if `t.paste s` is Kan. -/
def isKanEquivIsKanPaste (Ht : IsKan t) : (IsKan s) ≃ (IsKan (t.paste s)) :=
  equivOfSubsingletonOfSubsingleton Ht.paste Ht.ofPaste

/-- Pasting of left extensions preserves being absolute Kan. -/
noncomputable def IsAbsKan.paste (H : IsAbsKan t) (Hs : IsAbsKan s) :
    IsAbsKan (t.paste s) :=
  fun k ↦ ((H k).paste (Hs k)).ofIsoKan (pasteWhiskerIso t s k).symm

/-- Given a left extension `t` of `g` along `f` and a left extension `s` of `t` along `h`, if `t`
and `t.paste s` are absolute Kan, then so is `s`. -/
noncomputable def IsAbsKan.ofPaste (H : IsAbsKan t) (Hp : IsAbsKan (t.paste s)) :
    IsAbsKan s :=
  fun k ↦ (H k).ofPaste ((Hp k).ofIsoKan (pasteWhiskerIso t s k))

/-- Let `t` be an absolute left Kan extension of `g` along `f` and `s` a left extension of `t` along
`h`. Then `s` is absolute Kan if and only if `t.paste s` is absolute Kan. -/
noncomputable def isAbsKanEquivIsAbsKanPaste (H : IsAbsKan t) :
    (IsAbsKan s) ≃ (IsAbsKan (t.paste s)) :=
  equivOfSubsingletonOfSubsingleton H.paste H.ofPaste

end Paste

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

/-- Kan lifts on `g` along `f` are unique up to isomorphism. -/
def uniqueUpToIso (P : IsKan s) (Q : IsKan t) : s ≅ t :=
  Limits.IsInitial.uniqueUpToIso P Q

@[simp]
theorem uniqueUpToIso_hom_right (P : IsKan s) (Q : IsKan t) :
    (uniqueUpToIso P Q).hom.right = P.desc t := rfl

@[simp]
theorem uniqueUpToIso_inv_right (P : IsKan s) (Q : IsKan t) :
    (uniqueUpToIso P Q).inv.right = Q.desc s := rfl

/-- Transport evidence that a left lift is a Kan lift across an isomorphism of lifts. -/
def ofIsoKan (P : IsKan s) (i : s ≅ t) : IsKan t :=
  Limits.IsInitial.ofIso P i

set_option backward.isDefEq.respectTransparency false in
/-- If `t : LeftLift f (𝟙 c ≫ g)` is a Kan lift, then `t.ofIdComp : LeftLift f g` is also
a Kan lift. -/
def ofIdComp (t : LeftLift f (𝟙 c ≫ g)) (P : IsKan t) : IsKan t.ofIdComp :=
  .mk (fun s ↦ t.whiskerIdCancel <| P.to (s.whisker (𝟙 c))) <| by
    intro s τ
    ext
    apply P.hom_ext
    simp [← LeftLift.w τ]

/-- If `s ≅ t` and `IsKan (s.whisker h)`, then `IsKan (t.whisker h)`. -/
def whiskerOfCommute (s t : LeftLift f g) (i : s ≅ t) {x : B} (h : x ⟶ c)
    (P : IsKan (s.whisker h)) :
    IsKan (t.whisker h) :=
  P.ofIsoKan <| whiskerIso i h

/-- `LeftLift.ofIso` preserves Kan lifts. -/
noncomputable def ofIso {f' : b ⟶ a} {g' : c ⟶ a} (H : IsKan t) (ef : f ≅ f') (eg : g ≅ g') :
    IsKan (t.ofIso ef eg) :=
  Limits.IsInitial.isInitialObj (LeftLift.mapIso ef eg).functor t H

end IsKan

namespace IsAbsKan

variable {s t : LeftLift f g}

/-- The family of 2-morphisms out of an absolute left Kan lift. -/
abbrev desc (H : IsAbsKan t) {x : B} {h : x ⟶ c} (s : LeftLift f (h ≫ g)) :
    h ≫ t.lift ⟶ s.lift :=
  (H h).desc s

/-- An absolute left Kan lift is a left Kan lift. -/
def isKan (H : IsAbsKan t) : IsKan t :=
  ((H (𝟙 c)).ofIdComp _).ofIsoKan <| whiskerOfIdCompIsoSelf t

/-- Transport evidence that a left lift is a Kan lift across an isomorphism of lifts. -/
def ofIsoAbsKan (P : IsAbsKan s) (i : s ≅ t) : IsAbsKan t :=
  fun h ↦ (P h).ofIsoKan (whiskerIso i h)

/-- `LeftLift.ofIso` preserves absolute left Kan lifts. -/
noncomputable def ofIso {f' : b ⟶ a} {g' : c ⟶ a} (H : IsAbsKan t) (ef : f ≅ f') (eg : g ≅ g') :
    IsAbsKan (t.ofIso ef eg) :=
  fun h ↦ ((H h).ofIso ef (whiskerLeftIso h eg)).ofIsoKan (whiskerOfIso ef eg t h)

end IsAbsKan

section Paste

variable {f : b ⟶ a} {g : d ⟶ a} {h : c ⟶ b}
variable {t : LeftLift f g} {s : LeftLift h t.lift}

/-- Given a left Kan lift `t` of `g` along `f`, a left lift `u` of `g` along `h ≫ f` induces,
via the universal property of `t`, a left lift of `t.lift` along `h`.
-/
def IsKan.ofIsKanTop (Ht : IsKan t) (u : LeftLift (h ≫ f) g) : LeftLift h t.lift :=
  .mk u.lift (Ht.desc (.mk (u.lift ≫ h) (u.unit ≫ (α_ u.lift h f).inv)))

@[simp]
theorem IsKan.ofIsKanTop_lift (Ht : IsKan t) (u : LeftLift (h ≫ f) g) :
    (Ht.ofIsKanTop u).lift = u.lift :=
  rfl

theorem IsKan.ofIsKanTop_fac (Ht : IsKan t) (u : LeftLift (h ≫ f) g) :
    t.unit ≫ (Ht.ofIsKanTop u).unit ▷ f = u.unit ≫ (α_ u.lift h f).inv := by
  simpa [IsKan.ofIsKanTop] using Ht.fac (.mk (u.lift ≫ h) (u.unit ≫ (α_ u.lift h f).inv))

set_option backward.isDefEq.respectTransparency false in
/-- Pasting of left lifts preserves being Kan. -/
def IsKan.paste (Ht : IsKan t) (Hs : IsKan s) : IsKan (t.paste s) :=
  IsKan.mk
    (fun u ↦
      LeftLift.homMk (Hs.desc (Ht.ofIsKanTop u)) <| by
        rw [paste_unit, ← cancel_mono (α_ u.lift h f).inv, ← Ht.ofIsKanTop_fac,
          ← Hs.fac (Ht.ofIsKanTop u)]
        bicategory)
    (fun u τ ↦ by
      ext
      apply Hs.hom_ext
      apply Ht.hom_ext
      rw [homMk_right, Hs.fac, Ht.ofIsKanTop_fac, ← LeftLift.w τ, paste_unit]
      bicategory)

set_option backward.isDefEq.respectTransparency false in
/-- Given a left lift `t` of `g` along `f` and a left lift `s` of `t` along `h`, if `t` and
`t.paste s` are Kan, then so is `s`. -/
def IsKan.ofPaste (Ht : IsKan t) (Hp : IsKan (t.paste s)) : IsKan s :=
  IsKan.mk
    (fun v ↦
      LeftLift.homMk (Hp.desc (t.paste v)) <| Ht.hom_ext <| by
        rw [← cancel_mono (α_ v.lift h f).hom, Category.assoc, Category.assoc, ← paste_unit,
          ← Hp.fac (t.paste v), paste_unit]
        bicategory)
    (fun v τ ↦ by
      ext
      apply Hp.hom_ext
      rw [homMk_right, Hp.fac, paste_unit, paste_unit, ← LeftLift.w τ]
      bicategory)

/-- Let `t` be a left Kan lift of `g` along `f` and `s` a left lift of `t` along `h`. Then `s` is
Kan if and only if `t.paste s` is Kan. -/
def isKanEquivIsKanPaste (Ht : IsKan t) : (IsKan s) ≃ (IsKan (t.paste s)) :=
  equivOfSubsingletonOfSubsingleton Ht.paste Ht.ofPaste

/-- Pasting of left lifts preserves being absolute Kan. -/
noncomputable def IsAbsKan.paste (H : IsAbsKan t) (Hs : IsAbsKan s) :
    IsAbsKan (t.paste s) :=
  fun k ↦ ((H k).paste (Hs k)).ofIsoKan (pasteWhiskerIso t s k).symm

/-- Given a left lift `t` of `g` along `f` and a left lift `s` of `t` along `h`, if `t` and
`t.paste s` are absolute Kan, then so is `s`. -/
noncomputable def IsAbsKan.ofPaste (H : IsAbsKan t) (Hp : IsAbsKan (t.paste s)) :
    IsAbsKan s :=
  fun k ↦ (H k).ofPaste ((Hp k).ofIsoKan (pasteWhiskerIso t s k))

/-- Let `t` be an absolute left Kan lift of `g` along `f` and `s` a left lift of `t` along `h`. Then
`s` is absolute Kan if and only if `t.paste s` is absolute Kan. -/
noncomputable def isAbsKanEquivIsAbsKanPaste (H : IsAbsKan t) :
    (IsAbsKan s) ≃ (IsAbsKan (t.paste s)) :=
  equivOfSubsingletonOfSubsingleton H.paste H.ofPaste

end Paste

end LeftLift

namespace RightExtension

variable {f : a ⟶ b} {g : a ⟶ c}

/-- A right Kan extension of `g` along `f` is a terminal object in `RightExtension f g`. -/
abbrev IsKan (t : RightExtension f g) := t.IsUniversal

/-- An absolute right Kan extension is a Kan extension that commutes with any 1-morphism. -/
abbrev IsAbsKan (t : RightExtension f g) :=
  ∀ {x : B} (h : c ⟶ x), IsKan (t.whisker h)

namespace IsKan

variable {s t : RightExtension f g}

/-- To show that a right extension `t` is a Kan extension, we need to show that for every right
extension `s` there is a unique morphism `s ⟶ t`. -/
abbrev mk (desc : ∀ s, s ⟶ t) (w : ∀ s τ, τ = desc s) :
    IsKan t :=
  .ofUniqueHom desc w

/-- The family of 2-morphisms into a right Kan extension. -/
abbrev desc (H : IsKan t) (s : RightExtension f g) : s.extension ⟶ t.extension :=
  CostructuredArrow.IsUniversal.lift H s

@[reassoc (attr := simp)]
theorem fac (H : IsKan t) (s : RightExtension f g) :
    f ◁ H.desc s ≫ t.counit = s.counit :=
  CostructuredArrow.IsUniversal.fac H s

/-- Two 2-morphisms into a right Kan extension are equal if their compositions with
each triangle 2-morphism are equal. -/
theorem hom_ext (H : IsKan t) {k : b ⟶ c} {τ τ' : k ⟶ t.extension}
    (w : f ◁ τ ≫ t.counit = f ◁ τ' ≫ t.counit) : τ = τ' :=
  CostructuredArrow.IsUniversal.hom_ext H w

/-- Kan extensions on `g` along `f` are unique up to isomorphism. -/
def uniqueUpToIso (P : IsKan s) (Q : IsKan t) : s ≅ t :=
  Limits.IsTerminal.uniqueUpToIso P Q

@[simp]
theorem uniqueUpToIso_hom_left (P : IsKan s) (Q : IsKan t) :
    (uniqueUpToIso P Q).hom.left = Q.desc s := rfl

@[simp]
theorem uniqueUpToIso_inv_left (P : IsKan s) (Q : IsKan t) :
    (uniqueUpToIso P Q).inv.left = P.desc t := rfl

/-- Transport evidence that a right extension is a Kan extension across an isomorphism
of extensions. -/
def ofIsoKan (P : IsKan s) (i : s ≅ t) : IsKan t :=
  Limits.IsTerminal.ofIso P i

set_option backward.isDefEq.respectTransparency false in
/-- If `t : RightExtension f (g ≫ 𝟙 c)` is a Kan extension, then `t.ofCompId : RightExtension f g`
is also a Kan extension. -/
def ofCompId (t : RightExtension f (g ≫ 𝟙 c)) (P : IsKan t) : IsKan t.ofCompId :=
  .mk (fun s ↦ t.whiskerIdCancel <| P.from (s.whisker (𝟙 c))) <| by
    intro s τ
    ext
    apply P.hom_ext
    simp [← RightExtension.w τ]

/-- If `s ≅ t` and `IsKan (s.whisker h)`, then `IsKan (t.whisker h)`. -/
def whiskerOfCommute (s t : RightExtension f g) (i : s ≅ t) {x : B} (h : c ⟶ x)
    (P : IsKan (s.whisker h)) :
    IsKan (t.whisker h) :=
  P.ofIsoKan <| whiskerIso i h

/-- `RightExtension.ofIso` preserves Kan extensions. -/
noncomputable def ofIso {f' : a ⟶ b} {g' : a ⟶ c} (H : IsKan t) (ef : f ≅ f') (eg : g ≅ g') :
    IsKan (t.ofIso ef eg) :=
  Limits.IsTerminal.isTerminalObj (RightExtension.mapIso ef eg).functor t H

end IsKan

namespace IsAbsKan

variable {s t : RightExtension f g}

/-- The family of 2-morphisms into an absolute right Kan extension. -/
abbrev desc (H : IsAbsKan t) {x : B} {h : c ⟶ x} (s : RightExtension f (g ≫ h)) :
    s.extension ⟶ t.extension ≫ h :=
  (H h).desc s

/-- An absolute right Kan extension is a right Kan extension. -/
def isKan (H : IsAbsKan t) : IsKan t :=
  ((H (𝟙 c)).ofCompId _).ofIsoKan <| whiskerOfCompIdIsoSelf t

/-- Transport evidence that a right extension is a Kan extension across an isomorphism
of extensions. -/
def ofIsoAbsKan (P : IsAbsKan s) (i : s ≅ t) : IsAbsKan t :=
  fun h ↦ (P h).ofIsoKan (whiskerIso i h)

/-- `RightExtension.ofIso` preserves absolute right Kan extensions. -/
noncomputable def ofIso {f' : a ⟶ b} {g' : a ⟶ c} (H : IsAbsKan t) (ef : f ≅ f') (eg : g ≅ g') :
    IsAbsKan (t.ofIso ef eg) :=
  fun h ↦ ((H h).ofIso ef (whiskerRightIso eg h)).ofIsoKan (whiskerOfIso ef eg t h)

end IsAbsKan

section Paste

variable {f : a ⟶ b} {g : a ⟶ c} {h : b ⟶ d}
variable {t : RightExtension f g} {s : RightExtension h t.extension}

/-- Given a right Kan extension `t` of `g` along `f`, a right extension `u` of `g` along `f ≫ h`
induces, via the universal property of `t`, a right extension of `t.extension` along `h`. -/
def IsKan.ofIsKanTop (Ht : IsKan t) (u : RightExtension (f ≫ h) g) : RightExtension h t.extension :=
  .mk u.extension (Ht.desc (.mk (h ≫ u.extension) ((α_ f h u.extension).inv ≫ u.counit)))

@[simp]
theorem IsKan.ofIsKanTop_extension (Ht : IsKan t) (u : RightExtension (f ≫ h) g) :
    (Ht.ofIsKanTop u).extension = u.extension :=
  rfl

theorem IsKan.ofIsKanTop_fac (Ht : IsKan t) (u : RightExtension (f ≫ h) g) :
    f ◁ (Ht.ofIsKanTop u).counit ≫ t.counit = (α_ f h u.extension).inv ≫ u.counit := by
  simpa [IsKan.ofIsKanTop] using
    Ht.fac (.mk (h ≫ u.extension) ((α_ f h u.extension).inv ≫ u.counit))

set_option backward.isDefEq.respectTransparency false in
/-- Pasting of right extensions preserves being Kan. -/
def IsKan.paste (Ht : IsKan t) (Hs : IsKan s) : IsKan (t.paste s) :=
  IsKan.mk
    (fun u ↦
      RightExtension.homMk (Hs.desc (Ht.ofIsKanTop u)) <| by
        rw [paste_counit, ← cancel_epi (α_ f h u.extension).inv, ← Ht.ofIsKanTop_fac,
          ← Hs.fac (Ht.ofIsKanTop u)]
        bicategory)
    (fun u τ ↦ by
      ext
      apply Hs.hom_ext
      apply Ht.hom_ext
      rw [homMk_left, Hs.fac, Ht.ofIsKanTop_fac, ← RightExtension.w τ, paste_counit]
      bicategory)

set_option backward.isDefEq.respectTransparency false in
/-- Given a right extension `t` of `g` along `f` and a right extension `s` of `t` along `h`, if `t`
and `t.paste s` are Kan, then so is `s`. -/
def IsKan.ofPaste (Ht : IsKan t) (Hp : IsKan (t.paste s)) : IsKan s :=
  IsKan.mk
    (fun v ↦
      RightExtension.homMk (Hp.desc (t.paste v)) <| Ht.hom_ext <| by
        rw [← cancel_epi (α_ f h v.extension).hom, ← paste_counit, ← Hp.fac (t.paste v),
          paste_counit]
        bicategory)
    (fun v τ ↦ by
      ext
      apply Hp.hom_ext
      rw [homMk_left, Hp.fac, paste_counit, paste_counit, ← RightExtension.w τ]
      bicategory)

/-- Let `t` be a right Kan extension of `g` along `f` and `s` a right extension of `t` along `h`.
Then `s` is Kan if and only if `t.paste s` is Kan. -/
def isKanEquivIsKanPaste (Ht : IsKan t) : (IsKan s) ≃ (IsKan (t.paste s)) :=
  equivOfSubsingletonOfSubsingleton Ht.paste Ht.ofPaste

/-- Pasting of right extensions preserves being absolute Kan. -/
noncomputable def IsAbsKan.paste (H : IsAbsKan t) (Hs : IsAbsKan s) :
    IsAbsKan (t.paste s) :=
  fun k ↦ ((H k).paste (Hs k)).ofIsoKan (pasteWhiskerIso t s k).symm

/-- Given a right extension `t` of `g` along `f` and a right extension `s` of `t` along `h`, if `t`
and `t.paste s` are absolute Kan, then so is `s`. -/
noncomputable def IsAbsKan.ofPaste (H : IsAbsKan t) (Hp : IsAbsKan (t.paste s)) :
    IsAbsKan s :=
  fun k ↦ (H k).ofPaste ((Hp k).ofIsoKan (pasteWhiskerIso t s k))

/-- Let `t` be an absolute right Kan extension of `g` along `f` and `s` a right extension of `t`
along `h`. Then `s` is absolute Kan if and only if `t.paste s` is absolute Kan. -/
noncomputable def isAbsKanEquivIsAbsKanPaste (H : IsAbsKan t) :
    (IsAbsKan s) ≃ (IsAbsKan (t.paste s)) :=
  equivOfSubsingletonOfSubsingleton H.paste H.ofPaste

end Paste

end RightExtension

namespace RightLift

variable {f : b ⟶ a} {g : c ⟶ a}

/-- A right Kan lift of `g` along `f` is a terminal object in `RightLift f g`. -/
abbrev IsKan (t : RightLift f g) := t.IsUniversal

/-- An absolute right Kan lift is a Kan lift such that every 1-morphism commutes with it. -/
abbrev IsAbsKan (t : RightLift f g) :=
  ∀ {x : B} (h : x ⟶ c), IsKan (t.whisker h)

namespace IsKan

variable {s t : RightLift f g}

/-- To show that a right lift `t` is a Kan lift, we need to show that for every right lift `s`
there is a unique morphism `s ⟶ t`. -/
abbrev mk (desc : ∀ s, s ⟶ t) (w : ∀ s τ, τ = desc s) :
    IsKan t :=
  .ofUniqueHom desc w

/-- The family of 2-morphisms into a right Kan lift. -/
abbrev desc (H : IsKan t) (s : RightLift f g) : s.lift ⟶ t.lift :=
  CostructuredArrow.IsUniversal.lift H s

@[reassoc (attr := simp)]
theorem fac (H : IsKan t) (s : RightLift f g) :
    H.desc s ▷ f ≫ t.counit = s.counit :=
  CostructuredArrow.IsUniversal.fac H s

/-- Two 2-morphisms into a right Kan lift are equal if their compositions with
each triangle 2-morphism are equal. -/
theorem hom_ext (H : IsKan t) {k : c ⟶ b} {τ τ' : k ⟶ t.lift}
    (w : τ ▷ f ≫ t.counit = τ' ▷ f ≫ t.counit) : τ = τ' :=
  CostructuredArrow.IsUniversal.hom_ext H w

/-- Kan lifts on `g` along `f` are unique up to isomorphism. -/
def uniqueUpToIso (P : IsKan s) (Q : IsKan t) : s ≅ t :=
  Limits.IsTerminal.uniqueUpToIso P Q

@[simp]
theorem uniqueUpToIso_hom_left (P : IsKan s) (Q : IsKan t) :
    (uniqueUpToIso P Q).hom.left = Q.desc s := rfl

@[simp]
theorem uniqueUpToIso_inv_left (P : IsKan s) (Q : IsKan t) :
    (uniqueUpToIso P Q).inv.left = P.desc t := rfl

/-- Transport evidence that a right lift is a Kan lift across an isomorphism of lifts. -/
def ofIsoKan (P : IsKan s) (i : s ≅ t) : IsKan t :=
  Limits.IsTerminal.ofIso P i

set_option backward.isDefEq.respectTransparency false in
/-- If `t : RightLift f (𝟙 c ≫ g)` is a Kan lift, then `t.ofIdComp : RightLift f g` is also
a Kan lift. -/
def ofIdComp (t : RightLift f (𝟙 c ≫ g)) (P : IsKan t) : IsKan t.ofIdComp :=
  .mk (fun s ↦ t.whiskerIdCancel <| P.from (s.whisker (𝟙 c))) <| by
    intro s τ
    ext
    apply P.hom_ext
    simp [← RightLift.w τ]

/-- If `s ≅ t` and `IsKan (s.whisker h)`, then `IsKan (t.whisker h)`. -/
def whiskerOfCommute (s t : RightLift f g) (i : s ≅ t) {x : B} (h : x ⟶ c)
    (P : IsKan (s.whisker h)) :
    IsKan (t.whisker h) :=
  P.ofIsoKan <| whiskerIso i h

/-- `RightLift.ofIso` preserves Kan lifts. -/
noncomputable def ofIso {f' : b ⟶ a} {g' : c ⟶ a} (H : IsKan t) (ef : f ≅ f') (eg : g ≅ g') :
    IsKan (t.ofIso ef eg) :=
  Limits.IsTerminal.isTerminalObj (RightLift.mapIso ef eg).functor t H

end IsKan

namespace IsAbsKan

variable {s t : RightLift f g}

/-- The family of 2-morphisms into an absolute right Kan lift. -/
abbrev desc (H : IsAbsKan t) {x : B} {h : x ⟶ c} (s : RightLift f (h ≫ g)) :
    s.lift ⟶ h ≫ t.lift :=
  (H h).desc s

/-- An absolute right Kan lift is a right Kan lift. -/
def isKan (H : IsAbsKan t) : IsKan t :=
  ((H (𝟙 c)).ofIdComp _).ofIsoKan <| whiskerOfIdCompIsoSelf t

/-- Transport evidence that a right lift is a Kan lift across an isomorphism of lifts. -/
def ofIsoAbsKan (P : IsAbsKan s) (i : s ≅ t) : IsAbsKan t :=
  fun h ↦ (P h).ofIsoKan (whiskerIso i h)

/-- `RightLift.ofIso` preserves absolute right Kan lifts. -/
noncomputable def ofIso {f' : b ⟶ a} {g' : c ⟶ a} (H : IsAbsKan t) (ef : f ≅ f') (eg : g ≅ g') :
    IsAbsKan (t.ofIso ef eg) :=
  fun h ↦ ((H h).ofIso ef (whiskerLeftIso h eg)).ofIsoKan (whiskerOfIso ef eg t h)

end IsAbsKan

section Paste

variable {f : b ⟶ a} {g : d ⟶ a} {h : c ⟶ b}
variable {t : RightLift f g} {s : RightLift h t.lift}

/-- Given a right Kan lift `t` of `g` along `f`, a right lift `u` of `g` along `h ≫ f` induces,
via the universal property of `t`, a right lift of `t.lift` along `h`. -/
def IsKan.ofIsKanTop (Ht : IsKan t) (u : RightLift (h ≫ f) g) : RightLift h t.lift :=
  .mk u.lift (Ht.desc (.mk (u.lift ≫ h) ((α_ u.lift h f).hom ≫ u.counit)))

@[simp]
theorem IsKan.ofIsKanTop_lift (Ht : IsKan t) (u : RightLift (h ≫ f) g) :
    (Ht.ofIsKanTop u).lift = u.lift :=
  rfl

theorem IsKan.ofIsKanTop_fac (Ht : IsKan t) (u : RightLift (h ≫ f) g) :
    (Ht.ofIsKanTop u).counit ▷ f ≫ t.counit = (α_ u.lift h f).hom ≫ u.counit := by
  simpa [IsKan.ofIsKanTop] using Ht.fac (.mk (u.lift ≫ h) ((α_ u.lift h f).hom ≫ u.counit))

set_option backward.isDefEq.respectTransparency false in
/-- Pasting of right lifts preserves being Kan. -/
def IsKan.paste (Ht : IsKan t) (Hs : IsKan s) : IsKan (t.paste s) :=
  IsKan.mk
    (fun u ↦
      RightLift.homMk (Hs.desc (Ht.ofIsKanTop u)) <| by
        rw [paste_counit, ← cancel_epi (α_ u.lift h f).hom, ← Ht.ofIsKanTop_fac,
          ← Hs.fac (Ht.ofIsKanTop u)]
        bicategory)
    (fun u τ ↦ by
      ext
      apply Hs.hom_ext
      apply Ht.hom_ext
      rw [homMk_left, Hs.fac, Ht.ofIsKanTop_fac, ← RightLift.w τ, paste_counit]
      bicategory)

set_option backward.isDefEq.respectTransparency false in
/-- Given a right lift `t` of `g` along `f` and a right lift `s` of `t` along `h`, if `t` and
`t.paste s` are Kan, then so is `s`. -/
def IsKan.ofPaste (Ht : IsKan t) (Hp : IsKan (t.paste s)) : IsKan s :=
  IsKan.mk
    (fun v ↦
      RightLift.homMk (Hp.desc (t.paste v)) <| Ht.hom_ext <| by
        rw [← cancel_epi (α_ v.lift h f).inv, ← paste_counit, ← Hp.fac (t.paste v), paste_counit]
        bicategory)
    (fun v τ ↦ by
      ext
      apply Hp.hom_ext
      rw [homMk_left, Hp.fac, paste_counit, paste_counit, ← RightLift.w τ]
      bicategory)

/-- Let `t` be a right Kan lift of `g` along `f` and `s` a right lift of `t` along `h`. Then `s` is
Kan if and only if `t.paste s` is Kan. -/
def isKanEquivIsKanPaste (Ht : IsKan t) : (IsKan s) ≃ (IsKan (t.paste s)) :=
  equivOfSubsingletonOfSubsingleton Ht.paste Ht.ofPaste

/-- Pasting of right lifts preserves being absolute Kan. -/
noncomputable def IsAbsKan.paste (H : IsAbsKan t) (Hs : IsAbsKan s) :
    IsAbsKan (t.paste s) :=
  fun k ↦ ((H k).paste (Hs k)).ofIsoKan (pasteWhiskerIso t s k).symm

/-- Given a right lift `t` of `g` along `f` and a right lift `s` of `t` along `h`, if `t` and
`t.paste s` are absolute Kan, then so is `s`. -/
noncomputable def IsAbsKan.ofPaste (H : IsAbsKan t) (Hp : IsAbsKan (t.paste s)) :
    IsAbsKan s :=
  fun k ↦ (H k).ofPaste ((Hp k).ofIsoKan (pasteWhiskerIso t s k))

/-- Let `t` be an absolute right Kan lift of `g` along `f` and `s` a right lift of `t` along `h`.
Then `s` is absolute Kan if and only if `t.paste s` is absolute Kan. -/
noncomputable def isAbsKanEquivIsAbsKanPaste (H : IsAbsKan t) :
    (IsAbsKan s) ≃ (IsAbsKan (t.paste s)) :=
  equivOfSubsingletonOfSubsingleton H.paste H.ofPaste

end Paste

end RightLift

end Bicategory

end CategoryTheory
