/-
Copyright (c) 2024 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import Mathlib.CategoryTheory.Bicategory.Kan.IsKan

/-!
# Existence of Kan extensions and Kan lifts in bicategories

We provide the propositional typeclass `HasLeftKanExtension f g`, which asserts that there
exists a left Kan extension of `g` along `f`. Under the assumption that `HasLeftKanExtension f g`,
we define the left Kan extension `lan f g` by using the axiom of choice.

## Main definitions

* `lan f g` is the left Kan extension of `g` along `f`, and is denoted by `f ⁺ g`.
* `lanLift f g` is the left Kan lift of `g` along `f`, and is denoted by `f ₊ g`.

-/

noncomputable section

namespace CategoryTheory

namespace Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B] {a b c : B}

section LeftKan

open LeftExtension

variable {f : a ⟶ b} {g : a ⟶ c}

/-- Left Kan extensions of `g` along `f`. -/
structure LeftKanExtension (f : a ⟶ b) (g : a ⟶ c) where
  /-- The underlying left extension. -/
  extension : LeftExtension f g
  /-- The proof that the extension is a Kan extension. -/
  isKan : extension.IsKan

/-- The existence of a left Kan extension of `g` along `f`. -/
class HasLeftKanExtension (f : a ⟶ b) (g : a ⟶ c) : Prop where mk' ::
  exists_leftKan : Nonempty (LeftKanExtension f g)

theorem HasLeftKanExtension.mk {t : LeftExtension f g} (H : IsKan t) : HasLeftKanExtension f g :=
  ⟨⟨t, H⟩⟩

/-- Use the axiom of choice to extract the explicit left kan extension. -/
def getLeftKanExtension (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g] : LeftKanExtension f g :=
  Classical.choice HasLeftKanExtension.exists_leftKan

/-- The left Kan extension of `g` along `f`. -/
def lan.extension (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g] : LeftExtension f g :=
  (getLeftKanExtension f g).extension

/-- The left Kan extension of `g` along `f`, denoted by `f ⁺ g`.
```
  b
  △ \
  |   \ f ⁺ g
f |     \
  |       ◿
  a - - - ▷ c
      g
```
-/
def lan (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g] : b ⟶ c :=
  (lan.extension f g).extension

@[inherit_doc] scoped infixr:90 " ⁺ " => lan

/-- The unit for the left kan extension `f ⁺ g`. -/
def lan.unit (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g] : g ⟶ f ≫ f ⁺ g :=
  (lan.extension f g).unit

/-- Evidence that the `lan.extension f g` is a kan extension. -/
def lan.isLeftKan (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g] : (lan.extension f g).IsKan :=
  (getLeftKanExtension f g).isKan

variable {f : a ⟶ b} {g : a ⟶ c}

/-- The family of 2-morphisms out of the left Kan extension `f ⁺ g`. -/
def lan.desc [HasLeftKanExtension f g] (s : LeftExtension f g) :
    f ⁺ g ⟶ s.extension :=
  (lan.isLeftKan f g).desc s

@[reassoc (attr := simp)]
theorem lan.lan₂_desc [HasLeftKanExtension f g] (s : LeftExtension f g) :
    lan.unit f g ≫ f ◁ lan.desc s = s.unit :=
  (lan.isLeftKan f g).fac s

@[simp]
theorem lan.isLeftKan_desc [HasLeftKanExtension f g] (s : LeftExtension f g) :
    (lan.isLeftKan f g).desc s = lan.desc s :=
  rfl

theorem lan.existsUnique [HasLeftKanExtension f g] (s : LeftExtension f g) :
    ∃! τ, lan.unit f g ≫ f ◁ τ = s.unit :=
  (lan.isLeftKan f g).existsUnique _

/-- Absolute left Kan extensions of `g` along `f`. -/
structure AbsLeftKan (f : a ⟶ b) (g : a ⟶ c) where
  /-- The underlying left extension. -/
  extension : LeftExtension f g
  /-- The proof that the extension is an absolute Kan extension. -/
  isAbsKan : extension.IsAbsKan

/-- The existence of an absolute left Kan extension of `g` along `f`. -/
class HasAbsLeftKan (f : a ⟶ b) (g : a ⟶ c) : Prop where mk' ::
  exists_absLeftKan : Nonempty (AbsLeftKan f g)

theorem HasAbsLeftKan.mk {t : LeftExtension f g} (H : IsAbsKan t) : HasAbsLeftKan f g := ⟨⟨t, H⟩⟩

/-- Use the axiom of choice to extract the explicit absolute left kan extension. -/
def absLan.getAbsLeftKanExtension (f : a ⟶ b) (g : a ⟶ c) [HasAbsLeftKan f g] : AbsLeftKan f g :=
  Classical.choice HasAbsLeftKan.exists_absLeftKan

instance [HasAbsLeftKan f g] {x : B} (h : c ⟶ x) : HasLeftKanExtension f (g ≫ h) :=
  .mk <| (absLan.getAbsLeftKanExtension f g).isAbsKan h

instance [HasAbsLeftKan f g] : HasLeftKanExtension f g :=
  .mk (lan.isLeftKan f (g ≫ 𝟙 c)).ofAlongCompId

/-- If there exists an absolute Kan extension of `g` along `f`, we have the evidence that the
distinguished kan extension `lan.extension f g` is an absolute Kan extension. -/
def lan.isAbsLeftKan (f : a ⟶ b) (g : a ⟶ c) [HasAbsLeftKan f g] : (lan.extension f g).IsAbsKan :=
  let ⟨_, H⟩ := absLan.getAbsLeftKanExtension f g
  H.ofIsoAbsKan <| IsKan.uniqueUpToIso H.isKan (lan.isLeftKan f g)

/-- `h : c ⟶ x` commutes with the left Kan extension of `g : a ⟶ c` along `f : a ⟶ b`. -/
class CommuteWithLeftKan
    (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g] {x : B} (h : c ⟶ x) : Prop where
  commute : Nonempty <| IsKan <| (lan.extension f g).whisker h

instance {x : B} {h : c ⟶ x} [HasLeftKanExtension f g] [CommuteWithLeftKan f g h] :
    HasLeftKanExtension f (g ≫ h) :=
  .mk (Classical.choice <| CommuteWithLeftKan.commute)

end LeftKan

section LeftLift

open LeftLift

variable {f : b ⟶ a} {g : c ⟶ a}

/-- Left lifts of `g` along `f`. -/
structure LeftKanLift (f : b ⟶ a) (g : c ⟶ a) where
  /-- The underlying left lift. -/
  lift : LeftLift f g
  /-- The proof that the left lift is a Kan lift. -/
  isKan : lift.IsKan

/-- The existence of a left kan lift of `g` along `f`. -/
class HasLeftKanLift (f : b ⟶ a) (g : c ⟶ a) : Prop where mk' ::
  exists_leftKanLift : Nonempty (LeftKanLift f g)

theorem HasLeftKanLift.mk {t : LeftLift f g} (H : IsKan t) : HasLeftKanLift f g := ⟨⟨t, H⟩⟩

/-- Use the axiom of choice to extract the explicit left kan lift. -/
def getLeftKanLift (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g] : LeftKanLift f g :=
  Classical.choice HasLeftKanLift.exists_leftKanLift

/-- The left kan lift of `g` along `f`. -/
def lanLift.lift (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g] : LeftLift f g :=
  (getLeftKanLift f g).lift

/-- The left kan lift of `g` along `f`, denoted by `f ₊ g`.
```
            b
          ◹ |
  f ₊ g /   |
      /     | f
    /       ▽
  c - - - ▷ a
       g
```
-/
def lanLift (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g] : c ⟶ b :=
  (lanLift.lift f g).lift

@[inherit_doc] scoped infixr:90 " ₊ " => lanLift

/-- The unit for `lanLift f g`. -/
def lanLift.unit (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g] : g ⟶ f ₊ g ≫ f :=
  (lanLift.lift f g).unit

/-- Evidence that the `lanLift.lift f g` is a kan lift. -/
def lanLift.isLeftKan (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g] : (lanLift.lift f g).IsKan :=
  (getLeftKanLift f g).isKan

variable {f : b ⟶ a} {g : c ⟶ a}

/-- The family of 2-morphisms out of the left kan lift `f ₊ g`. -/
def lanLift.desc [HasLeftKanLift f g] (s : LeftLift f g) :
    f ₊ g ⟶ s.lift :=
  (lanLift.isLeftKan f g).desc s

@[reassoc (attr := simp)]
theorem lanLift.unit_desc [HasLeftKanLift f g] (s : LeftLift f g) :
    lanLift.unit f g ≫ lanLift.desc s ▷ f = s.unit :=
  (lanLift.isLeftKan f g).fac s

@[simp]
theorem lanLift.isLeftKan_desc [HasLeftKanLift f g] (s : LeftLift f g) :
    (lanLift.isLeftKan f g).desc s = lanLift.desc s :=
  rfl

theorem lanLift.existsUnique [HasLeftKanLift f g] (s : LeftLift f g) :
    ∃! τ, lanLift.unit f g ≫ τ ▷ f = s.unit :=
  (lanLift.isLeftKan f g).existsUnique _

/-- Absolute left lifts of `g` along `f`. -/
structure AbsLeftKanLift (f : b ⟶ a) (g : c ⟶ a) where
  /-- The underlying left lift. -/
  lift : LeftLift f g
  /-- The proof that the left lift is an absolute Kan lift. -/
  isAbsKan : lift.IsAbsKan

/-- The existence of an absolute left Kan lift of `g` along `f`. -/
class HasAbsLeftKanLift (f : b ⟶ a) (g : c ⟶ a) : Prop where mk' ::
  exists_absLeftKanLift : Nonempty (AbsLeftKanLift f g)

theorem HasAbsLeftKanLift.mk {t : LeftLift f g} (H : IsAbsKan t) : HasAbsLeftKanLift f g :=
  ⟨⟨t, H⟩⟩

/-- Use the axiom of choice to extract the explicit absolute left kan lift. -/
def absLanLift.getAbsLeftKanLift (f : b ⟶ a) (g : c ⟶ a) [HasAbsLeftKanLift f g] :
    AbsLeftKanLift f g :=
  Classical.choice HasAbsLeftKanLift.exists_absLeftKanLift

instance [HasAbsLeftKanLift f g] {x : B} (h : x ⟶ c) : HasLeftKanLift f (h ≫ g) :=
  .mk <| (absLanLift.getAbsLeftKanLift f g).isAbsKan h

instance [HasAbsLeftKanLift f g] : HasLeftKanLift f g :=
  .mk (lanLift.isLeftKan f (𝟙 c ≫ g)).ofAlongIdComp

/-- If there exists an absolute Kan lift of `g` along `f`, we have the evidence that the
distinguished kan lift `lanLift.lift f g` is an absolute Kan lift. -/
def lanLift.isAbsLeftKan (f : b ⟶ a) (g : c ⟶ a) [HasAbsLeftKanLift f g] :
    (lanLift.lift f g).IsAbsKan :=
  let ⟨_, H⟩ := absLanLift.getAbsLeftKanLift f g
  fun h ↦ (H h).ofIso (whiskerIso (IsKan.uniqueUpToIso (H.isKan) (lanLift.isLeftKan f g)) h)

/-- `h : x ⟶ b` commutes with the left kan lift of `g : c ⟶ a` along `f : b ⟶ a`. -/
class CommuteWithLeftKanLift
    (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g] {x : B} (h : x ⟶ c) : Prop where
  commute : Nonempty <| IsKan <| (lanLift.lift f g).whisker h

instance {x : B} {h : x ⟶ c} [HasLeftKanLift f g] [CommuteWithLeftKanLift f g h] :
    HasLeftKanLift f (h ≫ g) :=
  .mk (Classical.choice <| CommuteWithLeftKanLift.commute)

end LeftLift

end Bicategory

end CategoryTheory
