/-
Copyright (c) 2024 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import Mathlib.CategoryTheory.Bicategory.Kan.IsKan

/-!
# Existence of Kan extensions and Kan lifts in bicategories

We provide the propositional typeclass `HasLeftKanExtension f g`, which asserts that there
exists a left Kan extension of `g` along `f`. See `CategoryTheory.Bicategory.Kan.IsKan` for
the definition of left Kan extensions. Under the assumption that `HasLeftKanExtension f g`,
we define the left Kan extension `lan f g` by using the axiom of choice.

## Main definitions

* `lan f g` is the left Kan extension of `g` along `f`, and is denoted by `f⁺ g`.
* `lanLift f g` is the left Kan lift of `g` along `f`, and is denoted by `f₊ g`.

## TODO

* `ran f g` is the right Kan extension of `g` along `f`, and is denoted by `f⁺⁺ g`.
* `ranLift f g` is the right Kan lift of `g` along `f`, and is denoted by `f₊₊ g`.

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
  leftExtension : LeftExtension f g
  /-- The evidence that the extension is a Kan extension. -/
  isKan : leftExtension.IsKan

/-- The existence of a left Kan extension of `g` along `f`. -/
class HasLeftKanExtension (f : a ⟶ b) (g : a ⟶ c) : Prop where mk' ::
  exists_leftKan : Nonempty (LeftKanExtension f g)

theorem HasLeftKanExtension.mk {t : LeftExtension f g} (H : IsKan t) : HasLeftKanExtension f g :=
  ⟨⟨t, H⟩⟩

/-- Use the axiom of choice to extract a left Kan extension. -/
def getLeftKanExtension (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g] : LeftKanExtension f g :=
  Classical.choice HasLeftKanExtension.exists_leftKan

/-- The left Kan extension of `g` along `f` at the level of structured arrows. -/
def Lan.leftExtension (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g] : LeftExtension f g :=
  (getLeftKanExtension f g).leftExtension

/-- The left Kan extension of `g` along `f`. -/
def lan (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g] : b ⟶ c :=
  (Lan.leftExtension f g).extension

/-- `f⁺ g` is the left Kan extension of `g` along `f`.
```
  b
  △ \
  |   \ f⁺ g
f |     \
  |       ◿
  a - - - ▷ c
      g
```
-/
scoped infixr:90 "⁺ " => lan

@[simp]
theorem Lan.leftExtension_extension (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g] :
    (Lan.leftExtension f g).extension = f⁺ g := rfl

/-- The unit for the left Kan extension `f⁺ g`. -/
def Lan.unit (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g] : g ⟶ f ≫ f⁺ g :=
  (Lan.leftExtension f g).unit

@[simp]
theorem Lan.leftExtension_unit (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g] :
    (Lan.leftExtension f g).unit = Lan.unit f g := rfl

/-- Evidence that the `Lan.extension f g` is a Kan extension. -/
def Lan.isKan (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g] : (Lan.leftExtension f g).IsKan :=
  (getLeftKanExtension f g).isKan

variable {f : a ⟶ b} {g : a ⟶ c}

/-- The family of 2-morphisms out of the left Kan extension `f⁺ g`. -/
def Lan.desc [HasLeftKanExtension f g] (s : LeftExtension f g) :
    f⁺ g ⟶ s.extension :=
  (Lan.isKan f g).desc s

@[reassoc (attr := simp)]
theorem Lan.unit_desc [HasLeftKanExtension f g] (s : LeftExtension f g) :
    Lan.unit f g ≫ f ◁ Lan.desc s = s.unit :=
  (Lan.isKan f g).fac s

@[simp]
theorem Lan.isKan_desc [HasLeftKanExtension f g] (s : LeftExtension f g) :
    (Lan.isKan f g).desc s = Lan.desc s :=
  rfl

theorem Lan.existsUnique [HasLeftKanExtension f g] (s : LeftExtension f g) :
    ∃! τ, Lan.unit f g ≫ f ◁ τ = s.unit :=
  (Lan.isKan f g).existsUnique _

/-- We say that a 1-morphism `h` commutes with the left Kan extension `f⁺ g` if the whiskered
left extension for `f⁺ g` by `h` is a Kan extension of `g ≫ h` along `f`. -/
class Lan.CommuteWith
    (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g] {x : B} (h : c ⟶ x) : Prop where
  commute : Nonempty <| IsKan <| (Lan.leftExtension f g).whisker h

namespace Lan.CommuteWith

theorem ofLanCompIsoLanAlongComp [HasLeftKanExtension f g]
    {x : B} {h : c ⟶ x} [HasLeftKanExtension f (g ≫ h)]
    (i : f⁺ (g ≫ h) ≅ f⁺ g ≫ h)
    (w : Lan.unit f (g ≫ h) ≫ f ◁ i.hom = Lan.unit f g ▷ h ≫ (α_ _ _ _).hom) :
    Lan.CommuteWith f g h :=
  ⟨⟨(Lan.isKan f (g ≫ h)).ofIsoKan <| StructuredArrow.isoMk i⟩⟩

variable (f : a ⟶ b) (g : a ⟶ c) [HasLeftKanExtension f g]
variable {x : B} (h : c ⟶ x) [Lan.CommuteWith f g h]

/-- Evidence that `h` commutes with the left Kan extension `f⁺ g`. -/
def isKan : IsKan <| (Lan.leftExtension f g).whisker h := Classical.choice Lan.CommuteWith.commute

instance : HasLeftKanExtension f (g ≫ h) := .mk <| Lan.CommuteWith.isKan f g h

/-- The isomorphism `f⁺ (g ≫ h) ≅ f⁺ g ≫ h` at the level of structured arrows. -/
def lanAlongCompIsoLanwhisker : Lan.leftExtension f (g ≫ h) ≅ (Lan.leftExtension f g).whisker h :=
  IsKan.uniqueUpToIso (Lan.isKan f (g ≫ h)) (Lan.CommuteWith.isKan f g h)

@[simp]
theorem lanAlongCompIsoLanwhisker_hom_right :
    (lanAlongCompIsoLanwhisker f g h).hom.right = Lan.desc ((Lan.leftExtension f g).whisker h) :=
  rfl

@[simp]
theorem lanAlongCompIsoLanwhisker_inv_right :
    (lanAlongCompIsoLanwhisker f g h).inv.right =
      (isKan f g h).desc (Lan.leftExtension f (g ≫ h)) :=
  rfl

/-- The 1-morphism `h` commutes with the left Kan extension `f⁺ g`. -/
@[simps!]
def lanAlongCompIsoLanComp : f⁺ (g ≫ h) ≅ f⁺ g ≫ h :=
    Comma.rightIso <| Lan.CommuteWith.lanAlongCompIsoLanwhisker f g h

end Lan.CommuteWith

/-- We say that there exists an absolute left Kan extension of `g` along `f` if any 1-morphism `h`
commutes with the left Kan extension `f⁺ g`. -/
class HasAbsLeftKanExtension (f : a ⟶ b) (g : a ⟶ c) extends HasLeftKanExtension f g : Prop where
  commute : ∀ {x : B} (h : c ⟶ x), Lan.CommuteWith f g h

instance [HasAbsLeftKanExtension f g] {x : B} (h : c ⟶ x) : Lan.CommuteWith f g h :=
  HasAbsLeftKanExtension.commute h

theorem HasAbsLeftKanExtension.ofIsAbsKan {t : LeftExtension f g} (H : IsAbsKan t) :
    HasAbsLeftKanExtension f g :=
  have : HasLeftKanExtension f g := .mk H.isKan
  ⟨fun h ↦ ⟨⟨H.ofIsoAbsKan (IsKan.uniqueUpToIso H.isKan (Lan.isKan f g)) h⟩⟩⟩

end LeftKan

section LeftLift

open LeftLift

variable {f : b ⟶ a} {g : c ⟶ a}

/-- Left lifts of `g` along `f`. -/
structure LeftKanLift (f : b ⟶ a) (g : c ⟶ a) where
  /-- The underlying left lift. -/
  leftLift : LeftLift f g
  /-- The evidence that the left lift is a Kan lift. -/
  isKan : leftLift.IsKan

/-- The existence of a left kan lift of `g` along `f`. -/
class HasLeftKanLift (f : b ⟶ a) (g : c ⟶ a) : Prop where mk' ::
  exists_leftKanLift : Nonempty (LeftKanLift f g)

theorem HasLeftKanLift.mk {t : LeftLift f g} (H : IsKan t) : HasLeftKanLift f g := ⟨⟨t, H⟩⟩

/-- Use the axiom of choice to extract a left Kan lift. -/
def getLeftKanLift (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g] : LeftKanLift f g :=
  Classical.choice HasLeftKanLift.exists_leftKanLift

/-- The left Kan lift of `g` along `f` at the level of structured arrows. -/
def LanLift.leftLift (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g] : LeftLift f g :=
  (getLeftKanLift f g).leftLift

/-- The left Kan lift of `g` along `f`. -/
def lanLift (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g] : c ⟶ b :=
  (LanLift.leftLift f g).lift

/-- `f₊ g` is the left Kan lift of `g` along `f`.
```
            b
          ◹ |
   f₊ g /   |
      /     | f
    /       ▽
  c - - - ▷ a
       g
```
-/
scoped infixr:90 "₊ " => lanLift

@[simp]
theorem LanLift.leftLift_lift (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g] :
    (LanLift.leftLift f g).lift = f₊ g := rfl

/-- The unit for the left Kan lift `f₊ g`. -/
def LanLift.unit (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g] : g ⟶ f₊ g ≫ f :=
  (LanLift.leftLift f g).unit

@[simp]
theorem LanLift.leftLift_unit (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g] :
    (LanLift.leftLift f g).unit = LanLift.unit f g := rfl

/-- Evidence that the `LanLift.lift f g` is a Kan lift. -/
def LanLift.isKan (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g] : (LanLift.leftLift f g).IsKan :=
  (getLeftKanLift f g).isKan

variable {f : b ⟶ a} {g : c ⟶ a}

/-- The family of 2-morphisms out of the left Kan lift `f₊ g`. -/
def LanLift.desc [HasLeftKanLift f g] (s : LeftLift f g) :
    f ₊ g ⟶ s.lift :=
  (LanLift.isKan f g).desc s

@[reassoc (attr := simp)]
theorem LanLift.unit_desc [HasLeftKanLift f g] (s : LeftLift f g) :
    LanLift.unit f g ≫ LanLift.desc s ▷ f = s.unit :=
  (LanLift.isKan f g).fac s

@[simp]
theorem LanLift.isKan_desc [HasLeftKanLift f g] (s : LeftLift f g) :
    (LanLift.isKan f g).desc s = LanLift.desc s :=
  rfl

theorem LanLift.existsUnique [HasLeftKanLift f g] (s : LeftLift f g) :
    ∃! τ, LanLift.unit f g ≫ τ ▷ f = s.unit :=
  (LanLift.isKan f g).existsUnique _

/-- We say that a 1-morphism `h` commutes with the left Kan lift `f₊ g` if the whiskered left lift
for `f₊ g` by `h` is a Kan lift of `h ≫ g` along `f`. -/
class LanLift.CommuteWith
    (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g] {x : B} (h : x ⟶ c) : Prop where
  commute : Nonempty <| IsKan <| (LanLift.leftLift f g).whisker h

namespace LanLift.CommuteWith

theorem ofLanCompIsoLanAlongComp [HasLeftKanLift f g]
    {x : B} {h : x ⟶ c} [HasLeftKanLift f (h ≫ g)]
    (i : f₊ (h ≫ g) ≅ h ≫ f₊ g)
    (w : LanLift.unit f (h ≫ g) ≫ i.hom ▷ f = h ◁ LanLift.unit f g ≫ (α_ _ _ _).inv) :
    LanLift.CommuteWith f g h :=
  ⟨⟨(LanLift.isKan f (h ≫ g)).ofIsoKan <| StructuredArrow.isoMk i⟩⟩

variable (f : b ⟶ a) (g : c ⟶ a) [HasLeftKanLift f g]
variable {x : B} (h : x ⟶ c) [LanLift.CommuteWith f g h]

/-- Evidence that `h` commutes with the left Kan lift `f₊ g`. -/
def isKan : IsKan <| (LanLift.leftLift f g).whisker h :=
    Classical.choice LanLift.CommuteWith.commute

instance : HasLeftKanLift f (h ≫ g) := .mk <| LanLift.CommuteWith.isKan f g h

/-- The isomorphism `f₊ (h ≫ g) ≅ h ≫ f₊ g` at the level of structured arrows. -/
def lanLiftAlongCompIsoLanLiftWhisker :
    LanLift.leftLift f (h ≫ g) ≅ (LanLift.leftLift f g).whisker h :=
  IsKan.uniqueUpToIso (LanLift.isKan f (h ≫ g)) (LanLift.CommuteWith.isKan f g h)

@[simp]
theorem lanLiftAlongCompIsoLanLiftWhisker_hom_right :
    (lanLiftAlongCompIsoLanLiftWhisker f g h).hom.right =
      LanLift.desc ((LanLift.leftLift f g).whisker h) :=
  rfl

@[simp]
theorem lanLiftAlongCompIsoLanLiftWhisker_inv_right :
    (lanLiftAlongCompIsoLanLiftWhisker f g h).inv.right =
      (isKan f g h).desc (LanLift.leftLift f (h ≫ g)) :=
  rfl

/-- The 1-morphism `h` commutes with the left Kan lift `f₊ g`. -/
@[simps!]
def lanLiftAlongCompIsoCompLan : f₊ (h ≫ g) ≅ h ≫ f₊ g :=
    Comma.rightIso <| LanLift.CommuteWith.lanLiftAlongCompIsoLanLiftWhisker f g h

end LanLift.CommuteWith

/-- We say that there exists an absolute left Kan lift of `g` along `f` if any 1-morphism `h`
commutes with the left Kan lift `f₊ g`. -/
class HasAbsLeftKanLift (f : b ⟶ a) (g : c ⟶ a) extends HasLeftKanLift f g : Prop where
  commute : ∀ {x : B} (h : x ⟶ c), LanLift.CommuteWith f g h

instance [HasAbsLeftKanLift f g] {x : B} (h : x ⟶ c) : LanLift.CommuteWith f g h :=
  HasAbsLeftKanLift.commute h

theorem HasAbsLeftKanLift.ofIsAbsKan {t : LeftLift f g} (H : IsAbsKan t) : HasAbsLeftKanLift f g :=
  have : HasLeftKanLift f g := .mk H.isKan
  ⟨fun h ↦ ⟨⟨H.ofIsoAbsKan (IsKan.uniqueUpToIso H.isKan (LanLift.isKan f g)) h⟩⟩⟩

end LeftLift

end Bicategory

end CategoryTheory
