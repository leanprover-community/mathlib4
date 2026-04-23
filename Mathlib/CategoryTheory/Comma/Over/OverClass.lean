/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Init
import Mathlib.Tactic.CategoryTheory.Reassoc
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Util.CompileInductive

/-!
# Typeclasses for `S`-objects and `S`-morphisms

**Warning**: This is not usually how typeclasses should be used.
This is only a sensible approach when the morphism is considered as a structure on `X`,
typically in algebraic geometry.

This is analogous to how we view ringhoms as structures via the `Algebra` typeclass.

For other applications use unbundled arrows or `CategoryTheory.Over`.

## Main definition
- `CategoryTheory.OverClass`: `OverClass X S` equips `X` with a morphism into `S`.
  `X ↘ S : X ⟶ S` is the structure morphism.
- `CategoryTheory.HomIsOver`:
  `HomIsOver f S` asserts that `f` commutes with the structure morphisms.

-/

@[expose] public section

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

variable {X Y Z : C} (f : X ⟶ Y) (S S' : C)

/--
`OverClass X S` is the typeclass containing the data of a structure morphism `X ↘ S : X ⟶ S`.
-/
class OverClass (X S : C) : Type v where
  ofHom ::
  /-- The structure morphism. Use `X ↘ S` instead. -/
  hom : X ⟶ S

/--
The structure morphism `X ↘ S : X ⟶ S` given `OverClass X S`.
The instance argument is an `optParam` instead so that it appears in the discrimination tree.
-/
def over (X S : C) (_ : OverClass X S := by infer_instance) : X ⟶ S := OverClass.hom

/-- The structure morphism `X ↘ S : X ⟶ S` given `OverClass X S`. -/
notation:90 X:90 " ↘ " S:90 => CategoryTheory.over X S inferInstance

/-- See Note [custom simps projection] -/
def OverClass.Simps.over (X S : C) [OverClass X S] : X ⟶ S := X ↘ S

initialize_simps_projections OverClass (hom → over)

/--
`X.CanonicallyOverClass S` is the typeclass containing the data of a
structure morphism `X ↘ S : X ⟶ S`,
and that `S` is (uniquely) inferable from the structure of `X`.
-/
class CanonicallyOverClass (X : C) (S : semiOutParam C) extends OverClass X S where

/-- See Note [custom simps projection] -/
def CanonicallyOverClass.Simps.over (X S : C) [CanonicallyOverClass X S] : X ⟶ S := X ↘ S

initialize_simps_projections CanonicallyOverClass (hom → over)

@[simps]
instance : OverClass X X := ⟨𝟙 _⟩

instance : IsIso (S ↘ S) := inferInstanceAs (IsIso (𝟙 S))

namespace CanonicallyOverClass
-- This cannot be a simp lemma because it loops with `comp_over`.
@[simps -isSimp]
instance (priority := 900) [CanonicallyOverClass X Y] [OverClass Y S] : OverClass X S :=
  ⟨X ↘ Y ≫ Y ↘ S⟩
end CanonicallyOverClass

/-- Given `OverClass X S` and `OverClass Y S` and `f : X ⟶ Y`,
`HomIsOver f S` is the typeclass asserting `f` commutes with the structure morphisms. -/
class HomIsOver (f : X ⟶ Y) (S : C) [OverClass X S] [OverClass Y S] : Prop where
  comp_over : f ≫ Y ↘ S = X ↘ S := by aesop

@[reassoc (attr := simp)]
lemma comp_over [OverClass X S] [OverClass Y S] [HomIsOver f S] :
    f ≫ Y ↘ S = X ↘ S :=
  HomIsOver.comp_over

instance [OverClass X S] : HomIsOver (𝟙 X) S where

instance [OverClass X S] [OverClass Y S] [OverClass Z S]
    (f : X ⟶ Y) (g : Y ⟶ Z) [HomIsOver f S] [HomIsOver g S] :
    HomIsOver (f ≫ g) S where

/-- `IsOverTower X Y S` is the typeclass asserting that the structure morphisms
`X ↘ Y`, `Y ↘ S`, and `X ↘ S` commute. -/
abbrev IsOverTower (X Y S : C) [OverClass X S] [OverClass Y S] [OverClass X Y] :=
  HomIsOver (X ↘ Y) S

instance [OverClass X S] : IsOverTower X X S where
instance [OverClass X S] : IsOverTower X S S where

instance [CanonicallyOverClass X Y] [OverClass Y S] : IsOverTower X Y S :=
  ⟨rfl⟩

lemma homIsOver_of_isOverTower [OverClass X S] [OverClass X S'] [OverClass Y S]
    [OverClass Y S'] [OverClass S S']
    [IsOverTower X S S'] [IsOverTower Y S S'] [HomIsOver f S] : HomIsOver f S' := by
  constructor
  rw [← comp_over (Y ↘ S), comp_over_assoc f, comp_over]

instance [CanonicallyOverClass X S]
    [OverClass X S'] [OverClass Y S] [OverClass Y S'] [OverClass S S']
    [IsOverTower X S S'] [IsOverTower Y S S'] [HomIsOver f S] : HomIsOver f S' :=
  homIsOver_of_isOverTower f S S'

instance [OverClass X S]
    [OverClass X S'] [CanonicallyOverClass Y S] [OverClass Y S'] [OverClass S S']
    [IsOverTower X S S'] [IsOverTower Y S S'] [HomIsOver f S] : HomIsOver f S' :=
  homIsOver_of_isOverTower f S S'

variable (X) in
/-- Bundle `X` with an `OverClass X S` instance into `Over S`. -/
@[simps! hom left]
def OverClass.asOver [OverClass X S] : Over S := Over.mk (X ↘ S)

/-- Bundle a morphism `f : X ⟶ Y` with `HomIsOver f S` into a morphism in `Over S`. -/
@[simps! left]
def OverClass.asOverHom [OverClass X S] [OverClass Y S] (f : X ⟶ Y) [HomIsOver f S] :
    OverClass.asOver X S ⟶ OverClass.asOver Y S :=
  Over.homMk f (comp_over f S)

@[simps]
instance OverClass.fromOver {S : C} (X : Over S) : OverClass X.left S where
  hom := X.hom

instance {S : C} {X Y : Over S} (f : X ⟶ Y) : HomIsOver f.left S where
  comp_over := Over.w f

variable [OverClass X S] [OverClass Y S] [OverClass Z S]

namespace OverClass

instance (f : X ⟶ Y) [IsIso f] [HomIsOver f S] : IsIso (asOverHom S f) :=
  have : IsIso ((Over.forget S).map (asOverHom S f)) := ‹_›
  isIso_of_reflects_iso _ (Over.forget _)

attribute [local simp] Iso.inv_comp_eq in
instance {e : X ≅ Y} [HomIsOver e.hom S] : HomIsOver e.inv S where

set_option linter.style.whitespace false in -- linter false positive
attribute [local simp ←] Iso.eq_inv_comp in
instance {e : X ≅ Y} [HomIsOver e.inv S] : HomIsOver e.hom S where

instance {f : X ⟶ Y} [IsIso f] [HomIsOver f S] : HomIsOver (asIso f).hom S where
instance {f : X ⟶ Y} [IsIso f] [HomIsOver f S] : HomIsOver (asIso f).inv S where
instance {f : X ⟶ Y} [IsIso f] [HomIsOver f S] : HomIsOver (inv f) S where

@[simp] lemma asOverHom_id : asOverHom S (𝟙 X) = 𝟙 (asOver X S) := rfl

@[simp, reassoc] lemma asOverHom_comp (f : X ⟶ Y) (g : Y ⟶ Z) [HomIsOver f S] [HomIsOver g S] :
    asOverHom S (f ≫ g) = asOverHom S f ≫ asOverHom S g := rfl

@[simp] lemma asOverHom_inv (f : X ⟶ Y) [IsIso f] [HomIsOver f S] :
    asOverHom S (inv f) = inv (asOverHom S f) := by simp [← hom_comp_eq_id, ← asOverHom_comp]

end OverClass

/-- Reinterpret an isomorphism over an object `S` into an isomorphism in the category over `S`. -/
@[simps]
def Iso.asOver (e : X ≅ Y) [HomIsOver e.hom S] : OverClass.asOver X S ≅ OverClass.asOver Y S where
  hom := OverClass.asOverHom S e.hom
  inv := OverClass.asOverHom S e.inv

end CategoryTheory
