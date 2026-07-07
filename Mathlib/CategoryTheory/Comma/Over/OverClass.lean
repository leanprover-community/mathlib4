/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Tactic.CategoryTheory.Reassoc
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Typeclasses for `S`-objects and `S`-morphisms

**Warning**: This is not usually how typeclasses should be used.
This is only a sensible approach when the morphism is considered as a structure on `X`,
typically in algebraic geometry.

This is analogous to how we view ringhoms as structures via the `Algebra` typeclass.

For other applications use unbundled arrows or `CategoryTheory.Over`.

## Main definition
- `CategoryTheory.OverClass`: `OverClass X S f` asserts that `f : X ⟶ S` is the structure
  morphism of `X` over `S`. Since `f` is an `outParam`, the notation `X ↘ S` elaborates to
  the structure morphism `f` itself.
- `CategoryTheory.HomIsOver`:
  `HomIsOver f S` asserts that `f` commutes with the structure morphisms.

-/

@[expose] public section

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

variable {X Y Z : C} (f : X ⟶ Y) (S S' : C) {fXY : X ⟶ Y} {fX : X ⟶ S} {fY : Y ⟶ S} {fZ : Z ⟶ S}
  {fX' : X ⟶ S'} {fY' : Y ⟶ S'} {fS : S ⟶ S'}

/--
`OverClass X S f` is the typeclass asserting that `f : X ⟶ S` is the structure morphism of `X`
over `S`. Since `f` is an `outParam`, the notation `X ↘ S` elaborates to `f` itself.
-/
class OverClass (X S : C) (f : outParam <| X ⟶ S) : Type v where

meta section
open Lean Elab Term Meta

/--
`X ↘ S` elaborates to the structure morphism `f : X ⟶ S` obtained by synthesizing an
`OverClass X S f` instance. In particular the notation unfolds to `f` during elaboration
and leaves no trace in the resulting term.
-/
elab:90 X:term:90 " ↘ " S:term:90 : term => do
  let X ← elabTerm X none
  let C ← inferType X
  tryPostponeIfMVar C
  let S ← elabTerm S C
  let f ← mkFreshExprMVar (← mkAppM ``Quiver.Hom #[X, S])
  discard <| synthInstance (← mkAppM ``OverClass #[X, S, f])
  instantiateMVars f

end

/--
`CanonicallyOverClass X S f` is the typeclass asserting that `f : X ⟶ S` is the structure
morphism of `X` over `S`, and that `S` is (uniquely) inferable from the structure of `X`.
-/
class CanonicallyOverClass (X : C) (S : semiOutParam C) (f : outParam <| X ⟶ S) : Type v
  extends OverClass X S f where

instance : OverClass X X (𝟙 X) := ⟨⟩

instance (priority := 900) {f : X ⟶ Y} {g : Y ⟶ S} [CanonicallyOverClass X Y f]
    [OverClass Y S g] : OverClass X S (f ≫ g) := ⟨⟩

/-- Given `OverClass X S fX` and `OverClass Y S fY` and `f : X ⟶ Y`,
`HomIsOver f S` is the typeclass asserting `f` commutes with the structure morphisms. -/
class HomIsOver (f : X ⟶ Y) (S : C) {fX : X ⟶ S} {fY : Y ⟶ S}
    [OverClass X S fX] [OverClass Y S fY] : Prop where
  comp_over : f ≫ Y ↘ S = X ↘ S := by aesop

-- this is not a simp lemma since the LHS will match every composition of morphisms
@[reassoc]
lemma comp_over [OverClass X S fX] [OverClass Y S fY] [HomIsOver f S] : f ≫ Y ↘ S = X ↘ S :=
  HomIsOver.comp_over

instance {fX : X ⟶ S} [OverClass X S fX] : HomIsOver (𝟙 X) S where

instance {fX : X ⟶ S} {fY : Y ⟶ S} {fZ : Z ⟶ S}
    [OverClass X S fX] [OverClass Y S fY] [OverClass Z S fZ]
    (f : X ⟶ Y) (g : Y ⟶ Z) [HomIsOver f S] [HomIsOver g S] :
    HomIsOver (f ≫ g) S where
  comp_over := by simp [comp_over]

/-- `IsOverTower X Y S` is the typeclass asserting that the structure morphisms
`X ↘ Y`, `Y ↘ S`, and `X ↘ S` commute. -/
abbrev IsOverTower (X Y S : C) {fXY : X ⟶ Y} {fX : X ⟶ S} {fY : Y ⟶ S}
    [OverClass X S fX] [OverClass Y S fY] [OverClass X Y fXY] :=
  HomIsOver (X ↘ Y) S

instance {fX : X ⟶ S} [OverClass X S fX] : IsOverTower X X S where
instance {fX : X ⟶ S} [OverClass X S fX] : IsOverTower X S S where

instance {f : X ⟶ Y} {g : Y ⟶ S} [CanonicallyOverClass X Y f] [OverClass Y S g] :
    IsOverTower X Y S :=
  ⟨rfl⟩

lemma homIsOver_of_isOverTower [OverClass X S fX] [OverClass X S' fX'] [OverClass Y S fY]
    [OverClass Y S' fY'] [OverClass S S' fS]
    [IsOverTower X S S'] [IsOverTower Y S S'] [HomIsOver f S] : HomIsOver f S' := by
  constructor
  rw [← comp_over (Y ↘ S) S', comp_over_assoc f, comp_over]

instance [CanonicallyOverClass X S fX]
    [OverClass X S' fX'] [OverClass Y S fY] [OverClass Y S' fY'] [OverClass S S' fS]
    [IsOverTower X S S'] [IsOverTower Y S S'] [HomIsOver f S] : HomIsOver f S' :=
  homIsOver_of_isOverTower f S S'

instance [OverClass X S fX]
    [OverClass X S' fX'] [CanonicallyOverClass Y S fY] [OverClass Y S' fY'] [OverClass S S' fS]
    [IsOverTower X S S'] [IsOverTower Y S S'] [HomIsOver f S] : HomIsOver f S' :=
  homIsOver_of_isOverTower f S S'

variable (X) in
/-- Bundle `X` with an `OverClass X S f` instance into `Over S`. -/
@[simps! hom left]
def OverClass.asOver {fX : X ⟶ S} [OverClass X S fX] : Over S := Over.mk (X ↘ S)

/-- Bundle a morphism `f : X ⟶ Y` with `HomIsOver f S` into a morphism in `Over S`. -/
@[simps! left]
def OverClass.asOverHom {fX : X ⟶ S} {fY : Y ⟶ S} [OverClass X S fX] [OverClass Y S fY]
    (f : X ⟶ Y) [HomIsOver f S] : OverClass.asOver X S ⟶ OverClass.asOver Y S :=
  Over.homMk f (comp_over f S)

instance OverClass.fromOver {S : C} (X : Over S) : OverClass X.left S X.hom := ⟨⟩

instance {S : C} {X Y : Over S} (f : X ⟶ Y) : HomIsOver f.left S where
  comp_over := Over.w f

variable [OverClass X S fX] [OverClass Y S fY] [OverClass Z S fZ]

namespace OverClass

instance (f : X ⟶ Y) [IsIso f] [HomIsOver f S] : IsIso (asOverHom S f) :=
  have : IsIso ((Over.forget S).map (asOverHom S f)) := ‹_›
  isIso_of_reflects_iso _ (Over.forget _)

attribute [local simp] Iso.inv_comp_eq in
instance {e : X ≅ Y} [HomIsOver e.hom S] : HomIsOver e.inv S where
  comp_over := by simp [comp_over]

set_option linter.style.whitespace false in -- linter false positive
attribute [local simp ←] Iso.eq_inv_comp in
instance {e : X ≅ Y} [HomIsOver e.inv S] : HomIsOver e.hom S where
  comp_over := by simp [comp_over]

instance {f : X ⟶ Y} [IsIso f] [HomIsOver f S] : HomIsOver (asIso f).hom S where
  comp_over := by simp [comp_over]

instance {f : X ⟶ Y} [IsIso f] [HomIsOver f S] : HomIsOver (asIso f).inv S where
  comp_over := by simp [comp_over]

instance {f : X ⟶ Y} [IsIso f] [HomIsOver f S] : HomIsOver (inv f) S where
  comp_over := by simp [comp_over]

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
