/-
Copyright (c) 2023 David Spivak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Spivak, Shaowei Lin
-/
import Init.Prelude
import Mathlib.CategoryTheory.Category.Basic

/-!
# Polynomial Functors

Defines the category of polynomial functors, as a type class parametrised by the type of objects.

## Notations

For polynomial functos, we use the same notation as that for categories.
* `𝟙 p` for the identity lens from `p` to itself (type as `\b1`)
* `p ⟶ q` for the space of lenses from `p` to `q` (type as `\-->`)
* `p ≫ q` for composition in the diagrammatic order (type as `\gg`)

We introduce some new notations in the `Poly` scope
* `A y^B` for monomials

Users may like to add `f ⊚ g` for composition in the classical order, using
```lean
local notation:80 f " ⊚ " g => composemap g f    -- type as \oo
```

Users preferring `;` to `≫` for composition in the diagrammatic order may add
```lean
local infixr:80 " ; " => composemap
```
-/

library_note "Poly universes"
/--
The category `Poly.{u, v}` of polynomial functors and lenses
between them contains polynomial functors
whose positions live in `Type u` and
whose directions have codomains in `Type v`.

These polynomial functors can be applied to types
in any `Type w` independent of `Type u` and `Type v`.
-/

universe u v w

namespace CategoryTheory

namespace Poly

/-!
## Category of polynommial functors
-/

/-- Poly as a type where the objects are pairs (pos, dir). -/
structure Poly where
  pos : Type u
  dir : pos -> Type v

/-- The type of lenses/maps from one polynomial functor to another. -/
def polymap (p q : Poly.{u, v}) : Type max u v :=
  Σ (onPos : p.pos -> q.pos),
  (P : p.pos) -> q.dir (onPos P) -> p.dir P

/-- The identity lens/map from a polynomial functor to itself. -/
def polyid (p : Poly) : polymap p p :=
  Sigma.mk (id) (λ _ ↦ id)

/-- Composition of lenses/maps. -/
def composemap {p q r : Poly} (f : polymap p q) (g : polymap q r) :
    (polymap p r) :=
  let onPos :=
    g.fst ∘ f.fst
  let onDir (P : p.pos) (rd : r.dir (onPos P)) :=
    f.snd P (g.snd (f.fst P) rd)
  Sigma.mk onPos onDir

/-- Poly as a type with some categorical structure. -/
instance Poly.categoryStruct : CategoryStruct Poly where
  Hom  := polymap
  id   := polyid
  comp := composemap

/-- Poly as a category. -/
instance Poly.category : Category Poly where
  id_comp := by intros; rfl
  comp_id := by intros; rfl
  assoc   := by intros; rfl

/-- Applying a polynomial functor to a type. -/
def applyFun (p : Poly.{u, v}) (T : Type w) : Type max u v w :=
  Σ (P : p.pos), (p.dir P) -> T

-- replaced by Poly.category.assoc --
-- theorem assoc {p q r s : Poly} :
--   (f : p ⇒ q) -> (g : q ⇒ r) -> (h : r ⇒ s) ->
--   (f ; (g ; h)) = ((f ; g) ; h) := by
--   intros
--   rfl

-- replaced by Poly.category.comp_id --
-- theorem unitl {p q : Poly} : (f : p ⇒ q) -> f = (f ; polyid) := by
--   intros
--   rfl

-- replaced by Poly.category.id_comp --
-- theorem unitr {p q : Poly} : (f : p ⇒ q) -> f = (polyid ; f) := by
--   intros
--   rfl

/-!
## Special functions
-/

/-- Notation for unique map from empty type. -/
scoped notation "!𝟬" => PEmpty.rec  -- type as !\sb0

/-- Unique map to unit type. -/
def bang1 {T : Type u} : T -> PUnit.{v+1} :=
  λ _ ↦ PUnit.unit

/-- Notation for unique map to unit type. -/
scoped notation "!𝟭" => bang1  -- type as !\sb1

/-!
## Special polynommial functors
-/

/-- A monomial functor. -/
def monomial (P : Type u) (D: Type v) : Poly.{u, v} where
  pos := P
  dir := (λ _ ↦ D)

/-- Notation for a monomial functor. -/
scoped notation:50 A:50 " y^" B:50 => monomial A B

/-- A representable functor. -/
def representable (D : Type v) : Poly.{u, v} := PUnit.{u+1} y^D

/-- Notation for a representable functor. -/
scoped notation:50 "y^" B:50 => representable B

/-- A constant polynomial functor. -/
def const (P : Type u) : Poly.{u, v} := P y^(PEmpty.{v+1})

/-- A linear polynomial functor. -/
def linear (P : Type u) : Poly.{u, v} := P y^(PUnit.{v+1})

/-- The initial object in Poly. -/
def poly0 : Poly.{u, v} := const PEmpty.{u+1}

/-- Notation for the initial object. -/
scoped notation "𝟬" => poly0  -- type as \sb0

/-- The terminal object in Poly. -/
def poly1 : Poly.{u, v} := const PUnit.{u+1}

/-- Notation for the terminal object. -/
scoped notation "𝟭" => poly1  -- type as \sb1

/-- The identity functor in Poly. -/
def y : Poly.{u, v} := linear PUnit.{u+1}

/-!
## Special lenses/maps
-/

def constantMap {T T' : Type u} (f : T -> T') : (const T) ⟶ (const T') :=
  Sigma.mk f (λ _ ↦ !𝟬)

def linearMap {T T' : Type u} (f : T -> T') : (linear T) ⟶ (linear T') :=
  Sigma.mk f (λ _ ↦ !𝟭)

def representableMap {T T' : Type u} (f : T -> T') : y^T' ⟶ y^T :=
  Sigma.mk !𝟭 (λ _ ↦ f)

def bang0poly {p : Poly.{u, v}} : 𝟬 ⟶ p :=
  Sigma.mk !𝟬 !𝟬

def bang1poly {P : Poly.{u, v}} : P ⟶ 𝟭 :=
  Sigma.mk !𝟭 (λ _ ↦ !𝟬)

def polymap2 (p q : Poly.{u, v}) : Type max u v :=
  (P : p.pos) -> Σ (Q : q.pos), q.dir Q -> p.dir P

def cast12 {p q : Poly.{u, v}} (f : p ⟶ q) : polymap2 p q :=
  λ P ↦ (Sigma.mk (f.fst P) (f.snd P))

def cast21 {p q : Poly.{u, v}} (f : polymap2 p q) : p ⟶ q :=
  Sigma.mk (λ P ↦ (f P).fst) (λ P ↦ (f P).snd)

def toTransformation {p q : Poly.{u, v}} (f : p ⟶ q) (T : Type) :
    (applyFun p T) -> (applyFun q T) :=
  λ pT ↦
  let P := pT.fst
  let Q := pT.snd
  Sigma.mk (f.fst P) (Q ∘ f.snd P)


-------- Substitution product ----------

def subst : Poly -> Poly -> Poly :=
  λ p q ↦
  {
    pos := applyFun p q.pos
    dir := λ x ↦
      let P := x.fst
      let Q := x.snd
    (d : p.dir P) × (q.dir (Q d))
  }

notation:80 p "◁" q => subst p q


def unitSubstRight {p : Poly} : (p ◁ y) ⟶ p :=
  sorry

structure Comonad where
  carrier : Poly
  counit  : carrier ⟶ y
  comult  : carrier ⟶ (carrier ◁ carrier)


end Poly

end CategoryTheory
