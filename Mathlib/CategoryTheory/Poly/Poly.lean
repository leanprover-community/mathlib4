/-
Copyright (c) 2023 David Spivak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Spivak, Shaowei Lin
-/
import Init.Prelude
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Monoidal.Category

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

universe u v u' v' w

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
structure polymap (p q : Poly.{u, v}) : Type max u v where
  onPos : p.pos -> q.pos
  onDir : (x : p.pos) -> q.dir (onPos x) -> p.dir x

/-- The identity lens/map from a polynomial functor to itself. -/
def polyid (p : Poly) : polymap p p where
  onPos := id
  onDir := λ _ ↦ id

/-- Composition of lenses/maps. -/
def composemap {p q r : Poly} (f : polymap p q) (g : polymap q r) :
    polymap p r where
  onPos := g.onPos ∘ f.onPos
  onDir := λ px rd ↦ f.onDir px (g.onDir (f.onPos px) rd)

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

/-- Applying a polynomial functor to get a type. -/
def applyFun (p : Poly.{u, v}) (T : Type w) :
    Type max u v w :=
  Σ (x : p.pos), (p.dir x) -> T

/-- Applying a lens/map to get a function. -/
def applyMap {p q : Poly.{u, v}} (f : p ⟶ q) (T : Type) :
    (applyFun p T) -> (applyFun q T) :=
  λ x ↦ Sigma.mk (f.onPos x.fst) (x.snd ∘ (f.onDir x.fst))





/-!
## Special polynommial functors
-/

/-- A monomial functor. -/
def monomial (P : Type u) (D: Type v) : Poly.{u, v} where
  pos := P
  dir := (λ _ ↦ D)

/-- Notation for a monomial functor. -/
scoped notation:80 A:80 " y^" B:80 => monomial A B

/-- A representable functor. -/
def representable (D : Type v) : Poly.{u, v} := PUnit.{u+1} y^D

/-- Notation for a representable functor. -/
scoped notation:80 "y^" B:80 => representable B

/-- A constant polynomial functor. -/
def const (P : Type u) : Poly.{u, v} := P y^(PEmpty.{v+1})

/-- Notation for a constant polynomial functor. -/
scoped notation:80 A:80 " y^0" => const A

/-- A linear polynomial functor. -/
def linear (P : Type u) : Poly.{u, v} := P y^(PUnit.{v+1})

/-- Notation for a linear polynomial functor. -/
scoped notation:80 A:80 " y^1" => linear A

/-- The identity functor in Poly. -/
def y : Poly.{u, v} := linear PUnit.{u+1}

/-- Additional notation for a linear polynomial functor. -/
scoped notation "y^1" => y

/-- The initial object in Poly. -/
def poly0 : Poly.{u, v} := const PEmpty.{u+1}

/-- Notation for the initial object. -/
scoped notation "𝟬" => poly0  -- type as `\sb0`

/-- Notation for unique map from empty type. -/
scoped notation "!𝟬" => PEmpty.rec  -- type as `!\sb0`

/-- The terminal object in Poly. -/
def poly1 : Poly.{u, v} := const PUnit.{u+1}

/-- Notation for the terminal object. -/
scoped notation "𝟭" => poly1  -- type as `\sb1`

/-- Notation for unique map to unit type. -/
scoped notation "!𝟭" => Function.const _ PUnit.unit  -- type as `!\sb1`





/-!
## Special lenses/maps
-/

/-- A lens/map between constant polynomial functors. -/
def constantMap {T T' : Type u} (f : T -> T') : T y^0 ⟶ T' y^0 where
  onPos := f
  onDir := (λ _ ↦ !𝟬)

/-- A lens/map between linear polynomial functors. -/
def linearMap {T T' : Type u} (f : T -> T') : T y^1 ⟶ T' y^1 where
  onPos := f
  onDir := (λ _ ↦ !𝟭)

/-- A lens/map between representable functors. -/
def representableMap {T T' : Type u} (f : T -> T') : y^T' ⟶ y^T where
  onPos := !𝟭
  onDir := (λ _ ↦ f)

/-- The unique lens/map from the initial object in Poly. -/
def bang0poly {p : Poly.{u, v}} : 𝟬 ⟶ p where
  onPos := !𝟬
  onDir := !𝟬

/-- The unique lens/map to the terminal object in Poly. -/
def bang1poly {P : Poly.{u, v}} : P ⟶ 𝟭 where
  onPos := !𝟭
  onDir := (λ _ ↦ !𝟬)

/-- A second representation for the type of lenses/maps. -/
def polymap2 (p q : Poly.{u, v}) : Type max u v :=
  (px : p.pos) -> Σ (qx : q.pos), q.dir qx -> p.dir px

/-- Casting from the default representation for the type
    of lenses/maps to the second representation. -/
def cast12 {p q : Poly.{u, v}} (f : p ⟶ q) : polymap2 p q :=
  λ px ↦ (Sigma.mk (f.onPos px) (f.onDir px))

/-- Casting from the second representation for the type
    of lenses/maps to the default representation. -/
def cast21 {p q : Poly.{u, v}} (f : polymap2 p q) : p ⟶ q where
  onPos := (λ px ↦ (f px).fst)
  onDir := (λ px ↦ (f px).snd)





/-!
## Substitution product
-/

/--
Substitution product of polynomial functors.
Require polynomial functors from Poly.{u, u}
for the product to remain in Poly.{u, u}.
-/
def subst (p q : Poly.{u, u}) : Poly.{u, u} where
  pos := applyFun p q.pos
  dir := λ x ↦ Σ (d : p.dir x.fst), (q.dir (x.snd d))

/-- Notation for substitution product of polynomial functors. -/
scoped infixr:80 "◁" => subst -- type as `\lhd`

def subst.whiskerLeft (p q q': Poly) (f : q ⟶ q') :
    (p ◁ q) ⟶ (p ◁ q') where
  onPos := λ x ↦ Sigma.mk x.fst (f.onPos ∘ x.snd)
  onDir := λ x d ↦ Sigma.mk d.fst (f.onDir (x.snd d.fst) d.snd)

def subst.whiskerRight (f : p ⟶ p') (q : Poly) :
    (p ◁ q) ⟶ (p' ◁ q) where
  onPos := applyMap f q.pos
  onDir := λ x d ↦ Sigma.mk (f.onDir x.fst d.fst) d.snd

def subst.leftUnitor.hom (p : Poly) : (y ◁ p) ⟶ p where
  onPos := λ x ↦ x.snd x.fst
  onDir := λ _ d ↦ Sigma.mk PUnit.unit d

def subst.leftUnitor.inv (p : Poly) : p ⟶ (y ◁ p) where
  onPos := λ x ↦ Sigma.mk PUnit.unit (λ _ ↦ x)
  onDir := λ _ d ↦ d.snd

def subst.leftUnitor (p : Poly) : (y ◁ p) ≅ p where
  hom := subst.leftUnitor.hom p
  inv := subst.leftUnitor.inv p

def subst.rightUnitor.hom (p : Poly) : (p ◁ y) ⟶ p where
  onPos := λ x ↦ x.fst
  onDir := λ _ d ↦ Sigma.mk d PUnit.unit

def subst.rightUnitor.inv (p : Poly) : p ⟶ (p ◁ y) where
  onPos := λ x ↦ Sigma.mk x (λ _ ↦ PUnit.unit)
  onDir := λ _ d ↦ d.fst

def subst.rightUnitor (p : Poly) : (p ◁ y) ≅ p where
  hom := subst.rightUnitor.hom p
  inv := subst.rightUnitor.inv p

def subst.associator.hom (p q r : Poly) :
    (p ◁ q) ◁ r ⟶ p ◁ (q ◁ r) := by
  constructor
  case onPos =>
    intro pq_r
    let pq_r1 := pq_r.fst
    let pq_r2 := pq_r.snd
    let pq_r11 := pq_r1.fst
    let pq_r12 := pq_r1.snd
    constructor
    case fst =>
      exact pq_r11
    case snd =>
      intro pd
      constructor
      case fst =>
        exact pq_r12 pd
      case snd =>
        intro qd
        exact pq_r2 (Sigma.mk pd qd)
  case onDir =>
    intro _ p_qr
    let p_qr1  := p_qr.fst
    let p_qr2  := p_qr.snd
    let p_qr21 := p_qr2.fst
    let p_qr22 := p_qr2.snd
    exact Sigma.mk (Sigma.mk p_qr1 p_qr21) p_qr22

def subst.associator.inv (p q r : Poly) :
    p ◁ (q ◁ r) ⟶ (p ◁ q) ◁ r := by
  constructor
  case onPos =>
    intro p_qr
    let p_qr1 := p_qr.fst
    let p_qr2 := p_qr.snd
    constructor
    case fst =>
      constructor
      case fst =>
        exact p_qr1
      case snd =>
        intros pd
        exact (p_qr2 pd).fst
    case snd =>
      intro pqd
      exact (p_qr2 pqd.fst).snd pqd.snd
  case onDir =>
    intro p_qr1 pq_rd
    let pq_rd1 := pq_rd.fst
    let pq_rd2 := pq_rd.snd
    constructor
    case fst =>
      exact pq_rd1.fst
    case snd =>
      constructor
      case fst =>
        exact pq_rd1.snd
      case snd =>
        exact pq_rd2

def subst.associator (p q r : Poly) : (p ◁ q) ◁ r ≅ p ◁ (q ◁ r) where
  hom := subst.associator.hom p q r
  inv := subst.associator.inv p q r

instance Poly.subst.monoidalStruct : MonoidalCategoryStruct Poly where
  tensorObj    := subst
  whiskerLeft  := subst.whiskerLeft
  whiskerRight := subst.whiskerRight
  tensorUnit   := y
  leftUnitor   := subst.leftUnitor
  rightUnitor  := subst.rightUnitor
  associator   := subst.associator

/-- All hyptheses proven automatically so none provided. -/
instance Poly.subst.monoidal : MonoidalCategory Poly where

-- structure Comonad where
--   carrier : Poly
--   counit  : carrier ⟶ y
--   comult  : carrier ⟶ (carrier ◁ carrier)


end Poly

end CategoryTheory
