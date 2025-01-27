import Mathlib.Algebra.Category.AlgebraCat.Basic
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.Topology.Category.TopCat.Basic

namespace ConcreteCategoriesDemo

universe u
open CategoryTheory
set_option pp.coercions false

/-!
# A demo of the concrete category refactors.

I have been working on refactoring the Mathlib implementation of *concrete categories*.
These are essential for getting more advanced mathematics in Mathlib, but we repeatedly ran into
some structural issues.
-/


/-!
## Quick category theory overview

A category consists of two collections and two operations:
* A collection of *objects* X, Y, Z, ...
* A collection of *morphisms* (aka *arrows*) f : X ⟶ Y, g : X ⟶ Z, ...
* For each object X, an *identity* morphism 𝟙 X : X ⟶ X
* For each pair of morphisms f : X ⟶ Y, g : Y ⟶ Z, a *composition* `f ≫ g : X ⟶ Z`
* Axioms: associativity and identity

In Mathlib we define them (approximately) as follows:
-/

#print Category
/-
Which prints something like:
class CategoryTheory.Category.{v, u} (obj : Type u) : Type (max u (v + 1)) where
  Hom : obj → obj → Type v
  id : (X : obj) → X ⟶ X
  comp : {X Y Z : obj} → (X ⟶ Y) → (Y ⟶ Z) → (X ⟶ Z)
  assoc : ∀ {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z), (f ≫ g) ≫ h = f ≫ g ≫ h
  id_comp : ∀ {X Y : obj} (f : X ⟶ Y), 𝟙 X ≫ f = f
  comp_id : ∀ {X Y : obj} (f : X ⟶ Y), f ≫ 𝟙 Y = f
-/

/-!
Objects are given by **parameter** `obj`, morphisms as **field** `Hom`.
That matches pen and paper maths, where we usually name categories after objects.
-/

/-!
## Important examples of categories
-/

#synth Category (Discrete Empty) -- "0": no objects, no morphisms
#synth Category (Discrete (Fin 1)) -- "1": one object, one (identity) morphism.
#synth Category (Discrete (Fin 2)) -- "2": two objects, one (identity) morphism each.

#synth Category (Type u) -- "Type": objects are types in a specific universe `u` and morphisms are
-- functions between types.
#synth Category TopCat -- "Top": objects are topological spaces, morphisms are continuous maps.
#synth Category Cat -- "Cat": objects are categories, morphisms are *functors*.
#synth Category Grp -- "Grp": objects are groups, morphisms are group homomorphisms.
#synth Category RingCat -- "Ring": objects are rings, morphisms are ring homomorphisms.

/-!
The second block of examples all look very similar:
the objects are some set of types (+ extra structure), and morphisms some set of function
(+ extra structure).

Objects of `RingCat` are types `α` together with typeclass instances `Ring α`:
-/
#print RingCat
/-!
And morphisms are functions `f : X → Y` bundled together with proofs about the group structure:
-/
#print RingCat.Hom
#print RingHom

/-!
## Concrete categories

So `Grp` and `RingCat` and `TopCat` and `Type` are examples of *concrete categories*.
A concrete category `C` has objects which are "fancy" types and morphisms which are "fancy" functions.
In complicated categorical terms, `C` has a *faithful functor* `C ⟶ Type`,
called the *forgetful functor*, since it "forgets" the "fancy" extra structure,
projecting it down to types and functions.
-/
#print forget

/-- And for `Type` itself, this forgetful functor is just the identity map. -/
example : forget Type = 𝟭 _ := rfl

/-!
So Mathlib used to have the existence of `forget` as the definition of a concrete category.
That works well when staying in the categorical world.
But combining with the "naïve" category-free world is difficult.

For example:
-/
#print RingHom.map_mul

#check RingHom.map_mul (𝟙 (RingCat.of ℤ))
/-
application type mismatch
  RingHom.map_mul (𝟙 (RingCat.of ℤ))
argument
  𝟙 (RingCat.of ℤ)
has type
  RingCat.of ℤ ⟶ RingCat.of ℤ : Type ?u.403
but is expected to have type
  ?m.398 →+* ?m.399 : Type (max ?u.397 ?u.396)
-/

/-!
More generally, even if we defined the `Category RingCat` instance to have `X ⟶ Y := X →+* Y`,
this equality is only *reducible with instances*, which tactics don't always see through.

So Mathlib ended up with many different workarounds: type ascriptions, `show`, `erw`, ...
The solution is to **break** the equality of `X ⟶ Y` and `X →+* Y`, everywhere, consistently.
-/

/-!
## Concrete category refactoring: Hom structures

Christian Merten started breaking the equality of morphisms and I picked up some of this.
We make `X ⟶ Y` and `X →+* Y` distinct by wrapping in a one-field structure:
-/

#print RingCat.Hom

/-!
We add explicit coercions `hom : (X ⟶ Y) → (X →+* Y)` and `ofHom : (X →+* Y) → (X ⟶ Y)`.
Sometimes, Lean's coercion mechanisms can insert these automatically.

Now all tactics agree on the equality of `X ⟶ Y` and `X →+* Y`: namely, they are **never** equal.
And so we can get rid of quite some type ascriptions and `erw`s,
at the expense of being more explicit about the casts.

We have implemented a few `Hom` structures already:
-/
#print AlgebraCat.Hom
#print ModuleCat.Hom
#print RingCat.Hom

/-!
Unfortunately, friction remains between the worlds.
We want to work with concrete categories in general:
-/
example {X Y Z : RingCat} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x) := by simp
example {X Y Z : Grp} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x) := by simp
example {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x) := by simp
/-!
This is true for any concrete category!
-/
#check ConcreteCategory.comp_apply

/-!
To turn `f ≫ g : X ⟶ Z` into a function, and `X` into a type (for `x : X`),
we use `CoeFun` and `CoeSort` instances.
If we have the forgetful functor, then the obvious way is:
-/
example {C : Type} [Category C] [HasForget C] (X : C) : Type := (forget C).obj X
example {C : Type} [Category C] [HasForget C] (X Y : C) (f : X ⟶ Y) :
    (forget C).obj X → (forget C).obj Y := (forget C).map f
/-!
But these instances lose track of the fact that, for `RingCat`, `X ⟶ Y` is a wrapper around `X →+* Y`.
So we ended up with two coercions: `(forget C).map f` (to work in general) versus
`RingHom.toFun (hom f)` (to work with rings).
These instances are definitionally equal, but not reducibly so.
(And similarly for `Grp`, `TopCat`, ... and `MonoidHom`, `ContinuousMap`, ...)

Mathlib already has a class for these kinds of bundled maps that coerce into functions:
they are instances of `FunLike`.
And we already have a way to turn objects of `RingCat` into types: it's the projection `X.carrier`.
So I created a new class, parametrizing over the coercions:
-/
#print ConcreteCategory
/-!
The important fields are `hom` and `ofHom`, corresponding to the `Hom` structure refactor,
and we need some laws on bijectivity, identity and composition.
These laws, plus `FunLike` give us a faithful forgetful functor:
-/
#print ConcreteCategory.toHasForget

/-!
## Does it work better?

Let's look at some type signatures:
-/
#check ∀ {X Y Z : RingCat} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X), (f ≫ g) x = g (f x)
#check map_mul -- Looks for `DFunLike.coe`
#check ConcreteCategory.comp_apply -- Looks for `ConcreteCategory.hom`

/-!
So we get a two-stage coercion which keeps the ring theorists happy (since their `FunLike` is still there)
and keeps the category theorists happy (since their `ConcreteCategory.hom` is still there).
A drawback is that `ConcreteCategory` has lots of parameters:
working in high generality means lots of `variable` declarations.

To figure out the precise definition of `ConcreteCategory` I went through a lot of experiments
changing details and trying to make Mathlib compile again:
* what becomes a parameter and what becomes a field?
* how to deal with edge cases like `Type`?
* which parameters can be explicit?

Now that the design is done, implementing is not so hard.
The `Hom` structure means explicitly inserting `hom` and `ofHom` (tedious but essentially mindless).
Upgrading `HasForget` to `ConcreteCategory` is usually a oneliner.
-/

/-!
## Lessons learned:

* If something (defeq of morphisms) works unreliably, consider disabling it everywhere (making a Hom structure).
* If you need more reducibility, try adding more parameters.
* Coercions and definitional equalities are still really hard.
-/

end ConcreteCategoriesDemo
