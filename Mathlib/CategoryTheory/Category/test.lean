import Mathlib.CategoryTheory.Grothendieck
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.Ring.Basic

/-!
# The category of pairs `(R, M)`, where `M` is an `R`-module.

We implement this using the Grothendieck construction.
-/

-- Porting note:
-- After the port, move `Module.pullback` and `LinearMap.pullback` into the linear algebra library.

variable {R S : Type _} [Semiring R] [Semiring S]
  {M : Type _} [AddCommMonoid M] [Module S M] {N : Type _} [AddCommMonoid N] [Module S N]

/--
A type synonym for pulling back a module structure along a morphism of rings.
We have `(r • x : Module.pullback f m) = ((f r) • x : M)`.
-/
def Module.pullback (_f : R →+* S) (M : Type _) := M

instance (f : R →+* S) [I : AddCommMonoid M] : AddCommMonoid (Module.pullback f M) := I
instance (f : R →+* S) [I : AddCommGroup M] : AddCommGroup (Module.pullback f M) := I
instance (f : R →+* S) [AddCommMonoid M] [Module S M] : Module R (Module.pullback f M) :=
  Module.compHom M f

/-- We can pullback a linear map along a morphism of rings,
obtaining a linear map between
the modules with module structure obtained by pullback along the morphism.
The underlying function is just original underlying function.
-/
def LinearMap.pullback (f : R →+* S) (g : M →ₗ[S] N) :
    (Module.pullback f M) →ₗ[R] (Module.pullback f N) where
  toFun := g
  map_add' := g.map_add
  map_smul' r x := g.map_smul (f r) x

/-- The functor from modules over `S` to modules over `R` giving by pulling back
along a ring morphisms `f`. -/
def ModuleCat.pullback {R S : Type _} [Semiring R] [Semiring S] (f : R →+* S) :
    ModuleCat S ⥤ ModuleCat R where
  obj M := ModuleCat.of R (Module.pullback f M)
  map g := g.pullback f

instance : Faithful (ModuleCat.pullback f) := {}

-- Oops, can't do this yet as we haven't ported RingCat!

/-- The functor from the opposite of the category of rings to the category of categories,
given by taking modules over a ring. -/
def ModuleCat.functor : RingCatᵒᵖ ⥤ Cat where
  obj R := ModuleCat (unop R)
  map f := ModuleCat.pullback f

/-- The category consisting of pairs `{ base := R, fiber := M }`,
`R` is a ring and `M` is a module over `R`. -/
def RingMod := Grothendieck ModuleCat.functor
deriving LargeCategory, ConcreteCategory

namespace RingMod

instance hasForgetToRingCat : HasForget₂ RingMod RingCat := sorry
instance hasForgetToAddCommGroupCat : HasForget₂ RingMod AddCommGroupCat := sorry

end RingMod

/-- The category consisting of pairs `{ base := R, fiber := M }`,
`R` is a commutative ring and `M` is a module over `R`. -/
def CommRingMod := Grothendieck ((forget₂ CommRingCat RingCat).op ⋙ ModuleCat.functor)
deriving LargeCategory, ConcreteCategory

namespace CommRingMod

instance hasForgetToCommRingCat : HasForget₂ CommRingMod CommRingCat := sorry
instance hasForgetToAddCommGroupCat : HasForget₂ CommRingMod AddCommGroupCat := sorry
instance hasForgetToRingMod : HasForget₂ CommRingMod RingMod := sorry

end CommRingMod

structure PresheafRel (F : Cᵒᵖ ⥤ R) (M : Rᵒᵖ ⥤ Cat) where
  presheaf : Cᵒᵖ ⥤ Grothendieck M
  iso : presheaf ⋙ Grothendieck.forget ≅ F
