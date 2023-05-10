import Mathlib.CategoryTheory.Grothendieck
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.RingCat.Basic

variable {R S : Type _} [CommRing R] [CommRing S]
  {M : Type _} [AddCommGroup M] [Module S M] {N : Type _} [AddCommGroup N] [Module S N]

def Module.pullback (_f : R →+* S) (M : Type _) := M

instance (f : R →+* S) [I : AddCommMonoid M] : AddCommMonoid (Module.pullback f M) := I
instance (f : R →+* S) [I : AddCommGroup M] : AddCommGroup (Module.pullback f M) := I
instance (f : R →+* S) [AddCommMonoid M] [Module S M] : Module R (Module.pullback f M) :=
  Module.compHom M f

def LinearMap.pullback (f : R →+* S) (g : M →ₗ[S] N) :
    (Module.pullback f M) →ₗ[R] (Module.pullback f N) where
  toFun := g
  map_add' := g.map_add
  map_smul' r x := g.map_smul (f r) x

def ModuleCat.pullback {R S : Type _} [CommRing R] [CommRing S] (f : R →+* S) :
    ModuleCat S ⥤ ModuleCat R where
  obj M := ModuleCat.of R (Module.pullback f M)
  map g := g.pullback f

-- Oops, can't do this yet as we haven't ported RingCat!

def ModuleCatFunctor : CommRingCat ⥤ Cat where
