/-
Copyright (c) 2023 Scott Morrison All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.Grothendieck.Opposite

/-!
# The category of pairs `(R, M)`, where `M` is an `R`-module.

We implement this using the Grothendieck construction.
-/

-- Rings live in `u`, modules live in `v`.
universe v u

-- Porting note:
-- After the port, move `Module.pullback` and `LinearMap.pullback` into the linear algebra library.

variable {R S : Type u} [Semiring R] [Semiring S]
  {M : Type v} [AddCommMonoid M] [Module S M] {N : Type v} [AddCommMonoid N] [Module S N]

/--
A type synonym for pulling back a module structure along a morphism of rings.
We have `(r • x : Module.pullback f m) = ((f r) • x : M)`.
-/
def Module.pullback (_f : R →+* S) (M : Type v) := M

instance (f : R →+* S) [I : AddCommMonoid M] : AddCommMonoid (Module.pullback f M) := I
instance (f : R →+* S) [I : AddCommGroup M] : AddCommGroup (Module.pullback f M) := I
instance (f : R →+* S) [AddCommMonoid M] [Module S M] : Module R (Module.pullback f M) :=
  Module.compHom M f

/-- We can pullback a linear map along a morphism of rings,
obtaining a linear map between
the modules with module structure obtained by pullback along the morphism.
The underlying function is just original underlying function.
-/
@[simps]
def LinearMap.pullback (f : R →+* S) (g : M →ₗ[S] N) :
    (Module.pullback f M) →ₗ[R] (Module.pullback f N) where
  toFun := g
  map_add' := g.map_add
  map_smul' r x := g.map_smul (f r) x

/-- The functor from modules over `S` to modules over `R` giving by pulling back
along a ring morphisms `f`. -/
@[simps]
def ModuleCat.pullback {R S : Type u} [Ring R] [Ring S] (f : R →+* S) :
    ModuleCat S ⥤ ModuleCat R where
  obj M := ModuleCat.of R (Module.pullback f M)
  map g := g.pullback f

open CategoryTheory

instance {R S : Type _} [Ring R] [Ring S] (f : R →+* S) : Faithful (ModuleCat.pullback f) where
  map_injective := @fun M N f g w => by ext x; exact LinearMap.congr_fun w x

open Opposite

/-- The functor from the opposite of the category of rings to the category of categories,
given by taking modules over a ring. -/
def ModuleCat.functor : RingCat.{u}ᵒᵖ ⥤ Cat.{v, max (v + 1) u} where
  obj R := Cat.of <| ModuleCat.{v} (unop R : RingCat.{u})
  map f := ModuleCat.pullback f.unop

instance (R : RingCat) : CoeSort (ModuleCat.functor.obj (op R)) (Type _) where
  coe := ModuleCat.carrier

instance (R : RingCat) (M : ModuleCat.functor.obj (op R)) : AddCommGroup M :=
  ModuleCat.isAddCommGroup _

instance (R : RingCat) (M : ModuleCat.functor.obj (op R)) : Module R M :=
  ModuleCat.isModule _

section

variable {R S : RingCat} (f : R ⟶ S) {M : ModuleCat R} {N : ModuleCat S}

/-- A `R`-linear map from `M` to the pullback of an `S`-module `N` along a ring homomorphism
`f : R →+* S` is the same thing as an `f`-semilinear map. -/
def ModuleCat.hom_functor_map_equiv :
    (M ⟶ (ModuleCat.functor.map (f.op)).obj N) ≃ (M →ₛₗ[f] N) where
  toFun f :=
  { f.toAddMonoidHom with
    map_smul' := fun r x => f.map_smul r x }
  invFun f :=
  { f.toAddMonoidHom with
    map_smul' := fun r x => f.map_smul' r x }
  left_inv f := by aesop
  right_inv f := by aesop

@[simp] lemma ModuleCat.hom_functor_map_equiv_apply_apply :
    ModuleCat.hom_functor_map_equiv f g x = g x := rfl

@[simp] lemma ModuleCat.hom_functor_map_equiv_symm_apply_apply :
    (ModuleCat.hom_functor_map_equiv f).symm g x = g x := rfl

-- This equivalence is also compatible with composition,
-- but it awkward to state as it involves `ModuleCat.functor.map_comp`
-- as an equation between functors.

/-- The category consisting of pairs `{ base := R, fiber := M }`,
where `R` is a ring and `M` is a module over `R`. -/
def RingMod := opGrothendieck ModuleCat.functor
deriving LargeCategory

namespace RingMod

instance : ConcreteCategory RingMod where
  forget :=
  { obj := fun ⟨R, M⟩ => R × M
    map := @fun ⟨R₁, M₁⟩ ⟨R₂, M₂⟩ ⟨f, g⟩ ⟨x, y⟩ =>
      ((forget RingCat).map f x, (forget (ModuleCat R₁)).map g y) }
  forget_faithful :=
  { map_injective := @fun ⟨R₁, M₁⟩ ⟨R₂, M₂⟩ ⟨f₁, g₁⟩ ⟨f₂, g₂⟩ w => by
     dsimp at w
     have p : f₁ = f₂
     · apply RingHom.ext
       exact fun r => congr_arg Prod.fst (congr_fun w (r, 0))
     fapply opGrothendieck.ext ⟨f₁, g₁⟩ ⟨f₂, g₂⟩ p
     · subst p
       apply LinearMap.ext
       exact fun m => congr_arg Prod.snd (congr_fun w (1, m)) }

@[simp] lemma forget_obj (R : RingCat) (M : ModuleCat.functor.obj (op R)) :
    (forget RingMod).obj ⟨R, M⟩ = (R × M) := rfl

/-- The functor from `RingMod` to `RingCat` which forgets the module. -/
def toRingCat : RingMod ⥤ RingCat where
  obj := fun ⟨R, _⟩ => R
  map := fun ⟨f, _⟩ => f

/-- The functor from `RingMod` to `AddCommGroupCat` which forgets the ring and its action. -/
def toAddCommGroupCat : RingMod ⥤ AddCommGroupCat where
  obj := fun ⟨_, M⟩ => AddCommGroupCat.of M
  map := fun f => (ModuleCat.hom_functor_map_equiv f.base f.fiber).toAddMonoidHom

end RingMod

-- TODO say all that again for `CommRing`?
