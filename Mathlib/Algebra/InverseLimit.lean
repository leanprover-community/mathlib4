/-
Copyright (c) 2024 Peiran Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peiran Wu
-/
import Mathlib.Data.Finset.Order
import Mathlib.Algebra.Module.LinearMap
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.RingTheory.Subring.Basic

/-!
# Inverse Limits of Modules, Abelian Groups, and Rings

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Tags

Foobars, barfoos
-/


variable {ι : Type*} [Preorder ι]
variable (G : ι → Type*)


section InverseSystem

variable (f : ∀ i j, i ≤ j → G j → G i)

/-- An inverse system is a family of objects and compatible morphisms,
has a greater index than the codomain. -/
class InverseSystem : Prop where
  map_self' : ∀ i x, f i i le_rfl x = x
  map_map' : ∀ {i j k} hij hjk x, f i j hij (f j k hjk x) = f i k (le_trans hij hjk) x

variable {G} [InverseSystem G f]

theorem InverseSystem.map_self i x : f i i le_rfl x = x :=
  InverseSystem.map_self' i x

theorem InverseSystem.map_map {i j k} (hij hjk x) :
    f i j hij (f j k hjk x) = f i k (le_trans hij hjk) x :=
  InverseSystem.map_map' hij hjk x

end InverseSystem


namespace Module

variable (R : Type*) [Ring R]
variable [∀ i, AddCommMonoid (G i)] [∀ i, Module R (G i)]
variable (f : ∀ i j, i ≤ j → G j →ₗ[R] G i)

private def inverseLimit : Submodule R (∀ i, G i) where
  carrier := { a | ∀ i j hij, a i = f i j hij (a j) }
  add_mem' ha hb i j hij := by simp [ha i j hij, hb i j hij]
  zero_mem' := by simp
  smul_mem' _ _ ha i j hij := by simp [ha i j hij]

/-- The inverse limit of an inverse family of rings and ring homomorphisms. -/
def InverseLimit : Type _ := inverseLimit G R f

namespace InverseLimit

variable {G R f}

instance addCommMonoid : AddCommMonoid (InverseLimit G R f) :=
  Submodule.addCommMonoid _

instance module : Module R (InverseLimit G R f) :=
  Submodule.module _

@[ext]
lemma ext {x y : inverseLimit G R f} (h : ∀ i, x.val i = y.val i) : x = y :=
  Subtype.eq <| funext h

end InverseLimit

end Module


namespace AddCommGroup

variable [∀ i, AddCommGroup (G i)]
variable (f : ∀ i j, i ≤ j → G j →+ G i)

private def inverseLimit : AddSubgroup (∀ i, G i) :=
  Submodule.toAddSubgroup <| Module.inverseLimit G ℤ
    fun i j hij => AddMonoidHom.toIntLinearMap (f i j hij)

def InverseLimit : Type _ := inverseLimit G f

namespace InverseLimit

variable {G f}

instance addCommGroup : AddCommGroup (InverseLimit G f) :=
  AddSubgroup.toAddCommGroup _

@[ext]
lemma ext {x y : inverseLimit G f} (h : ∀ i, x.val i = y.val i) : x = y :=
  Subtype.eq <| funext h

end InverseLimit

end AddCommGroup


namespace Ring

variable [∀ i, Ring (G i)]
variable (f : ∀ i j, i ≤ j → G j →+* G i)

private def inverseLimit : Subring (∀ i, G i) where
  carrier := (AddCommGroup.inverseLimit G fun i j hij => f i j hij).carrier
  mul_mem' ha hb i j hij := by simp [ha i j hij, hb i j hij]
  one_mem' := by simp [AddCommGroup.inverseLimit, Module.inverseLimit]
  add_mem' := (AddCommGroup.inverseLimit G fun i j hij => f i j hij).add_mem'
  zero_mem' := (AddCommGroup.inverseLimit G fun i j hij => f i j hij).zero_mem'
  neg_mem' ha i j hij := by simp [ha i j hij]

def InverseLimit : Type _ := inverseLimit G f

namespace InverseLimit

variable {G f}

@[ext]
lemma ext {x y : InverseLimit G f} (h : ∀ i, x.val i = y.val i) : x = y :=
  Subtype.eq <| funext h

instance ring : Ring (InverseLimit G f) :=
  Subring.toRing _

def projection (i : ι) : InverseLimit G f →+* G i where
  toFun := fun ⟨r, _⟩ => r i
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

lemma projection_map (i j hij) (r : InverseLimit G f):
    projection i r = (f i j hij) (projection j r) :=
  r.property i j hij

variable {R : Type*} [Ring R] {rProjection : ∀ i, R →+* G i}
 (rProjection_map : ∀ i j hij r, rProjection i r = (f i j hij) (rProjection j r))

def lift : R →+* InverseLimit G f where
  toFun := fun r => ⟨fun i => rProjection i r, fun _ _ _ => rProjection_map _ _ _ r⟩
  map_one' := ext fun i => map_one (rProjection i)
  map_mul' := fun r s => ext fun i => map_mul (rProjection i) r s
  map_zero' := ext fun i => map_zero (rProjection i)
  map_add' := fun r s => ext fun i => map_add (rProjection i) r s

lemma projection_lift :
    ∀ i, projection i ∘ (lift rProjection_map) = rProjection i :=
  fun _ => rfl

lemma lift_unique (lift' : R →+* InverseLimit G f)
    (projection_lift' : ∀ i, projection i ∘ lift' = rProjection i) :
    lift' = lift rProjection_map := by
  ext r i
  exact Function.funext_iff.mp (projection_lift' i) r

end InverseLimit

end Ring
