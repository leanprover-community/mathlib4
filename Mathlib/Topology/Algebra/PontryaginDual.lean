/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.Algebra.ContinuousMonoidHom

#align_import topology.algebra.continuous_monoid_hom from "leanprover-community/mathlib"@"6ca1a09bc9aa75824bf97388c9e3b441fc4ccf3f"

/-!
# Pontryagin dual

This file defines the Pontryagin dual of a topological group. The Pontryagin dual of a topological
group `A` is the topological group of continuous homomorphisms `A →* circle` with the compact-open
topology. For example, `ℤ` and `circle` are Pontryagin duals of each other. This is an example of
Pontryagin duality, which states that a locally compact abelian topological group is canonically
isomorphic to its double dual.

## Main definitions

* `PontryaginDual A`: The group of continuous homomorphisms `A →* circle`.
-/

open Pointwise Function

variable (A B C D E : Type*) [Monoid A] [Monoid B] [Monoid C] [Monoid D] [CommGroup E]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]
  [TopologicalSpace E] [TopologicalGroup E]

/-- The Pontryagin dual of `A` is the group of continuous homomorphism `A → circle`. -/
def PontryaginDual :=
  ContinuousMonoidHom A circle
#align pontryagin_dual PontryaginDual

-- Porting note: `deriving` doesn't derive these instances
instance : TopologicalSpace (PontryaginDual A) :=
  (inferInstance : TopologicalSpace (ContinuousMonoidHom A circle))

instance : T2Space (PontryaginDual A) :=
  (inferInstance : T2Space (ContinuousMonoidHom A circle))

-- Porting note: instance is now noncomputable
noncomputable instance : CommGroup (PontryaginDual A) :=
  (inferInstance : CommGroup (ContinuousMonoidHom A circle))

instance : TopologicalGroup (PontryaginDual A) :=
  (inferInstance : TopologicalGroup (ContinuousMonoidHom A circle))

-- Porting note: instance is now noncomputable
noncomputable instance : Inhabited (PontryaginDual A) :=
  (inferInstance : Inhabited (ContinuousMonoidHom A circle))

variable {A B C D E}

namespace PontryaginDual

open ContinuousMonoidHom

instance : FunLike (PontryaginDual A) A circle :=
  ContinuousMonoidHom.funLike

noncomputable instance : ContinuousMonoidHomClass (PontryaginDual A) A circle :=
  ContinuousMonoidHom.ContinuousMonoidHomClass

/-- `PontryaginDual` is a contravariant functor. -/
noncomputable def map (f : ContinuousMonoidHom A B) :
    ContinuousMonoidHom (PontryaginDual B) (PontryaginDual A) :=
  f.compLeft circle
#align pontryagin_dual.map PontryaginDual.map

@[simp]
theorem map_apply (f : ContinuousMonoidHom A B) (x : PontryaginDual B) (y : A) :
    map f x y = x (f y) :=
  rfl
#align pontryagin_dual.map_apply PontryaginDual.map_apply

@[simp]
theorem map_one : map (one A B) = one (PontryaginDual B) (PontryaginDual A) :=
  ext fun x => ext (fun _y => OneHomClass.map_one x)
#align pontryagin_dual.map_one PontryaginDual.map_one

@[simp]
theorem map_comp (g : ContinuousMonoidHom B C) (f : ContinuousMonoidHom A B) :
    map (comp g f) = ContinuousMonoidHom.comp (map f) (map g) :=
  ext fun _x => ext fun _y => rfl
#align pontryagin_dual.map_comp PontryaginDual.map_comp

@[simp]
nonrec theorem map_mul (f g : ContinuousMonoidHom A E) : map (f * g) = map f * map g :=
  ext fun x => ext fun y => map_mul x (f y) (g y)
#align pontryagin_dual.map_mul PontryaginDual.map_mul

variable (A B C D E)

/-- `ContinuousMonoidHom.dual` as a `ContinuousMonoidHom`. -/
noncomputable def mapHom [LocallyCompactSpace E] :
    ContinuousMonoidHom (ContinuousMonoidHom A E)
      (ContinuousMonoidHom (PontryaginDual E) (PontryaginDual A)) where
  toFun := map
  map_one' := map_one
  map_mul' := map_mul
  continuous_toFun := continuous_of_continuous_uncurry _ continuous_comp
#align pontryagin_dual.map_hom PontryaginDual.mapHom

end PontryaginDual
