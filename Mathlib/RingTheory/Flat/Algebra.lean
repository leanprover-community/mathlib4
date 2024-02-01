/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Flat.Stability
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Flat algebras and flat ring homomorphisms

We define flat algebras and flat ring homomorphisms.

## Main definitions

* `Algebra.Flat`: an `R`-algebra `S` is flat if it is flat as `R`-module
* `RingHom.Flat`: a ring homomorphism `f : R → S` is flat, if it makes `S` into a flat `R`-algebra

-/

universe u v w t

open Function (Injective Surjective)

open LinearMap (lsmul rTensor lTensor)

open TensorProduct

/-- An `R`-algebra `S` is flat if it is flat as `R`-module. -/
class Algebra.Flat (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S] : Prop where
  out : Module.Flat R S

namespace Algebra.Flat

attribute [instance] out

instance self (R : Type u) [CommRing R] : Algebra.Flat R R where
  out := Module.Flat.self R

variable (R : Type u) (S : Type v) (T : Type w) [CommRing R] [CommRing S] [CommRing T]

/-- If `T` is a flat `S`-algebra and `S` is a flat `R`-algebra,
then `T` is a flat `R`-algebra. -/
theorem comp [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.Flat R S] [Algebra.Flat S T] : Algebra.Flat R T where
  out := Module.Flat.comp R S T

end Algebra.Flat

/-- A `RingHom` is flat if `R` is flat as an `S` algebra. -/
class RingHom.Flat {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) : Prop where
  out : f.toAlgebra.Flat := by infer_instance

namespace RingHom.Flat

attribute [instance] out

/-- The identity of a ring is flat. -/
instance identity (R : Type u) [CommRing R] : RingHom.Flat (1 : R →+* R) where

variable {R : Type u} {S : Type v} {T : Type w} [CommRing R] [CommRing S] [CommRing T]
  (f : R →+* S) (g : S →+* T)

/-- Composition of flat ring homomorphisms is flat. -/
instance comp [RingHom.Flat f] [RingHom.Flat g] : RingHom.Flat (g.comp f) where
  out :=
    letI : Algebra R S := f.toAlgebra
    letI : Algebra S T := g.toAlgebra
    letI : Algebra R T := (g.comp f).toAlgebra
    letI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq (congrFun rfl)
    Algebra.Flat.comp R S T

end RingHom.Flat
