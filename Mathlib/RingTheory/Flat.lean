/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.RingTheory.Noetherian
import Mathlib.CategoryTheory.ShortExactSequence
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.Homology

#align_import ring_theory.flat from "leanprover-community/mathlib"@"62c0a4ef1441edb463095ea02a06e87f3dfe135c"

/-!
# Flat modules

A module `M` over a commutative ring `R` is *flat*
if for all finitely generated ideals `I` of `R`,
the canonical map `I ⊗ M →ₗ M` is injective.

This is equivalent to the claim that for all injective `R`-linear maps `f : M₁ → M₂`
the induced map `M₁ ⊗ M → M₂ ⊗ M` is injective.
See <https://stacks.math.columbia.edu/tag/00HD>.
This result is not yet formalised.

## Main declaration

* `Module.Flat`: the predicate asserting that an `R`-module `M` is flat.

## TODO

* Show that tensoring with a flat module preserves injective morphisms.
  Show that this is equivalent to be flat.
  See <https://stacks.math.columbia.edu/tag/00HD>.
  To do this, it is probably a good idea to think about a suitable
  categorical induction principle that should be applied to the category of `R`-modules,
  and that will take care of the administrative side of the proof.
* Define flat `R`-algebras
* Define flat ring homomorphisms
  - Show that the identity is flat
  - Show that composition of flat morphisms is flat
* Show that flatness is stable under base change (aka extension of scalars)
  For base change, it will be very useful to have a "characteristic predicate"
  instead of relying on the construction `A ⊗ B`.
  Indeed, such a predicate should allow us to treat both
  `A[X]` and `A ⊗ R[X]` as the base change of `R[X]` to `A`.
  (Similar examples exist with `Fin n → R`, `R × R`, `ℤ[i] ⊗ ℝ`, etc...)
* Generalize flatness to noncommutative rings.

-/


universe u v

namespace Module

open Function (Injective)
open CategoryTheory MonoidalCategory Limits

open LinearMap (lsmul)

variable (R : Type u) (M : Type u) [CommRing R] [AddCommGroup M] [Module R M]

open TensorProduct

def Flat.preserves_exactness : Prop :=
∀ ⦃N1 N2 N3 : ModuleCat.{u} R⦄ (l12 : N1 ⟶ N2) (l23 : N2 ⟶ N3)
  (_ : Exact l12 l23),
  Exact ((tensorRight <| ModuleCat.of R M).map l12)
    ((tensorRight <| ModuleCat.of R M).map l23)

def Flat.injective : Prop :=
∀ ⦃N N' : ModuleCat.{u} R⦄ (L : N ⟶ N'),
  Injective L → Injective ((tensorRight (ModuleCat.of R M)).map L)

def Flat.ideal : Prop :=
  ∀ ⦃I : Ideal R⦄, Injective (TensorProduct.lift ((lsmul R M).comp I.subtype))

def Flat.fg_ideal : Prop :=
  ∀ ⦃I : Ideal R⦄ (_ : I.FG), Injective (TensorProduct.lift ((lsmul R M).comp I.subtype))

/-- An `R`-module `M` is flat if for all finitely generated ideals `I` of `R`,
the canonical map `I ⊗ M →ₗ M` is injective. -/
class Flat  : Prop where
  out : ∀ ⦃I : Ideal R⦄ (_ : I.FG), Injective (TensorProduct.lift ((lsmul R M).comp I.subtype))
#align module.flat Module.Flat

namespace Flat

open TensorProduct LinearMap Submodule

instance self (R : Type u) [CommRing R] : Flat R R := ⟨by
  intro I _
  rw [← Equiv.injective_comp (TensorProduct.rid R I).symm.toEquiv]
  convert Subtype.coe_injective using 1
  ext x
  simp⟩
#align module.flat.self Module.Flat.self

end Flat

end Module
