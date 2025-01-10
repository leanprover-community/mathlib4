/-
Copyright (c) 2025 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Yunzhou Xie
-/
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Morita equivalence

We say that `R` and `S` are Morita equivalent if the categories of modules over `R` and `S` are
equivalent. In this file, we prove that Morita equivalence is an equivalence relation and that
isomorphic rings are Morita equivalent.

# Main definitions

- `MoritaEquivalent R S`: two rings `R` and `S` are Morita equivalent if their module categories
  are equivalent.
- `IsMoritaEquivalent R S`: a predicate asserting that `R` and `S` are Morita equivalent.

## TODO

- For any ring `R`, `R` and `Matₙ(R)` are Morita equivalent.

## References

* [Nathan Jacobson, *Basic Algebra II*][jacobson1989]

## Tags

Morita Equivalence, Category Theory, Noncommutative Ring, Module Theory

-/

universe v u₁ u₂ u₃

open CategoryTheory

/--
Two rings are Morita equivalent if their module categories are equivalent.
-/
structure MoritaEquivalent (R : Type u₁) (S : Type u₂) [Ring R] [Ring S] where
  /-- the underlying equivalence of category -/
  eqv : ModuleCat.{v} R ≌ ModuleCat.{v} S

/--
Two rings are Morita equivalent if their module categories are equivalent.
-/
structure IsMoritaEquivalent (R : Type u₁) (S : Type u₂) [Ring R] [Ring S] : Prop where
  cond : Nonempty <| MoritaEquivalent.{v} R S

namespace MoritaEquivalent

variable {R : Type u₁} [Ring R] {S : Type u₂} [Ring S] {T : Type u₃} [Ring T]

/--
Every ring is Morita equivalent to itself.
-/
@[refl]
def refl : MoritaEquivalent R R where
  eqv := CategoryTheory.Equivalence.refl (C := ModuleCat.{v} R)

/--
If `R` is Morita equivalent to `S`, then `S` is Morita equivalent to `R`.
-/
@[symm]
def symm (e : MoritaEquivalent R S) : MoritaEquivalent S R where
  eqv := e.eqv.symm

/--
If `R` is Morita equivalent to `S` and `S` is Morita equivalent to `T`, then `R` is Morita
equivalent to `T`.
-/
@[trans]
def trans (e : MoritaEquivalent R S) (e' : MoritaEquivalent S T) :
    MoritaEquivalent R T where
  eqv := e.eqv.trans e'.eqv

/--
If `R` is isomorphic to `S` as rings, then `R` is Morita equivalent to `S`.
-/
noncomputable def ofRingEquiv (f : R ≃+* S) : MoritaEquivalent R S where
  eqv := ModuleCat.restrictScalarsEquivalenceOfRingEquiv f.symm

end MoritaEquivalent

namespace IsMoritaEquivalent

variable {R : Type u₁} [Ring R] {S : Type u₂} [Ring S] {T : Type u₃} [Ring T]

lemma refl : IsMoritaEquivalent R R where
  cond := ⟨.refl⟩

lemma symm (h : IsMoritaEquivalent.{v} R S) : IsMoritaEquivalent.{v} S R where
  cond := h.cond.map .symm

lemma trans (h : IsMoritaEquivalent.{v} R S) (h' : IsMoritaEquivalent.{v} S T) :
    IsMoritaEquivalent.{v} R T where
  cond := Nonempty.map2 .trans h.cond h'.cond

lemma of_ringEquiv (f : R ≃+* S) : IsMoritaEquivalent R S where
  cond := ⟨.ofRingEquiv f⟩

end IsMoritaEquivalent
