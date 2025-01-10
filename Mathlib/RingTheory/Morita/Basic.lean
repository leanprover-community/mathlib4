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

- `MoritaEquivalence R S`: two rings `R` and `S` are Morita equivalent if their module categories
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
def MoritaEquivalence (R : Type u₁) (S : Type u₂) [Ring R] [Ring S] :=
  ModuleCat.{v} R ≌ ModuleCat.{v} S

/--
Two rings are Morita equivalent if their module categories are equivalent.
-/
structure IsMoritaEquivalent (R : Type u₁) [Ring R] (S : Type u₂) [Ring S] : Prop where
  cond : Nonempty <| MoritaEquivalence.{max u₁ u₂} R S

namespace MoritaEquivalence

variable {R : Type u₁} [Ring R] {S : Type u₂} [Ring S] {T : Type u₃} [Ring T]

/--
Every ring is Morita equivalent to itself.
-/
def refl : MoritaEquivalence R R :=
    CategoryTheory.Equivalence.refl (C := ModuleCat.{v} R)

/--
If `R` is Morita equivalent to `S`, then `S` is Morita equivalent to `R`.
-/
def symm (e : MoritaEquivalence R S) : MoritaEquivalence S R :=
    CategoryTheory.Equivalence.symm e

/--
If `R` is Morita equivalent to `S` and `S` is Morita equivalent to `T`, then `R` is Morita
equivalent to `T`.
-/
def trans (e : MoritaEquivalence R S) (e' : MoritaEquivalence S T) : MoritaEquivalence R T :=
  CategoryTheory.Equivalence.trans e e'

/--
If `R` is isomorphic to `S` as rings, then `R` is Morita equivalent to `S`.
-/
noncomputable def ofRingEquiv (f : R ≃+* S) : MoritaEquivalence R S :=
  ModuleCat.restrictScalarsEquivalenceOfRingEquiv f.symm

end MoritaEquivalence

namespace IsMoritaEquivalent

variable {R : Type u₁} [Ring R] {S : Type u₂} [Ring S] {T : Type u₃} [Ring T]

lemma refl : IsMoritaEquivalent R R where
  cond := ⟨.refl⟩

lemma symm (h : IsMoritaEquivalent R S) : IsMoritaEquivalent S R where
  cond := h.cond.map .symm

lemma trans (h : IsMoritaEquivalent R S) (h' : IsMoritaEquivalent S T) :
    IsMoritaEquivalent R T where
  cond := Nonempty.map2 (fun e e' ↦ MoritaEquivalence.trans e e') h.cond h'.cond

lemma of_ringEquiv (f : R ≃+* S) : IsMoritaEquivalent R S where
  cond := ⟨.ofRingEquiv f⟩

end IsMoritaEquivalent
