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

- `IsMoritaEquivalent R S`: a predicate asserting that `R` and `S` are Morita equivalent.

## TODO

- For any ring `R`, `R` and `Matₙ(R)` are Morita equivalent.
- Morita equivalence in terms of projective generators.
- Morita equivalence in terms of full idempotents.
- If `R ≈ S`, then `R` is simple iff `S` is simple.

## References

* [Nathan Jacobson, *Basic Algebra II*][jacobson1989]

## Tags

Morita Equivalence, Category Theory, Noncommutative Ring, Module Theory

-/

universe u₁ u₂ u₃

open CategoryTheory

/--
Two rings are Morita equivalent if their module categories are equivalent.
-/
structure IsMoritaEquivalent (R : Type u₁) [Ring R] (S : Type u₂) [Ring S] : Prop where
  cond : Nonempty <| ModuleCat.{max u₁ u₂} R ≌ ModuleCat.{max u₁ u₂} S

namespace IsMoritaEquivalent

variable {R : Type u₁} [Ring R] {S : Type u₂} [Ring S] {T : Type u₃} [Ring T]

lemma refl : IsMoritaEquivalent R R where
  cond := ⟨.refl⟩

lemma symm (h : IsMoritaEquivalent R S) : IsMoritaEquivalent S R where
  cond := h.cond.map .symm

-- TODO: We have restricted universe here, but if we have more Mortia Equivalence in terms full
-- idempotents, we could remove the restriction.
lemma trans {R S T : Type u₁} [Ring R] [Ring S] [Ring T]
    (h : IsMoritaEquivalent R S) (h' : IsMoritaEquivalent S T) :
    IsMoritaEquivalent R T where
  cond := Nonempty.map2 .trans h.cond h'.cond

lemma of_ringEquiv (f : R ≃+* S) : IsMoritaEquivalent R S where
  cond := ⟨ModuleCat.restrictScalarsEquivalenceOfRingEquiv f.symm⟩

end IsMoritaEquivalent
