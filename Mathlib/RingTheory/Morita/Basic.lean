/-
Copyright (c) 2025 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Yunzhou Xie
-/
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Morita equivalence

For two `R`-algebras `A` and `B` are Morita equivalent if the categories of modules over `A` and
`B` are `R`-linearly equivalent. In this file, we prove that Morita equivalence is an equivalence
relation and that isomorphic algebras are Morita equivalent.

# Main definitions

- `MoritaEquivalence R A B`: a structure containing a `R`-linear equivalence of categories between
  the module categories of `A` and `B`.
- `IsMoritaEquivalent R A B`: a predicate asserting that `R`-algebras `A` and `B` are Morita
  equivalent.

## TODO

- For any ring `R`, `R` and `Matₙ(R)` are Morita equivalent.
- Morita equivalence in terms of projective generators.
- Morita equivalence in terms of full idempotents.
- Morita equivalence in terms of existence of an invertible bimodule.
- If `R ≈ S`, then `R` is simple iff `S` is simple.

## References

* [Nathan Jacobson, *Basic Algebra II*][jacobson1989]

## Tags

Morita Equivalence, Category Theory, Noncommutative Ring, Module Theory

-/

universe u₀ u₁ u₂ u₃

open CategoryTheory

variable (R : Type u₀) [CommRing R]

open scoped ModuleCat.Algebra

@[ext]
structure MoritaEquivalence
    (A : Type u₁) [Ring A] [Algebra R A]
    (B : Type u₂) [Ring B] [Algebra R B] where
  eqv : ModuleCat.{max u₁ u₂} A ≌ ModuleCat.{max u₁ u₂} B
  additive : eqv.functor.Additive := by infer_instance
  linear : eqv.functor.Linear R := by infer_instance

namespace MoritaEquivalence

attribute [instance] MoritaEquivalence.additive MoritaEquivalence.linear

/--
For any `R`-algebra `A`, `A` is Morita equivalent to itself.
-/
def refl (A : Type u₁) [Ring A] [Algebra R A] : MoritaEquivalence R A A where
  eqv := CategoryTheory.Equivalence.refl
  additive := CategoryTheory.Functor.instAdditiveId
  linear := CategoryTheory.Functor.instLinearId

/--
For any `R`-algebras `A` and `B`, if `A` is Morita equivalent to `B`, then `B` is Morita equivalent
to `A`.
-/
def symm {A : Type u₁} [Ring A] [Algebra R A] {B : Type u₂} [Ring B] [Algebra R B]
    (e : MoritaEquivalence R A B) : MoritaEquivalence R B A where
  eqv := e.eqv.symm
  additive := e.eqv.inverse_additive
  linear := e.eqv.inverseLinear R

-- TODO: We have restricted all the rings to the same universe here because of the complication
-- `max u₁ u₂`, `max u₂ u₃` vs `max u₁ u₃`. But if we once we proved the definition of Morita
-- equivalence is equivalent to the existence of a full idempotent element, we can remove this
-- restriction in the universe.
-- Or alternatively, @alreadydone has sketched an argument on how the universe restriction can be
-- removed via a categorical argument,
-- see [here](https://github.com/leanprover-community/mathlib4/pull/20640#discussion_r1912189931)
/--
For any `R`-algebras `A`, `B`, and `C`, if `A` is Morita equivalent to `B` and `B` is Morita
equivalent to `C`, then `A` is Morita equivalent to `C`.
-/
def trans {A B C : Type u₁}
    [Ring A] [Algebra R A] [Ring B] [Algebra R B] [Ring C] [Algebra R C]
    (e : MoritaEquivalence R A B) (e' : MoritaEquivalence R B C) :
    MoritaEquivalence R A C where
  eqv := e.eqv.trans e'.eqv
  additive := Functor.instAdditiveComp e.eqv.functor e'.eqv.functor
  linear := Functor.instLinearComp e.eqv.functor e'.eqv.functor

variable {R} in
/--
Equivalence `R`-algebras are Morita equivalent.
-/
noncomputable def ofAlgEquiv {A : Type u₁} {B : Type u₂}
      [Ring A] [Algebra R A] [Ring B] [Algebra R B] (f : A ≃ₐ[R] B) :
    MoritaEquivalence R A B where
  eqv := ModuleCat.restrictScalarsEquivalenceOfRingEquiv f.symm.toRingEquiv
  linear := ModuleCat.Algebra.restrictScalarsEquivalenceOfRingEquiv_linear f.symm

end MoritaEquivalence

/--
Two rings are Morita equivalent if their module categories are equivalent.
-/
structure IsMoritaEquivalent
    (A : Type u₁) [Ring A] [Algebra R A]
    (B : Type u₂) [Ring B] [Algebra R B] : Prop where
  cond : Nonempty <| MoritaEquivalence R A B

namespace IsMoritaEquivalent

-- variable {A : Type u₁} [Ring R] {B : Type u₂} [Ring B] {C : Type u₃} [Ring T]

lemma refl {A : Type u₁} [Ring A] [Algebra R A] : IsMoritaEquivalent R A A where
  cond := ⟨.refl R A⟩

lemma symm {A : Type u₁} [Ring A] [Algebra R A] {B : Type u₂} [Ring B] [Algebra R B]
    (h : IsMoritaEquivalent R A B) : IsMoritaEquivalent R B A where
  cond := h.cond.map <| .symm R

lemma trans {A B C : Type u₁} [Ring A] [Ring B] [Ring C] [Algebra R A] [Algebra R B] [Algebra R C]
    (h : IsMoritaEquivalent R A B) (h' : IsMoritaEquivalent R B C) :
    IsMoritaEquivalent R A C where
  cond := Nonempty.map2 (.trans R) h.cond h'.cond

lemma of_AlgEquiv {A : Type u₁} [Ring A] [Algebra R A] {B : Type u₂} [Ring B] [Algebra R B]
    (f : A ≃ₐ[R] B) : IsMoritaEquivalent R A B where
  cond := ⟨.ofAlgEquiv f⟩

end IsMoritaEquivalent
