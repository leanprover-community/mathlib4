/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.Prod
public import Mathlib.LinearAlgebra.AffineSpace.Combination
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap

/-!
# Modules are convex spaces

This file shows that every module over ordered coefficients is a convex space.

## Main declarations

* `ConvexSpace.ofModule`: A semimodule space over a semiring is a convex space.
* `convexSpaceSelf`: A semiring is a convex space over itself.
* `IsModuleConvexSpace`: Predicate for a convex space and module structures to be compatible.
-/

public section

namespace Convexity
variable {R M N I : Type*} [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- Any semimodule over an ordered semiring is a convex space.

This is not an instance because it creates a diamond with structural instances such as
`ConvexSpace R X → ConvexSpace R Y → ConvexSpace R (X × Y)` because
`(∑ i, f i).fst = ∑ i, (f i).fst` isn't defeq, ultimately because `Finset.sum` isn't a field of
`AddCommMonoid` but derived from them through recursion. -/
@[expose, implicit_reducible]
def ConvexSpace.ofModule : ConvexSpace R M where
  sConvexComb w := w.weights.sum fun m r ↦ r • m
  sConvexComb_single := by simp
  assoc := by
    simp [Finsupp.sum_mapDomain_index, add_smul, Finsupp.sum_sum_index, Finsupp.sum_smul_index,
      mul_smul, Finsupp.smul_sum]

instance convexSpaceSelf : ConvexSpace R R := .ofModule

variable (R M) [ConvexSpace R M] in
/-- Typeclass for a convex space structure on a module to be given by weighted sums. -/
class IsModuleConvexSpace : Prop where
  sConvexComb_eq_sum (w : StdSimplex R M) : w.sConvexComb = w.weights.sum fun m r ↦ r • m

export IsModuleConvexSpace (sConvexComb_eq_sum)
attribute [simp] sConvexComb_eq_sum

@[deprecated (since := "2026-04-03")]
alias _root_.convexCombination_eq_sum := sConvexComb_eq_sum

attribute [local instance] ConvexSpace.ofModule in
protected lemma IsModuleConvexSpace.ofModule : IsModuleConvexSpace R M where
  sConvexComb_eq_sum _ := rfl

instance isModuleConvexSpace_self : IsModuleConvexSpace R R := .ofModule

section IsModuleConvexSpace
variable [ConvexSpace R M] [IsModuleConvexSpace R M]

/-- `iConvexComb` in a module can be expressed as a sum. -/
@[simp]
lemma iConvexComb_eq_sum (w : StdSimplex R I) (f : I → M) :
    w.iConvexComb f = w.weights.sum fun i r ↦ r • f i := by
  simp [iConvexComb, sConvexComb_eq_sum, Finsupp.sum_mapDomain_index, add_smul]

/-- `convexCombPair` in a module can be expressed as a sum. -/
@[simp]
lemma convexCombPair_eq_sum (a b : R) (ha hb hab) (x y : M) :
    convexCombPair a b ha hb hab x y = a • x + b • y := by
  classical simp [convexCombPair, sConvexComb_eq_sum, Finsupp.sum_add_index, add_smul]

instance [ConvexSpace R N] [IsModuleConvexSpace R N] : IsModuleConvexSpace R (M × N) where
  sConvexComb_eq_sum w := by ext <;> simp [Finsupp.sum, Prod.fst_sum, Prod.snd_sum]

instance {ι : Type*} {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    [∀ i, ConvexSpace R (M i)] [∀ i, IsModuleConvexSpace R (M i)] :
    IsModuleConvexSpace R (∀ i, M i) where
  sConvexComb_eq_sum w := by ext; simp [Finsupp.sum]

instance {ι : Type*} : IsModuleConvexSpace R (ι →₀ M) where
  sConvexComb_eq_sum w := by ext; simp [Finsupp.sum]

end IsModuleConvexSpace

variable (R I) in
lemma StdSimplex.isAffineMap_weights : IsAffineMap R (weights (R := R) (M := I)) where
  map_sConvexComb s := by simp [sConvexComb_eq_sum, Finsupp.sum_mapDomain_index, add_smul]

end Convexity
