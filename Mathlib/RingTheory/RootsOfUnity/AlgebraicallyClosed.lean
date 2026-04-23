/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import Mathlib.FieldTheory.SeparableClosure
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.Tactic.ArithMult.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike

/-!
# Instances for HasEnoughRootsOfUnity

We provide an instance for `HasEnoughRootsOfUnity F n` when `F` is a separably closed field
and `n` is not divisible by the characteristic. In particular, when `F` has characteristic zero,
this hold for all `n ≠ 0`.
-/

@[expose] public section

variable (F : Type*) [Field F] (n k : ℕ) [NeZero (n : F)]

namespace IsSepClosed

variable [IsSepClosed F]

/-- A separably closed field `F` satisfies `HasEnoughRootsOfUnity F n` for all `n`
that are not divisible by the characteristic of `F`. -/
instance hasEnoughRootsOfUnity : HasEnoughRootsOfUnity F n where
  prim := by
    have : NeZero n := .of_neZero_natCast F
    have := isCyclotomicExtension {n} F fun _ h _ ↦ Set.mem_singleton_iff.mp h ▸ ‹NeZero (n : F)›
    exact IsCyclotomicExtension.exists_isPrimitiveRoot (S := {n}) F _ rfl (NeZero.ne _)
  cyc :=
    have : NeZero n := .of_neZero_natCast F
    rootsOfUnity.isCyclic F n

instance hasEnoughRootsOfUnity_pow : HasEnoughRootsOfUnity F (n ^ k) :=
  have : NeZero ((n ^ k : ℕ) : F) := by exact_mod_cast ‹NeZero (n : F)›.pow
  inferInstance

end IsSepClosed

namespace AlgebraicClosure

instance hasEnoughRootsOfUnity : HasEnoughRootsOfUnity (AlgebraicClosure F) n :=
  have : NeZero (n : AlgebraicClosure F) :=
    ‹NeZero (n : F)›.of_injective (algebraMap F (AlgebraicClosure F)).injective
  inferInstance

instance hasEnoughRootsOfUnity_pow : HasEnoughRootsOfUnity (AlgebraicClosure F) (n ^ k) :=
  have : NeZero (n : AlgebraicClosure F) :=
    ‹NeZero (n : F)›.of_injective (algebraMap F (AlgebraicClosure F)).injective
  inferInstance

end AlgebraicClosure

namespace SeparableClosure

instance hasEnoughRootsOfUnity : HasEnoughRootsOfUnity (SeparableClosure F) n :=
  have : NeZero (n : SeparableClosure F) :=
    ‹NeZero (n : F)›.of_injective (algebraMap F (SeparableClosure F)).injective
  inferInstance

instance hasEnoughRootsOfUnity_pow : HasEnoughRootsOfUnity (SeparableClosure F) (n ^ k) :=
  have : NeZero (n : SeparableClosure F) :=
    ‹NeZero (n : F)›.of_injective (algebraMap F (SeparableClosure F)).injective
  inferInstance

end SeparableClosure
