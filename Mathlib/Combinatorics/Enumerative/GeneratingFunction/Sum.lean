/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Combinatorics.Enumerative.GeneratingFunction.Defs
public import Mathlib.Data.Finite.Sum

/-!
# Generating function of a disjoint union

`α ⊕ β` with weight `Sum.elim wα wβ` has GF `genFun wα + genFun wβ`: its weight-fibres
split as the disjoint union of the component fibres.

## Main results

* `sumFiberEquiv`: the fibre splits as a disjoint union.
* `instFiniteFibersSumElim`: finiteness propagates by instance resolution.
* `genFun_sum`: the GF of the disjoint union is the sum of GFs.
-/

@[expose] public section

universe u v w

namespace Combinatorics

variable {α : Type u} {β : Type v} {σ : Type w}

/-- The fiber of a disjoint union splits as the disjoint union of the fibers. -/
def sumFiberEquiv (wα : α → σ →₀ ℕ) (wβ : β → σ →₀ ℕ) (d : σ →₀ ℕ) :
    {x : α ⊕ β // Sum.elim wα wβ x = d} ≃ {a // wα a = d} ⊕ {b // wβ b = d} :=
  Equiv.subtypeSum

instance instFiniteFibersSumElim {wα : α → σ →₀ ℕ} {wβ : β → σ →₀ ℕ}
    [FiniteFibers wα] [FiniteFibers wβ] : FiniteFibers (Sum.elim wα wβ) where
  finite_fiber d := Finite.of_equiv _ (sumFiberEquiv wα wβ d).symm

private theorem card_sumElim_fiber {wα : α → σ →₀ ℕ} {wβ : β → σ →₀ ℕ}
    [FiniteFibers wα] [FiniteFibers wβ] (d : σ →₀ ℕ) :
    Nat.card {x : α ⊕ β // Sum.elim wα wβ x = d}
      = Nat.card {a // wα a = d} + Nat.card {b // wβ b = d} :=
  (Nat.card_congr (sumFiberEquiv wα wβ d)).trans Nat.card_sum

/-- The weighted GF of a disjoint union is the sum of the weighted GFs. -/
@[simp]
theorem genFun_sum {wα : α → σ →₀ ℕ} {wβ : β → σ →₀ ℕ}
    [FiniteFibers wα] [FiniteFibers wβ] :
    genFun (Sum.elim wα wβ) = genFun wα + genFun wβ := by
  ext d
  simp [card_sumElim_fiber]

end Combinatorics
