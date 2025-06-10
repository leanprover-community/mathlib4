/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Data.ENNReal.Basic
import Mathlib.RingTheory.Finiteness.Defs

/-! # The `WithLp` type synonym

`WithLp p V` is a copy of `V` with exactly the same vector space structure, but with the Lp norm
instead of any existing norm on `V`; recall that by default `ι → R` and `R × R` are equipped with
a norm defined as the supremum of the norms of their components.

This file defines the vector space structure for all types `V`; the norm structure is built for
different specializations of `V` in downstream files.

Note that this should not be used for infinite products, as in these cases the "right" Lp spaces is
not the same as the direct product of the spaces. See the docstring in `Mathlib/Analysis/PiLp` for
more details.

## Main definitions

* `WithLp p V`: a copy of `V` to be equipped with an L`p` norm.
* `WithLp.equiv p V`: the canonical equivalence between `WithLp p V` and `V`.
* `WithLp.linearEquiv p K V`: the canonical `K`-module isomorphism between `WithLp p V` and `V`.

## Implementation notes

The pattern here is the same one as is used by `Lex` for order structures; it avoids having a
separate synonym for each type (`ProdLp`, `PiLp`, etc), and allows all the structure-copying code
to be shared.

TODO: is it safe to copy across the topology and uniform space structure too for all reasonable
choices of `V`?
-/


open scoped ENNReal

universe uK uK' uV

/-- A type synonym for the given `V`, associated with the L`p` norm. Note that by default this just
forgets the norm structure on `V`; it is up to downstream users to implement the L`p` norm (for
instance, on `Prod` and finite `Pi` types). -/
@[nolint unusedArguments]
def WithLp (_p : ℝ≥0∞) (V : Type uV) : Type uV := V

variable (p : ℝ≥0∞) (K : Type uK) (K' : Type uK') (V : Type uV)

namespace WithLp

/-- The canonical equivalence between `WithLp p V` and `V`. This should always be used to convert
back and forth between the representations. -/
protected def equiv : WithLp p V ≃ V := Equiv.refl _

/-- A recursor for `WithLp p V`, that reduces to the underlying space `V`.

This unfortunately cannot be registered with `cases_eliminator`, but it can still be used as
`cases v using WithLp.rec with | toLp v =>`. -/
@[elab_as_elim]
protected def rec {motive : WithLp p V → Sort*}
    (toLp : ∀ v : V, motive ((WithLp.equiv p _).symm v)) :
    ∀ v, motive v :=
  fun v => toLp ((WithLp.equiv p _) v)

/-! `WithLp p V` inherits various module-adjacent structures from `V`. -/

instance instNontrivial [Nontrivial V] : Nontrivial (WithLp p V) := ‹Nontrivial V›
instance instUnique [Unique V] : Unique (WithLp p V) := ‹Unique V›
instance instDecidableEq [DecidableEq V] : DecidableEq (WithLp p V) := ‹DecidableEq V›

instance instAddCommGroup [AddCommGroup V] : AddCommGroup (WithLp p V) := ‹AddCommGroup V›
@[to_additive] instance instSMul [SMul K V] : SMul K (WithLp p V) := ‹SMul K V›
@[to_additive] instance instMulAction [Monoid K] [MulAction K V] : MulAction K V := ‹MulAction K V›
instance instDistribMulAction [Monoid K] [AddCommGroup V] [DistribMulAction K V] :
    DistribMulAction K (WithLp p V) := ‹DistribMulAction K V›
instance instModule [Semiring K] [AddCommGroup V] [Module K V] : Module K (WithLp p V) :=
  ‹Module K V›

@[to_additive]
instance instIsScalarTower [SMul K K'] [SMul K V] [SMul K' V] [IsScalarTower K K' V] :
    IsScalarTower K K' (WithLp p V) :=
  ‹IsScalarTower K K' V›

@[to_additive]
instance instSMulCommClass [SMul K V] [SMul K' V] [SMulCommClass K K' V] :
    SMulCommClass K K' (WithLp p V) :=
  ‹SMulCommClass K K' V›

instance instModuleFinite
    [Semiring K] [AddCommGroup V] [Module K V] [Module.Finite K V] :
    Module.Finite K (WithLp p V) :=
  ‹Module.Finite K V›

variable {K V}

/-! `WithLp.equiv` preserves the module structure. -/

@[simp]
theorem equiv_zero [AddCommGroup V] : WithLp.equiv p V 0 = 0 :=
  rfl

@[simp]
theorem equiv_symm_zero [AddCommGroup V] : (WithLp.equiv p V).symm 0 = 0 :=
  rfl

@[simp]
theorem equiv_symm_eq_zero_iff [AddCommGroup V] {x : V} :
    (WithLp.equiv p V).symm x = 0 ↔ x = 0 := Iff.rfl

@[simp]
theorem equiv_eq_zero_iff [AddCommGroup V] {x : WithLp p V} :
    WithLp.equiv p V x = 0 ↔ x = 0 := Iff.rfl

@[simp]
theorem equiv_add [AddCommGroup V] (x y : WithLp p V) :
    WithLp.equiv p V (x + y) = WithLp.equiv p V x + WithLp.equiv p V y :=
  rfl

@[simp]
theorem equiv_symm_add [AddCommGroup V] (x' y' : V) :
    (WithLp.equiv p V).symm (x' + y') = (WithLp.equiv p V).symm x' + (WithLp.equiv p V).symm y' :=
  rfl

@[simp]
theorem equiv_sub [AddCommGroup V] (x y : WithLp p V) :
    WithLp.equiv p V (x - y) = WithLp.equiv p V x - WithLp.equiv p V y :=
  rfl

@[simp]
theorem equiv_symm_sub [AddCommGroup V] (x' y' : V) :
    (WithLp.equiv p V).symm (x' - y') = (WithLp.equiv p V).symm x' - (WithLp.equiv p V).symm y' :=
  rfl

@[simp]
theorem equiv_neg [AddCommGroup V] (x : WithLp p V) : WithLp.equiv p V (-x) = -WithLp.equiv p V x :=
  rfl

@[simp]
theorem equiv_symm_neg [AddCommGroup V] (x' : V):
    (WithLp.equiv p V).symm (-x') = -(WithLp.equiv p V).symm x' :=
  rfl

@[simp]
theorem equiv_smul [SMul K V] (c : K) (x : WithLp p V) :
    WithLp.equiv p V (c • x) = c • WithLp.equiv p V x :=
  rfl

@[simp]
theorem equiv_symm_smul [SMul K V] (c : K) (x' : V) :
    (WithLp.equiv p V).symm (c • x') = c • (WithLp.equiv p V).symm x' :=
  rfl

variable (K V)

/-- `WithLp.equiv` as a linear equivalence. -/
@[simps -fullyApplied]
protected def linearEquiv [Semiring K] [AddCommGroup V] [Module K V] : WithLp p V ≃ₗ[K] V :=
  { LinearEquiv.refl _ _ with
    toFun := WithLp.equiv _ _
    invFun := (WithLp.equiv _ _).symm }

end WithLp
