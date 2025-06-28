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
* `WithLp.toLp`: the canonical equivalence between `V` and `WithLp p V`.
* `WithLp.ofLp`: the canonical equivalence between `WithLp p V` and `V`.
* `WithLp.toLpLinear p K V`: the canonical `K`-module isomorphism between `V` and `WithLp p V`.

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

variable {V} in
/-- The canonical equivalence between `V` and `WithLp p V`. This should always be used to convert
back and forth between the representations. -/
def toLp : V ≃ WithLp p V := .refl _

variable {p V} in
/-- The canonical equivalence between `WithLp p V` and `V`. This should always be used to convert
back and forth between the representations. -/
def ofLp : WithLp p V ≃ V := .refl _

/-- The canonical equivalence between `WithLp p V` and `V`. This should always be used to convert
back and forth between the representations. -/
@[deprecated WithLp.ofLp (since := "2025-06-08")]
protected def equiv : WithLp p V ≃ V := Equiv.refl _

/-- A recursor for `WithLp p V`, that reduces to the underlying space `V`.

This unfortunately cannot be registered with `cases_eliminator`, but it can still be used as
`cases v using WithLp.rec with | toLp v =>`. -/
@[elab_as_elim]
protected def rec {motive : WithLp p V → Sort*} (toLp : ∀ v : V, motive (toLp p v)) :
    ∀ v, motive v :=
  fun v => toLp (ofLp v)

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

@[simp] lemma symm_toLp : (@toLp p V).symm = ofLp := rfl
@[simp] lemma symm_ofLp : (@ofLp p V).symm = toLp p := rfl

@[simp] lemma ofLp_toLp (x : V) : ofLp (toLp p x) = x := rfl
@[simp] lemma toLp_ofLp (x : WithLp p V) : toLp p (ofLp x) = x := rfl

section AddCommGroup
variable [AddCommGroup V]

@[simp] lemma toLp_zero : toLp p (0 : V) = 0 := rfl
@[simp] lemma ofLp_zero : ofLp (0 : WithLp p V) = 0 := rfl

@[simp] lemma toLp_add (x y : V) : toLp p (x + y) = toLp p x + toLp p y := rfl
@[simp] lemma ofLp_add (x y : WithLp p V) : ofLp (x + y) = ofLp x + ofLp y := rfl

@[simp] lemma toLp_sub (x y : V) : toLp p (x - y) = toLp p x - toLp p y := rfl
@[simp] lemma ofLp_sub (x y : WithLp p V) : ofLp (x - y) = ofLp x - ofLp y := rfl

@[simp] lemma toLp_neg (x : V) : toLp p (-x) = -toLp p x := rfl
@[simp] lemma ofLp_neg (x : WithLp p V) : ofLp (-x) = -ofLp x := rfl

@[simp] lemma toLp_eq_zero {x : V} : toLp p x = 0 ↔ x = 0 := .rfl
@[simp] lemma ofLp_eq_zero {x : WithLp p V} : ofLp x = 0 ↔ x = 0 := .rfl

end AddCommGroup

@[simp] lemma toLp_smul [SMul K V] (c : K) (x : V) : toLp p (c • x) = c • (toLp p x) := rfl
@[simp] lemma ofLp_smul [SMul K V] (c : K) (x : WithLp p V) : ofLp (c • x) = c • ofLp x := rfl

section equiv

set_option linter.deprecated false in
@[deprecated ofLp_zero (since := "2025-06-08")]
theorem equiv_zero [AddCommGroup V] : WithLp.equiv p V 0 = 0 :=
  rfl

set_option linter.deprecated false in
@[deprecated toLp_zero (since := "2025-06-08")]
theorem equiv_symm_zero [AddCommGroup V] : (WithLp.equiv p V).symm 0 = 0 :=
  rfl

set_option linter.deprecated false in
@[deprecated toLp_eq_zero (since := "2025-06-08")]
theorem equiv_symm_eq_zero_iff [AddCommGroup V] {x : V} :
    (WithLp.equiv p V).symm x = 0 ↔ x = 0 := Iff.rfl

set_option linter.deprecated false in
@[deprecated ofLp_eq_zero (since := "2025-06-08")]
theorem equiv_eq_zero_iff [AddCommGroup V] {x : WithLp p V} :
    WithLp.equiv p V x = 0 ↔ x = 0 := Iff.rfl

set_option linter.deprecated false in
@[deprecated ofLp_add (since := "2025-06-08")]
theorem equiv_add [AddCommGroup V] (x y : WithLp p V) :
    WithLp.equiv p V (x + y) = WithLp.equiv p V x + WithLp.equiv p V y :=
  rfl

set_option linter.deprecated false in
@[deprecated toLp_add (since := "2025-06-08")]
theorem equiv_symm_add [AddCommGroup V] (x' y' : V) :
    (WithLp.equiv p V).symm (x' + y') = (WithLp.equiv p V).symm x' + (WithLp.equiv p V).symm y' :=
  rfl

set_option linter.deprecated false in
@[deprecated ofLp_sub (since := "2025-06-08")]
theorem equiv_sub [AddCommGroup V] (x y : WithLp p V) :
    WithLp.equiv p V (x - y) = WithLp.equiv p V x - WithLp.equiv p V y :=
  rfl

set_option linter.deprecated false in
@[deprecated toLp_sub (since := "2025-06-08")]
theorem equiv_symm_sub [AddCommGroup V] (x' y' : V) :
    (WithLp.equiv p V).symm (x' - y') = (WithLp.equiv p V).symm x' - (WithLp.equiv p V).symm y' :=
  rfl

set_option linter.deprecated false in
@[deprecated ofLp_neg (since := "2025-06-08")]
theorem equiv_neg [AddCommGroup V] (x : WithLp p V) : WithLp.equiv p V (-x) = -WithLp.equiv p V x :=
  rfl

set_option linter.deprecated false in
@[deprecated toLp_neg (since := "2025-06-08")]
theorem equiv_symm_neg [AddCommGroup V] (x' : V):
    (WithLp.equiv p V).symm (-x') = -(WithLp.equiv p V).symm x' :=
  rfl

set_option linter.deprecated false in
@[deprecated ofLp_smul (since := "2025-06-08")]
theorem equiv_smul [SMul K V] (c : K) (x : WithLp p V) :
    WithLp.equiv p V (c • x) = c • WithLp.equiv p V x :=
  rfl

set_option linter.deprecated false in
@[deprecated toLp_smul (since := "2025-06-08")]
theorem equiv_symm_smul [SMul K V] (c : K) (x' : V) :
    (WithLp.equiv p V).symm (c • x') = c • (WithLp.equiv p V).symm x' :=
  rfl

end equiv

variable (K V)

/-- `WithLp.ofLp` as a linear equivalence. -/
@[simps -fullyApplied]
def ofLpLinearEquiv [Semiring K] [AddCommGroup V] [Module K V] : WithLp p V ≃ₗ[K] V  where
  __ := LinearEquiv.refl _ _
  toFun := WithLp.ofLp
  invFun := WithLp.toLp p

/-- `WithLp.equiv` as a linear equivalence. -/
@[deprecated WithLp.ofLpLinearEquiv (since := "2025-06-08")]
protected alias linearEquiv := ofLpLinearEquiv

end WithLp
