/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Data.ENNReal.Basic
import Mathlib.RingTheory.Finiteness

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
set_option linter.uppercaseLean3 false

universe uK uK' uV

/-- A type synonym for the given `V`, associated with the L`p` norm. Note that by default this just
forgets the norm structure on `V`; it is up to downstream users to implement the L`p` norm (for
instance, on `Prod` and finite `Pi` types). -/
@[nolint unusedArguments]
def WithLp (_p : ℝ≥0∞) (V : Type uV) : Type uV := V

variable (p : ℝ≥0∞) (K : Type uK) (K' : Type uK')  (V : Type uV)

namespace WithLp

/-- The canonical equivalence between `WithLp p V` and `V`. This should always be used to convert
back and forth between the representations. -/
protected def equiv : WithLp p V ≃ V := Equiv.refl _

instance instNontrivial [Nontrivial V] : Nontrivial (WithLp p V) := ‹Nontrivial V›
instance instUnique [Unique V] : Unique (WithLp p V) := ‹Unique V›

variable [Semiring K] [Semiring K'] [AddCommGroup V]

/-! `WithLp p V` inherits various module-adjacent structures from `V`. -/

instance instAddCommGroup : AddCommGroup (WithLp p V) := ‹AddCommGroup V›
instance instModule [Module K V] : Module K (WithLp p V) := ‹Module K V›

instance instIsScalarTower [SMul K K'] [Module K V] [Module K' V] [IsScalarTower K K' V] :
    IsScalarTower K K' (WithLp p V) :=
  ‹IsScalarTower K K' V›

instance instSMulCommClass [Module K V] [Module K' V] [SMulCommClass K K' V] :
    SMulCommClass K K' (WithLp p V) :=
  ‹SMulCommClass K K' V›

instance instModuleFinite [Module K V] [Module.Finite K V] : Module.Finite K (WithLp p V) :=
  ‹Module.Finite K V›

variable {K V}
variable [Module K V]
variable (c : K) (x y : WithLp p V) (x' y' : V)

/-! `WithLp.equiv` preserves the module structure. -/

@[simp]
theorem equiv_zero : WithLp.equiv p V 0 = 0 :=
  rfl
#align pi_Lp.equiv_zero WithLp.equiv_zero

@[simp]
theorem equiv_symm_zero : (WithLp.equiv p V).symm 0 = 0 :=
  rfl
#align pi_Lp.equiv_symm_zero WithLp.equiv_symm_zero

@[simp]
theorem equiv_add : WithLp.equiv p V (x + y) = WithLp.equiv p V x + WithLp.equiv p V y :=
  rfl
#align pi_Lp.equiv_add WithLp.equiv_add

@[simp]
theorem equiv_symm_add :
    (WithLp.equiv p V).symm (x' + y') = (WithLp.equiv p V).symm x' + (WithLp.equiv p V).symm y' :=
  rfl
#align pi_Lp.equiv_symm_add WithLp.equiv_symm_add

@[simp]
theorem equiv_sub : WithLp.equiv p V (x - y) = WithLp.equiv p V x - WithLp.equiv p V y :=
  rfl
#align pi_Lp.equiv_sub WithLp.equiv_sub

@[simp]
theorem equiv_symm_sub :
    (WithLp.equiv p V).symm (x' - y') = (WithLp.equiv p V).symm x' - (WithLp.equiv p V).symm y' :=
  rfl
#align pi_Lp.equiv_symm_sub WithLp.equiv_symm_sub

@[simp]
theorem equiv_neg : WithLp.equiv p V (-x) = -WithLp.equiv p V x :=
  rfl
#align pi_Lp.equiv_neg WithLp.equiv_neg

@[simp]
theorem equiv_symm_neg : (WithLp.equiv p V).symm (-x') = -(WithLp.equiv p V).symm x' :=
  rfl
#align pi_Lp.equiv_symm_neg WithLp.equiv_symm_neg

@[simp]
theorem equiv_smul : WithLp.equiv p V (c • x) = c • WithLp.equiv p V x :=
  rfl
#align pi_Lp.equiv_smul WithLp.equiv_smul

@[simp]
theorem equiv_symm_smul : (WithLp.equiv p V).symm (c • x') = c • (WithLp.equiv p V).symm x' :=
  rfl
#align pi_Lp.equiv_symm_smul WithLp.equiv_symm_smul

variable (K V)

/-- `WithLp.equiv` as a linear equivalence. -/
@[simps (config := .asFn)]
protected def linearEquiv : WithLp p V ≃ₗ[K] V :=
  { LinearEquiv.refl _ _ with
    toFun := WithLp.equiv _ _
    invFun := (WithLp.equiv _ _).symm }

end WithLp
