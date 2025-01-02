/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Data.ENNReal.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Algebra.Equiv.TransferInstance

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
structure WithLp (_p : ℝ≥0∞) (V : Type uV) : Type uV where
  val: V

variable (p : ℝ≥0∞) (K : Type uK) (K' : Type uK') (V : Type uV)

namespace WithLp

/-- The canonical equivalence between `WithLp p V` and `V`. This should always be used to convert
back and forth between the representations. -/
protected def equiv : WithLp p V ≃ V := ⟨(·.val),(⟨·⟩),fun _ => rfl,fun _ => rfl⟩

@[ext]
lemma ext (x y : WithLp p V) (h: WithLp.equiv p V x = WithLp.equiv p V y) : x = y := by
  cases x; cases y; simpa

instance instNontrivial [Nontrivial V] : Nontrivial (WithLp p V) := (WithLp.equiv p V).nontrivial
instance instUnique [Unique V] : Unique (WithLp p V) := (WithLp.equiv p V).unique
instance instInhabited [Inhabited V] : Inhabited (WithLp p V) := (WithLp.equiv p V).inhabited

variable [Semiring K] [Semiring K'] [AddCommGroup V]

/-! `WithLp p V` inherits various module-adjacent structures from `V`. -/

instance instAddCommGroup : AddCommGroup (WithLp p V) := (WithLp.equiv p V).addCommGroup

/-- `WithLp.equiv` as an additive isomorphism. -/
protected def addEquiv : WithLp p V ≃+ V := {WithLp.equiv p V with map_add' _ _ := rfl}

@[simp]
lemma addEquiv_apply : ⇑(WithLp.addEquiv p V) = ⇑(WithLp.equiv p V) := rfl

@[simp]
lemma addEquiv_symm : ⇑(WithLp.addEquiv p V).symm = ⇑(WithLp.equiv p V).symm := rfl

instance instModule [Module K V] : Module K (WithLp p V) :=
  (WithLp.addEquiv p V).module K

/-- `WithLp.equiv` as a linear equivalence. -/
protected def linearEquiv [Module K V] : (WithLp p V) ≃ₗ[K] V :=
  {WithLp.addEquiv p V with map_smul' _ _ := rfl}

@[simp]
lemma linearEquiv_apply [Module K V] : ⇑(WithLp.linearEquiv p K V) = ⇑(WithLp.equiv p V) := rfl

@[simp]
lemma linearEquiv_symm_apply [Module K V] : ⇑(WithLp.linearEquiv p K V).symm =
    ⇑(WithLp.equiv p V).symm :=
  rfl

instance instIsScalarTower [SMul K K'] [Module K V] [Module K' V] [IsScalarTower K K' V] :
    IsScalarTower K K' (WithLp p V) :=
  LinearEquiv.isScalarTower K' (WithLp.linearEquiv p K V)

instance instSMulCommClass [Module K V] [Module K' V] [SMulCommClass K K' V] :
    SMulCommClass K K' (WithLp p V) where
  smul_comm a b c := by simp [Equiv.smul_def]; exact smul_comm _ _ _

instance instModuleFinite [Module K V] [Module.Finite K V] : Module.Finite K (WithLp p V) :=
  Module.Finite.equiv (WithLp.linearEquiv p K V).symm

variable {K V}
variable [Module K V]
variable (c : K) (x y : WithLp p V) (x' y' : V)

@[simp]
theorem equiv_zero : WithLp.equiv p V 0 = 0 :=
  rfl
/-! `WithLp.equiv` preserves the module structure. -/


@[simp]
theorem equiv_symm_zero : (WithLp.equiv p V).symm 0 = 0 :=
  rfl

@[simp]
theorem equiv_add : WithLp.equiv p V (x + y) = WithLp.equiv p V x + WithLp.equiv p V y :=
  rfl

@[simp]
theorem equiv_symm_add :
    (WithLp.equiv p V).symm (x' + y') = (WithLp.equiv p V).symm x' + (WithLp.equiv p V).symm y' :=
  rfl

@[simp]
theorem equiv_sub : WithLp.equiv p V (x - y) = WithLp.equiv p V x - WithLp.equiv p V y :=
  rfl

@[simp]
theorem equiv_symm_sub :
    (WithLp.equiv p V).symm (x' - y') = (WithLp.equiv p V).symm x' - (WithLp.equiv p V).symm y' :=
  rfl

@[simp]
theorem equiv_neg : WithLp.equiv p V (-x) = -WithLp.equiv p V x :=
  rfl

@[simp]
theorem equiv_symm_neg : (WithLp.equiv p V).symm (-x') = -(WithLp.equiv p V).symm x' :=
  rfl

@[simp]
theorem equiv_smul : WithLp.equiv p V (c • x) = c • WithLp.equiv p V x :=
  rfl

@[simp]
theorem equiv_symm_smul : (WithLp.equiv p V).symm (c • x') = c • (WithLp.equiv p V).symm x' :=
  rfl

variable (K V)


end WithLp
