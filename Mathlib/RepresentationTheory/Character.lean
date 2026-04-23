/-
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
module

public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.GroupWithZero.Invertible
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
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
# Characters of representations

This file introduces characters of representation and proves basic lemmas about how characters
behave under various operations on representations.

A key result is the orthogonality of characters for irreducible representations of finite group
over an algebraically closed field whose characteristic doesn't divide the order of the group. It
is the theorem `char_orthonormal`

## Implementation notes

Irreducible representations are implemented categorically, using the `CategoryTheory.Simple` class
defined in `Mathlib/CategoryTheory/Simple.lean`

## TODO
* Once we have the monoidal closed structure on `FdRep k G` and a better API for the rigid
  structure, `char_dual` and `char_linHom` should probably be stated
  in terms of `Vᘁ` and `ihom V W`.
-/

@[expose] public section


noncomputable section

universe u

open CategoryTheory LinearMap CategoryTheory.MonoidalCategory Representation Module

variable {k : Type u} [Field k]

namespace FDRep

section Monoid

variable {G : Type u} [Monoid G]

/-- The character of a representation `V : FDRep k G` is the function associating to `g : G` the
trace of the linear map `V.ρ g`. -/
def character (V : FDRep k G) (g : G) :=
  LinearMap.trace k V (V.ρ g)

theorem char_mul_comm (V : FDRep k G) (g : G) (h : G) :
    V.character (h * g) = V.character (g * h) := by simp only [trace_mul_comm, character, map_mul]

@[simp]
theorem char_one (V : FDRep k G) : V.character 1 = Module.finrank k V := by
  simp only [character, map_one, trace_one]

/-- The character is multiplicative under the tensor product. -/
@[simp]
theorem char_tensor (V W : FDRep k G) : (V ⊗ W).character = V.character * W.character := by
  ext g; convert trace_tensorProduct' (V.ρ g) (W.ρ g)

/-- The character of isomorphic representations is the same. -/
theorem char_iso {V W : FDRep k G} (i : V ≅ W) : V.character = W.character := by
  ext g
  simp only [character, FDRep.Iso.conj_ρ i]
  exact (trace_conj' (V.ρ g) _).symm

end Monoid

section Group

variable {G : Type u} [Group G]

/-- The character of a representation is constant on conjugacy classes. -/
@[simp]
theorem char_conj (V : FDRep k G) (g : G) (h : G) : V.character (h * g * h⁻¹) = V.character g := by
  rw [char_mul_comm, inv_mul_cancel_left]

@[simp]
theorem char_dual (V : FDRep k G) (g : G) : (of (dual V.ρ)).character g = V.character g⁻¹ :=
  trace_transpose' (V.ρ g⁻¹)

@[simp]
theorem char_linHom (V W : FDRep k G) (g : G) :
    (of (linHom V.ρ W.ρ)).character g = V.character g⁻¹ * W.character g := by
  rw [← char_iso (dualTensorIsoLinHom _ _), char_tensor, Pi.mul_apply, char_dual]

variable [Fintype G] [Invertible (Fintype.card G : k)]

theorem average_char_eq_finrank_invariants (V : FDRep k G) :
    ⅟(Fintype.card G : k) • ∑ g : G, V.character g = finrank k (invariants V.ρ) := by
  rw [← (isProj_averageMap V.ρ).trace]
  simp [character, GroupAlgebra.average, _root_.map_sum]

/--
If `V` are `W` are finite-dimensional representations of a finite group, then the
scalar product of their characters is equal to the dimension of the space of
equivariant maps from `V` to `W`.
-/
theorem scalar_product_char_eq_finrank_equivariant (V W : FDRep k G) :
    ⅟(Fintype.card G : k) • ∑ g : G, W.character g * V.character g⁻¹ =
    Module.finrank k (V ⟶ W) := by
  conv_lhs => congr; rfl; congr; rfl; intro _; rw [mul_comm, ← FDRep.char_linHom]
  -- The scalar product is the character of `Hom(V, W).`
  rw [FDRep.average_char_eq_finrank_invariants, ← LinearEquiv.finrank_eq
    (Representation.linHom.invariantsEquivFDRepHom V W), of_ρ']
  -- The average over the group of the character of a representation equals the dimension of the
  -- space of invariants, and the space of invariants of `Hom(W, V)` is the subspace of
  --`G`-equivariant linear maps, `Hom_G(W, V)`.

end Group

section Orthogonality

variable {G : Type u} [Group G] [IsAlgClosed k]

variable [Fintype G] [Invertible (Fintype.card G : k)]

open scoped Classical in
/-- Orthogonality of characters for irreducible representations of finite group over an
algebraically closed field whose characteristic doesn't divide the order of the group. -/
theorem char_orthonormal (V W : FDRep k G) [Simple V] [Simple W] :
    ⅟(Fintype.card G : k) • ∑ g : G, V.character g * W.character g⁻¹ =
      if Nonempty (V ≅ W) then ↑1 else ↑0 := by
  rw [scalar_product_char_eq_finrank_equivariant]
  -- The scalar products of the characters is equal to the dimension of the space of
  -- equivariant maps `W ⟶ V`.
  rw_mod_cast [finrank_hom_simple_simple W V, Iso.nonempty_iso_symm]
  -- By Schur's Lemma, the dimension of `Hom_G(W, V)` is `1` is `V ≅ W` and `0` otherwise.

end Orthogonality

end FDRep

namespace Representation

section Monoid

variable {G k V W : Type*} [Monoid G] [Field k] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
  (ρ : Representation k G V) (σ : Representation k G W)

/-- The character of a representation `ρ : Representation k G V` is the function associating to
`g : G` the trace of the linear map `ρ g`. -/
def character (g : G) :=
  LinearMap.trace k V (ρ g)

omit [FiniteDimensional k V] in
theorem char_mul_comm (g : G) (h : G) :
    ρ.character (h * g) = ρ.character (g * h) := by simp only [trace_mul_comm, character, map_mul]

@[simp]
theorem char_one (ρ : Representation k G V) : ρ.character 1 = Module.finrank k V := by
  simp only [character, map_one, trace_one]

/-- The character is multiplicative under the tensor product. -/
@[simp]
theorem char_tensor : (tprod ρ σ).character = ρ.character * σ.character := by
  ext g; convert trace_tensorProduct' (ρ g) (σ g)

omit [FiniteDimensional k V] [FiniteDimensional k W] in
variable {ρ σ} in
/-- The character of isomorphic representations is the same. -/
theorem char_iso (φ : Equiv ρ σ) : ρ.character = σ.character := by
  ext g
  simp [character, ← φ.conj_apply_self]

end Monoid

section Group

variable {G k V W : Type*} [Group G] [Field k] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
  (ρ : Representation k G V) (σ : Representation k G W)

omit [FiniteDimensional k V] in
/-- The character of a representation is constant on conjugacy classes. -/
@[simp]
theorem char_conj (g : G) (h : G) : ρ.character (h * g * h⁻¹) = ρ.character g := by
  rw [char_mul_comm, inv_mul_cancel_left]

@[simp]
theorem char_dual (g : G) : ρ.dual.character g = ρ.character g⁻¹ :=
  trace_transpose' (ρ g⁻¹)

@[simp]
theorem char_linHom (g : G) :
    (linHom ρ σ).character g = ρ.character g⁻¹ * σ.character g := by
  rw [← char_iso (Equiv.dualTensorHom ρ σ), char_tensor, Pi.mul_apply, char_dual]

variable [Fintype G] [Invertible (Nat.card G : k)]

theorem card_inv_mul_sum_char_eq_finrank :
    (Nat.card G : k)⁻¹ * ∑ g : G, ρ.character g = finrank k (invariants ρ) := by
  have : Invertible (Fintype.card G : k) := by rw [Fintype.card_eq_nat_card]; assumption
  rw [← (isProj_averageMap ρ).trace]
  simp [character, GroupAlgebra.average, _root_.map_sum]

/--
If `V` are `W` are finite-dimensional representations of a finite group, then the
scalar product of their characters is equal to the dimension of the space of
equivariant maps from `V` to `W`.
-/
theorem card_inv_mul_sum_char_mul_char_eq_finrank :
    (Nat.card G : k)⁻¹ * ∑ g : G, σ.character g * ρ.character g⁻¹ =
      finrank k (IntertwiningMap ρ σ) := by
  simp_rw [mul_comm, ← char_linHom, card_inv_mul_sum_char_eq_finrank,
    (invariantsEquivIntertwiningMap ρ σ).finrank_eq]

end Group

section Orthogonality

variable {G k V W : Type*} [Group G] [Field k] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
  (ρ : Representation k G V) (σ : Representation k G W)

variable [Fintype G] [Invertible (Nat.card G : k)] [IsAlgClosed k]

open scoped Classical in
/-- Orthogonality of characters for irreducible representations of finite group over an
algebraically closed field whose characteristic doesn't divide the order of the group. -/
theorem char_orthonormal [IsIrreducible ρ] [IsIrreducible σ] :
    (Nat.card G : k)⁻¹ * ∑ g : G, ρ.character g * σ.character g⁻¹ =
      if Nonempty (Equiv σ ρ) then ↑1 else ↑0 := by
  cases isEmpty_or_nonempty (Equiv σ ρ)
  · rw [card_inv_mul_sum_char_mul_char_eq_finrank]
    simpa
  · obtain φ : σ.Equiv ρ := Classical.choice inferInstance
    rw [char_iso φ, card_inv_mul_sum_char_mul_char_eq_finrank]
    simp

end Orthogonality

end Representation
