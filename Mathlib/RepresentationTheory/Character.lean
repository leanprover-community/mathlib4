/-
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle

! This file was ported from Lean 3 source module representation_theory.character
! leanprover-community/mathlib commit 55b3f8206b8596db8bb1804d8a92814a0b6670c9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.RepresentationTheory.FdRep
import Mathlib.LinearAlgebra.Trace
import Mathlib.RepresentationTheory.Invariants

/-!
# Characters of representations

This file introduces characters of representation and proves basic lemmas about how characters
behave under various operations on representations.

# TODO
* Once we have the monoidal closed structure on `fdRep k G` and a better API for the rigid
structure, `char_dual` and `char_lin_hom` should probably be stated in terms of `Vᘁ` and `ihom V W`.
-/


noncomputable section

universe u

open CategoryTheory LinearMap CategoryTheory.MonoidalCategory Representation FiniteDimensional

open scoped BigOperators

variable {k : Type u} [Field k]

namespace FdRep

section Monoid

variable {G : Type u} [Monoid G]

/-- The character of a representation `V : fdRep k G` is the function associating to `g : G` the
trace of the linear map `V.ρ g`.-/
def character (V : FdRep k G) (g : G) :=
  LinearMap.trace k V (V.ρ g)
#align fdRep.character FdRep.character

theorem char_mul_comm (V : FdRep k G) (g : G) (h : G) : V.character (h * g) = V.character (g * h) :=
  by simp only [trace_mul_comm, character, map_mul]
#align fdRep.char_mul_comm FdRep.char_mul_comm

@[simp]
theorem char_one (V : FdRep k G) : V.character 1 = FiniteDimensional.finrank k V := by
  simp only [character, map_one, trace_one]
#align fdRep.char_one FdRep.char_one

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The character is multiplicative under the tensor product. -/
@[simp]
theorem char_tensor (V W : FdRep k G) : (V ⊗ W).character = V.character * W.character := by ext g;
  convert trace_tensor_product' (V.ρ g) (W.ρ g)
#align fdRep.char_tensor FdRep.char_tensor

/-- The character of isomorphic representations is the same. -/
theorem char_iso {V W : FdRep k G} (i : V ≅ W) : V.character = W.character := by ext g;
  simp only [character, FdRep.Iso.conj_ρ i]; exact (trace_conj' (V.ρ g) _).symm
#align fdRep.char_iso FdRep.char_iso

end Monoid

section Group

variable {G : Type u} [Group G]

/-- The character of a representation is constant on conjugacy classes. -/
@[simp]
theorem char_conj (V : FdRep k G) (g : G) (h : G) : V.character (h * g * h⁻¹) = V.character g := by
  rw [char_mul_comm, inv_mul_cancel_left]
#align fdRep.char_conj FdRep.char_conj

@[simp]
theorem char_dual (V : FdRep k G) (g : G) : (of (dual V.ρ)).character g = V.character g⁻¹ :=
  trace_transpose' (V.ρ g⁻¹)
#align fdRep.char_dual FdRep.char_dual

@[simp]
theorem char_linHom (V W : FdRep k G) (g : G) :
    (of (linHom V.ρ W.ρ)).character g = V.character g⁻¹ * W.character g := by
  rw [← char_iso (dual_tensor_iso_lin_hom _ _), char_tensor, Pi.mul_apply, char_dual]
#align fdRep.char_lin_hom FdRep.char_linHom

variable [Fintype G] [Invertible (Fintype.card G : k)]

theorem average_char_eq_finrank_invariants (V : FdRep k G) :
    ⅟ (Fintype.card G : k) • ∑ g : G, V.character g = finrank k (invariants V.ρ) := by
  rw [← (is_proj_average_map V.ρ).trace]; simp [character, GroupAlgebra.average, _root_.map_sum]
#align fdRep.average_char_eq_finrank_invariants FdRep.average_char_eq_finrank_invariants

end Group

section Orthogonality

variable {G : GroupCat.{u}} [IsAlgClosed k]

open scoped Classical

variable [Fintype G] [Invertible (Fintype.card G : k)]

/-- Orthogonality of characters for irreducible representations of finite group over an
algebraically closed field whose characteristic doesn't divide the order of the group. -/
theorem char_orthonormal (V W : FdRep k G) [Simple V] [Simple W] :
    ⅟ (Fintype.card G : k) • ∑ g : G, V.character g * W.character g⁻¹ =
      if Nonempty (V ≅ W) then ↑1 else ↑0 := by
  -- First, we can rewrite the summand `V.character g * W.character g⁻¹` as the character
  -- of the representation `V ⊗ W* ≅ Hom(W, V)` applied to `g`.
  conv in
    V.character _ *
      W.character _ =>
    rw [mul_comm, ← char_dual, ← Pi.mul_apply, ← char_tensor]
    rw [char_iso (FdRep.dualTensorIsoLinHom W.ρ V)]
  -- The average over the group of the character of a representation equals the dimension of the
  -- space of invariants.
  rw [average_char_eq_finrank_invariants]
  rw [show (of (lin_hom W.ρ V.ρ)).ρ = lin_hom W.ρ V.ρ from FdRep.of_ρ (lin_hom W.ρ V.ρ)]
  -- The space of invariants of `Hom(W, V)` is the subspace of `G`-equivariant linear maps,
  -- `Hom_G(W, V)`.
  rw [(lin_hom.invariants_equiv_fdRep_hom W V).finrank_eq]
  -- By Schur's Lemma, the dimension of `Hom_G(W, V)` is `1` is `V ≅ W` and `0` otherwise.
  rw_mod_cast [finrank_hom_simple_simple W V, iso.nonempty_iso_symm]
#align fdRep.char_orthonormal FdRep.char_orthonormal

end Orthogonality

end FdRep

