/-
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
import Mathlib.RepresentationTheory.FdRep
import Mathlib.LinearAlgebra.Trace
import Mathlib.RepresentationTheory.Invariants

#align_import representation_theory.character from "leanprover-community/mathlib"@"55b3f8206b8596db8bb1804d8a92814a0b6670c9"

/-!
# Characters of representations

This file introduces characters of representation and proves basic lemmas about how characters
behave under various operations on representations.

A key result is the orthogonality of characters for irreducible representations of finite group
over an algebraically closed field whose characteristic doesn't divide the order of the group. It
is the theorem `char_orthonormal`

# Implementation notes

Irreducible representations are implemented categorically, using the `Simple` class defined in
`Mathlib.CategoryTheory.Simple`

# TODO
* Once we have the monoidal closed structure on `FdRep k G` and a better API for the rigid
structure, `char_dual` and `char_linHom` should probably be stated in terms of `Vᘁ` and `ihom V W`.
-/


noncomputable section

universe u

open CategoryTheory LinearMap CategoryTheory.MonoidalCategory Representation FiniteDimensional

variable {k : Type u} [Field k]

namespace FdRep
set_option linter.uppercaseLean3 false -- `FdRep`

section Monoid

variable {G : Type u} [Monoid G]

/-- The character of a representation `V : FdRep k G` is the function associating to `g : G` the
trace of the linear map `V.ρ g`. -/
def character (V : FdRep k G) (g : G) :=
  LinearMap.trace k V (V.ρ g)
#align fdRep.character FdRep.character

theorem char_mul_comm (V : FdRep k G) (g : G) (h : G) :
    V.character (h * g) = V.character (g * h) := by simp only [trace_mul_comm, character, map_mul]
#align fdRep.char_mul_comm FdRep.char_mul_comm

@[simp]
theorem char_one (V : FdRep k G) : V.character 1 = FiniteDimensional.finrank k V := by
  simp only [character, map_one, trace_one]
#align fdRep.char_one FdRep.char_one

/-- The character is multiplicative under the tensor product. -/
theorem char_tensor (V W : FdRep k G) : (V ⊗ W).character = V.character * W.character := by
  ext g; convert trace_tensorProduct' (V.ρ g) (W.ρ g)
#align fdRep.char_tensor FdRep.char_tensor

-- Porting note: adding variant of `char_tensor` to make the simp-set confluent
@[simp]
theorem char_tensor' (V W : FdRep k G) :
    character (Action.FunctorCategoryEquivalence.inverse.obj
    (Action.FunctorCategoryEquivalence.functor.obj V ⊗
     Action.FunctorCategoryEquivalence.functor.obj W)) = V.character * W.character := by
  simp [← char_tensor]

/-- The character of isomorphic representations is the same. -/
theorem char_iso {V W : FdRep k G} (i : V ≅ W) : V.character = W.character := by
  ext g; simp only [character, FdRep.Iso.conj_ρ i]; exact (trace_conj' (V.ρ g) _).symm
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
  rw [← char_iso (dualTensorIsoLinHom _ _), char_tensor, Pi.mul_apply, char_dual]
#align fdRep.char_lin_hom FdRep.char_linHom

variable [Fintype G] [Invertible (Fintype.card G : k)]

theorem average_char_eq_finrank_invariants (V : FdRep k G) :
    ⅟ (Fintype.card G : k) • ∑ g : G, V.character g = finrank k (invariants V.ρ) := by
  erw [← (isProj_averageMap V.ρ).trace] -- Porting note: Changed `rw` to `erw`
  simp [character, GroupAlgebra.average, _root_.map_sum]
#align fdRep.average_char_eq_finrank_invariants FdRep.average_char_eq_finrank_invariants

end Group

section Orthogonality

variable {G : Grp.{u}} [IsAlgClosed k]

open scoped Classical

variable [Fintype G] [Invertible (Fintype.card G : k)]

/-- Orthogonality of characters for irreducible representations of finite group over an
algebraically closed field whose characteristic doesn't divide the order of the group. -/
theorem char_orthonormal (V W : FdRep k G) [Simple V] [Simple W] :
    ⅟ (Fintype.card G : k) • ∑ g : G, V.character g * W.character g⁻¹ =
      if Nonempty (V ≅ W) then ↑1 else ↑0 := by
  -- First, we can rewrite the summand `V.character g * W.character g⁻¹` as the character
  -- of the representation `V ⊗ W* ≅ Hom(W, V)` applied to `g`.
  -- Porting note: Originally `conv in V.character _ * W.character _ =>`
  conv_lhs =>
    enter [2, 2, g]
    rw [mul_comm, ← char_dual, ← Pi.mul_apply, ← char_tensor]
    rw [char_iso (FdRep.dualTensorIsoLinHom W.ρ V)]
  -- The average over the group of the character of a representation equals the dimension of the
  -- space of invariants.
  rw [average_char_eq_finrank_invariants]
  rw [show (of (linHom W.ρ V.ρ)).ρ = linHom W.ρ V.ρ from FdRep.of_ρ (linHom W.ρ V.ρ)]
  -- The space of invariants of `Hom(W, V)` is the subspace of `G`-equivariant linear maps,
  -- `Hom_G(W, V)`.
  erw [(linHom.invariantsEquivFdRepHom W V).finrank_eq] -- Porting note: Changed `rw` to `erw`
  -- By Schur's Lemma, the dimension of `Hom_G(W, V)` is `1` is `V ≅ W` and `0` otherwise.
  rw_mod_cast [finrank_hom_simple_simple W V, Iso.nonempty_iso_symm]
#align fdRep.char_orthonormal FdRep.char_orthonormal

end Orthogonality

end FdRep
