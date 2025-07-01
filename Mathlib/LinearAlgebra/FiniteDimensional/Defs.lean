/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Finite dimensional vector spaces

This file defines finite dimensional vector spaces and shows our definition is equivalent to
alternative definitions.

## Main definitions

Assume `V` is a vector space over a division ring `K`. There are (at least) three equivalent
definitions of finite-dimensionality of `V`:

- it admits a finite basis.
- it is finitely generated.
- it is noetherian, i.e., every subspace is finitely generated.

We introduce a typeclass `FiniteDimensional K V` capturing this property. For ease of transfer of
proof, it is defined using the second point of view, i.e., as `Module.Finite`. However, we prove
that all these points of view are equivalent, with the following lemmas
(in the namespace `FiniteDimensional`):

- `Module.finBasis` and `Module.finBasisOfFinrankEq`
  are bases for finite dimensional vector spaces, where the index type
  is `Fin` (in `Mathlib/LinearAlgebra/Dimension/Free.lean`)
- `fintypeBasisIndex` states that a finite-dimensional
  vector space has a finite basis
- `of_fintype_basis` states that the existence of a basis indexed by a
  finite type implies finite-dimensionality
- `of_finite_basis` states that the existence of a basis indexed by a
  finite set implies finite-dimensionality
- `of_finrank_pos` states that a nonzero finrank (implying non-infinite dimension)
  implies finite-dimensionality
- `IsNoetherian.iff_fg` states that the space is finite-dimensional if and only if
  it is noetherian (in `Mathlib/FieldTheory/Finiteness.lean`)

We make use of `finrank`, the dimension of a finite dimensional space, returning a `Nat`, as
opposed to `Module.rank`, which returns a `Cardinal`. When the space has infinite dimension, its
`finrank` is by convention set to `0`. `finrank` is not defined using `FiniteDimensional`.
For basic results that do not need the `FiniteDimensional` class, import
`Mathlib/LinearAlgebra/Finrank.lean`.

Preservation of finite-dimensionality and formulas for the dimension are given for
- submodules (`FiniteDimensional.finiteDimensional_submodule`)
- linear equivs, in `LinearEquiv.finiteDimensional`

## Implementation notes

You should not assume that there has been any effort to state lemmas as generally as possible.

Plenty of the results hold for general fg modules or notherian modules, and they can be found in
`Mathlib/LinearAlgebra/FreeModule/Finite/Rank.lean` and `Mathlib/RingTheory/Noetherian.lean`.
-/

assert_not_exists Module.Projective Subalgebra

universe u v v' w

open Cardinal Module Submodule

/-- `FiniteDimensional` vector spaces are defined to be finite modules.
Use `FiniteDimensional.of_fintype_basis` to prove finite dimension from another definition. -/
abbrev FiniteDimensional (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V] :=
  Module.Finite K V

variable {K : Type u} {V : Type v}

namespace FiniteDimensional
variable [DivisionRing K] [AddCommGroup V] [Module K V] {V₂ : Type v'} [AddCommGroup V₂]
  [Module K V₂]

/-- If the codomain of an injective linear map is finite dimensional, the domain must be as well. -/
theorem of_injective (f : V →ₗ[K] V₂) (w : Function.Injective f) [FiniteDimensional K V₂] :
    FiniteDimensional K V :=
  Module.Finite.of_injective f w

/-- If the domain of a surjective linear map is finite dimensional, the codomain must be as well. -/
theorem of_surjective (f : V →ₗ[K] V₂) (w : Function.Surjective f) [FiniteDimensional K V] :
    FiniteDimensional K V₂ :=
  Module.Finite.of_surjective f w

variable (K V)

instance finiteDimensional_pi {ι : Type*} [Finite ι] : FiniteDimensional K (ι → K) :=
  Finite.pi

instance finiteDimensional_pi' {ι : Type*} [Finite ι] (M : ι → Type*) [∀ i, AddCommGroup (M i)]
    [∀ i, Module K (M i)] [∀ i, FiniteDimensional K (M i)] : FiniteDimensional K (∀ i, M i) :=
  Finite.pi

variable {K V}

/-- If a vector space has a finite basis, then it is finite-dimensional. -/
theorem of_fintype_basis {ι : Type w} [Finite ι] (h : Basis ι K V) : FiniteDimensional K V :=
  Module.Finite.of_basis h

/-- If a vector space is `FiniteDimensional`, all bases are indexed by a finite type -/
noncomputable def fintypeBasisIndex {ι : Type*} [FiniteDimensional K V] (b : Basis ι K V) :
    Fintype ι :=
  @Fintype.ofFinite _ (Module.Finite.finite_basis b)

/-- If a vector space is `FiniteDimensional`, `Basis.ofVectorSpace` is indexed by
  a finite type. -/
noncomputable instance [FiniteDimensional K V] : Fintype (Basis.ofVectorSpaceIndex K V) :=
  fintypeBasisIndex (Basis.ofVectorSpace K V)

/-- If a vector space has a basis indexed by elements of a finite set, then it is
finite-dimensional. -/
theorem of_finite_basis {ι : Type w} {s : Set ι} (h : Basis s K V) (hs : Set.Finite s) :
    FiniteDimensional K V :=
  haveI := hs.fintype
  of_fintype_basis h

/-- A subspace of a finite-dimensional space is also finite-dimensional.

This is a shortcut instance to simplify inference in the presence of `[FiniteDimensional K V]`.
-/
instance finiteDimensional_submodule [FiniteDimensional K V] (S : Submodule K V) :
    FiniteDimensional K S := by
  infer_instance

/-- A quotient of a finite-dimensional space is also finite-dimensional. -/
instance finiteDimensional_quotient [FiniteDimensional K V] (S : Submodule K V) :
    FiniteDimensional K (V ⧸ S) :=
  Module.Finite.quotient K S

theorem of_finrank_pos (h : 0 < finrank K V) : FiniteDimensional K V :=
  Module.finite_of_finrank_pos h

theorem of_finrank_eq_succ {n : ℕ} (hn : finrank K V = n.succ) :
    FiniteDimensional K V :=
  Module.finite_of_finrank_eq_succ hn

/-- We can infer `FiniteDimensional K V` in the presence of `[Fact (finrank K V = n + 1)]`. Declare
this as a local instance where needed. -/
theorem of_fact_finrank_eq_succ (n : ℕ) [hn : Fact (finrank K V = n + 1)] :
    FiniteDimensional K V :=
  of_finrank_eq_succ hn.out

end FiniteDimensional

namespace Module

variable (K V)
variable [DivisionRing K] [AddCommGroup V] [Module K V]

/-- In a finite-dimensional space, its dimension (seen as a cardinal) coincides with its
`finrank`. This is a copy of `finrank_eq_rank _ _` which creates easier typeclass searches. -/
theorem finrank_eq_rank' [FiniteDimensional K V] : (finrank K V : Cardinal.{v}) = Module.rank K V :=
  finrank_eq_rank _ _

variable {K V}

theorem finrank_of_infinite_dimensional (h : ¬FiniteDimensional K V) : finrank K V = 0 :=
  Module.finrank_of_not_finite h

theorem finiteDimensional_iff_of_rank_eq_nsmul {W} [AddCommGroup W] [Module K W] {n : ℕ}
    (hn : n ≠ 0) (hVW : Module.rank K V = n • Module.rank K W) :
    FiniteDimensional K V ↔ FiniteDimensional K W :=
  Module.finite_iff_of_rank_eq_nsmul hn hVW

/-- If a vector space is finite-dimensional, then the cardinality of any basis is equal to its
`finrank`. -/
theorem finrank_eq_card_basis' [FiniteDimensional K V] {ι : Type w} (h : Basis ι K V) :
    (finrank K V : Cardinal.{w}) = #ι :=
  Module.mk_finrank_eq_card_basis h

end Module

namespace FiniteDimensional
section DivisionRing
variable [DivisionRing K] [AddCommGroup V] [Module K V] {V₂ : Type v'} [AddCommGroup V₂]
  [Module K V₂]

variable (K)

instance finiteDimensional_self : FiniteDimensional K K := inferInstance

/-- The submodule generated by a finite set is finite-dimensional. -/
theorem span_of_finite {A : Set V} (hA : Set.Finite A) : FiniteDimensional K (Submodule.span K A) :=
  Module.Finite.span_of_finite K hA

/-- The submodule generated by a single element is finite-dimensional. -/
instance span_singleton (x : V) : FiniteDimensional K (K ∙ x) :=
  Module.Finite.span_singleton K x

/-- The submodule generated by a finset is finite-dimensional. -/
instance span_finset (s : Finset V) : FiniteDimensional K (span K (s : Set V)) :=
  Module.Finite.span_finset K s

/-- Pushforwards of finite-dimensional submodules are finite-dimensional. -/
instance (f : V →ₗ[K] V₂) (p : Submodule K V) [FiniteDimensional K p] :
    FiniteDimensional K (p.map f) :=
  Module.Finite.map _ _

end DivisionRing

section Tower

variable (F K A : Type*) [DivisionRing F] [DivisionRing K] [AddCommGroup A]
variable [Module F K] [Module K A] [Module F A] [IsScalarTower F K A]

theorem trans [FiniteDimensional F K] [FiniteDimensional K A] : FiniteDimensional F A :=
  Module.Finite.trans K A

end Tower

end FiniteDimensional

namespace Submodule

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V]

/-- A submodule is finitely generated if and only if it is finite-dimensional -/
theorem fg_iff_finiteDimensional (s : Submodule K V) : s.FG ↔ FiniteDimensional K s :=
  (fg_top s).symm.trans Module.finite_def.symm

end DivisionRing

end Submodule

namespace LinearEquiv

variable [DivisionRing K] [AddCommGroup V] [Module K V] {V₂ : Type v'} [AddCommGroup V₂]
  [Module K V₂]

/-- Finite dimensionality is preserved under linear equivalence. -/
protected theorem finiteDimensional (f : V ≃ₗ[K] V₂) [FiniteDimensional K V] :
    FiniteDimensional K V₂ :=
  Module.Finite.equiv f

end LinearEquiv
