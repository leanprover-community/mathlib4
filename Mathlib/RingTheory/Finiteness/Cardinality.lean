/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.LinearAlgebra.Basis.Cardinality
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finite modules and types with finitely many elements

This file relates `Module.Finite` and `_root_.Finite`.

-/

open Function (Surjective)
open Finsupp

section ModuleAndAlgebra

universe v u
variable (R : Type u) (A B M N : Type*)

namespace Module

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

namespace Finite

open Submodule Set

/-- A finite module admits a surjective linear map from a finite free module. -/
lemma exists_fin' [Module.Finite R M] : ∃ (n : ℕ) (f : (Fin n → R) →ₗ[R] M), Surjective f := by
  have ⟨n, s, hs⟩ := exists_fin (R := R) (M := M)
  refine ⟨n, Basis.constr (Pi.basisFun R _) ℕ s, ?_⟩
  rw [← LinearMap.range_eq_top, Basis.constr_range, hs]

variable {M}

lemma _root_.Module.finite_of_finite [Finite R] [Module.Finite R M] : Finite M := by
  obtain ⟨n, f, hf⟩ := exists_fin' R M; exact .of_surjective f hf

variable {R}

/-- A finite dimensional vector space over a finite field is finite -/
@[deprecated (since := "2024-10-22")]
alias _root_.FiniteDimensional.fintypeOfFintype := finite_of_finite

/-- A module over a finite ring has finite dimension iff it is finite. -/
lemma _root_.Module.finite_iff_finite [Finite R] : Module.Finite R M ↔ Finite M :=
  ⟨fun _ ↦ finite_of_finite R, fun _ ↦ .of_finite⟩

variable (R) in
lemma _root_.Set.Finite.submoduleSpan [Finite R] {s : Set M} (hs : s.Finite) :
    (Submodule.span R s : Set M).Finite := by
  lift s to Finset M using hs
  rw [Set.Finite, ← Module.finite_iff_finite (R := R)]
  dsimp
  infer_instance

/-- If a free module is finite, then any arbitrary basis is finite. -/
lemma finite_basis [Nontrivial R] {ι} [Module.Finite R M]
    (b : Basis ι R M) :
    _root_.Finite ι :=
  let ⟨s, hs⟩ := ‹Module.Finite R M›
  basis_finite_of_finite_spans s.finite_toSet hs b

end Finite

variable {R M}
lemma not_finite_of_infinite_basis [Nontrivial R] {ι} [Infinite ι] (b : Basis ι R M) :
    ¬ Module.Finite R M :=
  fun _ ↦ (Finite.finite_basis b).not_infinite ‹_›

end Module

end ModuleAndAlgebra

namespace Module.Finite

universe u
variable (R : Type u) (M : Type*) [Ring R] [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- The kernel of a surjective linear map from a finite free module to a given finite module. -/
noncomputable def kerRepr := LinearMap.ker (Finite.exists_fin' R M).choose_spec.choose

/-- A representative of a finite module in the same universe as the ring. -/
protected abbrev repr : Type u := _ ⧸ kerRepr R M

/-- The representative is isomorphic to the original module. -/
noncomputable def reprEquiv : Finite.repr R M ≃ₗ[R] M :=
  LinearMap.quotKerEquivOfSurjective _ (Finite.exists_fin' R M).choose_spec.choose_spec

end Module.Finite
