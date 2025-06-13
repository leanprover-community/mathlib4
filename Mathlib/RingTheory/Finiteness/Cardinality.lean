/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.LinearAlgebra.Basis.Cardinality
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Isomorphisms
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

/-- A finite module can be realised as a quotient of `Fin n → R` (i.e. `R^n`). -/
theorem exists_fin_quot_equiv (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]
      [Module.Finite R M] :
    ∃ (n : ℕ) (S : Submodule R (Fin n → R)), Nonempty ((_ ⧸ S) ≃ₗ[R] M) :=
  let ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  ⟨n, LinearMap.ker f, ⟨f.quotKerEquivOfSurjective hf⟩⟩

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
