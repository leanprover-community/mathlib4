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

variable (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M]

open Module in
theorem Submodule.fg_iff_exists_fin_linearMap {N : Submodule R M} :
    N.FG ↔ ∃ (n : ℕ) (f : (Fin n → R) →ₗ[R] M), LinearMap.range f = N := by
  simp_rw [fg_iff_exists_fin_generating_family, ← ((Pi.basisFun R _).constr ℕ).exists_congr_right]
  simp [Basis.constr_range]

theorem AddSubmonoid.fg_iff_exists_fin_addMonoidHom {M : Type*} [AddCommMonoid M]
    {S : AddSubmonoid M} : S.FG ↔ ∃ (n : ℕ) (f : (Fin n → ℕ) →+ M), AddMonoidHom.mrange f = S := by
  rw [← S.toNatSubmodule_toAddSubmonoid, ← Submodule.fg_iff_addSubmonoid_fg,
    Submodule.fg_iff_exists_fin_linearMap]
  exact exists_congr fun n => ⟨fun ⟨f, hf⟩ => ⟨f, hf ▸ LinearMap.range_toAddSubmonoid _⟩,
    fun ⟨f, hf⟩ => ⟨f.toNatLinearMap, Submodule.toAddSubmonoid_inj.mp <|
      hf ▸ LinearMap.range_toAddSubmonoid _⟩⟩

theorem AddSubgroup.fg_iff_exists_fin_addMonoidHom {M : Type*} [AddCommGroup M]
    {H : AddSubgroup M} : H.FG ↔ ∃ (n : ℕ) (f : (Fin n → ℤ) →+ M), AddMonoidHom.range f = H := by
  rw [← H.toIntSubmodule_toAddSubgroup, ← Submodule.fg_iff_addSubgroup_fg,
    Submodule.fg_iff_exists_fin_linearMap]
  refine exists_congr fun n => ⟨fun ⟨f, hf⟩ => ⟨f, hf ▸ LinearMap.range_toAddSubgroup _⟩,
    fun ⟨f, hf⟩ => ⟨f.toIntLinearMap, Submodule.toAddSubmonoid_inj.mp ?_⟩⟩
  simp [hf]

namespace Module

namespace Finite

open Submodule Set

/-- A finite module admits a surjective linear map from a finite free module. -/
lemma exists_fin' [Module.Finite R M] : ∃ (n : ℕ) (f : (Fin n → R) →ₗ[R] M), Surjective f :=
  have ⟨n, f, hf⟩ := (Submodule.fg_iff_exists_fin_linearMap R M).mp fg_top
  ⟨n, f, by rw [← LinearMap.range_eq_top, hf]⟩

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

/-- The kernel of a random surjective linear map from a finite free module
to a given finite module. -/
noncomputable def kerRepr := LinearMap.ker (Finite.exists_fin' R M).choose_spec.choose

/-- A representative of a finite module in the same universe as the ring. -/
protected abbrev repr : Type u := _ ⧸ kerRepr R M

/-- The representative is isomorphic to the original module. -/
noncomputable def reprEquiv : Finite.repr R M ≃ₗ[R] M :=
  LinearMap.quotKerEquivOfSurjective _ (Finite.exists_fin' R M).choose_spec.choose_spec

end Module.Finite
