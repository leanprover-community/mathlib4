/-
Copyright (c) 2025 Antoine Chambert-Loir, María-Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, Maria-Inés de Frutos-Fernandez
-/
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.FiniteType
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.LinearAlgebra.Basis.Cardinality
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Data.DFinsupp.Small

/-! # Smallness properties of modules and algebras -/

universe u

namespace Submodule

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

instance small_sup {P Q : Submodule R M} [smallP : Small.{u} P] [smallQ : Small.{u} Q] :
    Small.{u} (P ⊔ Q : Submodule R M) := by
  rw [Submodule.sup_eq_range]
  exact small_range _

instance : SemilatticeSup {P : Submodule R M // Small.{u} P} where
  sup := fun P Q ↦ ⟨P.val ⊔ Q.val, small_sup (smallP := P.property) (smallQ := Q.property)⟩
  le_sup_left := fun P Q ↦ by rw [← Subtype.coe_le_coe]; exact le_sup_left
  le_sup_right := fun P Q ↦ by rw [← Subtype.coe_le_coe]; exact le_sup_right
  sup_le := fun _ _ _ hPR hQR ↦ by
    rw [← Subtype.coe_le_coe] at hPR hQR ⊢
    exact sup_le hPR hQR

instance : Inhabited {P : Submodule R M // Small.{u} P} where
  default := ⟨⊥, inferInstance⟩

instance small_iSup
    {ι : Type*} {P : ι → Submodule R M} [Small.{u} ι] [∀ i, Small.{u} (P i)] :
    Small.{u} (iSup P : Submodule R M) := by
  classical
  rw [iSup_eq_range_dfinsupp_lsum]
  apply small_range

theorem FG.small [Small.{u} R] (P : Submodule R M) (hP : P.FG) : Small.{u} P := by
  rw [fg_iff_exists_fin_generating_family] at hP
  obtain ⟨n, s, rfl⟩ := hP
  rw [← Fintype.range_linearCombination]
  apply small_range

variable (R M) in
theorem _root_.Module.Finite.small [Small.{u} R] [Module.Finite R M] : Small.{u} M := by
  have : Small.{u} (⊤ : Submodule R M) :=
    FG.small _ (Module.finite_def.mp inferInstance)
  rwa [← small_univ_iff]

instance small_span_singleton [Small.{u} R] (m : M) :
    Small.{u} (span R {m}) := FG.small _ (fg_span_singleton _)

theorem small_span [Small.{u} R] (s : Set M) [Small.{u} s] :
    Small.{u} (span R s) := by
  suffices span R s = iSup (fun i : s ↦ span R ({(↑i : M)} : Set M)) by
    rw [this]
    apply small_iSup
  simp [← Submodule.span_iUnion]

end Submodule

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

namespace Algebra

open MvPolynomial AlgHom

instance small_adjoin [Small.{u} R] {s : Set S} [Small.{u} s] :
    Small.{u} (adjoin R s : Subalgebra R S) := by
  rw [Algebra.adjoin_eq_range]
  apply small_range

theorem _root_.Subalgebra.FG.small [Small.{u} R] {A : Subalgebra R S} (fgS : A.FG) :
    Small.{u} A := by
  obtain ⟨s, hs, rfl⟩ := fgS
  exact small_adjoin

theorem FiniteType.small [Small.{u} R] [Algebra.FiniteType R S] :
    Small.{u} S := by
  have : Small.{u} (⊤ : Subalgebra R S) :=
    Subalgebra.FG.small Algebra.FiniteType.out
  rwa [← small_univ_iff]

end Algebra
