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
import Mathlib.Data.DFinsupp.Small

/-! # Smallness properties of modules and algebras -/

universe u

namespace Submodule

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

theorem small_sup {P Q : Submodule R M} (_ : Small.{u} P) (_ : Small.{u} Q) :
    Small.{u} (P ⊔ Q : Submodule R M) := by
  rw [Submodule.sup_eq_range]
  exact small_range _

theorem FG.small [Small.{u} R] (P : Submodule R M) (hP : P.FG) : Small.{u} P := by
  rw [fg_iff_exists_fin_generating_family] at hP
  obtain ⟨n, s, rfl⟩ := hP
  rw [← Fintype.range_linearCombination]
  apply small_range

theorem small_iSup
    {ι : Type*} {P : ι → Submodule R M} (_ : Small.{u} ι) (_ : ∀ i, Small.{u} (P i)) :
    Small.{u} (iSup P : Submodule R M) := by
  classical
  rw [iSup_eq_range_dfinsupp_lsum]
  have : Small.{u} (Π₀ (i : ι), ↥(P i)) := inferInstance
  apply small_range

theorem small_span [Small.{u} R] (s : Set M) [Small.{u} s] :
    Small.{u} (span R s) := by
  suffices span R s = iSup (fun i : s ↦ span R ({(↑i : M)} : Set M)) by
    rw [this]
    exact small_iSup (by trivial) fun _ ↦ FG.small _ (fg_span_singleton _)
  simp [← Submodule.span_iUnion]

instance : SemilatticeSup {P : Submodule R M // Small.{u} P} where
  sup := fun P Q ↦ ⟨P.val ⊔ Q.val, small_sup P.property Q.property⟩
  le_sup_left := fun P Q ↦ by rw [← Subtype.coe_le_coe]; exact le_sup_left
  le_sup_right := fun P Q ↦ by rw [← Subtype.coe_le_coe]; exact le_sup_right
  sup_le := fun _ _ _ hPR hQR ↦ by
    rw [← Subtype.coe_le_coe] at hPR hQR ⊢
    exact sup_le hPR hQR

instance : Inhabited {P : Submodule R M // Small.{u} P} where
  default := ⟨⊥, inferInstance⟩

end Submodule

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

namespace Algebra

open MvPolynomial AlgHom

theorem small_adjoin [Small.{u} R] {s : Set S} [Small.{u} s] :
    Small.{u} (adjoin R s : Subalgebra R S) := by
  let j' := mapEquiv (Shrink.{u} s) (Shrink.ringEquiv R)
  have : Small.{u} (MvPolynomial (Shrink.{u} s) R) := small_of_surjective j'.surjective
  let j : MvPolynomial (Shrink.{u} s) R →ₐ[R] S := aeval (fun i ↦ (equivShrink s).symm i)
  have hj : adjoin R s = j.range := by
    rw [← adjoin_range_eq_range_aeval, ← Function.comp_def]
    simp
  rw [hj]
  apply small_range (f := j)

theorem FiniteType.small [Small.{u} R] [Algebra.FiniteType R S] :
    Small.{u} S := by
  obtain ⟨s : Finset S, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra R S).FG)
  have : Small.{u} (adjoin R s : Subalgebra R S) := small_adjoin
  apply small_of_surjective (f := (adjoin R s).subtype)
  rw [hs]
  exact fun x ↦ ⟨⟨x, by simp⟩, by simp⟩

theorem _root_.Subalgebra.FG.small [Small.{u} R] {A : Subalgebra R S} (fgS : A.FG) :
    Small.{u} A := by
  have : FiniteType R A := (Subalgebra.fg_iff_finiteType A).mp fgS
  exact FiniteType.small (R := R) (S := A)

end Algebra
