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


/-! # Smallness properties of modules and algebras -/

universe u

namespace Submodule

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

theorem bot_small : Small.{u} (⊥ : Submodule R M) := by
  let f : Unit → (⊥ : Submodule R M) := fun _ ↦ 0
  have : Small.{u} Unit := small_lift Unit
  apply small_of_surjective (f := f)
  rintro ⟨x, hx⟩
  simp only [mem_bot] at hx
  use default
  simp [← Subtype.coe_inj, f, hx]

theorem small_sup {P Q : Submodule R M} (_ : Small.{u} P) (_ : Small.{u} Q) :
    Small.{u} (P ⊔ Q : Submodule R M) := by
  rw [Submodule.sup_eq_range]
  exact small_range _

theorem FG.small [Small.{u} R] (P : Submodule R M) (hP : P.FG) : Small.{u} P := by
  rw [fg_iff_exists_fin_generating_family] at hP
  obtain ⟨n, s, rfl⟩ := hP
  rw [← Fintype.range_linearCombination]
  apply small_range

theorem small_directSum
    {ι : Type*} {P : ι → Submodule R M} [Small.{u} ι] [∀ i, Small.{u} (P i)] :
    Small.{u} (Π₀ (i : ι), ↥(P i)) := by
  classical
  -- Define somewhere else
  have : Small.{u} (Finset ι) := small_of_injective (f := Finset.toSet) Finset.coe_injective
  have (s : Finset ι) : Small.{u} (Π (i : s), P i) := small_Pi _
  let h : (Σ (s : Finset ι), (Π i : s, P i)) → Π₀ i, P i := fun sf ↦ by
    exact {
      toFun (i : ι) := if h : i ∈ sf.1.val then sf.2 ⟨i, h⟩ else 0
      support' := Trunc.mk ⟨sf.1.val, fun i ↦ by
        simp only [Finset.mem_val, dite_eq_right_iff]
        by_cases hi : i ∈ sf.1
        · exact Or.inl hi
        · apply Or.inr fun h ↦ False.elim (hi h)⟩}
  apply small_of_surjective (f := h)
  intro m
  use ⟨m.support, fun i ↦ m i⟩
  ext i
  simp only [Finset.mem_val, DFinsupp.mem_support_toFun, ne_eq, dite_eq_ite, DFinsupp.coe_mk',
    ite_not, SetLike.coe_eq_coe, ite_eq_right_iff, h]
  simp only [eq_comm, imp_self, h]

theorem small_iSup
    {ι : Type*} {P : ι → Submodule R M} (_ : Small.{u} ι) (_ : ∀ i, Small.{u} (P i)) :
    Small.{u} (iSup P : Submodule R M) := by
  classical
  rw [iSup_eq_range_dfinsupp_lsum]
  have : Small.{u} (Π₀ (i : ι), ↥(P i)) := Submodule.small_directSum
  apply small_range

theorem small_span [Small.{u} R] (s : Set M) [Small.{u} s] :
    Small.{u} (span R s) := by
  suffices span R s = iSup (fun i : s ↦ span R ({(↑i : M)} : Set M)) by
    rw [this]
    exact small_iSup (by trivial) fun _ ↦ FG.small _ (fg_span_singleton _)
  apply le_antisymm
  · rw [span_le]
    intro i hi
    apply mem_iSup_of_mem (⟨i, hi⟩ : s)
    refine span_mono (s := {i}) (by simp) (mem_span_singleton_self i)
  · apply iSup_le
    rintro ⟨i, hi⟩
    simp only [span_singleton_le_iff_mem]
    apply span_mono (s := {i}) _ (mem_span_singleton_self i)
    simp only [Set.singleton_subset_iff, hi]

instance : SemilatticeSup {P : Submodule R M // Small.{u} P} where
  sup := fun P Q ↦ ⟨P.val ⊔ Q.val, small_sup P.property Q.property⟩
  le_sup_left := fun P Q ↦ by rw [← Subtype.coe_le_coe]; exact le_sup_left
  le_sup_right := fun P Q ↦ by rw [← Subtype.coe_le_coe]; exact le_sup_right
  sup_le := fun _ _ _ hPR hQR ↦ by
    rw [← Subtype.coe_le_coe] at hPR hQR ⊢
    exact sup_le hPR hQR

instance : Inhabited {P : Submodule R M // Small.{u} P} where
  default := ⟨⊥, bot_small⟩

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
