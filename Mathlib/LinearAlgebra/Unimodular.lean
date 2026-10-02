/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Unimodular elements and completion to a basis

An element `v` of a module is *unimodular* if some linear functional takes the value `1` at `v`.
For a free module this is equivalent to the coordinates of `v` in any basis generating the unit
ideal (for `M = ℤⁿ`: the gcd of the coordinates is `1`, i.e. `v` is a *primitive* vector).

## Main definitions

* `Module.IsUnimodular R v`: some linear functional takes the value `1` at `v`.

## Main results

* `Module.Basis.span_repr_eq_range_applyₗ`: the coordinates of `v` in a basis generate the
  ideal of values taken at `v` by the linear functionals;
* `Module.Basis.isUnimodular_iff_span_repr_eq_top`: the coordinate characterisation of
  unimodularity in the free case;
* `Module.IsUnimodular.exists_basis_zero_eq`: a unimodular vector of a rank-two module can be
  completed to a basis;
* `Module.Free.isUnimodular_one`: in a nonzero algebra that is free as a module, `1` is
  unimodular.

## References

* [T. Y. Lam, *Serre's Problem on Projective Modules*][lam_2006].
-/

public section

namespace Module

variable (R : Type*) [Semiring R] {M : Type*} [AddCommMonoid M] [Module R M]

/-- An element `v` of an `R`-module is *unimodular* if some linear functional takes the value
`1` at `v`. -/
def IsUnimodular (v : M) : Prop := ∃ f : M →ₗ[R] R, f v = 1

variable {R} {v : M}

theorem isUnimodular_iff : IsUnimodular R v ↔ ∃ f : M →ₗ[R] R, f v = 1 := Iff.rfl

theorem isUnimodular_of_apply_eq_one {f : M →ₗ[R] R} (hf : f v = 1) : IsUnimodular R v := ⟨f, hf⟩

end Module

namespace Module.Basis

section CommSemiring

variable {R : Type*} [CommSemiring R] {M : Type*} [AddCommMonoid M] [Module R M]

/-- The coordinates of `v` in a basis `b` generate the ideal of values taken at `v` by the linear
functionals on `M`. In particular this ideal does not depend on `b`. -/
theorem span_repr_eq_range_applyₗ {ι : Type*} (b : Basis ι R M) (v : M) :
    Ideal.span (Set.range (b.repr v)) = LinearMap.range (LinearMap.applyₗ v) := by
  refine le_antisymm (Ideal.span_le.mpr ?_) ?_
  · rintro _ ⟨i, rfl⟩
    exact ⟨b.coord i, rfl⟩
  · rintro _ ⟨f, rfl⟩
    simp only [LinearMap.applyₗ_apply_apply, ← congr_arg f (b.linearCombination_repr v),
      Finsupp.linearCombination_apply, map_finsuppSum, map_smul, smul_eq_mul]
    exact Submodule.finsuppSum_mem R _ _ _ fun i _ ↦
      Ideal.mul_mem_right _ _ Ideal.mem_span_range_self

/-- Coordinate characterisation of unimodularity in the free case: given a basis `b`, the
coordinates of `v` generate the unit ideal iff `v` is unimodular. -/
theorem isUnimodular_iff_span_repr_eq_top {ι : Type*} {b : Basis ι R M} {v : M} :
    IsUnimodular R v ↔ Ideal.span (Set.range (b.repr v)) = ⊤ := by
  simp [Ideal.eq_top_iff_one, span_repr_eq_range_applyₗ, isUnimodular_iff]

end CommSemiring

section Algebra

variable {R : Type*} [CommRing R] {A : Type*} [Ring A] [Nontrivial A] [Algebra R A]

/-- In a nonzero algebra that is free as a module, `1` is *unimodular*. -/
theorem _root_.Module.Free.isUnimodular_one [Module.Free R A] : IsUnimodular R (1 : A) :=
  isUnimodular_iff_span_repr_eq_top.mpr (Module.Free.chooseBasis R A).span_repr_one_eq_top

end Algebra

end Module.Basis

namespace Module.IsUnimodular

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Free R M]

/-- A unimodular vector of a rank-two module can be completed to a basis: it is the first
vector of a basis. -/
theorem exists_basis_zero_eq (hM : Module.finrank R M = 2) {v : M} (hv : IsUnimodular R v) :
    ∃ e : Basis (Fin 2) R M, e 0 = v := by
  have : Nontrivial R := not_subsingleton_iff_nontrivial.mp fun _ ↦ by simp at hM
  have : Module.Finite R M := Module.finite_of_finrank_eq_succ hM
  obtain ⟨f, hf⟩ := isUnimodular_iff.mp hv
  let b := (Module.Free.chooseBasis R M).reindex
    (Fintype.equivFinOfCardEq ((Module.finrank_eq_card_chooseBasisIndex R M).symm.trans hM))
  let N : Matrix (Fin 2) (Fin 2) R := !![b.repr v 0, -(f (b 1)); b.repr v 1, f (b 0)]
  have hdet : N.det = 1 := by
    rw [Matrix.det_fin_two_of, neg_mul, sub_neg_eq_add, mul_comm (f (b 1)) (b.repr v 1), ← hf]
    conv_rhs => rw [← b.sum_repr v]
    rw [map_sum, Fin.sum_univ_two, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  refine ⟨b.map (Matrix.toLinearEquiv b N (hdet ▸ isUnit_one)), ?_⟩
  simpa [N] using (Fin.sum_univ_two fun i ↦ b.repr v i • b i).symm.trans (b.sum_repr v)

end Module.IsUnimodular
