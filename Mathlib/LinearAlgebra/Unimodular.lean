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

An element `v` of an `R`-module is *unimodular* if some linear functional takes the value
`1` at `v`; for a free module this is equivalent to the coordinates of `v` in any basis
generating the unit ideal (for `M = ℤⁿ`: the gcd of the coordinates is `1`, i.e. `v` is a
*primitive* vector).

The main results are:
* `Module.Basis.span_repr_eq_top_iff`: the coordinate characterisation of unimodularity in
  the free case;
* `Module.Free.exists_basis_zero_eq`: a unimodular vector of a rank-two module can be
  completed to a basis. This fails in higher rank, see [lam_2006];
* `Module.Basis.span_repr_one_eq_top` and `Module.Free.exists_linearMap_one_eq_one`:
  in a nonzero algebra that is free as a module, `1` is unimodular.

## References

* [T. Y. Lam, *Serre's Problem on Projective Modules*][lam_2006], Chapter I.
-/

public section

namespace Module.Basis

section

variable {R : Type*} [CommSemiring R] {M : Type*} [AddCommMonoid M] [Module R M]

/-- Coordinate characterisation of unimodularity in the free case: given a basis `b`, the
coordinates of `v` generate the unit ideal iff some linear functional takes the value `1`
at `v` (that is, iff `v` is *unimodular*). -/
theorem span_repr_eq_top_iff {ι : Type*} (b : Module.Basis ι R M) {v : M} :
    Ideal.span (Set.range (b.repr v)) = ⊤ ↔ ∃ f : M →ₗ[R] R, f v = 1 := by
  rw [Ideal.eq_top_iff_one]
  refine ⟨fun h ↦ ?_, fun ⟨f, hf⟩ ↦ ?_⟩
  · obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp h
    exact ⟨c.sum fun i a ↦ a • b.coord i, by simpa using hc⟩
  · rw [← b.linearCombination_repr v, Finsupp.linearCombination_apply, map_finsuppSum] at hf
    simp only [← hf, map_smul, smul_eq_mul]
    exact Submodule.finsuppSum_mem R _ _ _ fun i _ ↦
      Ideal.mul_mem_right _ _ Ideal.mem_span_range_self

end

section Algebra

variable {R : Type*} [CommRing R] {A ι : Type*} [Ring A] [Nontrivial A] [Algebra R A]

/-- In a nonzero algebra that is free as a module, the coordinates of `1` in any basis generate
the unit ideal; that is, `1` is *unimodular*. -/
theorem span_repr_one_eq_top (e : Module.Basis ι R A) :
    Ideal.span (Set.range (e.repr 1)) = ⊤ := by
  nontriviality R
  have : Module.Free R A := .of_basis e
  by_contra h
  obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ h
  refine Module.FaithfullyFlat.submodule_ne_top h𝔪 (Submodule.eq_top_iff'.mpr fun a : A ↦ ?_)
  rw [← mul_one a, ← e.linearCombination_repr 1, Finsupp.linearCombination_apply, Finsupp.mul_sum]
  exact Submodule.sum_mem _ fun i _ ↦ by
    simpa using Submodule.smul_mem_smul (hle (Ideal.subset_span ⟨i, rfl⟩)) Submodule.mem_top

end Algebra

end Module.Basis

namespace Module.Free

variable {R : Type*} [CommRing R]

section

variable {M : Type*} [AddCommGroup M] [Module R M] [Module.Free R M]

/-- A *unimodular* vector of a rank-two module can be completed to a basis: if some linear
functional takes the value `1` at `v`, then `v` is the first vector of a basis. -/
theorem exists_basis_zero_eq (hM : Module.finrank R M = 2) {v : M}
    (hv : ∃ f : M →ₗ[R] R, f v = 1) :
    ∃ e : Module.Basis (Fin 2) R M, e 0 = v := by
  obtain ⟨f, hf⟩ := hv
  have : Nontrivial R := not_subsingleton_iff_nontrivial.mp fun _ ↦ by simp at hM
  have : Module.Finite R M := Module.finite_of_finrank_eq_succ hM
  let b := (chooseBasis R M).reindex
    (Fintype.equivFinOfCardEq ((Module.finrank_eq_card_chooseBasisIndex R M).symm.trans hM))
  let N : Matrix (Fin 2) (Fin 2) R := !![b.repr v 0, -(f (b 1)); b.repr v 1, f (b 0)]
  have hdet : N.det = 1 := by
    rw [Matrix.det_fin_two_of, neg_mul, sub_neg_eq_add, mul_comm (f (b 1)) (b.repr v 1), ← hf]
    conv_rhs => rw [← b.sum_repr v]
    rw [map_sum, Fin.sum_univ_two, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  refine ⟨b.map (Matrix.toLinearEquiv b N (hdet ▸ isUnit_one)), ?_⟩
  simpa [N] using (Fin.sum_univ_two fun i ↦ b.repr v i • b i).symm.trans (b.sum_repr v)

end

/-- In a nonzero algebra that is free as a module, there is a linear functional taking the
value `1` at `1`; that is, `1` is *unimodular*. -/
theorem exists_linearMap_one_eq_one {A : Type*} [Ring A] [Nontrivial A] [Algebra R A]
    [Module.Free R A] : ∃ f : A →ₗ[R] R, f 1 = 1 :=
  (chooseBasis R A).span_repr_eq_top_iff.mp (chooseBasis R A).span_repr_one_eq_top

end Module.Free
