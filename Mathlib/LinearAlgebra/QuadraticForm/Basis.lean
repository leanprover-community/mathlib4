/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.BigOperators.Sym
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Constructing a bilinear map from a quadratic map, given a basis

This file provides an alternative to `QuadraticMap.associated`; unlike that definition, this one
does not require `Invertible (2 : R)`. Unlike that definition, this only works in the presence of
a basis.
-/

open LinearMap (BilinMap)

namespace QuadraticMap

section

variable {ι R M N}

variable [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] [DecidableEq ι]

open Finsupp in
theorem map_finsuppSum (Q : QuadraticMap R M N) (f : ι →₀ R) (g : ι → R → M) :
    Q (f.sum g) = (f.sum fun i r => Q (g i r)) +
    ∑ p ∈ f.support.sym2 with ¬ p.IsDiag,
      Sym2.lift
        ⟨fun i j => (polar Q) (g i (f i)) (g j (f j)), fun i j => by simp only [polar_comm]⟩ p := by
  rw [sum, QuadraticMap.map_sum]
  exact congrArg (HAdd.hAdd _) rfl

open Finsupp in
theorem map_linearCombination (Q : QuadraticMap R M N) {g : ι → M} (l : ι →₀ R) :
    Q (linearCombination R g l) = (l.sum fun i r => (r * r) • Q (g i)) +
    ∑ p ∈ l.support.sym2 with ¬ p.IsDiag,
      Sym2.lift
        ⟨fun i j => (l i) • (l j) • (polar Q) (g i) (g j), fun i j => by
          simp only [polar_comm]
          rw [smul_comm]⟩ p := by
  simp_rw [linearCombination_apply, map_finsupp_sum,
    polar_smul_left, polar_smul_right, map_smul]

theorem basis_expansion (Q : QuadraticMap R M N) (bm : Basis ι R M) (x : M) :
    Q x = ((bm.repr x).sum fun i r => (r * r) • Q (bm i)) +
    ∑ p ∈ (bm.repr x).support.sym2 with ¬ p.IsDiag,
      Sym2.lift
        ⟨fun i j => ((bm.repr x) i) • ((bm.repr x) j) • (polar Q) (bm i) (bm j), fun i j => by
          simp only [polar_comm]
          rw [smul_comm]⟩ p := by
  rw [← map_finsupp_linearCombination, Basis.linearCombination_repr]

end

variable {ι R M N}  [LinearOrder ι]
variable [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

/-- Given an ordered basis, produce a bilinear form associated with the quadratic form.

Unlike `QuadraticMap.associated`, this is not symmetric; however, as a result it can be used even
in characteristic two. When considered as a matrix, the form is triangular. -/
noncomputable def toBilin (Q : QuadraticMap R M N) (bm : Basis ι R M) : LinearMap.BilinMap R M N :=
  bm.constr (S := R) fun i =>
    bm.constr (S := R) fun j =>
      if i = j then Q (bm i) else if i < j then polar Q (bm i) (bm j) else 0

theorem toBilin_apply (Q : QuadraticMap R M N) (bm : Basis ι R M) (i j : ι) :
    Q.toBilin bm (bm i) (bm j) =
      if i = j then Q (bm i) else if i < j then polar Q (bm i) (bm j) else 0 := by
  simp [toBilin]

theorem toQuadraticMap_toBilin (Q : QuadraticMap R M N) (bm : Basis ι R M) :
    (Q.toBilin bm).toQuadraticMap = Q := by
  ext x
  rw [← bm.linearCombination_repr x, LinearMap.BilinMap.toQuadraticMap_apply,
      Finsupp.linearCombination_apply, Finsupp.sum]
  simp_rw [LinearMap.map_sum₂, map_sum, LinearMap.map_smul₂, _root_.map_smul, toBilin_apply,
    smul_ite, smul_zero, ← Finset.sum_product', ← Finset.diag_union_offDiag,
    Finset.sum_union (Finset.disjoint_diag_offDiag _), Finset.sum_diag, if_true]
  rw [Finset.sum_ite_of_false, QuadraticMap.map_sum, ← Finset.sum_filter]
  · simp_rw [← polar_smul_right _ (bm.repr x <| Prod.snd _),
      ← polar_smul_left _ (bm.repr x <| Prod.fst _)]
    simp_rw [QuadraticMap.map_smul, mul_smul, Finset.sum_sym2_filter_not_isDiag]
    rfl
  · intro x hx
    rw [Finset.mem_offDiag] at hx
    simpa using hx.2.2

/-- From a free module, every quadratic map can be built from a bilinear form.

See `BilinMap.not_forall_toQuadraticMap_surjective` for a counterexample when the module is
not free. -/
theorem _root_.LinearMap.BilinMap.toQuadraticMap_surjective [Module.Free R M] :
    Function.Surjective (LinearMap.BilinMap.toQuadraticMap : LinearMap.BilinMap R M N → _) := by
  intro Q
  obtain ⟨ι, b⟩ := Module.Free.exists_basis (R := R) (M := M)
  letI : LinearOrder ι := IsWellOrder.linearOrder WellOrderingRel
  exact ⟨_, toQuadraticMap_toBilin _ b⟩

@[simp]
lemma add_toBilin (bm : Basis ι R M) (Q₁ Q₂ : QuadraticMap R M N) :
    (Q₁ + Q₂).toBilin bm = Q₁.toBilin bm + Q₂.toBilin bm := by
  refine bm.ext fun i => bm.ext fun j => ?_
  obtain h | rfl | h := lt_trichotomy i j
  · simp [h.ne, h, toBilin_apply, polar_add]
  · simp [toBilin_apply]
  · simp [h.ne', h.not_lt, toBilin_apply, polar_add]

variable (S) [CommSemiring S] [Algebra S R]
variable [Module S N] [IsScalarTower S R N]

@[simp]
lemma smul_toBilin (bm : Basis ι R M) (s : S) (Q : QuadraticMap R M N) :
    (s • Q).toBilin bm = s • Q.toBilin bm := by
  refine bm.ext fun i => bm.ext fun j => ?_
  obtain h | rfl | h := lt_trichotomy i j
  · simp [h.ne, h, toBilin_apply, polar_smul]
  · simp [toBilin_apply]
  · simp [h.ne', h.not_lt, toBilin_apply]

/-- `QuadraticMap.toBilin` as an S-linear map -/
@[simps]
noncomputable def toBilinHom (bm : Basis ι R M) : QuadraticMap R M N →ₗ[S] BilinMap R M N where
  toFun Q := Q.toBilin bm
  map_add' := add_toBilin bm
  map_smul' := smul_toBilin S bm

lemma toBilin_symm_eq_Polar (Q : QuadraticMap R M N) (bm : Basis ι R M) :
    (Q.toBilin bm) + (Q.toBilin bm).flip = polarBilin Q := by
  ext a b
  conv_rhs => rw [← toQuadraticMap_toBilin Q bm]
  simp only [toQuadraticMap_toBilin]
  symm
  calc Q (a + b) - Q a - Q b = (Q.toBilin bm).toQuadraticMap (a + b) - Q a - Q b := by
        rw [ toQuadraticMap_toBilin Q]
  _ = (((Q.toBilin bm) a a + (Q.toBilin bm) b a) + (Q.toBilin bm) (a + b) b) - Q a - Q b := by
    rw [LinearMap.BilinMap.toQuadraticMap_apply, map_add, map_add, LinearMap.add_apply]
  _ = (((Q.toBilin bm).toQuadraticMap a + (Q.toBilin bm) b a) + (Q.toBilin bm) (a + b) b) - Q a
    - Q b := by rw [LinearMap.BilinMap.toQuadraticMap_apply]
  _ = ((Q a + (Q.toBilin bm) b a) + (Q.toBilin bm) (a + b) b) - Q a - Q b := by
    rw [ toQuadraticMap_toBilin Q]
  _ = ((Q a + (Q.toBilin bm) b a) + ((Q.toBilin bm) a b + (Q.toBilin bm).toQuadraticMap b)) - Q a
    - Q b := by rw [map_add, LinearMap.add_apply,
      LinearMap.BilinMap.toQuadraticMap_apply (Q.toBilin bm) b]
  _ = ((Q a + (Q.toBilin bm) b a) + ((Q.toBilin bm) a b + Q b)) - Q a - Q b := by
    rw [ toQuadraticMap_toBilin Q]
  _ = ((Q.toBilin bm) a) b + ((Q.toBilin bm) b) a := by abel

lemma polar_toQuadraticMap (B : BilinMap R M N) (x y : M) :
    polar B.toQuadraticMap x y = B x y + B y x := by
  simp only [polar, BilinMap.toQuadraticMap_apply, map_add, LinearMap.add_apply]
  abel

lemma polarBilin_toQuadraticMap (B : BilinMap R M N) :
    polarBilin B.toQuadraticMap = B + B.flip := by
  ext x y
  simp only [polarBilin_apply_apply, polar_toQuadraticMap, LinearMap.add_apply,
    LinearMap.flip_apply]

theorem toBilin_toQuadraticMap (B : BilinMap R M N) (bm : Basis ι R M) (x y : M) :
    let s := (bm.repr x).support ∪ (bm.repr y).support
    B.toQuadraticMap.toBilin bm x y =
      (∑ i ∈ s,
        ((bm.repr x) i) •((bm.repr y) i) • B (bm i) (bm i)) +
      ∑ p ∈ Finset.filter (fun p ↦ p.1 < p.2) s.offDiag,
        ((bm.repr x) p.1) • ((bm.repr y) p.2) • (B + B.flip) (bm p.1) (bm p.2) := by
  simp_rw [toBilin, polar_toQuadraticMap, BilinMap.toQuadraticMap_apply]
  let s := (bm.repr x).support ∪ (bm.repr y).support
  conv_lhs => rw [← bm.linearCombination_repr x, Finsupp.linearCombination_apply,
    Finsupp.sum_of_support_subset (s := s) (bm.repr x) Finset.subset_union_left _
      (fun i _ ↦ zero_smul R (bm i))]
  conv_lhs =>  rw [← bm.linearCombination_repr y, Finsupp.linearCombination_apply,
    Finsupp.sum_of_support_subset (s := s) (bm.repr y) Finset.subset_union_right _
      (fun i _ ↦ zero_smul R (bm i))]
  simp_rw [LinearMap.map_sum₂, map_sum, LinearMap.map_smul₂, _root_.map_smul,
    ← Finset.sum_product', ← Finset.diag_union_offDiag s,
    Finset.sum_union (Finset.disjoint_diag_offDiag _), Finset.sum_diag]
  simp only [Basis.constr_basis, ↓reduceIte, smul_ite, smul_add, smul_zero, add_right_inj]
  rw [Finset.sum_ite_of_false (by aesop) _ _, ← Finset.sum_filter]
  simp_rw [LinearMap.add_apply, LinearMap.flip_apply, smul_add]
  simp only [Finset.subset_union_left, Finset.subset_union_right, s]

end QuadraticMap
