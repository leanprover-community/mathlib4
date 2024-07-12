/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Sym.Sym2.Order

/-!
# Constructing a bilinear form from a quadratic form, given a basis

This file provides an alternative to `QuadraticForm.associated`; unlike that definition, this one
does not require `Invertible (2 : R)`. Unlike that definition, this only works in the presence of
a basis.
-/

-- TODO: move
theorem Finset.sum_sym2_filter_not_isDiag {ι α} [LinearOrder ι] [AddCommMonoid α]
    (s : Finset ι) (p : Sym2 ι → α) :
    ∑ i in s.sym2.filter (¬ ·.IsDiag), p i =
      ∑ i in s.offDiag.filter (fun i => i.1 < i.2), p s(i.1, i.2) := by
  rw [Finset.offDiag_filter_lt_eq_filter_le]
  conv_rhs => rw [← Finset.sum_subtype_eq_sum_filter]
  refine (Finset.sum_equiv Sym2.sortEquiv.symm ?_ ?_).symm
  · rintro ⟨⟨i₁, j₁⟩, hij₁⟩
    simp [and_assoc]
  · rintro ⟨⟨i₁, j₁⟩, hij₁⟩
    simp

namespace QuadraticForm

variable {ι R M} [LinearOrder ι] [CommRing R] [AddCommGroup M] [Module R M]

/-- Given an ordered basis, produce a bilinear form associated with the quadratic form.

Unlike `QuadraticForm.associated`, this is not symmetric; however, as a result it can be used even
in characteristic two. When considered as a matrix, the form is triangular. -/
noncomputable def toBilin (Q : QuadraticForm R M) (bm : Basis ι R M) : LinearMap.BilinForm R M :=
  bm.constr (S := R) fun i =>
    bm.constr (S := R) fun j =>
      if i = j then Q (bm i) else if i < j then polar Q (bm i) (bm j) else 0

theorem toBilin_apply (Q : QuadraticForm R M) (bm : Basis ι R M) (i j : ι) :
    Q.toBilin bm (bm i) (bm j) =
      if i = j then Q (bm i) else if i < j then polar Q (bm i) (bm j) else 0 := by
  simp [toBilin]

theorem toQuadraticForm_toBilin (Q : QuadraticForm R M) (bm : Basis ι R M) :
    (Q.toBilin bm).toQuadraticForm = Q := by
  ext x
  rw [← bm.total_repr x, LinearMap.BilinForm.toQuadraticForm_apply, Finsupp.total_apply,
    Finsupp.sum]
  simp_rw [LinearMap.map_sum₂, map_sum, LinearMap.map_smul₂, _root_.map_smul, toBilin_apply,
    smul_ite, smul_zero, ← Finset.sum_product', ← Finset.diag_union_offDiag,
    Finset.sum_union (Finset.disjoint_diag_offDiag _), Finset.sum_diag, if_true]
  rw [Finset.sum_ite_of_false, QuadraticForm.map_sum, ← Finset.sum_filter]
  · simp_rw [smul_eq_mul, ← polar_smul_right _ (bm.repr x <| Prod.snd _),
      ← polar_smul_left _ (bm.repr x <| Prod.fst _)]
    simp_rw [QuadraticForm.map_smul, ← mul_assoc, Finset.sum_sym2_filter_not_isDiag]
    rfl
  · intro x hx
    rw [Finset.mem_offDiag] at hx
    simpa using hx.2.2

/-- In a free module, every quadratic form can be built from a bilinear form.

See `QuadraticForm.not_forall_toQuadraticForm_surjective` for a counterexample when the module is
not free. -/
theorem toQuadraticForm_surjective [Module.Free R M] :
    Function.Surjective (LinearMap.BilinForm.toQuadraticForm : LinearMap.BilinForm R M → _) := by
  intro Q
  obtain ⟨ι, b⟩ := Module.Free.exists_basis (R := R) (M := M)
  letI : LinearOrder ι := IsWellOrder.linearOrder WellOrderingRel
  exact ⟨_, toQuadraticForm_toBilin _ b⟩

end QuadraticForm
