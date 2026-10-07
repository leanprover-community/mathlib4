/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie
-/
module

public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
public import Mathlib.GroupTheory.IsPerfect

/-!
# Simplicity of `PSLₙ(F)` (general case)

This file develops the general Iwasawa-style proof that
`PSL ι F = SL ι F / Z(SL ι F)` is a simple group whenever the
"non-degenerate" hypothesis holds:

* `Fintype.card ι ≥ 3`, **or**
* `Fintype.card ι = 2` and `|F| ≥ 4` (already handled in
  `Mathlib/LinearAlgebra/Projectivization/PSL/PSL2.lean`).

The proof follows the standard outline:

1. `SL ι F` acts on the projective space `ℙ F (ι → F)` and the action
   factors through `PSL ι F`, with kernel the centre.
2. The induced action of `PSL ι F` on `ℙ F (ι → F)` is `2`-transitive
   and hence primitive (and quasi-preprimitive).
3. For every line `p ∈ ℙ F (ι → F)` the unipotent radical of its
   stabiliser - the subgroup `Matrix.SpecialLinearGroup.lineStab p.submodule`
   of `SL ι F` fixing `p` and acting trivially on `(ι → F) / p` - is abelian
   and the union of its conjugates generates `SL ι F`.
4. `SL ι F` is perfect for `Fintype.card ι ≥ 3` over any field, and
   for `Fintype.card ι = 2` over any field with `|F| ≥ 4`.
5. Applying `MulAction.IwasawaStructure.isSimpleGroup` to the image of
   the line-stabilisers in `PSL ι F` yields simplicity.

The key computational ingredient is the Whitehead identity
`Matrix.SpecialLinearGroup.diag2n_eq_elemDiagSL`, expressing an
elementary diagonal matrix as a product of six transvections
(setting `U(b) := 1 + b·E_{i,j}`, `L(b) := 1 + b·E_{j,i}`):

`diag_{ij}(α) = U(α) · L(-α⁻¹) · U(α) · U(-1) · L(1) · U(-1)`.

The `Fintype.card ι = 2` case of the final statement is transported from
`Matrix.ProjectiveSpecialLinearGroup.rank_two_simple'` along the reindexing
isomorphism `PSL ι F ≃* PSL(2, F)`.
-/

@[expose] public section

open scoped LinearAlgebra.Projectivization Matrix Pointwise

open Projectivization MulAction Matrix Matrix.SpecialLinearGroup

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι] [Fintype ι]

namespace SLnSimple

open scoped commutatorElement

/-- For any nontrivial `ι`, the line-stabilisers `Matrix.SpecialLinearGroup.lineStab p.submodule`
generate the whole of `SL ι F`.

Every element of `SL ι F` is a product of transvections and elementary diagonals
(`Matrix.SpecialLinearGroup.diagonal_transvection_induction'`); transvections lie in the
line-stabiliser of a coordinate axis, and the elementary diagonals are products of transvections
by the Whitehead decomposition `Matrix.SpecialLinearGroup.diag2n_eq_elemDiagSL`. -/
lemma iSup_lineStab_eq_top [Nontrivial ι] :
    ⨆ p : ℙ F (ι → F), lineStab p.submodule = ⊤ := by
  rw [eq_top_iff]
  rintro M -
  refine diagonal_transvection_induction' _ M ?_ (fun i j hij a ↦ ?_)
    fun A B hA hB ↦ mul_mem hA hB
  · intro i j hij c hc
    rw [diag2n_eq_elemDiagSL hij c hc]
    exact elemDiagSL_mem_iSup_lineStab hij c
  · exact le_iSup (fun p : ℙ F (ι → F) ↦ lineStab p.submodule)
      (.mk F (Pi.single i 1) (Pi.single_ne_zero_iff.2 one_ne_zero)) <| by
      rw [Projectivization.submodule_mk]
      exact transvection_mem_lineStab hij a

lemma transvection_eq_commutator (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) (hkj : k ≠ j) (α : F) :
    transvection hij α = ⁅transvection hik α, transvection hkj (1 : F)⁆ := by
  rw [commutatorElement_def, transvection_inv, transvection_inv]
  refine Subtype.ext ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, transvection_coe, mul_add, add_mul, one_mul,
    mul_one, ← single_neg, mul_neg, neg_mul, add_zero, single_mul_single_same,
    single_mul_single_of_ne _ _ _ _ hij.symm, single_mul_single_of_ne _ _ _ _ hik.symm,
    single_mul_single_of_ne _ _ _ _ hkj.symm]
  abel

omit [DecidableEq ι] in
/-- Given `card ι ≥ 3` and `i, j : ι` (not necessarily distinct), there
exists `k : ι` distinct from both. -/
lemma exists_third_index_of_three_le (hι : 3 ≤ Fintype.card ι) (i j : ι) :
    ∃ k : ι, k ≠ i ∧ k ≠ j := by
  classical
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := {i, j}) (t := .univ) <|
    Finset.card_le_two.trans_lt (by rw [Finset.card_univ]; omega)
  exact ⟨k, by simpa [not_or] using hk⟩

/-- For `Fintype.card ι ≥ 3` and any `i ≠ j`, the transvection
`transvection hij α` belongs to the commutator subgroup of `SL ι F`. -/
private lemma transvection_mem_commutator_of_three_le (hι : 3 ≤ Fintype.card ι) (i j : ι)
    (hij : i ≠ j) (α : F) : transvection hij α ∈ commutator (Matrix.SpecialLinearGroup ι F) := by
  obtain ⟨k, hki, hkj⟩ := exists_third_index_of_three_le hι i j
  rw [transvection_eq_commutator i j k hij hki.symm hkj α]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- For `Fintype.card ι ≥ 3`, every elementary diagonal (built via `elemDiagSL`)
lies in the commutator subgroup. -/
private lemma elemDiagSL_mem_commutator_of_three_le (hι : 3 ≤ Fintype.card ι) {i j : ι}
    (hij : i ≠ j) (α : F) : elemDiagSL hij α ∈ commutator (Matrix.SpecialLinearGroup ι F) :=
  have h := transvection_mem_commutator_of_three_le (F := F) hι
  mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (h i j hij α) (h j i hij.symm _)) (h i j hij α))
    (h i j hij (-1))) (h j i hij.symm 1)) (h i j hij (-1))

/-- `commutator (SL ι F) = ⊤` when `Fintype.card ι ≥ 3` (no condition on `F`
beyond being a field). -/
lemma commutator_SL_eq_top_of_three_le_card (hι : 3 ≤ Fintype.card ι) :
    commutator (Matrix.SpecialLinearGroup ι F) = ⊤ := by
  ext M
  simp only [Subgroup.mem_top, iff_true]
  have : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  refine diagonal_transvection_induction' _ M ?_
    (transvection_mem_commutator_of_three_le hι) fun A B hA hB ↦ mul_mem hA hB
  intro i j hij c hc
  rw [diag2n_eq_elemDiagSL hij c hc]
  exact elemDiagSL_mem_commutator_of_three_le hι hij c

/-- `commutator (PSL ι F) = ⊤` when `Fintype.card ι ≥ 3`. -/
lemma commutator_PSL_eq_top_of_three_le_card (hι : 3 ≤ Fintype.card ι) :
    commutator (Matrix.ProjectiveSpecialLinearGroup ι F) = ⊤ :=
  have : Group.IsPerfect (Matrix.SpecialLinearGroup ι F) :=
    ⟨commutator_SL_eq_top_of_three_le_card hι⟩
  Group.IsPerfect.commutator_eq_top

/-! ### Iwasawa structure -/

/-- The Iwasawa data on `PSL ι F` (acting on `ℙ F (ι → F)`) coming
from the images of the line-stabilisers. -/
noncomputable def PSL.Iwasawa [Nontrivial ι] :
    IwasawaStructure (Matrix.ProjectiveSpecialLinearGroup ι F) (ℙ F (ι → F)) where
  T := PSL.iwasawaT
  is_comm p :=
    have : IsMulCommutative (lineStab (F := F) (ι := ι) p.submodule) :=
      p.submodule_eq.symm ▸ lineStab_isMulCommutative_of_span p.rep p.rep_nonzero
    Subgroup.map_isMulCommutative _ _
  is_conj g p := by
    induction g using QuotientGroup.induction_on with | H g =>
    induction p with | h v h =>
    simp [Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk, PSL.iwasawaT, ← PSL.iwasawaT_map_conj,
      ← lineStab_smul, Submodule.pointwise_smul_def, Subgroup.ext_iff,
      Submodule.mem_span_singleton, smul_comm]
  is_generator := by
    rw [← Subgroup.map_iSup, iSup_lineStab_eq_top]
    exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

end SLnSimple

/-- **The PSLₙ simplicity theorem (`n ≥ 3` case)**: when
`Fintype.card ι ≥ 3`, the group `PSL ι F` is simple for every field `F`. -/
theorem Matrix.ProjectiveSpecialLinearGroup.isSimpleGroup_of_three_le (hι : 3 ≤ Fintype.card ι) :
    IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup ι F) :=
  have : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  MulAction.IwasawaStructure.isSimpleGroup
    (SLnSimple.commutator_PSL_eq_top_of_three_le_card hι) SLnSimple.PSL.Iwasawa inferInstance
