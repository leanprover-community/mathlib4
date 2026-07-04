/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie
-/

module

public import Mathlib.LinearAlgebra.Projectivization.Action

/-!
# Stabilizer of a line in PSL(n, F)
This file contains key constructions to prove that `PSL(n, F)` is simple via
showing it has an Iwasawa structure.

## Main definitions

* `Matrix.SpecialLinearGroup.lineStab` : the unipotent radical attached to a subspace `L ⊆ ι → F`
  defined as the subgroup of `SL ι F` consisting of matrices `A` such that `A - 1`
  sends every vector into `L`.

* `PSL.iwasawaT` : the candidate family of subgroups for the Iwasawa structure on
  `PSL ι F` acting on the projective space `ℙ F (ι → F)` from `Matrix.SpecialLinearGroup.lineStab`.

-/

@[expose] public section

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- The "unipotent radical" attached to a subspace `L ⊆ ι → F`: the subgroup of
`SL ι F` consisting of matrices `A` such that `A - 1` sends every vector into `L`.
When `L` is one-dimensional this is an abelian subgroup of the stabilizer of `L` in `SL`. -/
def Matrix.SpecialLinearGroup.lineStab (L : Submodule F (ι → F)) :
    Subgroup (SpecialLinearGroup ι F) where
  carrier := {A | ∀ w : ι → F, A • w - w ∈ L}
  one_mem' := by simp
  mul_mem' {A B} hA hB := fun w ↦ by
    simp only [Set.mem_setOf_eq, mul_smul] at hA hB ⊢
    rw [show A • B • w - w = ((A • (B • w) - A • w) - (B • w - w)) +
      (B • w - w) + (A • w - w) by abel, ← smul_sub]
    exact add_mem (add_mem (hA _) (hB w)) (hA w)
  inv_mem' {A} hA := fun w ↦ by
    convert neg_mem (hA (A⁻¹ • w)) using 1
    rw [← mul_smul, mul_inv_cancel, one_smul, neg_sub]

@[simp]
lemma Matrix.SpecialLinearGroup.mem_lineStab_iff (A : SpecialLinearGroup ι F)
    (L : Submodule F (ι → F)) : A ∈ lineStab L ↔ ∀ w : ι → F, A • w - w ∈ L :=
  Iff.rfl

open scoped LinearAlgebra.Projectivization

/-- The candidate family of subgroups for the Iwasawa structure on
`PSL ι F` acting on the projective space `ℙ F (ι → F)`: the unipotent radical
attached to the line through `p`. -/
noncomputable abbrev PSL.iwasawaT (p : ℙ F (ι → F)) :
    Subgroup (Matrix.ProjectiveSpecialLinearGroup ι F) :=
  Subgroup.map (QuotientGroup.mk' _)
    (Matrix.SpecialLinearGroup.lineStab p.submodule)

open scoped Pointwise

lemma PSL.smul_submodule (g : Matrix.SpecialLinearGroup ι F) (p : ℙ F (ι → F)) :
    (g • p).submodule = g • p.submodule:= by
  induction p using Projectivization.ind with | _ v hv => ?_
  simp [Submodule.ext_iff, Submodule.pointwise_smul_def, Submodule.mem_span_singleton, smul_comm]

/-- Equivariance of `lineStab` under conjugation by elements of `SL`. -/
lemma Matrix.SpecialLinearGroup.lineStab_smul
    (g : Matrix.SpecialLinearGroup ι F) (L : Submodule F (ι → F)) :
    Matrix.SpecialLinearGroup.lineStab (g • L) =
      MulAut.conj g • Matrix.SpecialLinearGroup.lineStab L := by
  ext A
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [mem_lineStab_iff, Submodule.mem_smul_pointwise_iff_exists, MulAut.smul_def,
    MulAut.inv_apply, MulAut.conj_symm_apply]
  refine ⟨fun hA w ↦ ?_, fun hA w ↦ ⟨g⁻¹ • (A • w - w), ?_, by simp⟩⟩
  · obtain ⟨v, hv, hvw⟩ := hA (g • w)
    simp_all [eq_comm (a := g • v), sub_eq_iff_eq_add, mul_smul]
  · simpa [mul_smul, smul_sub] using hA (g⁻¹ • w)

/-- The SL-level equivariance pushed through the quotient: the image in `PSL` of
the conjugate `MulAut.conj g_SL • H` equals `MulAut.conj (mk g_SL) • (image of H)`. -/
lemma PSL.iwasawaT_map_conj (g : Matrix.SpecialLinearGroup ι F)
    (H : Subgroup (Matrix.SpecialLinearGroup ι F)) :
    Subgroup.map (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup ι F)))
        (MulAut.conj g • H) =
      MulAut.conj (QuotientGroup.mk g : Matrix.ProjectiveSpecialLinearGroup ι F) •
        Subgroup.map (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup ι F))) H := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    MulAut.smul_def, MulAut.inv_apply, MulAut.conj_symm_apply, QuotientGroup.mk'_apply]
  exact ⟨fun ⟨a, ha, ha'⟩ ↦ ⟨g⁻¹ * a * g, ha, by simp [ha']⟩,
    fun ⟨a, ha, hx⟩ ↦ ⟨g * a * g⁻¹, by simp [mul_assoc, ha], by simp [hx, mul_assoc]⟩⟩

private lemma LinearMap.exists_restrict_span_singleton_eq_smul_id
    {R V : Type*} [CommSemiring R] [AddCommMonoid V] [Module R V]
    {v : V} {A : V →ₗ[R] V} (hAv : A v ∈ Submodule.span R {v}) :
    ∃ c : R, A v = c • v ∧ ∃ hcomap : Submodule.span R {v} ≤ (Submodule.span R {v}).comap A,
      A.restrict hcomap = (c • LinearMap.id : Submodule.span R {v} →ₗ[R] _) := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hAv
  refine ⟨c, hc.symm, fun w hw ↦ ?_, LinearMap.ext fun ⟨w, hw⟩ ↦ ?_⟩
  <;> obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
  · simpa [Submodule.mem_comap, map_smul] using Submodule.smul_mem _ _ hAv
  · simp [Subtype.ext_iff, ← hc, smul_comm a c v]

lemma Matrix.SpecialLinearGroup.lineStab_fix_of_span
    (v : ι → F) (hv : v ≠ 0)
    (A : Matrix.SpecialLinearGroup ι F)
    (hA : A ∈ lineStab (Submodule.span F {v})) :
    A • v = v := by
  set L : Submodule F (ι → F) := Submodule.span F {v}
  obtain ⟨c, hcv, hcomap, hres⟩ :=
    LinearMap.exists_restrict_span_singleton_eq_smul_id (A := A.toLin'.toLinearMap)
      (by simpa using! add_mem (hA v) (Submodule.mem_span_singleton_self v))
  have hQ : L.mapQ L A.toLin'.toLinearMap hcomap = LinearMap.id := LinearMap.ext fun x ↦ by
    induction x using Submodule.Quotient.induction_on with
    | _ w => simpa [Submodule.Quotient.eq] using! hA w
  have hdet := A.toLin'.toLinearMap.det_eq_det_mul_det L hcomap
  rw [show LinearMap.det A.toLin'.toLinearMap = 1 by simp [toLin'_to_linearMap],
      hres, hQ, LinearMap.det_smul, finrank_span_singleton hv, pow_one,
      LinearMap.det_id, LinearMap.det_id, mul_one, mul_one] at hdet
  exact hcv.trans (hdet ▸ one_smul F v)

/-- The subgroup `lineStab (span F {v})` is commutative when `v ≠ 0`. -/
lemma Matrix.SpecialLinearGroup.lineStab_isMulCommutative_of_span'
    (v : ι → F) (hv : v ≠ 0) (A B : SpecialLinearGroup ι F)
    (hA : A ∈ SpecialLinearGroup.lineStab (Submodule.span F {v}))
    (hB : B ∈ SpecialLinearGroup.lineStab (Submodule.span F {v})) :
    A * B = B * A := by
  refine Subtype.ext <| ext_iff_smul.2 fun w ↦ ?_
  obtain ⟨α, hα⟩ := Submodule.mem_span_singleton.mp (hA w)
  obtain ⟨β, hβ⟩ := Submodule.mem_span_singleton.mp (hB w)
  simp only [coe_mul, mul_smul, ← Matrix.SpecialLinearGroup.smul_def]
  rw [← sub_add_cancel (A • w) w, ← hα, ← sub_add_cancel (B • w) w,
    ← hβ, smul_add, smul_add, ← sub_left_inj (a := w), ← add_sub, ← hα, ← add_sub, ← hβ,
    smul_comm, lineStab_fix_of_span v hv A hA, smul_comm, lineStab_fix_of_span v hv B hB, add_comm]

lemma Matrix.SpecialLinearGroup.lineStab_isMulCommutative_of_span
    (v : ι → F) (hv : v ≠ 0) : IsMulCommutative (lineStab (Submodule.span F {v})) :=
  ⟨⟨fun ⟨A, hA⟩ ⟨B, hB⟩ ↦ by simpa using lineStab_isMulCommutative_of_span' v hv A B hA hB⟩⟩
