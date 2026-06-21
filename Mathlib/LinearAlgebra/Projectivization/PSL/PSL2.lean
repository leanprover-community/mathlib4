/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie
-/
module

public import Mathlib.GroupTheory.GroupAction.Iwasawa
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.LinearAlgebra.Projectivization.PSL.Stabilizer

/-!
-/

@[expose] public section

variable {ι F : Type*} [Field F] [DecidableEq ι] [Fintype ι]

open Matrix Matrix.SpecialLinearGroup

open scoped MatrixGroups

namespace SL2Gen

/-- A transvection `transvection i j hij b` lies in `lineStab (span F {Pi.single i 1})`. -/
lemma transvection_mem_lineStab (i j : ι) (hij : i ≠ j) (b : F) :
    transvection hij b ∈ lineStab (Submodule.span F {(Pi.single i (1 : F) : ι → F)}) :=
  fun w ↦ Submodule.mem_span_singleton.2 ⟨b * w j, by simp [mul_smul,
    Matrix.SpecialLinearGroup.smul_def, transvection_coe, add_smul, Matrix.single_mulVec_eq]⟩

/-- Every transvection in `SL ι F` whose indices are `(i₁, i₂)` or `(i₂, i₁)` is in the join
of `lineStab(span F {e_{i₁}})` and `lineStab(span F {e_{i₂}})`. -/
lemma transvection_mem_lineStab_sup (t : TransvectionStruct (Fin 2) F) :
    t.toSpecialLinearGroup ∈
      lineStab (Submodule.span F {(Pi.single 0 1 : Fin 2 → F)})
      ⊔ lineStab (Submodule.span F {(Pi.single 1 1 : Fin 2 → F)}) := by
  obtain ⟨i, j, hij, c⟩ := t
  simp only [Fin.isValue, TransvectionStruct.toSpecialLinearGroup_mk]
  fin_cases i <;> fin_cases j <;> try tauto
  · exact Subgroup.mem_sup_left <| transvection_mem_lineStab 0 1 zero_ne_one c
  · exact Subgroup.mem_sup_right <| transvection_mem_lineStab 1 0 one_ne_zero c

/-- SL-level generation: in the 2-element-index case, the join of the two `lineStab` subgroups
attached to the two coordinate axes is all of `SL ι F`. -/
lemma SL_card_two_lineStab_sup_eq_top :
    lineStab (Submodule.span F {(Pi.single 0 1: Fin 2 → F)}) ⊔
      lineStab (Submodule.span F {(Pi.single 1 1: Fin 2 → F)}) =
      (⊤ : Subgroup SL(2, F)) :=
  le_antisymm le_top fun M _ ↦ SL2.transvection_induction _
      (fun i j hij a ↦ by simpa using transvection_mem_lineStab_sup ⟨i, j, hij, a⟩)
      (fun _ _ ↦ mul_mem) M

end SL2Gen

open scoped LinearAlgebra.Projectivization

/-- At the SL level: when `Fintype.card ι = 2`, the supremum over all projective points of
the `lineStab` subgroups equals `⊤` in `SL ι F`. -/
lemma PSL.iSup_lineStab_eq_top :
    (⨆ p : ℙ F (Fin 2 → F), lineStab p.submodule) = (⊤ : Subgroup SL(2, F)) := by
  refine le_antisymm le_top (SL2Gen.SL_card_two_lineStab_sup_eq_top (F := F) ▸
    sup_le ?_ ?_)
  <;> rw [← Projectivization.submodule_mk (K := F) _ (Pi.single_ne_zero_iff.2 one_ne_zero)]
  <;> exact le_iSup_iff.2 fun b a ↦ a _

/-- The Iwasawa generator property: when `Fintype.card ι = 2`, the supremum of the
`iwasawaT` subgroups equals all of `PSL`. -/
lemma PSL.iSup_iwasawaT_eq_top :
    iSup (PSL.iwasawaT (F := F) (ι := Fin 2)) = ⊤ := by
  have step1 : iSup (PSL.iwasawaT (F := F) (ι := Fin 2)) =
      Subgroup.map (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)))
        (⨆ p : ℙ F (Fin 2 → F),
          Matrix.SpecialLinearGroup.lineStab (F := F) (ι := Fin 2) p.submodule) := by
    rw [Subgroup.map_iSup]
  rw [step1, PSL.iSup_lineStab_eq_top]
  exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

open MulAction

/-- The Iwasawa structure on PSL(2, F). -/
noncomputable abbrev PSL2.Iwasawa : IwasawaStructure PSL(2, F) (ℙ F (Fin 2 → F)) where
  T := PSL.iwasawaT
  is_comm p := by
    have hSL : IsMulCommutative (lineStab (F := F) (ι := Fin 2) p.submodule) := by
      rw [← Projectivization.mk_rep p, Projectivization.submodule_mk]
      exact lineStab_isMulCommutative_of_span p.rep p.rep_nonzero
    exact Subgroup.map_isMulCommutative _ _
  is_conj g p := by
    obtain ⟨g_SL, rfl⟩ := QuotientGroup.mk_surjective g
    rw [Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk]
    change Subgroup.map _ _ = _
    rw [PSL.smul_submodule, Matrix.SpecialLinearGroup.lineStab_smul,
      PSL.iwasawaT_map_conj]
  is_generator := PSL.iSup_iwasawaT_eq_top

namespace SL2Simple

open Matrix.SpecialLinearGroup

/-- `commutator (PSL ι F) = ⊤`. -/
lemma PSL_commutator_eq_top (hF : ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1) :
    commutator PSL(2, F) = ⊤ := by
  obtain ⟨a, ha, hasq⟩ := hF
  haveI : Group.IsPerfect SL(2, F) := ⟨SL2.commutator_eq_top a ha hasq⟩
  have : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := inferInstance
  exact this.commutator_eq_top

/-- `PSL ι F` is nontrivial whenever `ι` has at least two elements (and `F` is a field,
hence in particular nontrivial). -/
instance PSL_nontrivial [Nontrivial ι] :
    Nontrivial (Matrix.ProjectiveSpecialLinearGroup ι F) := by
  obtain ⟨i₁, i₂, hij⟩ := exists_pair_ne ι
  set g : Matrix.SpecialLinearGroup ι F := transvection hij 1
  refine ⟨⟨(QuotientGroup.mk g : Matrix.ProjectiveSpecialLinearGroup ι F),
    1, fun h ↦ one_ne_zero (α := F) ?_⟩⟩
  rwa [QuotientGroup.eq_one_iff, transvection_mem_center_iff] at h

end SL2Simple

theorem Matrix.ProjectiveSpecialLinearGroup.rank_two_simple'
    (hF : ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1) :
    IsSimpleGroup PSL(2, F) :=
  MulAction.IwasawaStructure.isSimpleGroup
    (SL2Simple.PSL_commutator_eq_top hF) PSL2.Iwasawa inferInstance

private lemma field_cond_of_four_le_card (hF : 4 ≤ Nat.card F) :
    ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1 := by
  have : Finite F := (Nat.card_pos_iff.1 (by omega)).2
  obtain ⟨x, hx⟩ : IsCyclic Fˣ := by infer_instance
  refine ⟨x, Units.ne_zero x, fun h ↦ ?_⟩
  grw [Nat.card_eq_card_units_add_one F, ← orderOf_eq_card_of_forall_mem_zpowers hx,
    orderOf_le_of_pow_eq_one zero_lt_two (Units.ext <| by simpa using h)] at hF
  omega

theorem Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (hF : 4 ≤ Nat.card F) :
    IsSimpleGroup PSL(2, F) :=
  Matrix.ProjectiveSpecialLinearGroup.rank_two_simple' (field_cond_of_four_le_card hF)
