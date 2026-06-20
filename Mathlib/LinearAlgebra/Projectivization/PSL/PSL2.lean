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

open Matrix.SpecialLinearGroup in
/-- Every transvection in `SL ι F` whose indices are `(i₁, i₂)` or `(i₂, i₁)` is in the join
of `lineStab(span F {e_{i₁}})` and `lineStab(span F {e_{i₂}})`. -/
lemma transvection_mem_lineStab_sup (t : Matrix.TransvectionStruct (Fin 2) F) :
    ∃ A : SL(2, F), A.1 = t.toMatrix ∧
      A ∈ lineStab (Submodule.span F {(Pi.single 0 1 : Fin 2 → F)})
        ⊔ lineStab (Submodule.span F {(Pi.single 1 1 : Fin 2 → F)}) := by
  obtain ⟨i, j, hij_t, c⟩ := t
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij_t
  · exact ⟨transvection zero_ne_one c, rfl,
      Subgroup.mem_sup_left <| transvection_mem_lineStab 0 1 zero_ne_one c⟩
  · exact ⟨transvection one_ne_zero c, rfl,
      Subgroup.mem_sup_right <| transvection_mem_lineStab 1 0 one_ne_zero c⟩
  · exact absurd rfl hij_t

/-- The diagonal `SL` element with entries `α` and `α⁻¹` (at positions `i₁` and `i₂`)
is a product of six transvections, all of which lie in `U₁ ⊔ U₂`.

Uses the formula `D(α) = U(α) · L(-α⁻¹) · U(α) · U(-1) · L(1) · U(-1)`, which is
the Steinberg/Bruhat decomposition of the diagonal element. -/
lemma diag_alpha_in_lineStab_sup (i₁ i₂ : ι) (hij : i₁ ≠ i₂) (α : F) (hα : α ≠ 0) :
    ∃ A : Matrix.SpecialLinearGroup ι F,
      A.1 *ᵥ Pi.single i₁ 1 = α • Pi.single i₁ (1 : F) ∧
      A.1 *ᵥ Pi.single i₂ 1 = α⁻¹ • Pi.single i₂ (1 : F) ∧
      A ∈ Matrix.SpecialLinearGroup.lineStab
            (Submodule.span F {(Pi.single i₁ (1 : F) : ι → F)})
        ⊔ Matrix.SpecialLinearGroup.lineStab
            (Submodule.span F {(Pi.single i₂ (1 : F) : ι → F)}) := by
  -- U(b) = transvection i₁ i₂ b ∈ lineStab(span F {e_{i₁}})
  -- L(b) = transvection i₂ i₁ b ∈ lineStab(span F {e_{i₂}})
  set U : F → Matrix.SpecialLinearGroup ι F := fun b => transvection hij b with hU_def
  set L : F → Matrix.SpecialLinearGroup ι F := fun b => transvection hij.symm b with hL_def
  -- A = U(α) · L(-α⁻¹) · U(α) · U(-1) · L(1) · U(-1)
  let A : Matrix.SpecialLinearGroup ι F :=
    U α * L (-α⁻¹) * U α * U (-1) * L 1 * U (-1)
  refine ⟨A, ?_, ?_, ?_⟩
  · ext j
    simp [A, U, L, transvection_coe, add_mul, mul_add, Pi.single_apply]
    split_ifs with hi1
    · simp [hi1, mul_inv_cancel₀ hα, Matrix.one_apply, hij, hij.symm]
    · simp [hi1, hij, hij.symm, mul_inv_cancel₀ hα, Matrix.single_apply]
      grind
  · ext j
    simp [A, U, L, transvection_coe, add_mul, mul_add, Pi.single_apply]
    split_ifs with hi2
    · simp [hi2, mul_inv_cancel₀ hα, Matrix.one_apply, hij, hij.symm, inv_mul_cancel₀ hα]
    · simp [hi2, Matrix.single_apply, hij]
      grind
  · refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ (Subgroup.mem_sup_right
      (transvection_mem_lineStab i₂ i₁ hij.symm _))) ?_) ?_) (Subgroup.mem_sup_right
      (transvection_mem_lineStab i₂ i₁ hij.symm _))) ?_
    <;> exact Subgroup.mem_sup_left (transvection_mem_lineStab i₁ i₂ hij _)

/-- SL-level generation: in the 2-element-index case, the join of the two `lineStab` subgroups
attached to the two coordinate axes is all of `SL ι F`. -/
lemma SL_card_two_lineStab_sup_eq_top :
    Matrix.SpecialLinearGroup.lineStab
        (Submodule.span F {(Pi.single 0 1: Fin 2 → F)})
      ⊔ Matrix.SpecialLinearGroup.lineStab
        (Submodule.span F {(Pi.single 1 1: Fin 2 → F)})
      = (⊤ : Subgroup SL(2, F)) := by
  -- Define the goal as a property of plain matrices via `diagonal_transvection_induction`.
  set U₁ : Subgroup SL(2, F) := lineStab
      (Submodule.span F {(Pi.single 0 (1 : F) : Fin 2 → F)}) with hU₁_def
  set U₂ : Subgroup SL(2, F) := lineStab
      (Submodule.span F {(Pi.single 1 (1 : F) : Fin 2 → F)}) with hU₂_def
  -- It suffices to show every M ∈ SL is in U₁ ⊔ U₂. We do this by induction over
  -- the diagonal-transvection decomposition.
  rw [eq_top_iff]
  rintro M -
  -- Lift M to a matrix M.1 and show P M.1, then extract.
  obtain ⟨B, hBM, hB_mem⟩ : ∃ B : SL(2, F), B.1 = M.1 ∧ B ∈ U₁ ⊔ U₂ := by
    refine Matrix.diagonal_transvection_induction (fun N ↦ ∃ B : SL(2, F), B.1 = N ∧ B ∈ U₁ ⊔ U₂)
      M.1 (fun D hD ↦ ?_) transvection_mem_lineStab_sup fun A B ⟨A', hA', hA'_mem⟩
      ⟨B', hB', hB'_mem⟩ ↦ ⟨A' * B', by simp [hA', hB'], mul_mem hA'_mem hB'_mem⟩
    · -- Diagonal case: D with det D = det M.1 = 1.
      have hdet : (Matrix.diagonal D).det = 1 := by
        rw [hD, M.2]
      -- card ι = 2, so D = diag(D i₁, D i₂), and D i₁ * D i₂ = 1.
      have hprod : D 0 * D 1 = 1 := by
        rw [← Fin.prod_univ_two, ← Matrix.det_diagonal, hD, M.2]
      have hDi₁ : D 0 ≠ 0 := fun h ↦ by simp [h] at hprod
      have hDi₂_eq : D 1 = (D 0)⁻¹ := eq_inv_of_mul_eq_one_left
        (by rw [mul_comm]; exact hprod)
      -- Apply the diagonal lemma to get A with the desired action.
      obtain ⟨A, hAi₁, hAi₂, hA_mem⟩ :=
        diag_alpha_in_lineStab_sup (0 : Fin 2) 1 zero_ne_one (D 0) hDi₁
      refine ⟨A, ?_, hA_mem⟩
      ext i j
      simp [funext_iff] at hAi₁ hAi₂
      fin_cases i <;> fin_cases j <;> simp [hAi₁, hAi₂, hDi₂_eq]
  -- Conclude: M = B (since M.1 = B.1 implies M = B).
  rwa [Subtype.ext hBM] at hB_mem

end SL2Gen

open scoped LinearAlgebra.Projectivization

/-- At the SL level: when `Fintype.card ι = 2`, the supremum over all projective points of
the `lineStab` subgroups equals `⊤` in `SL ι F`. -/
lemma PSL.iSup_lineStab_eq_top :
    (⨆ p : ℙ F (Fin 2 → F), lineStab p.submodule) = (⊤ : Subgroup SL(2, F)) := by
  set p₁ : ℙ F (Fin 2 → F) := Projectivization.mk F (Pi.single 0 1)
    (fun h ↦ one_ne_zero <| Pi.single_eq_zero_iff.1 h) with hp₁_eq
  set p₂ : ℙ F (Fin 2 → F) := Projectivization.mk F (Pi.single 1 1)
    (fun h ↦ one_ne_zero <| Pi.single_eq_zero_iff.1 h) with hp₂_eq
  -- The SL-level supremum at p₁, p₂ is already ⊤.
  have hSL : lineStab p₁.submodule ⊔ lineStab p₂.submodule = (⊤ : Subgroup SL(2, F)) := by
    have hp1 : p₁.submodule = Submodule.span F {(Pi.single 0 1 : Fin 2 → F)} := by
      rw [hp₁_eq, Projectivization.submodule_mk]
    have hp2 : p₂.submodule = Submodule.span F {(Pi.single 1 1 : Fin 2 → F)} := by
      rw [hp₂_eq, Projectivization.submodule_mk]
    rw [hp1, hp2]
    exact SL2Gen.SL_card_two_lineStab_sup_eq_top
  -- Now lift to the full iSup.
  apply le_antisymm le_top
  rw [← hSL]
  change _ ≤ iSup (lineStab ∘ _)
  rw [← Function.comp_apply (g := Projectivization.submodule) (f := lineStab) (x := p₁),
      ← Function.comp_apply (g := Projectivization.submodule) (f := lineStab) (x := p₂)]
  exact sup_le (le_iSup _ _) (le_iSup _ _)

/-- The Iwasawa generator property: when `Fintype.card ι = 2`, the supremum of the
`iwasawaT` subgroups equals all of `PSL`. -/
lemma PSL.iSup_iwasawaT_eq_top :
    iSup (PSL.iwasawaT (F := F) (ι := Fin 2)) = ⊤ := by
  -- Pop out the quotient via Subgroup.map_iSup.
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

/-! ### PSL is simple when `card ι = 2` and `|F| ≥ 4`. -/

namespace SL2Simple

open SL2Gen Matrix.SpecialLinearGroup

open scoped commutatorElement

/-- The subgroup `lineStab (span F {e_{i₁}})` is contained in `commutator (SL ι F)`. -/
lemma lineStab_le_commutator_of_card_two (a : F) (ha : a ≠ 0) (hasq : a ^ 2 ≠ 1) :
    Matrix.SpecialLinearGroup.lineStab
      (Submodule.span F {(Pi.single 0 (1 : F) : Fin 2 → F)}) ≤ commutator SL(2, F) := fun A hA ↦ by
  -- For A ∈ lineStab, A.1 *ᵥ e_{i₁} = e_{i₁} by lineStab_fix_of_span.
  have he1 : (Pi.single 0 (1 : F) : Fin 2 → F) ≠ 0 := by
    intro h; have := congr_fun h 0; simp at this
  have hAe1 : A.1 *ᵥ (Pi.single 0 1) = Pi.single 0 1 :=
    Matrix.SpecialLinearGroup.lineStab_fix_of_span (Pi.single 0 1) he1 A hA
  -- A.1 *ᵥ e_{i₂} = e_{i₂} + c • e_{i₁} for some c (using membership).
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp <| hA <| Pi.single 1 1
  have hAeq : A = transvection zero_ne_one c := Subtype.ext <| by
    simp [Fin.isValue, Matrix.SpecialLinearGroup.smul_def, funext_iff, Pi.smul_apply,
      eq_comm (a := c), eq_comm (a := (0 : F)), sub_eq_zero] at hc hAe1
    simp [Fin.isValue, transvection_coe, ← Matrix.ext_iff, hc, hAe1]
  rw [hAeq]
  exact transvection_mem_commutator a ha hasq c

/-- The image of any line stabilizer in SL is in the commutator subgroup. -/
lemma lineStab_le_commutator_general (hF : ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1) (p : ℙ F ((Fin 2) → F)) :
    lineStab p.submodule ≤ commutator (SL(2, F)) := fun x hx ↦ by
  obtain ⟨a, ha, hasq⟩ := hF
  have he1_ne : (Pi.single 0 1 : Fin 2 → F) ≠ 0 := by
    intro h; have := congr_fun h 0; simp at this
  set p₁ : ℙ F (Fin 2 → F) := Projectivization.mk F (Pi.single 0 1) he1_ne with hp₁_def
  obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq (M := SL(2, F)) p₁ p
  -- For each x in lineStab(p.submodule), we want to show x is in commutator.
  rw [← hg, PSL.smul_submodule, hp₁_def, Projectivization.submodule_mk, lineStab_smul,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
  convert Subgroup.Normal.conj_mem (H := commutator SL(2, F)) inferInstance
    ((MulAut.conj g)⁻¹ • x) (lineStab_le_commutator_of_card_two a ha hasq hx) g
  simp; group

/-- `commutator (SL ι F) = ⊤` when `card ι = 2` and `|F| ≥ 4`. -/
lemma SL_commutator_eq_top (hF : ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1) :
    commutator SL(2, F) = ⊤ := by
  rw [eq_top_iff, ← PSL.iSup_lineStab_eq_top]
  exact iSup_le (fun p => lineStab_le_commutator_general hF p)

/-- `commutator (PSL ι F) = ⊤`. -/
lemma PSL_commutator_eq_top (hF : ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1) :
    commutator PSL(2, F) = ⊤ := by
  haveI : Group.IsPerfect SL(2, F) := ⟨SL_commutator_eq_top hF⟩
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
