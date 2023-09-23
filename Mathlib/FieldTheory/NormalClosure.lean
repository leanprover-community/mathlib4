/-
Copyright (c) 2023 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/

import Mathlib.FieldTheory.Normal
import Mathlib.Order.Closure

#align_import field_theory.normal from "leanprover-community/mathlib"@"9fb8964792b4237dac6200193a0d533f1b3f7423"
/-!
# Normal closures
The normal closure of a tower of fields `L/K/F` is the smallest intermediate field of `L/K` that
contains the image of every `F`-algebra embedding `K →ₐ[F] L`.

## Main Definitions
- `normalClosure F K L` a tower of fields `L/K/F`.
-/

open BigOperators IntermediateField IsScalarTower Polynomial

variable (F K L : Type*) [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L] [Algebra K L]
  [IsScalarTower F K L]

/-- The normal closure of `K` in `L`. -/
noncomputable def normalClosure : IntermediateField F L :=
  ⨆ f : K →ₐ[F] L, f.fieldRange

lemma normalClosure_def : normalClosure F K L = ⨆ f : K →ₐ[F] L, f.fieldRange :=
  rfl

variable {F K L}

lemma normalClosure_le_iff {K' : IntermediateField F L} :
    normalClosure F K L ≤ K' ↔ ∀ f : K →ₐ[F] L, f.fieldRange ≤ K' :=
  iSup_le_iff

lemma AlgHom.fieldRange_le_normalClosure  (f : K →ₐ[F] L) : f.fieldRange ≤ normalClosure F K L :=
  le_iSup AlgHom.fieldRange f

variable (F K L)

namespace normalClosure

theorem restrictScalars_eq_iSup_adjoin [h : Normal F L] :
    normalClosure F K L = ⨆ x : K, adjoin F ((minpoly F x).rootSet L) := by
  classical
  have hi : ∀ x : K, IsIntegral F x :=
    fun x ↦ (isIntegral_algebraMap_iff (algebraMap K L).injective).mp (h.isIntegral _)
  refine' le_antisymm (iSup_le _) (iSup_le fun x => adjoin_le_iff.mpr fun y hy => _)
  · rintro f _ ⟨x, rfl⟩
    refine' le_iSup (fun x => adjoin F ((minpoly F x).rootSet L)) x
        (subset_adjoin F ((minpoly F x).rootSet L) _)
    rw [mem_rootSet_of_ne (minpoly.ne_zero (hi x)), AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  · rw [Polynomial.rootSet, Finset.mem_coe, Multiset.mem_toFinset] at hy
    let g := (algHomAdjoinIntegralEquiv F (hi x)).symm ⟨y, hy⟩
    refine' le_iSup (fun f : K →ₐ[F] L => f.fieldRange) ((g.liftNormal L).comp (toAlgHom F K L))
        ⟨x, (g.liftNormal_commutes L (AdjoinSimple.gen F x)).trans _⟩
    rw [Algebra.id.map_eq_id, RingHom.id_apply]
    -- Porting note: in mathlib3 this next `apply` closed the goal.
    -- Now it can't find a proof by unification, so we have to do it ourselves.
    apply PowerBasis.lift_gen
    change aeval y (minpoly F (AdjoinSimple.gen F x)) = 0
    exact minpoly_gen F x ▸ aeval_eq_zero_of_mem_rootSet (Multiset.mem_toFinset.mpr hy)

#align normal_closure.restrict_scalars_eq_supr_adjoin normalClosure.restrictScalars_eq_iSup_adjoin

instance normal [h : Normal F L] : Normal F (normalClosure F K L) := by
  let ϕ := algebraMap K L
  rw [← IntermediateField.restrictScalars_normal, restrictScalars_eq_iSup_adjoin]
  -- Porting note: use the `(_)` trick to obtain an instance by unification.
  apply IntermediateField.normal_iSup (h := _)
  intro x
  -- Porting note: use the `(_)` trick to obtain an instance by unification.
  apply Normal.of_isSplittingField (p := minpoly F x) (hFEp := _)
  exact adjoin_rootSet_isSplittingField (minpoly.algebraMap_eq ϕ.injective (A := F) x ▸ h.splits _)
#align normal_closure.normal normalClosure.normal

instance is_finiteDimensional [FiniteDimensional F K] :
    FiniteDimensional F (normalClosure F K L) := by
  haveI : ∀ f : K →ₐ[F] L, FiniteDimensional F f.fieldRange := fun f =>
    f.toLinearMap.finiteDimensional_range
  apply IntermediateField.finiteDimensional_iSup_of_finite

noncomputable instance algebra : Algebra K (normalClosure F K L) :=
  IntermediateField.algebra
    { ⨆ f : K →ₐ[F] L, f.fieldRange with
      algebraMap_mem' := fun r => (toAlgHom F K L).fieldRange_le_normalClosure ⟨r, rfl⟩ }

instance : IsScalarTower F K (normalClosure F K L) := by
  apply of_algebraMap_eq'
  ext x
  exact algebraMap_apply F K L x

instance : IsScalarTower K (normalClosure F K L) L :=
  of_algebraMap_eq' rfl

lemma restrictScalars_eq :
    (toAlgHom K (normalClosure F K L) L).fieldRange.restrictScalars F = normalClosure F K L :=
  SetLike.ext' Subtype.range_val

end normalClosure

namespace IntermediateField

variable {F L}
variable (K K' : IntermediateField F L)

lemma le_normalClosure : K ≤ normalClosure F K L :=
K.fieldRange_val.symm.trans_le K.val.fieldRange_le_normalClosure

lemma normalClosure_of_normal [Normal F K] : normalClosure F K L = K :=
by simp only [normalClosure_def, AlgHom.fieldRange_of_normal, iSup_const]

variable [Normal F L]

lemma normalClosure_def' : normalClosure F K L = ⨆ f : L →ₐ[F] L, K.map f := by
  refine' (normalClosure_def F K L).trans (le_antisymm (iSup_le (fun f ↦ _)) (iSup_le (fun f ↦ _)))
  · exact le_iSup_of_le (f.liftNormal L) (fun b ⟨a, h⟩ ↦ ⟨a, a.2, h ▸ f.liftNormal_commutes L a⟩)
  · exact le_iSup_of_le (f.comp K.val) (fun b ⟨a, h⟩ ↦ ⟨⟨a, h.1⟩, h.2⟩)

lemma normalClosure_def'' : normalClosure F K L = ⨆ f : L ≃ₐ[F] L, K.map f := by
  refine' (normalClosure_def' K).trans (le_antisymm (iSup_le (fun f ↦ _)) (iSup_le (fun f ↦ _)))
  · exact le_iSup_of_le (f.restrictNormal' L)
      (fun b ⟨a, h⟩ ↦ ⟨a, h.1, h.2 ▸ f.restrictNormal_commutes L a⟩)
  · exact le_iSup_of_le f le_rfl

lemma normalClosure_mono (h : K ≤ K') : normalClosure F K L ≤ normalClosure F K' L := by
  rw [normalClosure_def', normalClosure_def']
  exact iSup_mono (fun f ↦ map_mono f h)

variable (F L)

/-- `normalClosure` as a `ClosureOperator`. -/
@[simps]
noncomputable def closureOperator : ClosureOperator (IntermediateField F L) where
  toFun := fun K ↦ normalClosure F K L
  monotone' := fun K K' ↦ normalClosure_mono K K'
  le_closure' := le_normalClosure
  idempotent' := fun K ↦ normalClosure_of_normal (normalClosure F K L)

variable {K : IntermediateField F L} {F L}

lemma normal_iff_normalClosure_eq : Normal F K ↔ normalClosure F K L = K :=
⟨@normalClosure_of_normal (K := K), fun h ↦ h ▸ normalClosure.normal F K L⟩

lemma normal_iff_normalClosure_le : Normal F K ↔ normalClosure F K L ≤ K :=
normal_iff_normalClosure_eq.trans (le_normalClosure K).le_iff_eq.symm

lemma normal_iff_forall_fieldRange_le : Normal F K ↔ ∀ σ : K →ₐ[F] L, σ.fieldRange ≤ K :=
by rw [normal_iff_normalClosure_le, normalClosure_def, iSup_le_iff]

lemma normal_iff_forall_map_le : Normal F K ↔ ∀ σ : L →ₐ[F] L, K.map σ ≤ K :=
by rw [normal_iff_normalClosure_le, normalClosure_def', iSup_le_iff]

lemma normal_iff_forall_map_le' : Normal F K ↔ ∀ σ : L ≃ₐ[F] L, K.map ↑σ ≤ K :=
by rw [normal_iff_normalClosure_le, normalClosure_def'', iSup_le_iff]

lemma normal_iff_forall_fieldRange_eq : Normal F K ↔ ∀ σ : K →ₐ[F] L, σ.fieldRange = K :=
⟨@AlgHom.fieldRange_of_normal (E := K), normal_iff_forall_fieldRange_le.2 ∘ fun h σ ↦ (h σ).le⟩

lemma normal_iff_forall_map_eq : Normal F K ↔ ∀ σ : L →ₐ[F] L, K.map σ = K :=
⟨fun h σ ↦ (K.fieldRange_val ▸ AlgHom.map_fieldRange K.val σ).trans
  (normal_iff_forall_fieldRange_eq.1 h _), fun h ↦ normal_iff_forall_map_le.2 (fun σ ↦ (h σ).le)⟩

lemma normal_iff_forall_map_eq' : Normal F K ↔ ∀ σ : L ≃ₐ[F] L, K.map ↑σ = K :=
⟨fun h σ ↦ normal_iff_forall_map_eq.1 h σ, fun h ↦ normal_iff_forall_map_le'.2 (fun σ ↦ (h σ).le)⟩

end IntermediateField
