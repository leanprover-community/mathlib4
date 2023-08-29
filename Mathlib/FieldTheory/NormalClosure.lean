/-
Copyright (c) 2023 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/

import Mathlib.FieldTheory.Normal

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
noncomputable def normalClosure : IntermediateField K L :=
  { (⨆ f : K →ₐ[F] L, f.fieldRange) with
    algebraMap_mem' := fun r =>
      le_iSup (fun f : K →ₐ[F] L => f.fieldRange) (IsScalarTower.toAlgHom F K L) ⟨r, rfl⟩ }
#align normal_closure normalClosure

namespace normalClosure

theorem restrictScalars_eq_iSup_adjoin [h : Normal F L] :
    (normalClosure F K L).restrictScalars F = ⨆ x : K, adjoin F ((minpoly F x).rootSet L) := by
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
    exact minpoly_gen (hi x) ▸ aeval_eq_zero_of_mem_rootSet (Multiset.mem_toFinset.mpr hy)

#align normal_closure.restrict_scalars_eq_supr_adjoin normalClosure.restrictScalars_eq_iSup_adjoin

instance normal [h : Normal F L] : Normal F (normalClosure F K L) := by
  let ϕ := algebraMap K L
  -- ⊢ Normal F { x // x ∈ normalClosure F K L }
  rw [← IntermediateField.restrictScalars_normal, restrictScalars_eq_iSup_adjoin]
  -- ⊢ Normal F { x // x ∈ ⨆ (x : K), adjoin F (rootSet (minpoly F x) L) }
  -- Porting note: use the `(_)` trick to obtain an instance by unification.
  apply IntermediateField.normal_iSup (h := _)
  -- ⊢ ∀ (i : K), Normal F { x // x ∈ adjoin F (rootSet (minpoly F i) L) }
  intro x
  -- ⊢ Normal F { x_1 // x_1 ∈ adjoin F (rootSet (minpoly F x) L) }
  -- Porting note: use the `(_)` trick to obtain an instance by unification.
  apply Normal.of_isSplittingField (p := minpoly F x) (hFEp := _)
  -- ⊢ IsSplittingField F { x_1 // x_1 ∈ adjoin F (rootSet (minpoly F x) L) } (minp …
  exact adjoin_rootSet_isSplittingField ((minpoly.eq_of_algebraMap_eq ϕ.injective
    ((isIntegral_algebraMap_iff ϕ.injective).mp (h.isIntegral (ϕ x))) rfl).symm ▸ h.splits _)
#align normal_closure.normal normalClosure.normal

instance is_finiteDimensional [FiniteDimensional F K] :
    FiniteDimensional F (normalClosure F K L) := by
  haveI : ∀ f : K →ₐ[F] L, FiniteDimensional F f.fieldRange := fun f =>
    f.toLinearMap.finiteDimensional_range
  apply IntermediateField.finiteDimensional_iSup_of_finite
  -- 🎉 no goals
#align normal_closure.is_finite_dimensional normalClosure.is_finiteDimensional

instance isScalarTower : IsScalarTower F (normalClosure F K L) L :=
  -- Porting note: the last argument here `(⨆ (f : K →ₐ[F] L), f.fieldRange).toSubalgebra`
  -- was just written as `_` in mathlib3.
  IsScalarTower.subalgebra' F L L (⨆ (f : K →ₐ[F] L), f.fieldRange).toSubalgebra
#align normal_closure.is_scalar_tower normalClosure.isScalarTower

end normalClosure
