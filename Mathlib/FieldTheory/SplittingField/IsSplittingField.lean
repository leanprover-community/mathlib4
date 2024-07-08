/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.FieldTheory.IntermediateField
import Mathlib.RingTheory.Adjoin.Field

#align_import field_theory.splitting_field.is_splitting_field from "leanprover-community/mathlib"@"9fb8964792b4237dac6200193a0d533f1b3f7423"

/-!
# Splitting fields

This file introduces the notion of a splitting field of a polynomial and provides an embedding from
a splitting field to any field that splits the polynomial. A polynomial `f : K[X]` splits
over a field extension `L` of `K` if it is zero or all of its irreducible factors over `L` have
degree `1`. A field extension of `K` of a polynomial `f : K[X]` is called a splitting field
if it is the smallest field extension of `K` such that `f` splits.

## Main definitions

* `Polynomial.IsSplittingField`: A predicate on a field to be a splitting field of a polynomial
  `f`.

## Main statements

* `Polynomial.IsSplittingField.lift`: An embedding of a splitting field of the polynomial `f` into
  another field such that `f` splits.

-/


noncomputable section

open scoped Classical Polynomial

universe u v w

variable {F : Type u} (K : Type v) (L : Type w)

namespace Polynomial

variable [Field K] [Field L] [Field F] [Algebra K L]

/-- Typeclass characterising splitting fields. -/
class IsSplittingField (f : K[X]) : Prop where
  splits' : Splits (algebraMap K L) f
  adjoin_rootSet' : Algebra.adjoin K (f.rootSet L : Set L) = ⊤
#align polynomial.is_splitting_field Polynomial.IsSplittingField

namespace IsSplittingField

variable {K}

-- Porting note: infer kinds are unsupported
-- so we provide a version of `splits'` with `f` explicit.
theorem splits (f : K[X]) [IsSplittingField K L f] : Splits (algebraMap K L) f :=
  splits'
#align polynomial.is_splitting_field.splits Polynomial.IsSplittingField.splits

-- Porting note: infer kinds are unsupported
-- so we provide a version of `adjoin_rootSet'` with `f` explicit.
theorem adjoin_rootSet (f : K[X]) [IsSplittingField K L f] :
    Algebra.adjoin K (f.rootSet L : Set L) = ⊤ :=
  adjoin_rootSet'
#align polynomial.is_splitting_field.adjoin_root_set Polynomial.IsSplittingField.adjoin_rootSet

section ScalarTower

variable [Algebra F K] [Algebra F L] [IsScalarTower F K L]

instance map (f : F[X]) [IsSplittingField F L f] : IsSplittingField K L (f.map <| algebraMap F K) :=
  ⟨by rw [splits_map_iff, ← IsScalarTower.algebraMap_eq]; exact splits L f,
    Subalgebra.restrictScalars_injective F <| by
      rw [rootSet, aroots, map_map, ← IsScalarTower.algebraMap_eq, Subalgebra.restrictScalars_top,
        eq_top_iff, ← adjoin_rootSet L f, Algebra.adjoin_le_iff]
      exact fun x hx => @Algebra.subset_adjoin K _ _ _ _ _ _ hx⟩
#align polynomial.is_splitting_field.map Polynomial.IsSplittingField.map

theorem splits_iff (f : K[X]) [IsSplittingField K L f] :
    Splits (RingHom.id K) f ↔ (⊤ : Subalgebra K L) = ⊥ :=
  ⟨fun h => by -- Porting note: replaced term-mode proof
    rw [eq_bot_iff, ← adjoin_rootSet L f, rootSet, aroots, roots_map (algebraMap K L) h,
      Algebra.adjoin_le_iff]
    intro y hy
    rw [Multiset.toFinset_map, Finset.mem_coe, Finset.mem_image] at hy
    obtain ⟨x : K, -, hxy : algebraMap K L x = y⟩ := hy
    rw [← hxy]
    exact SetLike.mem_coe.2 <| Subalgebra.algebraMap_mem _ _,
    fun h => @RingEquiv.toRingHom_refl K _ ▸ RingEquiv.self_trans_symm
      (RingEquiv.ofBijective _ <| Algebra.bijective_algebraMap_iff.2 h) ▸ by
        rw [RingEquiv.toRingHom_trans]
        exact splits_comp_of_splits _ _ (splits L f)⟩
#align polynomial.is_splitting_field.splits_iff Polynomial.IsSplittingField.splits_iff

theorem mul (f g : F[X]) (hf : f ≠ 0) (hg : g ≠ 0) [IsSplittingField F K f]
    [IsSplittingField K L (g.map <| algebraMap F K)] : IsSplittingField F L (f * g) :=
  ⟨(IsScalarTower.algebraMap_eq F K L).symm ▸
      splits_mul _ (splits_comp_of_splits _ _ (splits K f))
        ((splits_map_iff _ _).1 (splits L <| g.map <| algebraMap F K)), by
    rw [rootSet, aroots_mul (mul_ne_zero hf hg),
      Multiset.toFinset_add, Finset.coe_union, Algebra.adjoin_union_eq_adjoin_adjoin,
      aroots_def, aroots_def, IsScalarTower.algebraMap_eq F K L, ← map_map,
      roots_map (algebraMap K L) ((splits_id_iff_splits <| algebraMap F K).2 <| splits K f),
      Multiset.toFinset_map, Finset.coe_image, Algebra.adjoin_algebraMap, ← rootSet, adjoin_rootSet,
      Algebra.map_top, IsScalarTower.adjoin_range_toAlgHom, ← map_map, ← rootSet, adjoin_rootSet,
      Subalgebra.restrictScalars_top]⟩
#align polynomial.is_splitting_field.mul Polynomial.IsSplittingField.mul

end ScalarTower

/-- Splitting field of `f` embeds into any field that splits `f`. -/
def lift [Algebra K F] (f : K[X]) [IsSplittingField K L f]
    (hf : Splits (algebraMap K F) f) : L →ₐ[K] F :=
  if hf0 : f = 0 then
    (Algebra.ofId K F).comp <|
      (Algebra.botEquiv K L : (⊥ : Subalgebra K L) →ₐ[K] K).comp <| by
        rw [← (splits_iff L f).1 (show f.Splits (RingHom.id K) from hf0.symm ▸ splits_zero _)]
        exact Algebra.toTop
  else AlgHom.comp (by
    rw [← adjoin_rootSet L f];
    exact Classical.choice (lift_of_splits _ fun y hy =>
      have : aeval y f = 0 := (eval₂_eq_eval_map _).trans <|
        (mem_roots <| map_ne_zero hf0).1 (Multiset.mem_toFinset.mp hy)
    ⟨IsAlgebraic.isIntegral ⟨f, hf0, this⟩,
      splits_of_splits_of_dvd _ hf0 hf <| minpoly.dvd _ _ this⟩)) Algebra.toTop
#align polynomial.is_splitting_field.lift Polynomial.IsSplittingField.lift

theorem finiteDimensional (f : K[X]) [IsSplittingField K L f] : FiniteDimensional K L :=
  ⟨@Algebra.top_toSubmodule K L _ _ _ ▸
    adjoin_rootSet L f ▸ fg_adjoin_of_finite (Finset.finite_toSet _) fun y hy ↦
      if hf : f = 0 then by rw [hf, rootSet_zero] at hy; cases hy
      else IsAlgebraic.isIntegral ⟨f, hf, (mem_rootSet'.mp hy).2⟩⟩
#align polynomial.is_splitting_field.finite_dimensional Polynomial.IsSplittingField.finiteDimensional

theorem of_algEquiv [Algebra K F] (p : K[X]) (f : F ≃ₐ[K] L) [IsSplittingField K F p] :
    IsSplittingField K L p := by
  constructor
  · rw [← f.toAlgHom.comp_algebraMap]
    exact splits_comp_of_splits _ _ (splits F p)
  · rw [← (Algebra.range_top_iff_surjective f.toAlgHom).mpr f.surjective,
      adjoin_rootSet_eq_range (splits F p), adjoin_rootSet F p]
#align polynomial.is_splitting_field.of_alg_equiv Polynomial.IsSplittingField.of_algEquiv

theorem adjoin_rootSet_eq_range [Algebra K F] (f : K[X]) [IsSplittingField K L f] (i : L →ₐ[K] F) :
    Algebra.adjoin K (rootSet f F) = i.range :=
  (Polynomial.adjoin_rootSet_eq_range (splits L f) i).mpr (adjoin_rootSet L f)

end IsSplittingField

end Polynomial

open Polynomial

variable {K L} [Field K] [Field L] [Algebra K L] {p : K[X]} {F : IntermediateField K L}

theorem IntermediateField.splits_of_splits (h : p.Splits (algebraMap K L))
    (hF : ∀ x ∈ p.rootSet L, x ∈ F) : p.Splits (algebraMap K F) := by
  simp_rw [← F.fieldRange_val, rootSet_def, Finset.mem_coe, Multiset.mem_toFinset] at hF
  exact splits_of_comp _ F.val.toRingHom h hF
#align intermediate_field.splits_of_splits IntermediateField.splits_of_splits

theorem IsIntegral.mem_intermediateField_of_minpoly_splits {x : L} (int : IsIntegral K x)
    {F : IntermediateField K L} (h : Splits (algebraMap K F) (minpoly K x)) : x ∈ F := by
  rw [← F.fieldRange_val]; exact int.mem_range_algebraMap_of_minpoly_splits h
