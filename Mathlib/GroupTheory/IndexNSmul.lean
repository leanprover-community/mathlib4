/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs

import Mathlib.Algebra.Group.Subgroup.ZPowers.Lemmas
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Lemmas about index and multiplication-by-n

In this file we collect some results involving the multiplication-by-`n` map
`nsmulAddMonoidHom n` (for a natural number `n`) on a commutative additive group
and the (relative) index of subgroups.
-/

public section

namespace AddSubgroup

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]

open Module

open QuotientAddGroup in
variable (M) in
/-- The index of the image of the multiplication-by-`n` map on an additive group `M` that is free
and finitely generated as a `ℤ`-module is `n ^ finrank ℤ M`. -/
lemma index_range_nsmul [Free ℤ M] [Module.Finite ℤ M] (n : ℕ) :
    (nsmulAddMonoidHom (α := M) n).range.index = n ^ finrank ℤ M :=
  calc
    _ = (nsmulAddMonoidHom (α := (Fin (finrank ℤ M) → ℤ)) n).range.index := by
      simpa [AddEquiv.map_range_nsmulAddMonoidHom]
        using (index_map_equiv (nsmulAddMonoidHom (α := M) n).range
                (Module.finBasis ℤ M).equivFun.toAddEquiv).symm
    _ = _ := by
      simp [index_eq_card, Nat.card_congr (addEquivPiModRangeNSMulAddMonoidHom _ n).toEquiv,
        Nat.card_fun, Int.range_nsmulAddMonoidHom,
        Nat.card_congr (Int.quotientZMultiplesNatEquivZMod n).toEquiv]

/-- The relative index in `S` of the image of the multiplication-by-`n` map
on an additive subgroup `S` of an additive group such that `S` is free
and finitely generated as a `ℤ`-module is `n ^ finrank ℤ S`. -/
lemma relIndex_map_nsmul (n : ℕ) (S : AddSubgroup M) [Free ℤ ↥S.toIntSubmodule]
    [Module.Finite ℤ ↥S.toIntSubmodule] :
    (S.map (nsmulAddMonoidHom (α := M) n)).relIndex S = n ^ finrank ℤ S := by
  simpa only [relIndex, addSubgroupOf_map_nsmulAddMonoidHom_eq_range]
    using index_range_nsmul S.toIntSubmodule n

/-- On an additive group that is torsion-free as a `ℤ`-module, the linear map given by
multiplication by `n : ℕ` is injective (when `n ≠ 0`). -/
lemma distribSMulToLinearMap_injective_of_isTorsionFree [IsTorsionFree ℤ M] {n : ℕ} (hn : n ≠ 0) :
    Function.Injective (DistribSMul.toLinearMap ℤ M n) :=
  LinearMap.ker_eq_bot.mp <| (Submodule.eq_bot_iff _).mpr fun x hx ↦ by simp_all

/-- On an additive group that is torsion-free as a `ℤ`-module, the multiplication-by-`n` map
is injective (when `n ≠ 0`). -/
lemma nsmulAddMonoidHom_injective_of_isTorsionFree [IsTorsionFree ℤ M] {n : ℕ} (hn : n ≠ 0) :
    Function.Injective (nsmulAddMonoidHom (α := M) n) :=
  (AddMonoidHom.ker_eq_bot_iff _).mp <| (eq_bot_iff_forall _).mpr fun x hx ↦ by simp_all

/-- If `A` is a subgroup of finite index of an additive group `M` that is finitely generated
and torsion-free as a `ℤ`-module, then `A` and `M` have the same rank. -/
lemma finrank_eq_of_finiteIndex [Module.Finite ℤ M] [IsTorsionFree ℤ M] (A : AddSubgroup M)
    [A.FiniteIndex] :
    finrank ℤ A = finrank ℤ M := by
  refine le_antisymm A.toIntSubmodule.finrank_le ?_
  have : finrank ℤ (DistribSMul.toLinearMap ℤ M A.index).range = finrank ℤ M :=
    (DistribSMul.toLinearMap ..).finrank_range_of_inj <|
      distribSMulToLinearMap_injective_of_isTorsionFree FiniteIndex.index_ne_zero
  rw [← this]
  refine Submodule.finrank_mono <| (OrderIso.symm_apply_le toIntSubmodule).mp fun m hm ↦ ?_
  obtain ⟨x, rfl⟩ : ∃ x, A.index • x = m := by simpa using hm
  exact A.nsmul_index_mem x

/-- If `A ≤ B` are subgroups of an additive group `M` such that `A` has finite relative index
in `B`, where `B` is finitely generated and torsion-free as a `ℤ`-module, then `A` and `B`
have the same rank. -/
lemma finrank_eq_of_isFiniteRelIndex {A B : AddSubgroup M} [Module.Finite ℤ B] [IsTorsionFree ℤ B]
    (h : A ≤ B) [A.IsFiniteRelIndex B] :
    finrank ℤ A = finrank ℤ B := by
  have : (A.addSubgroupOf B).FiniteIndex := IsFiniteRelIndex.to_finiteIndex_addSubgroupOf
  rw [← finrank_eq_of_finiteIndex (A.addSubgroupOf B)]
  exact (addSubgroupOfEquivOfLe h).symm.toIntLinearEquiv.finrank_eq

end AddSubgroup

end
