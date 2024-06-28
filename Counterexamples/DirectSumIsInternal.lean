/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Kevin Buzzard
-/
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.Data.Fintype.Lattice
import Mathlib.Tactic.FinCases

#align_import direct_sum_is_internal from "leanprover-community/mathlib"@"328375597f2c0dd00522d9c2e5a33b6a6128feeb"

/-!
# Not all complementary decompositions of a module over a semiring make up a direct sum

This shows that while `ℤ≤0` and `ℤ≥0` are complementary `ℕ`-submodules of `ℤ`, which in turn
implies as a collection they are `CompleteLattice.Independent` and that they span all of `ℤ`, they
do not form a decomposition into a direct sum.

This file demonstrates why `DirectSum.isInternal_submodule_of_independent_of_iSup_eq_top` must
take `Ring R` and not `Semiring R`.
-/


namespace Counterexample

theorem UnitsInt.one_ne_neg_one : (1 : ℤˣ) ≠ -1 := by decide
#align counterexample.units_int.one_ne_neg_one Counterexample.UnitsInt.one_ne_neg_one

/-- Submodules of positive and negative integers, keyed by sign. -/
def withSign (i : ℤˣ) : Submodule ℕ ℤ :=
  AddSubmonoid.toNatSubmodule <|
    show AddSubmonoid ℤ from
      { carrier := {z | 0 ≤ i • z}
        zero_mem' := show 0 ≤ i • (0 : ℤ) from (smul_zero _).ge
        add_mem' := fun {x y} (hx : 0 ≤ i • x) (hy : 0 ≤ i • y) =>
          show 0 ≤ i • (x + y) by
            rw [smul_add]
            exact add_nonneg hx hy }
#align counterexample.with_sign Counterexample.withSign

local notation "ℤ≥0" => withSign 1

local notation "ℤ≤0" => withSign (-1)

theorem mem_withSign_one {x : ℤ} : x ∈ ℤ≥0 ↔ 0 ≤ x :=
  show _ ≤ (_ : ℤˣ) • x ↔ _ by rw [one_smul]
#align counterexample.mem_with_sign_one Counterexample.mem_withSign_one

theorem mem_withSign_neg_one {x : ℤ} : x ∈ ℤ≤0 ↔ x ≤ 0 :=
  show _ ≤ (_ : ℤˣ) • x ↔ _ by rw [Units.neg_smul, le_neg, one_smul, neg_zero]
#align counterexample.mem_with_sign_neg_one Counterexample.mem_withSign_neg_one

/-- The two submodules are complements. -/
theorem withSign.isCompl : IsCompl ℤ≥0 ℤ≤0 := by
  constructor
  · apply Submodule.disjoint_def.2
    intro x hx hx'
    exact le_antisymm (mem_withSign_neg_one.mp hx') (mem_withSign_one.mp hx)
  · rw [codisjoint_iff_le_sup]
    intro x _hx
    obtain hp | hn := (le_refl (0 : ℤ)).le_or_le x
    · exact Submodule.mem_sup_left (mem_withSign_one.mpr hp)
    · exact Submodule.mem_sup_right (mem_withSign_neg_one.mpr hn)
#align counterexample.with_sign.is_compl Counterexample.withSign.isCompl

def withSign.independent : CompleteLattice.Independent withSign := by
  apply
    (CompleteLattice.independent_pair UnitsInt.one_ne_neg_one _).mpr withSign.isCompl.disjoint
  intro i
  fin_cases i <;> simp
#align counterexample.with_sign.independent Counterexample.withSign.independent

theorem withSign.iSup : iSup withSign = ⊤ := by
  rw [← Finset.sup_univ_eq_iSup, UnitsInt.univ, Finset.sup_insert, Finset.sup_singleton]
  exact withSign.isCompl.sup_eq_top
#align counterexample.with_sign.supr Counterexample.withSign.iSup

/-- But there is no embedding into `ℤ` from the direct sum. -/
theorem withSign.not_injective :
    ¬Function.Injective (DirectSum.toModule ℕ ℤˣ ℤ fun i => (withSign i).subtype) := by
  intro hinj
  let p1 : ℤ≥0 := ⟨1, mem_withSign_one.2 zero_le_one⟩
  let n1 : ℤ≤0 := ⟨-1, mem_withSign_neg_one.2 <| neg_nonpos.2 zero_le_one⟩
  let z :=
    DirectSum.lof ℕ _ (fun i => withSign i) 1 p1 + DirectSum.lof ℕ _ (fun i => withSign i) (-1) n1
  have : z ≠ 0 := by
    intro h
    replace h := DFunLike.congr_fun h 1
    -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
    erw [DFinsupp.zero_apply, DFinsupp.add_apply, DFinsupp.single_eq_same,
      DFinsupp.single_eq_of_ne UnitsInt.one_ne_neg_one.symm, add_zero, Subtype.ext_iff,
      Submodule.coe_zero] at h
    apply zero_ne_one h.symm
  apply hinj.ne this
  rw [LinearMap.map_zero, LinearMap.map_add, DirectSum.toModule_lof, DirectSum.toModule_lof]
  simp
#align counterexample.with_sign.not_injective Counterexample.withSign.not_injective

/-- And so they do not represent an internal direct sum. -/
theorem withSign.not_internal : ¬DirectSum.IsInternal withSign :=
  withSign.not_injective ∘ And.left
#align counterexample.with_sign.not_internal Counterexample.withSign.not_internal

end Counterexample
