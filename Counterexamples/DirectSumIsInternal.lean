/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Kevin Buzzard
-/
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.Data.Fintype.Lattice
import Mathlib.Tactic.FinCases

/-!
# Not all complementary decompositions of a module over a semiring make up a direct sum

This shows that while `ℤ≤0` and `ℤ≥0` are complementary `ℕ`-submodules of `ℤ`, which in turn
implies as a collection they are `iSupIndep` and that they span all of `ℤ`, they
do not form a decomposition into a direct sum.

This file demonstrates why `DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top` must
take `Ring R` and not `Semiring R`.
-/


namespace Counterexample

theorem UnitsInt.one_ne_neg_one : (1 : ℤˣ) ≠ -1 := by decide

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

local notation "ℤ≥0" => withSign 1

local notation "ℤ≤0" => withSign (-1)

theorem mem_withSign_one {x : ℤ} : x ∈ ℤ≥0 ↔ 0 ≤ x :=
  show _ ≤ (_ : ℤˣ) • x ↔ _ by rw [one_smul]

theorem mem_withSign_neg_one {x : ℤ} : x ∈ ℤ≤0 ↔ x ≤ 0 :=
  show _ ≤ (_ : ℤˣ) • x ↔ _ by rw [Units.neg_smul, le_neg, one_smul, neg_zero]

/-- The two submodules are complements. -/
theorem withSign.isCompl : IsCompl ℤ≥0 ℤ≤0 := by
  constructor
  · apply Submodule.disjoint_def.2
    intro x hx hx'
    exact le_antisymm (mem_withSign_neg_one.mp hx') (mem_withSign_one.mp hx)
  · rw [codisjoint_iff_le_sup]
    intro x _hx
    obtain hp | hn := (le_refl (0 : ℤ)).ge_or_le x
    · exact Submodule.mem_sup_left (mem_withSign_one.mpr hp)
    · exact Submodule.mem_sup_right (mem_withSign_neg_one.mpr hn)

def withSign.independent : iSupIndep withSign := by
  apply
    (iSupIndep_pair UnitsInt.one_ne_neg_one _).mpr withSign.isCompl.disjoint
  intro i
  fin_cases i <;> simp

theorem withSign.iSup : iSup withSign = ⊤ := by
  rw [← Finset.sup_univ_eq_iSup, UnitsInt.univ, Finset.sup_insert, Finset.sup_singleton]
  exact withSign.isCompl.sup_eq_top

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
    -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
    erw [DFinsupp.zero_apply, DFinsupp.add_apply, DFinsupp.single_eq_same,
      DFinsupp.single_eq_of_ne UnitsInt.one_ne_neg_one.symm, add_zero, Subtype.ext_iff,
      Submodule.coe_zero] at h
    apply zero_ne_one h.symm
  apply hinj.ne this
  rw [LinearMap.map_zero, LinearMap.map_add, DirectSum.toModule_lof, DirectSum.toModule_lof]
  simp [p1, n1]

/-- And so they do not represent an internal direct sum. -/
theorem withSign.not_internal : ¬DirectSum.IsInternal withSign :=
  withSign.not_injective ∘ And.left

end Counterexample
