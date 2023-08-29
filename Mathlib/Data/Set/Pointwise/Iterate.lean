/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Data.Set.Pointwise.SMul
import Mathlib.Algebra.Hom.Iterate
import Mathlib.Dynamics.FixedPoints.Basic

#align_import data.set.pointwise.iterate from "leanprover-community/mathlib"@"9003f28797c0664a49e4179487267c494477d853"

/-!
# Results about pointwise operations on sets with iteration.
-/


open Pointwise

open Set Function

/-- Let `n : ℤ` and `s` a subset of a commutative group `G` that is invariant under preimage for
the map `x ↦ x^n`. Then `s` is invariant under the pointwise action of the subgroup of elements
`g : G` such that `g^(n^j) = 1` for some `j : ℕ`. (This subgroup is called the Prüfer subgroup when
 `G` is the `Circle` and `n` is prime.) -/
@[to_additive
      "Let `n : ℤ` and `s` a subset of an additive commutative group `G` that is invariant
      under preimage for the map `x ↦ n • x`. Then `s` is invariant under the pointwise action of
      the additive subgroup of elements `g : G` such that `(n^j) • g = 0` for some `j : ℕ`.
      (This additive subgroup is called the Prüfer subgroup when `G` is the `AddCircle` and `n` is
      prime.)"]
theorem smul_eq_self_of_preimage_zpow_eq_self {G : Type*} [CommGroup G] {n : ℤ} {s : Set G}
    (hs : (fun x => x ^ n) ⁻¹' s = s) {g : G} {j : ℕ} (hg : g ^ n ^ j = 1) : g • s = s := by
  suffices ∀ {g' : G} (_ : g' ^ n ^ j = 1), g' • s ⊆ s by
    refine' le_antisymm (this hg) _
    conv_lhs => rw [← smul_inv_smul g s]
    replace hg : g⁻¹ ^ n ^ j = 1
    · rw [inv_zpow, hg, inv_one]
    simpa only [le_eq_subset, set_smul_subset_set_smul_iff] using this hg
  rw [(IsFixedPt.preimage_iterate hs j : (zpowGroupHom n)^[j] ⁻¹' s = s).symm]
  -- ⊢ ∀ {g' : G}, g' ^ n ^ j = 1 → g' • (fun x => x ^ n)^[j] ⁻¹' s ⊆ (fun x => x ^ …
  rintro g' hg' - ⟨y, hy, rfl⟩
  -- ⊢ (fun x => g' • x) y ∈ (fun x => x ^ n)^[j] ⁻¹' s
  change (zpowGroupHom n)^[j] (g' * y) ∈ s
  -- ⊢ (↑(zpowGroupHom n))^[j] (g' * y) ∈ s
  replace hg' : (zpowGroupHom n)^[j] g' = 1
  -- ⊢ (↑(zpowGroupHom n))^[j] g' = 1
  · simpa [zpowGroupHom]
    -- 🎉 no goals
  rwa [iterate_map_mul, hg', one_mul]
  -- 🎉 no goals
#align smul_eq_self_of_preimage_zpow_eq_self smul_eq_self_of_preimage_zpow_eq_self
#align vadd_eq_self_of_preimage_zsmul_eq_self vadd_eq_self_of_preimage_zsmul_eq_self
