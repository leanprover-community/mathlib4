/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Extended norm

**ATTENTION.** This file is deprecated. Mathlib now has classes `ENormed(Add)(Comm)Monoid` for
(additive) (commutative) monoids with an `ENorm`: this is very similar to this definition, but
much more general. Should the need arise, an enormed version of a normed space can be added later:
this will be different from this file.


In this file we define a structure `ENormedSpace 𝕜 V` representing an extended norm (i.e., a norm
that can take the value `∞`) on a vector space `V` over a normed field `𝕜`. We do not use `class`
for an `ENormedSpace` because the same space can have more than one extended norm.
For example, the space of measurable functions `f : α → ℝ` has a family of `L_p` extended norms.

We prove some basic inequalities, then define

* `EMetricSpace` structure on `V` corresponding to `e : ENormedSpace 𝕜 V`;
* the subspace of vectors with finite norm, called `e.finiteSubspace`;
* a `NormedSpace` structure on this space.

The last definition is an instance because the type involves `e`.

## Implementation notes

We do not define extended normed groups. They can be added to the chain once someone will need them.

## Tags

normed space, extended norm
-/


noncomputable section

open ENNReal

set_option linter.deprecated false

namespace ENormedSpace

variable {𝕜 : Type*} {V : Type*} [NormedField 𝕜] [AddCommGroup V] [Module 𝕜 V]
  (e : ENormedSpace 𝕜 V)

attribute [coe] ENormedSpace.toFun

instance : CoeFun (ENormedSpace 𝕜 V) fun _ => V → ℝ≥0∞ :=
  ⟨ENormedSpace.toFun⟩

instance partialOrder : PartialOrder (ENormedSpace 𝕜 V) where
  le e₁ e₂ := ∀ x, e₁ x ≤ e₂ x
  le_refl _ _ := le_rfl
  le_trans _ _ _ h₁₂ h₂₃ x := le_trans (h₁₂ x) (h₂₃ x)
  le_antisymm _ _ h₁₂ h₂₁ := ext fun x => le_antisymm (h₁₂ x) (h₂₁ x)

/-- The `ENormedSpace` sending each non-zero vector to infinity. -/
noncomputable instance : Top (ENormedSpace 𝕜 V) :=
  ⟨{  toFun := fun x => open scoped Classical in if x = 0 then 0 else ⊤
      eq_zero' := fun x => by split_ifs <;> simp [*]
      map_add_le' := fun x y => by
        split_ifs with hxy hx hy hy hx hy hy <;> try simp [*]
        simp [hx, hy] at hxy
      map_smul_le' := fun c x => by
        split_ifs with hcx hx hx <;> simp only [smul_eq_zero, not_or] at hcx
        · simp only [mul_zero, le_refl]
        · have : c = 0 := by tauto
          simp [this]
        · tauto
        · simpa [mul_top'] using hcx.1 }⟩

noncomputable instance : Inhabited (ENormedSpace 𝕜 V) :=
  ⟨⊤⟩

noncomputable instance : OrderTop (ENormedSpace 𝕜 V) where
  top := ⊤
  le_top e x := by obtain h | h := eq_or_ne x 0 <;> simp [top_map, h]

noncomputable instance : SemilatticeSup (ENormedSpace 𝕜 V) :=
  { ENormedSpace.partialOrder with
    le := (· ≤ ·)
    lt := (· < ·)
    sup := fun e₁ e₂ =>
      { toFun := fun x => max (e₁ x) (e₂ x)
        eq_zero' := fun _ h => e₁.eq_zero_iff.1 (ENNReal.max_eq_zero_iff.1 h).1
        map_add_le' := fun _ _ =>
          max_le (le_trans (e₁.map_add_le _ _) <| add_le_add (le_max_left _ _) (le_max_left _ _))
            (le_trans (e₂.map_add_le _ _) <| add_le_add (le_max_right _ _) (le_max_right _ _))
        map_smul_le' := fun c x => le_of_eq <| by simp only [map_smul, mul_max] }
    le_sup_left := fun _ _ _ => le_max_left _ _
    le_sup_right := fun _ _ _ => le_max_right _ _
    sup_le := fun _ _ _ h₁ h₂ x => max_le (h₁ x) (h₂ x) }

/-- Metric space structure on `e.finiteSubspace`. We use `EMetricSpace.toMetricSpace`
to ensure that this definition agrees with `e.emetricSpace`. -/
instance metricSpace : MetricSpace e.finiteSubspace := by
  letI := e.emetricSpace
  refine EMetricSpace.toMetricSpace fun x y => ?_
  change e (x - y) ≠ ⊤
  exact ne_top_of_le_ne_top (ENNReal.add_lt_top.2 ⟨x.2, y.2⟩).ne (e.map_sub_le x y)

/-- Normed group instance on `e.finiteSubspace`. -/
instance normedAddCommGroup : NormedAddCommGroup e.finiteSubspace :=
  { e.metricSpace with
    norm := fun x => (e x).toReal
    dist_eq := fun _ _ => rfl }

/-- Normed space instance on `e.finiteSubspace`. -/
instance normedSpace : NormedSpace 𝕜 e.finiteSubspace where
  norm_smul_le c x := le_of_eq <| by simp [finite_norm_eq, ENNReal.toReal_mul]

end ENormedSpace
