/-
Copyright (c) 2025 Dominic Steinitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Steinitz
-/
import Mathlib.Topology.FiberBundle.Instances.GBundleDefs
import Mathlib.Topology.FiberBundle.Instances.Mobius

set_option linter.style.longLine false
set_option linter.style.lambdaSyntax false
set_option linter.style.cdot false

open Bundle Topology MulAction Set

/- Let's try this out with the circle as the base space, the real line as the fibre and the trivial group
(the only element is the identity) which btw shows that this is a trivial bundle. With the möbius bundle,
when we are able to specify it, the structure group would have to contain 2 elements to capture the twist.

But first we start with ℝˣ as the structure group!
 -/

noncomputable
def CylinderAsGBundle : GBundleCore (atlas (EuclideanSpace ℝ (Fin 1)) Circle) Circle ℝ ℝˣ where
  baseSet i := i.1.source
  isOpen_baseSet i := i.1.open_source
  indexAt := achart (EuclideanSpace ℝ (Fin 1))
  mem_baseSet_at := mem_chart_source (EuclideanSpace ℝ (Fin 1))
  coordChange i j x v := v
  coordChange_self _ _ _ _ := rfl
  continuousOn_coordChange i j := continuous_snd.continuousOn
  coordChange_comp _ _ _ _ _ _ := rfl
  coordChange_structure_group := by
    intro i j x hx
    have h1 : ∃ g : ℝˣ, ∀ v : ℝ, v = g • v := by
      existsi 1
      intro v
      have h2 : (1 : ℝ) • v = v := one_smul ℝ v
      exact h2.symm
    exact h1

open Matrix

instance {n : ℕ} : MulAction (orthogonalGroup (Fin n) ℝ) (EuclideanSpace ℝ (Fin n)) where
  smul g x := g.1.mulVec x
  one_smul x := by
    change (1 : orthogonalGroup (Fin n) ℝ).1.mulVec x = x
    simp [Matrix.mulVec_one]
  mul_smul f g x := by
    change (f * g).1.mulVec x = f.1.mulVec (g.1.mulVec x)
    simp [Matrix.mulVec_mulVec]

lemma orthGroupInv {n} {v : (EuclideanSpace ℝ (Fin n))} : (-1 : (orthogonalGroup (Fin n) ℝ)) • v = -v := by
 have h1 : (-1 : (orthogonalGroup (Fin n) ℝ)) • v = (-1 : (orthogonalGroup (Fin n) ℝ)).1.mulVec v := rfl
 have h2 : -1 *ᵥ v = -(1 *ᵥ v) := Matrix.neg_mulVec v (1 : Matrix (Fin n) (Fin n) ℝ)
 have h3 : -(1 *ᵥ v) = -v := by simp
 calc (-1 : (orthogonalGroup (Fin n) ℝ)) • v = (-1 : (orthogonalGroup (Fin n) ℝ)).1.mulVec v := rfl
      _ = -(1 *ᵥ v) := Matrix.neg_mulVec v (1 : Matrix (Fin n) (Fin n) ℝ)
      _ = -v := by simp

theorem MyCoordChange_structure_group : ∀ (i j : Fin 2),
  ∀ x ∈ (fun i ↦ if i = 0 then U.source else V.source) i ∩ (fun i ↦ if i = 0 then U.source else V.source) j,
    ∃ g : (orthogonalGroup (Fin 1) ℝ), ∀ (v : EuclideanSpace ℝ (Fin 1)), MyCoordChange i j x v = g • v := by
    intro i j x hx
    fin_cases i
    · fin_cases j
      . have h1 : ∃ g : (orthogonalGroup (Fin 1) ℝ), ∀ v : (EuclideanSpace ℝ (Fin 1)), v = g • v := by
            existsi 1
            intro v
            have h2 : (1 : (orthogonalGroup (Fin 1) ℝ)) • v = v := one_smul (orthogonalGroup (Fin 1) ℝ) v
            exact h2.symm
        exact h1
      · have h2 : ∃ (g : ↥(orthogonalGroup (Fin 1) ℝ)), ∀ (v : EuclideanSpace ℝ (Fin 1)),
          MyCoordChange ((fun i ↦ i) 0) ((fun i ↦ i) 1) x v = g • v := by
            by_cases h : (x.val 1) > (0 : ℝ)
            . existsi 1
              intro v
              have h5 : MyCoordChange ((fun i ↦ i) 0) ((fun i ↦ i) 1) x v = (1 : (orthogonalGroup (Fin 1) ℝ)) • v := by
                calc MyCoordChange ((fun i ↦ i) 0) ((fun i ↦ i) 1) x v = if (x.val 1) > 0 then v else -v := rfl
                     _ = v := if_pos h
                     _ = (1 : (orthogonalGroup (Fin 1) ℝ)) • v := (one_smul (orthogonalGroup (Fin 1) ℝ) v).symm
              exact h5
            . exists -1
              intro v
              have h5 : MyCoordChange ((fun i ↦ i) 0) ((fun i ↦ i) 1) x v = (-1 : (orthogonalGroup (Fin 1) ℝ)) • v := by
                calc MyCoordChange ((fun i ↦ i) 0) ((fun i ↦ i) 1) x v = if (x.val 1) > 0 then v else -v := rfl
                     _ = -v := if_neg h
                     _ = (-1 : (orthogonalGroup (Fin 1) ℝ)) • v := by exact orthGroupInv.symm
              exact h5
        exact h2
    · fin_cases j
      · have h2 : ∃ (g : ↥(orthogonalGroup (Fin 1) ℝ)), ∀ (v : EuclideanSpace ℝ (Fin 1)),
          MyCoordChange ((fun i ↦ i) 1) ((fun i ↦ i) 0) x v = g • v := by
          by_cases h : (x.val 1) > (0 : ℝ)
          . existsi 1
            intro v
            have h5 : MyCoordChange ((fun i ↦ i) 1) ((fun i ↦ i) 0) x v = (1 : (orthogonalGroup (Fin 1) ℝ)) • v := by
                calc MyCoordChange ((fun i ↦ i) 1) ((fun i ↦ i) 0) x v = if (x.val 1) > 0 then v else -v := rfl
                     _ = v := if_pos h
                     _ = (1 : (orthogonalGroup (Fin 1) ℝ)) • v := (one_smul (orthogonalGroup (Fin 1) ℝ) v).symm
            exact h5
          . existsi -1
            intro v
            have h5 : MyCoordChange ((fun i ↦ i) 1) ((fun i ↦ i) 0) x v = (-1 : (orthogonalGroup (Fin 1) ℝ)) • v := by
                calc MyCoordChange ((fun i ↦ i) 1) ((fun i ↦ i) 0) x v = if (x.val 1) > 0 then v else -v := rfl
                     _ = -v := if_neg h
                     _ = (-1 : (orthogonalGroup (Fin 1) ℝ)) • v := by exact orthGroupInv.symm
            exact h5
        exact h2
      · have h1 : ∃ g : (orthogonalGroup (Fin 1) ℝ), ∀ v : (EuclideanSpace ℝ (Fin 1)), v = g • v := by
            existsi 1
            intro v
            have h2 : (1 : (orthogonalGroup (Fin 1) ℝ)) • v = v := one_smul (orthogonalGroup (Fin 1) ℝ) v
            exact h2.symm
        exact h1

noncomputable
def MobiusAsGBundle : GBundleCore (Fin 2) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) (EuclideanSpace ℝ (Fin 1)) (orthogonalGroup (Fin 1) ℝ) where
  baseSet i := if i = 0 then U.source else V.source
  isOpen_baseSet := by
    intro i
    split
    · exact U.open_source
    · exact V.open_source
  indexAt x := if (x.val 0) > 0 then 0 else 1
  mem_baseSet_at := my_mem_baseSet_at
  coordChange := MyCoordChange
  coordChange_self := MyCoordChange_self
  continuousOn_coordChange := by
    intro i j
    exact MyContinuousOn_coordChange i j
  coordChange_comp := MyCoordChange_comp
  coordChange_structure_group := MyCoordChange_structure_group
