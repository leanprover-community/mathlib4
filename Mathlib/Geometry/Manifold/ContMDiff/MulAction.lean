/-
Copyright (c) 2026 Cody Mitchell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cody Mitchell
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Constructions

/-!
# Smooth scalar actions on manifolds

This file defines typeclasses for scalar actions that are smooth in one or both variables, together
with the corresponding API for `ContMDiff*`.

## Main definitions

* `ContMDiffConstSMul`: the action `x ↦ c • x` is `C^n` for every constant scalar `c`;
* `ContMDiffSMul`: the action `(c, x) ↦ c • x` is `C^n` in both variables.

## Main results

* `ContMDiffWithinAt.smul`, `ContMDiffAt.smul`, `ContMDiffOn.smul`, `ContMDiff.smul`;
* `ContMDiffWithinAt.const_smul`, `ContMDiffAt.const_smul`,
  `ContMDiffOn.const_smul`, `ContMDiff.const_smul`;
* `ContMDiffSMul.contMDiffConstSMul`: a smooth action is smooth in the second variable.
-/

public section

open Set Function Filter ChartedSpace Pointwise

open scoped Topology Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {EΓ : Type*} [NormedAddCommGroup EΓ] [NormedSpace 𝕜 EΓ]
  {HΓ : Type*} [TopologicalSpace HΓ]
  {IΓ : ModelWithCorners 𝕜 EΓ HΓ} {Γ : Type*} [TopologicalSpace Γ] [ChartedSpace HΓ Γ]
  {s : Set M} {x : M} {n : WithTop ℕ∞}

/-- Typeclass asserting that scalar multiplication by any constant is smooth. -/
class ContMDiffConstSMul (J : ModelWithCorners 𝕜 E' H') (n : WithTop ℕ∞) (Γ : Type*) (N : Type*)
    [TopologicalSpace N] [ChartedSpace H' N] [SMul Γ N] : Prop where
  contMDiff_const_smul : ∀ c : Γ, ContMDiff J J n (fun y : N ↦ c • y)

/-- Typeclass asserting that scalar multiplication is smooth in both variables. -/
class ContMDiffSMul (IΓ : ModelWithCorners 𝕜 EΓ HΓ) (J : ModelWithCorners 𝕜 E' H')
    (n : WithTop ℕ∞) (Γ : Type*) (N : Type*) [TopologicalSpace Γ] [ChartedSpace HΓ Γ]
    [TopologicalSpace N] [ChartedSpace H' N] [SMul Γ N] : Prop where
  contMDiff_smul : ContMDiff (IΓ.prod J) J n (fun p : Γ × N ↦ p.1 • p.2)

export ContMDiffConstSMul (contMDiff_const_smul)
export ContMDiffSMul (contMDiff_smul)

section Main

section Instances

variable {Γ' : Type*} [TopologicalSpace Γ'] [ChartedSpace H' Γ']
  {N' : Type*} [TopologicalSpace N'] [ChartedSpace H' N'] [SMul Γ' N']
  [ContMDiffSMul J J n Γ' N']

instance (priority := 100) ContMDiffSMul.contMDiffConstSMul :
    ContMDiffConstSMul J n Γ' N' where
  contMDiff_const_smul c :=
    (contMDiff_smul (IΓ := J) (J := J) (n := n) (Γ := Γ') (N := N')).comp
      ((contMDiff_const : ContMDiff J J n fun _ : N' ↦ c).prodMk
        (contMDiff_id : ContMDiff J J n fun y : N' ↦ y))

end Instances

section SMul

variable [SMul Γ N] [ContMDiffSMul IΓ J n Γ N]

/-- The scalar multiplication of two `C^n` functions within a set at a point is `C^n` within this
set at this point. -/
theorem ContMDiffWithinAt.smul {f : M → Γ} {g : M → N} (hf : ContMDiffWithinAt I IΓ n f s x)
    (hg : ContMDiffWithinAt I J n g s x) : ContMDiffWithinAt I J n (f • g) s x :=
  (contMDiff_smul (IΓ := IΓ) (J := J) (n := n) (Γ := Γ) (N := N)).contMDiffAt.comp_contMDiffWithinAt
    x (hf.prodMk hg)

/-- The scalar multiplication of two `C^n` functions at a point is `C^n` at this point. -/
theorem ContMDiffAt.smul {f : M → Γ} {g : M → N} (hf : ContMDiffAt I IΓ n f x)
    (hg : ContMDiffAt I J n g x) : ContMDiffAt I J n (f • g) x := by
  rw [← contMDiffWithinAt_univ] at *
  exact hf.smul hg

/-- The scalar multiplication of two `C^n` functions on a domain is `C^n` on this domain. -/
theorem ContMDiffOn.smul {f : M → Γ} {g : M → N} (hf : ContMDiffOn I IΓ n f s)
    (hg : ContMDiffOn I J n g s) : ContMDiffOn I J n (f • g) s := fun y hy =>
  (hf y hy).smul (hg y hy)

/-- The scalar multiplication of two `C^n` functions is `C^n`. -/
theorem ContMDiff.smul {f : M → Γ} {g : M → N} (hf : ContMDiff I IΓ n f) (hg : ContMDiff I J n g) :
    ContMDiff I J n (f • g) :=
  (contMDiff_smul (IΓ := IΓ) (J := J) (n := n) (Γ := Γ) (N := N)).comp (hf.prodMk hg)

end SMul

section ConstSMul

variable {R : Type*} [SMul R N] [ContMDiffConstSMul J n R N]

/-- The scalar multiplication of a constant and a `C^n` function within a set at a point is `C^n`
within this set at this point. -/
theorem ContMDiffWithinAt.const_smul {f : M → N} (c : R) (hf : ContMDiffWithinAt I J n f s x) :
    ContMDiffWithinAt I J n (fun y ↦ c • f y) s x :=
  (contMDiff_const_smul (J := J) (n := n) (Γ := R) (N := N) c).contMDiffAt.comp_contMDiffWithinAt
    x hf

/-- The scalar multiplication of a constant and a `C^n` function at a point is `C^n` at this
point. -/
theorem ContMDiffAt.const_smul {f : M → N} (c : R) (hf : ContMDiffAt I J n f x) :
    ContMDiffAt I J n (fun y ↦ c • f y) x := by
  rw [← contMDiffWithinAt_univ] at *
  exact hf.const_smul c

/-- The scalar multiplication of a constant and a `C^n` function on a domain is `C^n` on this
domain. -/
theorem ContMDiffOn.const_smul {f : M → N} (hf : ContMDiffOn I J n f s) (c : R) :
    ContMDiffOn I J n (fun y ↦ c • f y) s := fun y hy =>
  (hf y hy).const_smul c

/-- The scalar multiplication of a constant and a `C^n` function is `C^n`. -/
theorem ContMDiff.const_smul {f : M → N} (hf : ContMDiff I J n f) (c : R) :
    ContMDiff I J n (fun y ↦ c • f y) := fun y =>
  (hf y).const_smul c

end ConstSMul

end Main
