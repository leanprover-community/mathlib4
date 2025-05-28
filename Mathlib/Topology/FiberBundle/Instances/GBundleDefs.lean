/-
Copyright (c) 2025 Dominic Steinitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Steinitz
-/
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.FiberBundle.Basic
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.FiberBundle.Basic


open Matrix Bundle Manifold

structure GBundleCore (ι : Type*) (B : Type*) [TopologicalSpace B]
  (F : Type*) [TopologicalSpace F]
  (G : Type*) [Group G] [MulAction G F] extends FiberBundleCore ι B F where
  coordChange_structure_group :
    ∀ i j, ∀ x ∈ baseSet i ∩ baseSet j, ∃ g : G, ∀ v : F, coordChange i j x v = g • v

open RightActions

class SmoothLeftGAction
{𝕜 : Type*} [NontriviallyNormedField 𝕜] (n : WithTop ℕ∞)
{E_G : Type*} [NormedAddCommGroup E_G] [NormedSpace 𝕜 E_G]
{E_M : Type*} [NormedAddCommGroup E_M] [NormedSpace 𝕜 E_M]
{H_G : Type*} [TopologicalSpace H_G] (I_G : ModelWithCorners 𝕜 E_G H_G)
{H_M : Type*} [TopologicalSpace H_M] (I_M : ModelWithCorners 𝕜 E_M H_M)
(G : Type*) [TopologicalSpace G] [ChartedSpace H_G G] [Group G] [LieGroup I_G n G]
(M : Type*) [TopologicalSpace M] [ChartedSpace H_M M]
[MulAction G M]
[IsManifold I_G n G]
[IsManifold I_M n M] : Prop where
  (smooth_smul : ContMDiff (I_G.prod I_M) I_M ⊤ (fun p : G × M => p.1 •> p.2))

class SmoothRightGAction
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] (n : WithTop ℕ∞)
  {E_G : Type*} [NormedAddCommGroup E_G] [NormedSpace 𝕜 E_G]
  {E_M : Type*} [NormedAddCommGroup E_M] [NormedSpace 𝕜 E_M]
  {H_G : Type*} [TopologicalSpace H_G] (I_G : ModelWithCorners 𝕜 E_G H_G)
  {H_M : Type*} [TopologicalSpace H_M] (I_M : ModelWithCorners 𝕜 E_M H_M)
  (G : Type*) [TopologicalSpace G] [ChartedSpace H_G G] [Group G] [LieGroup I_G n G]
  (M : Type*) [TopologicalSpace M] [ChartedSpace H_M M]
  [MulAction (MulOpposite G) M]
  [IsManifold I_G n G]
  [IsManifold I_M n M]
  : Prop where
  smooth_smul : ContMDiff (I_M.prod I_G) I_M ⊤ (fun p : M × G => p.1 <• p.2)

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {n : WithTop ℕ∞}
variable {E_G E_M : Type*} [NormedAddCommGroup E_G] [NormedAddCommGroup E_M]
variable [NormedSpace 𝕜 E_G] [NormedSpace 𝕜 E_M]
variable {H_G H_M : Type*} [TopologicalSpace H_G] [TopologicalSpace H_M]
variable {G : Type*} [TopologicalSpace G] [ChartedSpace H_G G] [Group G]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H_M M]
variable {I_G : ModelWithCorners 𝕜 E_G H_G}
variable {I_M : ModelWithCorners 𝕜 E_M H_M}
variable [LieGroup I_G n G]
variable [IsManifold I_G n G] [IsManifold I_M n M]
variable [MulAction G M] [SmoothLeftGAction n I_G I_M G M]

open MulOpposite

instance mulAction_op_of_left [Group G] [MulAction G M] : MulAction (Gᵐᵒᵖ) M where
  smul g m := (unop g)⁻¹ • m
  one_smul := by
    intro b
    have h1 : (1 : G) • b = b := MulAction.one_smul b
    have h3 : unop (1 : Gᵐᵒᵖ)⁻¹ •> b = b := by rw [<-inv_one] at h1; exact h1
    exact h3

  mul_smul := by
    intro g₁ g₂ m
    have h1 : (unop (g₁ * g₂))⁻¹ •> m = (unop g₁)⁻¹ • ((unop g₂)⁻¹ • m) := by
      calc
      (unop (g₁ * g₂))⁻¹ •> m
        = (unop g₂ * unop g₁)⁻¹ •> m       := by rw [unop_mul]
      _ = ((unop g₁)⁻¹ * (unop g₂)⁻¹) •> m := by rw [_root_.mul_inv_rev]
      _ = (unop g₁)⁻¹ • ((unop g₂)⁻¹ • m)  := by rw [MulAction.mul_smul]
    exact h1

instance SmoothRightGAction_of_Left
  [MulAction G M]
  [LieGroup I_G ⊤ G]
  [ IsManifold I_M ⊤ M]

  [SmoothLeftGAction ⊤ I_G I_M G M] :
  SmoothRightGAction ⊤ I_G I_M G M where

  smooth_smul := by
    let f : M × G → G × M := fun (p, g) => (g⁻¹, p)
    have hf : ContMDiff (I_M.prod I_G) (I_G.prod I_M) ⊤ f := by
      apply ContMDiff.prodMk
      · exact ContMDiff.comp (contMDiff_inv I_G ⊤) contMDiff_snd
      · exact contMDiff_fst
    exact ContMDiff.comp (SmoothLeftGAction.smooth_smul ⊤) hf

universe uK uB uF uH uI uG uP

structure PrincipalBundleCore
  (ι : Type uP)
  {𝕜 : Type uK} [NontriviallyNormedField 𝕜]
  {n : WithTop ℕ∞}
  {E_B : Type uB} {E_F : Type uF} {E_G : Type uG}
  [NormedAddCommGroup E_B] [NormedSpace 𝕜 E_B]
  [NormedAddCommGroup E_F] [NormedSpace 𝕜 E_F]
  [NormedAddCommGroup E_G] [NormedSpace 𝕜 E_G]
  {H_B : Type uH} {H_F : Type uI} {H_G : Type uG}
  [TopologicalSpace H_B] [TopologicalSpace H_F] [TopologicalSpace H_G]
  {I_B : ModelWithCorners 𝕜 E_B H_B}
  {I_F : ModelWithCorners 𝕜 E_F H_F}
  {I_G : ModelWithCorners 𝕜 E_G H_G}
  (B : Type uB) [TopologicalSpace B] [ChartedSpace H_B B] [IsManifold I_B n B]
  (F : Type uF) [TopologicalSpace F]
  [TopologicalSpace G] [ChartedSpace H_G G] [Group G] [LieGroup I_G n G]
  (core : FiberBundleCore ι B F)
  [MulAction (MulOpposite G) (TotalSpace F (core.Fiber))]
  [ChartedSpace (ModelProd H_B H_F) (TotalSpace F core.Fiber)]
  [IsManifold (ModelWithCorners.prod I_B I_F) n (TotalSpace F core.Fiber)]
  [SmoothRightGAction n I_G (ModelWithCorners.prod I_B I_F) G (TotalSpace F core.Fiber)]
  where
  (respects_fibres : ∀ (p : TotalSpace F (core.Fiber)) (g : G), core.proj (p <• g) = core.proj p)
  (is_free : ∀ (p : TotalSpace F (core.Fiber)) (g : G), p <• g = p → g = 1)
  (is_transitive : ∀ (p q : TotalSpace F (core.Fiber)),
    core.proj p = core.proj q → ∃ g : G, p <• g = q)

-- TODO: move to better location
instance {α : Type*} [DecidableEq α] [Fintype α] : MulAction (orthogonalGroup α ℝ) (α -> ℝ) where
  smul g x := g.1.mulVec x
  one_smul x := by
    change (1 : orthogonalGroup α ℝ).1.mulVec x = x
    simp [Matrix.mulVec_one]
  mul_smul := fun f g x => by
    show (f * g).1.mulVec x = f.1.mulVec (g.1.mulVec x)
    simp [Matrix.mulVec_mulVec]
