/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.IsROrC.Lemmas
import Mathlib.Topology.TietzeExtension
/-!
# `ℂ` satisfies the Tietze extension theorem

We provide this result here in order to avoid pulling unnecessary imports into either of
`Topology.TietzeExtension` or `Analysis.Complex.Basic`.
-/

universe u v w

-- this is not an instance because Lean cannot determine `𝕜`.
theorem TietzeExtension.of_tvs (𝕜 : Type v) [NontriviallyNormedField 𝕜] {E : Type w}
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [TopologicalAddGroup E] [ContinuousSMul 𝕜 E]
    [T2Space E] [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜] [TietzeExtension.{u, v} 𝕜] :
    TietzeExtension.{u, w} E :=
  Basis.ofVectorSpace 𝕜 E |>.equivFun.toContinuousLinearEquiv.toHomeomorph |> .of_homeo

instance Complex.instTietzeExtension : TietzeExtension ℂ :=
  TietzeExtension.of_tvs ℝ

instance IsROrC.instTietzeExtension {𝕜 : Type*} [IsROrC 𝕜] : TietzeExtension 𝕜 :=
  TietzeExtension.of_tvs ℝ

instance IsROrC.instTietzeExtensionTVS {𝕜 : Type v} [IsROrC 𝕜] {E : Type w}
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [TopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E] :
    TietzeExtension.{u, w} E :=
  TietzeExtension.of_tvs 𝕜
