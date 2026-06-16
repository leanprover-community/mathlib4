/-
Copyright (c) 2026 Ben Eltschig, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-! # Algebra instances on vector bundles

In this file we prove that for every Cⁿ `𝕜`-vector bundle `E`, the action of `𝕜` on
`Bundle.TotalSpace F E` is Cⁿ too. The file name is kept general so that if we add typeclasses for
things like fibre bundles with a Cⁿ fibrewise addition in the future, we can add instances for them
here too.
-/

public section

open Bundle FiberBundle

open scoped ContDiff Manifold

variable {n : ℕ∞ω} {𝕜 B B' F M : Type*} {E : B → Type*}
  [NontriviallyNormedField 𝕜] {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B]
  [ChartedSpace HB B] {EM : Type*} [NormedAddCommGroup EM]
  [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners 𝕜 EM HM}
  [TopologicalSpace M] [ChartedSpace HM M]
  [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)]
  [FiberBundle F E] [VectorBundle 𝕜 F E] [ContMDiffVectorBundle n F E IB]

/-- The action of `𝕜` on the total space of any Cⁿ bundle of `𝕜`-vector spaces is Cⁿ. -/
instance : ContMDiffSMul 𝓘(𝕜, 𝕜) (IB.prod 𝓘(𝕜, F)) n 𝕜 (TotalSpace F E) where
  contMDiff_smul := by
    suffices h : ∀ b, ContMDiffOn (𝓘(𝕜, 𝕜).prod (IB.prod 𝓘(𝕜, F))) (IB.prod 𝓘(𝕜, F)) n
        (fun x : 𝕜 × TotalSpace F E ↦ x.1 • x.2)
          (.univ ×ˢ (π F E ⁻¹' (trivializationAt F E b).baseSet)) from
      fun ⟨a, x⟩ ↦ (h x.1).contMDiffAt <|
        prod_mem_nhds Filter.univ_mem <| ((trivializationAt F E x.1).open_baseSet.preimage <|
          continuous_proj F E).mem_nhds <| mem_baseSet_trivializationAt F E _
    refine fun b ↦ .congr (f := fun x ↦ ⟨_, (trivializationAt F E b).symm x.2.1
        (x.1 • (trivializationAt F E b x.2).2)⟩) ?_ fun ⟨a, x⟩ ⟨_, hx⟩ ↦ by
      ext
      · rfl
      · simp only [heq_eq_eq, ← ((trivializationAt F E b).linear _ hx).map_smul]
        exact ((trivializationAt F E b).symm_proj_apply ⟨x.1, a • x.2⟩ hx).symm
    refine ((trivializationAt F E b).contMDiffOn_symm (n := n) (IB := IB).comp
      (f := (fun x : 𝕜 × _ ↦ ⟨x.2.1, x.1 • (trivializationAt F E b x.2).2⟩)) ?_ ?_).congr ?_
    · refine ((contMDiff_proj E).comp contMDiff_snd).contMDiffOn.prodMk ?_
      refine contMDiff_smul.comp_contMDiffOn ?_ (I' := 𝓘(𝕜, 𝕜).prod 𝓘(𝕜, F))
        (f := fun x : 𝕜 × TotalSpace F E ↦ (x.1, (trivializationAt F E b x.2).2))
      refine contMDiffOn_id.prodMap (g := fun x ↦ (trivializationAt F E b x).2) ?_
      refine contMDiff_snd.comp_contMDiffOn ?_ (I' := IB.prod 𝓘(𝕜, F))
      rw [← (trivializationAt F E b).source_eq]
      exact (trivializationAt F E b).contMDiffOn
    · rw [Trivialization.target_eq]
      exact fun ⟨a, x⟩ ⟨_, hx⟩ ↦ ⟨hx, trivial⟩
    · intro x hx
      ext
      · simp_all
      · simp [Trivialization.symm_apply _ hx.2]
