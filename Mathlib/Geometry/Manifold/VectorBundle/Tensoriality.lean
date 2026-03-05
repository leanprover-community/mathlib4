/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang, Heather Macbeth
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.Misc
public import Mathlib.Geometry.Manifold.VectorBundle.Extend
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
public import Mathlib.Geometry.Manifold.VectorBundle.IsBilinearPrelim

/-!
# The tensoriality criterion

-/
open Bundle Filter Function Topology Module

open scoped Bundle Manifold ContDiff

@[expose] public section -- TODO: think if we want to expose all definitions!

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable
  -- `F` model fiber
  (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  -- `V` vector bundle
  (V : M → Type*) [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x : M, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  [ContMDiffVectorBundle 1 F V I]

variable
  (F' : Type*) [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] [FiniteDimensional 𝕜 F']
  (V' : M → Type*) [TopologicalSpace (TotalSpace F' V')]
  [∀ x, AddCommGroup (V' x)] [∀ x, Module 𝕜 (V' x)] [∀ x : M, TopologicalSpace (V' x)]
  [FiberBundle F' V'] [VectorBundle 𝕜 F' V']
  [ContMDiffVectorBundle 1 F' V' I]

variable (G : Type*) [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  (W : M → Type*) [∀ x, AddCommGroup (W x)] [∀ x, Module 𝕜 (W x)]

lemma tensoriality_criterion
    {φ : (Π x : M, V x) → (Π x, W x)} {x}
    {σ σ' : Π x : M, V x} (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x)
    (hσσ' : σ x = σ' x)
    (φ_smul : ∀ f : M → 𝕜, ∀ σ, MDiffAt f x → MDiffAt (T% σ) x →
      φ (f • σ) x = f x • φ σ x)
    (φ_add : ∀ σ σ', MDiffAt (T% σ) x → MDiffAt (T% σ') x →
      φ (σ + σ') x = φ σ x + φ σ' x) : φ σ x = φ σ' x := by
  have locality {σ σ'} (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x)
      (hσσ' : ∀ᶠ x' in 𝓝 x, σ x' = σ' x') : φ σ x = φ σ' x := by
    classical
    rw [eventually_nhds_iff] at hσσ'
    obtain ⟨t, htσσ', ht, hxt⟩ := hσσ'
    let ψ (x' : M) : 𝕜 := if x' ∈ t then 1 else 0
    have hψx : ψ x = 1 := by simp [ψ, hxt]
    have (x' : M) : ((ψ : M → 𝕜) • σ) x' = ((ψ : M → 𝕜) • σ') x' := by
      dsimp [ψ]
      split_ifs with hx't
      · simpa using htσσ' _ hx't
      · simp
    have hψ' : MDifferentiableAt I 𝓘(𝕜) ψ x := by
      have : MDifferentiableAt I 𝓘(𝕜, 𝕜) (fun x_1 ↦ (1:𝕜)) x := mdifferentiableAt_const
      refine this.congr_of_eventuallyEq ?_
      apply eventually_nhds_iff.mpr
      exact ⟨t, by simp [ψ], ht, hxt⟩
    calc φ σ x
      _ = φ ((ψ : M → 𝕜) • σ) x := by simp [φ_smul _ _ hψ' hσ, hψx]
      _ = φ ((ψ : M → 𝕜) • σ') x := by rw [funext this]
      _ = φ σ' x := by simp [φ_smul _ _ hψ' hσ', hψx]
  let ι : Type _ := Basis.ofVectorSpaceIndex 𝕜 F
  classical
  have sum_phi {s : Finset ι} (σ : ι → Π x : M, V x)
      (hσ : ∀ i, MDiffAt  (T% (σ i)) x):
      φ (fun x' ↦ ∑ i ∈ s, σ i x') x = ∑ i ∈ s, φ (σ i) x := by
    induction s using Finset.induction_on with
    | empty =>
       simp only [Finset.sum_empty]
       have h₁ : MDiffAt (fun x' : M ↦ (0 : 𝕜)) x := mdifferentiableAt_const
       rw [show (fun x' : M ↦ (0 : V x')) = (0 : M → 𝕜) • fun x' ↦ 0 by simp;rfl]
       rw [φ_smul]
       · simp
       · exact h₁
       -- TODO: add mdifferentiable_zeroSection and/or use it!
       apply (contMDiff_zeroSection _ _).mdifferentiableAt one_ne_zero
    | insert a s ha h =>
        change φ (fun x' : M ↦ ∑ i ∈ (insert a s : Finset ι), σ i x') x = _
        simp only [Finset.sum_insert ha, ← h]
        exact φ_add _ _ (hσ a) (.sum_section hσ)
  have x_mem := (FiberBundle.mem_baseSet_trivializationAt F V x)
  let b := Basis.ofVectorSpace 𝕜 F
  let t := trivializationAt F V x
  let s := t.localFrame b
  let c := t.localFrame_coeff I b
  have hs (i) : MDiffAt (T% (s i)) x:=
    (contMDiffAt_localFrame_of_mem 1 _ b i x_mem).mdifferentiableAt (by simp)
  have hc {σ : (x : M) → V x} (hσ : MDiffAt (T% σ) x) (i) :
      MDiffAt (LinearMap.piApply (c i) σ) x :=
    mdifferentiableAt_localFrame_coeff b x_mem hσ i
  have hφ {σ : (x : M) → V x}
          (hσ : MDiffAt (T% σ) x) :
      φ σ x = φ (fun x' ↦ ∑ i, LinearMap.piApply (c i) σ x' • s i x') x := by
    exact
      locality hσ
        (.sum_section fun i ↦ (hc hσ i).smul_section (hs i))
        (t.eventually_eq_localFrame_sum_coeff_smul b x_mem)
  rw [hφ hσ, hφ hσ', sum_phi, sum_phi]
  · change ∑ i, φ ((LinearMap.piApply (c i) σ) • (s i)) x =
      ∑ i, φ ((LinearMap.piApply (c i) σ') • (s i)) x
    congr
    ext i
    rw [φ_smul _ _ (hc hσ i) (hs i), φ_smul _ _ (hc hσ' i) (hs i)]
    simp [hσσ']
  · exact fun i ↦ (hc hσ' i).smul_section (hs i)
  · exact fun i ↦ (hc hσ i).smul_section (hs i)

include I in
lemma tensoriality_criterion₂
    {φ : (Π x : M, V x) → (Π x : M, V' x) → (Π x, W x)} {x}
    {σ σ' : Π x : M, V x}
    {τ τ' : Π x : M, V' x}
    (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x)
    (hτ : MDiffAt (T% τ) x) (hτ' : MDiffAt (T% τ') x)
    (hσσ' : σ x = σ' x)
    (hττ' : τ x = τ' x)
    (σ_smul : ∀ f : M → 𝕜, ∀ {σ τ}, MDiffAt f x → MDiffAt (T% σ) x → MDiffAt (T% τ) x →
      φ (f • σ) τ x = f x • φ σ τ x)
    (σ_add : ∀ σ σ' τ, MDiffAt (T% σ) x → MDiffAt (T% σ') x → MDiffAt (T% τ) x →
      φ (σ + σ') τ x = φ σ τ x + φ σ' τ x)
    (τ_smul : ∀ f : M → 𝕜, ∀ {σ τ}, MDiffAt f x → MDiffAt (T% σ) x → MDiffAt (T% τ) x →
        φ σ (f • τ) x = f x • φ σ τ x)
    (τ_add : ∀ σ τ τ', MDiffAt (T% σ) x → MDiffAt (T% τ) x → MDiffAt (T% τ') x →
        φ σ (τ + τ') x = φ σ τ x + φ σ τ' x) : φ σ τ x = φ σ' τ' x := by
  trans φ σ' τ x
  · let φ1 : (Π x : M, V x) → (Π x, W x) := fun X ↦ φ X τ
    change φ1 σ x = φ1 σ' x
    apply tensoriality_criterion I F V W hσ hσ' hσσ'
    exacts [fun f σ hf hσ ↦ σ_smul _ hf hσ hτ, fun σ σ' hσ hσ' ↦ σ_add _ _ _ hσ hσ' hτ]
  · let φ1 : (Π x : M, V' x) → (Π x, W x) := fun X ↦ φ σ' X
    change φ1 τ x = φ1 τ' x
    apply tensoriality_criterion I F' V' W hτ hτ' hττ'
    exacts [fun f τ hf hτ ↦ τ_smul _ hf hσ' hτ, fun τ τ' hτ hτ' ↦ τ_add _ _ _ hσ' hτ hτ']

section tensoriality

variable [IsManifold I 1 M]

variable
  {V}
  -- TODO can probably remove the next two hypotheses, by transport
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]

variable
  {V'}
  -- TODO can probably remove the next two hypotheses, by transport
  [∀ x, IsTopologicalAddGroup (V' x)] [∀ x, ContinuousSMul 𝕜 (V' x)]

variable
  {W}
  -- TODO can probably remove the next three hypotheses, by transport
  [∀ x : M, TopologicalSpace (W x)]
  [∀ x, IsTopologicalAddGroup (W x)]
  [∀ x, ContinuousSMul 𝕜 (W x)]
  [TopologicalSpace (TotalSpace G W)]
  [FiberBundle G W] [VectorBundle 𝕜 G W]

noncomputable def mkTensorAt
    -- `φ` explicit to make it easier to generate the side conditions at point of use
    (φ : (Π x : M, V x) → (Π x, W x)) (x)
    (φ_smul : ∀ f : M → 𝕜, ∀ σ, MDiffAt f x → MDiffAt (T% σ) x →
      φ (f • σ) x = f x • φ σ x)
    (φ_add : ∀ σ σ', MDiffAt (T% σ) x → MDiffAt (T% σ') x →
      φ (σ + σ') x = φ σ x + φ σ' x) :
    V x →L[𝕜] W x :=
    let Ψ : V x ≃L[𝕜] F := (trivializationAt F V x).continuousLinearEquivAt 𝕜 x
      (FiberBundle.mem_baseSet_trivializationAt' x)
    have : T2Space (V x) := Ψ.symm.toHomeomorph.t2Space
    have : FiniteDimensional 𝕜 (V x) := Ψ.symm.toLinearEquiv.finiteDimensional
    LinearMap.toContinuousLinearMap {
      toFun v := φ (_root_.extend F v) x
      map_add' v₁ v₂ := by
        rw [← φ_add]
        · apply tensoriality_criterion I F _ _ _ _ _ φ_smul φ_add
          · exact mdifferentiableAt_extend ..
          · apply mdifferentiableAt_add_section
            · exact mdifferentiableAt_extend ..
            · exact mdifferentiableAt_extend ..
          · simp
        · exact mdifferentiableAt_extend ..
        · exact mdifferentiableAt_extend ..
      map_smul' c v := by
        dsimp
        rw [← φ_smul (fun _ ↦ c)]
        · apply tensoriality_criterion I F _ _ _ _ _ φ_smul φ_add
          · exact mdifferentiableAt_extend ..
          · apply MDifferentiableAt.smul_section
            · exact mdifferentiableAt_const
            · exact mdifferentiableAt_extend ..
          · simp
        · exact mdifferentiable_const ..
        · exact mdifferentiableAt_extend .. }

variable {I} in
theorem mkTensorAt_apply
    -- `φ` explicit to make it easier to generate the side conditions at point of use
    {φ : (Π x : M, V x) → (Π x, W x)} {x}
    (φ_smul : ∀ f : M → 𝕜, ∀ σ, MDiffAt f x → MDiffAt (T% σ) x →
      φ (f • σ) x = f x • φ σ x)
    (φ_add : ∀ σ σ', MDiffAt (T% σ) x → MDiffAt (T% σ') x →
      φ (σ + σ') x = φ σ x + φ σ' x) {σ : Π x : M, V x} (hσ : MDiffAt (T% σ) x) :
    mkTensorAt I F φ x φ_smul φ_add (σ x) = φ σ x := by
  apply tensoriality_criterion I F _ _ _ hσ _ φ_smul φ_add
  · exact mdifferentiableAt_extend ..
  · simp

variable {I} in
theorem mkTensorAt_apply_eq_extend
    -- `φ` explicit to make it easier to generate the side conditions at point of use
    {φ : (Π x : M, V x) → (Π x, W x)} {x}
    (φ_smul : ∀ f : M → 𝕜, ∀ σ, MDiffAt f x → MDiffAt (T% σ) x →
      φ (f • σ) x = f x • φ σ x)
    (φ_add : ∀ σ σ', MDiffAt (T% σ) x → MDiffAt (T% σ') x →
      φ (σ + σ') x = φ σ x + φ σ' x) (σ : V x) :
    mkTensorAt I F φ x φ_smul φ_add σ = φ (_root_.extend F σ) x :=
  rfl

noncomputable def mkTensor
    -- `φ` explicit to make it easier to generate the side conditions at point of use
    (φ : (Π x : M, V x) → (Π x, W x))
    (φ_smul : ∀ x, ∀ f : M → 𝕜, ∀ σ, MDiffAt f x → MDiffAt (T% σ) x → φ (f • σ) x = f x • φ σ x)
    (φ_add : ∀ x, ∀ σ σ', MDiffAt (T% σ) x → MDiffAt (T% σ') x → φ (σ + σ') x = φ σ x + φ σ' x)
    (x : M) :
    V x →L[𝕜] W x :=
  mkTensorAt I F φ x (φ_smul x) (φ_add x)

theorem contMDiff_mkTensor
    (φ : (Π x : M, V x) → (Π x, W x))
    (φ_smul : ∀ x, ∀ f : M → 𝕜, ∀ σ, MDiffAt f x → MDiffAt (T% σ) x → φ (f • σ) x = f x • φ σ x)
    (φ_add : ∀ x, ∀ σ σ', MDiffAt (T% σ) x → MDiffAt (T% σ') x → φ (σ + σ') x = φ σ x + φ σ' x)
    -- hopefully this is the correct smoothness criterion!
    {k} (φ_contMDiff : ∀ (σ : Π x : M, V x), CMDiff k (T% σ) → CMDiff k (T% (φ σ))) :
    -- elaborators not working here
    let T (x : M) : TotalSpace (F →L[𝕜] G) (fun x ↦ V x →L[𝕜] W x) :=
      ⟨x, mkTensor I F φ φ_smul φ_add x⟩
    ContMDiff I (I.prod 𝓘(𝕜, F →L[𝕜] G)) k T := by
  sorry

noncomputable def mk2TensorAt
    -- `φ` explicit to make it easier to generate the side conditions at point of use
    (φ : (Π x : M, V x) → (Π x : M, V' x) → (Π x, W x)) {x}
    (σ_smul : ∀ f : M → 𝕜, ∀ {σ τ}, MDiffAt f x → MDiffAt (T% σ) x → MDiffAt (T% τ) x →
      φ (f • σ) τ x = f x • φ σ τ x)
    (σ_add : ∀ σ σ' τ, MDiffAt (T% σ) x → MDiffAt (T% σ') x → MDiffAt (T% τ) x →
      φ (σ + σ') τ x = φ σ τ x + φ σ' τ x)
    (τ_smul : ∀ f : M → 𝕜, ∀ {σ τ}, MDiffAt f x → MDiffAt (T% σ) x → MDiffAt (T% τ) x →
        φ σ (f • τ) x = f x • φ σ τ x)
    (τ_add : ∀ σ τ τ', MDiffAt (T% σ) x → MDiffAt (T% τ) x → MDiffAt (T% τ') x →
        φ σ (τ + τ') x = φ σ τ x + φ σ τ' x) :
    V x →L[𝕜] V' x →L[𝕜] W x :=
    let Ψ : V x ≃L[𝕜] F := (trivializationAt F V x).continuousLinearEquivAt 𝕜 x
      (FiberBundle.mem_baseSet_trivializationAt' x)
    have : T2Space (V x) := Ψ.symm.toHomeomorph.t2Space
    have : FiniteDimensional 𝕜 (V x) := Ψ.symm.toLinearEquiv.finiteDimensional
    let Ψ' : V' x ≃L[𝕜] F' := (trivializationAt F' V' x).continuousLinearEquivAt 𝕜 x
      (FiberBundle.mem_baseSet_trivializationAt' x)
    have : T2Space (V' x) := Ψ'.symm.toHomeomorph.t2Space
    have : FiniteDimensional 𝕜 (V' x) := Ψ'.symm.toLinearEquiv.finiteDimensional
    have H : IsBilinearMap 𝕜
      (fun (v : V x) (w : V' x) ↦ φ (_root_.extend F v) (_root_.extend F' w) x) :=
    { add_left v₁ v₂ w := by
        rw [← σ_add]
        · apply tensoriality_criterion₂ I F _ F' _ _ _ _ _ _ _ rfl σ_smul σ_add τ_smul τ_add
          · exact mdifferentiableAt_extend ..
          · apply mdifferentiableAt_add_section
            · exact mdifferentiableAt_extend ..
            · exact mdifferentiableAt_extend ..
          · exact mdifferentiableAt_extend ..
          · exact mdifferentiableAt_extend ..
          · simp
        · exact mdifferentiableAt_extend ..
        · exact mdifferentiableAt_extend ..
        · exact mdifferentiableAt_extend ..
      smul_left c v w := by
        rw [← σ_smul (f := fun _ ↦ c)]
        · apply tensoriality_criterion₂ I F _ F' _ _ _ _ _ _ _ rfl σ_smul σ_add τ_smul τ_add
          · exact mdifferentiableAt_extend ..
          · apply MDifferentiableAt.smul_section
            · exact mdifferentiableAt_const
            · exact mdifferentiableAt_extend ..
          · exact mdifferentiableAt_extend ..
          · exact mdifferentiableAt_extend ..
          · simp
        · exact mdifferentiable_const ..
        · exact mdifferentiableAt_extend ..
        · exact mdifferentiableAt_extend ..
      add_right v w₁ w₂ := by
        rw [← τ_add]
        · apply tensoriality_criterion₂ I F _ F' _ _ _ _ _ _ rfl _ σ_smul σ_add τ_smul τ_add
          · exact mdifferentiableAt_extend ..
          · exact mdifferentiableAt_extend ..
          · exact mdifferentiableAt_extend ..
          · apply mdifferentiableAt_add_section
            · exact mdifferentiableAt_extend ..
            · exact mdifferentiableAt_extend ..
          · simp
        · exact mdifferentiableAt_extend ..
        · exact mdifferentiableAt_extend ..
        · exact mdifferentiableAt_extend ..
      smul_right c v w := by
        rw [← τ_smul (f := fun _ ↦ c)]
        · apply tensoriality_criterion₂ I F _ F' _ _ _ _ _ _ rfl _ σ_smul σ_add τ_smul τ_add
          · exact mdifferentiableAt_extend ..
          · exact mdifferentiableAt_extend ..
          · exact mdifferentiableAt_extend ..
          · apply MDifferentiableAt.smul_section
            · exact mdifferentiableAt_const
            · exact mdifferentiableAt_extend ..
          · simp
        · exact mdifferentiable_const ..
        · exact mdifferentiableAt_extend ..
        · exact mdifferentiableAt_extend .. }
    H.toContinuousLinearMap

variable {I} in
theorem mk2TensorAt_apply
    -- `φ` explicit to make it easier to generate the side conditions at point of use
    {φ : (Π x : M, V x) → (Π x : M, V' x) → (Π x, W x)} {x}
    (σ_smul : ∀ f : M → 𝕜, ∀ {σ τ}, MDiffAt f x → MDiffAt (T% σ) x → MDiffAt (T% τ) x →
      φ (f • σ) τ x = f x • φ σ τ x)
    (σ_add : ∀ σ σ' τ, MDiffAt (T% σ) x → MDiffAt (T% σ') x → MDiffAt (T% τ) x →
      φ (σ + σ') τ x = φ σ τ x + φ σ' τ x)
    (τ_smul : ∀ f : M → 𝕜, ∀ {σ τ}, MDiffAt f x → MDiffAt (T% σ) x → MDiffAt (T% τ) x →
        φ σ (f • τ) x = f x • φ σ τ x)
    (τ_add : ∀ σ τ τ', MDiffAt (T% σ) x → MDiffAt (T% τ) x → MDiffAt (T% τ') x →
        φ σ (τ + τ') x = φ σ τ x + φ σ τ' x)
    {σ : Π x : M, V x} (hσ : MDiffAt (T% σ) x) {τ : Π x : M, V' x} (hτ : MDiffAt (T% τ) x) :
    mk2TensorAt I F F' φ σ_smul σ_add τ_smul τ_add (σ x) (τ x) = φ σ τ x := by
  apply tensoriality_criterion₂ I F _ F' _ _ _ hσ _ hτ _ _ σ_smul σ_add τ_smul τ_add
  · exact mdifferentiableAt_extend ..
  · exact mdifferentiableAt_extend ..
  · simp
  · simp

variable {I} in
theorem mk2TensorAt_apply_eq_extend
    -- `φ` explicit to make it easier to generate the side conditions at point of use
    {φ : (Π x : M, V x) → (Π x : M, V' x) → (Π x, W x)} {x}
    (σ_smul : ∀ f : M → 𝕜, ∀ {σ τ}, MDiffAt f x → MDiffAt (T% σ) x → MDiffAt (T% τ) x →
      φ (f • σ) τ x = f x • φ σ τ x)
    (σ_add : ∀ σ σ' τ, MDiffAt (T% σ) x → MDiffAt (T% σ') x → MDiffAt (T% τ) x →
      φ (σ + σ') τ x = φ σ τ x + φ σ' τ x)
    (τ_smul : ∀ f : M → 𝕜, ∀ {σ τ}, MDiffAt f x → MDiffAt (T% σ) x → MDiffAt (T% τ) x →
        φ σ (f • τ) x = f x • φ σ τ x)
    (τ_add : ∀ σ τ τ', MDiffAt (T% σ) x → MDiffAt (T% τ) x → MDiffAt (T% τ') x →
        φ σ (τ + τ') x = φ σ τ x + φ σ τ' x)
    (σ : V x) (τ : V' x) :
    mk2TensorAt I F F' φ σ_smul σ_add τ_smul τ_add σ τ
    = φ (_root_.extend F σ) (_root_.extend F' τ) x :=
  rfl

theorem mk2TensorAt_add
    (φ : (Π x : M, V x) → (Π x : M, V' x) → (Π x, W x)) {x}
    (φ_σ_smul : ∀ (f : M → 𝕜), ∀ {σ τ}, MDiffAt f x → MDiffAt (T% σ) x → MDiffAt (T% τ) x →
      φ (f • σ) τ x = f x • φ σ τ x)
    (φ_σ_add : ∀ (σ σ' τ), MDiffAt (T% σ) x → MDiffAt (T% σ') x → MDiffAt (T% τ) x →
      φ (σ + σ') τ x = φ σ τ x + φ σ' τ x)
    (φ_τ_smul : ∀ (f : M → 𝕜), ∀ {σ τ}, MDiffAt f x → MDiffAt (T% σ) x → MDiffAt (T% τ) x →
        φ σ (f • τ) x = f x • φ σ τ x)
    (φ_τ_add : ∀ (σ τ τ'), MDiffAt (T% σ) x → MDiffAt (T% τ) x → MDiffAt (T% τ') x →
        φ σ (τ + τ') x = φ σ τ x + φ σ τ' x)
    (ψ : (Π x : M, V x) → (Π x : M, V' x) → (Π x, W x))
    (ψ_σ_smul : ∀ (f : M → 𝕜), ∀ {σ τ}, MDiffAt f x → MDiffAt (T% σ) x → MDiffAt (T% τ) x →
      ψ (f • σ) τ x = f x • ψ σ τ x)
    (ψ_σ_add : ∀ (σ σ' τ), MDiffAt (T% σ) x → MDiffAt (T% σ') x → MDiffAt (T% τ) x →
      ψ (σ + σ') τ x = ψ σ τ x + ψ σ' τ x)
    (ψ_τ_smul : ∀ (f : M → 𝕜), ∀ {σ τ}, MDiffAt f x → MDiffAt (T% σ) x → MDiffAt (T% τ) x →
        ψ σ (f • τ) x = f x • ψ σ τ x)
    (ψ_τ_add : ∀ (σ τ τ'), MDiffAt (T% σ) x → MDiffAt (T% τ) x → MDiffAt (T% τ') x →
        ψ σ (τ + τ') x = ψ σ τ x + ψ σ τ' x) :
    mk2TensorAt I F F' (φ + ψ)
      (fun {_ _ τ} hf hσ hτ ↦
      (congr($(φ_σ_smul _ hf hσ hτ) + $(ψ_σ_smul _ hf hσ hτ))).trans
        (smul_add _ _ _).symm)
      (fun σ₁ σ₂ τ hσ₁ hσ₂ hτ ↦
        (congr($(φ_σ_add _ _ _ hσ₁ hσ₂ hτ) + $(ψ_σ_add _ _ _ hσ₁ hσ₂ hτ))).trans <| by
        dsimp
        abel)
      (fun {_ σ _} hf hσ hτ ↦
      (congr($(φ_τ_smul _ hf hσ hτ) + $(ψ_τ_smul _ hf hσ hτ))).trans
        (smul_add _ _ _).symm)
      (fun σ {τ₁ τ₂} hσ hτ₁ hτ₂ ↦
        (congr($(φ_τ_add _ _ _ hσ hτ₁ hτ₂) + $(ψ_τ_add _ _ _ hσ hτ₁ hτ₂))).trans <| by
        dsimp
        abel)
    = mk2TensorAt I F F' φ φ_σ_smul φ_σ_add φ_τ_smul φ_τ_add
      + mk2TensorAt I F F' ψ ψ_σ_smul ψ_σ_add ψ_τ_smul ψ_τ_add := by
  ext
  simp [mk2TensorAt, IsBilinearMap.toContinuousLinearMap, IsBilinearMap.toLinearMap]

end tensoriality
