/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang, Heather Macbeth
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.Extend
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
public import Mathlib.Geometry.Manifold.VectorBundle.IsBilinearPrelim

/-!
# The tensoriality criterion

-/
open Bundle Filter Function Topology Module

open scoped Bundle Manifold ContDiff

@[expose] public section -- TODO: think if we want to expose all definitions!

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable
  (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [FiberBundle F V]

variable
  (F' : Type*) [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {V' : M → Type*} [TopologicalSpace (TotalSpace F' V')]
  [∀ x, AddCommGroup (V' x)] [∀ x, Module 𝕜 (V' x)] [∀ x : M, TopologicalSpace (V' x)]
  [FiberBundle F' V']

variable {A : Type*} [AddCommGroup A] [Module 𝕜 A]

structure TensorialAt (Φ : (Π x : M, V x) → A) (x : M) : Prop where
  smul : ∀ f : M → 𝕜, ∀ σ : Π x : M, V x, MDiffAt f x → MDiffAt (T% σ) x → Φ (f • σ) = f x • Φ σ
  add : ∀ σ σ', MDiffAt (T% σ) x → MDiffAt (T% σ') x → Φ (σ + σ') = Φ σ + Φ σ'

variable {Φ : (Π x : M, V x) → A} {x : M}
variable {I F F'}

namespace TensorialAt

theorem «local» (hΦ : TensorialAt I F Φ x) {σ σ' : Π x : M, V x}
    (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x) (hσσ' : ∀ᶠ x' in 𝓝 x, σ x' = σ' x') :
    Φ σ = Φ σ' := by
  classical
  rw [eventually_nhds_iff] at hσσ'
  obtain ⟨t, htσσ', ht, hxt⟩ := hσσ'
  let ψ (x' : M) : 𝕜 := if x' ∈ t then 1 else 0
  have hψx : ψ x = 1 := by simp [ψ, hxt]
  have (x' : M) : (ψ • σ) x' = (ψ • σ') x' := by
    dsimp [ψ]
    split_ifs with hx't
    · simpa using htσσ' _ hx't
    · simp
  have hψ' : MDiffAt ψ x := by
    have : MDiffAt (fun (_x : M) ↦ (1 : 𝕜)) x := mdifferentiableAt_const
    refine this.congr_of_eventuallyEq ?_
    apply eventually_nhds_iff.mpr
    exact ⟨t, by simp [ψ], ht, hxt⟩
  calc Φ σ
    _ = Φ (ψ • σ) := by simp [hΦ.smul _ _ hψ' hσ, hψx]
    _ = Φ (ψ • σ') := by rw [funext this]
    _ = Φ σ' := by simp [hΦ.smul _ _ hψ' hσ', hψx]

variable [VectorBundle 𝕜 F V] [VectorBundle 𝕜 F' V']

theorem sum (hΦ : TensorialAt I F Φ x) {ι : Type*} {s : Finset ι} (σ : ι → Π x : M, V x)
    (hσ : ∀ i, MDiffAt (T% (σ i)) x) :
    Φ (fun x' ↦ ∑ i ∈ s, σ i x') = ∑ i ∈ s, Φ (σ i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      have h₁ : MDiffAt (fun x' : M ↦ (0 : 𝕜)) x := mdifferentiableAt_const
      rw [show (fun x' : M ↦ (0 : V x')) = (0 : M → 𝕜) • fun x' ↦ 0 by simp;rfl]
      rw [hΦ.smul]
      · simp
      · exact h₁
      -- TODO: add mdifferentiable_zeroSection and/or use it!
      apply (contMDiff_zeroSection _ _).mdifferentiableAt one_ne_zero
  | insert a s ha h =>
      change Φ (fun x' : M ↦ ∑ i ∈ (insert a s : Finset ι), σ i x') = _
      simp only [Finset.sum_insert ha, ← h]
      exact hΦ.add _ _ (hσ a) (.sum_section hσ)

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 F']
  [ContMDiffVectorBundle 1 F V I] [ContMDiffVectorBundle 1 F' V' I]

lemma pointwise (hΦ : TensorialAt I F Φ x) {σ σ' : Π x : M, V x}
    (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x) (hσσ' : σ x = σ' x) :
    Φ σ = Φ σ' := by
  -- Select a local frame `s` for the bundle `V` near `x`,
  -- and let `c` be the family of linear maps evaluating the coefficients of a section relative to
  -- this frame
  let t := trivializationAt F V x
  have x_mem : x ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt F V x
  let b := Basis.ofVectorSpace 𝕜 F
  let s := t.localFrame b
  let c := t.localFrame_coeff I b
  have hs (i) : MDiffAt (T% (s i)) x :=
    (contMDiffAt_localFrame_of_mem 1 _ b i x_mem).mdifferentiableAt (by simp)
  have hc {σ : (x : M) → V x} (hσ : MDiffAt (T% σ) x) (i) :
      MDiffAt (LinearMap.piApply (c i) σ) x :=
    mdifferentiableAt_localFrame_coeff b x_mem hσ i
  -- By the locality of the operation `(Φ · x)`, its value a
  have hΦ_eq {σ : (x : M) → V x} (hσ : MDiffAt (T% σ) x) :
      Φ σ = Φ (fun x' ↦ ∑ i, LinearMap.piApply (c i) σ x' • s i x') :=
    hΦ.local hσ
      (.sum_section fun i ↦ (hc hσ i).smul_section (hs i))
      (t.eventually_eq_localFrame_sum_coeff_smul b x_mem)
  rw [hΦ_eq hσ, hΦ_eq hσ', hΦ.sum, hΦ.sum]
  · congr! 1 with i
    calc Φ ((LinearMap.piApply (c i) σ) • (s i))
        = c i x (σ x) • Φ (s i) := hΦ.smul _ _ (hc hσ i) (hs i)
      _ = c i x (σ' x) • Φ (s i) := by rw [hσσ']
      _ = Φ ((LinearMap.piApply (c i) σ') • (s i)) :=
          hΦ.smul _ _ (hc hσ' i) (hs i) |>.symm
  · exact fun i ↦ (hc hσ' i).smul_section (hs i)
  · exact fun i ↦ (hc hσ i).smul_section (hs i)

lemma pointwise₂
    {Φ : (Π x : M, V x) → (Π x : M, V' x) → A} {x}
    (hΦ₁ : ∀ τ, MDiffAt (T% τ) x → TensorialAt I F (Φ · τ) x)
    (hΦ₂ : ∀ σ, MDiffAt (T% σ) x → TensorialAt I F' (Φ σ ·) x)
    {σ σ' : Π x : M, V x} {τ τ' : Π x : M, V' x}
    (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x)
    (hτ : MDiffAt (T% τ) x) (hτ' : MDiffAt (T% τ') x)
    (hσσ' : σ x = σ' x) (hττ' : τ x = τ' x) :
    Φ σ τ = Φ σ' τ' := by
  trans Φ σ' τ
  · exact (hΦ₁ _ hτ).pointwise hσ hσ' hσσ'
  · exact (hΦ₂ _ hσ').pointwise hτ hτ' hττ'

variable [IsManifold I 1 M]
  -- TODO can probably remove the next four hypotheses, by transport
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
  [∀ x, IsTopologicalAddGroup (V' x)] [∀ x, ContinuousSMul 𝕜 (V' x)]
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul 𝕜 A]

noncomputable def mkHom
    -- `Φ` explicit to make it easier to generate the side conditions at point of use
    (Φ : (Π x : M, V x) → A) (x) (hΦ : TensorialAt I F (Φ) x) :
    V x →L[𝕜] A :=
  let Ψ : V x ≃L[𝕜] F := (trivializationAt F V x).continuousLinearEquivAt 𝕜 x
    (FiberBundle.mem_baseSet_trivializationAt' x)
  have : T2Space (V x) := Ψ.symm.toHomeomorph.t2Space
  have : FiniteDimensional 𝕜 (V x) := Ψ.symm.toLinearEquiv.finiteDimensional
  LinearMap.toContinuousLinearMap {
    toFun v := Φ (_root_.extend F v)
    map_add' v₁ v₂ := by
      rw [← hΦ.add]
      · apply hΦ.pointwise
        · exact mdifferentiableAt_extend ..
        · apply mdifferentiableAt_add_section
          · exact mdifferentiableAt_extend ..
          · exact mdifferentiableAt_extend ..
        · simp
      · exact mdifferentiableAt_extend ..
      · exact mdifferentiableAt_extend ..
    map_smul' c v := by
      dsimp
      rw [← hΦ.smul (fun _ ↦ c)]
      · apply hΦ.pointwise
        · exact mdifferentiableAt_extend ..
        · apply MDifferentiableAt.smul_section
          · exact mdifferentiableAt_const
          · exact mdifferentiableAt_extend ..
        · simp
      · exact mdifferentiable_const ..
      · exact mdifferentiableAt_extend .. }

theorem mkHom_apply {Φ : (Π x : M, V x) → A} {x} (hΦ : TensorialAt I F (Φ ·) x)
    {σ : Π x : M, V x} (hσ : MDiffAt (T% σ) x) :
    mkHom Φ x hΦ (σ x) = Φ σ := by
  apply hΦ.pointwise _ hσ
  · simp
  · exact mdifferentiableAt_extend ..

theorem mkHom_apply_eq_extend {Φ : (Π x : M, V x) → A} {x} (hΦ : TensorialAt I F Φ x) (σ : V x) :
    mkHom Φ x hΦ σ = Φ (_root_.extend F σ) :=
  rfl

noncomputable def mkHom₂
    -- `φ` explicit to make it easier to generate the side conditions at point of use
    (φ : (Π x : M, V x) → (Π x : M, V' x) → A) {x}
    (hφ₁ : ∀ τ, MDiffAt (T% τ) x → TensorialAt I F (φ · τ) x)
    (hφ₂ : ∀ σ, MDiffAt (T% σ) x → TensorialAt I F' (φ σ) x) :
    V x →L[𝕜] V' x →L[𝕜] A :=
  let Ψ : V x ≃L[𝕜] F := (trivializationAt F V x).continuousLinearEquivAt 𝕜 x
    (FiberBundle.mem_baseSet_trivializationAt' x)
  have : T2Space (V x) := Ψ.symm.toHomeomorph.t2Space
  have : FiniteDimensional 𝕜 (V x) := Ψ.symm.toLinearEquiv.finiteDimensional
  let Ψ' : V' x ≃L[𝕜] F' := (trivializationAt F' V' x).continuousLinearEquivAt 𝕜 x
    (FiberBundle.mem_baseSet_trivializationAt' x)
  have : T2Space (V' x) := Ψ'.symm.toHomeomorph.t2Space
  have : FiniteDimensional 𝕜 (V' x) := Ψ'.symm.toLinearEquiv.finiteDimensional
  have H : IsBilinearMap 𝕜
    (fun (v : V x) (w : V' x) ↦ φ (_root_.extend F v) (_root_.extend F' w)) :=
  { add_left v₁ v₂ w := by
      rw [← (hφ₁ _ _).add]
      · apply TensorialAt.pointwise₂ hφ₁ hφ₂ _ _ _ _ _ rfl
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
      rw [← (hφ₁ _ _).smul (f := fun _ ↦ c)]
      · apply TensorialAt.pointwise₂ hφ₁ hφ₂ _ _ _ _ _ rfl
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
      rw [← (hφ₂ _ _).add]
      · apply TensorialAt.pointwise₂ hφ₁ hφ₂
        · exact mdifferentiableAt_extend ..
        · exact mdifferentiableAt_extend ..
        · exact mdifferentiableAt_extend ..
        · apply mdifferentiableAt_add_section
          · exact mdifferentiableAt_extend ..
          · exact mdifferentiableAt_extend ..
        · rfl
        · simp
      · exact mdifferentiableAt_extend ..
      · exact mdifferentiableAt_extend ..
      · exact mdifferentiableAt_extend ..
    smul_right c v w := by
      rw [← (hφ₂ _ _).smul (f := fun _ ↦ c)]
      · apply TensorialAt.pointwise₂ hφ₁ hφ₂
        · exact mdifferentiableAt_extend ..
        · exact mdifferentiableAt_extend ..
        · exact mdifferentiableAt_extend ..
        · apply MDifferentiableAt.smul_section
          · exact mdifferentiableAt_const
          · exact mdifferentiableAt_extend ..
        · rfl
        · simp
      · exact mdifferentiable_const ..
      · exact mdifferentiableAt_extend ..
      · exact mdifferentiableAt_extend .. }
  H.toContinuousLinearMap

theorem mkHom₂_apply
    {φ : (Π x : M, V x) → (Π x : M, V' x) → A} {x}
    (hφ₁ : ∀ τ, MDiffAt (T% τ) x → TensorialAt I F (φ · τ) x)
    (hφ₂ : ∀ σ, MDiffAt (T% σ) x → TensorialAt I F' (φ σ) x)
    {σ : Π x : M, V x} (hσ : MDiffAt (T% σ) x) {τ : Π x : M, V' x} (hτ : MDiffAt (T% τ) x) :
    mkHom₂ φ hφ₁ hφ₂ (σ x) (τ x) = φ σ τ := by
  apply TensorialAt.pointwise₂ hφ₁ hφ₂ _ hσ _ hτ
  · simp
  · simp
  · exact mdifferentiableAt_extend ..
  · exact mdifferentiableAt_extend ..

theorem mkHom₂_apply_eq_extend
    {φ : (Π x : M, V x) → (Π x : M, V' x) → A} {x}
    (hφ₁ : ∀ τ, MDiffAt (T% τ) x → TensorialAt I F (φ · τ) x)
    (hφ₂ : ∀ σ, MDiffAt (T% σ) x → TensorialAt I F' (φ σ) x)
    (σ : V x) (τ : V' x) :
    mkHom₂ φ hφ₁ hφ₂ σ τ = φ (_root_.extend F σ) (_root_.extend F' τ) :=
  rfl

variable
  -- TODO can probably remove the next two hypotheses, by transport
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]

variable
  -- TODO can probably remove the next two hypotheses, by transport
  [∀ x, IsTopologicalAddGroup (V' x)] [∀ x, ContinuousSMul 𝕜 (V' x)]

variable
  (G : Type*) [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {W : M → Type*} [∀ x, AddCommGroup (W x)] [∀ x, Module 𝕜 (W x)]
  -- TODO can probably remove the next three hypotheses, by transport
  [∀ x : M, TopologicalSpace (W x)] [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul 𝕜 (W x)]
  [TopologicalSpace (TotalSpace G W)] [FiberBundle G W] [VectorBundle 𝕜 G W]

theorem contMDiff_mkHom
    (φ : (Π x : M, V x) → (Π x, W x))
    (hφ : ∀ x, TensorialAt I F (φ · x) x)
    -- hopefully this is the correct smoothness criterion!
    {k} (φ_contMDiff : ∀ (σ : Π x : M, V x), CMDiff k (T% σ) → CMDiff k (T% (φ σ))) :
    -- elaborators not working here
    let T (x : M) : TotalSpace (F →L[𝕜] G) (fun x ↦ V x →L[𝕜] W x) :=
      ⟨x, mkHom (φ · x) x (hφ x)⟩
    ContMDiff I (I.prod 𝓘(𝕜, F →L[𝕜] G)) k T := by
  sorry

end TensorialAt
