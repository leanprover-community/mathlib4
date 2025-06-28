/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-!
# The tensoriality criterion

-/
open Bundle Filter Function Topology

open scoped Bundle Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  -- `F` model fiber
  (n : WithTop ℕ∞)
  (V : M → Type*) [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x : M, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  -- `V` vector bundle

variable (F' : Type*) [NormedAddCommGroup F'] [NormedSpace ℝ F']
  (m : WithTop ℕ∞)
  (V' : M → Type*) [TopologicalSpace (TotalSpace F' V')]
  [∀ x, AddCommGroup (V' x)] [∀ x, Module ℝ (V' x)]
  [∀ x : M, TopologicalSpace (V' x)] [∀ x, IsTopologicalAddGroup (V' x)]
  [∀ x, ContinuousSMul ℝ (V' x)]

lemma tensoriality_criterion [FiberBundle F V] [VectorBundle ℝ F V] [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] [FiberBundle F' V'] [VectorBundle ℝ F' V'] [T2Space M]
    [IsManifold I ∞ M]
    {φ : (Π x : M, V x) → (Π x, V' x)} {x}
    {σ σ' : Π x : M, V x}
    (hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, F)) (fun x ↦ TotalSpace.mk' F x (σ x)) x)
    (hσ' : MDifferentiableAt I (I.prod 𝓘(ℝ, F)) (fun x ↦ TotalSpace.mk' F x (σ' x)) x)
    (hσσ' : σ x = σ' x)
    (φ_smul : ∀ f : M → ℝ, ∀ σ, MDifferentiableAt I 𝓘(ℝ) f x →
          MDifferentiableAt I (I.prod 𝓘(ℝ, F)) (fun x ↦ TotalSpace.mk' F x (σ x)) x →
          φ (f • σ) x = f x • φ σ x)
    (φ_add : ∀ σ σ',
          MDifferentiableAt I (I.prod 𝓘(ℝ, F)) (fun x ↦ TotalSpace.mk' F x (σ x)) x →
          MDifferentiableAt I (I.prod 𝓘(ℝ, F)) (fun x ↦ TotalSpace.mk' F x (σ' x)) x →
          φ (σ + σ') x = φ σ x + φ σ' x) : φ σ x = φ σ' x := by
  have locality {σ σ'}
      (hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, F)) (fun x ↦ TotalSpace.mk' F x (σ x)) x)
      (hσ' : MDifferentiableAt I (I.prod 𝓘(ℝ, F)) (fun x ↦ TotalSpace.mk' F x (σ' x)) x)
      (hσσ' : ∀ᶠ x' in 𝓝 x, σ x' = σ' x') : φ σ x = φ σ' x := by
    obtain ⟨ψ, _, hψ⟩ := (SmoothBumpFunction.nhds_basis_support (I := I) hσσ').mem_iff.1 hσσ'
    have (x : M) : ((ψ : M → ℝ) • σ) x = ((ψ : M → ℝ) • σ') x := by
      by_cases h : σ x = σ' x
      · rw [Pi.smul_apply', Pi.smul_apply', h]
      · simp [notMem_support.mp fun a ↦ h (hψ a)]
    have hψ' : MDifferentiableAt I 𝓘(ℝ) ψ x :=
       ψ.contMDiffAt.mdifferentiableAt ENat.LEInfty.out
    calc φ σ x
      _ = φ ((ψ : M → ℝ) • σ) x := by simp [φ_smul _ _ hψ' hσ]
      _ = φ ((ψ : M → ℝ) • σ') x := by rw [funext this]
      _ = φ σ' x := by simp [φ_smul _ _ hψ' hσ']
  let ι : Type _ := Basis.ofVectorSpaceIndex ℝ F
  classical
  have sum_phi {s : Finset ι} (σ : ι → Π x : M, V x)
      (hσ : ∀ i, MDifferentiableAt I (I.prod 𝓘(ℝ, F)) (fun x ↦ TotalSpace.mk' F x (σ i x)) x):
      φ (fun x' ↦ ∑ i ∈ s, σ i x') x = ∑ i ∈ s, φ (σ i) x := by
    induction s using Finset.induction_on with
    | empty =>
       simp only [Finset.sum_empty]
       have h₁ : MDifferentiableAt I 𝓘(ℝ) (fun x' : M ↦ (0 : ℝ)) x := by
         exact contMDiffAt_const.mdifferentiableAt le_rfl
       rw [show (fun x' : M ↦ (0 : V x')) = (0 : M → ℝ) • fun x' ↦ 0 by simp;rfl]
       rw [φ_smul]
       simp
       exact h₁
       apply (contMDiff_zeroSection _ _).mdifferentiableAt ENat.LEInfty.out
    | insert a s ha h =>
        change φ (fun x' : M ↦ ∑ i ∈ (insert a s : Finset ι), σ i x') x = _
        simp [Finset.sum_insert ha, Finset.sum_insert ha, ← h]
        erw [φ_add]
        apply hσ a
        sorry
  have x_mem := (FiberBundle.mem_baseSet_trivializationAt F V x)
  let b := Basis.ofVectorSpace ℝ F
  let t := trivializationAt F V x
  let s := b.localFrame (trivializationAt F V x)
  let c := Basis.localFrame_repr t b
  rw [locality _ _ (b.localFrame_repr_spec x_mem σ), locality _ _ (b.localFrame_repr_spec x_mem σ'),
      sum_phi, sum_phi]
  · change ∑ i, φ ((c i σ) • (s i)) x = ∑ i, φ ((c i σ') • (s i)) x
    congr
    ext i
    rw [φ_smul, φ_smul]
    · congr
      apply b.localFrame_repr_congr
      assumption
    all_goals sorry
  all_goals sorry

include I in
omit [IsManifold I 1 M] [∀ (x : M), IsTopologicalAddGroup (V x)]
  [∀ (x : M), ContinuousSMul ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [∀ (x : M), IsTopologicalAddGroup (V' x)] [∀ (x : M), ContinuousSMul ℝ (V' x)] in
lemma tensoriality_criterion' [FiberBundle F V] [VectorBundle ℝ F V] [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] [FiberBundle F' V'] [VectorBundle ℝ F' V'] [T2Space M]
    {φ : (Π x : M, V x) → (Π x, V' x)} {x}
    {σ σ' : Π x : M, V x}
    (hσσ' : σ x = σ' x)
    (φ_smul : ∀ f : M → ℝ, ∀ σ, φ (f • σ) x = f x • φ σ x)
    (φ_add : ∀ σ σ', φ (σ + σ') x = φ σ x + φ σ' x) : φ σ x = φ σ' x := by
  have locality {σ σ'} (hσσ' : ∀ᶠ x' in 𝓝 x, σ x' = σ' x') :
      φ σ x = φ σ' x := by
    obtain ⟨ψ, _, hψ⟩ := (SmoothBumpFunction.nhds_basis_support (I := I) hσσ').mem_iff.1 hσσ'
    have (x : M) : ((ψ : M → ℝ) • σ) x = ((ψ : M → ℝ) • σ') x := by
      by_cases h : σ x = σ' x
      · rw [Pi.smul_apply', Pi.smul_apply', h]
      · simp [notMem_support.mp fun a ↦ h (hψ a)]
    calc φ σ x
      _ = φ ((ψ : M → ℝ) • σ) x := by simp [φ_smul]
      _ = φ ((ψ : M → ℝ) • σ') x := by rw [funext this]
      _ = φ σ' x := by simp [φ_smul]
  let ι : Type _ := Basis.ofVectorSpaceIndex ℝ F
  classical
  have sum_phi {s : Finset ι} (σ : ι → Π x : M, V x) :
      φ (fun x' ↦ ∑ i ∈ s, σ i x') x = ∑ i ∈ s, φ (σ i) x := by
    induction s using Finset.induction_on with
    | empty =>
       simp only [Finset.sum_empty]
       rw [show (fun x' : M ↦ (0 : V x')) = (0 : M → ℝ) • fun x' ↦ 0 by simp;rfl, φ_smul]
       simp
    | insert a s ha h =>
        change φ (fun x' : M ↦ ∑ i ∈ (insert a s : Finset ι), σ i x') x = _
        simp [Finset.sum_insert ha, Finset.sum_insert ha, ← h]
        erw [φ_add]
  have x_mem := (FiberBundle.mem_baseSet_trivializationAt F V x)
  let b := Basis.ofVectorSpace ℝ F
  let t := trivializationAt F V x
  let s := b.localFrame (trivializationAt F V x)
  let c := Basis.localFrame_repr t b
  rw [locality (b.localFrame_repr_spec x_mem σ), locality (b.localFrame_repr_spec x_mem σ'),
      sum_phi, sum_phi]
  change ∑ i, φ ((c i σ) • (s i)) x = ∑ i, φ ((c i σ') • (s i)) x
  congr
  ext i
  rw [φ_smul, φ_smul]
  congr
  apply b.localFrame_repr_congr
  assumption

/- include I in
lemma tensoriality_criterion'' [FiberBundle F V] [VectorBundle ℝ F V] [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] [FiberBundle F' V'] [VectorBundle ℝ F' V'] [T2Space M]
    {φ : (Π x : M, V x) → (Π x, V' x)} {x}
    {σ σ' : Π x : M, V x}
    {Pσ : (Π x : M, V x) → Prop}
    {Pσ_loc : ∀ σ σ', (∀ᶠ x' in 𝓝 x, σ x' = σ' x') → Pσ σ → Pσ σ'}
    (hσ : Pσ σ)
    (hσ' : Pσ σ')
    {Pf : (M → ℝ) → Prop}
    {Pf_loc : ∀ f f', (∀ᶠ x' in 𝓝 x, f x' = f' x') → Pf f → Pf f'}
    (Pf_smooth : ∀ f, MDifferentiableAt I 𝓘(ℝ) f x → Pf f)
    (hσσ' : σ x = σ' x)
    (φ_smul : ∀ f : M → ℝ, ∀ σ, Pf f → Pσ σ → φ (f • σ) x = f x • φ σ x)
    (φ_add : ∀ σ σ', Pσ σ → Pσ σ → φ (σ + σ') x = φ σ x + φ σ' x) : φ σ x = φ σ' x := by
  have locality {σ σ'} (hσσ' : ∀ᶠ x' in 𝓝 x, σ x' = σ' x') :
      φ σ x = φ σ' x := by
    obtain ⟨ψ, _, hψ⟩ := (SmoothBumpFunction.nhds_basis_support (I := I) hσσ').mem_iff.1 hσσ'
    have (x : M) : ((ψ : M → ℝ) • σ) x = ((ψ : M → ℝ) • σ') x := by
      by_cases h : σ x = σ' x
      · rw [Pi.smul_apply', Pi.smul_apply', h]
      · simp [notMem_support.mp fun a ↦ h (hψ a)]
    calc φ σ x
      _ = φ ((ψ : M → ℝ) • σ) x := by simp [φ_smul]
      _ = φ ((ψ : M → ℝ) • σ') x := by rw [funext this]
      _ = φ σ' x := by simp [φ_smul]
  let ι : Type _ := Basis.ofVectorSpaceIndex ℝ F
  classical
  have sum_phi {s : Finset ι} (σ : ι → Π x : M, V x) :
      φ (fun x' ↦ ∑ i ∈ s, σ i x') x = ∑ i ∈ s, φ (σ i) x := by
    induction s using Finset.induction_on with
    | empty =>
       simp only [Finset.sum_empty]
       rw [show (fun x' : M ↦ (0 : V x')) = (0 : M → ℝ) • fun x' ↦ 0 by simp;rfl, φ_smul]
       simp
    | insert a s ha h =>
        change φ (fun x' : M ↦ ∑ i ∈ (insert a s : Finset ι), σ i x') x = _
        simp [Finset.sum_insert ha, Finset.sum_insert ha, ← h]
        erw [φ_add]
  have x_mem := (FiberBundle.mem_baseSet_trivializationAt F V x)
  let b := Basis.ofVectorSpace ℝ F
  let t := trivializationAt F V x
  let s := b.localFrame (trivializationAt F V x)
  let c := Basis.localFrame_repr t b
  rw [locality (b.localFrame_repr_spec x_mem σ), locality (b.localFrame_repr_spec x_mem σ'),
      sum_phi, sum_phi]
  change ∑ i, φ ((c i σ) • (s i)) x = ∑ i, φ ((c i σ') • (s i)) x
  congr
  ext i
  rw [φ_smul, φ_smul]
  congr
  apply b.localFrame_repr_congr
  assumption
 -/
