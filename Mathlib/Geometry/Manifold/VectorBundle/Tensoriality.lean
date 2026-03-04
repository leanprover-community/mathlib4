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

/-!
# The tensoriality criterion

-/
open Bundle Filter Function Topology Module

open scoped Bundle Manifold ContDiff

@[expose] public section -- TODO: think if we want to expose all definitions!

variable {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  -- `F` model fiber
  (n : WithTop ℕ∞)
  (V : M → Type*) [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  -- [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  -- `V` vector bundle

variable (F' : Type*) [NormedAddCommGroup F'] [NormedSpace ℝ F']
  (m : WithTop ℕ∞)
  (V' : M → Type*) [TopologicalSpace (TotalSpace F' V')]
  [∀ x, AddCommGroup (V' x)] [∀ x, Module ℝ (V' x)]
  [∀ x : M, TopologicalSpace (V' x)]
  -- [∀ x, IsTopologicalAddGroup (V' x)] [∀ x, ContinuousSMul ℝ (V' x)]

omit [IsManifold I 1 M] [FiberBundle F V] [VectorBundle ℝ F V] in
lemma tensoriality_criterion [FiberBundle F V] [VectorBundle ℝ F V]
    [ContMDiffVectorBundle 1 F V I] [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] [FiberBundle F' V'] [VectorBundle ℝ F' V'] [T2Space M]
    [IsManifold I ∞ M]
    {φ : (Π x : M, V x) → (Π x, V' x)} {x}
    {σ σ' : Π x : M, V x} (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x)
    (hσσ' : σ x = σ' x)
    (φ_smul : ∀ f : M → ℝ, ∀ σ, MDiffAt f x → MDiffAt (T% σ) x →
      φ (f • σ) x = f x • φ σ x)
    (φ_add : ∀ σ σ', MDiffAt (T% σ) x → MDiffAt (T% σ') x →
      φ (σ + σ') x = φ σ x + φ σ' x) : φ σ x = φ σ' x := by
  have locality {σ σ'} (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x)
      (hσσ' : ∀ᶠ x' in 𝓝 x, σ x' = σ' x') : φ σ x = φ σ' x := by
    obtain ⟨ψ, _, hψ⟩ := (SmoothBumpFunction.nhds_basis_support (I := I) hσσ').mem_iff.1 hσσ'
    have (x : M) : ((ψ : M → ℝ) • σ) x = ((ψ : M → ℝ) • σ') x := by
      by_cases h : σ x = σ' x
      · rw [Pi.smul_apply', Pi.smul_apply', h]
      · simp [notMem_support.mp fun a ↦ h (hψ a)]
    have hψ' : MDifferentiableAt I 𝓘(ℝ) ψ x :=
       ψ.contMDiffAt.mdifferentiableAt (by simp)
    calc φ σ x
      _ = φ ((ψ : M → ℝ) • σ) x := by simp [φ_smul _ _ hψ' hσ]
      _ = φ ((ψ : M → ℝ) • σ') x := by rw [funext this]
      _ = φ σ' x := by simp [φ_smul _ _ hψ' hσ']
  let ι : Type _ := Basis.ofVectorSpaceIndex ℝ F
  classical
  have sum_phi {s : Finset ι} (σ : ι → Π x : M, V x)
      (hσ : ∀ i, MDiffAt  (T% (σ i)) x):
      φ (fun x' ↦ ∑ i ∈ s, σ i x') x = ∑ i ∈ s, φ (σ i) x := by
    induction s using Finset.induction_on with
    | empty =>
       simp only [Finset.sum_empty]
       have h₁ : MDiffAt (fun x' : M ↦ (0 : ℝ)) x := mdifferentiableAt_const
       rw [show (fun x' : M ↦ (0 : V x')) = (0 : M → ℝ) • fun x' ↦ 0 by simp;rfl]
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
  let b := Basis.ofVectorSpace ℝ F
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
omit [IsManifold I 1 M] [FiberBundle F V] [VectorBundle ℝ F V] in
lemma tensoriality_criterion' [FiberBundle F V] [VectorBundle ℝ F V] [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] [FiberBundle F' V'] [VectorBundle ℝ F' V'] [T2Space M]
    [ContMDiffVectorBundle 1 F V I]
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
      simp only [Finset.sum_insert ha, ← h]
      erw [φ_add]
  have x_mem := (FiberBundle.mem_baseSet_trivializationAt F V x)
  let b := Basis.ofVectorSpace ℝ F
  let t := trivializationAt F V x
  let s := t.localFrame b
  let c := t.localFrame_coeff (I := I) b
  rw [locality (t.eventually_eq_localFrame_sum_coeff_smul (I := I) b x_mem)]
  nth_rw 2 [locality (t.eventually_eq_localFrame_sum_coeff_smul (I := I) b x_mem)]
  rw [sum_phi, sum_phi]
  -- FIXME: the `erw` below can be made an `rw` by uncommenting this `change`
  --change ∑ i, φ (((LinearMap.piApply (c i)) σ) • (s i)) x =
  --  ∑ i, φ (((LinearMap.piApply (c i)) σ') • (s i)) x
  congr with i
  -- `erw?` says this is because of smul with a constant vs. a function `M → ℝ`
  erw [φ_smul, φ_smul]
  congr

include I in
omit [IsManifold I 1 M] [FiberBundle F V] [VectorBundle ℝ F V] in
lemma tensoriality_criterion₂' [FiberBundle F V] [VectorBundle ℝ F V]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [T2Space M] [ContMDiffVectorBundle 1 F V I]
    [FiberBundle F' V'] [VectorBundle ℝ F' V']
    {φ : (Π x : M, V x) → (Π x : M, V x) → (Π x, V' x)} {x}
    {σ σ' τ τ' : Π x : M, V x}
    (hσσ' : σ x = σ' x)
    (hττ' : τ x = τ' x)
    (φ_smul : ∀ f : M → ℝ, ∀ σ τ, φ (f • σ) τ x = f x • φ σ τ x)
    (φ_add : ∀ σ σ' τ, φ (σ + σ') τ x = φ σ τ x + φ σ' τ x)
    (τ_smul : ∀ f : M → ℝ, ∀ σ τ, φ σ (f • τ) x = f x • φ σ τ x)
    (τ_add : ∀ σ τ τ', φ σ (τ + τ') x = φ σ τ x + φ σ τ' x) : φ σ τ x = φ σ' τ' x := by
  trans φ σ' τ x
  · let φ1 : (Π x : M, V x) → (Π x, V' x) := fun X ↦ φ X τ
    change φ1 σ x = φ1 σ' x
    exact tensoriality_criterion' I F V F' V' hσσ' (by simp [φ_smul, φ1]) (by simp [φ_add, φ1])
  · let φ1 : (Π x : M, V x) → (Π x, V' x) := fun X ↦ φ σ' X
    change φ1 τ x = φ1 τ' x
    exact tensoriality_criterion' I F V F' V' hττ' (by simp [τ_smul, φ1]) (by simp [τ_add, φ1])

include I in
omit [IsManifold I 1 M] in
lemma tensoriality_criterion₂ [ContMDiffVectorBundle 1 F V I] [IsManifold I ∞ M]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [T2Space M]
    [FiberBundle F' V'] [VectorBundle ℝ F' V']
    {φ : (Π x : M, V x) → (Π x : M, V x) → (Π x, V' x)} {x}
    {σ σ' τ τ' : Π x : M, V x}
    (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x)
    (hτ : MDiffAt (T% τ) x) (hτ' : MDiffAt (T% τ') x)
    (hσσ' : σ x = σ' x)
    (hττ' : τ x = τ' x)
    (φ_smul : ∀ {f : M → ℝ}, ∀ {σ τ}, MDiffAt f x → MDiffAt (T% σ) x →
      φ (f • σ) τ x = f x • φ σ τ x)
    (φ_add : ∀ {σ σ' τ}, MDiffAt (T% σ) x → MDiffAt (T% σ') x →
      φ (σ + σ') τ x = φ σ τ x + φ σ' τ x)
    (τ_smul : ∀ {f : M → ℝ}, ∀ {σ τ}, MDiffAt f x → MDiffAt (T% τ) x →
        φ σ (f • τ) x = f x • φ σ τ x)
    (τ_add : ∀ {σ τ τ'}, MDiffAt (T% τ) x → MDiffAt (T% τ') x →
        φ σ (τ + τ') x = φ σ τ x + φ σ τ' x) : φ σ τ x = φ σ' τ' x := by
  trans φ σ' τ x
  · let φ1 : (Π x : M, V x) → (Π x, V' x) := fun X ↦ φ X τ
    change φ1 σ x = φ1 σ' x
    apply tensoriality_criterion I F V F' V' hσ hσ' hσσ'
    exacts [fun f σ hf hσ ↦ φ_smul hf hσ, fun σ σ' hσ hσ' ↦ φ_add hσ hσ']
  · let φ1 : (Π x : M, V x) → (Π x, V' x) := fun X ↦ φ σ' X
    change φ1 τ x = φ1 τ' x
    apply tensoriality_criterion I F V F' V' hτ hτ' hττ'
    exacts [fun f τ hf hτ ↦ τ_smul hf hτ, fun τ τ' hτ hτ' ↦ τ_add hτ hτ']

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
  let c := Basis.localFrame_coeff t b
  rw [locality (b.localFrame_eventually_eq_sum_coeff_smul x_mem σ),
      locality (b.localFrame_eventually_eq_sum_coeff_smul x_mem σ'), sum_phi, sum_phi]
  change ∑ i, φ ((c i σ) • (s i)) x = ∑ i, φ ((c i σ') • (s i)) x
  congr
  ext i
  rw [φ_smul, φ_smul]
  congr
  apply b.localFrame_coeff_congr
  assumption
 -/


section tensoriality

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]

variable
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [(x : M) → AddCommGroup (V x)] [(x : M) → Module ℝ (V x)] [(x : M) → TopologicalSpace (V x)]
  -- TODO can probably remove the next two hypotheses, by transport
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]

variable
  (F' : Type*) [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {V' : M → Type*} [TopologicalSpace (TotalSpace F' V')] [(x : M) → AddCommGroup (V' x)]
  [(x : M) → Module ℝ (V' x)] [(x : M) → TopologicalSpace (V' x)]
  -- TODO can probably remove the next two hypotheses, by transport
  [∀ x, IsTopologicalAddGroup (V' x)] [∀ x, ContinuousSMul ℝ (V' x)]
  [FiberBundle F' V'] [VectorBundle ℝ F' V']

noncomputable def mkTensorAt
    -- `φ` explicit to make it easier to generate the side conditions at point of use
    (φ : (Π x : M, V x) → (Π x, V' x)) (x)
    (φ_smul : ∀ f : M → ℝ, ∀ σ, MDiffAt f x → MDiffAt (T% σ) x →
      φ (f • σ) x = f x • φ σ x)
    (φ_add : ∀ σ σ', MDiffAt (T% σ) x → MDiffAt (T% σ') x →
      φ (σ + σ') x = φ σ x + φ σ' x) :
    V x →L[ℝ] V' x :=
    let Ψ : V x ≃L[ℝ] F := (trivializationAt F V x).continuousLinearEquivAt ℝ x
      (FiberBundle.mem_baseSet_trivializationAt' x)
    have : T2Space (V x) := Ψ.symm.toHomeomorph.t2Space
    have : FiniteDimensional ℝ (V x) := Ψ.symm.toLinearEquiv.finiteDimensional
    LinearMap.toContinuousLinearMap {
      toFun v := φ (_root_.extend I F v) x
      map_add' v₁ v₂ := by
        rw [← φ_add]
        · apply tensoriality_criterion I F _ F' _ _ _ _ φ_smul φ_add
          · exact mdifferentiable_extend ..
          · apply mdifferentiableAt_add_section
            · exact mdifferentiable_extend ..
            · exact mdifferentiable_extend ..
          · simp
        · exact mdifferentiable_extend ..
        · exact mdifferentiable_extend ..
      map_smul' c v := by
        dsimp
        rw [← φ_smul (fun _ ↦ c)]
        · apply tensoriality_criterion I F _ F' _ _ _ _ φ_smul φ_add
          · exact mdifferentiable_extend ..
          · apply MDifferentiableAt.smul_section
            · exact mdifferentiableAt_const
            · exact mdifferentiable_extend ..
          · simp
        · exact mdifferentiable_const ..
        · exact mdifferentiable_extend .. }

variable {I} in
theorem mkTensorAt_apply
    -- `φ` explicit to make it easier to generate the side conditions at point of use
    {φ : (Π x : M, V x) → (Π x, V' x)} {x}
    (φ_smul : ∀ f : M → ℝ, ∀ σ, MDiffAt f x → MDiffAt (T% σ) x →
      φ (f • σ) x = f x • φ σ x)
    (φ_add : ∀ σ σ', MDiffAt (T% σ) x → MDiffAt (T% σ') x →
      φ (σ + σ') x = φ σ x + φ σ' x) {σ : Π x : M, V x} (hσ : MDiffAt (T% σ) x) :
    mkTensorAt I F F' φ x φ_smul φ_add (σ x) = φ σ x := by
  apply tensoriality_criterion I F _ F' _ _ hσ _ φ_smul φ_add
  · exact mdifferentiable_extend ..
  · simp

noncomputable def mkTensor
    -- `φ` explicit to make it easier to generate the side conditions at point of use
    (φ : (Π x : M, V x) → (Π x, V' x))
    -- TODO could weaken `φ_smul` and `φ_add` to require the property only globally, is it useful?
    (φ_smul : ∀ x, ∀ f : M → ℝ, ∀ σ, MDiffAt f x → MDiffAt (T% σ) x → φ (f • σ) x = f x • φ σ x)
    (φ_add : ∀ x, ∀ σ σ', MDiffAt (T% σ) x → MDiffAt (T% σ') x → φ (σ + σ') x = φ σ x + φ σ' x)
    (x : M) :
    V x →L[ℝ] V' x :=
  mkTensorAt I F F' φ x (φ_smul x) (φ_add x)

theorem contMDiff_mkTensor
    (φ : (Π x : M, V x) → (Π x, V' x))
    (φ_smul : ∀ x, ∀ f : M → ℝ, ∀ σ, MDiffAt f x → MDiffAt (T% σ) x → φ (f • σ) x = f x • φ σ x)
    (φ_add : ∀ x, ∀ σ σ', MDiffAt (T% σ) x → MDiffAt (T% σ') x → φ (σ + σ') x = φ σ x + φ σ' x)
    -- hopefully this is the correct smoothness criterion!
    {k} (φ_contMDiff : ∀ (σ : Π x : M, V x), CMDiff k (T% σ) → CMDiff k (T% (φ σ))) :
    -- elaborators not working here
    let T (x : M) : TotalSpace (F →L[ℝ] F') (fun x ↦ V x →L[ℝ] V' x) :=
      ⟨x, mkTensor I F F' φ φ_smul φ_add x⟩
    ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F')) k T := by
  sorry

-- TODO allow the two input types to differ
noncomputable def mk2TensorAt
    -- `φ` explicit to make it easier to generate the side conditions at point of use
    (φ : (Π x : M, V x) → (Π x : M, V x) → (Π x, V' x)) {x}
    (σ_smul : ∀ {f : M → ℝ}, ∀ {σ τ}, MDiffAt f x → MDiffAt (T% σ) x →
      φ (f • σ) τ x = f x • φ σ τ x)
    (σ_add : ∀ {σ σ' τ}, MDiffAt (T% σ) x → MDiffAt (T% σ') x →
      φ (σ + σ') τ x = φ σ τ x + φ σ' τ x)
    (τ_smul : ∀ {f : M → ℝ}, ∀ {σ τ}, MDiffAt f x → MDiffAt (T% τ) x →
        φ σ (f • τ) x = f x • φ σ τ x)
    (τ_add : ∀ {σ τ τ'}, MDiffAt (T% τ) x → MDiffAt (T% τ') x →
        φ σ (τ + τ') x = φ σ τ x + φ σ τ' x) :
    V x →L[ℝ] V x →L[ℝ] V' x :=
    let Ψ : V x ≃L[ℝ] F := (trivializationAt F V x).continuousLinearEquivAt ℝ x
      (FiberBundle.mem_baseSet_trivializationAt' x)
    have : T2Space (V x) := Ψ.symm.toHomeomorph.t2Space
    have : FiniteDimensional ℝ (V x) := Ψ.symm.toLinearEquiv.finiteDimensional
    have H : IsBilinearMap ℝ
      (fun (v w : V x) ↦ φ (_root_.extend I F v) (_root_.extend I F w) x) :=
    { add_left v₁ v₂ w := by
        rw [← σ_add]
        · apply tensoriality_criterion₂ I F _ F' _ _ _ _ _ _ rfl σ_smul σ_add τ_smul τ_add
          · exact mdifferentiable_extend ..
          · apply mdifferentiableAt_add_section
            · exact mdifferentiable_extend ..
            · exact mdifferentiable_extend ..
          · exact mdifferentiable_extend ..
          · exact mdifferentiable_extend ..
          · simp
        · exact mdifferentiable_extend ..
        · exact mdifferentiable_extend ..
      smul_left c v w := by
        rw [← σ_smul (f := fun _ ↦ c)]
        · apply tensoriality_criterion₂ I F _ F' _ _ _ _ _ _ rfl σ_smul σ_add τ_smul τ_add
          · exact mdifferentiable_extend ..
          · apply MDifferentiableAt.smul_section
            · exact mdifferentiableAt_const
            · exact mdifferentiable_extend ..
          · exact mdifferentiable_extend ..
          · exact mdifferentiable_extend ..
          · simp
        · exact mdifferentiable_const ..
        · exact mdifferentiable_extend ..
      add_right v w₁ w₂ := by
        rw [← τ_add]
        · apply tensoriality_criterion₂ I F _ F' _ _ _ _ _ rfl _ σ_smul σ_add τ_smul τ_add
          · exact mdifferentiable_extend ..
          · exact mdifferentiable_extend ..
          · exact mdifferentiable_extend ..
          · apply mdifferentiableAt_add_section
            · exact mdifferentiable_extend ..
            · exact mdifferentiable_extend ..
          · simp
        · exact mdifferentiable_extend ..
        · exact mdifferentiable_extend ..
      smul_right c v w := by
        rw [← τ_smul (f := fun _ ↦ c)]
        · apply tensoriality_criterion₂ I F _ F' _ _ _ _ _ rfl _ σ_smul σ_add τ_smul τ_add
          · exact mdifferentiable_extend ..
          · exact mdifferentiable_extend ..
          · exact mdifferentiable_extend ..
          · apply MDifferentiableAt.smul_section
            · exact mdifferentiableAt_const
            · exact mdifferentiable_extend ..
          · simp
        · exact mdifferentiable_const ..
        · exact mdifferentiable_extend .. }
    H.toContinuousLinearMap

variable {I} in
theorem mk2TensorAt_apply
    -- `φ` explicit to make it easier to generate the side conditions at point of use
    {φ : (Π x : M, V x) → (Π x : M, V x) → (Π x, V' x)} {x}
    (σ_smul : ∀ {f : M → ℝ}, ∀ {σ τ}, MDiffAt f x → MDiffAt (T% σ) x →
      φ (f • σ) τ x = f x • φ σ τ x)
    (σ_add : ∀ {σ σ' τ}, MDiffAt (T% σ) x → MDiffAt (T% σ') x →
      φ (σ + σ') τ x = φ σ τ x + φ σ' τ x)
    (τ_smul : ∀ {f : M → ℝ}, ∀ {σ τ}, MDiffAt f x → MDiffAt (T% τ) x →
        φ σ (f • τ) x = f x • φ σ τ x)
    (τ_add : ∀ {σ τ τ'}, MDiffAt (T% τ) x → MDiffAt (T% τ') x →
        φ σ (τ + τ') x = φ σ τ x + φ σ τ' x)
    {σ : Π x : M, V x} (hσ : MDiffAt (T% σ) x) {τ : Π x : M, V x} (hτ : MDiffAt (T% τ) x) :
    mk2TensorAt I F F' φ σ_smul σ_add τ_smul τ_add (σ x) (τ x) = φ σ τ x := by
  apply tensoriality_criterion₂ I F _ F' _ _ hσ _ hτ _ _ σ_smul σ_add τ_smul τ_add
  · exact mdifferentiable_extend ..
  · exact mdifferentiable_extend ..
  · simp
  · simp

theorem mk2TensorAt_add
    (φ : (Π x : M, V x) → (Π x : M, V x) → (Π x, V' x)) {x}
    (φ_σ_smul : ∀ {f : M → ℝ}, ∀ {σ τ}, MDiffAt f x → MDiffAt (T% σ) x →
      φ (f • σ) τ x = f x • φ σ τ x)
    (φ_σ_add : ∀ {σ σ' τ}, MDiffAt (T% σ) x → MDiffAt (T% σ') x →
      φ (σ + σ') τ x = φ σ τ x + φ σ' τ x)
    (φ_τ_smul : ∀ {f : M → ℝ}, ∀ {σ τ}, MDiffAt f x → MDiffAt (T% τ) x →
        φ σ (f • τ) x = f x • φ σ τ x)
    (φ_τ_add : ∀ {σ τ τ'}, MDiffAt (T% τ) x → MDiffAt (T% τ') x →
        φ σ (τ + τ') x = φ σ τ x + φ σ τ' x)
    (ψ : (Π x : M, V x) → (Π x : M, V x) → (Π x, V' x))
    (ψ_σ_smul : ∀ {f : M → ℝ}, ∀ {σ τ}, MDiffAt f x → MDiffAt (T% σ) x →
      ψ (f • σ) τ x = f x • ψ σ τ x)
    (ψ_σ_add : ∀ {σ σ' τ}, MDiffAt (T% σ) x → MDiffAt (T% σ') x →
      ψ (σ + σ') τ x = ψ σ τ x + ψ σ' τ x)
    (ψ_τ_smul : ∀ {f : M → ℝ}, ∀ {σ τ}, MDiffAt f x → MDiffAt (T% τ) x →
        ψ σ (f • τ) x = f x • ψ σ τ x)
    (ψ_τ_add : ∀ {σ τ τ'}, MDiffAt (T% τ) x → MDiffAt (T% τ') x →
        ψ σ (τ + τ') x = ψ σ τ x + ψ σ τ' x) :
    mk2TensorAt I F F' (φ + ψ)
      (fun {_ _ τ} hf hσ ↦
      (congr($(φ_σ_smul hf hσ (τ := τ)) + $(ψ_σ_smul hf hσ (τ := τ)))).trans (smul_add _ _ _).symm)
      (fun {σ₁ σ₂} τ hσ₁ hσ₂ ↦
        (congr($(φ_σ_add hσ₁ hσ₂ (τ := τ)) + $(ψ_σ_add hσ₁ hσ₂ (τ := τ)))).trans <| by
        dsimp
        abel)
      (fun {_ σ _} hf hτ ↦
      (congr($(φ_τ_smul hf hτ (σ := σ)) + $(ψ_τ_smul hf hτ (σ := σ)))).trans (smul_add _ _ _).symm)
      (fun σ {τ₁ τ₂} hτ₁ hτ₂ ↦
        (congr($(φ_τ_add hτ₁ hτ₂ (σ := σ)) + $(ψ_τ_add hτ₁ hτ₂ (σ := σ)))).trans <| by
        dsimp
        abel)
    = mk2TensorAt I F F' φ φ_σ_smul φ_σ_add φ_τ_smul φ_τ_add
      + mk2TensorAt I F F' ψ ψ_σ_smul ψ_σ_add ψ_τ_smul ψ_τ_add := by
  ext
  simp [mk2TensorAt, IsBilinearMap.toContinuousLinearMap, IsBilinearMap.toLinearMap]

end tensoriality
