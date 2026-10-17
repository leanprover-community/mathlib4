/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang, Heather Macbeth
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
public import Mathlib.Topology.Algebra.Module.TransferInstance
public import Mathlib.Topology.VectorBundle.FiniteDimensional
import Mathlib.Geometry.Manifold.Notation
public import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame

/-!
# The tensoriality criterion

Given vector bundles `V` and `W` over a manifold `M`, one can construct a section of the hom-bundle
`Π x, V x →L[𝕜] W x` from a *tensorial* operation sending sections of `V` to sections of `W`.
This file provides this construction.

In fact, we define tensoriality, and provide the above criterion, in slightly greater generality:
for operations sending sections of `V` to a vector space `A` (which in the above application is the
fibre `W x`), the construction produces a continuous linear map `V x →L[𝕜] A`.

## Main definitions

* `Tensorial`: Propositional structure stating that an operation on sections of a vector bundle
  `V` is tensorial.

* `Tensorial.mkHom`: An operation on sections of `V` which is tensorial at `x` defines a
  continuous linear map out of `V x`.

* `Tensorial.mkHom₂`: An operation on sections of `V` and `V'` which is tensorial at `x` in both
  arguments defines a continuous bilinear map out of `V x` and `V' x`.

-/

open Bundle FiberBundle Topology Module

open scoped Manifold ContDiff

public section

structure RegPkg {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners 𝕜 E H) [ChartedSpace H M]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (V : M → Type*) [TopologicalSpace (TotalSpace F V)] [∀ x : M, TopologicalSpace (V x)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  [ContMDiffVectorBundle 1 F V I]
  (x : M)
where
  P : (M → 𝕜) → Prop
  P' : (Π x : M, V x) → Prop
  loc_const {f : M → 𝕜} (c : 𝕜) (hf : ∀ᶠ x' in 𝓝 x, f x' = c) : P f
  zeroSection : P' (fun _ ↦ 0)
  extend (v : V x) : P' (extend F v)
  -- sum_fin {n : ℕ} {σ : Fin n → Π x : M, V x} (h : ∀ i, P' (σ i)) : P' (∑ i, σ i)
  smul {f : M → 𝕜} {σ : Π x, V x} (hf : P f) (hσ : P' σ) : P' (fun x ↦ f x • σ x)
  add {σ σ' : Π x, V x} (hσ : P' σ) (hσ' : P' σ') : P' (σ + σ')
  localFrame_fin {e : Trivialization F (TotalSpace.proj (F := F) (E := V))}
      [MemTrivializationAtlas e]
      (he : x ∈ e.baseSet)
      {n : ℕ} (b : Basis (Fin n) 𝕜 F) {σ : Π x, V x} (hσ : P' σ) (i : Fin n) :
      P' (e.localFrame b i)
  localFrame_coeff_fin {e : Trivialization F (TotalSpace.proj (F := F) (E := V))}
      [MemTrivializationAtlas e]
      (he : x ∈ e.baseSet)
      {n : ℕ} (b : Basis (Fin n) 𝕜 F) {σ : Π x, V x} (hσ : P' σ) (i : Fin n) :
      P ((LinearMap.piApply (e.localFrameCoeff I b i)) σ)

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]

variable
  (F' : Type*) [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {V' : M → Type*} [TopologicalSpace (TotalSpace F' V')]
  [∀ x, AddCommGroup (V' x)] [∀ x, Module 𝕜 (V' x)] [∀ x : M, TopologicalSpace (V' x)]
  [FiberBundle F' V']

variable
  (F'' : Type*) [NormedAddCommGroup F''] [NormedSpace 𝕜 F'']
  {V'' : M → Type*} [TopologicalSpace (TotalSpace F'' V'')]
  [∀ x, AddCommGroup (V'' x)] [∀ x, Module 𝕜 (V'' x)] [∀ x : M, TopologicalSpace (V'' x)]
  [FiberBundle F'' V'']

variable {A : Type*} [AddCommGroup A] [Module 𝕜 A]

namespace RegPkg

variable {x : M} (R : RegPkg I F V x)

lemma const (c : 𝕜) : R.P (fun _ ↦ c) := by
  simp [R.loc_const c]

lemma sum_section {ι : Type*} {s : Finset ι} {σ : ι → Π x : M, V x}
    (hσ : ∀ i ∈ s, R.P' (σ i)) : R.P' (fun x ↦ ∑ i ∈ s, σ i x) := by
  -- see `Finset.sum_apply x s σ`
  sorry

lemma localFrame [FiniteDimensional 𝕜 F] {ι : Type*}
  {e : Trivialization F TotalSpace.proj} [MemTrivializationAtlas e]
  (b : Basis ι 𝕜 F) (he : x ∈ e.baseSet) {σ : (x : M) → V x} (hσ : R.P' σ) (i : ι) :
      R.P' (e.localFrame b i) := by
  sorry

lemma localFrame_coeff [FiniteDimensional 𝕜 F] {ι : Type*}
  {e : Trivialization F TotalSpace.proj} [MemTrivializationAtlas e]
  (b : Basis ι 𝕜 F) (he : x ∈ e.baseSet) {σ : (x : M) → V x} (hσ : R.P' σ) (i : ι) :
      R.P ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) := by
  sorry

end RegPkg

structure Tensorial {x : M} (R : RegPkg I F V x) (Φ : (Π x : M, V x) → A) : Prop where
  smul {f : M → 𝕜} {σ : Π x : M, V x} (hf : R.P f)
    (hσ : R.P' σ) : Φ (f • σ) = f x • Φ σ
  add {σ σ'} (hσ : R.P' σ) (hσ' : R.P' σ') :
    Φ (σ + σ') = Φ σ + Φ σ'

variable {Φ : (Π x : M, V x) → A} {x : M}
variable {F' F''}

namespace Tensorial

variable {R : RegPkg I F V x}


/-- If the operation `Φ` on sections of a vector bundle `V` is tensorial at `x`, then it depends
only on the germ of the section at `x`.

This is later superseded by `TensorialAt.pointwise`, showing that `Φ` depends only on the value at
`x` itself. -/
protected theorem «local» (hΦ : Tensorial R Φ) {σ σ' : Π x : M, V x}
    (hσ : R.P' σ) (hσ' : R.P' σ') (hσσ' : ∀ᶠ x' in 𝓝 x, σ x' = σ' x') :
    Φ σ = Φ σ' := by
  classical
  -- Introduce the indicator function of a neighbourhood `t` of `x` on which equality holds,
  -- and cut off the two sections `σ` and `σ'` using this indicator function.
  let ψ (x' : M) : 𝕜 := if σ x' = σ' x' then 1 else 0
  have hψx : ψ x = 1 := by simp [ψ, hσσ'.self_of_nhds]
  have (x' : M) : (ψ • σ) x' = (ψ • σ') x' := by
    dsimp [ψ]
    split_ifs with hx' <;> simp [hx']
  have hψ' : R.P ψ :=
    R.loc_const 1 (hσσ'.mono fun x' hx' ↦ by simp [ψ, hx'])
  calc Φ σ
    _ = Φ (ψ • σ) := by simp [hΦ.smul hψ' hσ, hψx]
    _ = Φ (ψ • σ') := by rw [funext this]
    _ = Φ σ' := by simp [hΦ.smul hψ' hσ', hψx]

variable [VectorBundle 𝕜 F' V'] [VectorBundle 𝕜 F'' V'']

/-- A tensorial operation on sections of a vector bundle respects zero (since it respects scalar
multiplication). -/
theorem zero (hΦ : Tensorial R Φ) : Φ 0 = 0 := by
  calc
    Φ 0 = Φ ((0 : M → 𝕜) • (0 : Π x, V x)) := by simp
    _   = 0 • Φ 0 := hΦ.smul (R.const 0) R.zeroSection
    _   = 0 := by simp

/-- A tensorial operation on sections of a vector bundle respects sums (since it respects binary
addition). -/
theorem sum (hΦ : Tensorial R Φ) {ι : Type*} {s : Finset ι} (σ : ι → Π x : M, V x)
    (hσ : ∀ i ∈ s, R.P' (σ i)) :
    Φ (fun x' ↦ ∑ i ∈ s, σ i x') = ∑ i ∈ s, Φ (σ i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty]
      exact hΦ.zero
  | insert a s ha h =>
      simp only [Finset.mem_insert, forall_eq_or_imp] at hσ
      simp only [Finset.sum_insert ha, ← h hσ.2]
      apply hΦ.add hσ.1 <| R.sum_section hσ.2

variable [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 F'] [FiniteDimensional 𝕜 F'']
  --[ContMDiffVectorBundle 1 F V I] [ContMDiffVectorBundle 1 F' V' I]
  --[ContMDiffVectorBundle 1 F'' V'' I]

/-- If the operation `Φ` on sections of a vector bundle `V` is tensorial at `x`, then it depends
only on the value of the section at `x`. -/
lemma pointwise (hΦ : Tensorial R Φ) {σ σ' : Π x : M, V x}
    (hσ : R.P' σ) (hσ' : R.P' σ') (hσσ' : σ x = σ' x) :
    Φ σ = Φ σ' := by
  -- Select a local frame `s` for the bundle `V` near `x`,
  -- and let `c` be the family of linear maps evaluating the coefficients of a section relative to
  -- this frame
  let t := trivializationAt F V x
  have x_mem : x ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt F V x
  let b := Basis.ofVectorSpace 𝕜 F
  let s := t.localFrame b
  let c := t.localFrameCoeff I b
  have hs : ∀ i, R.P' (s i) :=
    R.localFrame b x_mem hσ
  have hc {σ : (x : M) → V x} (hσ : R.P' σ) : ∀ i, R.P (LinearMap.piApply (c i) σ) :=
    R.localFrame_coeff b x_mem hσ
  -- By the locality of the operation `(Φ · x)`, its value on `σ` agrees with the value of `Φ` on
  -- the expansion of `σ` into coefficients relative to the frame.
  have hΦ_eq {σ : (x : M) → V x} (hσ : R.P' σ) :
      Φ σ = Φ (fun x' ↦ ∑ i, c i x' (σ x') • s i x') :=
    hΦ.local hσ
      (R.sum_section fun i _ ↦ R.smul (hc hσ i) (hs i))
      (t.eventually_eq_localFrame_sum_coeff_smul b x_mem)
  -- Now evaluate using the tensoriality properties.
  rw [hΦ_eq hσ, hΦ_eq hσ', hΦ.sum, hΦ.sum]
  · congr! 1 with i
    calc Φ ((LinearMap.piApply (c i) σ) • (s i))
        = c i x (σ x) • Φ (s i) := hΦ.smul (hc hσ i) (hs i)
      _ = c i x (σ' x) • Φ (s i) := by rw [hσσ']
      _ = Φ ((LinearMap.piApply (c i) σ') • (s i)) :=
          hΦ.smul (hc hσ' i) (hs i) |>.symm
  · exact fun i _ ↦ R.smul (hc hσ' i) (hs i)
  · exact fun i _ ↦ R.smul (hc hσ i) (hs i)

/-- If the operation `Φ` on sections of vector bundles `V` and `V'` is tensorial at `x` in each
argument, then it depends only on the value of the sections at `x`. -/
lemma pointwise₂ [ContMDiffVectorBundle 1 F' V' I]
    {Φ : (Π x : M, V x) → (Π x : M, V' x) → A} {x}
    {R : RegPkg I F V x} {R' : RegPkg I F' V' x}
    (hΦ₁ : ∀ τ, R'.P' τ → Tensorial R (Φ · τ))
    (hΦ₂ : ∀ σ, R.P' σ → Tensorial R' (Φ σ ·))
    {σ σ' : Π x : M, V x} {τ τ' : Π x : M, V' x}
    (hσ : R.P' σ) (hσ' : R.P' σ')
    (hτ : R'.P' τ) (hτ' : R'.P' τ')
    (hσσ' : σ x = σ' x) (hττ' : τ x = τ' x) :
    Φ σ τ = Φ σ' τ' := by
  trans Φ σ' τ
  · exact (hΦ₁ _ hτ).pointwise hσ hσ' hσσ'
  · exact (hΦ₂ _ hσ').pointwise hτ hτ' hττ'

variable [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul 𝕜 A] [CompleteSpace 𝕜]

/-- Given an `A`-valued operation `Φ` on sections of a vector bundle `V` which is tensorial at `x`,
the construction `TensorialAt.mkHom` provides the associated continuous linear map `V x →L[𝕜] A`. -/
noncomputable def mkHom
    -- `Φ` and `x` explicit to make it easier to generate the side condition at point of use
    (Φ : (Π x : M, V x) → A) (x : M) {R : RegPkg I F V x} (hΦ : Tensorial R Φ) :
    V x →L[𝕜] A :=
  have : T2Space (V x) := FiberBundle.t2Space F V x
  have : FiniteDimensional 𝕜 (V x) := VectorBundle.finiteDimensional 𝕜 F V x
  have : IsTopologicalAddGroup (V x) :=
    (VectorBundle.continuousLinearEquivAt 𝕜 F V x).toContinuousAddEquiv.isTopologicalAddGroup
  have (x : M) : ContinuousSMul 𝕜 (V x) :=
    (VectorBundle.continuousLinearEquivAt 𝕜 F V x).continuousSMul
  LinearMap.toContinuousLinearMap {
    toFun v := Φ (extend F v)
    map_add' v₁ v₂ := by
      rw [← hΦ.add (R.extend v₁) (R.extend v₂)]
      apply hΦ.pointwise (R.extend _) <| R.add (R.extend v₁) (R.extend v₂)
      simp
    map_smul' c v := by
      dsimp
      rw [← hΦ.smul (R.const c) (R.extend _)]
      apply hΦ.pointwise (R.extend _) <|
        R.smul (R.const c) (R.extend _)
      simp }

theorem mkHom_apply {Φ : (Π x : M, V x) → A} (hΦ : Tensorial R Φ)
    {σ : Π x : M, V x} (hσ : R.P' σ) :
    mkHom Φ x hΦ (σ x) = Φ σ :=
  hΦ.pointwise (R.extend _) hσ (by simp)

theorem mkHom_apply_eq_extend {Φ : (Π x : M, V x) → A} (hΦ : Tensorial R Φ) (σ : V x) :
    mkHom Φ x hΦ σ = Φ (extend F σ) :=
  (rfl)

/-- Given an `A`-valued operation `Φ` on sections of vector bundles `V` and `V'` which is tensorial
at `x` in each argument, the construction `TensorialAt.mkHom₂` provides the associated continuous
linear map `V x →L[𝕜] V' x →L[𝕜] A`. -/
noncomputable def mkHom₂ [ContMDiffVectorBundle 1 F' V' I]
    -- `Φ` and `x` explicit to make it easier to generate the side conditions at point of use
    (Φ : (Π x : M, V x) → (Π x : M, V' x) → A) (x : M)
    {R : RegPkg I F V x} {R' : RegPkg I F' V' x}
    (hΦ₁ : ∀ τ, R'.P' τ → Tensorial R (Φ · τ))
    (hΦ₂ : ∀ σ, R.P' σ → Tensorial R' (Φ σ ·)) :
    V x →L[𝕜] V' x →L[𝕜] A :=
  have : T2Space (V x) := FiberBundle.t2Space F V x
  have : FiniteDimensional 𝕜 (V x) := VectorBundle.finiteDimensional 𝕜 F V x
  have : T2Space (V' x) := FiberBundle.t2Space F' V' x
  have : FiniteDimensional 𝕜 (V' x) := VectorBundle.finiteDimensional 𝕜 F' V' x
  have : IsTopologicalAddGroup (V x) :=
    (VectorBundle.continuousLinearEquivAt 𝕜 F V x).toContinuousAddEquiv.isTopologicalAddGroup
  have : IsTopologicalAddGroup (V' x) :=
    (VectorBundle.continuousLinearEquivAt 𝕜 F' V' x).toContinuousAddEquiv.isTopologicalAddGroup
  have (x : M) : ContinuousSMul 𝕜 (V x) :=
    (VectorBundle.continuousLinearEquivAt 𝕜 F V x).continuousSMul
  have (x : M) : ContinuousSMul 𝕜 (V' x) :=
    (VectorBundle.continuousLinearEquivAt 𝕜 F' V' x).continuousSMul
  have H : IsBilinearMap 𝕜
    (fun (v : V x) (w : V' x) ↦ Φ (extend F v) (extend F' w)) :=
  { add_left v₁ v₂ w := by
      rw [← (hΦ₁ _ <| R'.extend w).add (R.extend v₁) (R.extend v₂)]
      exact Tensorial.pointwise₂ hΦ₁ hΦ₂ (R.extend (v₁ + v₂)) (R.add (R.extend v₁) (R.extend v₂))
          (R'.extend w) (R'.extend w) (by simp) rfl
    smul_left c v w := by
      rw [← (hΦ₁ _ <| R'.extend w).smul (f := fun _ ↦ c) (R.const c) (R.extend v)]
      exact Tensorial.pointwise₂ hΦ₁ hΦ₂ (R.extend _) (R.smul (R.const c) (R.extend v))
              (R'.extend w) (R'.extend w) (by simp) rfl
    add_right v w₁ w₂ := by
      rw [← (hΦ₂ _ (R.extend v)).add (R'.extend w₁) (R'.extend w₂) ]
      exact Tensorial.pointwise₂ hΦ₁ hΦ₂ (R.extend _) (R.extend _) (R'.extend _)
        (R'.add (R'.extend w₁) (R'.extend w₂)) rfl (by simp)
    smul_right c v w := by
      rw [← (hΦ₂ _ (R.extend _)).smul (R'.const ..) (R'.extend _)]
      apply Tensorial.pointwise₂ hΦ₁ hΦ₂ (R.extend _)
        (R.extend ..) (R'.extend ..) (R'.smul (R'.const c) (R'.extend w)) rfl (by simp) }
  H.toLinearMap.toContinuousBilinearMap

theorem mkHom₂_apply [ContMDiffVectorBundle 1 F' V' I]
    {Φ : (Π x : M, V x) → (Π x : M, V' x) → A} {x}
    {R : RegPkg I F V x} {R' : RegPkg I F' V' x}
    (hΦ₁ : ∀ τ, R'.P' τ → Tensorial R (Φ · τ))
    (hΦ₂ : ∀ σ, R.P' σ → Tensorial R' (Φ σ ·))
    {σ : Π x : M, V x} (hσ : R.P' σ)
    {τ : Π x : M, V' x} (hτ : R'.P' τ) :
    mkHom₂ Φ x hΦ₁ hΦ₂ (σ x) (τ x) = Φ σ τ :=
  Tensorial.pointwise₂ hΦ₁ hΦ₂ (R.extend _) hσ (R'.extend _) hτ
    (by simp) (by simp)

theorem mkHom₂_apply_eq_extend [ContMDiffVectorBundle 1 F' V' I]
    {Φ : (Π x : M, V x) → (Π x : M, V' x) → A} {x}
    {R : RegPkg I F V x} {R' : RegPkg I F' V' x}
    (hΦ₁ : ∀ τ, R'.P' τ → Tensorial R (Φ · τ))
    (hΦ₂ : ∀ σ, R.P' σ → Tensorial R' (Φ σ ·))
    (σ : V x) (τ : V' x) :
    mkHom₂ Φ x hΦ₁ hΦ₂ σ τ = Φ (extend F σ) (extend F' τ) :=
  (rfl)

/-- Given an `A`-valued operation `Φ` on sections of vector bundles `V`, `V'` and `V''` which is
tensorial at `x` in each argument, the construction `TensorialAt.mkHom₃` provides the associated
continuous linear map `V x →L[𝕜] V' x →L[𝕜] V'' x →L[𝕜] A`. -/
noncomputable def mkHom₃ [ContMDiffVectorBundle 1 F' V' I] [ContMDiffVectorBundle 1 F'' V'' I]
    {R : RegPkg I F V x} {R' : RegPkg I F' V' x} {R'' : RegPkg I F'' V'' x}
    -- `Φ` and `x` explicit to make it easier to generate the side conditions at point of use
    (Φ : (Π x : M, V x) → (Π x : M, V' x) → (Π x : M, V'' x) → A) (x : M)
    -- TODO: may require further differentiability conditions here, or not!
    -- if so, propagate down below
    (hΦ₁ : ∀ τ υ, R'.P' τ → R''.P' υ → Tensorial R (Φ · τ υ))
    (hΦ₂ : ∀ σ υ, R.P' σ → R''.P' υ → Tensorial R' (Φ σ · υ))
    (hΦ₃ : ∀ σ τ, R.P' σ → R'.P' τ → Tensorial R'' (Φ σ τ ·)) :
    V x →L[𝕜] V' x →L[𝕜] V'' x →L[𝕜] A :=
  sorry -- TODO: prove mutatis mutandis

theorem mkHom₃_apply [ContMDiffVectorBundle 1 F' V' I] [ContMDiffVectorBundle 1 F'' V'' I]
    {R : RegPkg I F V x} {R' : RegPkg I F' V' x} {R'' : RegPkg I F'' V'' x}
    {Φ : (Π x : M, V x) → (Π x : M, V' x) → (Π x : M, V'' x) → A} {x}
    (hΦ₁ : ∀ τ υ, R'.P' τ → R''.P' υ → Tensorial R (Φ · τ υ))
    (hΦ₂ : ∀ σ υ, R.P' σ → R''.P' υ → Tensorial R' (Φ σ · υ))
    (hΦ₃ : ∀ σ τ, R.P' σ → R'.P' τ → Tensorial R'' (Φ σ τ ·))
    {σ : Π x : M, V x} (hσ : R.P' σ) {τ : Π x : M, V' x} (hτ : R'.P' τ)
    {τ' : Π x : M, V'' x} (hτ : R''.P' τ') :
    mkHom₃ Φ x hΦ₁ hΦ₂ hΦ₃ (σ x) (τ x) (τ' x) = Φ σ τ τ' :=
  sorry -- mkHom₂_apply mutatis mutandis

theorem mkHom₃_apply_eq_extend [ContMDiffVectorBundle 1 F' V' I] [ContMDiffVectorBundle 1 F'' V'' I]
    {R : RegPkg I F V x} {R' : RegPkg I F' V' x} {R'' : RegPkg I F'' V'' x}
    {Φ : (Π x : M, V x) → (Π x : M, V' x) → (Π x : M, V'' x) → A} {x}
    (hΦ₁ : ∀ τ υ, R'.P' τ → R''.P' υ → Tensorial R (Φ · τ υ))
    (hΦ₂ : ∀ σ υ, R.P' σ → R''.P' υ → Tensorial R' (Φ σ · υ))
    (hΦ₃ : ∀ σ τ, R.P' σ → R'.P' τ → Tensorial R'' (Φ σ τ ·))
    (σ : V x) (τ : V' x) (τ' : V'' x) :
    mkHom₃ Φ x hΦ₁ hΦ₂ hΦ₃ σ τ τ' =
      Φ (FiberBundle.extend F σ) (FiberBundle.extend F' τ) (FiberBundle.extend F'' τ') :=
  sorry -- once the above proofs are filled in, this should be try by `rfl`

end Tensorial

def MDiffAtPkg [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜] : RegPkg I F V x where
  P f := MDiffAt f x
  P' σ := MDiffAt (T% σ) x
  loc_const _ h := mdifferentiableAt_const.congr_of_eventuallyEq h
  zeroSection := mdifferentiableAt_zeroSection ..
  extend _ := mdifferentiableAt_extend ..
  smul hf hσ := hf.fun_smul_section hσ
  add hσ hσ' := mdifferentiableAt_add_section hσ hσ'
  localFrame_fin hx _ _ _ _ _ :=
    (contMDiffAt_localFrame_of_mem 1 _ _ _ hx).mdifferentiableAt zero_ne_one.symm
  localFrame_coeff_fin hx _ _ _ hσ _ :=
    mdifferentiableAt_localFrameCoeff _ hx hσ _
