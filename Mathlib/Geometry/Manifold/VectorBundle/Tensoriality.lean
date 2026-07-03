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
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame

/-!
# The tensoriality criterion

Given vector bundles `V` and `W` over a manifold `M`, one can construct a section of the hom-bundle
`Π x, V x →L[𝕜] W x` from a *tensorial* operation sending sections of `V` to sections of `W`.
This file provides this construction.

In fact, we define tensoriality, and provide the above criterion, in slightly greater generality:
for operations sending sections of `V` to a vector space `A` (which in the above application is the
fibre `W x`), the construction produces a continuous linear map `V x →L[𝕜] A`.

## Main definitions

* `TensorialAt`: Propositional structure stating that an operation on sections of a vector bundle
  `V` is tensorial.

* `TensorialAt.mkHom`: An operation on sections of `V` which is tensorial at `x` defines a
  continuous linear map out of `V x`.

* `TensorialAt.mkHom₂`: An operation on sections of `V` and `V'` which is tensorial at `x` in both
  arguments defines a continuous bilinear map out of `V x` and `V' x`.

-/

open Bundle FiberBundle Topology Module

open scoped Manifold ContDiff

public section

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

variable
  (F'' : Type*) [NormedAddCommGroup F''] [NormedSpace 𝕜 F'']
  {V'' : M → Type*} [TopologicalSpace (TotalSpace F'' V'')]
  [∀ x, AddCommGroup (V'' x)] [∀ x, Module 𝕜 (V'' x)] [∀ x : M, TopologicalSpace (V'' x)]
  [FiberBundle F'' V'']

variable {A : Type*} [AddCommGroup A] [Module 𝕜 A]

/-- An operation `Φ` on sections of a vector bundle `V` over `M` is *tensorial* at `x : M`, if it
respects addition and scalar multiplication by germs of differentiable functions at `f`. -/
structure TensorialNear (Φ : (Π x : M, V x) → A) (x : M) : Prop where
  smul {f : M → 𝕜} {σ : Π x : M, V x} (hf : ∀ᶠ x' in 𝓝 x, MDiffAt f x')
    (hσ : ∀ᶠ x' in 𝓝 x, MDiffAt (T% σ) x') : Φ (f • σ) = f x • Φ σ
  add {σ σ'} (hσ : ∀ᶠ x' in 𝓝 x, MDiffAt (T% σ) x') (hσ' : ∀ᶠ x' in 𝓝 x, MDiffAt (T% σ') x') :
    Φ (σ + σ') = Φ σ + Φ σ'

/-- An operation `Φ` on sections of a vector bundle `V` over `M` is *tensorial* at `x : M`, if it
respects addition and scalar multiplication by germs of differentiable functions at `f`. -/
structure TensorialAt (Φ : (Π x : M, V x) → A) (x : M) : Prop where
  smul : ∀ {f : M → 𝕜} {σ : Π x : M, V x}, MDiffAt f x → MDiffAt (T% σ) x → Φ (f • σ) = f x • Φ σ
  add : ∀ {σ σ'}, MDiffAt (T% σ) x → MDiffAt (T% σ') x → Φ (σ + σ') = Φ σ + Φ σ'

variable {Φ : (Π x : M, V x) → A} {x : M}
variable {I F F' F''}

namespace TensorialNear

/-- If the operation `Φ` on sections of a vector bundle `V` is tensorial near `x`, then it depends
only on the germ of the section at `x`.

This is later superseded by `TensorialAt.pointwise`, showing that `Φ` depends only on the value at
`x` itself. -/
protected theorem «local» (hΦ : TensorialNear I F Φ x) {σ σ' : Π x : M, V x}
    (hσ : ∀ᶠ x' in 𝓝 x, MDiffAt (T% σ) x') (hσ' : ∀ᶠ x' in 𝓝 x, MDiffAt (T% σ') x')
    (hσσ' : ∀ᶠ x' in 𝓝 x, σ x' = σ' x') :
    Φ σ = Φ σ' := by
  classical
  -- Introduce the indicator function of a neighbourhood `t` of `x` on which equality holds,
  -- and cut off the two sections `σ` and `σ'` using this indicator function.
  let ψ (x' : M) : 𝕜 := if σ x' = σ' x' then 1 else 0
  have hψx : ψ x = 1 := by simp [ψ, hσσ'.self_of_nhds]
  have (x' : M) : (ψ • σ) x' = (ψ • σ') x' := by
    dsimp [ψ]
    split_ifs with hx' <;> simp [hx']
  have hψ' : ∀ᶠ x' in 𝓝 x, MDiffAt ψ x' := by
    have : ∀ᶠ x' in 𝓝 x, MDiffAt (fun (_ : M) ↦ (1 : 𝕜)) x' :=
      Filter.Eventually.of_forall fun x ↦ mdifferentiableAt_const
    filter_upwards [this, hσσ'.eventually_nhds] with x' h h'
    apply h.congr_of_eventuallyEq
    filter_upwards [h'] with x'' hx''
    simp [ψ, hx'']
  calc Φ σ
    _ = Φ (ψ • σ) := by simp [hΦ.smul hψ' hσ, hψx]
    _ = Φ (ψ • σ') := by rw [funext this]
    _ = Φ σ' := by simp [hΦ.smul hψ' hσ', hψx]

variable [VectorBundle 𝕜 F V] [VectorBundle 𝕜 F' V'] [VectorBundle 𝕜 F'' V'']

open Filter Eventually in
/-- A tensorial operation on sections of a vector bundle respects zero (since it respects scalar
multiplication). -/
theorem zero (hΦ : TensorialNear I F Φ x) : Φ 0 = 0 := by
  calc
    Φ 0 = Φ ((0 : M → 𝕜) • (0 : Π x, V x)) := by simp
    _   = 0 • Φ 0 := hΦ.smul (of_forall fun _ ↦ mdifferentiableAt_const)
                             (of_forall fun _ ↦ mdifferentiableAt_zeroSection ..)
    _   = 0 := by simp

/-- A tensorial operation on sections of a vector bundle respects sums (since it respects binary
addition). -/
theorem sum (hΦ : TensorialNear I F Φ x) {ι : Type*} {s : Finset ι} (σ : ι → Π x : M, V x)
    (hσ : ∀ i ∈ s, ∀ᶠ x' in 𝓝 x, MDiffAt (T% (σ i)) x') :
    Φ (fun x' ↦ ∑ i ∈ s, σ i x') = ∑ i ∈ s, Φ (σ i) := by
  classical
  replace hσ : ∀ᶠ x' in 𝓝 x, ∀ i ∈ s, MDiffAt (T% (σ i)) x' :=
    (Finset.eventually_all s).mpr hσ
  -- FIXME: there is a delaborator bug at `hσ` which should be
  -- `∀ᶠ (x' : M) in 𝓝 x, ∀ i ∈ s, MDiffAt (T% (σ i)) x'`
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty]
      exact hΦ.zero
  | insert a s ha h =>
      simp only [Finset.sum_insert ha, ← Pi.add_def]
      simp only [Finset.mem_insert, forall_eq_or_imp] at hσ
      rw [hΦ.add]
      · rw [h]
        filter_upwards [hσ] with x' ⟨_, hx'⟩ using hx'
      · filter_upwards [hσ] with x' ⟨hx', _⟩ using hx'
      · filter_upwards [hσ] with x' ⟨_, H⟩ using .sum_section H

variable [CompleteSpace 𝕜]
  [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 F'] [FiniteDimensional 𝕜 F'']
  [ContMDiffVectorBundle 1 F V I] [ContMDiffVectorBundle 1 F' V' I]
  [ContMDiffVectorBundle 1 F'' V'' I]

/-- If the operation `Φ` on sections of a vector bundle `V` is tensorial near `x`, then it depends
only on the value of the section at `x`. -/
lemma pointwise (hΦ : TensorialNear I F Φ x) {σ σ' : Π x : M, V x}
    (hσ : ∀ᶠ x' in 𝓝 x, MDiffAt (T% σ) x') (hσ' : ∀ᶠ x' in 𝓝 x, MDiffAt (T% σ') x')
    (hσσ' : σ x = σ' x) :
    Φ σ = Φ σ' := by
  -- Select a local frame `s` for the bundle `V` near `x`,
  -- and let `c` be the family of linear maps evaluating the coefficients of a section relative to
  -- this frame
  let t := trivializationAt F V x
  have x_mem : x ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt F V x
  let b := Basis.ofVectorSpace 𝕜 F
  let s := t.localFrame b
  let c := t.localFrame_coeff I b
  have mem := t.open_baseSet.mem_nhds x_mem
  have hs : ∀ᶠ x' in 𝓝 x, ∀ i, MDiffAt (T% (s i)) x' := by
    filter_upwards [mem] with x' hx'
    exact fun i ↦ (contMDiffAt_localFrame_of_mem 1 _ b i hx').mdifferentiableAt (by simp)
  have hc {σ : (x : M) → V x} (hσ : ∀ᶠ x' in 𝓝 x, MDiffAt (T% σ) x') :
      ∀ᶠ x' in 𝓝 x, ∀ i, MDiffAt (LinearMap.piApply (c i) σ) x' :=
    (hσ.and mem).mono fun x' ⟨hx', hx''⟩ i ↦
      mdifferentiableAt_localFrame_coeff b hx'' hx' i
  -- By the locality of the operation `(Φ · x)`, its value on `σ` agrees with the value of `Φ` on
  -- the expansion of `σ` into coefficients relative to the frame.
  have hΦ_eq {σ : (x : M) → V x} (hσ : ∀ᶠ x' in 𝓝 x, MDiffAt (T% σ) x') :
      Φ σ = Φ (fun x' ↦ ∑ i, c i x' (σ x') • s i x') := by
    apply hΦ.local hσ
    · filter_upwards [hc hσ, hs] with x' H H'
      exact .sum_section fun i _ ↦ (H i).smul_section (H' i)
    · exact t.eventually_eq_localFrame_sum_coeff_smul b x_mem
  -- Now evaluate using the tensoriality properties.
  rw [hΦ_eq hσ, hΦ_eq hσ', hΦ.sum, hΦ.sum]
  · congr! 1 with i
    replace hσ : ∀ i, ∀ᶠ x' in 𝓝 x, MDiffAt ((LinearMap.piApply (c i)) σ) x' :=
      fun i ↦ (hc hσ).mono fun _ a ↦ a i
    replace hσ' : ∀ i, ∀ᶠ x' in 𝓝 x, MDiffAt ((LinearMap.piApply (c i)) σ') x' :=
      fun i ↦ (hc hσ').mono fun _ a ↦ a i
    replace hs : ∀ i, ∀ᶠ x' in 𝓝 x, MDiffAt (T% (s i)) x' :=
      fun i ↦ Filter.Eventually.mono hs fun _ a ↦ a i
    calc Φ ((LinearMap.piApply (c i) σ) • (s i))
        = c i x (σ x) • Φ (s i) := hΦ.smul (hσ i) (hs i)
      _ = c i x (σ' x) • Φ (s i) := by rw [hσσ']
      _ = Φ ((LinearMap.piApply (c i) σ') • (s i)) :=
          hΦ.smul (hσ' i) (hs i) |>.symm
  · intro i _
    filter_upwards [hc hσ', hs] with x' hx' hx''
    exact (hx' i).smul_section (hx'' i)
  · intro i _
    filter_upwards [hc hσ, hs] with x' hx' hx''
    exact (hx' i).smul_section (hx'' i)

end TensorialNear

namespace TensorialAt

lemma TensorialNear (hΦ : TensorialAt I F Φ x) : TensorialNear I F Φ x where
  smul hf hσ := hΦ.smul hf.self_of_nhds hσ.self_of_nhds
  add hσ hσ' := hΦ.add hσ.self_of_nhds hσ'.self_of_nhds

/-- If the operation `Φ` on sections of a vector bundle `V` is tensorial at `x`, then it depends
only on the germ of the section at `x`.

This is later superseded by `TensorialAt.pointwise`, showing that `Φ` depends only on the value at
`x` itself. -/
protected theorem «local» (hΦ : TensorialAt I F Φ x) {σ σ' : Π x : M, V x}
    (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x) (hσσ' : ∀ᶠ x' in 𝓝 x, σ x' = σ' x') :
    Φ σ = Φ σ' := by
  classical
  -- Introduce the indicator function of a neighbourhood `t` of `x` on which equality holds,
  -- and cut off the two sections `σ` and `σ'` using this indicator function.
  let ψ (x' : M) : 𝕜 := if σ x' = σ' x' then 1 else 0
  have hψx : ψ x = 1 := by simp [ψ, hσσ'.self_of_nhds]
  have (x' : M) : (ψ • σ) x' = (ψ • σ') x' := by
    dsimp [ψ]
    split_ifs with hx' <;> simp [hx']
  have hψ' : MDiffAt ψ x := by
    have : MDiffAt (fun (_x : M) ↦ (1 : 𝕜)) x := mdifferentiableAt_const
    exact this.congr_of_eventuallyEq (hσσ'.mono fun x' hx' ↦ by simp [ψ, hx'])
  calc Φ σ
    _ = Φ (ψ • σ) := by simp [hΦ.smul hψ' hσ, hψx]
    _ = Φ (ψ • σ') := by rw [funext this]
    _ = Φ σ' := by simp [hΦ.smul hψ' hσ', hψx]

variable [VectorBundle 𝕜 F V] [VectorBundle 𝕜 F' V'] [VectorBundle 𝕜 F'' V'']

/-- A tensorial operation on sections of a vector bundle respects zero (since it respects scalar
multiplication). -/
theorem zero (hΦ : TensorialAt I F Φ x) : Φ 0 = 0 := by
  calc
    Φ 0 = Φ ((0 : M → 𝕜) • (0 : Π x, V x)) := by simp
    _   = 0 • Φ 0 := hΦ.smul mdifferentiableAt_const (mdifferentiable_zeroSection ..)
    _   = 0 := by simp

/-- A tensorial operation on sections of a vector bundle respects sums (since it respects binary
addition). -/
theorem sum (hΦ : TensorialAt I F Φ x) {ι : Type*} {s : Finset ι} (σ : ι → Π x : M, V x)
    (hσ : ∀ i ∈ s, MDiffAt (T% (σ i)) x) :
    Φ (fun x' ↦ ∑ i ∈ s, σ i x') = ∑ i ∈ s, Φ (σ i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty]
      exact hΦ.zero
  | insert a s ha h =>
      simp only [Finset.mem_insert, forall_eq_or_imp] at hσ
      simp only [Finset.sum_insert ha, ← h hσ.2]
      exact hΦ.add hσ.1 <| .sum_section hσ.2

variable [CompleteSpace 𝕜]
  [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 F'] [FiniteDimensional 𝕜 F'']
  [ContMDiffVectorBundle 1 F V I] [ContMDiffVectorBundle 1 F' V' I]
  [ContMDiffVectorBundle 1 F'' V'' I]

/-- If the operation `Φ` on sections of a vector bundle `V` is tensorial at `x`, then it depends
only on the value of the section at `x`. -/
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
  -- By the locality of the operation `(Φ · x)`, its value on `σ` agrees with the value of `Φ` on
  -- the expansion of `σ` into coefficients relative to the frame.
  have hΦ_eq {σ : (x : M) → V x} (hσ : MDiffAt (T% σ) x) :
      Φ σ = Φ (fun x' ↦ ∑ i, c i x' (σ x') • s i x') :=
    hΦ.local hσ
      (.sum_section fun i _ ↦ (hc hσ i).smul_section (hs i))
      (t.eventually_eq_localFrame_sum_coeff_smul b x_mem)
  -- Now evaluate using the tensoriality properties.
  rw [hΦ_eq hσ, hΦ_eq hσ', hΦ.sum, hΦ.sum]
  · congr! 1 with i
    calc Φ ((LinearMap.piApply (c i) σ) • (s i))
        = c i x (σ x) • Φ (s i) := hΦ.smul (hc hσ i) (hs i)
      _ = c i x (σ' x) • Φ (s i) := by rw [hσσ']
      _ = Φ ((LinearMap.piApply (c i) σ') • (s i)) :=
          hΦ.smul (hc hσ' i) (hs i) |>.symm
  · exact fun i _ ↦ (hc hσ' i).smul_section (hs i)
  · exact fun i _ ↦ (hc hσ i).smul_section (hs i)

/-- If the operation `Φ` on sections of vector bundles `V` and `V'` is tensorial at `x` in each
argument, then it depends only on the value of the sections at `x`. -/
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

variable [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul 𝕜 A]

/-- Given an `A`-valued operation `Φ` on sections of a vector bundle `V` which is tensorial at `x`,
the construction `TensorialAt.mkHom` provides the associated continuous linear map `V x →L[𝕜] A`. -/
noncomputable def mkHom
    -- `Φ` and `x` explicit to make it easier to generate the side condition at point of use
    (Φ : (Π x : M, V x) → A) (x : M) (hΦ : TensorialAt I F Φ x) :
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
      rw [← hΦ.add (mdifferentiableAt_extend ..) (mdifferentiableAt_extend ..)]
      apply hΦ.pointwise (mdifferentiableAt_extend ..) <|
        mdifferentiableAt_add_section (mdifferentiableAt_extend ..) (mdifferentiableAt_extend ..)
      simp
    map_smul' c v := by
      dsimp
      rw [← hΦ.smul (f := fun _ ↦ c) (mdifferentiable_const ..) (mdifferentiableAt_extend ..)]
      apply hΦ.pointwise (mdifferentiableAt_extend ..) <|
        mdifferentiableAt_const.smul_section (mdifferentiableAt_extend ..)
      simp }

theorem mkHom_apply {Φ : (Π x : M, V x) → A} {x} (hΦ : TensorialAt I F (Φ ·) x)
    {σ : Π x : M, V x} (hσ : MDiffAt (T% σ) x) :
    mkHom Φ x hΦ (σ x) = Φ σ :=
  hΦ.pointwise (mdifferentiableAt_extend ..) hσ (by simp)

theorem mkHom_apply_eq_extend {Φ : (Π x : M, V x) → A} {x} (hΦ : TensorialAt I F Φ x) (σ : V x) :
    mkHom Φ x hΦ σ = Φ (extend F σ) :=
  (rfl)

/-- Given an `A`-valued operation `Φ` on sections of vector bundles `V` and `V'` which is tensorial
at `x` in each argument, the construction `TensorialAt.mkHom₂` provides the associated continuous
linear map `V x →L[𝕜] V' x →L[𝕜] A`. -/
noncomputable def mkHom₂
    -- `Φ` and `x` explicit to make it easier to generate the side conditions at point of use
    (Φ : (Π x : M, V x) → (Π x : M, V' x) → A) (x : M)
    (hΦ₁ : ∀ τ, MDiffAt (T% τ) x → TensorialAt I F (Φ · τ) x)
    (hΦ₂ : ∀ σ, MDiffAt (T% σ) x → TensorialAt I F' (Φ σ) x) :
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
      rw [← (hΦ₁ _ (mdifferentiableAt_extend ..)).add (mdifferentiableAt_extend ..)
        (mdifferentiableAt_extend ..)]
      apply TensorialAt.pointwise₂ hΦ₁ hΦ₂ (mdifferentiableAt_extend ..) _
        (mdifferentiableAt_extend ..) (mdifferentiableAt_extend ..) _ rfl
      · exact mdifferentiableAt_add_section (mdifferentiableAt_extend ..)
          (mdifferentiableAt_extend ..)
      · simp
    smul_left c v w := by
      rw [← (hΦ₁ _ (mdifferentiableAt_extend ..)).smul (f := fun _ ↦ c) (mdifferentiable_const ..)
        (mdifferentiableAt_extend ..)]
      apply TensorialAt.pointwise₂ hΦ₁ hΦ₂ (mdifferentiableAt_extend ..)
        (mdifferentiableAt_const.smul_section (mdifferentiableAt_extend ..))
        (mdifferentiableAt_extend ..) (mdifferentiableAt_extend ..)
      · simp
      · rfl
    add_right v w₁ w₂ := by
      rw [← (hΦ₂ _ (mdifferentiableAt_extend ..)).add (mdifferentiableAt_extend ..)
        (mdifferentiableAt_extend ..)]
      apply TensorialAt.pointwise₂ hΦ₁ hΦ₂ (mdifferentiableAt_extend ..)
        (mdifferentiableAt_extend ..) (mdifferentiableAt_extend ..) <|
        mdifferentiableAt_add_section (mdifferentiableAt_extend ..) (mdifferentiableAt_extend ..)
      · rfl
      · simp
    smul_right c v w := by
      rw [← (hΦ₂ _ (mdifferentiableAt_extend ..)).smul (f := fun _ ↦ c) (mdifferentiable_const ..)
        (mdifferentiableAt_extend ..)]
      apply TensorialAt.pointwise₂ hΦ₁ hΦ₂ (mdifferentiableAt_extend ..)
        (mdifferentiableAt_extend ..) (mdifferentiableAt_extend ..) <|
        mdifferentiableAt_const.smul_section (mdifferentiableAt_extend ..)
      · rfl
      · simp }
  H.toLinearMap.toContinuousBilinearMap

theorem mkHom₂_apply
    {Φ : (Π x : M, V x) → (Π x : M, V' x) → A} {x}
    (hΦ₁ : ∀ τ, MDiffAt (T% τ) x → TensorialAt I F (Φ · τ) x)
    (hΦ₂ : ∀ σ, MDiffAt (T% σ) x → TensorialAt I F' (Φ σ) x)
    {σ : Π x : M, V x} (hσ : MDiffAt (T% σ) x) {τ : Π x : M, V' x} (hτ : MDiffAt (T% τ) x) :
    mkHom₂ Φ x hΦ₁ hΦ₂ (σ x) (τ x) = Φ σ τ :=
  TensorialAt.pointwise₂ hΦ₁ hΦ₂ (mdifferentiableAt_extend ..) hσ (mdifferentiableAt_extend ..) hτ
    (by simp) (by simp)

theorem mkHom₂_apply_eq_extend
    {Φ : (Π x : M, V x) → (Π x : M, V' x) → A} {x}
    (hΦ₁ : ∀ τ, MDiffAt (T% τ) x → TensorialAt I F (Φ · τ) x)
    (hΦ₂ : ∀ σ, MDiffAt (T% σ) x → TensorialAt I F' (Φ σ) x)
    (σ : V x) (τ : V' x) :
    mkHom₂ Φ x hΦ₁ hΦ₂ σ τ = Φ (extend F σ) (extend F' τ) :=
  (rfl)

/-- Given an `A`-valued operation `Φ` on sections of vector bundles `V`, `V'` and `V''` which is
tensorial at `x` in each argument, the construction `TensorialAt.mkHom₃` provides the associated
continuous linear map `V x →L[𝕜] V' x →L[𝕜] V'' x →L[𝕜] A`. -/
noncomputable def mkHom₃
    -- `Φ` and `x` explicit to make it easier to generate the side conditions at point of use
    (Φ : (Π x : M, V x) → (Π x : M, V' x) → (Π x : M, V'' x) → A) (x : M)
    -- TODO: may require further differentiability conditions here, or not!
    -- if so, propagate down below
    (hΦ₁ : ∀ τ υ, MDiffAt (T% τ) x → MDiffAt (T% υ) x → TensorialAt I F (Φ · τ υ) x)
    (hΦ₂ : ∀ σ υ, MDiffAt (T% σ) x → MDiffAt (T% υ) x → TensorialAt I F' (Φ σ · υ) x)
    (hΦ₃ : ∀ σ τ, MDiffAt (T% σ) x → MDiffAt (T% τ) x → TensorialAt I F'' (Φ σ τ ·) x) :
    V x →L[𝕜] V' x →L[𝕜] V'' x →L[𝕜] A :=
  sorry -- TODO: prove mutatis mutandis

theorem mkHom₃_apply
    {Φ : (Π x : M, V x) → (Π x : M, V' x) → (Π x : M, V'' x) → A} {x}
    (hΦ₁ : ∀ τ υ, MDiffAt (T% τ) x → MDiffAt (T% υ) x → TensorialAt I F (Φ · τ υ) x)
    (hΦ₂ : ∀ σ υ, MDiffAt (T% σ) x → MDiffAt (T% υ) x → TensorialAt I F' (Φ σ · υ) x)
    (hΦ₃ : ∀ σ τ, MDiffAt (T% σ) x → MDiffAt (T% τ) x → TensorialAt I F'' (Φ σ τ ·) x)
    {σ : Π x : M, V x} (hσ : MDiffAt (T% σ) x) {τ : Π x : M, V' x} (hτ : MDiffAt (T% τ) x)
    {τ' : Π x : M, V'' x} (hτ : MDiffAt (T% τ') x) :
    mkHom₃ Φ x hΦ₁ hΦ₂ hΦ₃ (σ x) (τ x) (τ' x) = Φ σ τ τ' :=
  sorry -- mkHom₂_apply mutatis mutandis

theorem mkHom₃_apply_eq_extend
    {Φ : (Π x : M, V x) → (Π x : M, V' x) → (Π x : M, V'' x) → A} {x}
    (hΦ₁ : ∀ τ υ, MDiffAt (T% τ) x → MDiffAt (T% υ) x → TensorialAt I F (Φ · τ υ) x)
    (hΦ₂ : ∀ σ υ, MDiffAt (T% σ) x → MDiffAt (T% υ) x → TensorialAt I F' (Φ σ · υ) x)
    (hΦ₃ : ∀ σ τ, MDiffAt (T% σ) x → MDiffAt (T% τ) x → TensorialAt I F'' (Φ σ τ ·) x)
    (σ : V x) (τ : V' x) (τ' : V'' x) :
    mkHom₃ Φ x hΦ₁ hΦ₂ hΦ₃ σ τ τ' =
      Φ (FiberBundle.extend F σ) (FiberBundle.extend F' τ) (FiberBundle.extend F'' τ') :=
  sorry -- once the above proofs are filled in, this should be try by `rfl`

end TensorialAt
