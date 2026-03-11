/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.InnerProductSpace.MeanErgodic
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Functions invariant under (quasi)ergodic map

In this file we prove that an a.e. strongly measurable function `g : α → X`
that is a.e. invariant under a (quasi)ergodic map is a.e. equal to a constant.
We prove several versions of this statement with slightly different measurability assumptions.
We also formulate a version for `MeasureTheory.AEEqFun` functions
with all a.e. equalities replaced with equalities in the quotient space.
-/

public section

open Function Set Filter MeasureTheory Topology TopologicalSpace

variable {α X : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}

/-- Let `f : α → α` be a (quasi)ergodic map. Let `g : α → X` is a null-measurable function
from `α` to a nonempty space with a countable family of measurable sets
separating points of a set `s` such that `f x ∈ s` for a.e. `x`.
If `g` that is a.e.-invariant under `f`, then `g` is a.e. constant. -/
theorem QuasiErgodic.ae_eq_const_of_ae_eq_comp_of_ae_range₀ [Nonempty X] [MeasurableSpace X]
    {s : Set X} [MeasurableSpace.CountablySeparated s] {f : α → α} {g : α → X}
    (h : QuasiErgodic f μ) (hs : ∀ᵐ x ∂μ, g x ∈ s) (hgm : NullMeasurable g μ)
    (hg_eq : g ∘ f =ᵐ[μ] g) :
    ∃ c, g =ᵐ[μ] const α c := by
  refine exists_eventuallyEq_const_of_eventually_mem_of_forall_separating MeasurableSet hs ?_
  refine fun U hU ↦ h.ae_mem_or_ae_notMem₀ (s := g ⁻¹' U) (hgm hU) ?_b
  refine (hg_eq.mono fun x hx ↦ ?_).set_eq
  rw [← preimage_comp, mem_preimage, mem_preimage, hx]

section CountableSeparatingOnUniv

variable [Nonempty X] [MeasurableSpace X] [MeasurableSpace.CountablySeparated X]
  {f : α → α} {g : α → X}

/-- Let `f : α → α` be a (pre)ergodic map.
Let `g : α → X` be a measurable function from `α` to a nonempty measurable space
with a countable family of measurable sets separating the points of `X`.
If `g` is invariant under `f`, then `g` is a.e. constant. -/
theorem PreErgodic.ae_eq_const_of_ae_eq_comp (h : PreErgodic f μ) (hgm : Measurable g)
    (hg_eq : g ∘ f = g) : ∃ c, g =ᵐ[μ] const α c :=
  exists_eventuallyEq_const_of_forall_separating MeasurableSet fun U hU ↦
    h.ae_mem_or_ae_notMem (s := g ⁻¹' U) (hgm hU) <| by rw [← preimage_comp, hg_eq]

/-- Let `f : α → α` be a quasi-ergodic map.
Let `g : α → X` be a null-measurable function from `α` to a nonempty measurable space
with a countable family of measurable sets separating the points of `X`.
If `g` is a.e.-invariant under `f`, then `g` is a.e. constant. -/
theorem QuasiErgodic.ae_eq_const_of_ae_eq_comp₀ (h : QuasiErgodic f μ) (hgm : NullMeasurable g μ)
    (hg_eq : g ∘ f =ᵐ[μ] g) : ∃ c, g =ᵐ[μ] const α c :=
  h.ae_eq_const_of_ae_eq_comp_of_ae_range₀ (s := univ) univ_mem hgm hg_eq

/-- Let `f : α → α` be an ergodic map.
Let `g : α → X` be a null-measurable function from `α` to a nonempty measurable space
with a countable family of measurable sets separating the points of `X`.
If `g` is a.e.-invariant under `f`, then `g` is a.e. constant. -/
theorem Ergodic.ae_eq_const_of_ae_eq_comp₀ (h : Ergodic f μ) (hgm : NullMeasurable g μ)
    (hg_eq : g ∘ f =ᵐ[μ] g) : ∃ c, g =ᵐ[μ] const α c :=
  h.quasiErgodic.ae_eq_const_of_ae_eq_comp₀ hgm hg_eq

end CountableSeparatingOnUniv

variable [TopologicalSpace X] [MetrizableSpace X] [Nonempty X] {f : α → α}

namespace QuasiErgodic

/-- Let `f : α → α` be a quasi-ergodic map.
Let `g : α → X` be an a.e. strongly measurable function
from `α` to a nonempty metrizable topological space.
If `g` is a.e.-invariant under `f`, then `g` is a.e. constant. -/
theorem ae_eq_const_of_ae_eq_comp_ae {g : α → X} (h : QuasiErgodic f μ)
    (hgm : AEStronglyMeasurable g μ) (hg_eq : g ∘ f =ᵐ[μ] g) : ∃ c, g =ᵐ[μ] const α c := by
  borelize X
  rcases hgm.isSeparable_ae_range with ⟨t, ht, hgt⟩
  haveI := ht.secondCountableTopology
  exact h.ae_eq_const_of_ae_eq_comp_of_ae_range₀ hgt hgm.aemeasurable.nullMeasurable hg_eq

theorem eq_const_of_compQuasiMeasurePreserving_eq (h : QuasiErgodic f μ) {g : α →ₘ[μ] X}
    (hg_eq : g.compQuasiMeasurePreserving f h.1 = g) : ∃ c, g = .const α c :=
  have : g ∘ f =ᵐ[μ] g := (g.coeFn_compQuasiMeasurePreserving h.1).symm.trans
    (hg_eq.symm ▸ .refl _ _)
  let ⟨c, hc⟩ := h.ae_eq_const_of_ae_eq_comp_ae g.aestronglyMeasurable this
  ⟨c, AEEqFun.ext <| hc.trans (AEEqFun.coeFn_const _ _).symm⟩

end QuasiErgodic

namespace Ergodic

/-- Let `f : α → α` be an ergodic map.
Let `g : α → X` be an a.e. strongly measurable function
from `α` to a nonempty metrizable topological space.
If `g` is a.e.-invariant under `f`, then `g` is a.e. constant. -/
theorem ae_eq_const_of_ae_eq_comp_ae {g : α → X} (h : Ergodic f μ) (hgm : AEStronglyMeasurable g μ)
    (hg_eq : g ∘ f =ᵐ[μ] g) : ∃ c, g =ᵐ[μ] const α c :=
  h.quasiErgodic.ae_eq_const_of_ae_eq_comp_ae hgm hg_eq

theorem eq_const_of_compMeasurePreserving_eq (h : Ergodic f μ) {g : α →ₘ[μ] X}
    (hg_eq : g.compMeasurePreserving f h.1 = g) : ∃ c, g = .const α c :=
  h.quasiErgodic.eq_const_of_compQuasiMeasurePreserving_eq hg_eq

lemma eqLocus_compMeasurePreserving_eq_range_const {E : Type*} {p : ENNReal}
    [NormedAddCommGroup E] (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
    [Fact (1 ≤ p)] [IsFiniteMeasure μ] (h : Ergodic f μ) :
    LinearMap.eqLocus (Lp.compMeasurePreservingₗᵢ 𝕜 f h.toMeasurePreserving).toContinuousLinearMap 1
    = LinearMap.range (Lp.constₗ (E:=E) p μ 𝕜) := by
  ext g
  simp only [Lp.compMeasurePreservingₗᵢ, LinearMap.mem_eqLocus,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.coe_mk,
    Lp.compMeasurePreservingₗ_apply, Lp.compMeasurePreserving, ZeroHom.toFun_eq_coe, ZeroHom.coe_mk,
    ContinuousLinearMap.one_apply, LinearMap.mem_range, Lp.constₗ_apply]
  constructor
  · intro hg
    obtain ⟨y, h⟩ := eq_const_of_compMeasurePreserving_eq h (congrArg Subtype.val hg)
    use y
    exact Eq.symm <|SetLike.coe_eq_coe.mp h
  · intro ⟨y, hg⟩
    rw [← hg]
    ext
    grw [AEEqFun.coeFn_compMeasurePreserving]
    by_cases hZ : NeZero μ
    · apply Filter.EventuallyEq.of_eq
      ext x
      simp [AEEqFun.coeFn_const_eq]
    · simp only [not_neZero.mp hZ]
      rfl

lemma projection_const [IsProbabilityMeasure μ] {E : Type*} [NormedAddCommGroup E] (𝕜 : Type*)
    [RCLike 𝕜] [InnerProductSpace 𝕜 E] [NormedSpace ℝ E] [FiniteDimensional 𝕜 E] [CompleteSpace E]
    (g : Lp E 2 μ) :
    (Lp.constₗ 2 μ 𝕜).range.starProjection g = Lp.const 2 μ (∫ x, g x ∂ μ) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · use (∫ x, g x ∂μ)
    rfl
  · intro g ⟨c,hg⟩
    rw [Lp.constₗ_apply, ← indicatorConstLp_univ] at hg
    rw [inner_sub_left, ← indicatorConstLp_univ, ← hg, L2.inner_indicatorConstLp_indicatorConstLp,
      ← inner_conj_symm, L2.inner_indicatorConstLp_eq_inner_setIntegral]
    simp [sub_self]

/-- A special case of the von Neumann Mean Ergodic Theorem
`ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection` for the Koopman Operator of an
ergodic map. -/
theorem tendsto_birkhoffAverage_const [IsProbabilityMeasure μ] {E : Type*} [NormedAddCommGroup E]
    (𝕜 : Type*) [RCLike 𝕜] [InnerProductSpace 𝕜 E] [NormedSpace ℝ E] [FiniteDimensional 𝕜 E]
    [CompleteSpace E] (g : Lp E 2 μ) (h : Ergodic f μ) :
    Tendsto (birkhoffAverage 𝕜 (Lp.compMeasurePreserving f h.toMeasurePreserving) id · g) atTop
    (𝓝 (Lp.const 2 μ (∫x,g x ∂ μ))) := by
  simpa [eqLocus_compMeasurePreserving_eq_range_const _ h, projection_const] using
    ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection
    (Lp.compMeasurePreservingₗᵢ (E:=E) (p:=2) 𝕜 _ h.toMeasurePreserving).toContinuousLinearMap
    (LinearIsometry.norm_toContinuousLinearMap_le _) g

end Ergodic
