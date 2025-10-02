/-
Copyright (c) 2025 Luigi Massacci. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luigi Massacci
-/

import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.MeasureTheory.Integral.TestAgainst
/-!
# Continuously differentiable functions supported in a compact

This file develops the basic theory of `n`-times continuously differentiable functions with compact
support. That is, for `f : E → F` (where `E`, `F` are normed spaces) and `n : ℕ∞`,

- `f` is `n`-times continuously differentiable: `ContDiff ℝ n f`.
- `f` has compact support: `HasCompactSupport f`.

## Main definitions

- `TestFunction E F n`: the type of `n`-times continuously differentiable
  functions `E → F` with compact support.

## Notation

- `𝓓^{n}(E, F)`:  the space of `n`-times continuously differentiable functions `E → F`
  with compact support.
- `𝓓(E, F)`:   the space of smooth (infinitely differentiable) functions `E → F`
  with compact support i.e. `𝓓^{⊤}_{K}(E, F)`.

## Tags

distributions
-/

open TopologicalSpace SeminormFamily Set Function Seminorm UniformSpace
open scoped BoundedContinuousFunction Topology NNReal

variable (𝕜 E F : Type*) [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]
variable {n : ℕ∞}

/-- The type of `n`-times continuously differentiable maps with compact support. -/
structure TestFunction (n : ℕ∞) : Type _ where
  /-- The underlying function. Use coercion instead. -/
  protected toFun : E → F
  protected contDiff' : ContDiff ℝ n toFun
  protected compact_supp' : HasCompactSupport toFun

/-- Notation for the space of `n`-times continuously differentiable maps
with compact support. -/
scoped[Distributions] notation "𝓓^{" n "}(" E ", " F ")" =>
  TestFunction E F n

/-- Notation for the space of "test functions", i.e. smooth (infinitely differentiable) maps
with compact support. -/
scoped[Distributions] notation "𝓓(" E ", " F ")" =>
  TestFunction E F ⊤

open Distributions

/-- `TestFunctionClass B E F n K` states that `B` is a type of `n`-times continously
differentiable functions `E → F` with compact support. -/
class TestFunctionClass (B : Type*) (E F : outParam <| Type*)
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    (n : outParam ℕ∞) extends FunLike B E F where
  map_contDiff (f : B) : ContDiff ℝ n f
  compact_supp (f : B) : HasCompactSupport f

open TestFunctionClass

instance (B : Type*) (E F : outParam <| Type*)
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    (n : outParam ℕ∞) [TestFunctionClass B E F n] :
    ContinuousMapClass B E F where
  map_continuous f := (map_contDiff f).continuous

instance (B : Type*) (E F : outParam <| Type*)
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    (n : outParam ℕ∞) [TestFunctionClass B E F n] :
    BoundedContinuousMapClass B E F where
  map_bounded f := by
    rcases (map_continuous f).bounded_above_of_compact_support (compact_supp f) with ⟨C, hC⟩
    exact map_bounded (BoundedContinuousFunction.ofNormedAddCommGroup f (map_continuous f) C hC)

namespace TestFunction

instance toTestFunctionClass :
    TestFunctionClass 𝓓^{n}(E, F) E F n where
  coe f := f.toFun
  coe_injective' f g h := by cases f; cases g; congr
  map_contDiff f := f.contDiff'
  compact_supp f := f.compact_supp'

variable {E F}

protected theorem contDiff (f : 𝓓^{n}(E, F)) : ContDiff ℝ n f := map_contDiff f
protected theorem compact_supp (f : 𝓓^{n}(E, F)) : HasCompactSupport f := compact_supp f

@[simp]
theorem toFun_eq_coe {f : 𝓓^{n}(E, F)} : f.toFun = (f : E → F) :=
  rfl

/-- See note [custom simps projection]. -/
def Simps.apply (f : 𝓓^{n}(E, F)) : E →F  := f

-- this must come after the coe_to_fun definition
initialize_simps_projections TestFunction (toFun → apply)

@[ext]

theorem ext {f g : 𝓓^{n}(E, F)} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext _ _ h

/-- Copy of a `TestFunction` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : 𝓓^{n}(E, F)) (f' : E → F) (h : f' = f) : 𝓓^{n}(E, F) where
  toFun := f'
  contDiff' := h.symm ▸ f.contDiff
  compact_supp' := h.symm ▸ f.compact_supp

@[simp]
theorem coe_copy (f : 𝓓^{n}(E, F)) (f' : E → F) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

theorem copy_eq (f : 𝓓^{n}(E, F)) (f' : E → F) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

@[simp]
theorem toBoundedContinuousFunction_apply (f : 𝓓^{n}(E, F)) (x : E) :
   (f : BoundedContinuousFunction E F) x  = (f x) := rfl

section AddCommGroup

instance : Zero 𝓓^{n}(E, F) where
  zero := TestFunction.mk 0 contDiff_zero_fun HasCompactSupport.zero

@[simp]
lemma coe_zero : (0 : 𝓓^{n}(E, F)) = (0 : E → F) :=
  rfl

@[simp]
lemma zero_apply (x : E) : (0 : 𝓓^{n}(E, F)) x = 0 :=
  rfl

instance : Add 𝓓^{n}(E, F) where
  add f g := TestFunction.mk (f + g) (f.contDiff.add g.contDiff) (f.compact_supp.add g.compact_supp)

@[simp]
lemma coe_add (f g : 𝓓^{n}(E, F)) : (f + g : 𝓓^{n}(E, F)) = (f : E → F) + g :=
  rfl

@[simp]
lemma add_apply (f g : 𝓓^{n}(E, F)) (x : E) : (f + g) x = f x + g x :=
  rfl

instance : Neg 𝓓^{n}(E, F) where
  neg f := TestFunction.mk (-f) (f.contDiff.neg) (f.compact_supp.neg)

instance instSub : Sub 𝓓^{n}(E, F) :=
  ⟨fun f g =>
    ⟨f - g, (f.contDiff').sub (g.contDiff'),
    sub_eq_add_neg (f : E → F) g ▸ f.compact_supp.add g.compact_supp.neg
    ⟩
  ⟩

instance instSMul {R} [Semiring R] [Module R F] [SMulCommClass ℝ R F] [ContinuousConstSMul R F] :
   SMul R 𝓓^{n}(E, F) :=
  ⟨fun c f ↦
    TestFunction.mk (c • (f : E → F)) (f.contDiff.const_smul c)  f.compact_supp.smul_left
  ⟩

@[simp]
lemma coe_smul {R} [Semiring R] [Module R F] [SMulCommClass ℝ R F] [ContinuousConstSMul R F]
    (c : R) (f : 𝓓^{n}(E, F)) : (c • f : 𝓓^{n}(E, F)) = c • (f : E → F) :=
  rfl

@[simp]
lemma smul_apply {R} [Semiring R] [Module R F] [SMulCommClass ℝ R F] [ContinuousConstSMul R F]
    (c : R) (f : 𝓓^{n}(E, F)) (x : E) : (c • f) x = c • (f x) :=
  rfl

instance instNSMul : SMul ℕ 𝓓^{n}(E, F) :=
 ⟨fun c f ↦
    {
      toFun := c • f
      contDiff' := (f.contDiff').const_smul c
      compact_supp' := f.compact_supp.smul_left
    }
  ⟩

instance instZSMul : SMul ℤ 𝓓^{n}(E, F) :=
 ⟨fun c f ↦
    {
      toFun := c • f
      contDiff' := (f.contDiff').const_smul c
      compact_supp' := f.compact_supp.smul_left
    }
  ⟩

instance : AddCommGroup 𝓓^{n}(E, F) :=
  DFunLike.coe_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

variable (E F K n)

/-- Coercion as an additive homomorphism. -/
def coeHom : 𝓓^{n}(E, F) →+ E → F where
  toFun f := f
  map_zero' := coe_zero
  map_add' _ _ := rfl

variable {E F}

theorem coe_coeHom : (coeHom E F n : 𝓓^{n}(E, F) → E → F) = DFunLike.coe :=
  rfl

theorem coeHom_injective : Function.Injective (coeHom E F n) := by
  rw [coe_coeHom]
  exact DFunLike.coe_injective

end AddCommGroup

section Module

instance {R} [Semiring R] [Module R F] [SMulCommClass ℝ R F] [ContinuousConstSMul R F] :
    Module R 𝓓^{n}(E, F) :=
  (coeHom_injective n).module R (coeHom E F n) fun _ _ => rfl

end Module

variable (n : ℕ∞) (F)

/-- The natural inclusion `𝓓^{n}_{K}(E, F) → 𝓓^{n}(E, F)` as a linear map. -/
def ContDiffMapSupportedIn.toTestFunction (K : Compacts E) : 𝓓^{n}_{K}(E, F) →ₗ[𝕜] 𝓓^{n}(E, F)
    where
  toFun f := TestFunction.mk f (f.contDiff) (f.hasCompactSupport)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem ContDiffMapSupportedIn.toTestFunction_apply {K : Compacts E} (f : 𝓓^{n}_{K}(E, F)) (x : E) :
  (toTestFunction 𝕜 F n K f) x = f x := rfl

open ContDiffMapSupportedIn

section Topology

/-- The original topology on `𝓓^{n}(E, F)`, defined as the supremum over all compacts of the
topologies from each `𝓓^{n}_{K}(E, F)`. -/
noncomputable def originalTop : TopologicalSpace 𝓓^{n}(E, F) :=
  ⨆ (K : Compacts E), coinduced (toTestFunction 𝕜 F n K) (inferInstance)

variable (E)
noncomputable instance topologicalSpace : TopologicalSpace 𝓓^{n}(E, F) :=
  sInf {t : TopologicalSpace 𝓓^{n}(E, F)
       | originalTop ℝ F n ≤ t ∧ @LocallyConvexSpace ℝ 𝓓^{n}(E, F) _ _ _ _ t}

noncomputable instance : LocallyConvexSpace ℝ 𝓓^{n}(E, F) := by
  apply LocallyConvexSpace.sInf
  simp only [mem_setOf_eq, and_imp, imp_self, implies_true]

variable {E F n}

theorem continuous_toTestFunction (K : Compacts E) :
    Continuous (toTestFunction 𝕜 F n K) := by
  apply continuous_iff_coinduced_le.2
  have : originalTop 𝕜 F n ≤ TestFunction.topologicalSpace E F n := by
    exact le_sInf (by aesop)
  exact le_trans (le_sSup (by aesop)) this

protected theorem continuous_iff_continuous_comp {V : Type*} [AddCommMonoid V] [Module ℝ V]
    [t : TopologicalSpace V] [LocallyConvexSpace ℝ V] (f : 𝓓^{n}(E, F) →ₗ[ℝ] V) :
    Continuous f ↔
  ∀ K : Compacts E, Continuous (f ∘ toTestFunction 𝕜 F n K) := by
  rw [continuous_iff_le_induced]
  have : TestFunction.topologicalSpace E F n ≤ induced f t
        ↔ originalTop ℝ F n ≤ induced f t := by
      constructor <;> refine fun h ↦ ?_
      · refine le_trans (le_sInf (fun _ _ ↦ ?_)) h
        simp_all only [mem_setOf_eq]
      · refine sInf_le ?_
        simp only [mem_setOf_eq, LocallyConvexSpace.induced f, and_true, h]
  rw [this, originalTop, iSup_le_iff]
  simp_rw [← @coinduced_le_iff_le_induced _ _ f _ t,
    coinduced_compose, ← continuous_iff_coinduced_le]
  rfl

protected theorem continuous_from_bounded {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [LocallyConvexSpace ℝ V] (f : 𝓓^{n}(E, F) →ₗ[ℝ] V)
    (hb : ∀ K : Compacts E, ∃ k : ℕ, ∃ C : ℝ≥0, ∀ φ : 𝓓^{n}_{K}(E, F),
      ‖f (toTestFunction ℝ F n K φ)‖ ≤ C • (φ.seminorm' ℝ _ _ n K k)):
    Continuous f := by
    rw [TestFunction.continuous_iff_continuous_comp ℝ]
    intro K
    apply continuous_from_bounded (ContDiffMapSupportedIn.withSeminorms' ℝ E F n K)
              (norm_withSeminorms ℝ V) (f.comp (toTestFunction ℝ F n K))
    intro _
    obtain ⟨k, C, h⟩ := hb K
    refine ⟨{k}, C, le_def.mpr (fun φ ↦ ?_)⟩
    simp only [Seminorm.comp_apply, LinearMap.coe_comp, Function.comp_apply, coe_normSeminorm,
      Finset.sup_singleton, Seminorm.smul_apply]
    exact h φ

end Topology

variable (E)

@[simps]
noncomputable def toBoundedContinuousFunctionₗ : 𝓓^{n}(E, F) →ₗ[𝕜] E →ᵇ F  where
  toFun f := f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma to_bcf_comp_eq (K : Compacts E) :
  (toBoundedContinuousFunctionₗ 𝕜 E F n) ∘ (ContDiffMapSupportedIn.toTestFunction 𝕜 F n K)  =
    ContDiffMapSupportedIn.toBoundedContinuousFunctionₗ 𝕜 := by rfl

@[simps!]
noncomputable def toBoundedContinuousFunctionCLM : 𝓓^{n}(E, F) →L[𝕜] E →ᵇ F  :=
  { toLinearMap := toBoundedContinuousFunctionₗ 𝕜 E F n
    cont := show Continuous (toBoundedContinuousFunctionₗ ℝ E F n)
      by
        (
          rw [TestFunction.continuous_iff_continuous_comp ℝ (toBoundedContinuousFunctionₗ ℝ E F n)]
          intro K
          rw [to_bcf_comp_eq _ _]
          exact (ContDiffMapSupportedIn.toBoundedContinuousFunctionCLM 𝕜).continuous
        )
  }

theorem injective_toBoundedContinuousFunctionCLM :
    Function.Injective (toBoundedContinuousFunctionCLM 𝕜 E F n) := by
  intro f g
  simp [toBoundedContinuousFunctionCLM, toBoundedContinuousFunctionₗ]

theorem T25Space_TestFunction : T25Space 𝓓^{n}(E, F) :=
  T25Space.of_injective_continuous
    (injective_toBoundedContinuousFunctionCLM ℝ E F n)
    (toBoundedContinuousFunctionCLM ℝ E F n).continuous


namespace Measure

open MeasureTheory Module BoundedContinuousFunction

variable [MeasurableSpace E]
variable (μ : Measure E)

variable {E F}

noncomputable def testAgainst : 𝓓^{n}(E, F) → F := (∫ x, · x ∂μ)

@[simp]
lemma testAgainst_apply (f : 𝓓^{n}(E, F)) : testAgainst n μ f = (∫ x, f x ∂μ) := by
  rfl

variable [BorelSpace E] [IsFiniteMeasureOnCompacts μ]

lemma map_integrable (f : 𝓓^{n}(E, F)) : Integrable f μ  := by
  apply Continuous.integrable_of_hasCompactSupport (map_continuous f) (compact_supp f)

variable {K : Compacts E}

lemma map_integrable' (f : 𝓓^{n}_{K}(E, F)) : Integrable f μ  := by
  apply Continuous.integrable_of_hasCompactSupport (map_continuous f) (f.hasCompactSupport)

variable [SecondCountableTopology E] [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F]

noncomputable def testAgainstₗ : 𝓓^{n}(E, F) →ₗ[𝕜] F :=
  { toFun := testAgainst n μ
    map_add' := fun f g ↦ integral_add (Measure.map_integrable n μ f) (Measure.map_integrable n μ g)
    map_smul' := fun c f ↦ integral_smul c f}

variable [CompleteSpace F]

@[simps!]
noncomputable def testAgainstCLM : 𝓓^{n}(E, F) →L[𝕜] F where
  toLinearMap := (testAgainstₗ 𝕜 n μ : 𝓓^{n}(E, F) →ₗ[𝕜] F)
  cont := show Continuous (testAgainstₗ ℝ n μ) by
    (
      rw [TestFunction.continuous_iff_continuous_comp ℝ (testAgainstₗ ℝ n μ)]
      intro K
      have fin_μ : IsFiniteMeasure (μ.restrict K) := by
        have : Fact (μ K < ⊤) := fact_iff.mpr <| K.isCompact.measure_lt_top
        apply Restrict.isFiniteMeasure
      have : testAgainstₗ ℝ n μ ∘ (toTestFunction ℝ F n K)
          = (FiniteMeasure.testAgainstCLM (μ.restrict K) ℝ) ∘
            (ContDiffMapSupportedIn.toBoundedContinuousFunctionCLM 𝕜) := by
        ext f
        simp only [testAgainstₗ, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
          testAgainst_apply]
        simp only [FiniteMeasure.testAgainstCLM_apply,
          ContDiffMapSupportedIn.toBoundedContinuousFunctionCLM_apply_apply]
        have : ∫ (x : E) in (K : Set E)ᶜ, f x ∂μ = 0 := by
          refine setIntegral_eq_zero_of_forall_eq_zero f.zero_on_compl
        rw [← add_zero (∫ (x : E) in ↑K, f x ∂μ), ← this,
          integral_add_compl K.isCompact.measurableSet (map_integrable' n μ f)]
        congr
      rw [this]
      apply (FiniteMeasure.testAgainstCLM (μ.restrict K) 𝕜).continuous.comp
          (ContDiffMapSupportedIn.toBoundedContinuousFunctionCLM 𝕜).continuous
    )

end Measure

end TestFunction
