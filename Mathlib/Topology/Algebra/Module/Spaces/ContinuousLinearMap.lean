/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Yury Kudryashov
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.UniformConvergenceCLM
public import Mathlib.Topology.Algebra.Algebra.Equiv
public import Mathlib.Topology.Defs.Sequences
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.FastInstance
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Coherent

/-!
# Topology of bounded convergence on the space of continuous linear map

In this file, we endow `E →L[𝕜] F` with the "topology of bounded convergence",
or "topology of uniform convergence on bounded sets". This is declared as an instance.

A key feature of the topology of bounded convergence is that, in the normed setting, it coincides
with the operator norm topology.

Note that, more generally, we defined the "topology of `𝔖`-convergence" for any
`𝔖 : Set (Set E)` in `Mathlib.Topology.Algebra.Module.Spaces.UniformConvergenceCLM`.

Here is a list of type aliases for `E →L[𝕜] F` endowed with various topologies :
* `ContinuousLinearMap`: topology of bounded convergence
* `UniformConvergenceCLM`: topology of `𝔖`-convergence, for a general `𝔖 : Set (Set E)`
* `CompactConvergenceCLM`: topology of compact convergence
* `PointwiseConvergenceCLM`: topology of pointwise convergence, also called "weak-\* topology"
  or "strong-operator topology" depending on the context
* `ContinuousLinearMapWOT`: topology of weak pointwise convergence, also called "weak-operator
  topology"

## Main definitions

* `ContinuousLinearMap.topologicalSpace` is the topology of bounded convergence. This is
  declared as an instance.

## Main statements

* `ContinuousLinearMap.topologicalAddGroup` and
  `ContinuousLinearMap.continuousSMul` register these facts as instances for the special
  case of bounded convergence.

## References

* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## Tags

uniform convergence, bounded convergence
-/

@[expose] public section

open Bornology Filter Function Set Topology
open scoped UniformConvergence Uniformity

namespace ContinuousLinearMap

section BoundedConvergence

/-! ### Topology of bounded convergence  -/

variable {𝕜₁ 𝕜₂ 𝕜₃ : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂] [NormedField 𝕜₃] {σ : 𝕜₁ →+* 𝕜₂}
  {τ : 𝕜₂ →+* 𝕜₃} {ρ : 𝕜₁ →+* 𝕜₃} [RingHomCompTriple σ τ ρ] {E F G : Type*} [AddCommGroup E]
  [Module 𝕜₁ E] [AddCommGroup F] [Module 𝕜₂ F]
  [AddCommGroup G] [Module 𝕜₃ G] [TopologicalSpace E]

/-- The topology of bounded convergence on `E →L[𝕜] F`. This coincides with the topology induced by
the operator norm when `E` and `F` are normed spaces. -/
instance topologicalSpace [TopologicalSpace F] [IsTopologicalAddGroup F] :
    TopologicalSpace (E →SL[σ] F) :=
  fast_instance% UniformConvergenceCLM.instTopologicalSpace σ F { S | IsVonNBounded 𝕜₁ S }

instance topologicalAddGroup [TopologicalSpace F] [IsTopologicalAddGroup F] :
    IsTopologicalAddGroup (E →SL[σ] F) :=
  UniformConvergenceCLM.instIsTopologicalAddGroup σ F _

instance continuousSMul [RingHomSurjective σ] [RingHomIsometric σ] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousSMul 𝕜₂ F] : ContinuousSMul 𝕜₂ (E →SL[σ] F) :=
  UniformConvergenceCLM.continuousSMul σ F { S | IsVonNBounded 𝕜₁ S } fun _ hs => hs

instance uniformSpace [UniformSpace F] [IsUniformAddGroup F] : UniformSpace (E →SL[σ] F) :=
  fast_instance% UniformConvergenceCLM.instUniformSpace σ F { S | IsVonNBounded 𝕜₁ S }

instance isUniformAddGroup [UniformSpace F] [IsUniformAddGroup F] :
    IsUniformAddGroup (E →SL[σ] F) :=
  UniformConvergenceCLM.instIsUniformAddGroup σ F _

instance instContinuousEvalConst [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousSMul 𝕜₁ E] : ContinuousEvalConst (E →SL[σ] F) E F :=
  UniformConvergenceCLM.continuousEvalConst σ F _ Bornology.sUnion_isVonNBounded_eq_univ

instance instT2Space [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜₁ E]
    [T2Space F] : T2Space (E →SL[σ] F) :=
  UniformConvergenceCLM.t2Space σ F _ Bornology.sUnion_isVonNBounded_eq_univ

protected theorem hasBasis_nhds_zero_of_basis [TopologicalSpace F] [IsTopologicalAddGroup F]
    {ι : Type*} {p : ι → Prop} {b : ι → Set F} (h : (𝓝 0 : Filter F).HasBasis p b) :
    (𝓝 (0 : E →SL[σ] F)).HasBasis (fun Si : Set E × ι => IsVonNBounded 𝕜₁ Si.1 ∧ p Si.2)
      fun Si => { f : E →SL[σ] F | ∀ x ∈ Si.1, f x ∈ b Si.2 } :=
  UniformConvergenceCLM.hasBasis_nhds_zero_of_basis σ F { S | IsVonNBounded 𝕜₁ S }
    ⟨∅, isVonNBounded_empty 𝕜₁ E⟩
    (directedOn_of_sup_mem fun _ _ => IsVonNBounded.union) h

protected theorem hasBasis_nhds_zero [TopologicalSpace F] [IsTopologicalAddGroup F] :
    (𝓝 (0 : E →SL[σ] F)).HasBasis
      (fun SV : Set E × Set F => IsVonNBounded 𝕜₁ SV.1 ∧ SV.2 ∈ (𝓝 0 : Filter F))
      fun SV => { f : E →SL[σ] F | ∀ x ∈ SV.1, f x ∈ SV.2 } :=
  ContinuousLinearMap.hasBasis_nhds_zero_of_basis (𝓝 0).basis_sets

theorem isUniformEmbedding_toUniformOnFun [UniformSpace F] [IsUniformAddGroup F] :
    IsUniformEmbedding
      fun f : E →SL[σ] F ↦ UniformOnFun.ofFun {s | Bornology.IsVonNBounded 𝕜₁ s} f :=
  UniformConvergenceCLM.isUniformEmbedding_coeFn ..

instance uniformContinuousConstSMul
    {M : Type*} [Monoid M] [DistribMulAction M F] [SMulCommClass 𝕜₂ M F]
    [UniformSpace F] [IsUniformAddGroup F] [UniformContinuousConstSMul M F] :
    UniformContinuousConstSMul M (E →SL[σ] F) :=
  UniformConvergenceCLM.instUniformContinuousConstSMul σ F _ _

instance continuousConstSMul {M : Type*} [Monoid M] [DistribMulAction M F] [SMulCommClass 𝕜₂ M F]
    [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousConstSMul M F] :
    ContinuousConstSMul M (E →SL[σ] F) :=
  UniformConvergenceCLM.instContinuousConstSMul σ F _ _

protected theorem nhds_zero_eq_of_basis [TopologicalSpace F] [IsTopologicalAddGroup F]
    {ι : Type*} {p : ι → Prop} {b : ι → Set F} (h : (𝓝 0 : Filter F).HasBasis p b) :
    𝓝 (0 : E →SL[σ] F) =
      ⨅ (s : Set E) (_ : IsVonNBounded 𝕜₁ s) (i : ι) (_ : p i),
        𝓟 {f : E →SL[σ] F | MapsTo f s (b i)} :=
  UniformConvergenceCLM.nhds_zero_eq_of_basis _ _ _ h

protected theorem nhds_zero_eq [TopologicalSpace F] [IsTopologicalAddGroup F] :
    𝓝 (0 : E →SL[σ] F) =
      ⨅ (s : Set E) (_ : IsVonNBounded 𝕜₁ s) (U : Set F) (_ : U ∈ 𝓝 0),
        𝓟 {f : E →SL[σ] F | MapsTo f s U} :=
  UniformConvergenceCLM.nhds_zero_eq ..

/-- If `s` is a von Neumann bounded set and `U` is a neighbourhood of zero,
then sufficiently small continuous linear maps map `s` to `U`. -/
theorem eventually_nhds_zero_mapsTo [TopologicalSpace F] [IsTopologicalAddGroup F]
    {s : Set E} (hs : IsVonNBounded 𝕜₁ s) {U : Set F} (hu : U ∈ 𝓝 0) :
    ∀ᶠ f : E →SL[σ] F in 𝓝 0, MapsTo f s U :=
  UniformConvergenceCLM.eventually_nhds_zero_mapsTo _ hs hu

/-- If `S` is a von Neumann bounded set of continuous linear maps `f : E →SL[σ] F`
and `s` is a von Neumann bounded set in the domain,
then the set `{f x | (f ∈ S) (x ∈ s)}` is von Neumann bounded.

See also `isVonNBounded_iff` for an `Iff` version with stronger typeclass assumptions. -/
theorem isVonNBounded_image2_apply {R : Type*} [SeminormedRing R]
    [TopologicalSpace F] [IsTopologicalAddGroup F]
    [DistribMulAction R F] [ContinuousConstSMul R F] [SMulCommClass 𝕜₂ R F]
    {S : Set (E →SL[σ] F)} (hS : IsVonNBounded R S) {s : Set E} (hs : IsVonNBounded 𝕜₁ s) :
    IsVonNBounded R (Set.image2 (fun f x ↦ f x) S s) :=
  UniformConvergenceCLM.isVonNBounded_image2_apply hS hs

/-- A set `S` of continuous linear maps is von Neumann bounded
iff for any von Neumann bounded set `s`,
the set `{f x | (f ∈ S) (x ∈ s)}` is von Neumann bounded.

For the forward implication with weaker typeclass assumptions, see `isVonNBounded_image2_apply`. -/
theorem isVonNBounded_iff {R : Type*} [NormedDivisionRing R]
    [TopologicalSpace F] [IsTopologicalAddGroup F]
    [Module R F] [ContinuousConstSMul R F] [SMulCommClass 𝕜₂ R F]
    {S : Set (E →SL[σ] F)} :
    IsVonNBounded R S ↔
      ∀ s, IsVonNBounded 𝕜₁ s → IsVonNBounded R (Set.image2 (fun f x ↦ f x) S s) :=
  UniformConvergenceCLM.isVonNBounded_iff

theorem completeSpace [UniformSpace F] [IsUniformAddGroup F] [ContinuousSMul 𝕜₂ F] [CompleteSpace F]
    [ContinuousSMul 𝕜₁ E] (h : IsCoherentWith {s : Set E | IsVonNBounded 𝕜₁ s}) :
    CompleteSpace (E →SL[σ] F) :=
  UniformConvergenceCLM.completeSpace _ _ h sUnion_isVonNBounded_eq_univ

instance instCompleteSpace [IsTopologicalAddGroup E] [ContinuousSMul 𝕜₁ E] [SequentialSpace E]
    [UniformSpace F] [IsUniformAddGroup F] [ContinuousSMul 𝕜₂ F] [CompleteSpace F] :
    CompleteSpace (E →SL[σ] F) :=
  completeSpace <| .of_seq fun _ _ h ↦ (h.isVonNBounded_range 𝕜₁).insert _

theorem isUniformInducing_postcomp [UniformSpace F] [IsUniformAddGroup F]
    [UniformSpace G] [IsUniformAddGroup G] (f : F →SL[τ] G) (hf : IsUniformInducing f) :
    IsUniformInducing (f.comp : (E →SL[σ] F) → (E →SL[ρ] G)) :=
  UniformConvergenceCLM.isUniformInducing_postcomp _ f hf _

theorem isUniformEmbedding_postcomp [UniformSpace F] [IsUniformAddGroup F]
    [UniformSpace G] [IsUniformAddGroup G] (f : F →SL[τ] G) (hf : IsUniformEmbedding f) :
    IsUniformEmbedding (f.comp : (E →SL[σ] F) → (E →SL[ρ] G)) :=
  UniformConvergenceCLM.isUniformEmbedding_postcomp _ f hf _

variable [TopologicalSpace F] [TopologicalSpace G] (𝔖 : Set (Set E)) (𝔗 : Set (Set F))

theorem isInducing_postcomp [IsTopologicalAddGroup F] [IsTopologicalAddGroup G]
    (f : F →SL[τ] G) (hf : IsInducing f) :
    IsInducing (f.comp : (E →SL[σ] F) → (E →SL[ρ] G)) :=
  letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  haveI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  letI : UniformSpace G := IsTopologicalAddGroup.rightUniformSpace G
  haveI : IsUniformAddGroup G := isUniformAddGroup_of_addCommGroup
  (isUniformInducing_postcomp f <| AddMonoidHom.isUniformInducing_of_isInducing hf).isInducing

theorem isEmbedding_postcomp [IsTopologicalAddGroup F] [IsTopologicalAddGroup G]
    (f : F →SL[τ] G) (hf : IsEmbedding f) :
    IsEmbedding (f.comp : (E →SL[σ] F) → (E →SL[ρ] G)) :=
  .mk (isInducing_postcomp f hf.isInducing) fun _ _ ↦ f.cancel_left hf.injective

variable (G) in
/-- Pre-composition by a *fixed* continuous linear map as a continuous linear map.

Note that in non-normed space it is not always true that composition is continuous
in both variables, so we have to fix one of them. -/
@[simps! apply]
def precomp [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜₃ G] [RingHomSurjective σ]
    [RingHomIsometric σ] (L : E →SL[σ] F) : (F →SL[τ] G) →L[𝕜₃] E →SL[ρ] G where
  toFun f := f.comp L
  __ := precompUniformConvergenceCLM G { S | IsVonNBounded 𝕜₁ S } { S | IsVonNBounded 𝕜₂ S } L
    (fun _ hS ↦ hS.image L)

variable (E) in
/-- Post-composition by a *fixed* continuous linear map as a continuous linear map.

Note that in non-normed space it is not always true that composition is continuous
in both variables, so we have to fix one of them. -/
@[simps! apply]
def postcomp [IsTopologicalAddGroup F] [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜₃ G]
    [ContinuousConstSMul 𝕜₂ F] (L : F →SL[τ] G) : (E →SL[σ] F) →SL[τ] E →SL[ρ] G where
  toFun f := L.comp f
  __ := postcompUniformConvergenceCLM { S | IsVonNBounded 𝕜₁ S } L

variable (σ F) in
lemma toUniformConvergenceCLM_continuous [IsTopologicalAddGroup F]
    [ContinuousConstSMul 𝕜₂ F]
    (𝔖 : Set (Set E)) (h : 𝔖 ⊆ {S | IsVonNBounded 𝕜₁ S}) :
    Continuous (ContinuousLinearMap.toUniformConvergenceCLM σ F 𝔖) :=
  continuous_id_of_le <| UniformConvergenceCLM.topologicalSpace_mono _ _ h

/-- A bilinear map `B : E × F → G` which is (jointly) continuous is **hypocontinuous**:
in curried form, it defines a continuous linear map `E →L[𝕜] F →L[𝕜] G`.

In the normed setting, the converse is true, see `ContinuousLinearMap.continuous₂`.
In general, however, hypocontinuity is a strictly weaker condition than joint continuity. -/
theorem continuous_of_continuous_uncurry
    {𝕜₁ : Type*} [NontriviallyNormedField 𝕜₁] {σ : 𝕜₁ →+* 𝕜₂} [Module 𝕜₁ E]
    {τ : 𝕜₃ →+* 𝕜₂} [RingHomSurjective τ]
    [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜₃ G]
    [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜₂ F]
    (B : G →ₛₗ[τ] (E →SL[σ] F))
    (hB : Continuous (fun p : G × E ↦ B p.1 p.2)) :
    Continuous B :=
  UniformConvergenceCLM.continuous_of_continuous_uncurry (fun _ ↦ id) B hB

end BoundedConvergence

section BilinearMaps
variable {R 𝕜 𝕜₂ 𝕜₃ : Type*}
variable {E F G : Type*}

/-!
We prove some computation rules for continuous (semi-)bilinear maps in their first argument.
If `f` is a continuous bilinear map, to use the corresponding rules for the second argument, use
`(f _).map_add` and similar.
-/

section AddCommMonoid
variable
  [Semiring R] [NormedField 𝕜₂] [NormedField 𝕜₃]
  [AddCommMonoid E] [Module R E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜₂ F] [TopologicalSpace F]
  [AddCommGroup G] [Module 𝕜₃ G]
  [TopologicalSpace G] [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜₃ G]
  {σ₁₃ : R →+* 𝕜₃} {σ₂₃ : 𝕜₂ →+* 𝕜₃}

theorem map_add₂ (f : E →SL[σ₁₃] F →SL[σ₂₃] G) (x x' : E) (y : F) :
    f (x + x') y = f x y + f x' y := by rw [f.map_add, add_apply]

theorem map_zero₂ (f : E →SL[σ₁₃] F →SL[σ₂₃] G) (y : F) : f 0 y = 0 := by
  rw [f.map_zero, zero_apply]

theorem map_smulₛₗ₂ (f : E →SL[σ₁₃] F →SL[σ₂₃] G) (c : R) (x : E) (y : F) :
    f (c • x) y = σ₁₃ c • f x y := by rw [f.map_smulₛₗ, smul_apply]

/-- Send a continuous sesquilinear map to an abstract sesquilinear map (forgetting continuity). -/
def toLinearMap₁₂ (L : E →SL[σ₁₃] F →SL[σ₂₃] G) : E →ₛₗ[σ₁₃] F →ₛₗ[σ₂₃] G :=
  (coeLMₛₗ σ₂₃).comp L.toLinearMap

@[simp] lemma toLinearMap₁₂_apply (L : E →SL[σ₁₃] F →SL[σ₂₃] G) (v : E) (w : F) :
    L.toLinearMap₁₂ v w = L v w := rfl

lemma toLinearMap₁₂_injective :
    (toLinearMap₁₂ (E := E) (F := F) (G := G) (σ₁₃ := σ₁₃) (σ₂₃ := σ₂₃)).Injective := by
  simp [Function.Injective, LinearMap.ext_iff, ← ContinuousLinearMap.ext_iff]

lemma toLinearMap₁₂_inj (L₁ L₂ : E →SL[σ₁₃] F →SL[σ₂₃] G) :
    L₁.toLinearMap₁₂ = L₂.toLinearMap₁₂ ↔ L₁ = L₂ :=
  toLinearMap₁₂_injective.eq_iff

end AddCommMonoid

section Nonsemilinear
variable
  [NormedField 𝕜₂] [NormedField 𝕜₃]
  [AddCommMonoid E] [Module 𝕜₃ E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜₂ F] [TopologicalSpace F]
  [AddCommGroup G] [Module 𝕜₃ G]
  [TopologicalSpace G] [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜₃ G]
  {σ₂₃ : 𝕜₂ →+* 𝕜₃}

theorem map_smul₂ (f : E →L[𝕜₃] F →SL[σ₂₃] G) (c : 𝕜₃) (x : E) (y : F) :
    f (c • x) y = c • f x y := by
  rw [f.map_smul, smul_apply]

end Nonsemilinear

section AddCommGroup
variable
  [Semiring R] [NormedField 𝕜₂] [NormedField 𝕜₃]
  [AddCommGroup E] [Module R E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜₂ F] [TopologicalSpace F]
  [AddCommGroup G] [Module 𝕜₃ G]
  [TopologicalSpace G] [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜₃ G]
  {σ₁₃ : R →+* 𝕜₃} {σ₂₃ : 𝕜₂ →+* 𝕜₃}

theorem map_sub₂ (f : E →SL[σ₁₃] F →SL[σ₂₃] G) (x x' : E) (y : F) :
    f (x - x') y = f x y - f x' y := by rw [map_sub, sub_apply]

theorem map_neg₂ (f : E →SL[σ₁₃] F →SL[σ₂₃] G) (x : E) (y : F) : f (-x) y = -f x y := by
  rw [map_neg, neg_apply]

end AddCommGroup

section BilinForm
variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]

/-- Send a continuous bilinear form to an abstract bilinear form (forgetting continuity). -/
def toBilinForm (L : E →L[𝕜] E →L[𝕜] 𝕜) : LinearMap.BilinForm 𝕜 E := L.toLinearMap₁₂

@[simp] lemma toBilinForm_apply (L : E →L[𝕜] E →L[𝕜] 𝕜) (v : E) (w : E) :
    L.toBilinForm v w = L v w := rfl

lemma toBilinForm_injective : (toBilinForm (𝕜 := 𝕜) (E := E)).Injective :=
  toLinearMap₁₂_injective

lemma toBilinForm_inj (L₁ L₂ : E →L[𝕜] E →L[𝕜] 𝕜) :
    L₁.toBilinForm = L₂.toBilinForm ↔ L₁ = L₂ :=
  toBilinForm_injective.eq_iff

end BilinForm

end BilinearMaps

section RestrictScalars

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E] [ContinuousSMul 𝕜 E]
  {F : Type*} [AddCommGroup F]

section UniformSpace

variable [UniformSpace F] [IsUniformAddGroup F] [Module 𝕜 F]
  (𝕜' : Type*) [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜' 𝕜]
  [Module 𝕜' E] [IsScalarTower 𝕜' 𝕜 E] [Module 𝕜' F] [IsScalarTower 𝕜' 𝕜 F]

set_option backward.isDefEq.respectTransparency false in
theorem isUniformEmbedding_restrictScalars :
    IsUniformEmbedding (restrictScalars 𝕜' : (E →L[𝕜] F) → (E →L[𝕜'] F)) := by
  rw [← isUniformEmbedding_toUniformOnFun.of_comp_iff]
  convert isUniformEmbedding_toUniformOnFun using 4 with s
  exact ⟨fun h ↦ h.extend_scalars _, fun h ↦ h.restrict_scalars _⟩

theorem uniformContinuous_restrictScalars :
    UniformContinuous (restrictScalars 𝕜' : (E →L[𝕜] F) → (E →L[𝕜'] F)) :=
  (isUniformEmbedding_restrictScalars 𝕜').uniformContinuous

end UniformSpace

variable [TopologicalSpace F] [IsTopologicalAddGroup F] [Module 𝕜 F]
  (𝕜' : Type*) [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜' 𝕜]
  [Module 𝕜' E] [IsScalarTower 𝕜' 𝕜 E] [Module 𝕜' F] [IsScalarTower 𝕜' 𝕜 F]

theorem isEmbedding_restrictScalars :
    IsEmbedding (restrictScalars 𝕜' : (E →L[𝕜] F) → (E →L[𝕜'] F)) :=
  letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  haveI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  (isUniformEmbedding_restrictScalars _).isEmbedding

@[continuity, fun_prop]
theorem continuous_restrictScalars :
    Continuous (restrictScalars 𝕜' : (E →L[𝕜] F) → (E →L[𝕜'] F)) :=
  (isEmbedding_restrictScalars _).continuous

variable (𝕜 E F)
variable (𝕜'' : Type*) [Ring 𝕜'']
  [Module 𝕜'' F] [ContinuousConstSMul 𝕜'' F] [SMulCommClass 𝕜 𝕜'' F] [SMulCommClass 𝕜' 𝕜'' F]

/-- `ContinuousLinearMap.restrictScalars` as a `ContinuousLinearMap`. -/
def restrictScalarsL : (E →L[𝕜] F) →L[𝕜''] E →L[𝕜'] F :=
  .mk <| restrictScalarsₗ 𝕜 E F 𝕜' 𝕜''

variable {𝕜 E F 𝕜' 𝕜''}

@[simp]
theorem coe_restrictScalarsL : (restrictScalarsL 𝕜 E F 𝕜' 𝕜'' : (E →L[𝕜] F) →ₗ[𝕜''] E →L[𝕜'] F) =
    restrictScalarsₗ 𝕜 E F 𝕜' 𝕜'' :=
  rfl

@[simp]
theorem coe_restrict_scalarsL' : ⇑(restrictScalarsL 𝕜 E F 𝕜' 𝕜'') = restrictScalars 𝕜' :=
  rfl

end RestrictScalars

section Prod

variable {𝕜 E F G : Type*} (S : Type*) [NormedField 𝕜] [Semiring S]
  [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F]
  [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousConstSMul 𝕜 F]
  [AddCommGroup G] [Module 𝕜 G]
  [TopologicalSpace G] [IsTopologicalAddGroup G] [ContinuousConstSMul 𝕜 G]
  [Module S G] [SMulCommClass 𝕜 S G] [ContinuousConstSMul S G]

/-- `ContinuousLinearMap.coprod` as a `ContinuousLinearEquiv`. -/
@[simps!]
def coprodEquivL : ((E →L[𝕜] G) × (F →L[𝕜] G)) ≃L[S] (E × F →L[𝕜] G) where
  __ := coprodEquiv
  continuous_toFun :=
    (((fst 𝕜 E F).precomp G).coprod ((snd 𝕜 E F).precomp G)).continuous
  continuous_invFun :=
    (((inl 𝕜 E F).precomp G).prod ((inr 𝕜 E F).precomp G)).continuous

variable [Module S F] [SMulCommClass 𝕜 S F] [ContinuousConstSMul S F]

/-- `ContinuousLinearMap.prod` as a `ContinuousLinearEquiv`. -/
@[simps! apply]
def prodL : ((E →L[𝕜] F) × (E →L[𝕜] G)) ≃L[S] (E →L[𝕜] F × G) where
  __ := prodₗ S
  continuous_toFun := by
    change Continuous fun x => .id 𝕜 _ ∘L prodₗ S x
    simp_rw [← coprod_inl_inr]
    exact (((inl 𝕜 F G).postcomp E).coprod ((inr 𝕜 F G).postcomp E)).continuous
  continuous_invFun :=
    (((fst 𝕜 F G).postcomp E).prod ((snd 𝕜 F G).postcomp E)).continuous

end Prod

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

/-- `ContinuousLinearMap.toSpanSingleton` as a continuous linear equivalence. -/
@[simps!]
def toSpanSingletonCLE : E ≃L[𝕜] (𝕜 →L[𝕜] E) where
  toLinearEquiv := toSpanSingletonLE ..
  continuous_toFun := continuous_of_continuous_uncurry _ <|
    continuous_snd.smul continuous_fst
  continuous_invFun := continuous_eval_const 1

end ContinuousLinearMap

open ContinuousLinearMap

namespace ContinuousLinearEquiv

/-! ### Continuous linear equivalences -/

section Semilinear

variable {𝕜 : Type*} {𝕜₂ : Type*} {𝕜₃ : Type*} {𝕜₄ : Type*} {E : Type*} {F : Type*}
  {G : Type*} {H : Type*} [AddCommGroup E] [AddCommGroup F] [AddCommGroup G] [AddCommGroup H]
  [NormedField 𝕜] [NormedField 𝕜₂] [NormedField 𝕜₃] [NormedField 𝕜₄]
  [Module 𝕜 E] [Module 𝕜₂ F] [Module 𝕜₃ G] [Module 𝕜₄ H]
  [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalAddGroup G] [IsTopologicalAddGroup H] [ContinuousConstSMul 𝕜₃ G]
  [ContinuousConstSMul 𝕜₄ H] {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₁ : 𝕜₂ →+* 𝕜} {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₁₃ : 𝕜 →+* 𝕜₃}
  {σ₃₄ : 𝕜₃ →+* 𝕜₄} {σ₄₃ : 𝕜₄ →+* 𝕜₃} {σ₂₄ : 𝕜₂ →+* 𝕜₄} {σ₁₄ : 𝕜 →+* 𝕜₄} [RingHomInvPair σ₁₂ σ₂₁]
  [RingHomInvPair σ₂₁ σ₁₂] [RingHomInvPair σ₃₄ σ₄₃] [RingHomInvPair σ₄₃ σ₃₄]
  [RingHomCompTriple σ₂₁ σ₁₄ σ₂₄] [RingHomCompTriple σ₂₄ σ₄₃ σ₂₃] [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
  [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄] [RingHomCompTriple σ₂₃ σ₃₄ σ₂₄] [RingHomCompTriple σ₁₂ σ₂₄ σ₁₄]
  [RingHomIsometric σ₁₂] [RingHomIsometric σ₂₁]

/-- A pair of continuous (semi)linear equivalences generates a (semi)linear equivalence between the
spaces of continuous (semi)linear maps. -/
@[simps apply symm_apply toLinearEquiv_apply toLinearEquiv_symm_apply]
def arrowCongrSL (e₁₂ : E ≃SL[σ₁₂] F) (e₄₃ : H ≃SL[σ₄₃] G) :
    (E →SL[σ₁₄] H) ≃SL[σ₄₃] F →SL[σ₂₃] G :=
{ e₁₂.arrowCongrEquiv e₄₃ with
    -- given explicitly to help `simps`
    toFun := fun L => (e₄₃ : H →SL[σ₄₃] G).comp (L.comp (e₁₂.symm : F →SL[σ₂₁] E))
    -- given explicitly to help `simps`
    invFun := fun L => (e₄₃.symm : G →SL[σ₃₄] H).comp (L.comp (e₁₂ : E →SL[σ₁₂] F))
    map_add' := fun f g => by simp only [add_comp, comp_add]
    map_smul' := fun t f => by simp only [smul_comp, comp_smulₛₗ]
    continuous_toFun := ((postcomp F e₄₃.toContinuousLinearMap).comp
      (precomp H e₁₂.symm.toContinuousLinearMap)).continuous
    continuous_invFun := ((precomp H e₁₂.toContinuousLinearMap).comp
      (postcomp F e₄₃.symm.toContinuousLinearMap)).continuous }

end Semilinear

section Linear

variable {𝕜 : Type*} {E : Type*} {F : Type*} {G : Type*} {H : Type*} [AddCommGroup E]
  [AddCommGroup F] [AddCommGroup G] [AddCommGroup H] [NormedField 𝕜] [Module 𝕜 E]
  [Module 𝕜 F] [Module 𝕜 G] [Module 𝕜 H] [TopologicalSpace E] [TopologicalSpace F]
  [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalAddGroup G] [IsTopologicalAddGroup H]
  [ContinuousConstSMul 𝕜 G] [ContinuousConstSMul 𝕜 H]

/-- A pair of continuous linear equivalences generates a continuous linear equivalence between
the spaces of continuous linear maps. -/
def arrowCongr (e₁ : E ≃L[𝕜] F) (e₂ : H ≃L[𝕜] G) : (E →L[𝕜] H) ≃L[𝕜] F →L[𝕜] G :=
  e₁.arrowCongrSL e₂

@[simp] lemma arrowCongr_apply (e₁ : E ≃L[𝕜] F) (e₂ : H ≃L[𝕜] G) (f : E →L[𝕜] H) (x : F) :
    e₁.arrowCongr e₂ f x = e₂ (f (e₁.symm x)) := rfl

@[simp] lemma arrowCongr_symm (e₁ : E ≃L[𝕜] F) (e₂ : H ≃L[𝕜] G) :
    (e₁.arrowCongr e₂).symm = e₁.symm.arrowCongr e₂.symm := rfl

/-- A continuous linear equivalence of two spaces induces a continuous equivalence of algebras of
their endomorphisms. -/
def conjContinuousAlgEquiv (e : G ≃L[𝕜] H) : (G →L[𝕜] G) ≃A[𝕜] (H →L[𝕜] H) :=
  { e.arrowCongr e with
    map_mul' _ _ := by ext; simp
    commutes' _ := by ext; simp }

@[simp] theorem conjContinuousAlgEquiv_apply_apply (e : G ≃L[𝕜] H) (f : G →L[𝕜] G) (x : H) :
    e.conjContinuousAlgEquiv f x = e (f (e.symm x)) := rfl

theorem symm_conjContinuousAlgEquiv_apply_apply (e : G ≃L[𝕜] H) (f : H →L[𝕜] H) (x : G) :
    e.conjContinuousAlgEquiv.symm f x = e.symm (f (e x)) := rfl

theorem conjContinuousAlgEquiv_apply (e : G ≃L[𝕜] H) (f : G →L[𝕜] G) :
    e.conjContinuousAlgEquiv f = e ∘L f ∘L e.symm := rfl

@[simp] theorem symm_conjContinuousAlgEquiv (e : G ≃L[𝕜] H) :
    e.conjContinuousAlgEquiv.symm = e.symm.conjContinuousAlgEquiv := rfl

@[simp] theorem conjContinuousAlgEquiv_refl : conjContinuousAlgEquiv (.refl 𝕜 G) = .refl 𝕜 _ := rfl

theorem conjContinuousAlgEquiv_trans [IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E]
    (e : E ≃L[𝕜] G) (f : G ≃L[𝕜] H) :
    (e.trans f).conjContinuousAlgEquiv = e.conjContinuousAlgEquiv.trans f.conjContinuousAlgEquiv :=
  rfl

end Linear

end ContinuousLinearEquiv
