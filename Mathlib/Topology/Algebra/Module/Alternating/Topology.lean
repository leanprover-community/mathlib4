/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.Algebra.Module.Multilinear.Topology
public import Mathlib.Topology.Algebra.Module.Alternating.Basic

/-!
# Topology on continuous alternating maps

In this file we define `UniformSpace` and `TopologicalSpace` structures
on the space of continuous alternating maps between topological vector spaces.

The structures are induced by those on `ContinuousMultilinearMap`s,
and most of the lemmas follow from the corresponding lemmas about `ContinuousMultilinearMap`s.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

open Bornology Function Set Topology
open scoped UniformConvergence Filter

namespace ContinuousAlternatingMap

variable {𝕜 E F ι : Type*} [NormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [AddCommGroup F] [Module 𝕜 F]

section IsClosedRange

variable [TopologicalSpace F] [IsTopologicalAddGroup F]

instance instTopologicalSpace : TopologicalSpace (E [⋀^ι]→L[𝕜] F) :=
  .induced toContinuousMultilinearMap inferInstance

lemma isClosed_range_toContinuousMultilinearMap [ContinuousSMul 𝕜 E] [T2Space F] :
    IsClosed (Set.range (toContinuousMultilinearMap : (E [⋀^ι]→L[𝕜] F) →
      ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F)) := by
  simp only [range_toContinuousMultilinearMap, setOf_forall]
  repeat refine isClosed_iInter fun _ ↦ ?_
  exact isClosed_singleton.preimage (continuous_eval_const _)

end IsClosedRange

section IsUniformAddGroup

variable [UniformSpace F] [IsUniformAddGroup F]

instance instUniformSpace : UniformSpace (E [⋀^ι]→L[𝕜] F) :=
  .comap toContinuousMultilinearMap inferInstance

lemma isUniformEmbedding_toContinuousMultilinearMap :
    IsUniformEmbedding (toContinuousMultilinearMap : (E [⋀^ι]→L[𝕜] F) → _) where
  injective := toContinuousMultilinearMap_injective
  comap_uniformity := rfl

lemma uniformContinuous_toContinuousMultilinearMap :
    UniformContinuous (toContinuousMultilinearMap : (E [⋀^ι]→L[𝕜] F) → _) :=
  isUniformEmbedding_toContinuousMultilinearMap.uniformContinuous

theorem uniformContinuous_coe_fun [ContinuousSMul 𝕜 E] :
    UniformContinuous (DFunLike.coe : (E [⋀^ι]→L[𝕜] F) → (ι → E) → F) :=
  ContinuousMultilinearMap.uniformContinuous_coe_fun.comp
    uniformContinuous_toContinuousMultilinearMap

theorem uniformContinuous_eval_const [ContinuousSMul 𝕜 E] (x : ι → E) :
    UniformContinuous fun f : E [⋀^ι]→L[𝕜] F ↦ f x :=
  uniformContinuous_pi.1 uniformContinuous_coe_fun x

instance instIsUniformAddGroup : IsUniformAddGroup (E [⋀^ι]→L[𝕜] F) :=
  isUniformEmbedding_toContinuousMultilinearMap.isUniformAddGroup
    (toContinuousMultilinearMapLinear (R := ℕ))

instance instUniformContinuousConstSMul {M : Type*}
    [Monoid M] [DistribMulAction M F] [SMulCommClass 𝕜 M F] [ContinuousConstSMul M F] :
    UniformContinuousConstSMul M (E [⋀^ι]→L[𝕜] F) :=
  isUniformEmbedding_toContinuousMultilinearMap.uniformContinuousConstSMul fun _ _ ↦ rfl

theorem isUniformInducing_postcomp {G : Type*} [AddCommGroup G] [UniformSpace G]
    [IsUniformAddGroup G] [Module 𝕜 G] (g : F →L[𝕜] G) (hg : IsUniformInducing g) :
    IsUniformInducing (g.compContinuousAlternatingMap : (E [⋀^ι]→L[𝕜] F) → (E [⋀^ι]→L[𝕜] G)) := by
  rw [← isUniformEmbedding_toContinuousMultilinearMap.1.of_comp_iff]
  exact (ContinuousMultilinearMap.isUniformInducing_postcomp g hg).comp
    isUniformEmbedding_toContinuousMultilinearMap.1

section CompleteSpace

variable [ContinuousSMul 𝕜 E] [ContinuousConstSMul 𝕜 F] [CompleteSpace F]

open UniformOnFun in
theorem completeSpace (h : IsCoherentWith {s : Set (ι → E) | IsVonNBounded 𝕜 s}) :
    CompleteSpace (E [⋀^ι]→L[𝕜] F) := by
  wlog hF : T2Space F generalizing F
  · rw [(isUniformInducing_postcomp (SeparationQuotient.mkCLM _ _)
      SeparationQuotient.isUniformInducing_mk).completeSpace_congr]
    · exact this inferInstance
    · intro f
      use (SeparationQuotient.outCLM _ _).compContinuousAlternatingMap f
      ext
      simp
  have := ContinuousMultilinearMap.completeSpace (F := F) h
  rw [completeSpace_iff_isComplete_range
    isUniformEmbedding_toContinuousMultilinearMap.isUniformInducing]
  apply isClosed_range_toContinuousMultilinearMap.isComplete

instance instCompleteSpace [IsTopologicalAddGroup E] [SequentialSpace (ι → E)] :
    CompleteSpace (E [⋀^ι]→L[𝕜] F) :=
  completeSpace <| .of_seq fun _u x hux ↦ (hux.isVonNBounded_range 𝕜).insert x

end CompleteSpace

section RestrictScalars

variable (𝕜' : Type*) [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜' 𝕜]
  [Module 𝕜' E] [IsScalarTower 𝕜' 𝕜 E] [Module 𝕜' F] [IsScalarTower 𝕜' 𝕜 F] [ContinuousSMul 𝕜 E]

theorem isUniformEmbedding_restrictScalars :
    IsUniformEmbedding (restrictScalars 𝕜' : E [⋀^ι]→L[𝕜] F → E [⋀^ι]→L[𝕜'] F) := by
  rw [← isUniformEmbedding_toContinuousMultilinearMap.of_comp_iff]
  exact (ContinuousMultilinearMap.isUniformEmbedding_restrictScalars 𝕜').comp
    isUniformEmbedding_toContinuousMultilinearMap

theorem uniformContinuous_restrictScalars :
    UniformContinuous (restrictScalars 𝕜' : E [⋀^ι]→L[𝕜] F → E [⋀^ι]→L[𝕜'] F) :=
  (isUniformEmbedding_restrictScalars 𝕜').uniformContinuous

end RestrictScalars

end IsUniformAddGroup

variable [TopologicalSpace F] [IsTopologicalAddGroup F]

lemma isEmbedding_toContinuousMultilinearMap :
    IsEmbedding (toContinuousMultilinearMap : (E [⋀^ι]→L[𝕜] F → _)) :=
  letI := IsTopologicalAddGroup.rightUniformSpace F
  haveI := isUniformAddGroup_of_addCommGroup (G := F)
  isUniformEmbedding_toContinuousMultilinearMap.isEmbedding

instance instIsTopologicalAddGroup : IsTopologicalAddGroup (E [⋀^ι]→L[𝕜] F) :=
  isEmbedding_toContinuousMultilinearMap.topologicalAddGroup
    (toContinuousMultilinearMapLinear (R := ℕ))

@[continuity, fun_prop]
lemma continuous_toContinuousMultilinearMap :
    Continuous (toContinuousMultilinearMap : (E [⋀^ι]→L[𝕜] F → _)) :=
  isEmbedding_toContinuousMultilinearMap.continuous

instance instContinuousConstSMul
    {M : Type*} [Monoid M] [DistribMulAction M F] [SMulCommClass 𝕜 M F] [ContinuousConstSMul M F] :
    ContinuousConstSMul M (E [⋀^ι]→L[𝕜] F) :=
  isEmbedding_toContinuousMultilinearMap.continuousConstSMul id rfl

instance instContinuousSMul [ContinuousSMul 𝕜 F] : ContinuousSMul 𝕜 (E [⋀^ι]→L[𝕜] F) :=
  isEmbedding_toContinuousMultilinearMap.continuousSMul continuous_id rfl

theorem hasBasis_nhds_zero_of_basis {ι' : Type*} {p : ι' → Prop} {b : ι' → Set F}
    (h : (𝓝 (0 : F)).HasBasis p b) :
    (𝓝 (0 : E [⋀^ι]→L[𝕜] F)).HasBasis
      (fun Si : Set (ι → E) × ι' => IsVonNBounded 𝕜 Si.1 ∧ p Si.2)
      fun Si => { f | MapsTo f Si.1 (b Si.2) } := by
  rw [nhds_induced]
  exact (ContinuousMultilinearMap.hasBasis_nhds_zero_of_basis h).comap _

theorem hasBasis_nhds_zero :
    (𝓝 (0 : E [⋀^ι]→L[𝕜] F)).HasBasis
      (fun SV : Set (ι → E) × Set F => IsVonNBounded 𝕜 SV.1 ∧ SV.2 ∈ 𝓝 0)
      fun SV => { f | MapsTo f SV.1 SV.2 } :=
  hasBasis_nhds_zero_of_basis (Filter.basis_sets _)

/-- The inclusion of *alternating* continuous multilinear maps into continuous multilinear maps
as a continuous linear map. -/
@[simps! -fullyApplied]
def toContinuousMultilinearMapCLM
    (R : Type*) [Semiring R] [Module R F] [ContinuousConstSMul R F] [SMulCommClass 𝕜 R F] :
    E [⋀^ι]→L[𝕜] F →L[R] ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F :=
  ⟨toContinuousMultilinearMapLinear, continuous_induced_dom⟩

section ContinuousSMul

variable [ContinuousSMul 𝕜 E]

lemma isClosedEmbedding_toContinuousMultilinearMap [T2Space F] :
    IsClosedEmbedding (toContinuousMultilinearMap :
      (E [⋀^ι]→L[𝕜] F) → ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F) :=
  ⟨isEmbedding_toContinuousMultilinearMap, isClosed_range_toContinuousMultilinearMap⟩

instance instContinuousEvalConst : ContinuousEvalConst (E [⋀^ι]→L[𝕜] F) (ι → E) F :=
  .of_continuous_forget continuous_toContinuousMultilinearMap

instance instT2Space [T2Space F] : T2Space (E [⋀^ι]→L[𝕜] F) :=
  .of_injective_continuous DFunLike.coe_injective continuous_coeFun

instance instT3Space [T2Space F] : T3Space (E [⋀^ι]→L[𝕜] F) :=
  inferInstance

section RestrictScalars

variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜' 𝕜]
  [Module 𝕜' E] [IsScalarTower 𝕜' 𝕜 E] [Module 𝕜' F] [IsScalarTower 𝕜' 𝕜 F]

theorem isEmbedding_restrictScalars :
    IsEmbedding (restrictScalars 𝕜' : E [⋀^ι]→L[𝕜] F → E [⋀^ι]→L[𝕜'] F) :=
  letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  haveI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  (isUniformEmbedding_restrictScalars _).isEmbedding

@[continuity, fun_prop]
theorem continuous_restrictScalars :
    Continuous (restrictScalars 𝕜' : E [⋀^ι]→L[𝕜] F → E [⋀^ι]→L[𝕜'] F) :=
  isEmbedding_restrictScalars.continuous

variable (𝕜') in
/-- `ContinuousMultilinearMap.restrictScalars` as a `ContinuousLinearMap`. -/
@[simps -fullyApplied apply]
def restrictScalarsCLM [ContinuousConstSMul 𝕜' F] :
    E [⋀^ι]→L[𝕜] F →L[𝕜'] E [⋀^ι]→L[𝕜'] F where
  toFun := restrictScalars 𝕜'
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end RestrictScalars

end ContinuousSMul

section ContinuousConstSMul

variable {G : Type*} [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G] [ContinuousConstSMul 𝕜 F]

/-- Given a continuous linear map taking values in the space of continuous multilinear maps
such that all of its values are alternating maps,
lift it to a continuous linear map taking values in the space of continuous alternating maps. -/
def liftCLM (f : G →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F)
    (hf : ∀ x v i j, v i = v j → i ≠ j → f x v = 0) : G →L[𝕜] (E [⋀^ι]→L[𝕜] F) where
  toFun x := ⟨f x, hf x⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  cont := continuous_induced_rng.mpr (map_continuous f)

@[simp]
lemma liftCLM_apply (f : G →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F)
    (hf : ∀ x v i j, v i = v j → i ≠ j → f x v = 0) (x : G) (v : ι → E) :
    liftCLM f hf x v = f x v :=
  rfl

section CompContinuousLinearMap

variable {E' : Type*} [AddCommGroup E'] [Module 𝕜 E'] [TopologicalSpace E']
    [ContinuousConstSMul 𝕜 F]

/-- Composition of a continuous alternating map and a continuous linear map
as a bundled continuous linear map.

Note that for general topological vector spaces,
this function does not need to be continuous in `f`. -/
@[simps! apply]
def compContinuousLinearMapCLM (f : E →L[𝕜] E') : (E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F) where
  toLinearMap := compContinuousLinearMapₗ f
  cont := by
    rw [isEmbedding_toContinuousMultilinearMap.continuous_iff]
    exact (map_continuous <| ContinuousMultilinearMap.compContinuousLinearMapL fun _ ↦ f).comp
      continuous_toContinuousMultilinearMap

end CompContinuousLinearMap

variable [ContinuousSMul 𝕜 E]
variable (𝕜 E F)

/-- The application of a multilinear map as a `ContinuousLinearMap`. -/
def apply (m : ι → E) : E [⋀^ι]→L[𝕜] F →L[𝕜] F where
  toFun c := c m
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_eval_const m

variable {𝕜 E F}

@[simp]
lemma apply_apply {m : ι → E} {c : E [⋀^ι]→L[𝕜] F} : apply 𝕜 E F m c = c m := rfl

end ContinuousConstSMul

variable [ContinuousSMul 𝕜 E] {α : Type*} {p : α → E [⋀^ι]→L[𝕜] F}

theorem hasSum_eval {q : E [⋀^ι]→L[𝕜] F} (h : HasSum p q) (m : ι → E) :
    HasSum (fun a => p a m) (q m) :=
  h.map (applyAddHom m) (continuous_eval_const m)

theorem tsum_eval [T2Space F] (hp : Summable p) (m : ι → E) : (∑' a, p a) m = ∑' a, p a m :=
  (hasSum_eval hp.hasSum m).tsum_eq.symm

end ContinuousAlternatingMap

namespace ContinuousLinearMap
variable (𝕜 E F G ι : Type*) [NormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [ContinuousSMul 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousConstSMul 𝕜 F]
  [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [ContinuousConstSMul 𝕜 G]

/-- `ContinuousLinearMap.compContinuousAlternatingMap` as a bundled continuous bilinear map.

Given a continuous linear map `g : F →L[𝕜] G` and a continuous alternating map `f : E [⋀^ι]→L[𝕜] F`,
it returns the continuous alternating map `g ∘ f`.
This function is continuous in `f` (for each `g`)
and in `g` (as a function taking values in continuous linear maps).
Note that for a general topological vector space,
the map is not guaranteed to be continuous in `(g, f)`.
-/
@[simps! apply_apply]
def compContinuousAlternatingMapCLM :
    (F →L[𝕜] G) →L[𝕜] (E [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] G) where
  toFun g :=
    { toLinearMap := compContinuousAlternatingMapₗ _ _ _ _ g
      cont := by
        rw [ContinuousAlternatingMap.isEmbedding_toContinuousMultilinearMap.continuous_iff]
        exact (map_continuous <| compContinuousMultilinearMapL 𝕜 (fun _ : ι ↦ E) F G g).comp
          ContinuousAlternatingMap.continuous_toContinuousMultilinearMap }
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  cont := by
    rw [ContinuousLinearMap.isEmbedding_postcomp
      (ContinuousAlternatingMap.toContinuousMultilinearMapCLM 𝕜)
      ContinuousAlternatingMap.isEmbedding_toContinuousMultilinearMap |>.continuous_iff]
    exact map_continuous <|
      (precomp (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) G)
        ((ContinuousAlternatingMap.toContinuousMultilinearMapCLM 𝕜 : (E [⋀^ι]→L[𝕜] F) →L[𝕜] _))) ∘L
        (compContinuousMultilinearMapL 𝕜 (fun _ : ι ↦ E) F G)

end ContinuousLinearMap

namespace ContinuousLinearEquiv
variable {𝕜 E E' F G ι : Type*} [NormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup E'] [Module 𝕜 E'] [TopologicalSpace E']
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousConstSMul 𝕜 F]
  [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [ContinuousConstSMul 𝕜 G]

/-- `ContinuousLinearMap.compContinuousAlternatingMap` as a bundled continuous linear equiv.

Given a continuous linear equivalence `g : F ≃L[𝕜] G`,
this function returns the equivalence between continuous alternating maps with codomain `F`
and continuous alternating maps with codomain `G`
that acts by composing these maps with `g`.
-/
@[simps +simpRhs apply]
def continuousAlternatingMapCongrRight (g : F ≃L[𝕜] G) :
    (E [⋀^ι]→L[𝕜] F) ≃L[𝕜] (E [⋀^ι]→L[𝕜] G) where
  __ := g.continuousAlternatingMapCongrRightEquiv
  __ := ContinuousLinearMap.compContinuousAlternatingMapCLM 𝕜 E F G ι g.toContinuousLinearMap
  continuous_toFun := map_continuous <|
    ContinuousLinearMap.compContinuousAlternatingMapCLM 𝕜 E F G ι g.toContinuousLinearMap
  continuous_invFun := map_continuous <|
    ContinuousLinearMap.compContinuousAlternatingMapCLM 𝕜 E G F ι g.symm.toContinuousLinearMap

@[simp]
theorem _root_.ContinuousLinearEquiv.continuousAlternatingMapCongrRight_symm (g : F ≃L[𝕜] G) :
    (g.continuousAlternatingMapCongrRight (ι := ι) (E := E)).symm =
      g.symm.continuousAlternatingMapCongrRight :=
  rfl

/-- Given a continuous linear isomorphism between the domains,
generate a continuous linear isomorphism between the spaces of continuous alternating maps.

This is `ContinuousAlternatingMap.compContinuousLinearMap` as an equivalence,
and is the continuous version of `AlternatingMap.domLCongr`. -/
@[simps apply]
def continuousAlternatingMapCongrLeft (f : E ≃L[𝕜] E') :
    E [⋀^ι]→L[𝕜] F ≃L[𝕜] (E' [⋀^ι]→L[𝕜] F) where
  __ := f.continuousAlternatingMapCongrLeftEquiv
  __ := ContinuousAlternatingMap.compContinuousLinearMapCLM (f.symm : E' →L[𝕜] E)
  toFun g := g.compContinuousLinearMap (f.symm : E' →L[𝕜] E)
  continuous_invFun :=
    (ContinuousAlternatingMap.compContinuousLinearMapCLM (f : E →L[𝕜] E')).cont
  continuous_toFun :=
    (ContinuousAlternatingMap.compContinuousLinearMapCLM (f.symm : E' →L[𝕜] E)).cont

/-- Continuous linear equivalences between the domains and the codomains
generate a continuous linear equivalence between the spaces of continuous alternating maps. -/
@[simps! apply]
def continuousAlternatingMapCongr (e : E ≃L[𝕜] E') (e' : F ≃L[𝕜] G) :
    (E [⋀^ι]→L[𝕜] F) ≃L[𝕜] (E' [⋀^ι]→L[𝕜] G) :=
  e.continuousAlternatingMapCongrLeft.trans <| e'.continuousAlternatingMapCongrRight

end ContinuousLinearEquiv
