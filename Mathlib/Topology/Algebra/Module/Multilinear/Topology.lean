/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.Module.Multilinear.Bounded
public import Mathlib.Topology.Algebra.Module.StrongTopology
public import Mathlib.Topology.Algebra.Module.UniformConvergence
public import Mathlib.Topology.Algebra.SeparationQuotient.Section
public import Mathlib.Topology.Hom.ContinuousEvalConst
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Topology on continuous multilinear maps

In this file we define `TopologicalSpace` and `UniformSpace` structures
on `ContinuousMultilinearMap 𝕜 E F`,
where `E i` is a family of vector spaces over `𝕜` with topologies
and `F` is a topological vector space.
-/

@[expose] public section

open Bornology Function Set Topology
open scoped UniformConvergence Filter

namespace ContinuousMultilinearMap

variable {𝕜 ι : Type*} {E : ι → Type*} {F : Type*}
  [NormedField 𝕜]
  [∀ i, TopologicalSpace (E i)] [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)]
  [AddCommGroup F] [Module 𝕜 F]

/-- An auxiliary definition used to define topology on `ContinuousMultilinearMap 𝕜 E F`. -/
def toUniformOnFun [TopologicalSpace F] (f : ContinuousMultilinearMap 𝕜 E F) :
    (Π i, E i) →ᵤ[{s | IsVonNBounded 𝕜 s}] F :=
  UniformOnFun.ofFun _ f

open UniformOnFun in
lemma range_toUniformOnFun [DecidableEq ι] [TopologicalSpace F] :
    range toUniformOnFun =
      {f : (Π i, E i) →ᵤ[{s | IsVonNBounded 𝕜 s}] F |
        Continuous (toFun _ f) ∧
        (∀ (m : Π i, E i) i x y,
          toFun _ f (update m i (x + y)) = toFun _ f (update m i x) + toFun _ f (update m i y)) ∧
        (∀ (m : Π i, E i) i (c : 𝕜) x,
          toFun _ f (update m i (c • x)) = c • toFun _ f (update m i x))} := by
  ext f
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨f.cont, f.map_update_add, f.map_update_smul⟩
  · rintro ⟨hcont, hadd, hsmul⟩
    exact ⟨⟨⟨f, by intro; convert hadd, by intro; convert hsmul⟩, hcont⟩, rfl⟩

@[simp]
lemma toUniformOnFun_toFun [TopologicalSpace F] (f : ContinuousMultilinearMap 𝕜 E F) :
    UniformOnFun.toFun _ f.toUniformOnFun = f :=
  rfl

instance instTopologicalSpace [TopologicalSpace F] [IsTopologicalAddGroup F] :
    TopologicalSpace (ContinuousMultilinearMap 𝕜 E F) :=
  .induced toUniformOnFun <|
    @UniformOnFun.topologicalSpace _ _ (IsTopologicalAddGroup.rightUniformSpace F) _

instance instUniformSpace [UniformSpace F] [IsUniformAddGroup F] :
    UniformSpace (ContinuousMultilinearMap 𝕜 E F) :=
  .replaceTopology (.comap toUniformOnFun <| UniformOnFun.uniformSpace _ _ _) <| by
    rw [instTopologicalSpace, IsUniformAddGroup.rightUniformSpace_eq]; rfl

section IsUniformAddGroup

variable [UniformSpace F] [IsUniformAddGroup F]

lemma isUniformInducing_toUniformOnFun :
    IsUniformInducing (toUniformOnFun :
      ContinuousMultilinearMap 𝕜 E F → ((Π i, E i) →ᵤ[{s | IsVonNBounded 𝕜 s}] F)) := ⟨rfl⟩

lemma isUniformEmbedding_toUniformOnFun :
    IsUniformEmbedding (toUniformOnFun : ContinuousMultilinearMap 𝕜 E F → _) :=
  ⟨isUniformInducing_toUniformOnFun, DFunLike.coe_injective⟩

lemma isEmbedding_toUniformOnFun :
    IsEmbedding (toUniformOnFun : ContinuousMultilinearMap 𝕜 E F →
      ((Π i, E i) →ᵤ[{s | IsVonNBounded 𝕜 s}] F)) :=
  isUniformEmbedding_toUniformOnFun.isEmbedding

theorem uniformContinuous_coe_fun [∀ i, ContinuousSMul 𝕜 (E i)] :
    UniformContinuous (DFunLike.coe : ContinuousMultilinearMap 𝕜 E F → (Π i, E i) → F) :=
  (UniformOnFun.uniformContinuous_toFun sUnion_isVonNBounded_eq_univ).comp
    isUniformEmbedding_toUniformOnFun.uniformContinuous

theorem uniformContinuous_eval_const [∀ i, ContinuousSMul 𝕜 (E i)] (x : Π i, E i) :
    UniformContinuous fun f : ContinuousMultilinearMap 𝕜 E F ↦ f x :=
  uniformContinuous_pi.1 uniformContinuous_coe_fun x

instance instIsUniformAddGroup : IsUniformAddGroup (ContinuousMultilinearMap 𝕜 E F) :=
  let φ : ContinuousMultilinearMap 𝕜 E F →+ (Π i, E i) →ᵤ[{s | IsVonNBounded 𝕜 s}] F :=
    { toFun := toUniformOnFun, map_add' := fun _ _ ↦ rfl, map_zero' := rfl }
  isUniformEmbedding_toUniformOnFun.isUniformAddGroup φ

instance instUniformContinuousConstSMul {M : Type*}
    [Monoid M] [DistribMulAction M F] [SMulCommClass 𝕜 M F] [ContinuousConstSMul M F] :
    UniformContinuousConstSMul M (ContinuousMultilinearMap 𝕜 E F) :=
  haveI := uniformContinuousConstSMul_of_continuousConstSMul M F
  isUniformEmbedding_toUniformOnFun.uniformContinuousConstSMul fun _ _ ↦ rfl

theorem isUniformInducing_postcomp
    {G : Type*} [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G] [Module 𝕜 G]
    (g : F →L[𝕜] G) (hg : IsUniformInducing g) :
    IsUniformInducing (g.compContinuousMultilinearMap :
      ContinuousMultilinearMap 𝕜 E F → ContinuousMultilinearMap 𝕜 E G) := by
  rw [← isUniformInducing_toUniformOnFun.of_comp_iff]
  exact (UniformOnFun.postcomp_isUniformInducing hg).comp isUniformInducing_toUniformOnFun

section CompleteSpace

variable [∀ i, ContinuousSMul 𝕜 (E i)] [ContinuousConstSMul 𝕜 F] [CompleteSpace F]

open UniformOnFun in
theorem completeSpace (h : IsCoherentWith {s : Set (Π i, E i) | IsVonNBounded 𝕜 s}) :
    CompleteSpace (ContinuousMultilinearMap 𝕜 E F) := by
  classical
  wlog hF : T2Space F generalizing F
  · rw [(isUniformInducing_postcomp (SeparationQuotient.mkCLM _ _)
      SeparationQuotient.isUniformInducing_mk).completeSpace_congr]
    · exact this inferInstance
    · intro f
      use (SeparationQuotient.outCLM _ _).compContinuousMultilinearMap f
      simp [DFunLike.ext_iff]
  have H : ∀ {m : Π i, E i},
      Continuous fun f : (Π i, E i) →ᵤ[{s | IsVonNBounded 𝕜 s}] F ↦ toFun _ f m :=
    (uniformContinuous_eval (sUnion_isVonNBounded_eq_univ) _).continuous
  rw [completeSpace_iff_isComplete_range isUniformInducing_toUniformOnFun, range_toUniformOnFun]
  simp only [setOf_and, setOf_forall]
  apply_rules [IsClosed.isComplete, IsClosed.inter]
  · exact UniformOnFun.isClosed_setOf_continuous h
  · exact isClosed_iInter fun m ↦ isClosed_iInter fun i ↦
      isClosed_iInter fun x ↦ isClosed_iInter fun y ↦ isClosed_eq H (H.add H)
  · exact isClosed_iInter fun m ↦ isClosed_iInter fun i ↦
      isClosed_iInter fun c ↦ isClosed_iInter fun x ↦ isClosed_eq H (H.const_smul _)

instance instCompleteSpace [∀ i, IsTopologicalAddGroup (E i)] [SequentialSpace (Π i, E i)] :
    CompleteSpace (ContinuousMultilinearMap 𝕜 E F) :=
  completeSpace <| .of_seq fun _u x hux ↦ (hux.isVonNBounded_range 𝕜).insert x

end CompleteSpace

section RestrictScalars

variable (𝕜' : Type*) [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜' 𝕜]
  [∀ i, Module 𝕜' (E i)] [∀ i, IsScalarTower 𝕜' 𝕜 (E i)] [Module 𝕜' F] [IsScalarTower 𝕜' 𝕜 F]
  [∀ i, ContinuousSMul 𝕜 (E i)]

theorem isUniformEmbedding_restrictScalars :
    IsUniformEmbedding
      (restrictScalars 𝕜' : ContinuousMultilinearMap 𝕜 E F → ContinuousMultilinearMap 𝕜' E F) := by
  letI : NontriviallyNormedField 𝕜 :=
    ⟨let ⟨x, hx⟩ := @NontriviallyNormedField.non_trivial 𝕜' _; ⟨algebraMap 𝕜' 𝕜 x, by simpa⟩⟩
  rw [← isUniformEmbedding_toUniformOnFun.of_comp_iff]
  convert isUniformEmbedding_toUniformOnFun using 4 with s
  exact ⟨fun h ↦ h.extend_scalars _, fun h ↦ h.restrict_scalars _⟩

theorem uniformContinuous_restrictScalars :
    UniformContinuous
      (restrictScalars 𝕜' : ContinuousMultilinearMap 𝕜 E F → ContinuousMultilinearMap 𝕜' E F) :=
  (isUniformEmbedding_restrictScalars 𝕜').uniformContinuous

end RestrictScalars

end IsUniformAddGroup

variable [TopologicalSpace F] [IsTopologicalAddGroup F]

instance instIsTopologicalAddGroup : IsTopologicalAddGroup (ContinuousMultilinearMap 𝕜 E F) :=
  letI := IsTopologicalAddGroup.rightUniformSpace F
  haveI := isUniformAddGroup_of_addCommGroup (G := F)
  inferInstance

instance instContinuousConstSMul
    {M : Type*} [Monoid M] [DistribMulAction M F] [SMulCommClass 𝕜 M F] [ContinuousConstSMul M F] :
    ContinuousConstSMul M (ContinuousMultilinearMap 𝕜 E F) := by
  letI := IsTopologicalAddGroup.rightUniformSpace F
  haveI := isUniformAddGroup_of_addCommGroup (G := F)
  infer_instance

instance instContinuousSMul [ContinuousSMul 𝕜 F] :
    ContinuousSMul 𝕜 (ContinuousMultilinearMap 𝕜 E F) :=
  letI := IsTopologicalAddGroup.rightUniformSpace F
  haveI := isUniformAddGroup_of_addCommGroup (G := F)
  let φ : ContinuousMultilinearMap 𝕜 E F →ₗ[𝕜] (Π i, E i) → F :=
    { toFun := (↑), map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  UniformOnFun.continuousSMul_induced_of_image_bounded _ _ _ _ φ
    isEmbedding_toUniformOnFun.isInducing fun _ _ hu ↦ hu.image_multilinear _

theorem hasBasis_nhds_zero_of_basis {ι : Type*} {p : ι → Prop} {b : ι → Set F}
    (h : (𝓝 (0 : F)).HasBasis p b) :
    (𝓝 (0 : ContinuousMultilinearMap 𝕜 E F)).HasBasis
      (fun Si : Set (Π i, E i) × ι => IsVonNBounded 𝕜 Si.1 ∧ p Si.2)
      fun Si => { f | MapsTo f Si.1 (b Si.2) } := by
  letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  haveI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  rw [nhds_induced]
  refine (UniformOnFun.hasBasis_nhds_zero_of_basis _ ?_ ?_ h).comap DFunLike.coe
  · exact ⟨∅, isVonNBounded_empty _ _⟩
  · exact directedOn_of_sup_mem fun _ _ => Bornology.IsVonNBounded.union

theorem hasBasis_nhds_zero :
    (𝓝 (0 : ContinuousMultilinearMap 𝕜 E F)).HasBasis
      (fun SV : Set (Π i, E i) × Set F => IsVonNBounded 𝕜 SV.1 ∧ SV.2 ∈ 𝓝 0) fun SV =>
      { f | MapsTo f SV.1 SV.2 } :=
  hasBasis_nhds_zero_of_basis (Filter.basis_sets _)

theorem eventually_nhds_zero_mapsTo {s : Set (∀ i, E i)} (hs : IsVonNBounded 𝕜 s)
    {U : Set F} (hu : U ∈ 𝓝 0) :
    ∀ᶠ f : ContinuousMultilinearMap 𝕜 E F in 𝓝 0, MapsTo f s U :=
  hasBasis_nhds_zero.mem_of_mem (i := (s, U)) ⟨hs, hu⟩

theorem isVonNBounded_image2_apply [ContinuousConstSMul 𝕜 F]
    {S : Set (ContinuousMultilinearMap 𝕜 E F)} (hS : IsVonNBounded 𝕜 S)
    {s : Set (∀ i, E i)} (hs : IsVonNBounded 𝕜 s) :
    IsVonNBounded 𝕜 (Set.image2 (fun f x ↦ f x) S s) := by
  intro U hU
  filter_upwards [hS (eventually_nhds_zero_mapsTo hs hU)] with c hc
  rw [image2_subset_iff]
  intro f hf x hx
  rcases hc hf with ⟨g, hg, rfl⟩
  exact smul_mem_smul_set (hg hx)

section CompContinuousLinearMap
variable {E₁ : ι → Type*} [∀ i, TopologicalSpace (E₁ i)] [ContinuousConstSMul 𝕜 F]
  [∀ i, AddCommGroup (E₁ i)] [∀ i, Module 𝕜 (E₁ i)]

/-- `ContinuousMultilinearMap.compContinuousLinearMap` as a bundled continuous linear map.
This implementation fixes `f : Π i, E i →L[𝕜] E₁ i`.

Actually, the map is multilinear in `f`,
see `ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear`.

For a version fixing `g` and varying `f`, see `compContinuousLinearMapLRight`. -/
@[simps! apply]
def compContinuousLinearMapL (f : ∀ i, E i →L[𝕜] E₁ i) :
    ContinuousMultilinearMap 𝕜 E₁ F →L[𝕜] ContinuousMultilinearMap 𝕜 E F :=
  let aux : ContinuousMultilinearMap 𝕜 E₁ F →ₗ[𝕜] ContinuousMultilinearMap 𝕜 E F :=
    { toFun g := g.compContinuousLinearMap f
      map_add' _ _ := by ext; simp
      map_smul' _ _ := by ext; simp }
  { toLinearMap := aux
    cont := by
      apply continuous_of_tendsto_nhds_zero (f := aux)
      rw [hasBasis_nhds_zero.tendsto_iff hasBasis_nhds_zero]
      rintro ⟨U, V⟩ ⟨hU, hV⟩
      set φ : (∀ i, E i) →L[𝕜] (∀ i, E₁ i) :=
        .pi fun i ↦ f i ∘L .proj i
      exact ⟨(φ '' U, V), ⟨hU.image φ, hV⟩, fun g hg ↦ hg.comp (mapsTo_image _ _)⟩ }

end CompContinuousLinearMap

variable [∀ i, ContinuousSMul 𝕜 (E i)]

instance : ContinuousEvalConst (ContinuousMultilinearMap 𝕜 E F) (Π i, E i) F where
  continuous_eval_const x :=
    let _ := IsTopologicalAddGroup.rightUniformSpace F
    have _ := isUniformAddGroup_of_addCommGroup (G := F)
    (uniformContinuous_eval_const x).continuous

instance instT2Space [T2Space F] : T2Space (ContinuousMultilinearMap 𝕜 E F) :=
  .of_injective_continuous DFunLike.coe_injective continuous_coeFun

instance instT3Space [T2Space F] : T3Space (ContinuousMultilinearMap 𝕜 E F) :=
  inferInstance

section RestrictScalars

variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜' 𝕜]
  [∀ i, Module 𝕜' (E i)] [∀ i, IsScalarTower 𝕜' 𝕜 (E i)] [Module 𝕜' F] [IsScalarTower 𝕜' 𝕜 F]

theorem isEmbedding_restrictScalars :
    IsEmbedding
      (restrictScalars 𝕜' : ContinuousMultilinearMap 𝕜 E F → ContinuousMultilinearMap 𝕜' E F) :=
  letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  haveI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  (isUniformEmbedding_restrictScalars _).isEmbedding

@[continuity, fun_prop]
theorem continuous_restrictScalars :
    Continuous
      (restrictScalars 𝕜' : ContinuousMultilinearMap 𝕜 E F → ContinuousMultilinearMap 𝕜' E F) :=
  isEmbedding_restrictScalars.continuous

variable (𝕜') in
/-- `ContinuousMultilinearMap.restrictScalars` as a `ContinuousLinearMap`. -/
@[simps -fullyApplied apply]
def restrictScalarsLinear [ContinuousConstSMul 𝕜' F] :
    ContinuousMultilinearMap 𝕜 E F →L[𝕜'] ContinuousMultilinearMap 𝕜' E F where
  toFun := restrictScalars 𝕜'
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end RestrictScalars

variable (𝕜 E F)

/-- The application of a multilinear map as a `ContinuousLinearMap`. -/
def apply [ContinuousConstSMul 𝕜 F] (m : Π i, E i) : ContinuousMultilinearMap 𝕜 E F →L[𝕜] F where
  toFun c := c m
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_eval_const m

variable {𝕜 E F}

@[simp]
lemma apply_apply [ContinuousConstSMul 𝕜 F] {m : Π i, E i} {c : ContinuousMultilinearMap 𝕜 E F} :
    apply 𝕜 E F m c = c m := rfl

theorem hasSum_eval {α : Type*} {p : α → ContinuousMultilinearMap 𝕜 E F}
    {q : ContinuousMultilinearMap 𝕜 E F} (h : HasSum p q) (m : Π i, E i) :
    HasSum (fun a => p a m) (q m) :=
  h.map (applyAddHom m) (continuous_eval_const m)

theorem tsum_eval [T2Space F] {α : Type*} {p : α → ContinuousMultilinearMap 𝕜 E F} (hp : Summable p)
    (m : Π i, E i) : (∑' a, p a) m = ∑' a, p a m :=
  (hasSum_eval hp.hasSum m).tsum_eq.symm

end ContinuousMultilinearMap

namespace ContinuousLinearMap

variable {𝕜 ι : Type*} {E : ι → Type*} {F G : Type*} [NormedField 𝕜] [∀ i, TopologicalSpace (E i)]
  [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousConstSMul 𝕜 F]
  [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [ContinuousConstSMul 𝕜 G]

variable (𝕜 E F G) in
/-- `ContinuousLinearMap.compContinuousMultilinearMap` as a bundled continuous bilinear map. -/
def compContinuousMultilinearMapL :
    (F →L[𝕜] G) →L[𝕜] ContinuousMultilinearMap 𝕜 E F →L[𝕜] ContinuousMultilinearMap 𝕜 E G :=
  let aux : (F →L[𝕜] G) →ₗ[𝕜] ContinuousMultilinearMap 𝕜 E F →L[𝕜] ContinuousMultilinearMap 𝕜 E G :=
    { toFun g :=
        let aux₁ : ContinuousMultilinearMap 𝕜 E F →ₗ[𝕜] ContinuousMultilinearMap 𝕜 E G :=
          { toFun := g.compContinuousMultilinearMap
            map_add' _ _ := by ext; simp
            map_smul' _ _ := by ext; simp }
        { toLinearMap := aux₁
          cont := by
            apply continuous_of_tendsto_nhds_zero (f := aux₁)
            rw [ContinuousMultilinearMap.hasBasis_nhds_zero.tendsto_iff
              ContinuousMultilinearMap.hasBasis_nhds_zero]
            rintro ⟨U, V⟩ ⟨hU, hV⟩
            refine ⟨(U, g ⁻¹' V), ⟨hU, ?_⟩, ?_⟩
            · exact (map_continuous g).tendsto 0 <| by simpa
            · exact fun f hf ↦ hf
        }
      map_add' _ _ := by ext; simp
      map_smul' _ _ := by ext; simp }
  { toLinearMap := aux
    cont := by
      apply continuous_of_tendsto_nhds_zero (f := aux)
      rw [ContinuousLinearMap.hasBasis_nhds_zero.tendsto_iff <|
        ContinuousLinearMap.hasBasis_nhds_zero_of_basis <|
        ContinuousMultilinearMap.hasBasis_nhds_zero]
      rintro ⟨U, V, W⟩ ⟨hU, hV, hW⟩
      refine ⟨(.image2 (fun f v ↦ f v) U V, W), ⟨?_, hW⟩, ?_⟩
      · exact ContinuousMultilinearMap.isVonNBounded_image2_apply hU hV
      · exact fun g hg f hf m hm ↦ hg _ <| mem_image2_of_mem hf hm }

@[simp]
theorem compContinuousMultilinearMapL_apply (g : F →L[𝕜] G) (f : ContinuousMultilinearMap 𝕜 E F) :
    compContinuousMultilinearMapL 𝕜 E F G g f = g.compContinuousMultilinearMap f :=
  rfl

end ContinuousLinearMap

namespace ContinuousLinearEquiv

variable {𝕜 ι : Type*} {E E₁ : ι → Type*} {F G : Type*} [NormedField 𝕜]
  [∀ i, TopologicalSpace (E i)] [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)]
  [∀ i, TopologicalSpace (E₁ i)] [∀ i, AddCommGroup (E₁ i)] [∀ i, Module 𝕜 (E₁ i)]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousConstSMul 𝕜 F]
  [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [ContinuousConstSMul 𝕜 G]

variable (F) in
/-- `ContinuousMultilinearMap.compContinuousLinearMap` as a bundled continuous linear equiv,
given `f : Π i, E i ≃L[𝕜] E₁ i`. -/
def continuousMultilinearMapCongrLeft (f : ∀ i, E i ≃L[𝕜] E₁ i) :
    ContinuousMultilinearMap 𝕜 E₁ F ≃L[𝕜] ContinuousMultilinearMap 𝕜 E F where
  __ := ContinuousMultilinearMap.compContinuousLinearMapL fun i ↦ f i
  invFun := ContinuousMultilinearMap.compContinuousLinearMapL fun i ↦ (f i).symm
  left_inv g := by ext; simp
  right_inv g := by ext; simp

@[simp]
theorem continuousMultilinearMapCongrLeft_symm
    (f : ∀ i, E i ≃L[𝕜] E₁ i) :
    (ContinuousLinearEquiv.continuousMultilinearMapCongrLeft F f).symm =
      .continuousMultilinearMapCongrLeft F fun i : ι => (f i).symm :=
  rfl

@[simp]
theorem continuousMultilinearMapCongrLeft_apply
    (g : ContinuousMultilinearMap 𝕜 E₁ F) (f : ∀ i, E i ≃L[𝕜] E₁ i) :
    ContinuousLinearEquiv.continuousMultilinearMapCongrLeft F f g =
      g.compContinuousLinearMap fun i => (f i : E i →L[𝕜] E₁ i) :=
  rfl

variable (E) in
/-- `ContinuousLinearMap.compContinuousMultilinearMap` as a bundled
continuous linear equiv. -/
def continuousMultilinearMapCongrRight (g : F ≃L[𝕜] G) :
    ContinuousMultilinearMap 𝕜 E F ≃L[𝕜] ContinuousMultilinearMap 𝕜 E G where
  __ := ContinuousLinearMap.compContinuousMultilinearMapL _ _ _ _ g
  invFun := ContinuousLinearMap.compContinuousMultilinearMapL _ _ _ _ g.symm
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

@[simp]
theorem continuousMultilinearMapCongrRight_symm (g : F ≃L[𝕜] G) :
    (g.continuousMultilinearMapCongrRight E).symm = g.symm.continuousMultilinearMapCongrRight E :=
  rfl

@[simp]
theorem continuousMultilinearMapCongrRight_apply (g : F ≃L[𝕜] G)
    (f : ContinuousMultilinearMap 𝕜 E F) :
    g.continuousMultilinearMapCongrRight E f = (g : F →L[𝕜] G).compContinuousMultilinearMap f :=
  rfl

end ContinuousLinearEquiv
