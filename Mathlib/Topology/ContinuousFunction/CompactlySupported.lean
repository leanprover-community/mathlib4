/-
Copyright (c) 2024 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/
import Mathlib.Topology.ContinuousFunction.Bounded
import Mathlib.Topology.ContinuousFunction.CocompactMap

/-!
# Compactly supported continuous functions

The type of compactly supported continuous functions. When the domain is compact,
`C(α, β) ≃ C_c(α, β)` via the identity map. When the codomain is a metric space, every continuous
compactly supported map is a bounded continuous function. When the domain is a locally
compact space, this type has nice properties.

## TODO

* Create more intances of algebraic structures (e.g., `NonUnitalSemiring`) once the necessary
  type classes (e.g., `TopologicalRing`) are sufficiently generalized.
-/


universe u v w

variable {F : Type*} {α : Type u} {β : Type v} {γ : Type w} [TopologicalSpace α]

open BoundedContinuousFunction Topology Bornology

open Filter Metric

/-- `C_c(α, β)` is the type of continuous functions `α → β` with compact support from a topological
space to a metric space with a zero element.

When possible, instead of parametrizing results over `(f : C_c(α, β))`,
you should parametrize over `(F : Type*) [CompactlySupportedContinuousMapClass F α β] (f : F)`.

When you extend this structure, make sure to extend `CompactlySupportedContinuousMapClass`. -/
structure CompactlySupportedContinuousMap (α : Type u) (β : Type v) [TopologicalSpace α] [Zero β]
    [TopologicalSpace β] extends ContinuousMap α β : Type max u v where
  /-- The function has compact support . -/
  has_compact_support' : HasCompactSupport toFun

@[inherit_doc]
scoped[CompactlySupported] notation (priority := 2000)
  "C_c(" α ", " β ")" => CompactlySupportedContinuousMap α β

@[inherit_doc]
scoped[CompactlySupported] notation α " →C_c " β => CompactlySupportedContinuousMap α β

open CompactlySupported

section

/-- `CompactlySupportedContinuousMapClass F α β` states that `F` is a type of continuous maps with
compact support.

You should also extend this typeclass when you extend `CompactlySupportedContinuousMap`. -/
class CompactlySupportedContinuousMapClass (F : Type*) (α β : outParam <| Type*)
    [TopologicalSpace α] [Zero β] [TopologicalSpace β] [FunLike F α β]
    extends ContinuousMapClass F α β : Prop where
  /-- Each member of the class has compact support. -/
  has_compact_support (f : F) : HasCompactSupport f

end

export CompactlySupportedContinuousMapClass (has_compact_support)

namespace CompactlySupportedContinuousMap

section Basics

variable [TopologicalSpace β] [Zero β] [FunLike F α β] [CompactlySupportedContinuousMapClass F α β]

instance instFunLike : FunLike C_c(α, β) α β where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr

instance instCompactlySupportedContinuousMapClass :
    CompactlySupportedContinuousMapClass C_c(α, β) α β where
  map_continuous f := f.continuous_toFun
  has_compact_support f := f.has_compact_support'

instance instCoeTC : CoeTC F C_c(α, β) :=
  ⟨fun f =>
    { toFun := f
      continuous_toFun := map_continuous f
      has_compact_support' := has_compact_support f }⟩

@[simp]
theorem coe_toContinuousMap (f : C_c(α, β)) : (f.toContinuousMap : α → β) = f :=
  rfl

@[ext]
theorem ext {f g : C_c(α, β)} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

/-- Copy of a `CompactlySupportedContinuousMap` with a new `toFun` equal to the old one. Useful
to fix definitional equalities. -/
protected def copy (f : C_c(α, β)) (f' : α → β) (h : f' = f) : C_c(α, β) where
  toFun := f'
  continuous_toFun := by
    rw [h]
    exact f.continuous_toFun
  has_compact_support' := by
    simp_rw [h]
    exact f.has_compact_support'

@[simp]
theorem coe_copy (f : C_c(α, β)) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

theorem copy_eq (f : C_c(α, β)) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

theorem eq_of_empty [IsEmpty α] (f g : C_c(α, β)) : f = g :=
  ext <| IsEmpty.elim ‹_›

/-- A continuous function on a compact space has automatically compact support. -/
@[simps]
def ContinuousMap.liftCompactlySupported [CompactSpace α] : C(α, β) ≃ C_c(α, β) where
  toFun f :=
    { toFun := f
      continuous_toFun := f.continuous
      has_compact_support' := by
        simp only
        exact IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport f)
          (Set.subset_univ (tsupport f))
        }
  invFun f := f
  left_inv f := by
    ext
    rfl
  right_inv f := by
    ext
    rfl

/-- A continuous function on a compact space has automatically compact support. This is not an instance to avoid type class loops. -/
lemma compactlySupportedContinuousMapClass.ofCompact {G : Type*} [FunLike G α β]
    [ContinuousMapClass G α β] [CompactSpace α] : CompactlySupportedContinuousMapClass G α β where
  map_continuous := map_continuous
  has_compact_support := by
    intro f
    exact IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport f)
      (Set.subset_univ (tsupport f))

end Basics

/-! ### Algebraic structure

Whenever `β` has suitable algebraic structure and a compatible topological structure, then
`C_c(α, β)` inherits a corresponding algebraic structure. The primary exception to this is that
`C_c(α, β)` will not have a multiplicative identity.
-/


section AlgebraicStructure

variable [TopologicalSpace β] (x : α)

lemma hasCompactSupport_zero [Zero β]: HasCompactSupport (0 : C(α, β)) := by
  rw [HasCompactSupport, tsupport]
  simp only [ContinuousMap.coe_zero, Function.support_zero', closure_empty, isCompact_empty]

instance instZero [Zero β] : Zero C_c(α, β) :=
  ⟨⟨0, hasCompactSupport_zero⟩⟩

instance instInhabited [Zero β] : Inhabited C_c(α, β) :=
  ⟨0⟩

@[simp]
theorem coe_zero [Zero β] : ⇑(0 : C_c(α, β)) = 0 :=
  rfl

theorem zero_apply [Zero β] : (0 : C_c(α, β)) x = 0 :=
  rfl

instance instMul [MulZeroClass β] [ContinuousMul β] : Mul C_c(α, β) :=
  ⟨fun f g => ⟨f * g, HasCompactSupport.mul_left g.2⟩⟩

@[simp]
theorem coe_mul [MulZeroClass β] [ContinuousMul β] (f g : C_c(α, β)) : ⇑(f * g) = f * g :=
  rfl

theorem mul_apply [MulZeroClass β] [ContinuousMul β] (f g : C_c(α, β)) : (f * g) x = f x * g x :=
  rfl

instance instMulZeroClass [MulZeroClass β] [ContinuousMul β] : MulZeroClass C_c(α, β) :=
  DFunLike.coe_injective.mulZeroClass _ coe_zero coe_mul

instance instSemigroupWithZero [SemigroupWithZero β] [ContinuousMul β] :
    SemigroupWithZero C_c(α, β) :=
  DFunLike.coe_injective.semigroupWithZero _ coe_zero coe_mul

instance instAdd [AddZeroClass β] [ContinuousAdd β] : Add C_c(α, β) :=
  ⟨fun f g => ⟨f + g, HasCompactSupport.add f.2 g.2⟩⟩

@[simp]
theorem coe_add [AddZeroClass β] [ContinuousAdd β] (f g : C_c(α, β)) : ⇑(f + g) = f + g :=
  rfl

theorem add_apply [AddZeroClass β] [ContinuousAdd β] (f g : C_c(α, β)) : (f + g) x = f x + g x :=
  rfl

instance instAddZeroClass [AddZeroClass β] [ContinuousAdd β] : AddZeroClass C_c(α, β) :=
  DFunLike.coe_injective.addZeroClass _ coe_zero coe_add

instance instSMul [Zero β] {R : Type*} [Zero R] [SMulWithZero R β] [ContinuousConstSMul R β] :
    SMul R C_c(α, β) :=
  -- Porting note: Original version didn't have `Continuous.const_smul f.continuous r`
  ⟨fun r f => ⟨⟨r • ⇑f, Continuous.const_smul f.continuous r⟩, HasCompactSupport.smul_left f.2⟩⟩

@[simp, norm_cast]
theorem coe_smul [Zero β] {R : Type*} [Zero R] [SMulWithZero R β] [ContinuousConstSMul R β] (r : R)
    (f : C_c(α, β)) : ⇑(r • f) = r • ⇑f :=
  rfl

theorem smul_apply [Zero β] {R : Type*} [Zero R] [SMulWithZero R β] [ContinuousConstSMul R β]
    (r : R) (f : C_c(α, β)) (x : α) : (r • f) x = r • f x :=
  rfl

section AddMonoid

variable [AddMonoid β] [ContinuousAdd β] (f g : C_c(α, β))

instance instAddMonoid : AddMonoid C_c(α, β) :=
  DFunLike.coe_injective.addMonoid _ coe_zero coe_add fun _ _ => rfl

end AddMonoid

instance instAddCommMonoid [AddCommMonoid β] [ContinuousAdd β] : AddCommMonoid C_c(α, β) :=
  DFunLike.coe_injective.addCommMonoid _ coe_zero coe_add fun _ _ => rfl

section AddGroup

variable [AddGroup β] [TopologicalAddGroup β] (f g : C_c(α, β))

instance instNeg : Neg C_c(α, β) :=
  ⟨fun f => ⟨-f, by simpa only [neg_zero] using (zero_at_infty f).neg⟩⟩

@[simp]
theorem coe_neg : ⇑(-f) = -f :=
  rfl

theorem neg_apply : (-f) x = -f x :=
  rfl

instance instSub : Sub C_c(α, β) :=
  ⟨fun f g => ⟨f - g, by simpa only [sub_zero] using (zero_at_infty f).sub (zero_at_infty g)⟩⟩

@[simp]
theorem coe_sub : ⇑(f - g) = f - g :=
  rfl

theorem sub_apply : (f - g) x = f x - g x :=
  rfl

instance instAddGroup : AddGroup C_c(α, β) :=
  DFunLike.coe_injective.addGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ => rfl

end AddGroup

instance instAddCommGroup [AddCommGroup β] [TopologicalAddGroup β] : AddCommGroup C_c(α, β) :=
  DFunLike.coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ =>
    rfl

instance instIsCentralScalar [Zero β] {R : Type*} [Zero R] [SMulWithZero R β] [SMulWithZero Rᵐᵒᵖ β]
    [ContinuousConstSMul R β] [IsCentralScalar R β] : IsCentralScalar R C_c(α, β) :=
  ⟨fun _ _ => ext fun _ => op_smul_eq_smul _ _⟩

instance instSMulWithZero [Zero β] {R : Type*} [Zero R] [SMulWithZero R β]
    [ContinuousConstSMul R β] : SMulWithZero R C_c(α, β) :=
  Function.Injective.smulWithZero ⟨_, coe_zero⟩ DFunLike.coe_injective coe_smul

instance instMulActionWithZero [Zero β] {R : Type*} [MonoidWithZero R] [MulActionWithZero R β]
    [ContinuousConstSMul R β] : MulActionWithZero R C_c(α, β) :=
  Function.Injective.mulActionWithZero ⟨_, coe_zero⟩ DFunLike.coe_injective coe_smul

instance instModule [AddCommMonoid β] [ContinuousAdd β] {R : Type*} [Semiring R] [Module R β]
    [ContinuousConstSMul R β] : Module R C_c(α, β) :=
  Function.Injective.module R ⟨⟨_, coe_zero⟩, coe_add⟩ DFunLike.coe_injective coe_smul

instance instNonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring β] [TopologicalSemiring β] :
    NonUnitalNonAssocSemiring C_c(α, β) :=
  DFunLike.coe_injective.nonUnitalNonAssocSemiring _ coe_zero coe_add coe_mul fun _ _ => rfl

instance instNonUnitalSemiring [NonUnitalSemiring β] [TopologicalSemiring β] :
    NonUnitalSemiring C_c(α, β) :=
  DFunLike.coe_injective.nonUnitalSemiring _ coe_zero coe_add coe_mul fun _ _ => rfl

instance instNonUnitalCommSemiring [NonUnitalCommSemiring β] [TopologicalSemiring β] :
    NonUnitalCommSemiring C_c(α, β) :=
  DFunLike.coe_injective.nonUnitalCommSemiring _ coe_zero coe_add coe_mul fun _ _ => rfl

instance instNonUnitalNonAssocRing [NonUnitalNonAssocRing β] [TopologicalRing β] :
    NonUnitalNonAssocRing C_c(α, β) :=
  DFunLike.coe_injective.nonUnitalNonAssocRing _ coe_zero coe_add coe_mul coe_neg coe_sub
    (fun _ _ => rfl) fun _ _ => rfl

instance instNonUnitalRing [NonUnitalRing β] [TopologicalRing β] : NonUnitalRing C_c(α, β) :=
  DFunLike.coe_injective.nonUnitalRing _ coe_zero coe_add coe_mul coe_neg coe_sub (fun _ _ => rfl)
    fun _ _ => rfl

instance instNonUnitalCommRing [NonUnitalCommRing β] [TopologicalRing β] :
    NonUnitalCommRing C_c(α, β) :=
  DFunLike.coe_injective.nonUnitalCommRing _ coe_zero coe_add coe_mul coe_neg coe_sub
    (fun _ _ => rfl) fun _ _ => rfl

instance instIsScalarTower {R : Type*} [Semiring R] [NonUnitalNonAssocSemiring β]
    [TopologicalSemiring β] [Module R β] [ContinuousConstSMul R β] [IsScalarTower R β β] :
    IsScalarTower R C_c(α, β) C_c(α, β) where
  smul_assoc r f g := by
    ext
    simp only [smul_eq_mul, coe_mul, coe_smul, Pi.mul_apply, Pi.smul_apply]
    rw [← smul_eq_mul, ← smul_eq_mul, smul_assoc]

instance instSMulCommClass {R : Type*} [Semiring R] [NonUnitalNonAssocSemiring β]
    [TopologicalSemiring β] [Module R β] [ContinuousConstSMul R β] [SMulCommClass R β β] :
    SMulCommClass R C_c(α, β) C_c(α, β) where
  smul_comm r f g := by
    ext
    simp only [smul_eq_mul, coe_smul, coe_mul, Pi.smul_apply, Pi.mul_apply]
    rw [← smul_eq_mul, ← smul_eq_mul, smul_comm]

end AlgebraicStructure

section Uniform

variable [UniformSpace β] [UniformSpace γ] [Zero γ]
variable [FunLike F β γ] [CompactlySupportedContinuousMapClass F β γ]

theorem uniformContinuous (f : F) : UniformContinuous (f : β → γ) :=
  (map_continuous f).uniformContinuous_of_tendsto_cocompact (zero_at_infty f)

end Uniform

/-! ### Metric structure

When `β` is a metric space, then every element of `C_c(α, β)` is bounded, and so there is a natural
inclusion map `CompactlySupportedContinuousMap.toBCF : C_c(α, β) → (α →ᵇ β)`. Via this map `C_c(α, β)`
inherits a metric as the pullback of the metric on `α →ᵇ β`. Moreover, this map has closed range
in `α →ᵇ β` and consequently `C_c(α, β)` is a complete space whenever `β` is complete.
-/


section Metric

open Metric Set

variable [PseudoMetricSpace β] [Zero β] [FunLike F α β] [CompactlySupportedContinuousMapClass F α β]

protected theorem bounded (f : F) : ∃ C, ∀ x y : α, dist ((f : α → β) x) (f y) ≤ C := by
  obtain ⟨K : Set α, hK₁, hK₂⟩ := mem_cocompact.mp
    (tendsto_def.mp (zero_at_infty (f : F)) _ (closedBall_mem_nhds (0 : β) zero_lt_one))
  obtain ⟨C, hC⟩ := (hK₁.image (map_continuous f)).isBounded.subset_closedBall (0 : β)
  refine' ⟨max C 1 + max C 1, fun x y => _⟩
  have : ∀ x, f x ∈ closedBall (0 : β) (max C 1) := by
    intro x
    by_cases hx : x ∈ K
    · exact (mem_closedBall.mp <| hC ⟨x, hx, rfl⟩).trans (le_max_left _ _)
    · exact (mem_closedBall.mp <| mem_preimage.mp (hK₂ hx)).trans (le_max_right _ _)
  exact (dist_triangle (f x) 0 (f y)).trans
    (add_le_add (mem_closedBall.mp <| this x) (mem_closedBall'.mp <| this y))

theorem isBounded_range (f : C_c(α, β)) : IsBounded (range f) :=
  isBounded_range_iff.2 (CompactlySupportedContinuousMap.bounded f)

theorem isBounded_image (f : C_c(α, β)) (s : Set α) : IsBounded (f '' s) :=
  f.isBounded_range.subset <| image_subset_range _ _

instance (priority := 100) instBoundedContinuousMapClass : BoundedContinuousMapClass F α β :=
  { ‹CompactlySupportedContinuousMapClass F α β› with
    map_bounded := fun f => CompactlySupportedContinuousMap.bounded f }

/-- Construct a bounded continuous function from a continuous function vanishing at infinity. -/
@[simps!]
def toBCF (f : C_c(α, β)) : α →ᵇ β :=
  ⟨f, map_bounded f⟩

section

variable (α) (β)

theorem toBCF_injective : Function.Injective (toBCF : C_c(α, β) → α →ᵇ β) := fun f g h => by
  ext x
  simpa only using DFunLike.congr_fun h x

end

variable {C : ℝ} {f g : C_c(α, β)}

/-- The type of continuous functions vanishing at infinity, with the uniform distance induced by the
inclusion `CompactlySupportedContinuousMap.toBCF`, is a pseudo-metric space. -/
noncomputable instance instPseudoMetricSpace : PseudoMetricSpace C_c(α, β) :=
  PseudoMetricSpace.induced toBCF inferInstance

/-- The type of continuous functions vanishing at infinity, with the uniform distance induced by the
inclusion `CompactlySupportedContinuousMap.toBCF`, is a metric space. -/
noncomputable instance instMetricSpace {β : Type*} [MetricSpace β] [Zero β] :
    MetricSpace C_c(α, β) :=
  MetricSpace.induced _ (toBCF_injective α β) inferInstance

@[simp]
theorem dist_toBCF_eq_dist {f g : C_c(α, β)} : dist f.toBCF g.toBCF = dist f g :=
  rfl

open BoundedContinuousFunction

/-- Convergence in the metric on `C_c(α, β)` is uniform convergence. -/
theorem tendsto_iff_tendstoUniformly {ι : Type*} {F : ι → C_c(α, β)} {f : C_c(α, β)} {l : Filter ι} :
    Tendsto F l (𝓝 f) ↔ TendstoUniformly (fun i => F i) f l := by
  simpa only [Metric.tendsto_nhds] using
    @BoundedContinuousFunction.tendsto_iff_tendstoUniformly _ _ _ _ _ (fun i => (F i).toBCF)
      f.toBCF l

theorem isometry_toBCF : Isometry (toBCF : C_c(α, β) → α →ᵇ β) := by tauto

theorem isClosed_range_toBCF : IsClosed (range (toBCF : C_c(α, β) → α →ᵇ β)) := by
  refine' isClosed_iff_clusterPt.mpr fun f hf => _
  rw [clusterPt_principal_iff] at hf
  have : Tendsto f (cocompact α) (𝓝 0) := by
    refine' Metric.tendsto_nhds.mpr fun ε hε => _
    obtain ⟨_, hg, g, rfl⟩ := hf (ball f (ε / 2)) (ball_mem_nhds f <| half_pos hε)
    refine' (Metric.tendsto_nhds.mp (zero_at_infty g) (ε / 2) (half_pos hε)).mp
      (eventually_of_forall fun x hx => _)
    calc
      dist (f x) 0 ≤ dist (g.toBCF x) (f x) + dist (g x) 0 := dist_triangle_left _ _ _
      _ < dist g.toBCF f + ε / 2 := add_lt_add_of_le_of_lt (dist_coe_le_dist x) hx
      _ < ε := by simpa [add_halves ε] using add_lt_add_right (mem_ball.1 hg) (ε / 2)
  exact ⟨⟨f.toContinuousMap, this⟩, rfl⟩

@[deprecated] alias closed_range_toBCF := isClosed_range_toBCF -- 2024-03-17

/-- Continuous functions vanishing at infinity taking values in a complete space form a
complete space. -/
instance instCompleteSpace [CompleteSpace β] : CompleteSpace C_c(α, β) :=
  (completeSpace_iff_isComplete_range isometry_toBCF.uniformInducing).mpr
    isClosed_range_toBCF.isComplete

end Metric

section Norm

/-! ### Normed space

The norm structure on `C_c(α, β)` is the one induced by the inclusion `toBCF : C_c(α, β) → (α →ᵇ b)`,
viewed as an additive monoid homomorphism. Then `C_c(α, β)` is naturally a normed space over a normed
field `𝕜` whenever `β` is as well.
-/


section NormedSpace

noncomputable instance instSeminormedAddCommGroup [SeminormedAddCommGroup β] :
    SeminormedAddCommGroup C_c(α, β) :=
  SeminormedAddCommGroup.induced _ _ (⟨⟨toBCF, rfl⟩, fun _ _ => rfl⟩ : C_c(α, β) →+ α →ᵇ β)

noncomputable instance instNormedAddCommGroup [NormedAddCommGroup β] :
    NormedAddCommGroup C_c(α, β) :=
  NormedAddCommGroup.induced _ _ (⟨⟨toBCF, rfl⟩, fun _ _ => rfl⟩ : C_c(α, β) →+ α →ᵇ β)
    (toBCF_injective α β)

variable [SeminormedAddCommGroup β] {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 β]

@[simp]
theorem norm_toBCF_eq_norm {f : C_c(α, β)} : ‖f.toBCF‖ = ‖f‖ :=
  rfl

instance : NormedSpace 𝕜 C_c(α, β) where norm_smul_le k f := (norm_smul_le k f.toBCF : _)

end NormedSpace

section NormedRing

noncomputable instance instNonUnitalSeminormedRing [NonUnitalSeminormedRing β] :
    NonUnitalSeminormedRing C_c(α, β) :=
  { instNonUnitalRing, instSeminormedAddCommGroup with
    norm_mul := fun f g => norm_mul_le f.toBCF g.toBCF }

noncomputable instance instNonUnitalNormedRing [NonUnitalNormedRing β] :
    NonUnitalNormedRing C_c(α, β) :=
  { instNonUnitalRing, instNormedAddCommGroup with
    norm_mul := fun f g => norm_mul_le f.toBCF g.toBCF }

noncomputable instance instNonUnitalSeminormedCommRing [NonUnitalSeminormedCommRing β] :
    NonUnitalSeminormedCommRing C_c(α, β) :=
  { instNonUnitalSeminormedRing, instNonUnitalCommRing with }

noncomputable instance instNonUnitalNormedCommRing [NonUnitalNormedCommRing β] :
    NonUnitalNormedCommRing C_c(α, β) :=
  { instNonUnitalNormedRing, instNonUnitalCommRing with }

end NormedRing

end Norm

section Star

/-! ### Star structure

It is possible to equip `C_c(α, β)` with a pointwise `star` operation whenever there is a continuous
`star : β → β` for which `star (0 : β) = 0`. We don't have quite this weak a typeclass, but
`StarAddMonoid` is close enough.

The `StarAddMonoid` and `NormedStarGroup` classes on `C_c(α, β)` are inherited from their
counterparts on `α →ᵇ β`. Ultimately, when `β` is a C⋆-ring, then so is `C_c(α, β)`.
-/


variable [TopologicalSpace β] [AddMonoid β] [StarAddMonoid β] [ContinuousStar β]

instance instStar : Star C_c(α, β) where
  star f :=
    { toFun := fun x => star (f x)
      continuous_toFun := (map_continuous f).star
      zero_at_infty' := by
        simpa only [star_zero] using (continuous_star.tendsto (0 : β)).comp (zero_at_infty f) }

@[simp]
theorem coe_star (f : C_c(α, β)) : ⇑(star f) = star (⇑f) :=
  rfl

theorem star_apply (f : C_c(α, β)) (x : α) : (star f) x = star (f x) :=
  rfl

instance instStarAddMonoid [ContinuousAdd β] : StarAddMonoid C_c(α, β) where
  star_involutive f := ext fun x => star_star (f x)
  star_add f g := ext fun x => star_add (f x) (g x)

end Star

section NormedStar

variable [NormedAddCommGroup β] [StarAddMonoid β] [NormedStarGroup β]

instance instNormedStarGroup : NormedStarGroup C_c(α, β) where
  norm_star f := (norm_star f.toBCF : _)

end NormedStar

section StarModule

variable {𝕜 : Type*} [Zero 𝕜] [Star 𝕜] [AddMonoid β] [StarAddMonoid β] [TopologicalSpace β]
  [ContinuousStar β] [SMulWithZero 𝕜 β] [ContinuousConstSMul 𝕜 β] [StarModule 𝕜 β]

instance instStarModule : StarModule 𝕜 C_c(α, β) where
  star_smul k f := ext fun x => star_smul k (f x)

end StarModule

section StarRing

variable [NonUnitalSemiring β] [StarRing β] [TopologicalSpace β] [ContinuousStar β]
  [TopologicalSemiring β]

instance instStarRing : StarRing C_c(α, β) :=
  { CompactlySupportedContinuousMap.instStarAddMonoid with
    star_mul := fun f g => ext fun x => star_mul (f x) (g x) }

end StarRing

section CstarRing

instance instCstarRing [NonUnitalNormedRing β] [StarRing β] [CstarRing β] : CstarRing C_c(α, β) where
  norm_star_mul_self {f} := CstarRing.norm_star_mul_self (x := f.toBCF)

end CstarRing

/-! ### C_c as a functor

For each `β` with sufficient structure, there is a contravariant functor `C_c(-, β)` from the
category of topological spaces with morphisms given by `CocompactMap`s.
-/


variable {δ : Type*} [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]

local notation α " →co " β => CocompactMap α β

section

variable [Zero δ]

/-- Composition of a continuous function vanishing at infinity with a cocompact map yields another
continuous function vanishing at infinity. -/
def comp (f : C_c(γ, δ)) (g : β →co γ) : C_c(β, δ) where
  toContinuousMap := (f : C(γ, δ)).comp g
  zero_at_infty' := (zero_at_infty f).comp (cocompact_tendsto g)

@[simp]
theorem coe_comp_to_continuous_fun (f : C_c(γ, δ)) (g : β →co γ) : ((f.comp g) : β → δ) = f ∘ g :=
  rfl

@[simp]
theorem comp_id (f : C_c(γ, δ)) : f.comp (CocompactMap.id γ) = f :=
  ext fun _ => rfl

@[simp]
theorem comp_assoc (f : C_c(γ, δ)) (g : β →co γ) (h : α →co β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
theorem zero_comp (g : β →co γ) : (0 : C_c(γ, δ)).comp g = 0 :=
  rfl

end

/-- Composition as an additive monoid homomorphism. -/
def compAddMonoidHom [AddMonoid δ] [ContinuousAdd δ] (g : β →co γ) : C_c(γ, δ) →+ C_c(β, δ) where
  toFun f := f.comp g
  map_zero' := zero_comp g
  map_add' _ _ := rfl

/-- Composition as a semigroup homomorphism. -/
def compMulHom [MulZeroClass δ] [ContinuousMul δ] (g : β →co γ) : C_c(γ, δ) →ₙ* C_c(β, δ) where
  toFun f := f.comp g
  map_mul' _ _ := rfl

/-- Composition as a linear map. -/
def compLinearMap [AddCommMonoid δ] [ContinuousAdd δ] {R : Type*} [Semiring R] [Module R δ]
    [ContinuousConstSMul R δ] (g : β →co γ) : C_c(γ, δ) →ₗ[R] C_c(β, δ) where
  toFun f := f.comp g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Composition as a non-unital algebra homomorphism. -/
def compNonUnitalAlgHom {R : Type*} [Semiring R] [NonUnitalNonAssocSemiring δ]
    [TopologicalSemiring δ] [Module R δ] [ContinuousConstSMul R δ] (g : β →co γ) :
    C_c(γ, δ) →ₙₐ[R] C_c(β, δ) where
  toFun f := f.comp g
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

end CompactlySupportedContinuousMap
