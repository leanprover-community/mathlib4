/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Topology.ContinuousFunction.Algebra
import Mathlib.Topology.ContinuousFunction.Compact

/-!
# Continuous maps sending zero to zero

This is the type of continuous maps from `X` to `R` such that `(0 : X) ↦ (0 : R)` for which we
provide the scoped notation `C(X, R)₀`.  We provide this as a dedicated type solely for the
non-unital continuous functional calculus, as using various terms of type `Ideal C(X, R)` were
overly burdensome on type class synthesis.

Of course, one could generalize to maps between pointed topological spaces, but that goes beyond
the purpose of this type.
-/

assert_not_exists StarOrderedRing

open Set Function

/-- The type of continuous maps which map zero to zero.

Note that one should never use the structure projection `ContinuousMapZero.toContinuousMap` and
instead favor the coercion `(↑) : C(X, R)₀ → C(X, R)` available from the instance of
`ContinuousMapClass`. All the instances on `C(X, R)₀` from `C(X, R)` passes through this coercion,
not the structure projection. Of course, the two are definitionally equal, but not reducibly so. -/
structure ContinuousMapZero (X R : Type*) [Zero X] [Zero R] [TopologicalSpace X]
    [TopologicalSpace R] extends C(X, R) where
  map_zero' : toContinuousMap 0 = 0

namespace ContinuousMapZero

@[inherit_doc]
scoped notation "C(" X ", " R ")₀" => ContinuousMapZero X R

section Basic

variable {X Y R : Type*} [Zero X] [Zero Y] [Zero R]
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace R]

instance instFunLike : FunLike C(X, R)₀ X R where
  coe f := f.toFun
  coe_injective' _ _ h := congr(⟨⟨$(h), _⟩, _⟩)

instance instContinuousMapClass : ContinuousMapClass C(X, R)₀ X R where
  map_continuous f := f.continuous

instance instZeroHomClass : ZeroHomClass C(X, R)₀ X R where
  map_zero f := f.map_zero'

@[ext]
lemma ext {f g : C(X, R)₀} (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h

@[simp]
lemma coe_mk {f : C(X, R)} {h0 : f 0 = 0} : ⇑(mk f h0) = f := rfl

lemma toContinuousMap_injective : Injective ((↑) : C(X, R)₀ → C(X, R)) :=
  fun _ _ h ↦ congr(.mk $(h) _)

lemma range_toContinuousMap : range ((↑) : C(X, R)₀ → C(X, R)) = {f : C(X, R) | f 0 = 0} :=
  Set.ext fun f ↦ ⟨fun ⟨f', hf'⟩ ↦ hf' ▸ map_zero f', fun hf ↦ ⟨⟨f, hf⟩, rfl⟩⟩

/-- Composition of continuous maps which map zero to zero. -/
def comp (g : C(Y, R)₀) (f : C(X, Y)₀) : C(X, R)₀ where
  toContinuousMap := (g : C(Y, R)).comp (f : C(X, Y))
  map_zero' := show g (f 0) = 0 from map_zero f ▸ map_zero g

@[simp]
lemma comp_apply (g : C(Y, R)₀) (f : C(X, Y)₀) (x : X) : g.comp f x = g (f x) := rfl

instance instPartialOrder [PartialOrder R] : PartialOrder C(X, R)₀ :=
  .lift _ DFunLike.coe_injective'

lemma le_def [PartialOrder R] (f g : C(X, R)₀) : f ≤ g ↔ ∀ x, f x ≤ g x := Iff.rfl

protected instance instTopologicalSpace : TopologicalSpace C(X, R)₀ :=
  TopologicalSpace.induced ((↑) : C(X, R)₀ → C(X, R)) inferInstance

lemma embedding_toContinuousMap : Embedding ((↑) : C(X, R)₀ → C(X, R)) where
  induced := rfl
  inj _ _ h := ext fun x ↦ congr($(h) x)

instance [T0Space R] : T0Space C(X, R)₀ := embedding_toContinuousMap.t0Space
instance [T1Space R] : T1Space C(X, R)₀ := embedding_toContinuousMap.t1Space
instance [T2Space R] : T2Space C(X, R)₀ := embedding_toContinuousMap.t2Space

lemma closedEmbedding_toContinuousMap [T1Space R] :
    ClosedEmbedding ((↑) : C(X, R)₀ → C(X, R)) where
  toEmbedding := embedding_toContinuousMap
  isClosed_range := by
    rw [range_toContinuousMap]
    exact isClosed_singleton.preimage <| ContinuousMap.continuous_eval_const 0

@[fun_prop]
lemma continuous_comp_left {X Y Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] [Zero X] [Zero Y] [Zero Z] (f : C(X, Y)₀) :
    Continuous fun g : C(Y, Z)₀ ↦ g.comp f := by
  rw [continuous_induced_rng]
  show Continuous fun g : C(Y, Z)₀ ↦ (g : C(Y, Z)).comp (f : C(X, Y))
  fun_prop

/-- The identity function as an element of `C(s, R)₀` when `0 ∈ (s : Set R)`. -/
@[simps!]
protected def id {s : Set R} [Zero s] (h0 : ((0 : s) : R) = 0) : C(s, R)₀ :=
  ⟨.restrict s (.id R), h0⟩

@[simp]
lemma toContinuousMap_id {s : Set R} [Zero s] (h0 : ((0 : s) : R) = 0) :
    (ContinuousMapZero.id h0 : C(s, R)) = .restrict s (.id R) :=
  rfl

end Basic

section Algebra

variable {X R : Type*} [Zero X] [TopologicalSpace X]
variable [TopologicalSpace R]

instance instZero [Zero R] : Zero C(X, R)₀ where
  zero := ⟨0, rfl⟩

@[simp] lemma coe_zero [Zero R] : ⇑(0 : C(X, R)₀) = 0 := rfl

instance instAdd [AddZeroClass R] [ContinuousAdd R] : Add C(X, R)₀ where
  add f g := ⟨f + g, by simp⟩

@[simp] lemma coe_add [AddZeroClass R] [ContinuousAdd R] (f g : C(X, R)₀) : ⇑(f + g) = f + g := rfl

instance instMul [MulZeroClass R] [ContinuousMul R] : Mul C(X, R)₀ where
  mul f g := ⟨f * g, by simp⟩

@[simp] lemma coe_mul [MulZeroClass R] [ContinuousMul R] (f g : C(X, R)₀) : ⇑(f * g) = f * g := rfl

instance instSMul {M : Type*} [Zero R] [SMulZeroClass M R] [ContinuousConstSMul M R] :
    SMul M C(X, R)₀ where
  smul m f := ⟨m • f, by simp⟩

@[simp] lemma coe_smul {M : Type*} [Zero R] [SMulZeroClass M R] [ContinuousConstSMul M R]
    (m : M) (f : C(X, R)₀) : ⇑(m • f) = m • f := rfl

section Semiring

variable [CommSemiring R] [TopologicalSemiring R]

instance instNonUnitalCommSemiring : NonUnitalCommSemiring C(X, R)₀ :=
  toContinuousMap_injective.nonUnitalCommSemiring
    _ rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

instance instModule {M : Type*} [Semiring M] [Module M R] [ContinuousConstSMul M R] :
    Module M C(X, R)₀ :=
  toContinuousMap_injective.module M
    { toFun := _, map_add' := fun _ _ ↦ rfl, map_zero' := rfl } (fun _ _ ↦ rfl)

instance instSMulCommClass {M N : Type*} [SMulZeroClass M R] [ContinuousConstSMul M R]
    [SMulZeroClass N R] [ContinuousConstSMul N R] [SMulCommClass M N R] :
    SMulCommClass M N C(X, R)₀ where
  smul_comm _ _ _ := ext fun _ ↦ smul_comm ..

instance instSMulCommClass' {M : Type*} [SMulZeroClass M R] [SMulCommClass M R R]
    [ContinuousConstSMul M R] : SMulCommClass M C(X, R)₀ C(X, R)₀ where
  smul_comm m f g := ext fun x ↦ smul_comm m (f x) (g x)

instance instIsScalarTower {M N : Type*} [SMulZeroClass M R] [ContinuousConstSMul M R]
    [SMulZeroClass N R] [ContinuousConstSMul N R] [SMul M N] [IsScalarTower M N R] :
    IsScalarTower M N C(X, R)₀ where
  smul_assoc _ _ _ := ext fun _ ↦ smul_assoc ..

instance instIsScalarTower' {M : Type*} [SMulZeroClass M R] [IsScalarTower M R R]
    [ContinuousConstSMul M R] : IsScalarTower M C(X, R)₀ C(X, R)₀ where
  smul_assoc m f g := ext fun x ↦ smul_assoc m (f x) (g x)

instance instStarRing [StarRing R] [ContinuousStar R] : StarRing C(X, R)₀ where
  star f := ⟨star f, by simp⟩
  star_involutive _ := ext fun _ ↦ star_star _
  star_mul _ _ := ext fun _ ↦ star_mul ..
  star_add _ _ := ext fun _ ↦ star_add ..

instance instStarModule [StarRing R] {M : Type*} [SMulZeroClass M R] [ContinuousConstSMul M R]
    [Star M] [StarModule M R] [ContinuousStar R] : StarModule M C(X, R)₀ where
  star_smul r f := ext fun x ↦ star_smul r (f x)

@[simp] lemma coe_star [StarRing R] [ContinuousStar R] (f : C(X, R)₀) : ⇑(star f) = star ⇑f := rfl

instance [StarRing R] [ContinuousStar R] [TrivialStar R] : TrivialStar C(X, R)₀ where
  star_trivial _ := DFunLike.ext _ _ fun _ ↦ star_trivial _

instance instCanLift : CanLift C(X, R) C(X, R)₀ (↑) (fun f ↦ f 0 = 0) where
  prf f hf := ⟨⟨f, hf⟩, rfl⟩

/-- The coercion `C(X, R)₀ → C(X, R)` bundled as a non-unital star algebra homomorphism. -/
@[simps]
def toContinuousMapHom [StarRing R] [ContinuousStar R] : C(X, R)₀ →⋆ₙₐ[R] C(X, R) where
  toFun f := f
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl

lemma coe_toContinuousMapHom [StarRing R] [ContinuousStar R] :
    ⇑(toContinuousMapHom (X := X) (R := R)) = (↑) :=
  rfl

/-- The coercion `C(X, R)₀ → C(X, R)` bundled as a continuous linear map. -/
@[simps]
def toContinuousMapCLM (M : Type*) [Semiring M] [Module M R] [ContinuousConstSMul M R] :
    C(X, R)₀ →L[M] C(X, R) where
  toFun f := f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The evaluation at a point, as a continuous linear map from `C(X, R)₀` to `R`. -/
def evalCLM (𝕜 : Type*) {R : Type*} [CompactSpace X] [NormedField 𝕜] [NormedCommRing R]
    [NormedSpace 𝕜 R] (x : X) : C(X, R)₀ →L[𝕜] R :=
  (ContinuousMap.evalCLM 𝕜 x).comp (toContinuousMapCLM 𝕜 : C(X, R)₀ →L[𝕜] C(X, R))

@[simp]
lemma evalCLM_apply {𝕜 : Type*} {R : Type*} [CompactSpace X] [NormedField 𝕜] [NormedCommRing R]
    [NormedSpace 𝕜 R] (x : X) (f : C(X, R)₀) : evalCLM 𝕜 x f = f x := rfl

/-- Coercion to a function as an `AddMonoidHom`. Similar to `ContinuousMap.coeFnAddMonoidHom`. -/
def coeFnAddMonoidHom : C(X, R)₀ →+ X → R where
  toFun f := f
  map_zero' := coe_zero
  map_add' f g := by simp

@[simp] lemma coe_sum {ι : Type*} (s : Finset ι)
    (f : ι → C(X, R)₀) : ⇑(s.sum f) = s.sum (fun i => ⇑(f i)) :=
  map_sum coeFnAddMonoidHom f s

end Semiring

section Ring

variable {X R : Type*} [Zero X] [TopologicalSpace X]
variable [CommRing R] [TopologicalSpace R] [TopologicalRing R]

instance instSub : Sub C(X, R)₀ where
  sub f g := ⟨f - g, by simp⟩

instance instNeg : Neg C(X, R)₀ where
  neg f := ⟨-f, by simp⟩

instance instNonUnitalCommRing : NonUnitalCommRing C(X, R)₀ :=
  toContinuousMap_injective.nonUnitalCommRing _ rfl
  (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

@[simp]
lemma coe_neg (f : C(X, R)₀) : ⇑(-f) = -⇑f := rfl

instance : ContinuousNeg C(X, R)₀ where
  continuous_neg := by
    rw [continuous_induced_rng]
    exact continuous_neg.comp continuous_induced_dom

end Ring

end Algebra

section UniformSpace

variable {X R : Type*} [Zero X] [TopologicalSpace X]
variable [Zero R] [UniformSpace R]

protected instance instUniformSpace : UniformSpace C(X, R)₀ := .comap toContinuousMap inferInstance

lemma uniformEmbedding_toContinuousMap :
    UniformEmbedding ((↑) : C(X, R)₀ → C(X, R)) where
  comap_uniformity := rfl
  inj _ _ h := ext fun x ↦ congr($(h) x)

instance [T1Space R] [CompleteSpace C(X, R)] : CompleteSpace C(X, R)₀ :=
  completeSpace_iff_isComplete_range uniformEmbedding_toContinuousMap.toUniformInducing
    |>.mpr closedEmbedding_toContinuousMap.isClosed_range.isComplete

lemma uniformEmbedding_comp {Y : Type*} [UniformSpace Y] [Zero Y] (g : C(Y, R)₀)
    (hg : UniformEmbedding g) : UniformEmbedding (g.comp · : C(X, Y)₀ → C(X, R)₀) :=
  uniformEmbedding_toContinuousMap.of_comp_iff.mp <|
    ContinuousMap.uniformEmbedding_comp g.toContinuousMap hg |>.comp
      uniformEmbedding_toContinuousMap

/-- The uniform equivalence `C(X, R)₀ ≃ᵤ C(Y, R)₀` induced by a homeomorphism of the domains
sending `0 : X` to `0 : Y`. -/
def _root_.UniformEquiv.arrowCongrLeft₀ {Y : Type*} [TopologicalSpace Y] [Zero Y] (f : X ≃ₜ Y)
    (hf : f 0 = 0) : C(X, R)₀ ≃ᵤ C(Y, R)₀ where
  toFun g := g.comp ⟨f.symm.toContinuousMap, (f.toEquiv.apply_eq_iff_eq_symm_apply.eq ▸ hf).symm⟩
  invFun g := g.comp ⟨f.toContinuousMap, hf⟩
  left_inv g := ext fun _ ↦ congrArg g <| f.left_inv _
  right_inv g := ext fun _ ↦ congrArg g <| f.right_inv _
  uniformContinuous_toFun := uniformEmbedding_toContinuousMap.uniformContinuous_iff.mpr <|
    ContinuousMap.uniformContinuous_comp_left f.symm.toContinuousMap |>.comp
    uniformEmbedding_toContinuousMap.uniformContinuous
  uniformContinuous_invFun := uniformEmbedding_toContinuousMap.uniformContinuous_iff.mpr <|
    ContinuousMap.uniformContinuous_comp_left f.toContinuousMap |>.comp
    uniformEmbedding_toContinuousMap.uniformContinuous

end UniformSpace

section CompHoms

variable {X Y M R S : Type*} [Zero X] [Zero Y] [CommSemiring M]
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace R] [TopologicalSpace S]
  [CommSemiring R] [StarRing R] [TopologicalSemiring R] [ContinuousStar R]
  [CommSemiring S] [StarRing S] [TopologicalSemiring S] [ContinuousStar S]
  [Module M R] [Module M S] [ContinuousConstSMul M R] [ContinuousConstSMul M S]

variable (R) in
/-- The functor `C(·, R)₀` from topological spaces with zero (and `ContinuousMapZero` maps) to
non-unital star algebras. -/
@[simps]
def nonUnitalStarAlgHom_precomp (f : C(X, Y)₀) : C(Y, R)₀ →⋆ₙₐ[R] C(X, R)₀ where
  toFun g := g.comp f
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl
  map_smul' _ _ := rfl

variable (X) in
/-- The functor `C(X, ·)₀` from non-unital topological star algebras (with non-unital continuous
star homomorphisms) to non-unital star algebras. -/
@[simps apply]
def nonUnitalStarAlgHom_postcomp (φ : R →⋆ₙₐ[M] S) (hφ : Continuous φ) :
    C(X, R)₀ →⋆ₙₐ[M] C(X, S)₀ where
  toFun := .comp ⟨⟨φ, hφ⟩, by simp⟩
  map_zero' := ext <| by simp
  map_add' _ _ := ext <| by simp
  map_mul' _ _ := ext <| by simp
  map_star' _ := ext <| by simp [map_star]
  map_smul' r f := ext <| by simp

end CompHoms

section Norm

variable {α : Type*} {𝕜 : Type*} {R : Type*} [TopologicalSpace α] [CompactSpace α] [Zero α]

noncomputable instance [MetricSpace R] [Zero R]: MetricSpace C(α, R)₀ :=
  ContinuousMapZero.uniformEmbedding_toContinuousMap.comapMetricSpace _

noncomputable instance [NormedAddCommGroup R] : Norm C(α, R)₀ where
  norm f := ‖(f : C(α, R))‖

noncomputable instance [NormedCommRing R] : NonUnitalNormedCommRing C(α, R)₀ where
  dist_eq f g := NormedAddGroup.dist_eq (f : C(α, R)) g
  norm_mul f g := NormedRing.norm_mul (f : C(α, R)) g
  mul_comm f g := mul_comm f g

instance [NormedField 𝕜] [NormedCommRing R] [NormedAlgebra 𝕜 R] : NormedSpace 𝕜 C(α, R)₀ where
  norm_smul_le r f := norm_smul_le r (f : C(α, R))

instance [NormedCommRing R] [StarRing R] [CStarRing R] : CStarRing C(α, R)₀ where
  norm_mul_self_le f := CStarRing.norm_mul_self_le (f : C(α, R))

end Norm

end ContinuousMapZero
