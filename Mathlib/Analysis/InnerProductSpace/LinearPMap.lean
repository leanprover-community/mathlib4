/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.Module.LinearPMap

/-!

# Partially defined linear operators on Hilbert spaces

We will develop the basics of the theory of unbounded operators on Hilbert spaces.

## Main definitions

* `LinearPMap.IsFormalAdjoint`: An operator `T` is a formal adjoint of `S` if for all `x` in the
  domain of `T` and `y` in the domain of `S`, we have that `⟪T x, y⟫ = ⟪x, S y⟫`.
* `LinearPMap.adjoint`: The adjoint of a map `E →ₗ.[𝕜] F` as a map `F →ₗ.[𝕜] E`.

## Main statements

* `LinearPMap.adjoint_isFormalAdjoint`: The adjoint is a formal adjoint
* `LinearPMap.IsFormalAdjoint.le_adjoint`: Every formal adjoint is contained in the adjoint
* `ContinuousLinearMap.toPMap_adjoint_eq_adjoint_toPMap_of_dense`: The adjoint on
  `ContinuousLinearMap` and `LinearPMap` coincide.
* `LinearPMap.adjoint_isClosed`: The adjoint is a closed operator.
* `IsSelfAdjoint.isClosed`: Every self-adjoint operator is closed.

## Notation

* For `T : E →ₗ.[𝕜] F` the adjoint can be written as `T†`.
  This notation is localized in `LinearPMap`.

## Implementation notes

We use the junk value pattern to define the adjoint for all `LinearPMap`s. In the case that
`T : E →ₗ.[𝕜] F` is not densely defined the adjoint `T†` is the zero map from `T.adjoint.domain` to
`E`.

## References

* [J. Weidmann, *Linear Operators in Hilbert Spaces*][weidmann_linear]

## Tags

Unbounded operators, closed operators
-/

@[expose] public section


noncomputable section

open RCLike LinearPMap WithLp

open scoped ComplexConjugate

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

namespace LinearPMap

/-- An operator `T` is a formal adjoint of `S` if for all `x` in the domain of `T` and `y` in the
domain of `S`, we have that `⟪T x, y⟫ = ⟪x, S y⟫`. -/
def IsFormalAdjoint (T : E →ₗ.[𝕜] F) (S : F →ₗ.[𝕜] E) : Prop :=
  ∀ (x : T.domain) (y : S.domain), ⟪T x, y⟫ = ⟪(x : E), S y⟫

variable {T : E →ₗ.[𝕜] F} {S : F →ₗ.[𝕜] E}

@[symm]
protected theorem IsFormalAdjoint.symm (h : T.IsFormalAdjoint S) :
    S.IsFormalAdjoint T := fun y _ => by
  rw [← inner_conj_symm, ← inner_conj_symm (y : F), h]

variable (T)

/-- The domain of the adjoint operator.

This definition is needed to construct the adjoint operator and the preferred version to use is
`T.adjoint.domain` instead of `T.adjointDomain`. -/
def adjointDomain : Submodule 𝕜 F where
  carrier := {y | Continuous ((innerₛₗ 𝕜 y).comp T.toFun)}
  zero_mem' := by
    rw [Set.mem_setOf_eq, LinearMap.map_zero, LinearMap.zero_comp]
    exact continuous_zero
  add_mem' hx hy := by rw [Set.mem_setOf_eq, LinearMap.map_add] at *; exact hx.add hy
  smul_mem' a x hx := by
    rw [Set.mem_setOf_eq, LinearMap.map_smulₛₗ] at *
    exact hx.const_smul (conj a)

/-- The operator `fun x ↦ ⟪y, T x⟫` considered as a continuous linear operator
from `T.adjointDomain` to `𝕜`. -/
def adjointDomainMkCLM (y : T.adjointDomain) : StrongDual 𝕜 T.domain :=
  ⟨(innerₛₗ 𝕜 (y : F)).comp T.toFun, y.prop⟩

theorem adjointDomainMkCLM_apply (y : T.adjointDomain) (x : T.domain) :
    adjointDomainMkCLM T y x = ⟪(y : F), T x⟫ :=
  rfl

/-- The unique continuous extension of the operator `adjointDomainMkCLM` to `E`. -/
def adjointDomainMkCLMExtend (y : T.adjointDomain) : StrongDual 𝕜 E :=
  (T.adjointDomainMkCLM y).extend (Submodule.subtypeL T.domain)

variable {T}

@[simp]
theorem adjointDomainMkCLMExtend_apply (hT : Dense (T.domain : Set E)) (y : T.adjointDomain)
    (x : T.domain) : adjointDomainMkCLMExtend T y (x : E) = ⟪(y : F), T x⟫ :=
  ContinuousLinearMap.extend_eq _ hT.denseRange_val
    isUniformEmbedding_subtype_val.isUniformInducing _

variable [CompleteSpace E]

variable (hT : Dense (T.domain : Set E))

/-- The adjoint as a linear map from its domain to `E`.

This is an auxiliary definition needed to define the adjoint operator as a `LinearPMap` without
the assumption that `T.domain` is dense. -/
def adjointAux : T.adjointDomain →ₗ[𝕜] E where
  toFun y := (InnerProductSpace.toDual 𝕜 E).symm (adjointDomainMkCLMExtend T y)
  map_add' x y :=
    hT.eq_of_inner_left 𝕜 fun z zin => by
      simp [InnerProductSpace.toDual_symm_apply, inner_add_left,
        adjointDomainMkCLMExtend_apply hT _ ⟨z, zin⟩, inner_add_left]
  map_smul' _ _ :=
    hT.eq_of_inner_left 𝕜 fun z zin => by
      simp [inner_smul_left, RingHom.id_apply,
        InnerProductSpace.toDual_symm_apply, adjointDomainMkCLMExtend_apply hT _ ⟨z, zin⟩]

theorem adjointAux_inner (y : T.adjointDomain) (x : T.domain) :
    ⟪adjointAux hT y, x⟫ = ⟪(y : F), T x⟫ := by
  simp [adjointAux, hT]

theorem adjointAux_unique (y : T.adjointDomain) {x₀ : E}
    (hx₀ : ∀ x : T.domain, ⟪x₀, x⟫ = ⟪(y : F), T x⟫) : adjointAux hT y = x₀ :=
  hT.eq_of_inner_left 𝕜 fun v vin => (adjointAux_inner hT _ _).trans (hx₀ ⟨v, vin⟩).symm

variable (T)

open scoped Classical in
/-- The adjoint operator as a partially defined linear operator, denoted as `T†`. -/
@[informal "adjoint operator"]
def adjoint : F →ₗ.[𝕜] E where
  domain := T.adjointDomain
  toFun := if hT : Dense (T.domain : Set E) then adjointAux hT else 0

@[inherit_doc]
scoped postfix:1024 "†" => LinearPMap.adjoint

theorem mem_adjoint_domain_iff (y : F) : y ∈ T†.domain ↔ Continuous ((innerₛₗ 𝕜 y).comp T.toFun) :=
  Iff.rfl

variable {T}

theorem mem_adjoint_domain_of_exists (y : F) (h : ∃ w : E, ∀ x : T.domain, ⟪w, x⟫ = ⟪y, T x⟫) :
    y ∈ T†.domain := by
  obtain ⟨w, hw⟩ := h
  rw [T.mem_adjoint_domain_iff]
  have : Continuous ((innerSL 𝕜 w).comp T.domain.subtypeL) := by fun_prop
  convert this using 1
  exact funext fun x => (hw x).symm

theorem adjoint_apply_of_not_dense (hT : ¬Dense (T.domain : Set E)) (y : T†.domain) : T† y = 0 := by
  classical
  change (if hT : Dense (T.domain : Set E) then adjointAux hT else 0) y = _
  simp only [hT, not_false_iff, dif_neg, LinearMap.zero_apply]

theorem adjoint_apply_of_dense (y : T†.domain) : T† y = adjointAux hT y := by
  classical
  change (if hT : Dense (T.domain : Set E) then adjointAux hT else 0) y = _
  simp only [hT, dif_pos]

include hT in
theorem adjoint_apply_eq (y : T†.domain) {x₀ : E} (hx₀ : ∀ x : T.domain, ⟪x₀, x⟫ = ⟪(y : F), T x⟫) :
    T† y = x₀ :=
  (adjoint_apply_of_dense hT y).symm ▸ adjointAux_unique hT _ hx₀

include hT in
/-- The fundamental property of the adjoint. -/
theorem adjoint_isFormalAdjoint : T†.IsFormalAdjoint T := fun x =>
  (adjoint_apply_of_dense hT x).symm ▸ adjointAux_inner hT x

include hT in
/-- The adjoint is maximal in the sense that it contains every formal adjoint. -/
theorem IsFormalAdjoint.le_adjoint (h : T.IsFormalAdjoint S) : S ≤ T† :=
  ⟨-- Trivially, every `x : S.domain` is in `T.adjoint.domain`
  fun x hx =>
    mem_adjoint_domain_of_exists _
      ⟨S ⟨x, hx⟩, h.symm ⟨x, hx⟩⟩,-- Equality on `S.domain` follows from equality
  -- `⟪v, S x⟫ = ⟪v, T.adjoint y⟫` for all `v : T.domain`:
  fun _ _ hxy => (adjoint_apply_eq hT _ fun _ => by rw [h.symm, hxy]).symm⟩

end LinearPMap

namespace ContinuousLinearMap

variable [CompleteSpace E] [CompleteSpace F]
variable (A : E →L[𝕜] F) {p : Submodule 𝕜 E}

/-- Restricting `A` to a dense submodule and taking the `LinearPMap.adjoint` is the same
as taking the `ContinuousLinearMap.adjoint` interpreted as a `LinearPMap`. -/
theorem toPMap_adjoint_eq_adjoint_toPMap_of_dense (hp : Dense (p : Set E)) :
    (A.toPMap p).adjoint = A.adjoint.toPMap ⊤ := by
  ext x y hxy
  · simp only [LinearMap.toPMap_domain, Submodule.mem_top, iff_true,
      LinearPMap.mem_adjoint_domain_iff]
    exact ((innerSL 𝕜 x).comp <| A.comp <| Submodule.subtypeL _).cont
  refine LinearPMap.adjoint_apply_eq hp _ fun v => ?_
  simp only [adjoint_inner_left, LinearMap.toPMap_apply, coe_coe]

end ContinuousLinearMap

section Star

namespace LinearPMap

variable [CompleteSpace E]

instance instStar : Star (E →ₗ.[𝕜] E) where
  star := fun A ↦ A.adjoint

variable {A : E →ₗ.[𝕜] E}

theorem isSelfAdjoint_def : IsSelfAdjoint A ↔ A† = A := Iff.rfl

/-- Every self-adjoint `LinearPMap` has dense domain.

This is not true by definition since we define the adjoint without the assumption that the
domain is dense, but the choice of the junk value implies that a `LinearPMap` cannot be self-adjoint
if it does not have dense domain. -/
theorem _root_.IsSelfAdjoint.dense_domain (hA : IsSelfAdjoint A) : Dense (A.domain : Set E) := by
  by_contra h
  rw [isSelfAdjoint_def] at hA
  have h' : A.domain = ⊤ := by
    rw [← hA, Submodule.eq_top_iff']
    intro x
    rw [mem_adjoint_domain_iff, ← hA]
    refine (innerSL 𝕜 x).cont.comp ?_
    simp only [adjoint, h]
    exact continuous_const
  simp [h'] at h

end LinearPMap

end Star

/-! ### The graph of the adjoint -/

namespace Submodule

/-- The adjoint of a submodule

Note that the adjoint is taken with respect to the L^2 inner product on `E × F`, which is defined
as `WithLp 2 (E × F)`. -/
protected noncomputable
def adjoint (g : Submodule 𝕜 (E × F)) : Submodule 𝕜 (F × E) :=
  (g.map ((LinearEquiv.skewSwap 𝕜 F E).symm.trans
    (WithLp.linearEquiv 2 𝕜 (F × E)).symm).toLinearMap).orthogonal.map
      (WithLp.linearEquiv 2 𝕜 (F × E) : WithLp 2 (F × E) →ₗ[𝕜] F × E)

@[simp]
theorem mem_adjoint_iff (g : Submodule 𝕜 (E × F)) (x : F × E) :
    x ∈ g.adjoint ↔
    ∀ a b, (a, b) ∈ g → inner 𝕜 b x.fst - inner 𝕜 a x.snd = 0 := by
  simp only [Submodule.adjoint, mem_map, mem_orthogonal, LinearEquiv.coe_coe,
    LinearEquiv.trans_apply, LinearEquiv.skewSwap_symm_apply, coe_symm_linearEquiv, Prod.exists,
    prod_inner_apply, ofLp_fst, ofLp_snd, forall_exists_index, and_imp, coe_linearEquiv]
  constructor
  · rintro ⟨y, h1, h2⟩ a b hab
    rw [← h2, WithLp.ofLp_fst, WithLp.ofLp_snd]
    specialize h1 (toLp 2 (b, -a)) a b hab rfl
    dsimp at h1
    simp only [inner_neg_left, ← sub_eq_add_neg] at h1
    exact h1
  · intro h
    refine ⟨toLp 2 x, ?_, rfl⟩
    intro u a b hab hu
    simp [← hu, ← sub_eq_add_neg, h a b hab]

variable {T : E →ₗ.[𝕜] F} [CompleteSpace E]

theorem _root_.LinearPMap.adjoint_graph_eq_graph_adjoint (hT : Dense (T.domain : Set E)) :
    T†.graph = T.graph.adjoint := by
  ext x
  simp only [mem_graph_iff, Subtype.exists, exists_and_left, exists_eq_left, mem_adjoint_iff,
    forall_exists_index, forall_apply_eq_imp_iff]
  constructor
  · rintro ⟨hx, h⟩ a ha
    rw [← h, (adjoint_isFormalAdjoint hT).symm ⟨a, ha⟩ ⟨x.fst, hx⟩, sub_self]
  · intro h
    simp_rw [sub_eq_zero] at h
    have hx : x.fst ∈ T†.domain := by
      apply mem_adjoint_domain_of_exists
      use x.snd
      rintro ⟨a, ha⟩
      rw [← inner_conj_symm, ← h a ha, inner_conj_symm]
    use hx
    apply hT.eq_of_inner_right 𝕜
    rintro a ha
    rw [← h a ha, (adjoint_isFormalAdjoint hT).symm ⟨a, ha⟩ ⟨x.fst, hx⟩]

@[simp]
theorem _root_.LinearPMap.graph_adjoint_toLinearPMap_eq_adjoint (hT : Dense (T.domain : Set E)) :
    T.graph.adjoint.toLinearPMap = T† := by
  apply eq_of_eq_graph
  rw [adjoint_graph_eq_graph_adjoint hT]
  apply Submodule.toLinearPMap_graph_eq
  intro x hx hx'
  simp only [mem_adjoint_iff, mem_graph_iff, Subtype.exists, exists_and_left, exists_eq_left, hx',
    inner_zero_right, zero_sub, neg_eq_zero, forall_exists_index, forall_apply_eq_imp_iff] at hx
  apply hT.eq_zero_of_inner_right 𝕜
  exact fun a ha ↦ hx a ha

end Submodule

/-! ### Closedness -/

namespace LinearPMap

variable {T : E →ₗ.[𝕜] F} [CompleteSpace E]

theorem adjoint_isClosed (hT : Dense (T.domain : Set E)) :
    T†.IsClosed := by
  rw [IsClosed, adjoint_graph_eq_graph_adjoint hT, Submodule.adjoint]
  simp only [Submodule.map_coe]
  rw [LinearEquiv.coe_coe, LinearEquiv.image_eq_preimage_symm]
  exact (Submodule.isClosed_orthogonal _).preimage (WithLp.prod_continuous_toLp _ _ _)

/-- Every self-adjoint `LinearPMap` is closed. -/
theorem _root_.IsSelfAdjoint.isClosed {A : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A) : A.IsClosed := by
  rw [← isSelfAdjoint_def.mp hA]
  exact adjoint_isClosed hA.dense_domain

end LinearPMap
