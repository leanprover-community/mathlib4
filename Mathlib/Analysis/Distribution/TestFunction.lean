/-
Copyright (c) 2025 Luigi Massacci. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luigi Massacci, Anatole Dedecker
-/
module

public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
public import Mathlib.Analysis.Distribution.DerivNotation

/-!
# Continuously differentiable functions with compact support

This file develops the basic theory of bundled `n`-times continuously differentiable functions
with compact support contained in some open set `Ω`. More explicitly, given normed spaces `E`
and `F`, an open set `Ω : Opens E` and `n : ℕ∞`, we are interested in the space `𝓓^{n}(Ω, F)` of
maps `f : E → F` such that:

- `f` is `n`-times continuously differentiable: `ContDiff ℝ n f`.
- `f` has compact support: `HasCompactSupport f`.
- the support of `f` is inside the open set `Ω`: `tsupport f ⊆ Ω`.

This exists as a bundled type to equip it with the canonical LF topology induced by the inclusions
`𝓓_{K}^{n}(Ω, F) → 𝓓^{n}(Ω, F)` (see `ContDiffMapSupportedIn`). The dual space is then the space of
distributions, or "weak solutions" to PDEs, on `Ω`.

## Main definitions

- `TestFunction Ω F n`: the type of bundled `n`-times continuously differentiable
  functions `E → F` with compact support contained in `Ω`.
- `TestFunction.topologicalSpace`: the canonical LF topology on `𝓓^{n}(Ω, F)`. It is the
  locally convex inductive limit of the topologies on each `𝓓_{K}^{n}(Ω, F)`.

## Main statements

- `TestFunction.continuous_iff_continuous_comp`: a linear map from `𝓓^{n}(E, F)`
  to a locally convex space is continuous iff its restriction to `𝓓^{n}_{K}(E, F)` is
  continuous for each compact set `K`. We will later translate this concretely in terms
  of seminorms.

## Notation

- `𝓓^{n}(Ω, F)`: the space of bundled `n`-times continuously differentiable functions `E → F`
  with compact support contained in `Ω`.
- `𝓓(Ω, F)`: the space of bundled smooth (infinitely differentiable) functions `E → F`
  with compact support contained in `Ω`, i.e. `𝓓^{⊤}(Ω, F)`.

## Tags

distributions, test function
-/

@[expose] public section

open Function Seminorm SeminormFamily Set TopologicalSpace UniformSpace
open scoped BoundedContinuousFunction NNReal Topology ContDiff

variable {𝕜 𝕂 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω Ω₁ Ω₂ : Opens E}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [NormedSpace 𝕜 F']
  {n n₁ n₂ k : ℕ∞}

variable (Ω F n) in
/-- The type of bundled `n`-times continuously differentiable maps with compact support -/
@[informal "Test functions"]
structure TestFunction : Type _ where
  /-- The underlying function. Use coercion instead. -/
  protected toFun : E → F
  protected contDiff' : ContDiff ℝ n toFun
  protected hasCompactSupport' : HasCompactSupport toFun
  protected tsupport_subset' : tsupport toFun ⊆ Ω

/-- Notation for the space of bundled `n`-times continuously differentiable maps
with compact support. -/
scoped[Distributions] notation "𝓓^{" n "}(" Ω ", " F ")" => TestFunction Ω F n

/-- Notation for the space of "test functions", i.e. bundled smooth (infinitely differentiable) maps
with compact support. -/
scoped[Distributions] notation "𝓓(" Ω ", " F ")" => TestFunction Ω F ⊤

open Distributions

/-- `TestFunctionClass B Ω F n` states that `B` is a type of `n`-times continuously
differentiable functions `E → F` with compact support contained in `Ω : Opens E`. -/
class TestFunctionClass (B : Type*)
    {E : outParam <| Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (Ω : outParam <| Opens E)
    (F : outParam <| Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : outParam ℕ∞) extends FunLike B E F where
  map_contDiff (f : B) : ContDiff ℝ n f
  map_hasCompactSupport (f : B) : HasCompactSupport f
  tsupport_map_subset (f : B) : tsupport f ⊆ Ω

open TestFunctionClass

namespace TestFunctionClass

instance (B : Type*)
    {E : outParam <| Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (Ω : outParam <| Opens E)
    (F : outParam <| Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : outParam ℕ∞) [TestFunctionClass B Ω F n] :
    ContinuousMapClass B E F where
  map_continuous f := (map_contDiff f).continuous

instance (B : Type*)
    {E : outParam <| Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (Ω : outParam <| Opens E)
    (F : outParam <| Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : outParam ℕ∞) [TestFunctionClass B Ω F n] :
    BoundedContinuousMapClass B E F where
  map_bounded f := by
    obtain ⟨C, hC⟩ := (map_continuous f).bounded_above_of_compact_support (map_hasCompactSupport f)
    exact map_bounded (BoundedContinuousFunction.ofNormedAddCommGroup f (map_continuous f) C hC)

end TestFunctionClass

namespace TestFunction

instance toTestFunctionClass : TestFunctionClass 𝓓^{n}(Ω, F) Ω F n where
  coe f := f.toFun
  coe_injective' f g h := by cases f; cases g; congr
  map_contDiff f := f.contDiff'
  map_hasCompactSupport f := f.hasCompactSupport'
  tsupport_map_subset f := f.tsupport_subset'

protected theorem contDiff (f : 𝓓^{n}(Ω, F)) : ContDiff ℝ n f := map_contDiff f
protected theorem hasCompactSupport (f : 𝓓^{n}(Ω, F)) : HasCompactSupport f :=
  map_hasCompactSupport f
protected theorem tsupport_subset (f : 𝓓^{n}(Ω, F)) : tsupport f ⊆ Ω := tsupport_map_subset f

@[simp]
theorem toFun_eq_coe {f : 𝓓^{n}(Ω, F)} : f.toFun = (f : E → F) :=
  rfl

/-- See note [custom simps projection]. -/
def Simps.coe (f : 𝓓^{n}(Ω, F)) : E → F := f

initialize_simps_projections TestFunction (toFun → coe, as_prefix coe)

@[ext]
theorem ext {f g : 𝓓^{n}(Ω, F)} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext _ _ h

/-- Copy of a `TestFunction` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : 𝓓^{n}(Ω, F)) (f' : E → F) (h : f' = f) : 𝓓^{n}(Ω, F) where
  toFun := f'
  contDiff' := h.symm ▸ f.contDiff
  hasCompactSupport' := h.symm ▸ f.hasCompactSupport
  tsupport_subset' := h.symm ▸ f.tsupport_subset

@[simp]
theorem coe_copy (f : 𝓓^{n}(Ω, F)) (f' : E → F) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

theorem copy_eq (f : 𝓓^{n}(Ω, F)) (f' : E → F) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

@[simp]
theorem coe_toBoundedContinuousFunction (f : 𝓓^{n}(Ω, F)) :
    (f : BoundedContinuousFunction E F) = (f : E → F) := rfl

@[simp]
theorem coe_mk {f : E → F} {contDiff : ContDiff ℝ n f} {hasCompactSupport : HasCompactSupport f}
    {tsupport_subset : tsupport f ⊆ Ω} :
    TestFunction.mk f contDiff hasCompactSupport tsupport_subset = f :=
  rfl

section AddCommGroup

@[simps -fullyApplied]
instance : Zero 𝓓^{n}(Ω, F) where
  zero := ⟨0, contDiff_zero_fun, .zero, by simp only [tsupport_zero, empty_subset]⟩

@[simps -fullyApplied]
instance : Add 𝓓^{n}(Ω, F) where
  add f g := ⟨f + g, f.contDiff.add g.contDiff, f.hasCompactSupport.add g.hasCompactSupport,
    tsupport_add f g |>.trans <| union_subset f.tsupport_subset g.tsupport_subset⟩

@[simps -fullyApplied]
instance : Neg 𝓓^{n}(Ω, F) where
  neg f := ⟨-f, f.contDiff.neg, f.hasCompactSupport.neg, tsupport_neg f ▸ f.tsupport_subset⟩

@[simps -fullyApplied]
instance : Sub 𝓓^{n}(Ω, F) where
  sub f g := ⟨f - g, f.contDiff.sub g.contDiff, f.hasCompactSupport.sub g.hasCompactSupport,
    tsupport_sub f g |>.trans <| union_subset f.tsupport_subset g.tsupport_subset⟩

@[simps -fullyApplied]
instance {R} [Semiring R] [Module R F] [SMulCommClass ℝ R F] [ContinuousConstSMul R F] :
    SMul R 𝓓^{n}(Ω, F) where
  smul c f := ⟨c • f, f.contDiff.const_smul c, f.hasCompactSupport.smul_left,
    tsupport_smul_subset_right _ _ |>.trans f.tsupport_subset⟩

instance : AddCommGroup 𝓓^{n}(Ω, F) := fast_instance%
  DFunLike.coe_injective.addCommGroup _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

variable (Ω F n) in
/-- Coercion as an additive homomorphism. -/
@[simps -fullyApplied]
def coeFnAddMonoidHom : 𝓓^{n}(Ω, F) →+ E → F where
  toFun f := f
  map_zero' := coe_zero
  map_add' _ _ := rfl

end AddCommGroup

section Module

instance {R} [Semiring R] [Module R F] [SMulCommClass ℝ R F] [ContinuousConstSMul R F] :
    Module R 𝓓^{n}(Ω, F) := fast_instance%
  DFunLike.coe_injective.module R (coeFnAddMonoidHom Ω F n) fun _ _ ↦ rfl

instance {R S} [Semiring R] [Semiring S] [Module R F] [Module S F] [SMulCommClass ℝ R F]
    [SMulCommClass ℝ S F] [ContinuousConstSMul R F] [ContinuousConstSMul S F] [SMul R S]
    [IsScalarTower R S F] :
    IsScalarTower R S 𝓓^{n}(Ω, F) where
  smul_assoc _ _ _ := by ext; simp

end Module

open ContDiffMapSupportedIn

/-- The natural inclusion `𝓓^{n}_{K}(E, F) → 𝓓^{n}(Ω, F)` when `K ⊆ Ω`. -/
@[simps -fullyApplied]
def ofSupportedIn {K : Compacts E} (K_sub_Ω : (K : Set E) ⊆ Ω) (f : 𝓓^{n}_{K}(E, F)) :
    𝓓^{n}(Ω, F) :=
  ⟨f, f.contDiff, f.compact_supp, f.tsupport_subset.trans K_sub_Ω⟩

section Topology

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [t : TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [LocallyConvexSpace ℝ V]

variable (Ω F n) in
/-- The "original topology" on `𝓓^{n}(Ω, F)`, defined as the supremum over all compacts `K ⊆ Ω` of
the topology on `𝓓^{n}_{K}(E, F)`. In other words, this topology makes `𝓓^{n}(Ω, F)` the inductive
limit of the `𝓓^{n}_{K}(E, F)`s **in the category of topological spaces**.

Note that this has no reason to be a locally convex (or even vector space) topology. For this
reason, we actually endow `𝓓^{n}(Ω, F)` with another topology, namely the finest locally convex
topology which is coarser than this original topology. See `TestFunction.topologicalSpace`. -/
@[implicit_reducible]
noncomputable def originalTop : TopologicalSpace 𝓓^{n}(Ω, F) :=
  ⨆ (K : Compacts E) (K_sub_Ω : (K : Set E) ⊆ Ω),
    coinduced (ofSupportedIn K_sub_Ω) ContDiffMapSupportedIn.topologicalSpace

variable (Ω F n) in
/-- The canonical LF topology on `𝓓^{n}(Ω, F)`. This makes `𝓓^{n}(Ω, F)` the inductive
limit of the `𝓓^{n}_{K}(E, F)`s **in the category of locally convex topological vector spaces**
(over ℝ). See `TestFunction.continuous_iff_continuous_comp` for the corresponding universal
property.

More concretely, this is defined as the infimum of *all* locally convex topologies which are
coarser than the "original topology" `TestFunction.originalTop`, which corresponds to taking
the inductive limit in the category of topological spaces. -/
noncomputable instance topologicalSpace : TopologicalSpace 𝓓^{n}(Ω, F) :=
  sInf {t : TopologicalSpace 𝓓^{n}(Ω, F) | originalTop Ω F n ≤ t ∧
    @IsTopologicalAddGroup 𝓓^{n}(Ω, F) t _ ∧
    @ContinuousSMul ℝ 𝓓^{n}(Ω, F) _ _ t ∧
    @LocallyConvexSpace ℝ 𝓓^{n}(Ω, F) _ _ _ _ t}

noncomputable instance : IsTopologicalAddGroup 𝓓^{n}(Ω, F) :=
  topologicalAddGroup_sInf fun _ ⟨_, ht, _, _⟩ ↦ ht

noncomputable instance uniformSpace : UniformSpace 𝓓^{n}(Ω, F) :=
  IsTopologicalAddGroup.rightUniformSpace 𝓓^{n}(Ω, F)

noncomputable instance : IsUniformAddGroup 𝓓^{n}(Ω, F) :=
  isUniformAddGroup_of_addCommGroup

-- TODO: deduce for `RCLike` field `𝕂`
noncomputable instance : ContinuousSMul ℝ 𝓓^{n}(Ω, F) :=
  continuousSMul_sInf fun _ ⟨_, _, ht, _⟩ ↦ ht

noncomputable instance : LocallyConvexSpace ℝ 𝓓^{n}(Ω, F) :=
  .sInf fun _ ⟨_, _, _, ht⟩ ↦ ht

theorem originalTop_le : originalTop Ω F n ≤ topologicalSpace Ω F n :=
  le_sInf fun _t ⟨ht, _⟩ ↦ ht

/-- Fix a locally convex topology `t` on `𝓓^{n}(Ω, F)`. `t` is coarser than the canonical topology
on `𝓓^{n}(Ω, F)` if and only if it is coarser than the "original topology" given by
`TestFunction.originalTop`. -/
theorem topologicalSpace_le_iff {t : TopologicalSpace 𝓓^{n}(Ω, F)}
    [@IsTopologicalAddGroup _ t _] [@ContinuousSMul ℝ _ _ _ t]
    [@LocallyConvexSpace ℝ _ _ _ _ _ t] :
    topologicalSpace Ω F n ≤ t ↔ originalTop Ω F n ≤ t :=
  ⟨le_trans originalTop_le, fun H ↦ sInf_le ⟨H, inferInstance, inferInstance, inferInstance⟩⟩

/-- For every compact `K ⊆ Ω`, the inclusion map `𝓓^{n}_{K}(E, F) → 𝓓^{n}(Ω, F)` is
continuous. It is in fact a topological embedding, though this fact is not in Mathlib yet. -/
@[fun_prop]
theorem continuous_ofSupportedIn {K : Compacts E} (K_sub_Ω : (K : Set E) ⊆ Ω) :
    Continuous (ofSupportedIn K_sub_Ω : 𝓓^{n}_{K}(E, F) → 𝓓^{n}(Ω, F)) := by
  rw [continuous_iff_coinduced_le]
  exact le_trans (le_iSup₂_of_le K K_sub_Ω le_rfl) originalTop_le

variable (𝕜) in
/-- The natural inclusion `𝓓^{n}_{K}(E, F) → 𝓓^{n}(Ω, F)`, when `K ⊆ Ω`, as a continuous
linear map. -/
noncomputable def ofSupportedInCLM [SMulCommClass ℝ 𝕜 F] {K : Compacts E}
    (K_sub_Ω : (K : Set E) ⊆ Ω) :
    𝓓^{n}_{K}(E, F) →L[𝕜] 𝓓^{n}(Ω, F) where
  toFun f := ofSupportedIn K_sub_Ω f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_ofSupportedIn K_sub_Ω

@[deprecated (since := "2025-12-10")] alias ofSupportedInLM := ofSupportedInCLM

@[simp] theorem coe_ofSupportedInCLM [SMulCommClass ℝ 𝕜 F] {K : Compacts E}
    (K_sub_Ω : (K : Set E) ⊆ Ω) :
    (ofSupportedInCLM 𝕜 K_sub_Ω : 𝓓^{n}_{K}(E, F) → 𝓓^{n}(Ω, F)) = ofSupportedIn K_sub_Ω :=
  rfl

@[deprecated (since := "2025-12-10")] alias coe_ofSupportedInLM := coe_ofSupportedInCLM

/-- The **universal property** of the topology on `𝓓^{n}(Ω, F)`: a **linear** map from
`𝓓^{n}(Ω, F)` to a locally convex topological vector space is continuous if and only if its
precomposition with the inclusion `ofSupportedIn K_sub_Ω : 𝓓^{n}_{K}(E, F) → 𝓓^{n}(Ω, F)` is
continuous for every compact `K ⊆ Ω`. -/
protected theorem continuous_iff_continuous_comp [Algebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 F]
    [Module 𝕜 V] [IsScalarTower ℝ 𝕜 V] (f : 𝓓^{n}(Ω, F) →ₗ[𝕜] V) :
    Continuous f ↔ ∀ (K : Compacts E) (K_sub_Ω : (K : Set E) ⊆ Ω),
      Continuous (f ∘ ofSupportedIn K_sub_Ω) := by
  simp_rw [← f.coe_restrictScalars ℝ]
  rw [continuous_iff_le_induced]
  have : @IsTopologicalAddGroup _ (induced (f.restrictScalars ℝ) t) _ :=
    topologicalAddGroup_induced _
  have : @ContinuousSMul ℝ _ _ _ (induced (f.restrictScalars ℝ) t) := continuousSMul_induced _
  have : @LocallyConvexSpace ℝ _ _ _ _ _ (induced (f.restrictScalars ℝ) t) := .induced _
  simp_rw [topologicalSpace_le_iff, originalTop, iSup₂_le_iff, ← continuous_iff_le_induced,
    continuous_coinduced_dom]

variable (𝕜) in
/-- Reformulation of the universal property of the topology on `𝓓^{n}(Ω, F)`, in the form of a
custom constructor for continuous linear maps `𝓓^{n}(Ω, F) →L[𝕜] V`, where `V` is an arbitrary
locally convex topological vector space. See also `limitCLM`. -/
@[simps]
protected noncomputable def mkCLM [Algebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 F] [Module 𝕜 V]
    [IsScalarTower ℝ 𝕜 V]
    (toFun : 𝓓^{n}(Ω, F) → V)
    (map_add : ∀ f g, toFun (f + g) = toFun f + toFun g)
    (map_smul : ∀ c : 𝕜, ∀ f, toFun (c • f) = c • toFun f)
    (cont : ∀ (K : Compacts E) (K_sub_Ω : (K : Set E) ⊆ Ω),
      Continuous (toFun ∘ ofSupportedIn K_sub_Ω)) :
    𝓓^{n}(Ω, F) →L[𝕜] V :=
  letI Φ : 𝓓^{n}(Ω, F) →ₗ[𝕜] V := ⟨⟨toFun, map_add⟩, map_smul⟩
  { toLinearMap := Φ
    cont := show Continuous Φ by rwa [TestFunction.continuous_iff_continuous_comp] }

variable (𝕜) in
/-- Reformulation of the universal property of the topology on `𝓓^{n}(Ω, F)`, in the form of a
custom constructor for continuous linear maps `𝓓^{n}(Ω, F) →L[𝕜] V`, where `V` is an arbitrary
locally convex topological vector space. See also `mkCLM`. -/
@[simps!]
protected noncomputable def limitCLM [Algebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 F] [Module 𝕜 V]
    [IsScalarTower ℝ 𝕜 V]
    (toFun : 𝓓^{n}(Ω, F) → V)
    (T : Π (K : Compacts E), (K : Set E) ⊆ Ω → 𝓓^{n}_{K}(E, F) →L[𝕜] V)
    (toFun_eq_T : ∀ K K_sub_Ω f, toFun (ofSupportedIn K_sub_Ω f) = T K K_sub_Ω f) :
    𝓓^{n}(Ω, F) →L[𝕜] V :=
  haveI toFun_add (f g : 𝓓^{n}(Ω, F)) : toFun (f + g) = toFun f + toFun g := by
    set K : Compacts E := ⟨tsupport f ∪ tsupport g, .union f.hasCompactSupport g.hasCompactSupport⟩
    have K_sub_Ω : (K : Set E) ⊆ Ω := union_subset f.tsupport_subset g.tsupport_subset
    let f_K : 𝓓^{n}_{K}(E, F) :=
      .of_support_subset f.contDiff (subset_closure.trans subset_union_left)
    let g_K : 𝓓^{n}_{K}(E, F) :=
      .of_support_subset g.contDiff (subset_closure.trans subset_union_right)
    change toFun (ofSupportedIn K_sub_Ω (f_K + g_K)) =
      toFun (ofSupportedIn K_sub_Ω f_K) + toFun (ofSupportedIn K_sub_Ω g_K)
    simp [toFun_eq_T]
  haveI toFun_smul (c : 𝕜) (f : 𝓓^{n}(Ω, F)) : toFun (c • f) = c • toFun f := by
    set K : Compacts E := ⟨tsupport f, f.hasCompactSupport⟩
    have K_sub_Ω : (K : Set E) ⊆ Ω := f.tsupport_subset
    let f_K : 𝓓^{n}_{K}(E, F) := .of_support_subset f.contDiff subset_closure
    change toFun (ofSupportedIn K_sub_Ω (c • f_K)) = c • toFun (ofSupportedIn K_sub_Ω f_K)
    simp [toFun_eq_T]
  TestFunction.mkCLM 𝕜 toFun toFun_add toFun_smul
    (fun K K_sub_Ω ↦ .congr (T K K_sub_Ω).continuous (fun f ↦ (toFun_eq_T K K_sub_Ω f).symm))

end Topology

section ToBoundedContinuousFunctionCLM

variable (𝕜) in
/-- The inclusion of the space `𝓓^{n}(Ω, F)` into the space `E →ᵇ F` of bounded continuous
functions as a continuous `𝕜`-linear map. -/
@[simps! apply]
noncomputable def toBoundedContinuousFunctionCLM [Algebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 F] :
    𝓓^{n}(Ω, F) →L[𝕜] E →ᵇ F :=
  TestFunction.mkCLM 𝕜 (↑) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ (ContDiffMapSupportedIn.toBoundedContinuousFunctionCLM 𝕜).continuous)

lemma toBoundedContinuousFunctionCLM_eq_of_scalars [Algebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 F] (𝕜' : Type*)
    [NontriviallyNormedField 𝕜'] [NormedSpace 𝕜' F] [Algebra ℝ 𝕜'] [IsScalarTower ℝ 𝕜' F] :
    (toBoundedContinuousFunctionCLM 𝕜 : 𝓓^{n}(Ω, F) → _) = toBoundedContinuousFunctionCLM 𝕜' :=
  rfl

variable (𝕜) in
theorem injective_toBoundedContinuousFunctionCLM [Algebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 F] :
    Function.Injective (toBoundedContinuousFunctionCLM 𝕜 : 𝓓^{n}(Ω, F) →L[𝕜] E →ᵇ F) :=
  fun f g ↦ by simp [toBoundedContinuousFunctionCLM]

instance : ContinuousEval 𝓓^{n}(Ω, F) E F :=
  ContinuousEval.of_continuous_forget
    (toBoundedContinuousFunctionCLM ℝ).continuous

instance : T3Space 𝓓^{n}(Ω, F) :=
  suffices T2Space 𝓓^{n}(Ω, F) from inferInstance
  .of_injective_continuous (injective_toBoundedContinuousFunctionCLM ℝ)
    (ContinuousLinearMap.continuous _)

end ToBoundedContinuousFunctionCLM

section postcomp

variable [Algebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 F] [IsScalarTower ℝ 𝕜 F']

-- Note: generalizing this to a semilinear setting would require a typeclass-way of saying that
-- the `RingHom` is `ℝ`-linear.
/-- Given `T : F →L[𝕜] F'`, `postcompCLM T` is the continuous `𝕜`-linear-map sending
`f : 𝓓^{n}(Ω, F)` to `T ∘ f` as an element of `𝓓^{n}(Ω, F')`. -/
noncomputable def postcompCLM (T : F →L[𝕜] F') :
    𝓓^{n}(Ω, F) →L[𝕜] 𝓓^{n}(Ω, F') :=
  letI Φ (f : 𝓓^{n}(Ω, F)) : 𝓓^{n}(Ω, F') :=
    ⟨T ∘ f, T.restrictScalars ℝ |>.contDiff.comp f.contDiff,
      f.hasCompactSupport.comp_left (map_zero _),
      (tsupport_comp_subset (map_zero _) f).trans f.tsupport_subset⟩
  TestFunction.limitCLM 𝕜 Φ
    (fun K K_sub_Ω ↦ ofSupportedInCLM 𝕜 K_sub_Ω ∘L ContDiffMapSupportedIn.postcompCLM T)
    (fun _ _ _ ↦ by ext; simp [Φ])

@[simp]
lemma postcompCLM_apply (T : F →L[𝕜] F')
    (f : 𝓓^{n}(Ω, F)) :
    postcompCLM T f = T ∘ f :=
  rfl

end postcomp

section Monotone

variable [Algebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 F]

variable (𝕜) in
/-- If `n₁ ≥ n₂` and `Ω₁ ⊆ Ω₂`, `monoCLM 𝕜` is the continuous `𝕜`-linear inclusion of
`𝓓^{n₁}(Ω₁, F)` inside `𝓓^{n₂}(Ω₂, F)`. Otherwise, this is the zero map.

This is in fact a topological embedding when `n₁ = n₂` and `Ω₁ ⊆ Ω₂` (not in Mathlib as of
March 2026).

The parameters `n₁, n₂, Ω₁, Ω₂` are implicit as they can often be inferred from context, or
specified by a type ascription. -/
noncomputable def monoCLM :
    𝓓^{n₁}(Ω₁, F) →L[𝕜] 𝓓^{n₂}(Ω₂, F) :=
  open scoped Classical in
  letI Φ (f : 𝓓^{n₁}(Ω₁, F)) : 𝓓^{n₂}(Ω₂, F) :=
    if h : n₂ ≤ n₁ ∧ Ω₁ ≤ Ω₂ then
      ⟨f, f.contDiff.of_le (mod_cast h.1), f.hasCompactSupport, f.tsupport_subset.trans h.2⟩
    else 0
  TestFunction.limitCLM 𝕜 Φ
    (fun K K_sub_Ω₁ ↦ if h : n₂ ≤ n₁ ∧ Ω₁ ≤ Ω₂
      then ofSupportedInCLM 𝕜 (K_sub_Ω₁.trans h.2) ∘L ContDiffMapSupportedIn.monoCLM 𝕜
      else 0)
    (fun _ _ _ ↦ by ext; dsimp [Φ]; split_ifs with h <;> simp [h])

open scoped Classical in
@[simp]
lemma monoCLM_apply (f : 𝓓^{n₁}(Ω₁, F)) :
    ((monoCLM 𝕜 f : 𝓓^{n₂}(Ω₂, F)) : E → F) = if n₂ ≤ n₁ ∧ Ω₁ ≤ Ω₂ then f else 0 := by
  rw [monoCLM]
  split_ifs <;> rfl

lemma monoCLM_eq_zero (H : ¬ (n₂ ≤ n₁ ∧ Ω₁ ≤ Ω₂)) :
    (monoCLM 𝕜 : 𝓓^{n₁}(Ω₁, F) →L[𝕜] 𝓓^{n₂}(Ω₂, F)) = 0 := by
  ext; simp [H]

lemma monoCLM_eq_of_scalars (𝕜' : Type*)
    [NontriviallyNormedField 𝕜'] [NormedSpace 𝕜' F] [Algebra ℝ 𝕜'] [IsScalarTower ℝ 𝕜' F] :
    (monoCLM 𝕜 : 𝓓^{n₁}(Ω₁, F) → 𝓓^{n₂}(Ω₂, F)) = monoCLM 𝕜' :=
  rfl

end Monotone

section FDerivCLM

variable [Algebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 F]

variable (𝕜 n k) in
/-- `fderivCLM 𝕜 n k` is the continuous `𝕜`-linear-map sending `f : 𝓓^{n}_{K}(E, F)` to
its derivative as an element of `𝓓^{k}_{K}(E, E →L[ℝ] F)`.
This only makes mathematical sense if `k + 1 ≤ n`, otherwise we define it as the zero map. -/
noncomputable def fderivCLM :
    𝓓^{n}(Ω, F) →L[𝕜] 𝓓^{k}(Ω, E →L[ℝ] F) :=
  letI Φ (f : 𝓓^{n}(Ω, F)) : 𝓓^{k}(Ω, E →L[ℝ] F) :=
    if hk : k + 1 ≤ n then
      ⟨fderiv ℝ f, f.contDiff.fderiv_right (mod_cast hk),
        f.hasCompactSupport.fderiv ℝ, tsupport_fderiv_subset ℝ |>.trans f.tsupport_subset⟩
    else 0
  TestFunction.limitCLM 𝕜 Φ
    (fun K K_sub_Ω ↦ ofSupportedInCLM 𝕜 K_sub_Ω ∘L ContDiffMapSupportedIn.fderivCLM 𝕜 n k)
    (fun _ _ _ ↦ by ext; dsimp [Φ]; split_ifs with h <;> simp [h])

@[simp]
lemma fderivCLM_apply (f : 𝓓^{n}(Ω, F)) :
    fderivCLM 𝕜 n k f = if k + 1 ≤ n then fderiv ℝ f else 0 := by
  rw [fderivCLM]
  split_ifs <;> rfl

lemma fderivCLM_apply_of_le (f : 𝓓^{n}(Ω, F)) (hk : k + 1 ≤ n) :
    fderivCLM 𝕜 n k f = fderiv ℝ f := by
  simp [hk]

lemma fderivCLM_apply_of_gt (hk : n < k + 1) :
    (fderivCLM 𝕜 n k : 𝓓^{n}(Ω, F) →L[𝕜] 𝓓^{k}(Ω, E →L[ℝ] F)) = 0 := by
  ext : 2
  simp [not_le_of_gt hk]

variable (𝕜) in
lemma fderivCLM_ofSupportedIn {K : Compacts E}
    (K_sub_Ω : (K : Set E) ⊆ Ω) (f : 𝓓^{n}_{K}(E, F)) :
    fderivCLM 𝕜 n k (ofSupportedIn K_sub_Ω f) =
      ofSupportedIn K_sub_Ω (ContDiffMapSupportedIn.fderivCLM 𝕜 n k f) := by
  ext
  simp

variable (𝕜) in
lemma fderivCLM_eq_of_scalars (𝕜' : Type*)
    [NontriviallyNormedField 𝕜'] [NormedSpace 𝕜' F] [Algebra ℝ 𝕜'] [IsScalarTower ℝ 𝕜' F] :
    (fderivCLM 𝕜 n k : 𝓓^{n}(Ω, F) → _) = fderivCLM 𝕜' n k :=
  rfl

end FDerivCLM

section LineDerivCLM

variable [Algebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 F]

variable (𝕜) in
/-- `lineDerivCLM 𝕜 v` is the continuous `𝕜`-linear-map sending `f : 𝓓^{n}_{K}(E, F)` to
its derivative along the vector `v`, which is an element of `𝓓^{k}_{K}(E, F)`.
This only makes mathematical sense if `k + 1 ≤ n`, otherwise we define it as the zero map.

The parameters `n` and `k` are implicit as they can often be inferred from context, or
specified by a type ascription. For `n = k = ⊤`, we also provide instances of the `LineDeriv`
notation typeclass. -/
noncomputable def lineDerivCLM (v : E) :
    𝓓^{n}(Ω, F) →L[𝕜] 𝓓^{k}(Ω, F) :=
  -- Cannot use `ContinuousLinearMap.apply` here because we are mixing `ℝ` and `𝕜`
  letI ev_v : (E →L[ℝ] F) →L[𝕜] F :=
  { toFun f := f v
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  postcompCLM ev_v ∘L fderivCLM 𝕜 n k

lemma lineDerivCLM_eq_fderivCLM {f : 𝓓^{n}(Ω, F)} {v : E} {x : E} :
    (lineDerivCLM 𝕜 v f : 𝓓^{k}(Ω, F)) x = fderivCLM 𝕜 n k f x v :=
  rfl

@[simp]
lemma lineDerivCLM_apply {f : 𝓓^{n}(Ω, F)} {v : E} {x : E} :
    (lineDerivCLM 𝕜 v f : 𝓓^{k}(Ω, F)) x = if k + 1 ≤ n then lineDeriv ℝ f x v else 0 := by
  rw [lineDerivCLM_eq_fderivCLM, fderivCLM_apply]
  split_ifs with hk
  · have hk' : 0 < (n : ℕ∞ω) := mod_cast (ENat.add_one_pos.trans_le hk)
    rw [(f.contDiff.differentiable hk'.ne').differentiableAt.lineDeriv_eq_fderiv]
  · rfl

lemma lineDerivCLM_apply_of_le {f : 𝓓^{n}(Ω, F)} {v : E} {x : E} (hk : k + 1 ≤ n) :
    (lineDerivCLM 𝕜 v f : 𝓓^{k}(Ω, F)) x = lineDeriv ℝ f x v := by
  simp [hk]

lemma lineDerivCLM_apply_of_gt {v : E} (hk : n < k + 1) :
    (lineDerivCLM 𝕜 v : 𝓓^{n}(Ω, F) →L[𝕜] 𝓓^{k}(Ω, F)) = 0 := by
  ext
  simp [not_le_of_gt hk]

variable (𝕜) in
lemma lineDerivCLM_eq_of_scalars (𝕜' : Type*)
    [NontriviallyNormedField 𝕜'] [NormedSpace 𝕜' F] [Algebra ℝ 𝕜'] [IsScalarTower ℝ 𝕜' F]
    {v : E} : (lineDerivCLM 𝕜 v : 𝓓^{n}(Ω, F) → 𝓓^{k}(Ω, F)) = lineDerivCLM 𝕜' v :=
  rfl

lemma lineDerivCLM_add {v₁ v₂ : E} :
    (lineDerivCLM 𝕜 (v₁ + v₂) : 𝓓^{n}(Ω, F) →L[𝕜] 𝓓^{k}(Ω, F)) =
      lineDerivCLM 𝕜 v₁ + lineDerivCLM 𝕜 v₂ := by
  ext
  simp [-lineDerivCLM_apply, lineDerivCLM_eq_fderivCLM]

lemma lineDerivCLM_smul {c : ℝ} {v : E} :
    (lineDerivCLM 𝕜 (c • v) : 𝓓^{n}(Ω, F) →L[𝕜] 𝓓^{k}(Ω, F)) =
      c • lineDerivCLM 𝕜 v := by
  ext
  simp [-lineDerivCLM_apply, lineDerivCLM_eq_fderivCLM]

open LineDeriv

/-- Note: we cannot express the full generality of `lineDerivCLM` purely in terms of this typeclass,
because (by design) the target type `𝓓^{k}_{K}(E, F)` is not determined by the input type
`𝓓^{n}_{K}(E, F)`. -/
noncomputable instance : LineDeriv E 𝓓(Ω, F) 𝓓(Ω, F) where
  lineDerivOp v := lineDerivCLM ℝ v

variable (𝕜) in
lemma lineDerivOp_eq_lineDerivCLM {v : E} {f : 𝓓(Ω, F)} :
    ∂_{v} f = lineDerivCLM 𝕜 v f :=
  rfl

noncomputable instance : LineDerivAdd E 𝓓(Ω, F) 𝓓(Ω, F) where
  lineDerivOp_add v := map_add (lineDerivCLM ℝ v)
  lineDerivOp_left_add _ _ f := congr($lineDerivCLM_add f)

noncomputable instance : LineDerivSMul 𝕜 E 𝓓(Ω, F) 𝓓(Ω, F) where
  lineDerivOp_smul v := map_smul (lineDerivCLM 𝕜 v)

noncomputable instance : LineDerivLeftSMul ℝ E 𝓓(Ω, F) 𝓓(Ω, F) where
  lineDerivOp_left_smul _ _ f := congr($lineDerivCLM_smul f)

noncomputable instance : ContinuousLineDeriv E 𝓓(Ω, F) 𝓓(Ω, F) where
  continuous_lineDerivOp v := (lineDerivCLM ℝ v).continuous

lemma lineDerivOpCLM_eq_lineDerivCLM {v : E} :
    lineDerivOpCLM 𝕜 𝓓(Ω, F) v = lineDerivCLM 𝕜 v :=
  rfl

end LineDerivCLM

end TestFunction
