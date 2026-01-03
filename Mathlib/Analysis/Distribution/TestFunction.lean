/-
Copyright (c) 2025 Luigi Massacci. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luigi Massacci, Anatole Dedecker
-/
module

public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

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

variable {𝕜 𝕂 : Type*} [NontriviallyNormedField 𝕜] [RCLike 𝕂]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [NormedSpace 𝕂 F]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [NormedSpace 𝕜 F'] [NormedSpace 𝕂 F']
  {n k : ℕ∞}

variable (Ω F n) in
/-- The type of bundled `n`-times continuously differentiable maps with compact support -/
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

/-- `TestFunctionClass B Ω F n` states that `B` is a type of `n`-times continously
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

@[fun_prop]
protected theorem continuous (f : 𝓓^{n}(Ω, F)) : Continuous f :=
  f.contDiff.continuous

theorem differentiable_withOrder (f : 𝓓^{n}(Ω, F)) (hn : 1 ≤ n) : Differentiable ℝ f :=
  f.contDiff.differentiable (mod_cast hn)

theorem differentiable (f : 𝓓(Ω, F)) : Differentiable ℝ f :=
  f.contDiff.differentiable (by decide)

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

variable (𝕜) in
/-- The natural inclusion `𝓓^{n}_{K}(E, F) → 𝓓^{n}(Ω, F)`, when `K ⊆ Ω`, as a linear map. -/
def ofSupportedInLM [SMulCommClass ℝ 𝕜 F] {K : Compacts E} (K_sub_Ω : (K : Set E) ⊆ Ω) :
    𝓓^{n}_{K}(E, F) →ₗ[𝕜] 𝓓^{n}(Ω, F) where
  toFun f := ofSupportedIn K_sub_Ω f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem coe_ofSupportedInLM [SMulCommClass ℝ 𝕜 F] {K : Compacts E}
    (K_sub_Ω : (K : Set E) ⊆ Ω) :
    (ofSupportedInLM 𝕜 K_sub_Ω : 𝓓^{n}_{K}(E, F) → 𝓓^{n}(Ω, F)) = ofSupportedIn K_sub_Ω :=
  rfl

variable (𝕜 n k) in
/-- `fderivWithOrderLM 𝕜 n k` is the `𝕜`-linear-map sending `f : 𝓓^{n}(Ω, F)` to
its derivative as an element of `𝓓^{k}(Ω, E →L[ℝ] F)`.
This only makes mathematical sense if `k + 1 ≤ n`, otherwise we define it as the zero map.

See `fderivLM` for the very common case where everything is infinitely differentiable.

This is subsumed by `fderivWithOrderCLM`, which also bundles the continuity. -/
noncomputable def fderivWithOrderLM [SMulCommClass ℝ 𝕜 F] :
    𝓓^{n}(Ω, F) →ₗ[𝕜] 𝓓^{k}(Ω, E →L[ℝ] F) where
  toFun f :=
    if hk : k + 1 ≤ n then
      ⟨fderiv ℝ f, f.contDiff.fderiv_right (mod_cast hk),
        f.hasCompactSupport.fderiv ℝ, tsupport_fderiv_subset ℝ |>.trans f.tsupport_subset⟩
    else 0
  map_add' f g := by
    split_ifs with hk
    · have hk' : 1 ≤ (n : WithTop ℕ∞) := mod_cast (le_of_add_le_right hk)
      ext
      simp [fderiv_add (f.contDiff.differentiable hk').differentiableAt
                       (g.contDiff.differentiable hk').differentiableAt]
    · simp
  map_smul' c f := by
    split_ifs with hk
    · have hk' : 1 ≤ (n : WithTop ℕ∞) := mod_cast (le_of_add_le_right hk)
      ext
      simp [fderiv_const_smul (f.contDiff.differentiable hk').differentiableAt]
    · simp

@[simp]
lemma fderivWithOrderLM_apply [SMulCommClass ℝ 𝕜 F] (f : 𝓓^{n}(Ω, F)) :
    fderivWithOrderLM 𝕜 n k f = if k + 1 ≤ n then fderiv ℝ f else 0 := by
  rw [fderivWithOrderLM]
  split_ifs <;> rfl

lemma fderivWithOrderLM_apply_of_le [SMulCommClass ℝ 𝕜 F] (f : 𝓓^{n}(Ω, F)) (hk : k + 1 ≤ n) :
    fderivWithOrderLM 𝕜 n k f = fderiv ℝ f := by
  simp [hk]

lemma fderivWithOrderLM_apply_of_gt [SMulCommClass ℝ 𝕜 F] (f : 𝓓^{n}(Ω, F)) (hk : ¬ (k + 1 ≤ n)) :
    fderivWithOrderLM 𝕜 n k f = 0 := by
  ext : 1
  simp [hk]

variable (𝕜) in
lemma fderivWithOrderLM_eq_of_scalars [SMulCommClass ℝ 𝕜 F] (𝕜' : Type*)
    [NontriviallyNormedField 𝕜'] [NormedSpace 𝕜' F] [SMulCommClass ℝ 𝕜' F] :
    (fderivWithOrderLM 𝕜 n k : 𝓓^{n}(Ω, F) → _) = fderivWithOrderLM 𝕜' n k :=
  rfl

variable (𝕜) in
lemma fderivWithOrderLM_ofSupportedIn [SMulCommClass ℝ 𝕜 F] {K : Compacts E}
    (K_sub_Ω : (K : Set E) ⊆ Ω) (f : 𝓓^{n}_{K}(E, F)) :
    fderivWithOrderLM 𝕜 n k (ofSupportedIn K_sub_Ω f) =
      ofSupportedIn K_sub_Ω (ContDiffMapSupportedIn.fderivWithOrderLM 𝕜 n k f) := by
  ext
  simp

variable (𝕜) in
/-- `fderivLM 𝕜` is the `𝕜`-linear-map sending `f : 𝓓_{K}(E, F)` to
its derivative as an element of `𝓓_{K}(E, E →L[ℝ] F)`.

See also `fderivWithOrderLM` if you need more control on the regularities.

This is subsumed by `fderivCLM`, which also bundles the continuity. -/
noncomputable def fderivLM [SMulCommClass ℝ 𝕜 F] :
    𝓓(Ω, F) →ₗ[𝕜] 𝓓(Ω, E →L[ℝ] F) where
  toFun f := ⟨fderiv ℝ f, f.contDiff.fderiv_right le_rfl, f.hasCompactSupport.fderiv ℝ,
      tsupport_fderiv_subset ℝ |>.trans f.tsupport_subset⟩
  map_add' f g := by
    have h : 1 ≤ ∞ := mod_cast le_top
    ext
    simp [fderiv_add (f.contDiff.differentiable h).differentiableAt
                     (g.contDiff.differentiable h).differentiableAt]
  map_smul' c f := by
    have h : 1 ≤ ∞ := mod_cast le_top
    ext
    simp [fderiv_const_smul (f.contDiff.differentiable h).differentiableAt]

@[simp]
lemma fderivLM_apply [SMulCommClass ℝ 𝕜 F] (f : 𝓓(Ω, F)) :
    fderivLM 𝕜 f = fderiv ℝ f :=
  rfl

/-- Note: this turns out to be a definitional equality thanks to decidablity of the order
on `ℕ∞`. This means we could have *defined* `fderivLM` this way, but we avoid it
to make sure that `if`s won't appear in the smooth case. -/
lemma fderivLM_eq_withOrder [SMulCommClass ℝ 𝕜 F] :
    (fderivLM 𝕜 : 𝓓(Ω, F) →ₗ[𝕜] _) = fderivWithOrderLM 𝕜 ⊤ ⊤ :=
  rfl

variable (𝕜) in
lemma fderivLM_eq_of_scalars [SMulCommClass ℝ 𝕜 F] (𝕜' : Type*) [NontriviallyNormedField 𝕜']
    [NormedSpace 𝕜' F] [SMulCommClass ℝ 𝕜' F] :
    (fderivLM 𝕜 : 𝓓(Ω, F) → _) = fderivLM 𝕜' :=
  rfl

variable (𝕜) in
lemma fderivLM_ofSupportedIn [SMulCommClass ℝ 𝕜 F] {K : Compacts E} (K_sub_Ω : (K : Set E) ⊆ Ω)
    (f : 𝓓_{K}(E, F)) :
    fderivLM 𝕜 (ofSupportedIn K_sub_Ω f) =
      ofSupportedIn K_sub_Ω (ContDiffMapSupportedIn.fderivLM 𝕜 f) :=
  rfl

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
def ofSupportedInCLM [SMulCommClass ℝ 𝕜 F] {K : Compacts E} (K_sub_Ω : (K : Set E) ⊆ Ω) :
    𝓓^{n}_{K}(E, F) →L[𝕜] 𝓓^{n}(Ω, F) where
  toLinearMap := ofSupportedInLM 𝕜 K_sub_Ω
  cont := continuous_ofSupportedIn K_sub_Ω

@[simp] theorem coe_ofSupportedInCLM [SMulCommClass ℝ 𝕜 F] {K : Compacts E}
    (K_sub_Ω : (K : Set E) ⊆ Ω) :
    (ofSupportedInCLM 𝕜 K_sub_Ω : 𝓓^{n}_{K}(E, F) → 𝓓^{n}(Ω, F)) = ofSupportedIn K_sub_Ω :=
  rfl

/-- The **universal property** of the topology on `𝓓^{n}(Ω, F)`: a **linear** map from
`𝓓^{n}(Ω, F)` to a locally convex topological vector space is continuous if and only if its
precomposition with the inclusion `ofSupportedIn K_sub_Ω : 𝓓^{n}_{K}(E, F) → 𝓓^{n}(Ω, F)` is
continuous for every compact `K ⊆ Ω`. -/
protected theorem continuous_iff_continuous_comp [Algebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 F]
    [Module 𝕜 V] [IsScalarTower ℝ 𝕜 V] (f : 𝓓^{n}(Ω, F) →ₗ[𝕜] V) :
    Continuous f ↔ ∀ (K : Compacts E) (K_sub_Ω : (K : Set E) ⊆ Ω),
      Continuous (f ∘ₗ ofSupportedInLM 𝕜 K_sub_Ω) := by
  simp_rw [LinearMap.coe_comp, ← f.coe_restrictScalars ℝ, coe_ofSupportedInLM]
  rw [continuous_iff_le_induced]
  have : @IsTopologicalAddGroup _ (induced (f.restrictScalars ℝ) t) _ :=
    topologicalAddGroup_induced _
  have : @ContinuousSMul ℝ _ _ _ (induced (f.restrictScalars ℝ) t) := continuousSMul_induced _
  have : @LocallyConvexSpace ℝ _ _ _ _ _ (induced (f.restrictScalars ℝ) t) := .induced _
  simp_rw [topologicalSpace_le_iff, originalTop, iSup₂_le_iff, ← continuous_iff_le_induced,
    continuous_coinduced_dom]

end Topology

section postcomp

variable {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [NormedSpace 𝕜 F']
  [NormedSpace 𝕂 F'] [SMulCommClass ℝ 𝕜 F']
variable [SMulCommClass ℝ 𝕜 F]

-- Note: generalizing this to a semilinear setting would require a semilinear version of
-- `CompatibleSMul`.
/-- Given `T : F →L[𝕜] F'`, `postcompLM T` is the `𝕜`-linear-map sending `f : 𝓓^{n}(Ω, F)`
to `T ∘ f` as an element of `𝓓^{n}(Ω, F')`.

This is subsumed by `postcompCLM T`, which also bundles the continuity. -/
noncomputable def postcompLM [LinearMap.CompatibleSMul F F' ℝ 𝕜] (T : F →L[𝕜] F') :
    𝓓^{n}(Ω, F) →ₗ[𝕜] 𝓓^{n}(Ω, F') where
  toFun f := ⟨T ∘ f, T.restrictScalars ℝ |>.contDiff.comp f.contDiff,
    f.hasCompactSupport.comp_left (map_zero _),  by -- TODO: missing API lemma!
      grw [tsupport_comp_subset T.map_zero]; exact f.tsupport_subset⟩
  map_add' f g := by ext x; exact map_add T (f x) (g x)
  map_smul' c f := by ext x; exact map_smul T c (f x)

@[simp]
lemma postcompLM_apply [LinearMap.CompatibleSMul F F' ℝ 𝕜] (T : F →L[𝕜] F')
    (f : 𝓓^{n}(Ω, F)) :
    postcompLM T f = T ∘ f :=
  rfl

@[simp]
lemma postcompLM_ofSupportedIn [LinearMap.CompatibleSMul F F' ℝ 𝕜] {T : F →L[𝕜] F'}
    {K : Compacts E} (K_sub_Ω : (K : Set E) ⊆ Ω) {f : 𝓓^{n}_{K}(E, F)} :
    postcompLM T (ofSupportedIn K_sub_Ω f) = ofSupportedIn K_sub_Ω
      (ContDiffMapSupportedIn.postcompLM T f) :=
  rfl

/-- Given `T : F →L[𝕜] F'`, `postcompCLM T` is the continuous `𝕜`-linear-map sending
`f : 𝓓^{n}(Ω, F)` to `T ∘ f` as an element of `𝓓^{n}(Ω, F')`.

This is subsumed by `postcompCLM T`, which also bundles the continuity. -/
noncomputable def postcompCLM [LinearMap.CompatibleSMul F F' ℝ 𝕜] (T : F →L[𝕜] F') :
    𝓓^{n}(Ω, F) →L[𝕜] 𝓓^{n}(Ω, F') where
  toLinearMap := postcompLM T
  cont := show Continuous (postcompLM (T.restrictScalars ℝ)) by
    rw [TestFunction.continuous_iff_continuous_comp]
    intro K K_sub_Ω
    refine .congr ?_ fun f ↦ (postcompLM_ofSupportedIn K_sub_Ω).symm
    exact (ofSupportedInCLM ℝ K_sub_Ω).comp
      (ContDiffMapSupportedIn.postcompCLM (T.restrictScalars ℝ)) |>.continuous

@[simp]
lemma postcompCLM_apply [LinearMap.CompatibleSMul F F' ℝ 𝕜] (T : F →L[𝕜] F')
    (f : 𝓓^{n}(Ω, F)) :
    postcompCLM T f = T ∘ f :=
  rfl

end postcomp

section FDerivCLM

variable (𝕜 n k) in
/-- `fderivWithOrderCLM 𝕜 n k` is the continuous `𝕜`-linear-map sending `f : 𝓓^{n}_{K}(E, F)` to
its derivative as an element of `𝓓^{k}_{K}(E, E →L[ℝ] F)`.
This only makes mathematical sense if `k + 1 ≤ n`, otherwise we define it as the zero map.

See `fderivCLM` for the very common case where everything is infinitely differentiable. -/
noncomputable def fderivWithOrderCLM [SMulCommClass ℝ 𝕜 F] :
    𝓓^{n}(Ω, F) →L[𝕜] 𝓓^{k}(Ω, E →L[ℝ] F) where
  toLinearMap := fderivWithOrderLM 𝕜 n k
  cont := show Continuous (fderivWithOrderLM 𝕜 n k) by
    rw [fderivWithOrderLM_eq_of_scalars 𝕜 ℝ, TestFunction.continuous_iff_continuous_comp]
    intro K K_sub_Ω
    refine .congr ?_ fun f ↦ (fderivWithOrderLM_ofSupportedIn 𝕜 K_sub_Ω f).symm
    exact (continuous_ofSupportedIn K_sub_Ω).comp
      (ContDiffMapSupportedIn.fderivWithOrderCLM 𝕜 n k).continuous

@[simp]
lemma fderivWithOrderCLM_apply [SMulCommClass ℝ 𝕜 F] (f : 𝓓^{n}(Ω, F)) :
    fderivWithOrderCLM 𝕜 n k f = if k + 1 ≤ n then fderiv ℝ f else 0 :=
  fderivWithOrderLM_apply f

lemma fderivWithOrderCLM_apply_of_le [SMulCommClass ℝ 𝕜 F] (f : 𝓓^{n}(Ω, F)) (hk : k + 1 ≤ n) :
    fderivWithOrderCLM 𝕜 n k f = fderiv ℝ f :=
  fderivWithOrderLM_apply_of_le f hk

lemma fderivWithOrderCLM_apply_of_gt [SMulCommClass ℝ 𝕜 F] (f : 𝓓^{n}(Ω, F)) (hk : ¬ (k + 1 ≤ n)) :
    fderivWithOrderCLM 𝕜 n k f = 0 :=
  fderivWithOrderLM_apply_of_gt f hk

variable (𝕜) in
lemma fderivWithOrderCLM_eq_of_scalars [SMulCommClass ℝ 𝕜 F] (𝕜' : Type*)
    [NontriviallyNormedField 𝕜'] [NormedSpace 𝕜' F] [SMulCommClass ℝ 𝕜' F] :
    (fderivWithOrderLM 𝕜 n k : 𝓓^{n}(Ω, F) → _) = fderivWithOrderLM 𝕜' n k :=
  rfl

variable (𝕜) in
/-- `fderivCLM 𝕜` is the continuous `𝕜`-linear-map sending `f : 𝓓_{K}(E, F)` to
its derivative as an element of `𝓓_{K}(E, E →L[ℝ] F)`.

See also `fderivWithOrderCLM` if you need more control on the regularities. -/
noncomputable def fderivCLM [SMulCommClass ℝ 𝕜 F] :
    𝓓(Ω, F) →L[𝕜] 𝓓(Ω, E →L[ℝ] F) where
  toLinearMap := fderivLM 𝕜
  cont := show Continuous (fderivLM 𝕜) by
    rw [fderivLM_eq_of_scalars 𝕜 ℝ, TestFunction.continuous_iff_continuous_comp]
    intro K K_sub_Ω
    refine .congr ?_ fun f ↦ (fderivLM_ofSupportedIn 𝕜 K_sub_Ω f).symm
    exact (continuous_ofSupportedIn K_sub_Ω).comp
      (ContDiffMapSupportedIn.fderivCLM 𝕜).continuous

@[simp]
lemma fderivCLM_apply [SMulCommClass ℝ 𝕜 F] (f : 𝓓(Ω, F)) :
    fderivCLM 𝕜 f = fderiv ℝ f :=
  rfl

/-- Note: this turns out to be a definitional equality thanks to decidablity of the order
on `ℕ∞`. This means we could have *defined* `fderivLM` this way, but we avoid it
to make sure that `if`s won't appear in the smooth case. -/
lemma fderivCLM_eq_withOrder [SMulCommClass ℝ 𝕜 F] :
    (fderivCLM 𝕜 : 𝓓(Ω, F) →L[𝕜] _) = fderivWithOrderCLM 𝕜 ⊤ ⊤ :=
  rfl

variable (𝕜) in
lemma fderivCLM_eq_of_scalars [SMulCommClass ℝ 𝕜 F] (𝕜' : Type*) [NontriviallyNormedField 𝕜']
    [NormedSpace 𝕜' F] [SMulCommClass ℝ 𝕜' F] :
    (fderivCLM 𝕜 : 𝓓(Ω, F) → _) = fderivCLM 𝕜' :=
  rfl

-- TODO: stuck with `𝕜` due to too strict fields in `ContinuousLinearMap.apply`
variable (n k) in
/-- `fderivWithOrderCLM 𝕜 n k` is the continuous `𝕜`-linear-map sending `f : 𝓓^{n}_{K}(E, F)` to
its derivative as an element of `𝓓^{k}_{K}(E, E →L[ℝ] F)`.
This only makes mathematical sense if `k + 1 ≤ n`, otherwise we define it as the zero map.

See `fderivCLM` for the very common case where everything is infinitely differentiable. -/
noncomputable def lineDerivWithOrderCLM (v : E) :
    𝓓^{n}(Ω, F) →L[ℝ] 𝓓^{k}(Ω, F) :=
  postcompCLM (.apply ℝ F v) ∘L (fderivWithOrderCLM ℝ n k)

@[simp]
lemma lineDerivWithOrderCLM_apply {f : 𝓓^{n}(Ω, F)} {x v : E} :
    lineDerivWithOrderCLM n k v f x = if k + 1 ≤ n then lineDeriv ℝ f x v else 0 := by
  by_cases hk : k + 1 ≤ n
  · have : 1 ≤ n := le_of_add_le_right hk
    simp [lineDerivWithOrderCLM, hk,
          (f.differentiable_withOrder this).differentiableAt.lineDeriv_eq_fderiv]
  · simp [lineDerivWithOrderCLM, hk]

lemma lineDerivWithOrderCLM_apply_of_le {f : 𝓓^{n}(Ω, F)} {x v : E} (hk : k + 1 ≤ n) :
    lineDerivWithOrderCLM n k v f x = lineDeriv ℝ f x v := by
  simp [hk]

lemma lineDerivWithOrderCLM_apply_of_gt {v : E} (hk : ¬ (k + 1 ≤ n)) :
    (lineDerivWithOrderCLM n k v : 𝓓^{n}(Ω, F) →L[ℝ] 𝓓^{k}(Ω, F)) = 0 := by
  ext
  simp [hk]

-- TODO: stuck with `𝕜` due to too strict fields in `ContinuousLinearMap.apply`
/-- `fderivCLM 𝕜` is the continuous `𝕜`-linear-map sending `f : 𝓓_{K}(E, F)` to
its derivative as an element of `𝓓_{K}(E, E →L[ℝ] F)`.

See also `fderivWithOrderCLM` if you need more control on the regularities. -/
noncomputable def lineDerivCLM (v : E) :
    𝓓(Ω, F) →L[ℝ] 𝓓(Ω, F) :=
  postcompCLM (.apply ℝ F v) ∘L (fderivCLM ℝ)

@[simp]
lemma lineDerivCLM_apply {f : 𝓓(Ω, F)} {x v : E} :
    lineDerivCLM v f x = lineDeriv ℝ f x v := by
  simp [lineDerivCLM, f.differentiable.differentiableAt.lineDeriv_eq_fderiv]

/-- Note: this turns out to be a definitional equality thanks to decidablity of the order
on `ℕ∞`. This means we could have *defined* `lineDerivCLM` this way, but we avoid it
to make sure that `if`s won't appear in the smooth case. -/
lemma lineDerivCLM_eq_withOrder {v : E} :
    (lineDerivCLM v : 𝓓(Ω, F) →L[ℝ] _) = lineDerivWithOrderCLM ⊤ ⊤ v :=
  rfl

end FDerivCLM

section Integral

open MeasureTheory

variable {m : MeasurableSpace E} [OpensMeasurableSpace E] {F₁ F₂ F₃ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]

@[fun_prop]
protected theorem stronglyMeasurable (f : 𝓓^{n}(Ω, F)) :
    StronglyMeasurable f := by
  exact f.continuous.stronglyMeasurable_of_hasCompactSupport f.hasCompactSupport

@[fun_prop]
protected theorem aestronglyMeasurable {μ : Measure E} (f : 𝓓^{n}(Ω, F)) :
    AEStronglyMeasurable f μ :=
  f.stronglyMeasurable.aestronglyMeasurable

protected theorem memLp_top {μ : Measure E} (f : 𝓓^{n}(Ω, F)) :
    MemLp f ⊤ μ :=
  f.continuous.memLp_top_of_hasCompactSupport f.hasCompactSupport μ

protected theorem integrable {μ : Measure E}
    (H : ∀ K : Set E, IsCompact K → K ⊆ Ω → IsFiniteMeasure (μ.restrict K)) -- TODO
    (f : 𝓓^{n}(Ω, F)) : Integrable f μ := by
  rw [← integrableOn_iff_integrable_of_support_subset (subset_tsupport f)]
  specialize H (tsupport f) f.hasCompactSupport f.tsupport_subset
  exact f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport

protected theorem integrable_bilin (B : F₁ →L[𝕜] F₂ →L[𝕜] F₃) {μ : Measure E} {φ : E → F₂}
    (hφ : LocallyIntegrableOn φ Ω μ) (f : 𝓓^{n}(Ω, F₁)) :
    Integrable (fun x ↦ B (f x) (φ x)) μ := by
  suffices IntegrableOn (fun x ↦ B (f x) (φ x)) (tsupport f) μ by
    rwa [integrableOn_iff_integrable_of_support_subset] at this
    refine subset_trans ?_ (subset_tsupport f)
    exact fun x hx hfx ↦ hx (by simp [hfx])
  replace hφ := hφ.integrableOn_compact_subset f.tsupport_subset f.hasCompactSupport
  rw [IntegrableOn, ← memLp_one_iff_integrable] at hφ ⊢
  exact B.memLp_of_bilin 1 f.memLp_top hφ

variable [SMulCommClass ℝ 𝕜 F₁] [NormedSpace ℝ F₃] [SMulCommClass ℝ 𝕜 F₃]

noncomputable def integralAgainstBilinLM (B : F₁ →L[𝕜] F₂ →L[𝕜] F₃) (μ : Measure E) (φ : E → F₂) :
    𝓓^{n}(Ω, F₁) →ₗ[𝕜] F₃ where
  toFun f := open scoped Classical in
    if LocallyIntegrableOn φ Ω μ then ∫ x, B (f x) (φ x) ∂μ else 0
  map_add' f g := by
    split_ifs with hφ
    · simp_rw [coe_add, Pi.add_apply, map_add, ContinuousLinearMap.add_apply,
        integral_add (f.integrable_bilin B hφ) (g.integrable_bilin B hφ)]
    · simp
  map_smul' c f := by
    split_ifs with hφ
    · simp_rw [coe_smul, Pi.smul_apply, map_smul, ContinuousLinearMap.smul_apply,
        integral_smul c, RingHom.id_apply]
    · simp

@[simp]
lemma integralAgainstBilinLM_apply {B : F₁ →L[𝕜] F₂ →L[𝕜] F₃} {μ : Measure E} {φ : E → F₂}
    (hφ : LocallyIntegrableOn φ Ω μ) {f : 𝓓^{n}(Ω, F₁)} :
    integralAgainstBilinLM B μ φ f = ∫ x, B (f x) (φ x) ∂μ := by
  simp [integralAgainstBilinLM, hφ]

lemma integralAgainstBilinLM_eq_zero {B : F₁ →L[𝕜] F₂ →L[𝕜] F₃} {μ : Measure E} {φ : E → F₂}
    (hφ : ¬ LocallyIntegrableOn φ Ω μ) :
    (integralAgainstBilinLM B μ φ : 𝓓^{n}(Ω, F₁) →ₗ[𝕜] F₃) = 0 := by
  ext
  simp [integralAgainstBilinLM, hφ]

lemma integralAgainstBilinLM_ofSupportedIn {B : F₁ →L[𝕜] F₂ →L[𝕜] F₃} {μ : Measure E} {φ : E → F₂}
    (hφ : LocallyIntegrableOn φ Ω μ) {K : Compacts E} (K_sub_Ω : (K : Set E) ⊆ Ω)
    {f : 𝓓^{n}_{K}(E, F₁)} :
    integralAgainstBilinLM B μ φ (ofSupportedIn K_sub_Ω f) =
      ContDiffMapSupportedIn.integralAgainstBilinLM B μ φ f := by
  have hφ' := hφ.integrableOn_compact_subset K_sub_Ω K.isCompact
  simp [hφ, hφ']

variable [NormedSpace ℝ F₂]

-- TODO: generalize to 𝕜
noncomputable def integralAgainstBilinCLM (B : F₁ →L[ℝ] F₂ →L[ℝ] F₃) (μ : Measure E) (φ : E → F₂) :
    𝓓^{n}(Ω, F₁) →L[ℝ] F₃ where
  toLinearMap := integralAgainstBilinLM B μ φ
  cont := show Continuous (integralAgainstBilinLM B μ φ) by
    rw [TestFunction.continuous_iff_continuous_comp]
    intro K K_sub_Ω
    by_cases hφ : LocallyIntegrableOn φ Ω μ
    · refine .congr ?_ fun f ↦ (integralAgainstBilinLM_ofSupportedIn hφ K_sub_Ω).symm
      exact ContDiffMapSupportedIn.integralAgainstBilinCLM B μ φ |>.continuous
    · simpa [integralAgainstBilinLM_eq_zero hφ] using continuous_zero

@[simp]
lemma integralAgainstBilinCLM_apply {B : F₁ →L[ℝ] F₂ →L[ℝ] F₃} {μ : Measure E} {φ : E → F₂}
    (hφ : LocallyIntegrableOn φ Ω μ) {f : 𝓓^{n}(Ω, F₁)} :
    integralAgainstBilinCLM B μ φ f = ∫ x, B (f x) (φ x) ∂μ :=
  integralAgainstBilinLM_apply hφ

lemma integralAgainstBilinCLM_eq_zero {B : F₁ →L[ℝ] F₂ →L[ℝ] F₃} {μ : Measure E} {φ : E → F₂}
    (hφ : ¬ LocallyIntegrableOn φ Ω μ) :
    (integralAgainstBilinCLM B μ φ : 𝓓^{n}(Ω, F₁) →L[ℝ] F₃) = 0 := by
  ext
  simp [integralAgainstBilinCLM, integralAgainstBilinLM_eq_zero hφ]

end Integral

end TestFunction

end
