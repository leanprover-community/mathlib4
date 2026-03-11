/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Anatole Dedecker
-/
module

public import Mathlib.Analysis.LocallyConvex.BalancedCoreHull
public import Mathlib.Analysis.LocallyConvex.Bounded
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Topology.Algebra.Module.Determinant
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.Module.Simple
public import Mathlib.Topology.Algebra.SeparationQuotient.FiniteDimensional

/-!
# Finite-dimensional topological vector spaces over complete fields

Let `𝕜` be a complete nontrivially normed field, and `E` a topological vector space (TVS) over
`𝕜` (i.e we have `[AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]`
and `[ContinuousSMul 𝕜 E]`).

If `E` is finite dimensional and Hausdorff, then all linear maps from `E` to any other TVS are
continuous.

When `E` is a normed space, this gets us the equivalence of norms in finite dimension.

## Main results :

* `LinearMap.continuous_iff_isClosed_ker` : a linear form is continuous if and only if its kernel
  is closed.
* `LinearMap.continuous_of_finiteDimensional` : a linear map on a finite-dimensional Hausdorff
  space over a complete field is continuous.

## TODO

Generalize more of `Mathlib/Analysis/Normed/Module/FiniteDimension.lean` to general TVSs.

## Implementation detail

The main result from which everything follows is the fact that, if `ξ : ι → E` is a finite basis,
then `ξ.equivFun : E →ₗ (ι → 𝕜)` is continuous. However, for technical reasons, it is easier to
prove this when `ι` and `E` live in the same universe. So we start by doing that as a private
lemma, then we deduce `LinearMap.continuous_of_finiteDimensional` from it, and then the general
result follows as `continuous_equivFun_basis`.

-/

@[expose] public section

open Filter Module Set TopologicalSpace Topology

universe u v w x

noncomputable section

section FiniteDimensional

variable {𝕜 E F : Type*}
  [AddCommGroup E] [TopologicalSpace E]
  [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F]

/-- The space of continuous linear maps between finite-dimensional spaces is finite-dimensional. -/
instance ContinuousLinearMap.instModuleFinite [CommRing 𝕜] [Module 𝕜 E] [Module.Finite 𝕜 E]
    [Module 𝕜 F] [IsNoetherian 𝕜 F] [ContinuousConstSMul 𝕜 F] :
    Module.Finite 𝕜 (E →L[𝕜] F) :=
  .of_injective (ContinuousLinearMap.coeLM 𝕜 : (E →L[𝕜] F) →ₗ[𝕜] E →ₗ[𝕜] F)
    ContinuousLinearMap.coe_injective

/-- The space of continuous linear maps between finite-dimensional spaces is finite-dimensional.

This theorem is here to match searches looking for `FiniteDimensional` instead of `Module.Finite`.
We use a strictly more general `ContinuousLinearMap.instModuleFinite` as an instance. -/
protected theorem ContinuousLinearMap.finiteDimensional [Field 𝕜] [Module 𝕜 E]
    [FiniteDimensional 𝕜 E] [Module 𝕜 F] [FiniteDimensional 𝕜 F] [ContinuousConstSMul 𝕜 F] :
    FiniteDimensional 𝕜 (E →L[𝕜] F) :=
  inferInstance

end FiniteDimensional

section NormedField

variable {𝕜 : Type u} [hnorm : NontriviallyNormedField 𝕜] {E : Type v} [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] {F : Type w} [AddCommGroup F]
  [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] {F' : Type x}
  [AddCommGroup F'] [Module 𝕜 F'] [TopologicalSpace F'] [IsTopologicalAddGroup F']
  [ContinuousSMul 𝕜 F']

/-- If `𝕜` is a nontrivially normed field, any T2 topology on `𝕜` which makes it a topological
vector space over itself (with the norm topology) is *equal* to the norm topology. -/
theorem unique_topology_of_t2 {t : TopologicalSpace 𝕜} (h₁ : @IsTopologicalAddGroup 𝕜 t _)
    (h₂ : @ContinuousSMul 𝕜 𝕜 _ hnorm.toUniformSpace.toTopologicalSpace t) (h₃ : @T2Space 𝕜 t) :
    t = hnorm.toUniformSpace.toTopologicalSpace := by
  -- Let `𝓣₀` denote the topology on `𝕜` induced by the norm, and `𝓣` be any T2 vector
  -- topology on `𝕜`. To show that `𝓣₀ = 𝓣`, it suffices to show that they have the same
  -- neighborhoods of 0.
  refine IsTopologicalAddGroup.ext h₁ inferInstance (le_antisymm ?_ ?_)
  · -- To show `𝓣 ≤ 𝓣₀`, we have to show that closed balls are `𝓣`-neighborhoods of 0.
    rw [Metric.nhds_basis_closedBall.ge_iff]
    -- Let `ε > 0`. Since `𝕜` is nontrivially normed, we have `0 < ‖ξ₀‖ < ε` for some `ξ₀ : 𝕜`.
    intro ε hε
    rcases NormedField.exists_norm_lt 𝕜 hε with ⟨ξ₀, hξ₀, hξ₀ε⟩
    -- Since `ξ₀ ≠ 0` and `𝓣` is T2, we know that `{ξ₀}ᶜ` is a `𝓣`-neighborhood of 0.
    have : {ξ₀}ᶜ ∈ @nhds 𝕜 t 0 := IsOpen.mem_nhds isOpen_compl_singleton <|
      mem_compl_singleton_iff.mpr <| Ne.symm <| norm_ne_zero_iff.mp hξ₀.ne.symm
    -- Thus, its balanced core `𝓑` is too. Let's show that the closed ball of radius `ε` contains
    -- `𝓑`, which will imply that the closed ball is indeed a `𝓣`-neighborhood of 0.
    have : balancedCore 𝕜 {ξ₀}ᶜ ∈ @nhds 𝕜 t 0 := balancedCore_mem_nhds_zero this
    refine mem_of_superset this fun ξ hξ => ?_
    -- Let `ξ ∈ 𝓑`. We want to show `‖ξ‖ < ε`. If `ξ = 0`, this is trivial.
    by_cases hξ0 : ξ = 0
    · rw [hξ0]
      exact Metric.mem_closedBall_self hε.le
    · rw [mem_closedBall_zero_iff]
      -- Now suppose `ξ ≠ 0`. By contradiction, let's assume `ε < ‖ξ‖`, and show that
      -- `ξ₀ ∈ 𝓑 ⊆ {ξ₀}ᶜ`, which is a contradiction.
      by_contra! h
      suffices (ξ₀ * ξ⁻¹) • ξ ∈ balancedCore 𝕜 {ξ₀}ᶜ by
        rw [smul_eq_mul, mul_assoc, inv_mul_cancel₀ hξ0, mul_one] at this
        exact notMem_compl_iff.mpr (mem_singleton ξ₀) ((balancedCore_subset _) this)
      -- For that, we use that `𝓑` is balanced : since `‖ξ₀‖ < ε < ‖ξ‖`, we have `‖ξ₀ / ξ‖ ≤ 1`,
      -- hence `ξ₀ = (ξ₀ / ξ) • ξ ∈ 𝓑` because `ξ ∈ 𝓑`.
      refine (balancedCore_balanced _).smul_mem ?_ hξ
      rw [norm_mul, norm_inv, mul_inv_le_iff₀ (norm_pos_iff.mpr hξ0), one_mul]
      exact (hξ₀ε.trans h).le
  · -- Finally, to show `𝓣₀ ≤ 𝓣`, we simply argue that `id = (fun x ↦ x • 1)` is continuous from
    -- `(𝕜, 𝓣₀)` to `(𝕜, 𝓣)` because `(•) : (𝕜, 𝓣₀) × (𝕜, 𝓣) → (𝕜, 𝓣)` is continuous.
    calc
      @nhds 𝕜 hnorm.toUniformSpace.toTopologicalSpace 0 =
          map id (@nhds 𝕜 hnorm.toUniformSpace.toTopologicalSpace 0) :=
        map_id.symm
      _ = map (fun x => id x • (1 : 𝕜)) (@nhds 𝕜 hnorm.toUniformSpace.toTopologicalSpace 0) := by
        simp
      _ ≤ @nhds 𝕜 t ((0 : 𝕜) • (1 : 𝕜)) :=
        (@Tendsto.smul_const _ _ _ hnorm.toUniformSpace.toTopologicalSpace t _ _ _ _ _
          tendsto_id (1 : 𝕜))
      _ = @nhds 𝕜 t 0 := by rw [zero_smul]

/-- Any linear form on a topological vector space over a nontrivially normed field is continuous if
its kernel is closed. -/
theorem LinearMap.continuous_of_isClosed_ker (l : E →ₗ[𝕜] 𝕜)
    (hl : IsClosed (LinearMap.ker l : Set E)) :
    Continuous l := by
  -- `l` is either constant or surjective. If it is constant, the result is trivial.
  by_cases H : finrank 𝕜 (LinearMap.range l) = 0
  · rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at H
    rw [H]
    exact continuous_zero
  · -- In the case where `l` is surjective, we factor it as `φ : (E ⧸ l.ker) ≃ₗ[𝕜] 𝕜`. Note that
    -- `E ⧸ l.ker` is T2 since `l.ker` is closed.
    have : finrank 𝕜 (LinearMap.range l) = 1 :=
      le_antisymm (finrank_self 𝕜 ▸ (LinearMap.range l).finrank_le) (zero_lt_iff.mpr H)
    have hi : Function.Injective ((LinearMap.ker l).liftQ l (le_refl _)) := by
      rw [← LinearMap.ker_eq_bot]
      exact Submodule.ker_liftQ_eq_bot _ _ _ (le_refl _)
    have hs : Function.Surjective ((LinearMap.ker l).liftQ l (le_refl _)) := by
      rw [← LinearMap.range_eq_top, Submodule.range_liftQ]
      exact Submodule.eq_top_of_finrank_eq ((finrank_self 𝕜).symm ▸ this)
    let φ : (E ⧸ LinearMap.ker l) ≃ₗ[𝕜] 𝕜 :=
      LinearEquiv.ofBijective ((LinearMap.ker l).liftQ l (le_refl _)) ⟨hi, hs⟩
    have hlφ : (l : E → 𝕜) = φ ∘ (LinearMap.ker l).mkQ := by ext; rfl
    -- Since the quotient map `E →ₗ[𝕜] (E ⧸ l.ker)` is continuous, the continuity of `l` will follow
    -- form the continuity of `φ`.
    suffices Continuous φ.toEquiv by
      rw [hlφ]
      exact this.comp continuous_quot_mk
    -- The pullback by `φ.symm` of the quotient topology is a T2 topology on `𝕜`, because `φ.symm`
    -- is injective. Since `φ.symm` is linear, it is also a vector space topology.
    -- Hence, we know that it is equal to the topology induced by the norm.
    have : induced φ.toEquiv.symm inferInstance = hnorm.toUniformSpace.toTopologicalSpace := by
      refine unique_topology_of_t2 (topologicalAddGroup_induced φ.symm.toLinearMap)
        (continuousSMul_induced φ.symm.toMulActionHom) ?_
      rw [t2Space_iff]
      exact fun x y hxy =>
        @separated_by_continuous _ _ (induced _ _) _ _ _ continuous_induced_dom _ _
          (φ.toEquiv.symm.injective.ne hxy)
    -- Finally, the pullback by `φ.symm` is exactly the pushforward by `φ`, so we have to prove
    -- that `φ` is continuous when `𝕜` is endowed with the pushforward by `φ` of the quotient
    -- topology, which is trivial by definition of the pushforward.
    simp_rw +instances [this.symm, Equiv.induced_symm]
    exact continuous_coinduced_rng

/-- Any linear form on a topological vector space over a nontrivially normed field is continuous if
and only if its kernel is closed. -/
theorem LinearMap.continuous_iff_isClosed_ker (l : E →ₗ[𝕜] 𝕜) :
    Continuous l ↔ IsClosed (LinearMap.ker l : Set E) :=
  ⟨fun h => isClosed_singleton.preimage h, l.continuous_of_isClosed_ker⟩

/-- Over a nontrivially normed field, any linear form which is nonzero on a nonempty open set is
automatically continuous. -/
theorem LinearMap.continuous_of_nonzero_on_open (l : E →ₗ[𝕜] 𝕜) (s : Set E) (hs₁ : IsOpen s)
    (hs₂ : s.Nonempty) (hs₃ : ∀ x ∈ s, l x ≠ 0) : Continuous l := by
  refine l.continuous_of_isClosed_ker (l.isClosed_or_dense_ker.resolve_right fun hl => ?_)
  rcases hs₂ with ⟨x, hx⟩
  have : x ∈ interior (LinearMap.ker l : Set E)ᶜ := by
    rw [mem_interior_iff_mem_nhds]
    exact mem_of_superset (hs₁.mem_nhds hx) hs₃
  rwa [hl.interior_compl] at this

variable [CompleteSpace 𝕜]

/-- This version imposes `ι` and `E` to live in the same universe, so you should instead use
`continuous_equivFun_basis` which gives the same result without universe restrictions. -/
private theorem continuous_equivFun_basis_aux [T2Space E] {ι : Type v} [Finite ι]
    (ξ : Basis ι 𝕜 E) : Continuous ξ.equivFun := by
  have := Fintype.ofFinite ι
  letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  letI : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  suffices ∀ n, Fintype.card ι = n → Continuous ξ.equivFun by exact this _ rfl
  intro n hn
  induction n generalizing ι E with
  | zero =>
    rw [Fintype.card_eq_zero_iff] at hn
    exact continuous_of_const fun x y => funext hn.elim
  | succ n IH =>
    haveI : FiniteDimensional 𝕜 E := ξ.finiteDimensional_of_finite
    -- first step: thanks to the induction hypothesis, any n-dimensional subspace is equivalent
    -- to a standard space of dimension n, hence it is complete and therefore closed.
    have H₁ : ∀ s : Submodule 𝕜 E, finrank 𝕜 s = n → IsClosed (s : Set E) := by
      intro s s_dim
      letI : IsUniformAddGroup s := s.toAddSubgroup.isUniformAddGroup
      let b := Basis.ofVectorSpace 𝕜 s
      have U : IsUniformEmbedding b.equivFun.symm.toEquiv := by
        have : Fintype.card (Basis.ofVectorSpaceIndex 𝕜 s) = n := by
          rw [← s_dim]
          exact (finrank_eq_card_basis b).symm
        have : Continuous b.equivFun := IH b inferInstance this
        exact
          b.equivFun.symm.isUniformEmbedding b.equivFun.symm.toLinearMap.continuous_on_pi this
      have : IsComplete (s : Set E) :=
        completeSpace_coe_iff_isComplete.1 ((completeSpace_congr U).1 inferInstance)
      exact this.isClosed
    -- second step: any linear form is continuous, as its kernel is closed by the first step
    have H₂ : ∀ f : E →ₗ[𝕜] 𝕜, Continuous f := by
      intro f
      by_cases H : finrank 𝕜 (LinearMap.range f) = 0
      · rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at H
        rw [H]
        exact continuous_zero
      · have : finrank 𝕜 (LinearMap.ker f) = n := by
          have Z := f.finrank_range_add_finrank_ker
          rw [finrank_eq_card_basis ξ, hn] at Z
          have : finrank 𝕜 (LinearMap.range f) = 1 :=
            le_antisymm (finrank_self 𝕜 ▸ (LinearMap.range f).finrank_le) (zero_lt_iff.mpr H)
          rw [this, add_comm, Nat.add_one] at Z
          exact Nat.succ.inj Z
        have : IsClosed (LinearMap.ker f : Set E) := H₁ _ this
        exact LinearMap.continuous_of_isClosed_ker f this
    rw [continuous_pi_iff]
    intro i
    change Continuous (ξ.coord i)
    exact H₂ (ξ.coord i)

/-- A finite-dimensional t2 vector space over a complete field must carry the module topology.

Not declared as a global instance only for performance reasons. -/
@[local instance]
lemma isModuleTopologyOfFiniteDimensional [T2Space E] [FiniteDimensional 𝕜 E] :
    IsModuleTopology 𝕜 E :=
  -- for the proof, go to a model vector space `b → 𝕜` thanks to `continuous_equivFun_basis`, and
  -- use that it has the module topology
  let b := Basis.ofVectorSpace 𝕜 E
  have continuousEquiv : E ≃L[𝕜] (Basis.ofVectorSpaceIndex 𝕜 E) → 𝕜 :=
    { __ := b.equivFun
      continuous_toFun := continuous_equivFun_basis_aux b
      continuous_invFun := IsModuleTopology.continuous_of_linearMap (R := 𝕜)
        (A := (Basis.ofVectorSpaceIndex 𝕜 E) → 𝕜) (B := E) b.equivFun.symm }
  IsModuleTopology.iso continuousEquiv.symm

/-- Any linear map on a finite-dimensional space over a complete field is continuous. -/
theorem LinearMap.continuous_of_finiteDimensional [T2Space E] [FiniteDimensional 𝕜 E]
    (f : E →ₗ[𝕜] F') : Continuous f :=
  IsModuleTopology.continuous_of_linearMap f

instance LinearMap.continuousLinearMapClassOfFiniteDimensional [T2Space E] [FiniteDimensional 𝕜 E] :
    ContinuousLinearMapClass (E →ₗ[𝕜] F') 𝕜 E F' :=
  { LinearMap.semilinearMapClass with map_continuous := fun f => f.continuous_of_finiteDimensional }

/-- In finite dimensions over a non-discrete complete normed field, the canonical identification
(in terms of a basis) with `𝕜^n` (endowed with the product topology) is continuous.
This is the key fact which makes all linear maps from a T2 finite-dimensional TVS over such a field
continuous (see `LinearMap.continuous_of_finiteDimensional`), which in turn implies that all
norms are equivalent in finite dimensions. -/
theorem continuous_equivFun_basis [T2Space E] {ι : Type*} [Finite ι] (ξ : Basis ι 𝕜 E) :
    Continuous ξ.equivFun :=
  haveI : FiniteDimensional 𝕜 E := ξ.finiteDimensional_of_finite
  ξ.equivFun.toLinearMap.continuous_of_finiteDimensional

namespace LinearMap

variable [T2Space E] [FiniteDimensional 𝕜 E]

/-- The continuous linear map induced by a linear map on a finite-dimensional space -/
def toContinuousLinearMap : (E →ₗ[𝕜] F') ≃ₗ[𝕜] E →L[𝕜] F' where
  toFun f := ⟨f, f.continuous_of_finiteDimensional⟩
  invFun := (↑)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  right_inv _ := ContinuousLinearMap.coe_injective rfl

/-- Algebra equivalence between the linear maps and continuous linear maps on a finite-dimensional
space. -/
def _root_.Module.End.toContinuousLinearMap (E : Type v) [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] : (E →ₗ[𝕜] E) ≃ₐ[𝕜] (E →L[𝕜] E) :=
  { LinearMap.toContinuousLinearMap with
    map_mul' := fun _ _ ↦ rfl
    commutes' := fun _ ↦ rfl }

@[simp]
theorem coe_toContinuousLinearMap' (f : E →ₗ[𝕜] F') : ⇑(LinearMap.toContinuousLinearMap f) = f :=
  rfl

@[simp]
theorem coe_toContinuousLinearMap (f : E →ₗ[𝕜] F') :
    ((LinearMap.toContinuousLinearMap f) : E →ₗ[𝕜] F') = f :=
  rfl

@[simp]
theorem coe_toContinuousLinearMap_symm :
    ⇑(toContinuousLinearMap : (E →ₗ[𝕜] F') ≃ₗ[𝕜] E →L[𝕜] F').symm =
      ((↑) : (E →L[𝕜] F') → E →ₗ[𝕜] F') :=
  rfl

@[simp]
theorem det_toContinuousLinearMap (f : E →ₗ[𝕜] E) :
    (LinearMap.toContinuousLinearMap f).det = LinearMap.det f :=
  rfl

@[deprecated coe_toContinuousLinearMap (since := "2025-12-23")]
theorem ker_toContinuousLinearMap (f : E →ₗ[𝕜] F') :
    (LinearMap.toContinuousLinearMap f).ker = ker f := by
  simp

@[deprecated coe_toContinuousLinearMap (since := "2025-12-23")]
theorem range_toContinuousLinearMap (f : E →ₗ[𝕜] F') :
    (LinearMap.toContinuousLinearMap f).range = range f :=
  rfl

/-- A surjective linear map `f` with finite-dimensional codomain is an open map. -/
theorem isOpenMap_of_finiteDimensional (f : F →ₗ[𝕜] E) (hf : Function.Surjective f) :
    IsOpenMap f :=
  IsModuleTopology.isOpenMap_of_surjective hf

instance canLiftContinuousLinearMap : CanLift (E →ₗ[𝕜] F) (E →L[𝕜] F) (↑) fun _ => True :=
  ⟨fun f _ => ⟨LinearMap.toContinuousLinearMap f, rfl⟩⟩

lemma toContinuousLinearMap_eq_iff_eq_toLinearMap (f : E →ₗ[𝕜] E) (g : E →L[𝕜] E) :
    f.toContinuousLinearMap = g ↔ f = g.toLinearMap := by
  simp [ContinuousLinearMap.ext_iff, LinearMap.ext_iff]

lemma _root_.ContinuousLinearMap.toLinearMap_eq_iff_eq_toContinuousLinearMap (g : E →L[𝕜] E)
    (f : E →ₗ[𝕜] E) : g.toLinearMap = f ↔ g = f.toContinuousLinearMap := by
  simp [ContinuousLinearMap.ext_iff, LinearMap.ext_iff]

end LinearMap

section

variable [T2Space E] [T2Space F] [FiniteDimensional 𝕜 E]

namespace LinearEquiv

/-- The continuous linear equivalence induced by a linear equivalence on a finite-dimensional
space. -/
def toContinuousLinearEquiv (e : E ≃ₗ[𝕜] F) : E ≃L[𝕜] F :=
  { e with
    continuous_toFun := e.toLinearMap.continuous_of_finiteDimensional
    continuous_invFun :=
      haveI : FiniteDimensional 𝕜 F := e.finiteDimensional
      e.symm.toLinearMap.continuous_of_finiteDimensional }

@[simp]
theorem coe_toContinuousLinearEquiv (e : E ≃ₗ[𝕜] F) : (e.toContinuousLinearEquiv : E →ₗ[𝕜] F) = e :=
  rfl

@[simp]
theorem coe_toContinuousLinearEquiv' (e : E ≃ₗ[𝕜] F) : (e.toContinuousLinearEquiv : E → F) = e :=
  rfl

@[simp]
theorem coe_toContinuousLinearEquiv_symm (e : E ≃ₗ[𝕜] F) :
    (e.toContinuousLinearEquiv.symm : F →ₗ[𝕜] E) = e.symm :=
  rfl

@[simp]
theorem coe_toContinuousLinearEquiv_symm' (e : E ≃ₗ[𝕜] F) :
    (e.toContinuousLinearEquiv.symm : F → E) = e.symm :=
  rfl

@[simp]
theorem toLinearEquiv_toContinuousLinearEquiv (e : E ≃ₗ[𝕜] F) :
    e.toContinuousLinearEquiv.toLinearEquiv = e := by
  ext x
  rfl

theorem toLinearEquiv_toContinuousLinearEquiv_symm (e : E ≃ₗ[𝕜] F) :
    e.toContinuousLinearEquiv.symm.toLinearEquiv = e.symm := by
  ext x
  rfl

instance canLiftContinuousLinearEquiv :
    CanLift (E ≃ₗ[𝕜] F) (E ≃L[𝕜] F) ContinuousLinearEquiv.toLinearEquiv fun _ => True :=
  ⟨fun f _ => ⟨_, f.toLinearEquiv_toContinuousLinearEquiv⟩⟩

end LinearEquiv

variable [FiniteDimensional 𝕜 F]

/-- Two finite-dimensional topological vector spaces over a complete normed field are continuously
linearly equivalent if they have the same (finite) dimension. -/
theorem FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq
    (cond : finrank 𝕜 E = finrank 𝕜 F) : Nonempty (E ≃L[𝕜] F) :=
  (nonempty_linearEquiv_of_finrank_eq cond).map LinearEquiv.toContinuousLinearEquiv

/-- Two finite-dimensional topological vector spaces over a complete normed field are continuously
linearly equivalent if and only if they have the same (finite) dimension. -/
theorem FiniteDimensional.nonempty_continuousLinearEquiv_iff_finrank_eq :
    Nonempty (E ≃L[𝕜] F) ↔ finrank 𝕜 E = finrank 𝕜 F :=
  ⟨fun ⟨h⟩ => h.toLinearEquiv.finrank_eq, fun h =>
    FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq h⟩

/-- A continuous linear equivalence between two finite-dimensional topological vector spaces over a
complete normed field of the same (finite) dimension. -/
def ContinuousLinearEquiv.ofFinrankEq (cond : finrank 𝕜 E = finrank 𝕜 F) : E ≃L[𝕜] F :=
  (LinearEquiv.ofFinrankEq E F cond).toContinuousLinearEquiv

end

namespace Module.Basis
variable {ι : Type*} [Finite ι] [T2Space E]

/-- Construct a continuous linear map given the value at a finite basis. -/
def constrL (v : Basis ι 𝕜 E) (f : ι → F) : E →L[𝕜] F :=
  haveI : FiniteDimensional 𝕜 E := v.finiteDimensional_of_finite
  LinearMap.toContinuousLinearMap (v.constr 𝕜 f)

@[simp]
theorem coe_constrL (v : Basis ι 𝕜 E) (f : ι → F) : (v.constrL f : E →ₗ[𝕜] F) = v.constr 𝕜 f :=
  rfl

/-- The continuous linear equivalence between a vector space over `𝕜` with a finite basis and
functions from its basis indexing type to `𝕜`. -/
@[simps! apply]
def equivFunL (v : Basis ι 𝕜 E) : E ≃L[𝕜] ι → 𝕜 :=
  { v.equivFun with
    continuous_toFun :=
      haveI : FiniteDimensional 𝕜 E := v.finiteDimensional_of_finite
      v.equivFun.toLinearMap.continuous_of_finiteDimensional
    continuous_invFun := by
      change Continuous v.equivFun.symm.toFun
      exact v.equivFun.symm.toLinearMap.continuous_of_finiteDimensional }

@[simp]
lemma equivFunL_symm_apply_repr (v : Basis ι 𝕜 E) (x : E) :
    v.equivFunL.symm (v.repr x) = x :=
  v.equivFunL.symm_apply_apply x

@[simp]
theorem constrL_apply {ι : Type*} [Fintype ι] (v : Basis ι 𝕜 E) (f : ι → F) (e : E) :
    v.constrL f e = ∑ i, v.equivFun e i • f i :=
  v.constr_apply_fintype 𝕜 _ _

@[simp 1100]
theorem constrL_basis (v : Basis ι 𝕜 E) (f : ι → F) (i : ι) : v.constrL f (v i) = f i :=
  v.constr_basis 𝕜 _ _

end Module.Basis

namespace ContinuousLinearMap

variable [T2Space E] [FiniteDimensional 𝕜 E]

/-- Builds a continuous linear equivalence from a continuous linear map on a finite-dimensional
vector space whose determinant is nonzero. -/
def toContinuousLinearEquivOfDetNeZero (f : E →L[𝕜] E) (hf : f.det ≠ 0) : E ≃L[𝕜] E :=
  ((f : E →ₗ[𝕜] E).equivOfDetNeZero hf).toContinuousLinearEquiv

@[simp]
theorem coe_toContinuousLinearEquivOfDetNeZero (f : E →L[𝕜] E) (hf : f.det ≠ 0) :
    (f.toContinuousLinearEquivOfDetNeZero hf : E →L[𝕜] E) = f := by
  ext x
  rfl

@[simp]
theorem toContinuousLinearEquivOfDetNeZero_apply (f : E →L[𝕜] E) (hf : f.det ≠ 0) (x : E) :
    f.toContinuousLinearEquivOfDetNeZero hf x = f x :=
  rfl

theorem _root_.Matrix.toLin_finTwoProd_toContinuousLinearMap (a b c d : 𝕜) :
    LinearMap.toContinuousLinearMap
      (Matrix.toLin (Basis.finTwoProd 𝕜) (Basis.finTwoProd 𝕜) !![a, b; c, d]) =
      (a • ContinuousLinearMap.fst 𝕜 𝕜 𝕜 + b • ContinuousLinearMap.snd 𝕜 𝕜 𝕜).prod
        (c • ContinuousLinearMap.fst 𝕜 𝕜 𝕜 + d • ContinuousLinearMap.snd 𝕜 𝕜 𝕜) :=
  ContinuousLinearMap.ext <| Matrix.toLin_finTwoProd_apply _ _ _ _

end ContinuousLinearMap

end NormedField

section IsUniformAddGroup

variable (𝕜 E : Type*) [NontriviallyNormedField 𝕜]
  [CompleteSpace 𝕜] [AddCommGroup E] [UniformSpace E] [T2Space E] [IsUniformAddGroup E]
  [Module 𝕜 E] [ContinuousSMul 𝕜 E]

include 𝕜 in
theorem FiniteDimensional.complete [FiniteDimensional 𝕜 E] : CompleteSpace E := by
  set e := ContinuousLinearEquiv.ofFinrankEq (@finrank_fin_fun 𝕜 _ _ (finrank 𝕜 E)).symm
  have : IsUniformEmbedding e.toEquiv.symm := e.symm.isUniformEmbedding
  exact (completeSpace_congr this).1 inferInstance

variable {𝕜 E}

/-- A finite-dimensional subspace is complete. -/
theorem Submodule.complete_of_finiteDimensional (s : Submodule 𝕜 E) [FiniteDimensional 𝕜 s] :
    IsComplete (s : Set E) :=
  haveI : IsUniformAddGroup s := s.toAddSubgroup.isUniformAddGroup
  completeSpace_coe_iff_isComplete.1 (FiniteDimensional.complete 𝕜 s)

end IsUniformAddGroup

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E] [Module 𝕜 E]
  [ContinuousSMul 𝕜 E]
  [AddCommGroup F] [TopologicalSpace F] [T2Space F] [IsTopologicalAddGroup F] [Module 𝕜 F]
  [ContinuousSMul 𝕜 F]

/-- A finite-dimensional subspace is closed. -/
theorem Submodule.closed_of_finiteDimensional
    [T2Space E] (s : Submodule 𝕜 E) [FiniteDimensional 𝕜 s] :
    IsClosed (s : Set E) :=
  letI := IsTopologicalAddGroup.rightUniformSpace E
  haveI : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  s.complete_of_finiteDimensional.isClosed

/-- An injective linear map with finite-dimensional domain is a closed embedding. -/
theorem LinearMap.isClosedEmbedding_of_injective [T2Space E] [FiniteDimensional 𝕜 E] {f : E →ₗ[𝕜] F}
    (hf : LinearMap.ker f = ⊥) : IsClosedEmbedding f :=
  let g := LinearEquiv.ofInjective f (LinearMap.ker_eq_bot.mp hf)
  { IsEmbedding.subtypeVal.comp g.toContinuousLinearEquiv.toHomeomorph.isEmbedding with
    isClosed_range := by
      haveI := f.finiteDimensional_range
      simpa [LinearMap.coe_range f] using (LinearMap.range f).closed_of_finiteDimensional }

theorem isClosedEmbedding_smul_left [T2Space E] {c : E} (hc : c ≠ 0) :
    IsClosedEmbedding fun x : 𝕜 => x • c :=
  LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_toSpanSingleton 𝕜 hc)

-- `smul` is a closed map in the first argument.
theorem isClosedMap_smul_left [T2Space E] (c : E) : IsClosedMap fun x : 𝕜 => x • c := by
  by_cases hc : c = 0
  · simp_rw [hc, smul_zero]
    exact isClosedMap_const
  · exact (isClosedEmbedding_smul_left hc).isClosedMap

theorem ContinuousLinearMap.exists_right_inverse_of_surjective [FiniteDimensional 𝕜 F]
    (f : E →L[𝕜] F) (hf : f.range = ⊤) :
    ∃ g : F →L[𝕜] E, f.comp g = ContinuousLinearMap.id 𝕜 F :=
  let ⟨g, hg⟩ := (f : E →ₗ[𝕜] F).exists_rightInverse_of_surjective hf
  ⟨LinearMap.toContinuousLinearMap g, ContinuousLinearMap.coe_inj.1 hg⟩

/-- If `K` is a complete field and `V` is a finite-dimensional vector space over `K` (equipped with
any topology so that `V` is a topological `K`-module, meaning `[IsTopologicalAddGroup V]`
and `[ContinuousSMul K V]`), and `K` is locally compact, then `V` is locally compact.

This is not an instance because `K` cannot be inferred. -/
theorem LocallyCompactSpace.of_finiteDimensional_of_complete (K V : Type*)
    [NontriviallyNormedField K] [CompleteSpace K] [LocallyCompactSpace K]
    [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [Module K V] [ContinuousSMul K V] [FiniteDimensional K V] :
    LocallyCompactSpace V :=
  -- Reduce to `SeparationQuotient V`, which is a `T2Space`.
  suffices LocallyCompactSpace (SeparationQuotient V) from
    SeparationQuotient.isInducing_mk.locallyCompactSpace <|
      SeparationQuotient.range_mk (X := V) ▸ isClosed_univ.isLocallyClosed
  let ⟨_, ⟨b⟩⟩ := Basis.exists_basis K (SeparationQuotient V)
  have := FiniteDimensional.fintypeBasisIndex b
  b.equivFun.toContinuousLinearEquiv.toHomeomorph.isOpenEmbedding.locallyCompactSpace

section Riesz

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [AddCommGroup E] [UniformSpace E] [T2Space E] [IsUniformAddGroup E]
  [Module 𝕜 E] [ContinuousSMul 𝕜 E]

open scoped Pointwise in
/-- **Riesz's theorem**: a T2 topological vector space over a complete non-trivial normed field
which admits a totally bounded neighborhood of `0` is finite-dimensional. -/
theorem FiniteDimensional.of_totallyBounded_nhds_zero
    {U : Set E} (hU_nhds : U ∈ 𝓝 (0 : E)) (hU_tb : TotallyBounded U) :
    FiniteDimensional 𝕜 E := by
  obtain ⟨c, hc0, hc1⟩ : ∃ c : 𝕜, 0 < ‖c‖ ∧ ‖c‖ < 1 := NormedField.exists_norm_lt 𝕜 zero_lt_one
  have hc_ne : c ≠ 0 := norm_pos_iff.mp hc0
  have hcU_nhds : c • U ∈ 𝓝 (0 : E) := (set_smul_mem_nhds_zero_iff hc_ne).mpr hU_nhds
  obtain ⟨F, hF_finite, hF_subset_raw⟩ :=
    totallyBounded_iff_subset_finite_iUnion_nhds_zero.mp hU_tb (c • U) hcU_nhds
  have hF_subset : U ⊆ F + c • U := fun x hx ↦ by
    have hx_sub := hF_subset_raw hx
    simp only [Set.mem_iUnion] at hx_sub
    rcases hx_sub with ⟨f, hf, v, hv, rfl⟩
    exact Set.add_mem_add hf hv
  let M : Submodule 𝕜 E := Submodule.span 𝕜 F
  haveI hM_fin : FiniteDimensional 𝕜 M := Finite.span_of_finite 𝕜 hF_finite
  have h_ind : ∀ n : ℕ, U ⊆ (M : Set E) + c ^ n • U := by
    intro n
    induction n with
    | zero =>
      intro x hx
      rw [pow_zero, one_smul]
      exact ⟨0, M.zero_mem, x, hx, zero_add x⟩
    | succ n ih =>
      intro x hx
      rcases ih hx with ⟨m, hm, y, ⟨u, hu, rfl⟩, rfl⟩
      rcases hF_subset hu with ⟨f, hf, y', ⟨v, hv, rfl⟩, rfl⟩
      refine ⟨m + c ^ n • f, M.add_mem hm (M.smul_mem (c ^ n) (Submodule.subset_span hf)),
        c ^ (n + 1) • v, ⟨v, hv, rfl⟩, ?_⟩
      simp [smul_add, smul_smul, pow_succ, add_assoc]
  have h_vonN : Bornology.IsVonNBounded 𝕜 U := TotallyBounded.isVonNBounded 𝕜 hU_tb
  have h_U_small : Filter.Tendsto (fun n ↦ c ^ n • U) Filter.atTop (𝓝 0).smallSets :=
    h_vonN.tendsto_smallSets_nhds.comp (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hc1)
  have hU_sub_M : U ⊆ M := fun x hx ↦ by
    choose m hm u hu h_eq using fun n ↦ h_ind n hx
    have hu_tendsto : Filter.Tendsto u Filter.atTop (𝓝 0) := fun W hW ↦
      (Filter.tendsto_smallSets_iff.mp h_U_small W hW).mono fun n hn ↦ hn (hu n)
    have hm_tendsto : Filter.Tendsto m Filter.atTop (𝓝 x) := by
      have : m = fun n ↦ x - u n := funext fun n ↦ eq_sub_of_add_eq (h_eq n)
      rw [this]
      simpa using tendsto_const_nhds.sub hu_tendsto
    exact M.closed_of_finiteDimensional.mem_of_tendsto hm_tendsto (Filter.Eventually.of_forall hm)
  have hM_top : M = ⊤ := eq_top_iff.mpr fun z _ ↦ by
    have h_z_tendsto : Filter.Tendsto (fun n : ℕ ↦ c ^ n • z) Filter.atTop (𝓝 0) := by
      simpa only [zero_smul] using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hc1).smul_const z
    have h_ev : ∀ᶠ n in Filter.atTop, c ^ n • z ∈ U := h_z_tendsto hU_nhds
    obtain ⟨N, hN⟩ := h_ev.exists
    have h_smul : (c ^ N)⁻¹ • c ^ N • z ∈ M := M.smul_mem _ (hU_sub_M hN)
    rwa [smul_smul, inv_mul_cancel₀ (pow_ne_zero N hc_ne), one_smul] at h_smul
  exact FiniteDimensional.of_surjective M.subtype fun x ↦ ⟨⟨x, by simp [hM_top]⟩, rfl⟩

/-- **Riesz's theorem**: in a T2 topological vector space over a complete non-trivial normed field,
if there exists a totally bounded neighborhood of `0`, then the space is finite-dimensional. -/
theorem FiniteDimensional.of_exists_totallyBounded_nhds_zero
    (h : ∃ U ∈ 𝓝 (0 : E), TotallyBounded U) :
    FiniteDimensional 𝕜 E :=
  let ⟨_, hU_nhds, hU_tb⟩ := h
  of_totallyBounded_nhds_zero 𝕜 hU_nhds hU_tb

/-- **Riesz's theorem**: a locally compact topological vector space is finite-dimensional. -/
theorem FiniteDimensional.of_locallyCompactSpace [LocallyCompactSpace E] :
    FiniteDimensional 𝕜 E :=
  let ⟨_, hU_compact, hU_nhds⟩ := exists_compact_mem_nhds (0 : E)
  .of_totallyBounded_nhds_zero 𝕜 hU_nhds hU_compact.totallyBounded

/-- If a function has compact support, then either the function is trivial
or the space is finite-dimensional. -/
theorem HasCompactSupport.eq_zero_or_finiteDimensional {X : Type*}
    [TopologicalSpace X] [Zero X] [T1Space X]
    {f : E → X} (hf : HasCompactSupport f) (h'f : Continuous f) :
    f = 0 ∨ FiniteDimensional 𝕜 E :=
  (HasCompactSupport.eq_zero_or_locallyCompactSpace_of_addGroup hf h'f).imp_right fun h ↦
    have : LocallyCompactSpace E := h; .of_locallyCompactSpace 𝕜

/-- If a function has compact multiplicative support, then either the function is trivial
or the space is finite-dimensional. -/
theorem HasCompactMulSupport.eq_one_or_finiteDimensional {X : Type*}
    [TopologicalSpace X] [One X] [T1Space X]
    {f : E → X} (hf : HasCompactMulSupport f) (h'f : Continuous f) :
    f = 1 ∨ FiniteDimensional 𝕜 E :=
  have : T1Space (Additive X) := ‹_›
  HasCompactSupport.eq_zero_or_finiteDimensional 𝕜 (X := Additive X) hf h'f

end Riesz
