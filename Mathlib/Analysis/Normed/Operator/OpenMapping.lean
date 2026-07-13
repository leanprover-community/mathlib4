/-
Copyright (c) 2026 Kevin H. Wilson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin H. Wilson
-/
module

public import Mathlib.Analysis.LocallyConvex.BalancedCoreHull
public import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.Absorbent

/-!
# Open Mapping Theorem over Nontrivially Normed Fields

The open mapping theorem states that a surjective continuous linear map between two vector spaces
is _open_ if the underlying fields admit a nontrivial norm, the vector spaces are complete, have
a first countable topology, and the _target_ space is Hausdorff.

In the case that the vector spaces are Banach spaces (i.e., are normed spaces), then another
statement of the open mapping theorem is that every bounded linear bijection between Banach spaces
admits a bounded (not-necessarily linear!) inverse. This is
`exists_nonlinearRightInverse_of_surjective` in `Mathlib/Analysis/Normed/Operator/Banach.lean`.

TODO: The existence of such a right inverse does not extend as generally as the fact that the map is
open. However, there does exist such a right inverse when the underlying spaces are
_locally convex_. This is a consequence of Michael's Selection Theorem.

TODO: There is also a generalization of the open mapping theorem to arbitrary topological groups `G`
which admit a _contraction_ `c : G =ₜ G`, i.e., a homeomorphism such that, for every neighborhood
`s` of the identity, for every `x ∈ G`, there is some `n : ℕ` such that `(c ^ n) x ∈ s`.
-/

@[expose] public section

open Set Filter Topology Uniformity Function
open scoped Pointwise

variable {𝕜₁ 𝕜₂ : Type*} [NontriviallyNormedField 𝕜₁] [NontriviallyNormedField 𝕜₂]
  {σ : 𝕜₁ →+* 𝕜₂} [RingHomIsometric σ]
  {E : Type*} [AddCommGroup E] [Module 𝕜₁ E] [UniformSpace E] [IsUniformAddGroup E]
    [ContinuousSMul 𝕜₁ E] [FirstCountableTopology E] [CompleteSpace E]
  {F : Type*} [AddCommGroup F] [Module 𝕜₂ F] [UniformSpace F] [IsUniformAddGroup F]
    [ContinuousSMul 𝕜₂ F] [FirstCountableTopology F] [CompleteSpace F] [T2Space F]
  (f : E →SL[σ] F)

namespace ContinuousLinearMap

section

omit [FirstCountableTopology E] [CompleteSpace E] in
theorem closure_image_nhds_zero_of_surjective (hf : Surjective f)
    {V : Set E} (hV : V ∈ 𝓝 0) : closure (f '' V) ∈ 𝓝 0 := by
  -- Restrict scalars
  letI : Module 𝕜₁ F := Module.compHom F σ
  have hσ : Continuous σ :=
    (AddMonoidHomClass.isometry_of_norm σ fun _ ↦ RingHomIsometric.norm_map).continuous
  haveI : ContinuousSMul 𝕜₁ F := ⟨(hσ.comp continuous_fst).smul continuous_snd⟩
  haveI : (𝓤 F).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero F]
    infer_instance
  -- Since `V` is a neighborhood of `0`, pick a balanced neighborhood `U` of `0` with `U + U ⊆ V`.
  obtain ⟨U₀, hU₀_mem, hU₀_add⟩ := exists_nhds_zero_half hV
  set U := balancedCore 𝕜₁ U₀ with hU_def
  have hU_mem : U ∈ 𝓝 0 := balancedCore_mem_nhds_zero hU₀_mem
  have hU_bal : Balanced 𝕜₁ U := balancedCore_balanced U₀
  -- `B := closure (f '' U)` is symmetric and, being a closed absorbent set in a Baire space, has
  -- nonempty interior. Then `interior B - interior B` is a neighborhood of `0` inside
  -- `closure (f '' V)`, because `f '' U + f '' U = f '' (U + U) ⊆ f '' V`.
  let B := closure (f '' U)
  have hB_neg_eq : B = -B := by
    simp_rw [B, neg_closure, ← U.image_neg f, hU_bal.neg_eq]
  obtain ⟨y₀, hy₀⟩ : (interior B).Nonempty :=
    (((absorbent_nhds_zero hU_mem).image_of_surjective hf
      (map_smulₛₗ f)).mono subset_closure).interior_nonempty isClosed_closure
  refine mem_nhds_iff.mpr ⟨interior B - interior B, ?_, isOpen_interior.sub_right, ?_⟩
  · calc interior B - interior B
        ⊆ B - B := Set.sub_subset_sub interior_subset interior_subset
      _ = B + B := by rw [sub_eq_add_neg, ← hB_neg_eq]
      _ ⊆ closure (f '' U + f '' U) := subset_closure_add
      _ ⊆ closure (f '' V) := by
        gcongr
        rintro _ ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
        exact ⟨a + b, hU₀_add a (balancedCore_subset _ ha) b (balancedCore_subset _ hb),
          by rw [map_add]⟩
  · simpa using Set.sub_mem_sub hy₀ hy₀

/-- **Open mapping theorem.** A continuous surjective `σ`-semilinear map between complete,
first-countable, Hausdorff topological vector spaces over nontrivially normed fields, with `σ` an
isometric ring homomorphism between the scalar fields) is an open map. -/
theorem isOpenMap (hf : Surjective f) : IsOpenMap f := by
  -- Suffices to show that every neighborhood of 0 in a basis maps to a neighborhood of 0
  obtain ⟨U, hU⟩ := (nhds_basis_opens (0 : E)).exists_antitone_subbasis
  obtain ⟨φ, hφ_basis, hφ⟩ := hU.2.exists_subbasis_add_closure_subset
  simp_rw [forall_and] at hφ
  obtain ⟨hadd, hclosure⟩ := hφ
  have hφ_mem (n : ℕ) : U (φ n) ∈ 𝓝 0 := hφ_basis.mem_of_mem trivial
  rw [IsTopologicalAddGroup.isOpenMap_iff_nhds_zero, (hφ_basis.map f).ge_iff]
  intro n _
  -- Step 1: The closure of the image of `U (φ m)` is a neighborhood of `0`
  have baire (m : ℕ) : closure (f '' U (φ m)) ∈ 𝓝 0 :=
    f.closure_image_nhds_zero_of_surjective hf (hφ_mem m)
  -- Step 2: Suffices to show `closure (f '' U (φ (n + 2))) ⊆ f '' U (φ n)`
  refine Filter.mem_of_superset (baire (n + 2)) ?_
  -- Step 3: For any `w ∈ closure (f '' U (φ m))`, we can always find some `x ∈ U (φ m)` such that
  -- `w - f x ∈ closure (f '' U (φ (m + 1)))`
  have step (m : ℕ) (w : F) (hw : w ∈ closure (f '' U (φ m))) :
      ∃ x ∈ U (φ m), (w - f x) ∈ closure (f '' U (φ (m + 1))) := by
    have : {p : F | w - p ∈ closure (f '' U (φ (m + 1)))} ∈ 𝓝 w := by
      apply ContinuousAt.preimage_mem_nhds (by fun_prop)
      simpa using baire (m + 1)
    obtain ⟨p, hp, x, hx, rfl⟩ := mem_closure_iff_nhds.mp hw _ this
    refine ⟨x, hx, hp⟩
  -- Step 4: Find an element `x₀ ∈ U (φ (n + 2))` such that `f x₀` is close to `y`. Then using
  -- Step 3 refine the residuals, finding elements in smaller and smaller `U (φ ·)`s
  intro y hy
  choose! x_gen hx_gen hx_gen' using step
  let yᵢ : ℕ → F := fun k ↦ k.recOn y (fun m ym ↦ ym - f (x_gen (n + 2 + m) ym))
  let xᵢ : ℕ → E := fun m ↦ x_gen (n + 2 + m) (yᵢ m)
  let sᵢ : ℕ → E := fun m ↦ (Finset.range m).sum xᵢ
  -- The residuals `yᵢ k` stay in the closure of the image of the shrinking neighborhoods, so each
  -- generated step `xᵢ k` lies in `U (φ (n + 2 + k))`.
  have hyᵢ (k : ℕ) : yᵢ k ∈ closure (f '' U (φ (n + 2 + k))) := by
    induction k with
    | zero => exact hy
    | succ k ih => exact hx_gen' (n + 2 + k) (yᵢ k) ih
  have hxᵢ (k : ℕ) : xᵢ k ∈ U (φ (n + 2 + k)) := hx_gen (n + 2 + k) (yᵢ k) (hyᵢ k)
  have : CauchySeq sᵢ := by
    have hunif : (𝓤 E).HasAntitoneBasis fun i ↦ {x : E × E | x.2 - x.1 ∈ U (φ i)} :=
      ⟨hφ_basis.uniformity_of_nhds_zero, fun _ _ hij _ hx ↦ hφ_basis.antitone hij hx⟩
    refine hunif.cauchySeq_of_succ (fun k ↦ ?_) (fun k ↦ ?_)
    · intro ⟨a, c⟩ ⟨b, hab, hbc⟩
      simpa using hadd k (Set.add_mem_add hbc hab)
    · simpa [sᵢ, Finset.sum_range_succ] using hφ_basis.antitone (by lia) (hxᵢ k)
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete this
  refine ⟨x, hclosure n (mem_closure_of_tendsto hx (Eventually.of_forall ?_)), ?_⟩
  · -- Each partial sum lands in `U (φ (n + 1))`: peeling off the first term and using
    -- `U (φ (k + 1)) + U (φ (k + 1)) ⊆ U (φ k)` telescopes the shrinking tail into a fixed
    -- neighborhood.
    have aux (p) : ∀ j, (∑ l ∈ Finset.range p, xᵢ (j + l)) ∈ U (φ (n + 1 + j)) := by
      induction p with
      | zero => intro j; simpa using mem_of_mem_nhds (hφ_mem (n + 1 + j))
      | succ p ih =>
        intro j
        rw [Finset.sum_range_succ']
        refine hadd _ (Set.add_mem_add ?_ (hφ_basis.antitone (by lia) (hxᵢ j)))
        simpa only [Function.comp, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih (j + 1)
    intro m
    simpa using aux m 0
  · refine tendsto_nhds_unique ((f.continuous.tendsto x).comp hx) ?_
    have hf : f ∘ sᵢ = fun m ↦ y - yᵢ m := by
      ext m
      induction m with
      | zero => simp [sᵢ, yᵢ]
      | succ m ih => grind [Finset.sum_range_succ]
    -- The residuals `yᵢ m ∈ closure (f '' U (φ (n + 2 + m)))` are squeezed into every closed
    -- neighborhood of `0`, so they tend to `0`.
    have hy_tendsto : Tendsto yᵢ atTop (𝓝 0) := by
      apply (closed_nhds_basis 0).tendsto_right_iff.mpr
      intro U ⟨hU_nhds, hU_closed⟩
      obtain ⟨j, hj⟩ := hφ_basis.mem_iff.mp
        (f.continuous.continuousAt.preimage_mem_nhds (by simpa using hU_nhds))
      filter_upwards [Filter.eventually_ge_atTop j] with m hm
      refine closure_minimal ?_ hU_closed (hyᵢ m)
      rintro _ ⟨z, hz, rfl⟩
      exact hj (hφ_basis.antitone (by lia) hz)
    simpa [hf] using tendsto_const_nhds.sub hy_tendsto

theorem isQuotientMap (surj : Surjective f) : IsQuotientMap f :=
  (f.isOpenMap surj).isQuotientMap f.continuous surj

end

/-! ### Applications of the open mapping theorem -/

section

theorem interior_preimage (hsurj : Surjective f) (s : Set F) :
    interior (f ⁻¹' s) = f ⁻¹' interior s :=
  ((f.isOpenMap hsurj).preimage_interior_eq_interior_preimage f.continuous s).symm

theorem closure_preimage (hsurj : Surjective f) (s : Set F) : closure (f ⁻¹' s) = f ⁻¹' closure s :=
  ((f.isOpenMap hsurj).preimage_closure_eq_closure_preimage f.continuous s).symm

theorem frontier_preimage (hsurj : Surjective f) (s : Set F) :
    frontier (f ⁻¹' s) = f ⁻¹' frontier s :=
  ((f.isOpenMap hsurj).preimage_frontier_eq_frontier_preimage f.continuous s).symm

end

end ContinuousLinearMap

namespace LinearEquiv

variable {σ' : 𝕜₂ →+* 𝕜₁} [RingHomInvPair σ' σ] [RingHomInvPair σ σ']

/-- If a continous linear map is a bijection, then its inverse is also continuous. -/
@[continuity]
theorem continuous_symm (e : E ≃ₛₗ[σ] F) (h : Continuous e) : Continuous e.symm := by
  rw [continuous_def]
  intro s hs
  rw [← e.image_eq_preimage_symm]
  rw [← e.coe_coe] at h ⊢
  exact ContinuousLinearMap.isOpenMap (σ := σ) ⟨_, h⟩ e.surjective s hs

/-- Associating to a linear equivalence a continuous linear equivalence when the direct map is
continuous, thanks to the open mapping theorem that ensures that the inverse map is also
continuous. -/
def toContinuousLinearEquivOfContinuous (e : E ≃ₛₗ[σ] F) (h : Continuous e) : E ≃SL[σ] F :=
  { e with
    continuous_toFun := h
    continuous_invFun := e.continuous_symm h }

@[simp]
theorem coeFn_toContinuousLinearEquivOfContinuous (e : E ≃ₛₗ[σ] F) (h : Continuous e) :
    ⇑(e.toContinuousLinearEquivOfContinuous h) = e :=
  rfl

@[simp]
theorem coeFn_toContinuousLinearEquivOfContinuous_symm (e : E ≃ₛₗ[σ] F) (h : Continuous e) :
    ⇑(e.toContinuousLinearEquivOfContinuous h).symm = e.symm :=
  rfl

end LinearEquiv

namespace ContinuousLinearMap

section

variable {σ' : 𝕜₂ →+* 𝕜₁} [RingHomInvPair σ' σ] [RingHomInvPair σ σ']

/-- An injective continuous linear map with a closed range defines a continuous linear equivalence
between its domain and its range. -/
noncomputable def equivRange (hinj : Injective f) (hclo : IsClosed (range f)) :
    E ≃SL[σ] f.range :=
  letI : IsUniformAddGroup f.range := f.range.toAddSubgroup.isUniformAddGroup
  letI : FirstCountableTopology f.range :=
    inferInstanceAs (FirstCountableTopology (f.range : Set F))
  have : CompleteSpace f.range := hclo.completeSpace_coe
  LinearEquiv.toContinuousLinearEquivOfContinuous (LinearEquiv.ofInjective f.toLinearMap hinj) <|
    (f.continuous.codRestrict fun x ↦ f.mem_range_self x).congr fun _ ↦ rfl

@[simp]
theorem coe_linearMap_equivRange (hinj : Injective f) (hclo : IsClosed (range f)) :
    f.equivRange hinj hclo = f.rangeRestrict :=
  rfl

@[simp]
theorem coe_equivRange (hinj : Injective f) (hclo : IsClosed (range f)) :
    (f.equivRange hinj hclo : E → f.range) = f.rangeRestrict :=
  rfl

@[simp]
lemma equivRange_symm_toLinearEquiv (hinj : Injective f) (hclo : IsClosed (range f)) :
    (f.equivRange hinj hclo).toLinearEquiv.symm =
      (LinearEquiv.ofInjective f.toLinearMap hinj).symm := rfl

@[simp]
lemma equivRange_symm_apply (hinj : Injective f) (hclo : IsClosed (range f))
    (x : E) : (f.equivRange hinj hclo).symm ⟨f x, by simp⟩ = x := by
  simp [ContinuousLinearEquiv.symm_apply_eq, Subtype.ext_iff]

end

end ContinuousLinearMap

namespace ContinuousLinearEquiv

variable {σ' : 𝕜₂ →+* 𝕜₁} [RingHomInvPair σ' σ] [RingHomInvPair σ σ']

/-- Convert a bijective continuous linear map `f : E →SL[σ] F` to a continuous linear
equivalence. -/
noncomputable def ofBijective (f : E →SL[σ] F) (hinj : f.ker = ⊥) (hsurj : f.range = ⊤) :
    E ≃SL[σ] F :=
  (LinearEquiv.ofBijective f
        ⟨LinearMap.ker_eq_bot.mp hinj,
          LinearMap.range_eq_top.mp hsurj⟩).toContinuousLinearEquivOfContinuous
    (by exact f.continuous)

@[simp]
theorem coeFn_ofBijective (f : E →SL[σ] F) (hinj : f.ker = ⊥) (hsurj : f.range = ⊤) :
    ⇑(ofBijective f hinj hsurj) = f :=
  rfl

theorem coe_ofBijective (f : E →SL[σ] F) (hinj : f.ker = ⊥) (hsurj : f.range = ⊤) :
    ↑(ofBijective f hinj hsurj) = f := by
  ext
  rfl

@[simp]
theorem ofBijective_symm_apply_apply (f : E →SL[σ] F) (hinj : f.ker = ⊥) (hsurj : f.range = ⊤)
    (x : E) : (ofBijective f hinj hsurj).symm (f x) = x :=
  (ofBijective f hinj hsurj).symm_apply_apply x

@[simp]
theorem ofBijective_apply_symm_apply (f : E →SL[σ] F) (hinj : f.ker = ⊥)
    (hsurj : f.range = ⊤) (y : F) : f ((ofBijective f hinj hsurj).symm y) = y :=
  (ofBijective f hinj hsurj).apply_symm_apply y

end ContinuousLinearEquiv

/-! ### The closed graph theorem -/

section ClosedGraphThm

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [AddCommGroup E] [Module 𝕜 E] [UniformSpace E] [IsUniformAddGroup E]
    [ContinuousSMul 𝕜 E] [FirstCountableTopology E] [CompleteSpace E] [T2Space E]
  {F : Type*} [AddCommGroup F] [Module 𝕜 F] [UniformSpace F] [IsUniformAddGroup F]
    [ContinuousSMul 𝕜 F] [FirstCountableTopology F] [CompleteSpace F]
  (g : E →ₗ[𝕜] F)

/-- The **closed graph theorem**: a linear map between two complete, first-countable topological
vector spaces over a nontrivially normed field, with Hausdorff domain, whose graph is closed is
continuous. -/
theorem LinearMap.continuous_of_isClosed_graph (hg : IsClosed (g.graph : Set <| E × F)) :
    Continuous g := by
  letI : CompleteSpace g.graph := completeSpace_coe_iff_isComplete.mpr hg.isComplete
  letI : IsUniformAddGroup g.graph := g.graph.toAddSubgroup.isUniformAddGroup
  letI : FirstCountableTopology g.graph :=
    inferInstanceAs (FirstCountableTopology (g.graph : Set (E × F)))
  let φ₀ : E →ₗ[𝕜] E × F := LinearMap.id.prod g
  have : Function.LeftInverse Prod.fst φ₀ := fun x => rfl
  let φ : E ≃ₗ[𝕜] g.graph :=
    (LinearEquiv.ofLeftInverse this).trans (LinearEquiv.ofEq _ _ g.graph_eq_range_prod.symm)
  let ψ : g.graph ≃L[𝕜] E :=
    φ.symm.toContinuousLinearEquivOfContinuous continuous_subtype_val.fst
  exact (continuous_subtype_val.comp ψ.symm.continuous).snd

/-- A useful form of the **closed graph theorem**: to show that a linear map `g` is continuous,
it suffices to show that for any convergent sequence `uₙ ⟶ x`, if `g(uₙ) ⟶ y` then `y = g(x)`. -/
theorem LinearMap.continuous_of_seq_closed_graph
    (hg : ∀ (u : ℕ → E) (x y), Tendsto u atTop (𝓝 x) → Tendsto (g ∘ u) atTop (𝓝 y) → y = g x) :
    Continuous g := by
  refine g.continuous_of_isClosed_graph (IsSeqClosed.isClosed ?_)
  rintro φ ⟨x, y⟩ hφg hφ
  refine hg (Prod.fst ∘ φ) x y ((continuous_fst.tendsto _).comp hφ) ?_
  have : g ∘ Prod.fst ∘ φ = Prod.snd ∘ φ := by
    ext n
    exact (hφg n).symm
  rw [this]
  exact (continuous_snd.tendsto _).comp hφ

variable {g}

namespace ContinuousLinearMap

/-- Upgrade a `LinearMap` to a `ContinuousLinearMap` using the **closed graph theorem**. -/
def ofIsClosedGraph (hg : IsClosed (g.graph : Set <| E × F)) : E →L[𝕜] F where
  toLinearMap := g
  cont := g.continuous_of_isClosed_graph hg

@[simp]
theorem coeFn_ofIsClosedGraph (hg : IsClosed (g.graph : Set <| E × F)) :
    ⇑(ContinuousLinearMap.ofIsClosedGraph hg) = g :=
  rfl

theorem coe_ofIsClosedGraph (hg : IsClosed (g.graph : Set <| E × F)) :
    ↑(ContinuousLinearMap.ofIsClosedGraph hg) = g := by
  ext
  rfl

/-- Upgrade a `LinearMap` to a `ContinuousLinearMap` using a variation on the
**closed graph theorem**. -/
def ofSeqClosedGraph
    (hg : ∀ (u : ℕ → E) (x y), Tendsto u atTop (𝓝 x) → Tendsto (g ∘ u) atTop (𝓝 y) → y = g x) :
    E →L[𝕜] F where
  toLinearMap := g
  cont := g.continuous_of_seq_closed_graph hg

@[simp]
theorem coeFn_ofSeqClosedGraph
    (hg : ∀ (u : ℕ → E) (x y), Tendsto u atTop (𝓝 x) → Tendsto (g ∘ u) atTop (𝓝 y) → y = g x) :
    ⇑(ContinuousLinearMap.ofSeqClosedGraph hg) = g :=
  rfl

theorem coe_ofSeqClosedGraph
    (hg : ∀ (u : ℕ → E) (x y), Tendsto u atTop (𝓝 x) → Tendsto (g ∘ u) atTop (𝓝 y) → y = g x) :
    ↑(ContinuousLinearMap.ofSeqClosedGraph hg) = g := by
  ext
  rfl

end ContinuousLinearMap

end ClosedGraphThm
