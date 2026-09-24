/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Kevin H. Wilson
-/
module

public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Topology.Baire.Absorbent

/-!
# Banach / F-Space open mapping theorem

This file contains the Banach open mapping theorem, i.e., the fact that a bijective
bounded linear map between Banach spaces has a bounded inverse.

We prove a more general fact that, that a surjective semi-linear map from a complete,
first countable, vector space over a nontrivially normed field (an "F-space" in some tellings) to
a Hausdorff Baire space over another nontrivially normed field is open.

To do this, we give a criterion in `closure_image_mem_nhds_one_of_interior_nonempty` for a
homomorphism `f` between topological groups to be "almost open" in the sense that for every
`U ∈ 𝓝 1`, `closure (f '' U) ∈ 𝓝 1`. When `f` is continuous,  the domain is complete and the
codomain is Hausdorff, we show in `ContinuousMonoidHom.isOpenMap` that almost open implies open.

Finally, in `ContinuousLinearMap.isOpenMap` we prove the main theorem by utilizing the Baire
category theorem (in the guise of `Absorbent.interior_nonempty`) to show the map is itself open.

The file also records several consequences of this theorem, including some specializations to
Banach spaces specifically.
-/

@[expose] public section

open Function Metric Set Filter Finset Topology NNReal
open LinearMap (range ker)
open scoped Uniformity Pointwise

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜'] {σ : 𝕜 →+* 𝕜'}
variable {E F : Type*}

section IsTopologicalGroup

variable [Group E] [TopologicalSpace E] [IsTopologicalGroup E]
  [Group F] [TopologicalSpace F] [IsTopologicalGroup F]

/-- If the image of every neighborhood of the identity has a closure with nonempty interior,
then the map is _almost open_ in the sense that the closure of the image of every neighborhood
of the idenity in the domain is a neighborhood of the identity in the codomain -/
@[to_additive]
theorem closure_image_mem_nhds_one_of_interior_nonempty
    (f : E →* F) (hi : ∀ V ∈ 𝓝 (1 : E), (interior (closure (f '' V))).Nonempty)
    {U : Set E} (hU : U ∈ 𝓝 (1 : E)) : closure (f '' U) ∈ 𝓝 (1 : F) := by
  -- The identity `1` is clearly in `closure (f '' U)`, but the trick to show is that it lies
  -- in the interior. To do so, take `V` a neighborhood of `1` such that `V⁻¹ = V` and `V * V ⊆ U`
  -- and `y` in `interior (closure (f '' V))`
  obtain ⟨V, hV, -, hsymm, hVU⟩ := exists_closed_nhds_one_inv_eq_mul_subset hU
  obtain ⟨y, hy⟩ := hi V hV
  -- Then `y⁻¹ • closure (f '' V)` is a neighborhood of `1 : F`, so it suffices to show that
  -- `y⁻¹ • closure (f '' V) ⊆ closure (f '' U)`
  have hn : (fun z ↦ y * z) ⁻¹' closure (f '' V) ∈ 𝓝 (1 : F) :=
    (continuous_const_mul y).continuousAt.preimage_mem_nhds
      (by simpa using mem_interior_iff_mem_nhds.mp hy)
  refine mem_of_superset hn fun z hz ↦ ?_
  -- Which follows by the continuity of `(a, b) ↦ a⁻¹ * b`
  have hh := map_mem_closure₂ (f := fun a b : F ↦ a⁻¹ * b)
    (by fun_prop) (interior_subset hy) hz
    (u := f '' U) (by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      refine ⟨a⁻¹ * b, hVU (Set.mul_mem_mul ?_ hb), by simp⟩
      rw [← hsymm]
      exact inv_mem_inv.mpr ha)
  simpa [mul_assoc] using hh

end IsTopologicalGroup

section CompleteSpace

variable [Group E] [UniformSpace E] [IsUniformGroup E] [CompleteSpace E] [FirstCountableTopology E]
  [Group F] [TopologicalSpace F] [IsTopologicalGroup F] [T2Space F]

/-- If `f : E →ₜ* F` where `E` is a first-countable complete uniform group and `F` is a Hausdorff
topological group, then if `f` is almost open then it is open. Here almost open means that the
_closure_ of the image of a neighborhood of the identity of `E` is a neighborhood of the
identity of `F`. -/
@[to_additive]
theorem image_mem_nhds_one_of_closure_image_mem_nhds_one
    (f : E →ₜ* F) (ho : ∀ U ∈ 𝓝 (1 : E), closure (f '' U) ∈ 𝓝 (1 : F))
    {V : Set E} (hV : V ∈ 𝓝 (1 : E)) : f '' V ∈ 𝓝 (1 : F) := by
  -- We know that `1 ∈ f '' V` since `f` is a homomorphism and `1` is in the _interior_ of
  -- `closure (f '' V)` by `ho`. So we need to show that `1` is actually in the interior or `f '' V`
  -- To do that, we will find open neighborhoods `U (n + 2) ⊆ U (n + 1) ⊆ U n ⊆ V` such that
  -- `U (n + i + 1) ^ 2 ⊆ U (n + 1)` and `closure (U (n + i + 1)) ⊆ U (n + i)`
  obtain ⟨U, hU⟩ := (nhds_basis_opens (1 : E)).exists_antitone_subbasis
  obtain ⟨φ, hφ_basis, hφ⟩ := hU.2.exists_subbasis_mul_closure_subset
  have hmem (k : ℕ) : U (φ k) ∈ 𝓝 1 := hφ_basis.mem_of_mem trivial
  obtain ⟨n, hn⟩ := hφ_basis.mem_iff.mp hV
  -- Then it suffices to show that `closure (f '' U (n + 2)) ⊆ f '' (U n)`
  grw [← hn]
  refine mem_of_superset (ho _ (hmem (n + 2))) fun y hy ↦ ?_
  -- We'll build a Cauchy sequence `s : ℕ → E` such that `s i ∈ U (n + 1)` for all `i` and `f (s i)`
  -- converges to `y`. Thus, `y ∈ f '' (closure (U (n + 1))) ⊆ f '' (U n)`
  have step (m : ℕ) (w : F) (hw : w ∈ closure (f '' U (φ m))) :
      ∃ x ∈ U (φ m), (f x)⁻¹ * w ∈ closure (f '' U (φ (m + 1))) := by
    have hn : {p : F | p⁻¹ * w ∈ closure (f '' U (φ (m + 1)))} ∈ 𝓝 w := by
      apply ContinuousAt.preimage_mem_nhds (by fun_prop)
      simpa using ho _ (hmem (m + 1))
    obtain ⟨p, hp, x, hx, rfl⟩ := mem_closure_iff_nhds.mp hw _ hn
    exact ⟨x, hx, hp⟩
  -- Build the sequence "backwards:" define `r 0 = y`. At step `k`, choose `x k ∈ U (φ (n + 2 + k))`
  -- such that the next residual `r (k + 1) = (f (x k))⁻¹ * r k` lies in
  -- `closure (f '' U (φ (n + 2 + (k + 1))))`. Thus each correction leaves a smaller residual,
  -- while preserving `f (s k) * r k = y` for the partial products `s` defined below.
  choose! a ha ha' using step
  let r : ℕ → F := fun k ↦ k.recOn y (fun m z ↦ (f (a (n + 2 + m) z))⁻¹ * z)
  let x : ℕ → E := fun k ↦ a (n + 2 + k) (r k)
  have hr (k : ℕ) : r k ∈ closure (f '' U (φ (n + 2 + k))) := by
    induction k with
    | zero => exact hy
    | succ k ih => exact ha' _ _ ih
  have hx (k : ℕ) : x k ∈ U (φ (n + 2 + k)) := ha _ _ (hr k)
  -- Then the sequence `s k = ∏ i < k, x i` has `f (s k) * (r k) = y` for all `k` and since
  -- `(s k)⁻¹ * s (k + 1) = x k ∈ U (n + 2 + k)`, the sequence `s` is Cauchy and thus converges
  -- to some `z`.
  let s : ℕ → E := fun k ↦ ((List.range k).map x).prod
  have hs : CauchySeq s := by
    have hb : (𝓤 E).HasAntitoneBasis
        (fun i ↦ {p : E × E | p.1⁻¹ * p.2 ∈ U (φ i)}) :=
      ⟨hφ_basis.uniformity_of_nhds_one_inv_mul, fun _ _ hij _ hp ↦ hφ_basis.antitone hij hp⟩
    refine hb.cauchySeq_of_succ (fun k ↦ ?_) (fun k ↦ ?_)
    · intro ⟨b, d⟩ ⟨c, hbc, hcd⟩
      simpa [mul_assoc] using (hφ k).1 (Set.mul_mem_mul hbc hcd)
    · simpa [s, List.prod_range_succ, mul_assoc] using hφ_basis.antitone (by lia) (hx k)
  -- Since `s` is Cauchy and `E` is complete, it converges to some `z : E`.
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hs
  refine ⟨z, (hφ n).2 (mem_closure_of_tendsto hz (Eventually.of_forall ?_)), ?_⟩
  · -- Since `s k ∈ U (n + 1)` for all `k`, `z ∈ closure (U (n + 1)) ⊆ U n`.
    have aux (p : ℕ) : ∀ j,
        ((List.range p).map (fun l ↦ x (j + l))).prod ∈ U (φ (n + 1 + j)) := by
      induction p with
      | zero => intro j; simpa using mem_of_mem_nhds (hmem (n + 1 + j))
      | succ p ih =>
        intro j
        rw [List.prod_range_succ']
        refine (hφ _).1 (Set.mul_mem_mul (by grind) ?_)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (j + 1)
    intro k
    simpa [s] using aux k 0
  · -- Since `f (s k) * r k = y` for all `k`, and `r k → 1`, `f z = y` as `F` is Hausdorff and
    -- `f` is continuous
    have hid (k : ℕ) : f (s k) * r k = y := by
      induction k with
      | zero => simp [s, r]
      | succ k ih =>
        have hs : s (k + 1) = s k * x k := List.prod_range_succ _ _
        rw [hs]
        change f (s k * x k) * ((f (x k))⁻¹ * r k) = y
        simpa [map_mul, mul_assoc] using ih
    have hrt : Tendsto r atTop (𝓝 1) := by
      apply (closed_nhds_basis 1).tendsto_right_iff.mpr
      intro V ⟨hV, hcV⟩
      obtain ⟨j, hj⟩ := hφ_basis.mem_iff.mp
        (f.continuous.continuousAt.preimage_mem_nhds (by simpa using hV))
      filter_upwards [eventually_ge_atTop j] with k hk
      refine closure_minimal ?_ hcV (hr k)
      rintro _ ⟨v, hv, rfl⟩
      exact hj (hφ_basis.antitone (by omega) hv)
    have ht := ((f.continuous.tendsto z).comp hz).mul hrt
    change Tendsto (fun k ↦ f (s k) * r k) atTop (𝓝 (f z * 1)) at ht
    have heq : f z * 1 = y := tendsto_nhds_unique ht (by simpa only [Function.comp_apply, hid] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ y) atTop (𝓝 y)))
    simpa using heq

/-- The open mapping theorem for continuous group homomorphisms: If a group homomorphism is almost
open then it is open. Here almost open means that the _closure_ of the image of a neighborhood of
the identity of `E` is a neighborhood of the identity of `F`. -/
@[to_additive]
protected theorem ContinuousMonoidHom.isOpenMap
    (f : E →ₜ* F) (ho : ∀ U ∈ 𝓝 (1 : E), closure (f '' U) ∈ 𝓝 (1 : F)) : IsOpenMap f := by
  rw [IsTopologicalGroup.isOpenMap_iff_nhds_one, Filter.le_map_iff]
  intro V hV
  exact image_mem_nhds_one_of_closure_image_mem_nhds_one f ho hV

end CompleteSpace

section FSpace

variable [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E]
  [Module 𝕜 E] [ContinuousSMul 𝕜 E] [CompleteSpace E] [FirstCountableTopology E]
  [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [Module 𝕜' F] [ContinuousSMul 𝕜' F] [T2Space F] [BaireSpace F]
  {σ' : 𝕜' →+* 𝕜} [RingHomInvPair σ σ'] [RingHomIsometric σ']
  (f : E →SL[σ] F)

namespace ContinuousLinearMap

include σ'

/-- The open mapping theorem: a surjective continuous semilinear map from a complete
first-countable topological vector space to a Hausdorff Baire topological vector space is open. -/
protected theorem isOpenMap (hsurj : Surjective f) : IsOpenMap f := by
  apply (f : ContinuousAddMonoidHom E F).isOpenMap
  intro U hU
  apply closure_image_mem_nhds_zero_of_interior_nonempty f.toLinearMap.toAddMonoidHom ?_ hU
  intro V hV
  -- Being vector spaces allow us to show that the image of a neighborhood is _absorbent_ and
  -- hence, by the Baire category theorem, has nonempty interior
  have habs : Absorbent 𝕜' (f '' V) := by
    intro y
    obtain ⟨x, rfl⟩ := hsurj y
    obtain ⟨r, hr⟩ := absorbs_iff_norm.mp (absorbent_nhds_zero (𝕜 := 𝕜) hV x)
    refine Absorbs.of_norm ⟨r, fun c hc ↦ singleton_subset_iff.mpr ?_⟩
    have hx : x ∈ σ' c • V := hr (σ' c) (by simpa using hc) (mem_singleton x)
    obtain ⟨z, hz, hzx⟩ := hx
    refine ⟨f z, ⟨z, hz, rfl⟩, ?_⟩
    simpa using congrArg f hzx
  exact (habs.mono subset_closure).interior_nonempty isClosed_closure

theorem isQuotientMap (hsurj : Surjective f) : IsQuotientMap f :=
  (f.isOpenMap hsurj).isQuotientMap f.continuous hsurj

theorem interior_preimage (hsurj : Surjective f) (s : Set F) :
    interior (f ⁻¹' s) = f ⁻¹' interior s :=
  ((f.isOpenMap hsurj).preimage_interior_eq_interior_preimage f.continuous s).symm

theorem closure_preimage (hsurj : Surjective f) (s : Set F) : closure (f ⁻¹' s) = f ⁻¹' closure s :=
  ((f.isOpenMap hsurj).preimage_closure_eq_closure_preimage f.continuous s).symm

theorem frontier_preimage (hsurj : Surjective f) (s : Set F) :
    frontier (f ⁻¹' s) = f ⁻¹' frontier s :=
  ((f.isOpenMap hsurj).preimage_frontier_eq_frontier_preimage f.continuous s).symm

end ContinuousLinearMap

/-- A continuous surjective affine map between topological affine spaces is open if their
model vector spaces are respectively complete and first-countable, and Hausdorff and Baire. -/
theorem AffineMap.isOpenMap {F : Type*} [AddCommGroup F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [Module 𝕜 F] [ContinuousSMul 𝕜 F] [T2Space F] [BaireSpace F]
    {P Q : Type*} [TopologicalSpace P] [AddTorsor E P] [IsTopologicalAddTorsor P]
    [TopologicalSpace Q] [AddTorsor F Q] [IsTopologicalAddTorsor Q]
    (f : P →ᵃ[𝕜] Q) (hf : Continuous f) (surj : Surjective f) : IsOpenMap f :=
  AffineMap.isOpenMap_linear_iff.mp <|
    ContinuousLinearMap.isOpenMap { f.linear with cont := AffineMap.continuous_linear_iff.mpr hf }
      (f.linear_surjective_iff.mpr surj)


section Equivalences

variable [RingHomInvPair σ' σ]

namespace LinearEquiv

/-- If a continuous linear map is a bijection, then its inverse is also a continuous linear map. -/
@[continuity]
theorem continuous_symm (e : E ≃ₛₗ[σ] F) (h : Continuous e) : Continuous e.symm := by
  rw [continuous_def]
  intro s hs
  rw [← e.image_eq_preimage_symm]
  rw [← e.coe_coe] at h ⊢
  exact ContinuousLinearMap.isOpenMap (σ := σ) ⟨_, h⟩ e.surjective s hs

/-- The open mapping theorem can upgrade a continuous bijection to a continuous linear equivalence
when the assumptions apply -/
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

namespace ContinuousLinearEquiv

/-- Convert a bijective continuous linear map `f : E →SL[σ] F` from a Banach space to a normed space
to a continuous linear equivalence. -/
noncomputable def ofBijective (f : E →SL[σ] F) (hinj : f.ker = ⊥) (hsurj : f.range = ⊤) :
    E ≃SL[σ] F :=
  (LinearEquiv.ofBijective f
        ⟨LinearMap.ker_eq_bot.mp hinj,
          LinearMap.range_eq_top.mp hsurj⟩).toContinuousLinearEquivOfContinuous
    -- Porting note: `by exact` was not previously needed. Why is it needed now?
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

end Equivalences

namespace ContinuousLinearMap

section Endomorphisms

variable [T2Space E] [BaireSpace E]

lemma isUnit_iff_bijective {f : E →L[𝕜] E} :
    IsUnit f ↔ Bijective f := by
  constructor
  · rintro ⟨f, rfl⟩
    exact ContinuousLinearEquiv.ofUnit f |>.bijective
  · refine fun h ↦ ⟨ContinuousLinearEquiv.toUnit <| .ofBijective f ?_ ?_, rfl⟩ <;>
    simp only [LinearMap.range_eq_top, LinearMap.ker_eq_bot, f.coe_coe, h.1, h.2]

/--
A continuous linear endomorphism is a unit iff it's a unit viewed simply as a linear map, provided
the space is complete.
-/
theorem isUnit_iff_isUnit_toLinearMap {f : E →L[𝕜] E} :
    IsUnit f ↔ IsUnit (f : E →ₗ[𝕜] E) :=
  f.isUnit_iff_bijective.trans (Module.End.isUnit_iff _).symm

/--
The spectrum of a continuous linear map `f` over a Banach space is exactly the spectrum of `f`
viewed as a mere linear map.
-/
theorem spectrum_eq {f : E →L[𝕜] E} :
    spectrum 𝕜 f = spectrum 𝕜 (f : Module.End 𝕜 E) := by
  ext μ
  rw [spectrum.mem_iff, spectrum.mem_iff, ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap]
  rfl

end Endomorphisms

section ClosedRange

variable {F : Type*} [AddCommGroup F] [UniformSpace F] [IsUniformAddGroup F]
  [Module 𝕜' F] [ContinuousSMul 𝕜' F] [CompleteSpace F] [FirstCountableTopology F]
  [T2Space F] [RingHomInvPair σ' σ] {f : E →SL[σ] F}

/-- An injective continuous semilinear map with closed range between complete first-countable
topological vector spaces, with Hausdorff target, defines an equivalence onto its range.
The closed range is complete and first-countable, hence Baire. -/
noncomputable def equivRange (hinj : Injective f) (hclo : IsClosed (range f)) :
    E ≃SL[σ] f.range :=
  have : CompleteSpace f.range := hclo.completeSpace_coe
  have : IsUniformAddGroup f.range := f.range.toAddSubgroup.isUniformAddGroup
  have : FirstCountableTopology f.range := TopologicalSpace.Subtype.firstCountableTopology _
  have : (𝓤 f.range).IsCountablyGenerated :=
    IsUniformAddGroup.uniformity_countably_generated
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

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
lemma equivRange_symm_apply (hinj : Injective f) (hclo : IsClosed (range f))
    (x : E) : (f.equivRange hinj hclo).symm ⟨f x, by simp⟩ = x := by
  simp [ContinuousLinearEquiv.symm_apply_eq, Subtype.ext_iff]

end ClosedRange

section ComplementedRange

variable {F : Type*} [AddCommGroup F] [UniformSpace F]
    [IsUniformAddGroup F] [Module 𝕜 F] [ContinuousSMul 𝕜 F] [T2Space F] [BaireSpace F]
    [FirstCountableTopology F]

section CompleteComplement

variable {G : Submodule 𝕜 F} [CompleteSpace G]

/-- Intermediate definition used to show
`ContinuousLinearMap.closed_complemented_range_of_isCompl_of_ker_eq_bot`.

This is `f.coprod G.subtypeL` as a `ContinuousLinearEquiv`. -/
noncomputable def coprodSubtypeLEquivOfIsCompl (f : E →L[𝕜] F)
    (h : IsCompl f.range G) (hker : f.ker = ⊥) : (E × G) ≃L[𝕜] F :=
  haveI : IsUniformAddGroup G := G.toAddSubgroup.isUniformAddGroup
  haveI : FirstCountableTopology G := TopologicalSpace.Subtype.firstCountableTopology _
  ContinuousLinearEquiv.ofBijective (f.coprod G.subtypeL)
    (by
      rw [ker_coprod_of_disjoint_range]
      · simp [hker]
      · simp [h.disjoint])
    (by simp [LinearMap.range_coprod, h.sup_eq_top])

theorem range_eq_map_coprodSubtypeLEquivOfIsCompl
    (f : E →L[𝕜] F) (h : IsCompl f.range G) (hker : f.ker = ⊥) :
    f.range =
      ((⊤ : Submodule 𝕜 E).prod (⊥ : Submodule 𝕜 G)).map
        (f.coprodSubtypeLEquivOfIsCompl h hker : E × G →ₗ[𝕜] F) := by
  have : IsUniformAddGroup G := G.toAddSubgroup.isUniformAddGroup
  have : FirstCountableTopology G := TopologicalSpace.Subtype.firstCountableTopology _
  rw [coprodSubtypeLEquivOfIsCompl, ← ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap,
    ContinuousLinearEquiv.coe_ofBijective, coe_coprod, LinearMap.coprod_map_prod, Submodule.map_bot,
    sup_bot_eq, Submodule.map_top]

end CompleteComplement

/- TODO: remove the assumption `f.ker = ⊥` in the next lemma, by using the map induced by `f` on
`E / f.ker`, once we have quotient normed spaces. -/
theorem closed_complemented_range_of_isCompl_of_ker_eq_bot [CompleteSpace F] (f : E →L[𝕜] F)
    (G : Submodule 𝕜 F) (h : IsCompl f.range G) (hG : IsClosed (G : Set F)) (hker : f.ker = ⊥) :
    IsClosed (f.range : Set F) := by
  have : CompleteSpace G := hG.completeSpace_coe
  let g := coprodSubtypeLEquivOfIsCompl f h hker
  rw [range_eq_map_coprodSubtypeLEquivOfIsCompl f h hker]
  apply g.toHomeomorph.isClosed_image.2
  exact isClosed_univ.prod isClosed_singleton

end ComplementedRange

end ContinuousLinearMap

section ClosedGraphThm

variable [T2Space E] {F : Type*} [AddCommGroup F] [UniformSpace F] [IsUniformAddGroup F]
  [Module 𝕜 F] [ContinuousSMul 𝕜 F] [CompleteSpace F] [FirstCountableTopology F]
  (g : E →ₗ[𝕜] F)

local instance : (𝓤 E).IsCountablyGenerated :=
  IsUniformAddGroup.uniformity_countably_generated

/-- The **closed graph theorem**: a linear map between complete first-countable topological
vector spaces, with Hausdorff domain and closed graph, is continuous. -/
protected theorem LinearMap.continuous_of_isClosed_graph (hg : IsClosed (g.graph : Set <| E × F)) :
    Continuous g := by
  let : CompleteSpace g.graph := completeSpace_coe_iff_isComplete.mpr hg.isComplete
  let : IsUniformAddGroup g.graph := g.graph.toAddSubgroup.isUniformAddGroup
  let : FirstCountableTopology g.graph := TopologicalSpace.Subtype.firstCountableTopology _
  let φ₀ : E →ₗ[𝕜] E × F := LinearMap.id.prod g
  have : Function.LeftInverse Prod.fst φ₀ := fun x => rfl
  let φ : E ≃ₗ[𝕜] g.graph :=
    (LinearEquiv.ofLeftInverse this).trans (LinearEquiv.ofEq _ _ g.graph_eq_range_prod.symm)
  let ψ : g.graph ≃L[𝕜] E :=
    φ.symm.toContinuousLinearEquivOfContinuous continuous_subtype_val.fst
  exact (continuous_subtype_val.comp ψ.symm.continuous).snd

/-- A sequential form of the **closed graph theorem** for complete first-countable topological
vector spaces with Hausdorff domain. To show continuity, it suffices that for any convergent
sequence `uₙ ⟶ x`, if `f(uₙ) ⟶ y` then `y = f(x)`. -/
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

end FSpace

/-! ### Specializations to Banach spaces

When `E` and `F` are Banach spaces, we can talk of _bounded_ linear functions
(which are the same as continuous linear functions). This section provides some specific results
in this direction.
-/

variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜' F] (f : E →SL[σ] F)

namespace ContinuousLinearMap

/-- A (possibly nonlinear) right inverse to a continuous linear map, which doesn't have to be
linear itself but which satisfies a bound `‖inverse x‖ ≤ C * ‖x‖`. A surjective continuous linear
map doesn't always have a continuous linear right inverse, but it always has a nonlinear inverse
in this sense, by Banach's open mapping theorem. -/
structure NonlinearRightInverse where
  /-- The underlying function.

  Do NOT use directly. Use the coercion instead. -/
  toFun : F → E
  /-- The bound `C` so that `‖inverse x‖ ≤ C * ‖x‖` for all `x`. -/
  nnnorm : ℝ≥0
  bound' : ∀ y, ‖toFun y‖ ≤ nnnorm * ‖y‖
  right_inv' : ∀ y, f (toFun y) = y

instance : CoeFun (NonlinearRightInverse f) fun _ => F → E :=
  ⟨fun fsymm => fsymm.toFun⟩

@[simp]
theorem NonlinearRightInverse.right_inv {f : E →SL[σ] F} (fsymm : NonlinearRightInverse f) (y : F) :
    f (fsymm y) = y :=
  fsymm.right_inv' y

theorem NonlinearRightInverse.bound {f : E →SL[σ] F} (fsymm : NonlinearRightInverse f) (y : F) :
    ‖fsymm y‖ ≤ fsymm.nnnorm * ‖y‖ :=
  fsymm.bound' y

end ContinuousLinearMap

variable {σ' : 𝕜' →+* 𝕜} [RingHomInvPair σ σ'] [RingHomIsometric σ']

/-- Given a continuous linear equivalence, the inverse is in particular an instance of
`ContinuousLinearMap.NonlinearRightInverse` (which turns out to be linear). -/
noncomputable def ContinuousLinearEquiv.toNonlinearRightInverse
    [RingHomInvPair σ' σ] (f : E ≃SL[σ] F) :
    ContinuousLinearMap.NonlinearRightInverse (f : E →SL[σ] F) where
  toFun := f.invFun
  nnnorm := ‖(f.symm : F →SL[σ'] E)‖₊
  bound' _ := ContinuousLinearMap.le_opNorm (f.symm : F →SL[σ'] E) _
  right_inv' := f.apply_symm_apply

noncomputable instance [RingHomInvPair σ' σ] (f : E ≃SL[σ] F) :
    Inhabited (ContinuousLinearMap.NonlinearRightInverse (f : E →SL[σ] F)) :=
  ⟨f.toNonlinearRightInverse⟩

/-! ### Banach space specilizations

When the domain and codomain are Banach spaces, then continuous linear maps are the same thing
as _bounded_ linear maps. We record several useful lemmas about such spaces.
 -/

variable [CompleteSpace F]

namespace ContinuousLinearMap

section Banach
variable [RingHomIsometric σ]

include σ' in
/-- First step of the proof of the Banach open mapping theorem (using completeness of `F`):
by Baire's theorem, there exists a ball in `E` whose image closure has nonempty interior.
Rescaling everything, it follows that any `y ∈ F` is arbitrarily well approached by
images of elements of norm at most `C * ‖y‖`.
For further use, we will only need such an element whose image
is within distance `‖y‖/2` of `y`, to apply an iterative process. -/
theorem exists_approx_preimage_norm_le (surj : Surjective f) :
    ∃ C ≥ 0, ∀ y, ∃ x, dist (f x) y ≤ 1 / 2 * ‖y‖ ∧ ‖x‖ ≤ C * ‖y‖ := by
  have A : ⋃ n : ℕ, closure (f '' ball 0 n) = Set.univ := by
    refine Subset.antisymm (subset_univ _) fun y _ => ?_
    rcases surj y with ⟨x, hx⟩
    rcases exists_nat_gt ‖x‖ with ⟨n, hn⟩
    refine mem_iUnion.2 ⟨n, subset_closure ?_⟩
    refine (mem_image _ _ _).2 ⟨x, ⟨?_, hx⟩⟩
    rwa [mem_ball, dist_eq_norm, sub_zero]
  have : ∃ (n : ℕ) (x : _), x ∈ interior (closure (f '' ball 0 n)) :=
    nonempty_interior_of_iUnion_of_closed (fun n => isClosed_closure) A
  simp only [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at this
  rcases this with ⟨n, a, ε, ⟨εpos, H⟩⟩
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  refine ⟨(ε / 2)⁻¹ * ‖c‖ * 2 * n, by positivity, fun y => ?_⟩
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · have hc' : 1 < ‖σ c‖ := by simp only [RingHomIsometric.norm_map, hc]
    rcases rescale_to_shell hc' (half_pos εpos) hy with ⟨d, hd, ydlt, -, dinv⟩
    let δ := ‖d‖ * ‖y‖ / 4
    have δpos : 0 < δ := by positivity
    have : a + d • y ∈ ball a ε := by
      simp [dist_eq_norm, lt_of_le_of_lt ydlt.le (half_lt_self εpos)]
    rcases Metric.mem_closure_iff.1 (H this) _ δpos with ⟨z₁, z₁im, h₁⟩
    rcases (mem_image _ _ _).1 z₁im with ⟨x₁, hx₁, xz₁⟩
    rw [← xz₁] at h₁
    rw [mem_ball, dist_eq_norm, sub_zero] at hx₁
    have : a ∈ ball a ε := by
      simp only [mem_ball, dist_self]
      exact εpos
    rcases Metric.mem_closure_iff.1 (H this) _ δpos with ⟨z₂, z₂im, h₂⟩
    rcases (mem_image _ _ _).1 z₂im with ⟨x₂, hx₂, xz₂⟩
    rw [← xz₂] at h₂
    rw [mem_ball, dist_eq_norm, sub_zero] at hx₂
    let x := x₁ - x₂
    have I : ‖f x - d • y‖ ≤ 2 * δ :=
      calc
        ‖f x - d • y‖ = ‖f x₁ - (a + d • y) - (f x₂ - a)‖ := by
          congr 1
          simp only [x, f.map_sub]
          abel
        _ ≤ ‖f x₁ - (a + d • y)‖ + ‖f x₂ - a‖ := norm_sub_le _ _
        _ ≤ 2 * δ := by grind [dist_eq_norm']
    have J : ‖f (σ' d⁻¹ • x) - y‖ ≤ 1 / 2 * ‖y‖ :=
      calc
        ‖f (σ' d⁻¹ • x) - y‖ = ‖d⁻¹ • f x - (d⁻¹ * d) • y‖ := by
          rwa [f.map_smulₛₗ _, inv_mul_cancel₀, one_smul, map_inv₀, map_inv₀,
            RingHomCompTriple.comp_apply, RingHom.id_apply]
        _ = ‖d⁻¹ • (f x - d • y)‖ := by rw [mul_smul, smul_sub]
        _ = ‖d‖⁻¹ * ‖f x - d • y‖ := by rw [norm_smul, norm_inv]
        _ ≤ ‖d‖⁻¹ * (2 * δ) := by gcongr
        _ = 1 / 2 * ‖y‖ := by simp [δ, field]; norm_num
    rw [← dist_eq_norm] at J
    have K : ‖σ' d⁻¹ • x‖ ≤ (ε / 2)⁻¹ * ‖c‖ * 2 * ↑n * ‖y‖ :=
      calc
        ‖σ' d⁻¹ • x‖ = ‖d‖⁻¹ * ‖x₁ - x₂‖ := by rw [norm_smul, RingHomIsometric.norm_map, norm_inv]
        _ ≤ (ε / 2)⁻¹ * ‖c‖ * ‖y‖ * (n + n) := by
          gcongr
          · simpa using dinv
          · exact le_trans (norm_sub_le _ _) (by gcongr)
        _ = (ε / 2)⁻¹ * ‖c‖ * 2 * ↑n * ‖y‖ := by ring
    exact ⟨σ' d⁻¹ • x, J, K⟩

variable [CompleteSpace E]

section
include σ'

/-- The Banach open mapping theorem: if a bounded linear map between Banach spaces is onto, then
any point has a preimage with controlled norm. -/
theorem exists_preimage_norm_le (surj : Surjective f) :
    ∃ C > 0, ∀ y, ∃ x, f x = y ∧ ‖x‖ ≤ C * ‖y‖ := by
  obtain ⟨C, C0, hC⟩ := exists_approx_preimage_norm_le f surj
  /- Second step of the proof: starting from `y`, we want an exact preimage of `y`. Let `g y` be
    the approximate preimage of `y` given by the first step, and `h y = y - f(g y)` the part that
    has no preimage yet. We will iterate this process, taking the approximate preimage of `h y`,
    leaving only `h^2 y` without preimage yet, and so on. Let `u n` be the approximate preimage
    of `h^n y`. Then `u` is a converging series, and by design the sum of the series is a
    preimage of `y`. This uses completeness of `E`. -/
  choose g hg using hC
  let h y := y - f (g y)
  have hle : ∀ y, ‖h y‖ ≤ 1 / 2 * ‖y‖ := by
    intro y
    rw [← dist_eq_norm, dist_comm]
    exact (hg y).1
  refine ⟨2 * C + 1, by linarith, fun y => ?_⟩
  have hnle : ∀ n : ℕ, ‖h^[n] y‖ ≤ (1 / 2) ^ n * ‖y‖ := by
    intro n
    induction n with
    | zero => simp only [one_div, one_mul, iterate_zero_apply, pow_zero, le_rfl]
    | succ n IH =>
      rw [iterate_succ']
      apply le_trans (hle _) _
      rw [pow_succ', mul_assoc]
      gcongr
  let u n := g (h^[n] y)
  have ule : ∀ n, ‖u n‖ ≤ (1 / 2) ^ n * (C * ‖y‖) := fun n ↦ by
    apply le_trans (hg _).2
    calc
      C * ‖h^[n] y‖ ≤ C * ((1 / 2) ^ n * ‖y‖) := by gcongr; exact hnle n
      _ = (1 / 2) ^ n * (C * ‖y‖) := by ring
  have sNu : Summable fun n => ‖u n‖ := by
    refine .of_nonneg_of_le (fun n => norm_nonneg _) ule ?_
    exact Summable.mul_right _ (summable_geometric_of_lt_one (by simp) (by norm_num))
  have su : Summable u := sNu.of_norm
  let x := tsum u
  have x_ineq : ‖x‖ ≤ (2 * C + 1) * ‖y‖ :=
    calc
      ‖x‖ ≤ ∑' n, ‖u n‖ := norm_tsum_le_tsum_norm sNu
      _ ≤ ∑' n, (1 / 2) ^ n * (C * ‖y‖) :=
        sNu.tsum_le_tsum ule <| Summable.mul_right _ summable_geometric_two
      _ = (∑' n, (1 / 2) ^ n) * (C * ‖y‖) := tsum_mul_right
      _ = 2 * C * ‖y‖ := by rw [tsum_geometric_two, mul_assoc]
      _ ≤ 2 * C * ‖y‖ + ‖y‖ := le_add_of_nonneg_right (norm_nonneg y)
      _ = (2 * C + 1) * ‖y‖ := by ring
  have fsumeq : ∀ n : ℕ, f (∑ i ∈ Finset.range n, u i) = y - h^[n] y := by
    intro n
    induction n with
    | zero => simp [f.map_zero]
    | succ n IH => rw [sum_range_succ, f.map_add, IH, iterate_succ_apply', sub_add]
  have : Tendsto (fun n => ∑ i ∈ Finset.range n, u i) atTop (𝓝 x) := su.hasSum.tendsto_sum_nat
  have L₁ : Tendsto (fun n => f (∑ i ∈ Finset.range n, u i)) atTop (𝓝 (f x)) :=
    (f.continuous.tendsto _).comp this
  simp only [fsumeq] at L₁
  have L₂ : Tendsto (fun n => y - h^[n] y) atTop (𝓝 (y - 0)) := by
    refine tendsto_const_nhds.sub ?_
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) hnle ?_
    rw [← zero_mul ‖y‖]
    refine (_root_.tendsto_pow_atTop_nhds_zero_of_lt_one ?_ ?_).mul tendsto_const_nhds <;> norm_num
  have feq : f x = y - 0 := tendsto_nhds_unique L₁ L₂
  rw [sub_zero] at feq
  exact ⟨x, feq, x_ineq⟩

end

/-! ### Applications of the open mapping theorem -/

section
include σ'

theorem exists_nonlinearRightInverse_of_surjective (f : E →SL[σ] F)
    (hsurj : f.range = ⊤) : ∃ fsymm : NonlinearRightInverse f, 0 < fsymm.nnnorm := by
  choose C hC fsymm h using
    exists_preimage_norm_le _ (LinearMap.range_eq_top.1 hsurj)
  use {
      toFun := fsymm
      nnnorm := ⟨C, hC.lt.le⟩
      bound' := fun y => (h y).2
      right_inv' := fun y => (h y).1 }
  exact hC

end

/-- A surjective continuous linear map between Banach spaces admits a (possibly nonlinear)
controlled right inverse. In general, it is not possible to ensure that such a right inverse
is linear (take for instance the map from `E` to `E/F` where `F` is a closed subspace of `E`
without a closed complement. Then it doesn't have a continuous linear right inverse.) -/
noncomputable irreducible_def nonlinearRightInverseOfSurjective (f : E →SL[σ] F)
  (hsurj : f.range = ⊤) : NonlinearRightInverse f :=
  Classical.choose (exists_nonlinearRightInverse_of_surjective f hsurj)

theorem nonlinearRightInverseOfSurjective_nnnorm_pos (f : E →SL[σ] F) (hsurj : f.range = ⊤) :
    0 < (nonlinearRightInverseOfSurjective f hsurj).nnnorm := by
  rw [nonlinearRightInverseOfSurjective]
  exact Classical.choose_spec (exists_nonlinearRightInverse_of_surjective f hsurj)

end Banach
end ContinuousLinearMap

namespace ContinuousLinearMap

section

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [CompleteSpace E] [CompleteSpace F]

-- TODO: once mathlib has Fredholm operators, generalise the next four lemmas accordingly

/-- If `f : E →L[𝕜] F` is injective with closed range (and `E` and `F` are Banach spaces),
`f` is anti-Lipschitz. -/
lemma antilipschitz_of_injective_of_isClosed_range (f : E →L[𝕜] F)
    (hf : Injective f) (hf' : IsClosed (Set.range f)) : ∃ K, AntilipschitzWith K f :=
  ⟨_, .comp (.subtype_coe (Set.range f)) (f.equivRange hf hf').antilipschitz⟩

/-- A choice of anti-Lipschitz constant for `f : E →L[𝕜] F` injective with closed range
(assuming `E` and `F` are Banach spaces). -/
noncomputable def antilipschitzConstant_of_injective_of_isClosed_range (f : E →L[𝕜] F)
    (hf : Injective f) (hf' : IsClosed (Set.range f)) : ℝ≥0 :=
  Classical.choose (f.antilipschitz_of_injective_of_isClosed_range hf hf')

lemma antilipschitz_antiLipschitzConstant_of_injective_of_isClosed_range (f : E →L[𝕜] F)
    (hf : Injective f) (hf' : IsClosed (Set.range f)) :
    AntilipschitzWith (f.antilipschitzConstant_of_injective_of_isClosed_range hf hf') f :=
  Classical.choose_spec (f.antilipschitz_of_injective_of_isClosed_range hf hf')

/-- An injective bounded linear operator between Banach spaces has closed range
iff it is anti-Lipschitz. -/
lemma isClosed_range_iff_antilipschitz_of_injective (f : E →L[𝕜] F)
    (hf : Injective f) : IsClosed (Set.range f) ↔ ∃ K, AntilipschitzWith K f := by
  refine ⟨fun h ↦ f.antilipschitz_of_injective_of_isClosed_range hf h, fun h ↦ ?_⟩
  choose K hf' using h
  exact hf'.isClosed_range f.uniformContinuous

/-- A choice of continuous left inverse of an injective continuous linear map with closed range:
this is `LinearMap.leftInverse` as a continuous linear map;
by injectivity, the junk value of `leftInverse` never matters, and continuity of the inverse
follows form the closed range condition. -/
noncomputable def leftInverse_of_injective_of_isClosed_range
    (f : E →L[𝕜] F) (hf : Injective f) (hf' : IsClosed (range f)) : f.range →L[𝕜] E :=
  letI K := f.antilipschitzConstant_of_injective_of_isClosed_range hf hf'
  letI hfK := f.antilipschitz_antiLipschitzConstant_of_injective_of_isClosed_range hf hf'
  LinearMap.mkContinuous f.rangeRestrict.leftInverse K (by
    rintro ⟨y, x, rfl⟩
    have aux := hfK.le_mul_dist x 0
    simp only [dist_zero_right, map_zero] at aux
    convert! aux
    exact f.rangeRestrict.leftInverse_apply_of_inj
      (by rw [ker_codRestrict]; exact LinearMap.ker_eq_bot.mpr hf) x)

end

end ContinuousLinearMap

section BijectivityCriteria

namespace ContinuousLinearMap

variable {σ : 𝕜 →+* 𝕜'} {σ' : 𝕜' →+* 𝕜} [RingHomInvPair σ σ']
  {F : Type u_4} [NormedAddCommGroup F] [NormedSpace 𝕜' F] [CompleteSpace E]

lemma closed_range_of_antilipschitz {f : E →SL[σ] F} {c : ℝ≥0} (hf : AntilipschitzWith c f) :
    f.range.topologicalClosure = f.range :=
  SetLike.ext'_iff.mpr <| (hf.isClosed_range f.uniformContinuous).closure_eq

variable [CompleteSpace F]

lemma _root_.AntilipschitzWith.completeSpace_range_clm {f : E →SL[σ] F} {c : ℝ≥0}
    (hf : AntilipschitzWith c f) : CompleteSpace f.range :=
  IsClosed.completeSpace_coe (hs := hf.isClosed_range f.uniformContinuous)

variable [RingHomInvPair σ' σ] [RingHomIsometric σ']

lemma bijective_iff_dense_range_and_antilipschitz (f : E →SL[σ] F) :
    Bijective f ↔ f.range.topologicalClosure = ⊤ ∧ ∃ c, AntilipschitzWith c f := by
  refine ⟨fun h ↦ ⟨?eq_top, ?anti⟩, fun ⟨hd, c, hf⟩ ↦ ⟨hf.injective, ?surj⟩⟩
  case eq_top => simpa [SetLike.ext'_iff] using! h.2.denseRange.closure_eq
  case anti =>
    refine ⟨_, ContinuousLinearEquiv.ofBijective f ?_ ?_ |>.antilipschitz⟩ <;>
    simp only [LinearMap.range_eq_top, LinearMap.ker_eq_bot, f.coe_coe, h.1, h.2]
  case surj => rwa [← f.coe_coe, ← LinearMap.range_eq_top, ← closed_range_of_antilipschitz hf]

end ContinuousLinearMap

end BijectivityCriteria
