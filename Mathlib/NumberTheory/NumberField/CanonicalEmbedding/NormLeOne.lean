/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.PolarCoord
import Mathlib.NumberTheory.NumberField.Units.Regulator

/-!
# Fundamental Cone: set of elements of norm ≤ 1

In this file, we study the subset `NormLeOne` of the `fundamentalCone` of elements `x` with
`mixedEmbedding.norm x ≤ 1`.

Mainly, we prove that it is bounded, its frontier has volume zero and compute its volume.

## Strategy of proof

The proof is loosely based on the strategy given in [D. Marcus, *Number Fields*][marcus1977number].

1. since `NormLeOne K` is norm-stable, in the sense that
  `normLeOne K = normAtAllPlaces⁻¹' (normAtAllPlaces '' (normLeOne K))`,
  see `normLeOne_eq_preimage_image`, it's enough to study the subset
  `normAtAllPlaces '' (normLeOne K)` of `realSpace K`.

2. A description of `normAtAllPlaces '' (normLeOne K)` is given by `normAtAllPlaces_normLeOne`, it
  is the set of `x : realSpace K`, nonnegative at all places, whose norm is nonzero and `≤ 1` and
  such that `logMap x` is in the `fundamentalDomain` of `basisUnitLattice K`.
  Note that, here and elsewhere, we identify `x` with its image in `mixedSpace K` given
  by `mixedSpaceOfRealSpace x`.

3. In order to describe the inverse image in `realSpace K` of the `fundamentalDomain` of
  `basisUnitLattice K`, we define the map `expMap : realSpace K → realSpace K` that is, in
  some way, the right inverse of `logMap`, see `logMap_expMap`.

4. Denote by `ηᵢ` (with `i ≠ w₀` where `w₀` is the distinguished infinite place,
  see the description of `logSpace` below) the fundamental system of units given by
  `fundSystem` and let `|ηᵢ|` denote `normAtAllPlaces (mixedEmbedding ηᵢ))`, that is the vector
  `(w (ηᵢ))_w` in `realSpace K`. Then, the image of `|ηᵢ|` by `expMap.symm` form a basis of the
  subspace `{x : realSpace K | ∑ w, x w = 0}`. We complete by adding the vector `(mult w)_w` to
  get a basis, called `completeBasis`, of `realSpace K`. The basis `completeBasis K` has
  the property that, for `i ≠ w₀`, the image of `completeBasis K i` by the
  natural restriction map `realSpace K → logSpace K` is `basisUnitLattice K`.

5. At this point, we can construct the map `expMapBasis` that plays a crucial part in the proof.
  It is the map that sends `x : realSpace K` to `Real.exp (x w₀) * ∏_{i ≠ w₀} |ηᵢ| ^ x i`, see
  `expMapBasis_apply'`. Then, we prove a change of variable formula for `expMapBasis`, see
  `setLIntegral_expMapBasis_image`.

6. We define a set `paramSet` in `realSpace K` and prove that
  `normAtAllPlaces '' (normLeOne K) = expMapBasis (paramSet K)`, see
  `normAtAllPlaces_normLeOne_eq_image`. Using this, `setLIntegral_expMapBasis_image` and the results
  from `mixedEmbedding.polarCoord`, we can then compute the volume of `normLeOne K`, see
  `volume_normLeOne`.

7. Finally, we need to prove that the frontier of `normLeOne K` has zero-volume (we will prove
  in passing that `normLeOne K` is bounded.) For that we prove that
  `volume (interior (normLeOne K)) = volume (closure (normLeOne K))`, see
  `volume_interior_eq_volume_closure`. Since we now that the volume of `interior (normLeOne K)` is
  finite since it is bounded by the volume of `normLeOne K`, the result follows, see
  `volume_frontier_normLeOne`. We proceed in several steps.

  7.1. We prove first that
    `normAtAllPlaces⁻¹' (expMapBasis '' interior (paramSet K)) ⊆ interior (normLeOne K)`, see
    `subset_interior_normLeOne` (Note that here again we identify `realSpace K` with its image
    in `mixedSpace K`). The main argument is that `expMapBasis` is an open partial homeomorphism
    and that `interior (paramSet K)` is a subset of its source, so its image by `expMapBasis`
    is still open.

  7.2. The same kind of argument does not work with `closure (paramSet)` since it is not contained
    in the source of `expMapBasis`. So we define a compact set, called `compactSet K`, such that
    `closure (normLeOne K) ⊆ normAtAllPlaces⁻¹' (compactSet K)`, see `closure_normLeOne_subset`,
    and it is almost equal to `expMapBasis '' closure (paramSet K)`, see `compactSet_ae`.

  7.3. We get from the above that `normLeOne K ⊆ normAtAllPlaces⁻¹' (compactSet K)`, from which
    it follows easily that `normLeOne K` is bounded, see `isBounded_normLeOne`.

  7.4. Finally, we prove that `volume (normAtAllPlaces ⁻¹' compactSet K) =
    volume (normAtAllPlaces ⁻¹' (expMapBasis '' interior (paramSet K)))`, which implies that
    `volume (interior (normLeOne K)) = volume (closure (normLeOne K))` by the above and the fact
    that `volume (interior (normLeOne K)) ≤ volume (closure (normLeOne K))`, which boils down to
    the fact that the interior and closure of `paramSet K` are almost equal, see
    `closure_paramSet_ae_interior`.

## Spaces and maps

To help understand the proof, we make a list of (almost) all the spaces and maps used and
their connections (as hinted above, we do not mention the map `mixedSpaceOfRealSpace` since we
identify `realSpace K` with its image in `mixedSpace K`).

* `mixedSpace`: the set `({w // IsReal w} → ℝ) × (w // IsComplex w → ℂ)` where `w` denote the
  infinite places of `K`.

* `realSpace`: the set `w → ℝ` where `w` denote the infinite places of `K`

* `logSpace`: the set `{w // w ≠ w₀} → ℝ` where `w₀` is a distinguished place of `K`. It is the set
  used in the proof of Dirichlet Unit Theorem.

* `mixedEmbedding : K → mixedSpace K`: the map that sends `x : K` to `φ_w(x)` where, for all
  infinite place `w`, `φ_w : K → ℝ` or `ℂ`, resp. if `w` is real or if `w` is complex, denote a
  complex embedding associated to `w`.

* `logEmbedding : (𝓞 K)ˣ → logSpace K`: the map that sends the unit `u : (𝓞 K)ˣ` to
  `(mult w * log (w u))_w` for `w ≠ w₀`. Its image is `unitLattice K`, a `ℤ`-lattice of
  `logSpace K`, that admits `basisUnitLattice K` as a basis.

* `logMap : mixedSpace K → logSpace K`: this map is defined such that it factors `logEmbedding`,
  that is, for `u : (𝓞 K)ˣ`, `logMap (mixedEmbedding x) = logEmbedding x`, and that
  `logMap (c • x) = logMap x` for `c ≠ 0` and `norm x ≠ 0`. The inverse image of the fundamental
  domain of `basisUnitLattice K` by `logMap` (minus the elements of norm zero) is
  `fundamentalCone K`.

* `expMap : realSpace K → realSpace K`: the right inverse of `logMap` in the sense that
  `logMap (expMap x) = (x_w)_{w ≠ w₀}`.

* `expMapBasis : realSpace K → realSpace K`: the map that sends `x : realSpace K` to
  `Real.exp (x w₀) * ∏_{i ≠ w₀} |ηᵢ| ^ x i` where `|ηᵢ|` denote the vector of `realSpace K` given
  by `w (ηᵢ)` and `ηᵢ` denote the units in `fundSystem K`.

-/

variable (K : Type*) [Field K]

open Finset Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  NumberField.Units dirichletUnitTheorem

namespace NumberField.mixedEmbedding.fundamentalCone

section normAtAllPlaces

variable [NumberField K]

variable {K}

theorem logMap_normAtAllPlaces (x : mixedSpace K) :
    logMap (mixedSpaceOfRealSpace (normAtAllPlaces x)) = logMap x :=
  logMap_eq_of_normAtPlace_eq
    fun w ↦ by rw [normAtPlace_mixedSpaceOfRealSpace (normAtPlace_nonneg w x)]

theorem norm_normAtAllPlaces (x : mixedSpace K) :
    mixedEmbedding.norm (mixedSpaceOfRealSpace (normAtAllPlaces x)) = mixedEmbedding.norm x := by
  simp_rw [mixedEmbedding.norm_apply,
    normAtPlace_mixedSpaceOfRealSpace (normAtAllPlaces_nonneg _ _)]

theorem normAtAllPlaces_mem_fundamentalCone_iff {x : mixedSpace K} :
    mixedSpaceOfRealSpace (normAtAllPlaces x) ∈ fundamentalCone K ↔ x ∈ fundamentalCone K := by
  simp_rw [fundamentalCone, Set.mem_diff, Set.mem_preimage, logMap_normAtAllPlaces,
    Set.mem_setOf_eq, norm_normAtAllPlaces]

end normAtAllPlaces

section normLeOne_def

variable [NumberField K]

/--
The set of elements of the `fundamentalCone` of `norm ≤ 1`.
-/
abbrev normLeOne : Set (mixedSpace K) := fundamentalCone K ∩ {x | mixedEmbedding.norm x ≤ 1}

variable {K} in
theorem mem_normLeOne {x : mixedSpace K} :
    x ∈ normLeOne K ↔ x ∈ fundamentalCone K ∧ mixedEmbedding.norm x ≤ 1 := Set.mem_sep_iff

theorem measurableSet_normLeOne :
    MeasurableSet (normLeOne K) :=
  (measurableSet_fundamentalCone K).inter <|
    measurableSet_le (mixedEmbedding.continuous_norm K).measurable measurable_const

theorem normLeOne_eq_preimage_image :
    normLeOne K = normAtAllPlaces ⁻¹' (normAtAllPlaces '' (normLeOne K)) := by
  refine subset_antisymm (Set.subset_preimage_image _ _) ?_
  rintro x ⟨y, hy₁, hy₂⟩
  rw [mem_normLeOne, ← normAtAllPlaces_mem_fundamentalCone_iff, ← norm_normAtAllPlaces,
    ← mem_normLeOne] at hy₁ ⊢
  rwa [← hy₂]

@[deprecated (since := "2025-07-27")]
alias normLeOne_eq_primeage_image := normLeOne_eq_preimage_image

open scoped Classical in
theorem normAtAllPlaces_normLeOne :
    normAtAllPlaces '' (normLeOne K) =
    mixedSpaceOfRealSpace ⁻¹'
      (logMap ⁻¹'
          ZSpan.fundamentalDomain ((basisUnitLattice K).ofZLatticeBasis ℝ (unitLattice K))) ∩
      {x | (∀ w, 0 ≤ x w)} ∩
      {x | mixedEmbedding.norm (mixedSpaceOfRealSpace x) ≠ 0} ∩
      {x | mixedEmbedding.norm (mixedSpaceOfRealSpace x) ≤ 1} := by
  ext x
  refine ⟨?_, fun ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩ ↦ ?_⟩
  · rintro ⟨y, ⟨⟨h₁, h₂⟩, h₃⟩, rfl⟩
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rwa [Set.mem_preimage, ← logMap_normAtAllPlaces] at h₁
    · exact fun w ↦ normAtPlace_nonneg w y
    · rwa [Set.mem_setOf_eq, ← norm_normAtAllPlaces] at h₂
    · rwa [Set.mem_setOf_eq, ← norm_normAtAllPlaces] at h₃
  · exact ⟨mixedSpaceOfRealSpace x, ⟨⟨h₁, h₃⟩, h₄⟩, normAtAllPlaces_mixedSpaceOfRealSpace h₂⟩

end normLeOne_def

noncomputable section expMap

variable {K}

/--
The component of `expMap` at the place `w`.
-/
@[simps]
def expMap_single (w : InfinitePlace K) : OpenPartialHomeomorph ℝ ℝ where
  toFun := fun x ↦ Real.exp ((w.mult : ℝ)⁻¹ * x)
  invFun := fun x ↦ w.mult * Real.log x
  source := Set.univ
  target := Set.Ioi 0
  open_source := isOpen_univ
  open_target := isOpen_Ioi
  map_source' _ _ := Real.exp_pos _
  map_target' _ _ := trivial
  left_inv' _ _ := by simp only [Real.log_exp, mul_inv_cancel_left₀ mult_coe_ne_zero]
  right_inv' _ h := by simp only [inv_mul_cancel_left₀ mult_coe_ne_zero, Real.exp_log h]
  continuousOn_toFun := (continuousOn_const.mul continuousOn_id).rexp
  continuousOn_invFun := continuousOn_const.mul (Real.continuousOn_log.mono (by aesop))

/--
The derivative of `expMap_single`, see `hasDerivAt_expMap_single`.
-/
abbrev deriv_expMap_single (w : InfinitePlace K) (x : ℝ) : ℝ :=
  (expMap_single w x) * (w.mult : ℝ)⁻¹

theorem hasDerivAt_expMap_single (w : InfinitePlace K) (x : ℝ) :
    HasDerivAt (expMap_single w) (deriv_expMap_single w x) x := by
  simpa [expMap_single, mul_comm] using
    (HasDerivAt.comp x (Real.hasDerivAt_exp _) (hasDerivAt_mul_const (w.mult : ℝ)⁻¹))


variable [NumberField K]

/--
The map from `realSpace K → realSpace K` whose components is given by `expMap_single`. It is, in
some respect, a right inverse of `logMap`, see `logMap_expMap`.
-/
def expMap : OpenPartialHomeomorph (realSpace K) (realSpace K) :=
  OpenPartialHomeomorph.pi fun w ↦ expMap_single w

variable (K)

theorem expMap_source :
    expMap.source = (Set.univ : Set (realSpace K)) := by
  simp_rw [expMap, OpenPartialHomeomorph.pi_toPartialEquiv, PartialEquiv.pi_source, expMap_single,
    Set.pi_univ Set.univ]

theorem expMap_target :
    expMap.target = Set.univ.pi fun (_ : InfinitePlace K) ↦ Set.Ioi 0 := by
  simp_rw [expMap, OpenPartialHomeomorph.pi_toPartialEquiv, PartialEquiv.pi_target, expMap_single]

theorem injective_expMap :
    Function.Injective (expMap : realSpace K → realSpace K) :=
  Set.injOn_univ.1 (expMap_source K ▸ expMap.injOn)

theorem continuous_expMap :
    Continuous (expMap : realSpace K → realSpace K) :=
  continuousOn_univ.mp <| (expMap_source K) ▸ expMap.continuousOn

variable {K}

@[simp]
theorem expMap_apply (x : realSpace K) (w : InfinitePlace K) :
    expMap x w = Real.exp ((↑w.mult)⁻¹ * x w) := rfl

theorem expMap_pos (x : realSpace K) (w : InfinitePlace K) :
    0 < expMap x w := Real.exp_pos _

theorem expMap_smul (c : ℝ) (x : realSpace K) :
    expMap (c • x) = (expMap x) ^ c := by
  ext
  simp [mul_comm c _, ← mul_assoc, Real.exp_mul]

theorem expMap_add (x y : realSpace K) :
    expMap (x + y) = expMap x * expMap y := by
  ext
  simp [mul_add, Real.exp_add]

theorem expMap_sum {ι : Type*} (s : Finset ι) (f : ι → realSpace K) :
    expMap (∑ i ∈ s, f i) = ∏ i ∈ s, expMap (f i) := by
  ext
  simp [← Real.exp_sum, ← mul_sum]

@[simp]
theorem expMap_symm_apply (x : realSpace K) (w : InfinitePlace K) :
    expMap.symm x w = ↑w.mult * Real.log (x w) := rfl

theorem logMap_expMap {x : realSpace K}
    (hx : mixedEmbedding.norm (mixedSpaceOfRealSpace (expMap x)) = 1) :
    logMap (mixedSpaceOfRealSpace (expMap x)) = fun w ↦ x w.1 := by
  ext
  rw [logMap, normAtPlace_mixedSpaceOfRealSpace (Real.exp_nonneg _), expMap_apply, Real.log_exp,
    mul_sub, mul_inv_cancel_left₀ mult_coe_ne_zero, hx, Real.log_one, zero_mul, mul_zero, sub_zero]

theorem sum_expMap_symm_apply {x : K} (hx : x ≠ 0) :
    ∑ w : InfinitePlace K, expMap.symm ((normAtAllPlaces (mixedEmbedding K x))) w =
      Real.log (|Algebra.norm ℚ x| : ℚ) := by
  simp_rw [← prod_eq_abs_norm, Real.log_prod (fun _ _ ↦ pow_ne_zero _ ((map_ne_zero _).mpr hx)),
    Real.log_pow, expMap_symm_apply, normAtAllPlaces_mixedEmbedding]

/--
The derivative of `expMap`, see `hasFDerivAt_expMap`.
-/
abbrev fderiv_expMap (x : realSpace K) : realSpace K →L[ℝ] realSpace K :=
  .pi fun w ↦ (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (deriv_expMap_single w (x w))).comp
    (.proj w)

theorem hasFDerivAt_expMap (x : realSpace K) : HasFDerivAt expMap (fderiv_expMap x) x := by
  simpa [expMap, fderiv_expMap, hasFDerivAt_pi', OpenPartialHomeomorph.pi_apply,
    ContinuousLinearMap.proj_pi] using
    fun w ↦ (hasDerivAt_expMap_single w _).hasFDerivAt.comp x (hasFDerivAt_apply w x)

end expMap

noncomputable section completeBasis

variable [NumberField K]

variable {K}

open scoped Classical in
/--
A fixed equiv between `Fin (rank K)` and `{w : InfinitePlace K // w ≠ w₀}`.
-/
def equivFinRank : Fin (rank K) ≃ {w : InfinitePlace K // w ≠ w₀} :=
  Fintype.equivOfCardEq <| by
    rw [Fintype.card_subtype_compl, Fintype.card_ofSubsingleton, Fintype.card_fin, rank]

open scoped Classical in
variable (K) in
/--
A family of elements in the `realSpace K` formed of the image of the fundamental units
and the vector `(mult w)_w`. This family is in fact a basis of `realSpace K`, see `completeBasis`.
-/
def completeFamily : InfinitePlace K → realSpace K :=
  fun i ↦ if hi : i = w₀ then fun w ↦ mult w else
    expMap.symm <| normAtAllPlaces <| mixedEmbedding K <| fundSystem K <| equivFinRank.symm ⟨i, hi⟩

/--
An auxiliary map from `realSpace K` to `logSpace K` used to prove that `completeFamily` is
linearly independent, see `linearIndependent_completeFamily`.
-/
def realSpaceToLogSpace : realSpace K →ₗ[ℝ] {w : InfinitePlace K // w ≠ w₀} → ℝ where
  toFun := fun x w ↦ x w.1 - w.1.mult * (∑ w', x w') * (Module.finrank ℚ K : ℝ)⁻¹
  map_add' := fun _ _ ↦ funext fun _ ↦ by simpa [sum_add_distrib] using by ring
  map_smul' := fun _ _ ↦ funext fun _ ↦ by simpa [← mul_sum] using by ring

theorem realSpaceToLogSpace_apply (x : realSpace K) (w : {w : InfinitePlace K // w ≠ w₀}) :
    realSpaceToLogSpace x w = x w - w.1.mult * (∑ w', x w') * (Module.finrank ℚ K : ℝ)⁻¹ := rfl

theorem realSpaceToLogSpace_expMap_symm {x : K} (hx : x ≠ 0) :
    realSpaceToLogSpace (expMap.symm (normAtAllPlaces (mixedEmbedding K x))) =
      logMap (mixedEmbedding K x) := by
  ext w
  simp_rw [realSpaceToLogSpace_apply, sum_expMap_symm_apply hx, expMap_symm_apply,
    logMap, normAtPlace_apply, mul_sub, mul_assoc, norm_eq_norm]

theorem realSpaceToLogSpace_completeFamily_of_eq :
    realSpaceToLogSpace (completeFamily K w₀) = 0 := by
  ext
  rw [realSpaceToLogSpace_apply, completeFamily, dif_pos rfl, ← Nat.cast_sum, sum_mult_eq,
    mul_inv_cancel_right₀ (Nat.cast_ne_zero.mpr Module.finrank_pos.ne'), sub_self, Pi.zero_apply]

theorem realSpaceToLogSpace_completeFamily_of_ne (i : {w : InfinitePlace K // w ≠ w₀}) :
    realSpaceToLogSpace (completeFamily K i) = basisUnitLattice K (equivFinRank.symm i) := by
  ext
  rw [← logEmbedding_fundSystem, ← logMap_eq_logEmbedding, completeFamily, dif_neg,
    realSpaceToLogSpace_expMap_symm]
  exact coe_ne_zero _

theorem sum_eq_zero_of_mem_span_completeFamily {x : realSpace K}
    (hx : x ∈ Submodule.span ℝ (Set.range fun w : {w // w ≠ w₀} ↦ completeFamily K w.1)) :
    ∑ w, x w = 0 := by
  induction hx using Submodule.span_induction with
  | mem _ h =>
      obtain ⟨w, rfl⟩ := h
      simp_rw [completeFamily, dif_neg w.prop, sum_expMap_symm_apply (coe_ne_zero _),
        Units.norm, Rat.cast_one, Real.log_one]
  | zero => simp
  | add _ _ _ _ hx hy => simp [sum_add_distrib, hx, hy]
  | smul _ _ _ hx => simp [← mul_sum, hx]

variable (K)

theorem linearIndependent_completeFamily :
    LinearIndependent ℝ (completeFamily K) := by
  classical
  have h₁ : LinearIndependent ℝ (fun w : {w // w ≠ w₀} ↦ completeFamily K w.1) := by
    refine LinearIndependent.of_comp realSpaceToLogSpace ?_
    simp_rw [Function.comp_def, realSpaceToLogSpace_completeFamily_of_ne]
    convert (((basisUnitLattice K).ofZLatticeBasis ℝ _).reindex equivFinRank).linearIndependent
    simp
  have h₂ : completeFamily K w₀ ∉ Submodule.span ℝ
      (Set.range (fun w : {w // w ≠ w₀} ↦ completeFamily K w.1)) := by
    intro h
    have := sum_eq_zero_of_mem_span_completeFamily h
    rw [completeFamily, dif_pos rfl, ← Nat.cast_sum, sum_mult_eq, Nat.cast_eq_zero] at this
    exact Module.finrank_pos.ne' this
  rw [← linearIndependent_equiv (Equiv.optionSubtypeNe w₀), linearIndependent_option]
  exact ⟨h₁, h₂⟩

/--
A basis of `realSpace K` formed by the image of the fundamental units
(which form a basis of a subspace `{x : realSpace K | ∑ w, x w = 0}`) and the vector `(mult w)_w`.
For `i ≠ w₀`, the image of `completeBasis K i` by the natural restriction map
`realSpace K → logSpace K` is `basisUnitLattice K`
-/
def completeBasis : Basis (InfinitePlace K) ℝ (realSpace K) :=
  basisOfLinearIndependentOfCardEqFinrank (linearIndependent_completeFamily K)
    (Module.finrank_fintype_fun_eq_card _).symm

theorem completeBasis_apply_of_eq :
    completeBasis K w₀ = fun w ↦ (mult w : ℝ) := by
  rw [completeBasis, coe_basisOfLinearIndependentOfCardEqFinrank, completeFamily, dif_pos rfl]

theorem completeBasis_apply_of_ne (i : {w : InfinitePlace K // w ≠ w₀}) :
    completeBasis K i =
      expMap.symm (normAtAllPlaces (mixedEmbedding K (fundSystem K (equivFinRank.symm i)))) := by
  rw [completeBasis, coe_basisOfLinearIndependentOfCardEqFinrank, completeFamily, dif_neg]

theorem expMap_basis_of_eq :
    expMap (completeBasis K w₀) = fun _ ↦ Real.exp 1 := by
  ext
  simp_rw [expMap_apply, completeBasis_apply_of_eq, inv_mul_cancel₀ mult_coe_ne_zero]

theorem expMap_basis_of_ne (i : {w : InfinitePlace K // w ≠ w₀}) :
    expMap (completeBasis K i) =
      normAtAllPlaces (mixedEmbedding K (fundSystem K (equivFinRank.symm i))) := by
  rw [completeBasis_apply_of_ne, expMap.right_inv (by simp [expMap_target, pos_at_place])]

theorem abs_det_completeBasis_equivFunL_symm :
    |((completeBasis K).equivFunL.symm : realSpace K →L[ℝ] realSpace K).det| =
      Module.finrank ℚ K * regulator K := by
  classical
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (completeBasis K), ← Matrix.det_transpose,
    regulator_eq_regOfFamily_fundSystem, finrank_mul_regOfFamily_eq_det _ w₀ equivFinRank.symm]
  congr 2 with w i
  rw [Matrix.transpose_apply, LinearMap.toMatrix_apply, Matrix.of_apply, ← Basis.equivFunL_apply,
    ContinuousLinearMap.coe_coe, ContinuousLinearEquiv.coe_apply,
    (completeBasis K).equivFunL.apply_symm_apply]
  split_ifs with hw
  · rw [hw, completeBasis_apply_of_eq]
  · simp_rw [completeBasis_apply_of_ne K ⟨w, hw⟩, expMap_symm_apply, normAtAllPlaces_mixedEmbedding]

end completeBasis

noncomputable section expMapBasis

variable [NumberField K]

variable {K}

/--
The map that sends `x : realSpace K` to
`Real.exp (x w₀) * ∏_{i ≠ w₀} |ηᵢ| ^ x i` where `|ηᵢ|` denote the vector of `realSpace K` given
by `w (ηᵢ)` and `ηᵢ` denote the units in `fundSystem K`, see `expMapBasis_apply'`.
-/
def expMapBasis : OpenPartialHomeomorph (realSpace K) (realSpace K) :=
  (completeBasis K).equivFunL.symm.toHomeomorph.transOpenPartialHomeomorph expMap

variable (K)

theorem expMapBasis_source :
    expMapBasis.source = (Set.univ : Set (realSpace K)) := by
  simp [expMapBasis, expMap_source]

theorem injective_expMapBasis :
    Function.Injective (expMapBasis : realSpace K → realSpace K) :=
  (injective_expMap K).comp (completeBasis K).equivFun.symm.injective

theorem continuous_expMapBasis :
    Continuous (expMapBasis : realSpace K → realSpace K) :=
  (continuous_expMap K).comp (ContinuousLinearEquiv.continuous _)

variable {K}

theorem expMapBasis_pos (x : realSpace K) (w : InfinitePlace K) :
    0 < expMapBasis x w := expMap_pos _ _

theorem expMapBasis_nonneg (x : realSpace K) (w : InfinitePlace K) :
    0 ≤ expMapBasis x w := (expMapBasis_pos _ _).le

theorem expMapBasis_apply (x : realSpace K) :
    expMapBasis x = expMap ((completeBasis K).equivFun.symm x) := rfl

open scoped Classical in
theorem expMapBasis_apply' (x : realSpace K) :
    expMapBasis x = Real.exp (x w₀) •
      fun w : InfinitePlace K ↦
         ∏ i : {w // w ≠ w₀}, w (fundSystem K (equivFinRank.symm i)) ^ x i := by
  simp_rw [expMapBasis_apply, Basis.equivFun_symm_apply, Fintype.sum_eq_add_sum_subtype_ne _ w₀,
    expMap_add, expMap_smul, expMap_basis_of_eq, Pi.pow_def, Real.exp_one_rpow, Pi.mul_def,
    expMap_sum, expMap_smul, expMap_basis_of_ne, Pi.smul_def, smul_eq_mul, prod_apply, Pi.pow_apply,
    normAtAllPlaces_mixedEmbedding]

open scoped Classical in
theorem expMapBasis_apply'' (x : realSpace K) :
    expMapBasis x = Real.exp (x w₀) • expMapBasis (fun i ↦ if i = w₀ then 0 else x i) := by
  rw [expMapBasis_apply', expMapBasis_apply', if_pos rfl, smul_smul, ← Real.exp_add, add_zero]
  conv_rhs =>
    enter [2, w, 2, i]
    rw [if_neg i.prop]

theorem prod_expMapBasis_pow (x : realSpace K) :
    ∏ w, (expMapBasis x w) ^ w.mult = Real.exp (x w₀) ^ Module.finrank ℚ K := by
  simp_rw [expMapBasis_apply', Pi.smul_def, smul_eq_mul, mul_pow, prod_mul_distrib,
    prod_pow_eq_pow_sum, sum_mult_eq, ← prod_pow]
  rw [prod_comm]
  simp_rw [Real.rpow_pow_comm (apply_nonneg _ _), Real.finset_prod_rpow _ _
    fun _ _ ↦ pow_nonneg (apply_nonneg _ _) _, prod_eq_abs_norm, Units.norm, Rat.cast_one,
    Real.one_rpow, prod_const_one, mul_one]

theorem norm_expMapBasis (x : realSpace K) :
    mixedEmbedding.norm (mixedSpaceOfRealSpace (expMapBasis x)) =
      Real.exp (x w₀) ^ Module.finrank ℚ K := by
  simpa only [mixedEmbedding.norm_apply,
    normAtPlace_mixedSpaceOfRealSpace (expMapBasis_pos _ _).le] using prod_expMapBasis_pow x

theorem norm_expMapBasis_ne_zero (x : realSpace K) :
    mixedEmbedding.norm (mixedSpaceOfRealSpace (expMapBasis x)) ≠ 0 :=
  norm_expMapBasis x ▸ pow_ne_zero _ (Real.exp_ne_zero _)

open scoped Classical in
theorem logMap_expMapBasis (x : realSpace K) :
    logMap (mixedSpaceOfRealSpace (expMapBasis x)) ∈
        ZSpan.fundamentalDomain ((basisUnitLattice K).ofZLatticeBasis ℝ (unitLattice K))
      ↔ ∀ w, w ≠ w₀ → x w ∈ Set.Ico 0 1 := by
  classical
  simp_rw [ZSpan.mem_fundamentalDomain, equivFinRank.forall_congr_left, Subtype.forall]
  refine forall₂_congr fun w hw ↦ ?_
  rw [expMapBasis_apply'', map_smul, logMap_real_smul (norm_expMapBasis_ne_zero _)
    (Real.exp_ne_zero _), expMapBasis_apply, logMap_expMap (by rw [← expMapBasis_apply,
    norm_expMapBasis, if_pos rfl, Real.exp_zero, one_pow]), Basis.equivFun_symm_apply,
    Fintype.sum_eq_add_sum_subtype_ne _ w₀, if_pos rfl, zero_smul, zero_add]
  conv_lhs =>
    enter [2, 1, 2, w, 2, i]
    rw [if_neg i.prop]
  simp_rw [sum_apply, ← sum_fn, map_sum, Pi.smul_apply, ← Pi.smul_def, map_smul,
    completeBasis_apply_of_ne, expMap_symm_apply, normAtAllPlaces_mixedEmbedding,
    ← logEmbedding_component, logEmbedding_fundSystem, Finsupp.coe_finset_sum, Finsupp.coe_smul,
    sum_apply, Pi.smul_apply, Basis.ofZLatticeBasis_repr_apply, Basis.repr_self,
    Finsupp.single_apply, EmbeddingLike.apply_eq_iff_eq, Int.cast_ite, Int.cast_one, Int.cast_zero,
    smul_ite, smul_eq_mul, mul_one, mul_zero, Fintype.sum_ite_eq']

theorem normAtAllPlaces_image_preimage_expMapBasis (s : Set (realSpace K)) :
    normAtAllPlaces '' (normAtAllPlaces ⁻¹' (expMapBasis '' s)) = expMapBasis '' s := by
  apply normAtAllPlaces_image_preimage_of_nonneg
  rintro _ ⟨x, _, rfl⟩ w
  exact (expMapBasis_pos _ _).le

open scoped Classical in
theorem prod_deriv_expMap_single (x : realSpace K) :
    ∏ w, deriv_expMap_single w ((completeBasis K).equivFun.symm x w) =
      Real.exp (x w₀) ^ Module.finrank ℚ K * (∏ w : {w // IsComplex w}, expMapBasis x w.1)⁻¹ *
        (2⁻¹) ^ nrComplexPlaces K := by
  simp only [deriv_expMap_single, expMap_single_apply]
  rw [Finset.prod_mul_distrib]
  congr 1
  · simp_rw [← prod_expMapBasis_pow, prod_eq_prod_mul_prod, expMapBasis_apply, expMap_apply,
      mult_isReal, mult_isComplex, pow_one, Finset.prod_pow, pow_two, mul_assoc, mul_inv_cancel₀
      (Finset.prod_ne_zero_iff.mpr <| fun _ _ ↦ Real.exp_ne_zero _), mul_one]
  · simp [prod_eq_prod_mul_prod, mult_isReal, mult_isComplex]

variable (K)

/--
The derivative of `expMapBasis`, see `hasFDerivAt_expMapBasis`.
-/
abbrev fderiv_expMapBasis (x : realSpace K) : realSpace K →L[ℝ] realSpace K :=
  (fderiv_expMap ((completeBasis K).equivFun.symm x)).comp
    (completeBasis K).equivFunL.symm.toContinuousLinearMap

theorem hasFDerivAt_expMapBasis (x : realSpace K) :
    HasFDerivAt expMapBasis (fderiv_expMapBasis K x) x := by
  change HasFDerivAt (expMap ∘ (completeBasis K).equivFunL.symm) (fderiv_expMapBasis K x) x
  exact (hasFDerivAt_expMap _).comp x (completeBasis K).equivFunL.symm.hasFDerivAt

open Classical ContinuousLinearMap in
theorem abs_det_fderiv_expMapBasis (x : realSpace K) :
    |(fderiv_expMapBasis K x).det| =
      Real.exp (x w₀ * Module.finrank ℚ K) *
      (∏ w : {w // IsComplex w}, expMapBasis x w.1)⁻¹ * 2⁻¹ ^ nrComplexPlaces K *
        (Module.finrank ℚ K) * regulator K := by
  simp_rw [fderiv_expMapBasis, det, coe_comp, LinearMap.det_comp, fderiv_expMap, coe_pi, coe_comp,
    coe_proj, LinearMap.det_pi, LinearMap.det_ring, ContinuousLinearMap.coe_coe, smulRight_apply,
    one_apply, one_smul, abs_mul, abs_det_completeBasis_equivFunL_symm, prod_deriv_expMap_single]
  simp_rw [abs_mul, Real.exp_mul, abs_pow, Real.rpow_natCast, abs_of_nonneg (Real.exp_nonneg _),
    abs_inv, abs_prod, abs_of_nonneg (expMapBasis_nonneg _ _), Nat.abs_ofNat]
  ring

variable {K}

open ENNReal MeasureTheory

open scoped Classical in
theorem setLIntegral_expMapBasis_image {s : Set (realSpace K)} (hs : MeasurableSet s)
    {f : (InfinitePlace K → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x in expMapBasis '' s, f x =
      (2 : ℝ≥0∞)⁻¹ ^ nrComplexPlaces K * ENNReal.ofReal (regulator K) * (Module.finrank ℚ K) *
        ∫⁻ x in s, ENNReal.ofReal (Real.exp (x w₀ * Module.finrank ℚ K)) *
          (∏ i : {w : InfinitePlace K // IsComplex w},
            .ofReal (expMapBasis (fun w ↦ x w) i))⁻¹ * f (expMapBasis x) := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
    (fun x _ ↦ (hasFDerivAt_expMapBasis K x).hasFDerivWithinAt) (injective_expMapBasis K).injOn]
  simp_rw [abs_det_fderiv_expMapBasis]
  have : Measurable expMapBasis := (continuous_expMapBasis K).measurable
  rw [← lintegral_const_mul _ (by fun_prop)]
  congr with x
  have : 0 ≤ (∏ w : {w // IsComplex w}, expMapBasis x w.1)⁻¹ :=
    inv_nonneg.mpr <| Finset.prod_nonneg fun _ _ ↦ (expMapBasis_pos _ _).le
  rw [ofReal_mul (by positivity), ofReal_mul (by positivity), ofReal_mul (by positivity),
    ofReal_mul (by positivity), ofReal_pow (by positivity), ofReal_inv_of_pos (Finset.prod_pos
    fun _ _ ↦ expMapBasis_pos _ _), ofReal_inv_of_pos zero_lt_two, ofReal_ofNat, ofReal_natCast,
    ofReal_prod_of_nonneg (fun _ _ ↦ (expMapBasis_pos _ _).le)]
  ring

end expMapBasis

section paramSet

variable [NumberField K]

open scoped Classical in
/--
The set that parametrizes `normAtAllPlaces '' (normLeOne K)`, see
`normAtAllPlaces_normLeOne_eq_image`.
-/
abbrev paramSet : Set (realSpace K) :=
  Set.univ.pi fun w ↦ if w = w₀ then Set.Iic 0 else Set.Ico 0 1

theorem measurableSet_paramSet :
    MeasurableSet (paramSet K) := by
  refine MeasurableSet.univ_pi fun _ ↦ ?_
  split_ifs
  · exact measurableSet_Iic
  · exact measurableSet_Ico

open scoped Classical in
theorem interior_paramSet :
    interior (paramSet K) = Set.univ.pi fun w ↦ if w = w₀ then Set.Iio 0 else Set.Ioo 0 1 := by
  simp [interior_pi_set Set.finite_univ, apply_ite]

@[deprecated (since := "2025-08-26")] alias measurableSet_interior_paramSet :=
  measurableSet_interior

open scoped Classical in
theorem closure_paramSet :
    closure (paramSet K) = Set.univ.pi fun w ↦ if w = w₀ then Set.Iic 0 else Set.Icc 0 1 := by
  simp [closure_pi_set, apply_ite]

theorem normAtAllPlaces_normLeOne_eq_image :
    normAtAllPlaces '' (normLeOne K) = expMapBasis '' (paramSet K) := by
  ext x
  by_cases hx : ∀ w, 0 < x w
  · rw [← expMapBasis.right_inv (Set.mem_univ_pi.mpr hx), (injective_expMapBasis K).mem_set_image]
    simp only [normAtAllPlaces_normLeOne, Set.mem_inter_iff, Set.mem_setOf_eq, expMapBasis_nonneg,
      Set.mem_preimage, logMap_expMapBasis, implies_true, and_true, norm_expMapBasis,
      pow_le_one_iff_of_nonneg (Real.exp_nonneg _) Module.finrank_pos.ne', Real.exp_le_one_iff,
      ne_eq, pow_eq_zero_iff', Real.exp_ne_zero, false_and, not_false_eq_true, Set.mem_univ_pi]
    refine ⟨fun ⟨h₁, h₂⟩ w ↦ ?_, fun h ↦ ⟨fun w hw ↦ by simpa [hw] using h w, by simpa using h w₀⟩⟩
    · split_ifs with hw
      · exact hw ▸ h₂
      · exact h₁ w hw
  · refine ⟨?_, ?_⟩
    · rintro ⟨a, ⟨ha, _⟩, rfl⟩
      exact (hx fun w ↦ fundamentalCone.normAtPlace_pos_of_mem ha w).elim
    · rintro ⟨a, _, rfl⟩
      exact (hx fun w ↦ expMapBasis_pos a w).elim

theorem normLeOne_eq_preimage :
    normLeOne K = normAtAllPlaces ⁻¹' (expMapBasis '' (paramSet K)) := by
  rw [normLeOne_eq_preimage_image, normAtAllPlaces_normLeOne_eq_image]

theorem subset_interior_normLeOne :
    normAtAllPlaces ⁻¹' (expMapBasis '' interior (paramSet K)) ⊆ interior (normLeOne K) := by
  rw [normLeOne_eq_preimage]
  refine subset_trans (Set.preimage_mono ?_) <|
    preimage_interior_subset_interior_preimage (continuous_normAtAllPlaces K)
  have : IsOpen (expMapBasis '' (interior (paramSet K))) :=
    expMapBasis.isOpen_image_of_subset_source isOpen_interior (by simp [expMapBasis_source])
  exact interior_maximal (Set.image_mono interior_subset) this

open ENNReal MeasureTheory

theorem closure_paramSet_ae_interior : closure (paramSet K) =ᵐ[volume] interior (paramSet K) := by
  rw [closure_paramSet, interior_paramSet, volume_pi]
  refine Measure.ae_eq_set_pi fun w _ ↦ ?_
  split_ifs
  · exact Iio_ae_eq_Iic.symm
  · exact Ioo_ae_eq_Icc.symm

theorem setLIntegral_paramSet_exp {n : ℕ} (hn : 0 < n) :
    ∫⁻ (x : realSpace K) in paramSet K, .ofReal (Real.exp (x w₀ * n)) = (n : ℝ≥0∞)⁻¹ := by
  classical
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  rw [volume_pi, paramSet, Measure.restrict_pi_pi, lintegral_eq_lmarginal_univ 0,
    lmarginal_erase' _ (by fun_prop) (Finset.mem_univ w₀), if_pos rfl]
  simp_rw [Function.update_self, lmarginal, lintegral_const, Measure.pi_univ, if_neg
    (Finset.ne_of_mem_erase (Subtype.prop _)), Measure.restrict_apply_univ, Real.volume_Ico,
    sub_zero, ofReal_one, prod_const_one, mul_one, mul_comm _ (n : ℝ)]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_mul_Iic hn _), integral_exp_mul_Iic
    hn, mul_zero, Real.exp_zero, ofReal_div_of_pos hn, ofReal_one, ofReal_natCast, one_div]
  filter_upwards with _ using Real.exp_nonneg _

end paramSet

section compactSet

variable [NumberField K]

open Pointwise

open scoped Classical in
/--
A compact set that contains `expMapBasis '' closure (paramSet K)` and furthermore is almost
equal to it, see `compactSet_ae`.
-/
abbrev compactSet : Set (realSpace K) :=
  (Set.Icc (0 : ℝ) 1) • (expMapBasis '' Set.univ.pi fun w ↦ if w = w₀ then {0} else Set.Icc 0 1)

theorem isCompact_compactSet :
    IsCompact (compactSet K) := by
  refine isCompact_Icc.smul_set <| (isCompact_univ_pi fun w ↦ ?_).image_of_continuousOn
    (continuous_expMapBasis K).continuousOn
  split_ifs
  · exact isCompact_singleton
  · exact isCompact_Icc

theorem zero_mem_compactSet :
    0 ∈ compactSet K := by
  refine Set.zero_mem_smul_iff.mpr (Or.inl ⟨Set.left_mem_Icc.mpr zero_le_one, ?_⟩)
  exact Set.image_nonempty.mpr (Set.univ_pi_nonempty_iff.mpr (by aesop))

theorem nonneg_of_mem_compactSet {x : realSpace K} (hx : x ∈ compactSet K) (w : InfinitePlace K) :
    0 ≤ x w := by
  obtain ⟨c, hc, ⟨_, ⟨⟨a, ha, rfl⟩, _, rfl⟩⟩⟩ := hx
  exact mul_nonneg hc.1 (expMapBasis_pos _ _).le

variable {K} in
theorem compactSet_eq_union_aux₁ {x : realSpace K} (hx₀ : x ≠ 0)
    (hx₁ : x ∈ compactSet K) :
    x ∈ expMapBasis '' closure (paramSet K) := by
  classical
  obtain ⟨c, hc, ⟨_, ⟨y, hy, rfl⟩, rfl⟩⟩ := hx₁
  refine ⟨fun w ↦ if w = w₀ then Real.log c else y w, ?_, ?_⟩
  · rw [closure_paramSet, Set.mem_univ_pi]
    intro w
    split_ifs with h
    · refine Real.log_nonpos hc.1 hc.2
    · simpa [h] using hy w (Set.mem_univ _)
  · have hc' : 0 < c := by
      contrapose! hx₀
      rw [le_antisymm hx₀ hc.1, zero_smul]
    rw [expMapBasis_apply'', if_pos rfl, Real.exp_log hc']
    congr with w
    split_ifs with h
    · simpa [h, eq_comm] using hy w₀
    · rfl

variable {K} in
theorem compactSet_eq_union_aux₂ {x : realSpace K} (hx₀ : x ≠ 0)
    (hx₁ : x ∈ expMapBasis '' closure (paramSet K)) :
    x ∈ compactSet K := by
  classical
  simp only [closure_paramSet, Set.mem_image, Set.mem_smul, exists_exists_and_eq_and] at hx₁ ⊢
  obtain ⟨y, hy, rfl⟩ := hx₁
  refine ⟨Real.exp (y w₀), ⟨Real.exp_nonneg _, ?_⟩,
        fun i ↦ if i = w₀ then 0 else y i, Set.mem_univ_pi.mpr fun w ↦ ?_,
        by rw [expMapBasis_apply'' y]⟩
  · exact Real.exp_le_one_iff.mpr (by simpa using hy w₀ (Set.mem_univ _))
  · split_ifs with h
    · rfl
    · simpa [h] using hy w (Set.mem_univ _)

theorem compactSet_eq_union :
    compactSet K = expMapBasis '' closure (paramSet K) ∪ {0} := by
  classical
  ext x
  by_cases hx₀ : x = 0
  · simpa [hx₀] using zero_mem_compactSet K
  · refine ⟨fun hx ↦ Set.mem_union_left _ (compactSet_eq_union_aux₁ hx₀ hx), fun hx ↦ ?_⟩
    simp only [Set.union_singleton, Set.mem_insert_iff, hx₀, false_or] at hx
    exact compactSet_eq_union_aux₂ hx₀ hx

theorem expMapBasis_closure_subset_compactSet :
    expMapBasis '' closure (paramSet K) ⊆ compactSet K := by
  rw [compactSet_eq_union]
  exact Set.subset_union_left

theorem closure_normLeOne_subset :
    closure (normLeOne K) ⊆ normAtAllPlaces ⁻¹' (compactSet K) := by
  rw [normLeOne_eq_preimage]
  refine ((continuous_normAtAllPlaces K).closure_preimage_subset _).trans (Set.preimage_mono ?_)
  refine (isCompact_compactSet K).isClosed.closure_subset_iff.mpr ?_
  exact (Set.image_mono subset_closure).trans (expMapBasis_closure_subset_compactSet _)

open MeasureTheory

theorem compactSet_ae :
    compactSet K =ᵐ[volume] expMapBasis '' closure (paramSet K) := by
  rw [compactSet_eq_union]
  exact union_ae_eq_left_of_ae_eq_empty (by simp)

end compactSet

section main_results

variable [NumberField K]

open Bornology ENNReal MeasureTheory

theorem isBounded_normLeOne :
    IsBounded (normLeOne K) := by
  classical
  rw [normLeOne_eq_preimage]
  suffices IsBounded (expMapBasis '' paramSet K) by
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp this
    refine isBounded_iff_forall_norm_le.mpr ⟨C, fun x hx ↦ ?_⟩
    rw [norm_eq_sup'_normAtPlace]
    refine sup'_le _ _ fun w _ ↦ ?_
    simpa [normAtAllPlaces_apply, Real.norm_of_nonneg (normAtPlace_nonneg w x)]
      using (pi_norm_le_iff_of_nonempty _).mp (hC _ hx) w
  refine IsBounded.subset ?_ (Set.image_mono subset_closure)
  exact (isCompact_compactSet K).isBounded.subset (expMapBasis_closure_subset_compactSet K)

open scoped Classical in
theorem volume_normLeOne : volume (normLeOne K) =
    2 ^ nrRealPlaces K * NNReal.pi ^ nrComplexPlaces K * .ofReal (regulator K) := by
  rw [volume_eq_two_pow_mul_two_pi_pow_mul_integral (normLeOne_eq_preimage_image K).symm
    (measurableSet_normLeOne K), normLeOne_eq_preimage,
    normAtAllPlaces_image_preimage_expMapBasis,
    setLIntegral_expMapBasis_image (measurableSet_paramSet K) (by fun_prop)]
  simp_rw [ENNReal.inv_mul_cancel_right
    (Finset.prod_ne_zero_iff.mpr fun _ _ ↦ ofReal_ne_zero_iff.mpr (expMapBasis_pos _ _))
    (prod_ne_top fun _ _ ↦ ofReal_ne_top)]
  rw [setLIntegral_paramSet_exp K Module.finrank_pos, ofReal_mul zero_le_two, mul_pow,
    ofReal_ofNat, ENNReal.mul_inv_cancel_right (Nat.cast_ne_zero.mpr Module.finrank_pos.ne')
    (natCast_ne_top _), coe_nnreal_eq, NNReal.coe_real_pi, mul_mul_mul_comm, ← ENNReal.inv_pow,
    ← mul_assoc, ← mul_assoc, ENNReal.inv_mul_cancel_right (pow_ne_zero _ two_ne_zero)
    (pow_ne_top ENNReal.ofNat_ne_top)]

open scoped Classical in
theorem volume_interior_eq_volume_closure :
    volume (interior (normLeOne K)) = volume (closure (normLeOne K)) := by
  have h₁ : MeasurableSet (normAtAllPlaces ⁻¹' compactSet K) :=
    (isCompact_compactSet K).measurableSet.preimage (continuous_normAtAllPlaces K).measurable
  have h₂ : MeasurableSet (normAtAllPlaces ⁻¹' (expMapBasis '' interior (paramSet K))) := by
    refine MeasurableSet.preimage ?_ (continuous_normAtAllPlaces K).measurable
    refine MeasurableSet.image_of_continuousOn_injOn ?_ (continuous_expMapBasis K).continuousOn
      (injective_expMapBasis K).injOn
    exact measurableSet_interior
  refine le_antisymm (measure_mono interior_subset_closure) ?_
  refine (measure_mono (closure_normLeOne_subset K)).trans ?_
  refine le_of_eq_of_le ?_ (measure_mono (subset_interior_normLeOne K))
  rw [volume_eq_two_pow_mul_two_pi_pow_mul_integral Set.preimage_image_preimage h₁,
    normAtAllPlaces_image_preimage_of_nonneg (fun x a w ↦ nonneg_of_mem_compactSet K a w),
    volume_eq_two_pow_mul_two_pi_pow_mul_integral Set.preimage_image_preimage h₂,
    normAtAllPlaces_image_preimage_expMapBasis, setLIntegral_congr (compactSet_ae K),
    setLIntegral_expMapBasis_image measurableSet_closure (by fun_prop),
    setLIntegral_expMapBasis_image measurableSet_interior (by fun_prop),
    setLIntegral_congr (closure_paramSet_ae_interior K)]

open scoped Classical in
theorem volume_frontier_normLeOne :
     volume (frontier (normLeOne K)) = 0 := by
  rw [frontier, measure_diff, volume_interior_eq_volume_closure, tsub_self]
  · exact interior_subset_closure
  · exact measurableSet_interior.nullMeasurableSet
  · refine lt_top_iff_ne_top.mp <| lt_of_le_of_lt (measure_mono interior_subset) ?_
    rw [volume_normLeOne]
    exact Batteries.compareOfLessAndEq_eq_lt.mp rfl

end main_results

end NumberField.mixedEmbedding.fundamentalCone
