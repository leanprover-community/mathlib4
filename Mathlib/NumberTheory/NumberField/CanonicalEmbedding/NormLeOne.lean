/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone

/-!
# Fundamental Cone: set of elements of norm ≤ 1

In this file, we study the subset `NormLeOne` of the `fundamentalCone` of elements `x` with
`mixedEmbedding.norm x ≤ 1`.

Mainly, we prove that this is bounded, its frontier has volume zero and compute its volume.

## Strategy of proof

The proof is loosely based on the strategy given in [D. Marcus, *Number Fields*][marcus1977number].

1. since `NormLeOne K` is norm-stable, in the sense that
  `normLeOne K = normAtAllPlaces⁻¹' (normAtAllPlaces '' (normLeOne K))`,
  see `normLeOne_eq_primeage_image`, it's enough to study the subset
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
  `expMapBasis_apply'`.

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

open Finset NumberField NumberField.InfinitePlace NumberField.mixedEmbedding NumberField.Units
  NumberField.Units.dirichletUnitTheorem

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

theorem normLeOne_eq_primeage_image :
    normLeOne K = normAtAllPlaces⁻¹' (normAtAllPlaces '' (normLeOne K)) := by
  refine subset_antisymm (Set.subset_preimage_image _ _) ?_
  rintro x ⟨y, hy₁, hy₂⟩
  rw [mem_normLeOne, ← normAtAllPlaces_mem_fundamentalCone_iff, ← norm_normAtAllPlaces,
    ← mem_normLeOne] at hy₁ ⊢
  rwa [← hy₂]

open scoped Classical in
theorem normAtAllPlaces_normLeOne :
    normAtAllPlaces '' (normLeOne K) =
    mixedSpaceOfRealSpace⁻¹'
      (logMap⁻¹'
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
def expMap_single (w : InfinitePlace K) : PartialHomeomorph ℝ ℝ where
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

variable [NumberField K]

/--
The map from `realSpace K → realSpace K` whose components is given by `expMap_single`. It is, in
some respect, a right inverse of `logMap`, see `logMap_expMap`.
-/
def expMap : PartialHomeomorph (realSpace K) (realSpace K) :=
  PartialHomeomorph.pi fun w ↦ expMap_single w

variable (K)

theorem expMap_source :
    expMap.source = (Set.univ : Set (realSpace K)) := by
  simp_rw [expMap, PartialHomeomorph.pi_toPartialEquiv, PartialEquiv.pi_source, expMap_single,
    Set.pi_univ Set.univ]

theorem expMap_target :
    expMap.target = Set.univ.pi fun (_ : InfinitePlace K) ↦ Set.Ioi 0 := by
  simp_rw [expMap, PartialHomeomorph.pi_toPartialEquiv, PartialEquiv.pi_target, expMap_single]

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
  simp_rw [← prod_eq_abs_norm, Real.log_prod _ _ (fun _ _ ↦ pow_ne_zero _ ((map_ne_zero _).mpr hx)),
    Real.log_pow, expMap_symm_apply, normAtAllPlaces_mixedEmbedding]

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

theorem realSpaceToLogSpace_apply (x :realSpace K) (w : {w : InfinitePlace K // w ≠ w₀}) :
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
      simp_rw [completeFamily,  dif_neg w.prop, sum_expMap_symm_apply (coe_ne_zero _),
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
  rw [completeBasis_apply_of_ne, PartialHomeomorph.right_inv _
    (by simp [expMap_target, pos_at_place])]

end completeBasis

noncomputable section expMapBasis

variable [NumberField K]

variable {K}

/--
The map that sends `x : realSpace K` to
`Real.exp (x w₀) * ∏_{i ≠ w₀} |ηᵢ| ^ x i` where `|ηᵢ|` denote the vector of `realSpace K` given
by `w (ηᵢ)` and `ηᵢ` denote the units in `fundSystem K`, see `expMapBasis_apply'`.
-/
def expMapBasis : PartialHomeomorph (realSpace K) (realSpace K) :=
  (completeBasis K).equivFunL.symm.toHomeomorph.transPartialHomeomorph expMap

variable (K)

theorem expMapBasis_source :
    expMapBasis.source = (Set.univ : Set (realSpace K)) := by
  simp [expMapBasis, expMap_source]

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

end expMapBasis

end NumberField.mixedEmbedding.fundamentalCone
