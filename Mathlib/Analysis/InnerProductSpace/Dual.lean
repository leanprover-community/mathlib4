/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Analysis.Normed.Group.NullSubmodule
public import Mathlib.Topology.Algebra.Module.PerfectPairing

/-!
# The Fréchet-Riesz representation theorem

We consider an inner product space `E` over `𝕜`, which is either `ℝ` or `ℂ`. We define
`toDualMap`, a conjugate-linear isometric embedding of `E` into its dual, which maps an element `x`
of the space to `fun y => ⟪x, y⟫`.

Under the hypothesis of completeness (i.e., for Hilbert spaces), we upgrade this to `toDual`, a
conjugate-linear isometric *equivalence* of `E` onto its dual; that is, we establish the
surjectivity of `toDualMap`.  This is the Fréchet-Riesz representation theorem: every element of the
dual of a Hilbert space `E` has the form `fun u => ⟪x, u⟫` for some `x : E`.

For a bounded sesquilinear form `B : E →L⋆[𝕜] E →L[𝕜] 𝕜`,
we define a map `InnerProductSpace.continuousLinearMapOfBilin B : E →L[𝕜] E`,
given by substituting `E →L[𝕜] 𝕜` with `E` using `toDual`.


## References

* [M. Einsiedler and T. Ward, *Functional Analysis, Spectral Theory, and Applications*]
  [EinsiedlerWard2017]

## Tags

dual, Fréchet-Riesz
-/

@[expose] public section

noncomputable section

open ComplexConjugate Module

namespace InnerProductSpace

open RCLike ContinuousLinearMap

variable (𝕜 E : Type*)

section Seminormed

variable [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

local postfix:90 "†" => starRingEnd _

/-- An element `x` of an inner product space `E` induces an element of the strong dual space
`StrongDual 𝕜 E`, the map `fun y => ⟪x, y⟫`; moreover this operation is a conjugate-linear isometric
embedding of `E` into `StrongDual 𝕜 E`.
If `E` is complete, this operation is surjective, hence a conjugate-linear isometric equivalence;
see `toDual`.
-/
def toDualMap : E →ₗᵢ⋆[𝕜] StrongDual 𝕜 E :=
  { innerSL 𝕜 with norm_map' := innerSL_apply_norm _ }

variable {E}

@[simp]
theorem toContinuousLinearMap_toDualMap :
    (toDualMap 𝕜 E).toContinuousLinearMap = innerSL 𝕜 := rfl

@[simp]
theorem toDualMap_apply_apply {x y : E} : toDualMap 𝕜 E x y = ⟪x, y⟫ := rfl

@[deprecated (since := "2025-11-15")] alias toDualMap_apply := toDualMap_apply_apply

variable {𝕜} in
@[simp]
theorem _root_.innerSL_inj {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {x y : E} :
    innerSL 𝕜 x = innerSL 𝕜 y ↔ x = y :=
  (toDualMap 𝕜 E).injective.eq_iff

section NullSubmodule

open LinearMap

/-- For each `x : E`, the kernel of `⟪x, ⬝⟫` includes the null space. -/
lemma nullSubmodule_le_ker_toDualMap_right (x : E) : nullSubmodule 𝕜 E ≤ (toDualMap 𝕜 E x).ker :=
  fun _ hx ↦ inner_eq_zero_of_right x (mem_nullSubmodule_iff.mp hx)

/-- The kernel of the map `x ↦ ⟪·, x⟫` includes the null space. -/
lemma nullSubmodule_le_ker_toDualMap_left : nullSubmodule 𝕜 E ≤ (toDualMap 𝕜 E).ker :=
  fun _ hx ↦ ContinuousLinearMap.ext <| fun y ↦ inner_eq_zero_of_left y hx

end NullSubmodule

end Seminormed

section Normed
variable [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

local postfix:90 "†" => starRingEnd _

theorem innerSL_norm [Nontrivial E] : ‖(innerSL 𝕜 : E →L⋆[𝕜] E →L[𝕜] 𝕜)‖ = 1 :=
  show ‖(toDualMap 𝕜 E).toContinuousLinearMap‖ = 1 from LinearIsometry.norm_toContinuousLinearMap _

variable {E 𝕜}

theorem ext_inner_left_basis {ι : Type*} {x y : E} (b : Basis ι 𝕜 E)
    (h : ∀ i : ι, ⟪b i, x⟫ = ⟪b i, y⟫) : x = y := by
  apply (toDualMap 𝕜 E).map_eq_iff.mp
  refine (Function.Injective.eq_iff ContinuousLinearMap.coe_injective).mp (b.ext ?_)
  intro i
  simp only [ContinuousLinearMap.coe_coe, toDualMap_apply_apply]
  rw [← inner_conj_symm]
  conv_rhs => rw [← inner_conj_symm]
  exact congr_arg conj (h i)

theorem ext_inner_right_basis {ι : Type*} {x y : E} (b : Basis ι 𝕜 E)
    (h : ∀ i : ι, ⟪x, b i⟫ = ⟪y, b i⟫) : x = y := by
  refine ext_inner_left_basis b fun i => ?_
  rw [← inner_conj_symm]
  conv_rhs => rw [← inner_conj_symm]
  exact congr_arg conj (h i)

variable (𝕜) (E)
variable [CompleteSpace E]

/-- **Fréchet-Riesz representation**: any `ℓ` in the dual of a Hilbert space `E` is of the form
`fun u => ⟪y, u⟫` for some `y : E`, i.e. `toDualMap` is surjective.
-/
@[informal "Fréchet-Riesz representation of the dual of a Hilbert space"]
@[informal "Fréchet-Riesz representation of the dual of a Hilbert space"]
def toDual : E ≃ₗᵢ⋆[𝕜] StrongDual 𝕜 E :=
  LinearIsometryEquiv.ofSurjective (toDualMap 𝕜 E)
    (by
      intro ℓ
      set Y := ℓ.ker
      by_cases htriv : Y = ⊤
      · have hℓ : ℓ = 0 := by
          have h' := LinearMap.ker_eq_top.mp htriv
          rw [← coe_zero] at h'
          apply coe_injective
          exact h'
        exact ⟨0, by simp [hℓ]⟩
      · rw [← Submodule.orthogonal_eq_bot_iff] at htriv
        change Yᗮ ≠ ⊥ at htriv
        rw [Submodule.ne_bot_iff] at htriv
        obtain ⟨z : E, hz : z ∈ Yᗮ, z_ne_0 : z ≠ 0⟩ := htriv
        refine ⟨(starRingEnd (R := 𝕜) (ℓ z) / ⟪z, z⟫) • z, ?_⟩
        apply ContinuousLinearMap.ext
        intro x
        have h₁ : ℓ z • x - ℓ x • z ∈ Y := by
          rw [LinearMap.mem_ker, map_sub, map_smul, map_smul, smul_eq_mul,
            smul_eq_mul, mul_comm]
          exact sub_self (ℓ x * ℓ z)
        have h₂ : ℓ z * ⟪z, x⟫ = ℓ x * ⟪z, z⟫ :=
          haveI h₃ :=
            calc
              0 = ⟪z, ℓ z • x - ℓ x • z⟫ := by
                rw [(Y.mem_orthogonal' z).mp hz]
                exact h₁
              _ = ⟪z, ℓ z • x⟫ - ⟪z, ℓ x • z⟫ := by rw [inner_sub_right]
              _ = ℓ z * ⟪z, x⟫ - ℓ x * ⟪z, z⟫ := by simp [inner_smul_right]
          sub_eq_zero.mp h₃.symm
        calc
          ⟪(ℓ z† / ⟪z, z⟫) • z, x⟫ = ℓ z / ⟪z, z⟫ * ⟪z, x⟫ := by simp [inner_smul_left]
          _ = ℓ z * ⟪z, x⟫ / ⟪z, z⟫ := by rw [← div_mul_eq_mul_div]
          _ = ℓ x * ⟪z, z⟫ / ⟪z, z⟫ := by rw [h₂]
          _ = ℓ x := by have : ⟪z, z⟫ ≠ 0 := inner_self_ne_zero.mpr z_ne_0; field)

variable {𝕜} {E}

@[simp]
theorem toDual_apply_apply {x y : E} : toDual 𝕜 E x y = ⟪x, y⟫ := rfl

@[deprecated (since := "2025-11-15")] alias toDual_apply := toDual_apply_apply

@[simp]
theorem toDual_symm_apply {x : E} {y : StrongDual 𝕜 E} : ⟪(toDual 𝕜 E).symm y, x⟫ = y x := by
  rw [← toDual_apply_apply]
  simp only [LinearIsometryEquiv.apply_symm_apply]

@[simp]
lemma toLinearIsometry_toDual :
    (toDual 𝕜 E).toLinearIsometry = toDualMap 𝕜 E := rfl

lemma toDual_apply_eq_toDualMap_apply (x : E) :
    toDual 𝕜 E x = toDualMap 𝕜 E x := rfl

/-- Maps a bounded sesquilinear form to its continuous linear map,
given by interpreting the form as a map `B : E →L⋆[𝕜] StrongDual 𝕜 E`
and dualizing the result using `toDual`.
-/
def continuousLinearMapOfBilin (B : E →L⋆[𝕜] E →L[𝕜] 𝕜) : E →L[𝕜] E :=
  (toDual 𝕜 E).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp B

local postfix:1024 "♯" => continuousLinearMapOfBilin

variable (B : E →L⋆[𝕜] E →L[𝕜] 𝕜)

@[simp]
theorem continuousLinearMapOfBilin_zero : (0 : E →L⋆[𝕜] E →L[𝕜] 𝕜)♯ = 0 := by
  simp [continuousLinearMapOfBilin]

@[simp]
theorem continuousLinearMapOfBilin_apply (v w : E) : ⟪B♯ v, w⟫ = B v w := by
  rw [continuousLinearMapOfBilin, coe_comp', ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, Function.comp_apply, toDual_symm_apply]

theorem unique_continuousLinearMapOfBilin {v f : E} (is_lax_milgram : ∀ w, ⟪f, w⟫ = B v w) :
    f = B♯ v := by
  refine ext_inner_right 𝕜 ?_
  intro w
  rw [continuousLinearMapOfBilin_apply]
  exact is_lax_milgram w

end Normed

instance [NormedAddCommGroup E] [CompleteSpace E] [InnerProductSpace ℝ E] :
    (innerₗ E).IsContPerfPair where
  continuous_uncurry := continuous_inner
  bijective_left := (toDual ℝ E).bijective
  bijective_right := by
    convert (toDual ℝ E).bijective
    ext y
    simp

/-- A nonzero rank-one operator has rank one. -/
lemma rank_rankOne {𝕜 E F : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] {x : E} {y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    (rankOne 𝕜 x y).rank = 1 := by
  rw [LinearMap.rank, rankOne_def, range_smulRight_apply, Module.rank_eq_one_iff_finrank_eq_one]
  · exact finrank_span_singleton hx
  · exact map_eq_zero_iff _ (toDualMap 𝕜 F).injective |>.not.mpr hy

end InnerProductSpace

lemma OrthonormalBasis.norm_dual {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (b : OrthonormalBasis ι ℝ E) (L : StrongDual ℝ E) :
    ‖L‖ ^ 2 = ∑ i, L (b i) ^ 2 := by
  have := b.toBasis.finiteDimensional_of_finite
  simp_rw [← (InnerProductSpace.toDual ℝ E).symm.norm_map, ← b.sum_sq_inner_left,
    InnerProductSpace.toDual_symm_apply]
