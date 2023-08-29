/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Orientation
import Mathlib.Data.Complex.Orientation
import Mathlib.Tactic.LinearCombination

#align_import analysis.inner_product_space.two_dim from "leanprover-community/mathlib"@"cd8fafa2fac98e1a67097e8a91ad9901cfde48af"

/-!
# Oriented two-dimensional real inner product spaces

This file defines constructions specific to the geometry of an oriented two-dimensional real inner
product space `E`.

## Main declarations

* `Orientation.areaForm`: an antisymmetric bilinear form `E →ₗ[ℝ] E →ₗ[ℝ] ℝ` (usual notation `ω`).
  Morally, when `ω` is evaluated on two vectors, it gives the oriented area of the parallelogram
  they span. (But mathlib does not yet have a construction of oriented area, and in fact the
  construction of oriented area should pass through `ω`.)

* `Orientation.rightAngleRotation`: an isometric automorphism `E ≃ₗᵢ[ℝ] E` (usual notation `J`).
  This automorphism squares to -1. In a later file, rotations (`Orientation.rotation`) are defined,
  in such a way that this automorphism is equal to rotation by 90 degrees.

* `Orientation.basisRightAngleRotation`: for a nonzero vector `x` in `E`, the basis `![x, J x]`
  for `E`.

* `Orientation.kahler`: a complex-valued real-bilinear map `E →ₗ[ℝ] E →ₗ[ℝ] ℂ`. Its real part is the
  inner product and its imaginary part is `Orientation.areaForm`. For vectors `x` and `y` in `E`,
  the complex number `o.kahler x y` has modulus `‖x‖ * ‖y‖`. In a later file, oriented angles
  (`Orientation.oangle`) are defined, in such a way that the argument of `o.kahler x y` is the
  oriented angle from `x` to `y`.

## Main results

* `Orientation.rightAngleRotation_rightAngleRotation`: the identity `J (J x) = - x`

* `Orientation.nonneg_inner_and_areaForm_eq_zero_iff_sameRay`: `x`, `y` are in the same ray, if
  and only if `0 ≤ ⟪x, y⟫` and `ω x y = 0`

* `Orientation.kahler_mul`: the identity `o.kahler x a * o.kahler a y = ‖a‖ ^ 2 * o.kahler x y`

* `Complex.areaForm`, `Complex.rightAngleRotation`, `Complex.kahler`: the concrete
  interpretations of `areaForm`, `rightAngleRotation`, `kahler` for the oriented real inner
  product space `ℂ`

* `Orientation.areaForm_map_complex`, `Orientation.rightAngleRotation_map_complex`,
  `Orientation.kahler_map_complex`: given an orientation-preserving isometry from `E` to `ℂ`,
  expressions for `areaForm`, `rightAngleRotation`, `kahler` as the pullback of their concrete
  interpretations on `ℂ`

## Implementation notes

Notation `ω` for `Orientation.areaForm` and `J` for `Orientation.rightAngleRotation` should be
defined locally in each file which uses them, since otherwise one would need a more cumbersome
notation which mentions the orientation explicitly (something like `ω[o]`). Write

```
local notation "ω" => o.areaForm
local notation "J" => o.rightAngleRotation
```

-/


noncomputable section

open scoped RealInnerProductSpace ComplexConjugate

open FiniteDimensional

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

lemma FiniteDimensional.finiteDimensional_of_fact_finrank_eq_two {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] [Fact (finrank K V = 2)] : FiniteDimensional K V :=
  fact_finiteDimensional_of_finrank_eq_succ 1

attribute [local instance] FiniteDimensional.finiteDimensional_of_fact_finrank_eq_two

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 2)]
  (o : Orientation ℝ E (Fin 2))

namespace Orientation

/-- An antisymmetric bilinear form on an oriented real inner product space of dimension 2 (usual
notation `ω`). When evaluated on two vectors, it gives the oriented area of the parallelogram they
span. -/
irreducible_def areaForm : E →ₗ[ℝ] E →ₗ[ℝ] ℝ := by
  let z : AlternatingMap ℝ E ℝ (Fin 0) ≃ₗ[ℝ] ℝ :=
    AlternatingMap.constLinearEquivOfIsEmpty.symm
  let y : AlternatingMap ℝ E ℝ (Fin 1) →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
    LinearMap.llcomp ℝ E (AlternatingMap ℝ E ℝ (Fin 0)) ℝ z ∘ₗ AlternatingMap.curryLeftLinearMap
  exact y ∘ₗ AlternatingMap.curryLeftLinearMap (R' := ℝ) o.volumeForm
  -- 🎉 no goals
#align orientation.area_form Orientation.areaForm

local notation "ω" => o.areaForm

theorem areaForm_to_volumeForm (x y : E) : ω x y = o.volumeForm ![x, y] := by simp [areaForm]
                                                                              -- 🎉 no goals
#align orientation.area_form_to_volume_form Orientation.areaForm_to_volumeForm

@[simp]
theorem areaForm_apply_self (x : E) : ω x x = 0 := by
  rw [areaForm_to_volumeForm]
  -- ⊢ ↑(volumeForm o) ![x, x] = 0
  refine' o.volumeForm.map_eq_zero_of_eq ![x, x] _ (_ : (0 : Fin 2) ≠ 1)
  -- ⊢ Matrix.vecCons x ![x] 0 = Matrix.vecCons x ![x] 1
  · simp
    -- 🎉 no goals
  · norm_num
    -- 🎉 no goals
#align orientation.area_form_apply_self Orientation.areaForm_apply_self

theorem areaForm_swap (x y : E) : ω x y = -ω y x := by
  simp only [areaForm_to_volumeForm]
  -- ⊢ ↑(volumeForm o) ![x, y] = -↑(volumeForm o) ![y, x]
  convert o.volumeForm.map_swap ![y, x] (_ : (0 : Fin 2) ≠ 1)
  -- ⊢ ![x, y] = ![y, x] ∘ ↑(Equiv.swap 0 1)
  · ext i
    -- ⊢ Matrix.vecCons x ![y] i = (![y, x] ∘ ↑(Equiv.swap 0 1)) i
    fin_cases i <;> rfl
    -- ⊢ Matrix.vecCons x ![y] { val := 0, isLt := (_ : 0 < Nat.succ 1) } = (![y, x]  …
                    -- 🎉 no goals
                    -- 🎉 no goals
  · norm_num
    -- 🎉 no goals
#align orientation.area_form_swap Orientation.areaForm_swap

@[simp]
theorem areaForm_neg_orientation : (-o).areaForm = -o.areaForm := by
  ext x y
  -- ⊢ ↑(↑(areaForm (-o)) x) y = ↑(↑(-areaForm o) x) y
  simp [areaForm_to_volumeForm]
  -- 🎉 no goals
#align orientation.area_form_neg_orientation Orientation.areaForm_neg_orientation

/-- Continuous linear map version of `Orientation.areaForm`, useful for calculus. -/
def areaForm' : E →L[ℝ] E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    (↑(LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] E →L[ℝ] ℝ) ∘ₗ o.areaForm)
#align orientation.area_form' Orientation.areaForm'

@[simp]
theorem areaForm'_apply (x : E) :
    o.areaForm' x = LinearMap.toContinuousLinearMap (o.areaForm x) :=
  rfl
#align orientation.area_form'_apply Orientation.areaForm'_apply

theorem abs_areaForm_le (x y : E) : |ω x y| ≤ ‖x‖ * ‖y‖ := by
  simpa [areaForm_to_volumeForm, Fin.prod_univ_succ] using o.abs_volumeForm_apply_le ![x, y]
  -- 🎉 no goals
#align orientation.abs_area_form_le Orientation.abs_areaForm_le

theorem areaForm_le (x y : E) : ω x y ≤ ‖x‖ * ‖y‖ := by
  simpa [areaForm_to_volumeForm, Fin.prod_univ_succ] using o.volumeForm_apply_le ![x, y]
  -- 🎉 no goals
#align orientation.area_form_le Orientation.areaForm_le

theorem abs_areaForm_of_orthogonal {x y : E} (h : ⟪x, y⟫ = 0) : |ω x y| = ‖x‖ * ‖y‖ := by
  rw [o.areaForm_to_volumeForm, o.abs_volumeForm_apply_of_pairwise_orthogonal]
  -- ⊢ (Finset.prod Finset.univ fun i => ‖Matrix.vecCons x ![y] i‖) = ‖x‖ * ‖y‖
  · simp [Fin.prod_univ_succ]
    -- 🎉 no goals
  intro i j hij
  -- ⊢ inner (Matrix.vecCons x ![y] i) (Matrix.vecCons x ![y] j) = 0
  fin_cases i <;> fin_cases j
  -- ⊢ inner (Matrix.vecCons x ![y] { val := 0, isLt := (_ : 0 < 2) }) (Matrix.vecC …
                  -- ⊢ inner (Matrix.vecCons x ![y] { val := 0, isLt := (_ : 0 < 2) }) (Matrix.vecC …
                  -- ⊢ inner (Matrix.vecCons x ![y] { val := 1, isLt := (_ : (fun a => a < 2) 1) }) …
  · simp_all
    -- 🎉 no goals
  · simpa using h
    -- 🎉 no goals
  · simpa [real_inner_comm] using h
    -- 🎉 no goals
  · simp_all
    -- 🎉 no goals
#align orientation.abs_area_form_of_orthogonal Orientation.abs_areaForm_of_orthogonal

theorem areaForm_map {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [hF : Fact (finrank ℝ F = 2)] (φ : E ≃ₗᵢ[ℝ] F) (x y : F) :
    (Orientation.map (Fin 2) φ.toLinearEquiv o).areaForm x y =
    o.areaForm (φ.symm x) (φ.symm y) := by
  have : φ.symm ∘ ![x, y] = ![φ.symm x, φ.symm y] := by
    ext i
    fin_cases i <;> rfl
  simp [areaForm_to_volumeForm, volumeForm_map, this]
  -- 🎉 no goals
#align orientation.area_form_map Orientation.areaForm_map

/-- The area form is invariant under pullback by a positively-oriented isometric automorphism. -/
theorem areaForm_comp_linearIsometryEquiv (φ : E ≃ₗᵢ[ℝ] E)
    (hφ : 0 < LinearMap.det (φ.toLinearEquiv : E →ₗ[ℝ] E)) (x y : E) :
    o.areaForm (φ x) (φ y) = o.areaForm x y := by
  convert o.areaForm_map φ (φ x) (φ y)
  · symm
    -- ⊢ ↑(map (Fin 2) φ.toLinearEquiv) o = o
    rwa [← o.map_eq_iff_det_pos φ.toLinearEquiv] at hφ
    -- ⊢ Fintype.card (Fin 2) = finrank ℝ E
    rw [@Fact.out (finrank ℝ E = 2), Fintype.card_fin]
    -- 🎉 no goals
  · simp
    -- 🎉 no goals
  · simp
    -- 🎉 no goals
#align orientation.area_form_comp_linear_isometry_equiv Orientation.areaForm_comp_linearIsometryEquiv

/-- Auxiliary construction for `Orientation.rightAngleRotation`, rotation by 90 degrees in an
oriented real inner product space of dimension 2. -/
irreducible_def rightAngleRotationAux₁ : E →ₗ[ℝ] E :=
  let to_dual : E ≃ₗ[ℝ] E →ₗ[ℝ] ℝ :=
    (InnerProductSpace.toDual ℝ E).toLinearEquiv ≪≫ₗ LinearMap.toContinuousLinearMap.symm
  ↑to_dual.symm ∘ₗ ω
#align orientation.right_angle_rotation_aux₁ Orientation.rightAngleRotationAux₁

@[simp]
theorem inner_rightAngleRotationAux₁_left (x y : E) : ⟪o.rightAngleRotationAux₁ x, y⟫ = ω x y := by
  -- Porting note: split `simp only` for greater proof control
  simp only [rightAngleRotationAux₁, LinearEquiv.trans_symm, LinearIsometryEquiv.toLinearEquiv_symm,
    LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.trans_apply,
    LinearIsometryEquiv.coe_toLinearEquiv]
  rw [InnerProductSpace.toDual_symm_apply]
  -- ⊢ ↑(↑(LinearEquiv.symm (LinearEquiv.symm LinearMap.toContinuousLinearMap)) (↑( …
  norm_cast
  -- 🎉 no goals
#align orientation.inner_right_angle_rotation_aux₁_left Orientation.inner_rightAngleRotationAux₁_left

@[simp]
theorem inner_rightAngleRotationAux₁_right (x y : E) :
    ⟪x, o.rightAngleRotationAux₁ y⟫ = -ω x y := by
  rw [real_inner_comm]
  -- ⊢ inner (↑(rightAngleRotationAux₁ o) y) x = -↑(↑(areaForm o) x) y
  simp [o.areaForm_swap y x]
  -- 🎉 no goals
#align orientation.inner_right_angle_rotation_aux₁_right Orientation.inner_rightAngleRotationAux₁_right

/-- Auxiliary construction for `Orientation.rightAngleRotation`, rotation by 90 degrees in an
oriented real inner product space of dimension 2. -/
def rightAngleRotationAux₂ : E →ₗᵢ[ℝ] E :=
  { o.rightAngleRotationAux₁ with
    norm_map' := fun x => by
      dsimp
      -- ⊢ ‖↑(rightAngleRotationAux₁ o) x‖ = ‖x‖
      refine' le_antisymm _ _
      -- ⊢ ‖↑(rightAngleRotationAux₁ o) x‖ ≤ ‖x‖
      · cases' eq_or_lt_of_le (norm_nonneg (o.rightAngleRotationAux₁ x)) with h h
        -- ⊢ ‖↑(rightAngleRotationAux₁ o) x‖ ≤ ‖x‖
        · rw [← h]
          -- ⊢ 0 ≤ ‖x‖
          positivity
          -- 🎉 no goals
        refine' le_of_mul_le_mul_right _ h
        -- ⊢ ‖↑(rightAngleRotationAux₁ o) x‖ * ‖↑(rightAngleRotationAux₁ o) x‖ ≤ ‖x‖ * ‖↑ …
        rw [← real_inner_self_eq_norm_mul_norm, o.inner_rightAngleRotationAux₁_left]
        -- ⊢ ↑(↑(areaForm o) x) (↑(rightAngleRotationAux₁ o) x) ≤ ‖x‖ * ‖↑(rightAngleRota …
        exact o.areaForm_le x (o.rightAngleRotationAux₁ x)
        -- 🎉 no goals
      · let K : Submodule ℝ E := ℝ ∙ x
        -- ⊢ ‖x‖ ≤ ‖↑(rightAngleRotationAux₁ o) x‖
        have : Nontrivial Kᗮ := by
          apply @FiniteDimensional.nontrivial_of_finrank_pos ℝ
          have : finrank ℝ K ≤ Finset.card {x} := by
            rw [← Set.toFinset_singleton]
            exact finrank_span_le_card ({x} : Set E)
          have : Finset.card {x} = 1 := Finset.card_singleton x
          have : finrank ℝ K + finrank ℝ Kᗮ = finrank ℝ E := K.finrank_add_finrank_orthogonal
          have : finrank ℝ E = 2 := Fact.out
          linarith
        obtain ⟨w, hw₀⟩ : ∃ w : Kᗮ, w ≠ 0 := exists_ne 0
        -- ⊢ ‖x‖ ≤ ‖↑(rightAngleRotationAux₁ o) x‖
        have hw' : ⟪x, (w : E)⟫ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp w.2
        -- ⊢ ‖x‖ ≤ ‖↑(rightAngleRotationAux₁ o) x‖
        have hw : (w : E) ≠ 0 := fun h => hw₀ (Submodule.coe_eq_zero.mp h)
        -- ⊢ ‖x‖ ≤ ‖↑(rightAngleRotationAux₁ o) x‖
        refine' le_of_mul_le_mul_right _ (by rwa [norm_pos_iff] : 0 < ‖(w : E)‖)
        -- ⊢ ‖x‖ * ‖↑w‖ ≤ ‖↑(rightAngleRotationAux₁ o) x‖ * ‖↑w‖
        rw [← o.abs_areaForm_of_orthogonal hw']
        -- ⊢ |↑(↑(areaForm o) x) ↑w| ≤ ‖↑(rightAngleRotationAux₁ o) x‖ * ‖↑w‖
        rw [← o.inner_rightAngleRotationAux₁_left x w]
        -- ⊢ |inner (↑(rightAngleRotationAux₁ o) x) ↑w| ≤ ‖↑(rightAngleRotationAux₁ o) x‖ …
        exact abs_real_inner_le_norm (o.rightAngleRotationAux₁ x) w }
        -- 🎉 no goals
#align orientation.right_angle_rotation_aux₂ Orientation.rightAngleRotationAux₂

@[simp]
theorem rightAngleRotationAux₁_rightAngleRotationAux₁ (x : E) :
    o.rightAngleRotationAux₁ (o.rightAngleRotationAux₁ x) = -x := by
  apply ext_inner_left ℝ
  -- ⊢ ∀ (v : (fun x => E) (↑(rightAngleRotationAux₁ o) x)), inner v (↑(rightAngleR …
  intro y
  -- ⊢ inner y (↑(rightAngleRotationAux₁ o) (↑(rightAngleRotationAux₁ o) x)) = inne …
  have : ⟪o.rightAngleRotationAux₁ y, o.rightAngleRotationAux₁ x⟫ = ⟪y, x⟫ :=
    LinearIsometry.inner_map_map o.rightAngleRotationAux₂ y x
  rw [o.inner_rightAngleRotationAux₁_right, ← o.inner_rightAngleRotationAux₁_left, this,
    inner_neg_right]
#align orientation.right_angle_rotation_aux₁_right_angle_rotation_aux₁ Orientation.rightAngleRotationAux₁_rightAngleRotationAux₁

/-- An isometric automorphism of an oriented real inner product space of dimension 2 (usual notation
`J`). This automorphism squares to -1. We will define rotations in such a way that this
automorphism is equal to rotation by 90 degrees. -/
irreducible_def rightAngleRotation : E ≃ₗᵢ[ℝ] E :=
  LinearIsometryEquiv.ofLinearIsometry o.rightAngleRotationAux₂ (-o.rightAngleRotationAux₁)
    (by ext; simp [rightAngleRotationAux₂]) (by ext; simp [rightAngleRotationAux₂])
        -- ⊢ ↑(LinearMap.comp (rightAngleRotationAux₂ o).toLinearMap (-rightAngleRotation …
             -- 🎉 no goals
                                                -- ⊢ ↑(LinearMap.comp (-rightAngleRotationAux₁ o) (rightAngleRotationAux₂ o).toLi …
                                                     -- 🎉 no goals
#align orientation.right_angle_rotation Orientation.rightAngleRotation

local notation "J" => o.rightAngleRotation

@[simp]
theorem inner_rightAngleRotation_left (x y : E) : ⟪J x, y⟫ = ω x y := by
  rw [rightAngleRotation]
  -- ⊢ inner (↑(LinearIsometryEquiv.ofLinearIsometry (rightAngleRotationAux₂ o) (-r …
  exact o.inner_rightAngleRotationAux₁_left x y
  -- 🎉 no goals
#align orientation.inner_right_angle_rotation_left Orientation.inner_rightAngleRotation_left

@[simp]
theorem inner_rightAngleRotation_right (x y : E) : ⟪x, J y⟫ = -ω x y := by
  rw [rightAngleRotation]
  -- ⊢ inner x (↑(LinearIsometryEquiv.ofLinearIsometry (rightAngleRotationAux₂ o) ( …
  exact o.inner_rightAngleRotationAux₁_right x y
  -- 🎉 no goals
#align orientation.inner_right_angle_rotation_right Orientation.inner_rightAngleRotation_right

@[simp]
theorem rightAngleRotation_rightAngleRotation (x : E) : J (J x) = -x := by
  rw [rightAngleRotation]
  -- ⊢ ↑(LinearIsometryEquiv.ofLinearIsometry (rightAngleRotationAux₂ o) (-rightAng …
  exact o.rightAngleRotationAux₁_rightAngleRotationAux₁ x
  -- 🎉 no goals
#align orientation.right_angle_rotation_right_angle_rotation Orientation.rightAngleRotation_rightAngleRotation

@[simp]
theorem rightAngleRotation_symm :
    LinearIsometryEquiv.symm J = LinearIsometryEquiv.trans J (LinearIsometryEquiv.neg ℝ) := by
  rw [rightAngleRotation]
  -- ⊢ LinearIsometryEquiv.symm (LinearIsometryEquiv.ofLinearIsometry (rightAngleRo …
  exact LinearIsometryEquiv.toLinearIsometry_injective rfl
  -- 🎉 no goals
#align orientation.right_angle_rotation_symm Orientation.rightAngleRotation_symm

-- @[simp] -- Porting note: simp already proves this
theorem inner_rightAngleRotation_self (x : E) : ⟪J x, x⟫ = 0 := by simp
                                                                   -- 🎉 no goals
#align orientation.inner_right_angle_rotation_self Orientation.inner_rightAngleRotation_self

theorem inner_rightAngleRotation_swap (x y : E) : ⟪x, J y⟫ = -⟪J x, y⟫ := by simp
                                                                             -- 🎉 no goals
#align orientation.inner_right_angle_rotation_swap Orientation.inner_rightAngleRotation_swap

theorem inner_rightAngleRotation_swap' (x y : E) : ⟪J x, y⟫ = -⟪x, J y⟫ := by
  simp [o.inner_rightAngleRotation_swap x y]
  -- 🎉 no goals
#align orientation.inner_right_angle_rotation_swap' Orientation.inner_rightAngleRotation_swap'

theorem inner_comp_rightAngleRotation (x y : E) : ⟪J x, J y⟫ = ⟪x, y⟫ :=
  LinearIsometryEquiv.inner_map_map J x y
#align orientation.inner_comp_right_angle_rotation Orientation.inner_comp_rightAngleRotation

@[simp]
theorem areaForm_rightAngleRotation_left (x y : E) : ω (J x) y = -⟪x, y⟫ := by
  rw [← o.inner_comp_rightAngleRotation, o.inner_rightAngleRotation_right, neg_neg]
  -- 🎉 no goals
#align orientation.area_form_right_angle_rotation_left Orientation.areaForm_rightAngleRotation_left

@[simp]
theorem areaForm_rightAngleRotation_right (x y : E) : ω x (J y) = ⟪x, y⟫ := by
  rw [← o.inner_rightAngleRotation_left, o.inner_comp_rightAngleRotation]
  -- 🎉 no goals
#align orientation.area_form_right_angle_rotation_right Orientation.areaForm_rightAngleRotation_right

-- @[simp] -- Porting note: simp already proves this
theorem areaForm_comp_rightAngleRotation (x y : E) : ω (J x) (J y) = ω x y := by simp
                                                                                 -- 🎉 no goals
#align orientation.area_form_comp_right_angle_rotation Orientation.areaForm_comp_rightAngleRotation

@[simp]
theorem rightAngleRotation_trans_rightAngleRotation :
    LinearIsometryEquiv.trans J J = LinearIsometryEquiv.neg ℝ := by ext; simp
                                                                    -- ⊢ ↑(LinearIsometryEquiv.trans (rightAngleRotation o) (rightAngleRotation o)) x …
                                                                         -- 🎉 no goals
#align orientation.right_angle_rotation_trans_right_angle_rotation Orientation.rightAngleRotation_trans_rightAngleRotation

theorem rightAngleRotation_neg_orientation (x : E) :
    (-o).rightAngleRotation x = -o.rightAngleRotation x := by
  apply ext_inner_right ℝ
  -- ⊢ ∀ (v : E), inner (↑(rightAngleRotation (-o)) x) v = inner (-↑(rightAngleRota …
  intro y
  -- ⊢ inner (↑(rightAngleRotation (-o)) x) y = inner (-↑(rightAngleRotation o) x) y
  rw [inner_rightAngleRotation_left]
  -- ⊢ ↑(↑(areaForm (-o)) x) y = inner (-↑(rightAngleRotation o) x) y
  simp
  -- 🎉 no goals
#align orientation.right_angle_rotation_neg_orientation Orientation.rightAngleRotation_neg_orientation

@[simp]
theorem rightAngleRotation_trans_neg_orientation :
    (-o).rightAngleRotation = o.rightAngleRotation.trans (LinearIsometryEquiv.neg ℝ) :=
  LinearIsometryEquiv.ext <| o.rightAngleRotation_neg_orientation
#align orientation.right_angle_rotation_trans_neg_orientation Orientation.rightAngleRotation_trans_neg_orientation

theorem rightAngleRotation_map {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [hF : Fact (finrank ℝ F = 2)] (φ : E ≃ₗᵢ[ℝ] F) (x : F) :
    (Orientation.map (Fin 2) φ.toLinearEquiv o).rightAngleRotation x =
      φ (o.rightAngleRotation (φ.symm x)) := by
  apply ext_inner_right ℝ
  -- ⊢ ∀ (v : F), inner (↑(rightAngleRotation (↑(map (Fin 2) φ.toLinearEquiv) o)) x …
  intro y
  -- ⊢ inner (↑(rightAngleRotation (↑(map (Fin 2) φ.toLinearEquiv) o)) x) y = inner …
  rw [inner_rightAngleRotation_left]
  -- ⊢ ↑(↑(areaForm (↑(map (Fin 2) φ.toLinearEquiv) o)) x) y = inner (↑φ (↑(rightAn …
  trans ⟪J (φ.symm x), φ.symm y⟫
  -- ⊢ ↑(↑(areaForm (↑(map (Fin 2) φ.toLinearEquiv) o)) x) y = inner (↑(rightAngleR …
  · simp [o.areaForm_map]
    -- 🎉 no goals
  trans ⟪φ (J (φ.symm x)), φ (φ.symm y)⟫
  -- ⊢ inner (↑(rightAngleRotation o) (↑(LinearIsometryEquiv.symm φ) x)) (↑(LinearI …
  · rw [φ.inner_map_map]
    -- 🎉 no goals
  · simp
    -- 🎉 no goals
#align orientation.right_angle_rotation_map Orientation.rightAngleRotation_map

/-- `J` commutes with any positively-oriented isometric automorphism. -/
theorem linearIsometryEquiv_comp_rightAngleRotation (φ : E ≃ₗᵢ[ℝ] E)
    (hφ : 0 < LinearMap.det (φ.toLinearEquiv : E →ₗ[ℝ] E)) (x : E) : φ (J x) = J (φ x) := by
  convert(o.rightAngleRotation_map φ (φ x)).symm
  -- ⊢ x = ↑(LinearIsometryEquiv.symm φ) (↑φ x)
  · simp
    -- 🎉 no goals
  · symm
    -- ⊢ ↑(map (Fin 2) φ.toLinearEquiv) o = o
    rwa [← o.map_eq_iff_det_pos φ.toLinearEquiv] at hφ
    -- ⊢ Fintype.card (Fin 2) = finrank ℝ E
    rw [@Fact.out (finrank ℝ E = 2), Fintype.card_fin]
    -- 🎉 no goals
#align orientation.linear_isometry_equiv_comp_right_angle_rotation Orientation.linearIsometryEquiv_comp_rightAngleRotation

theorem rightAngleRotation_map' {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [Fact (finrank ℝ F = 2)] (φ : E ≃ₗᵢ[ℝ] F) :
    (Orientation.map (Fin 2) φ.toLinearEquiv o).rightAngleRotation =
      (φ.symm.trans o.rightAngleRotation).trans φ :=
  LinearIsometryEquiv.ext <| o.rightAngleRotation_map φ
#align orientation.right_angle_rotation_map' Orientation.rightAngleRotation_map'

/-- `J` commutes with any positively-oriented isometric automorphism. -/
theorem linearIsometryEquiv_comp_rightAngleRotation' (φ : E ≃ₗᵢ[ℝ] E)
    (hφ : 0 < LinearMap.det (φ.toLinearEquiv : E →ₗ[ℝ] E)) :
    LinearIsometryEquiv.trans J φ = φ.trans J :=
  LinearIsometryEquiv.ext <| o.linearIsometryEquiv_comp_rightAngleRotation φ hφ
#align orientation.linear_isometry_equiv_comp_right_angle_rotation' Orientation.linearIsometryEquiv_comp_rightAngleRotation'

/-- For a nonzero vector `x` in an oriented two-dimensional real inner product space `E`,
`![x, J x]` forms an (orthogonal) basis for `E`. -/
def basisRightAngleRotation (x : E) (hx : x ≠ 0) : Basis (Fin 2) ℝ E :=
  @basisOfLinearIndependentOfCardEqFinrank ℝ _ _ _ _ _ _ _ ![x, J x]
    (linearIndependent_of_ne_zero_of_inner_eq_zero (fun i => by fin_cases i <;> simp [hx])
                                                                -- ⊢ Matrix.vecCons x ![↑(rightAngleRotation o) x] { val := 0, isLt := (_ : 0 < 2 …
                                                                                -- 🎉 no goals
                                                                                -- 🎉 no goals
      (by
        intro i j hij
        -- ⊢ inner (Matrix.vecCons x ![↑(rightAngleRotation o) x] i) (Matrix.vecCons x ![ …
        fin_cases i <;> fin_cases j <;> simp_all))
        -- ⊢ inner (Matrix.vecCons x ![↑(rightAngleRotation o) x] { val := 0, isLt := (_  …
                        -- ⊢ inner (Matrix.vecCons x ![↑(rightAngleRotation o) x] { val := 0, isLt := (_  …
                        -- ⊢ inner (Matrix.vecCons x ![↑(rightAngleRotation o) x] { val := 1, isLt := (_  …
                                        -- 🎉 no goals
                                        -- 🎉 no goals
                                        -- 🎉 no goals
                                        -- 🎉 no goals
    (@Fact.out (finrank ℝ E = 2)).symm
#align orientation.basis_right_angle_rotation Orientation.basisRightAngleRotation

@[simp]
theorem coe_basisRightAngleRotation (x : E) (hx : x ≠ 0) :
    ⇑(o.basisRightAngleRotation x hx) = ![x, J x] :=
  coe_basisOfLinearIndependentOfCardEqFinrank _ _
#align orientation.coe_basis_right_angle_rotation Orientation.coe_basisRightAngleRotation

/-- For vectors `a x y : E`, the identity `⟪a, x⟫ * ⟪a, y⟫ + ω a x * ω a y = ‖a‖ ^ 2 * ⟪x, y⟫`. (See
`Orientation.inner_mul_inner_add_areaForm_mul_areaForm` for the "applied" form.)-/
theorem inner_mul_inner_add_areaForm_mul_areaForm' (a x : E) :
    ⟪a, x⟫ • innerₛₗ ℝ a + ω a x • ω a = ‖a‖ ^ 2 • innerₛₗ ℝ x := by
  by_cases ha : a = 0
  -- ⊢ inner a x • ↑(innerₛₗ ℝ) a + ↑(↑(areaForm o) a) x • ↑(areaForm o) a = ‖a‖ ^  …
  · simp [ha]
    -- 🎉 no goals
  apply (o.basisRightAngleRotation a ha).ext
  -- ⊢ ∀ (i : Fin 2), ↑(inner a x • ↑(innerₛₗ ℝ) a + ↑(↑(areaForm o) a) x • ↑(areaF …
  intro i
  -- ⊢ ↑(inner a x • ↑(innerₛₗ ℝ) a + ↑(↑(areaForm o) a) x • ↑(areaForm o) a) (↑(ba …
  fin_cases i
  -- ⊢ ↑(inner a x • ↑(innerₛₗ ℝ) a + ↑(↑(areaForm o) a) x • ↑(areaForm o) a) (↑(ba …
  · simp only [Fin.mk_zero, coe_basisRightAngleRotation, Matrix.cons_val_zero, LinearMap.add_apply,
      LinearMap.smul_apply, innerₛₗ_apply, real_inner_self_eq_norm_sq, smul_eq_mul,
      areaForm_apply_self, mul_zero, add_zero, Real.rpow_two, real_inner_comm]
    ring
    -- 🎉 no goals
  · simp only [Fin.mk_one, coe_basisRightAngleRotation, Matrix.cons_val_one, Matrix.head_cons,
      LinearMap.add_apply, LinearMap.smul_apply, innerₛₗ_apply, inner_rightAngleRotation_right,
      areaForm_apply_self, neg_zero, smul_eq_mul, mul_zero, areaForm_rightAngleRotation_right,
      real_inner_self_eq_norm_sq, zero_add, Real.rpow_two, mul_neg]
    rw [o.areaForm_swap]
    -- ⊢ -↑(↑(areaForm o) x) a * ‖a‖ ^ 2 = -(‖a‖ ^ 2 * ↑(↑(areaForm o) x) a)
    ring
    -- 🎉 no goals
#align orientation.inner_mul_inner_add_area_form_mul_area_form' Orientation.inner_mul_inner_add_areaForm_mul_areaForm'

/-- For vectors `a x y : E`, the identity `⟪a, x⟫ * ⟪a, y⟫ + ω a x * ω a y = ‖a‖ ^ 2 * ⟪x, y⟫`. -/
theorem inner_mul_inner_add_areaForm_mul_areaForm (a x y : E) :
    ⟪a, x⟫ * ⟪a, y⟫ + ω a x * ω a y = ‖a‖ ^ 2 * ⟪x, y⟫ :=
  congr_arg (fun f : E →ₗ[ℝ] ℝ => f y) (o.inner_mul_inner_add_areaForm_mul_areaForm' a x)
#align orientation.inner_mul_inner_add_area_form_mul_area_form Orientation.inner_mul_inner_add_areaForm_mul_areaForm

theorem inner_sq_add_areaForm_sq (a b : E) : ⟪a, b⟫ ^ 2 + ω a b ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
  simpa [sq, real_inner_self_eq_norm_sq] using o.inner_mul_inner_add_areaForm_mul_areaForm a b b
  -- 🎉 no goals
#align orientation.inner_sq_add_area_form_sq Orientation.inner_sq_add_areaForm_sq

/-- For vectors `a x y : E`, the identity `⟪a, x⟫ * ω a y - ω a x * ⟪a, y⟫ = ‖a‖ ^ 2 * ω x y`. (See
`Orientation.inner_mul_areaForm_sub` for the "applied" form.) -/
theorem inner_mul_areaForm_sub' (a x : E) : ⟪a, x⟫ • ω a - ω a x • innerₛₗ ℝ a = ‖a‖ ^ 2 • ω x := by
  by_cases ha : a = 0
  -- ⊢ inner a x • ↑(areaForm o) a - ↑(↑(areaForm o) a) x • ↑(innerₛₗ ℝ) a = ‖a‖ ^  …
  · simp [ha]
    -- 🎉 no goals
  apply (o.basisRightAngleRotation a ha).ext
  -- ⊢ ∀ (i : Fin 2), ↑(inner a x • ↑(areaForm o) a - ↑(↑(areaForm o) a) x • ↑(inne …
  intro i
  -- ⊢ ↑(inner a x • ↑(areaForm o) a - ↑(↑(areaForm o) a) x • ↑(innerₛₗ ℝ) a) (↑(ba …
  fin_cases i
  -- ⊢ ↑(inner a x • ↑(areaForm o) a - ↑(↑(areaForm o) a) x • ↑(innerₛₗ ℝ) a) (↑(ba …
  · simp only [o.areaForm_swap a x, neg_smul, sub_neg_eq_add, Fin.mk_zero,
      coe_basisRightAngleRotation, Matrix.cons_val_zero, LinearMap.add_apply, LinearMap.smul_apply,
      areaForm_apply_self, smul_eq_mul, mul_zero, innerₛₗ_apply, real_inner_self_eq_norm_sq,
      zero_add, Real.rpow_two]
    ring
    -- 🎉 no goals
  · simp only [Fin.mk_one, coe_basisRightAngleRotation, Matrix.cons_val_one, Matrix.head_cons,
      LinearMap.sub_apply, LinearMap.smul_apply, areaForm_rightAngleRotation_right,
      real_inner_self_eq_norm_sq, smul_eq_mul, innerₛₗ_apply, inner_rightAngleRotation_right,
      areaForm_apply_self, neg_zero, mul_zero, sub_zero, Real.rpow_two, real_inner_comm]
    ring
    -- 🎉 no goals
#align orientation.inner_mul_area_form_sub' Orientation.inner_mul_areaForm_sub'

/-- For vectors `a x y : E`, the identity `⟪a, x⟫ * ω a y - ω a x * ⟪a, y⟫ = ‖a‖ ^ 2 * ω x y`. -/
theorem inner_mul_areaForm_sub (a x y : E) : ⟪a, x⟫ * ω a y - ω a x * ⟪a, y⟫ = ‖a‖ ^ 2 * ω x y :=
  congr_arg (fun f : E →ₗ[ℝ] ℝ => f y) (o.inner_mul_areaForm_sub' a x)
#align orientation.inner_mul_area_form_sub Orientation.inner_mul_areaForm_sub

theorem nonneg_inner_and_areaForm_eq_zero_iff_sameRay (x y : E) :
    0 ≤ ⟪x, y⟫ ∧ ω x y = 0 ↔ SameRay ℝ x y := by
  by_cases hx : x = 0
  -- ⊢ 0 ≤ inner x y ∧ ↑(↑(areaForm o) x) y = 0 ↔ SameRay ℝ x y
  · simp [hx]
    -- 🎉 no goals
  constructor
  -- ⊢ 0 ≤ inner x y ∧ ↑(↑(areaForm o) x) y = 0 → SameRay ℝ x y
  · let a : ℝ := (o.basisRightAngleRotation x hx).repr y 0
    -- ⊢ 0 ≤ inner x y ∧ ↑(↑(areaForm o) x) y = 0 → SameRay ℝ x y
    let b : ℝ := (o.basisRightAngleRotation x hx).repr y 1
    -- ⊢ 0 ≤ inner x y ∧ ↑(↑(areaForm o) x) y = 0 → SameRay ℝ x y
    suffices ↑0 ≤ a * ‖x‖ ^ 2 ∧ b * ‖x‖ ^ 2 = 0 → SameRay ℝ x (a • x + b • J x) by
      rw [← (o.basisRightAngleRotation x hx).sum_repr y]
      simp only [Fin.sum_univ_succ, coe_basisRightAngleRotation, Matrix.cons_val_zero,
        Fin.succ_zero_eq_one', Fintype.univ_of_isEmpty, Finset.sum_empty, areaForm_apply_self,
        map_smul, map_add, real_inner_smul_right, inner_add_right, Matrix.cons_val_one,
        Matrix.head_cons, Algebra.id.smul_eq_mul, areaForm_rightAngleRotation_right,
        mul_zero, add_zero, zero_add, neg_zero, inner_rightAngleRotation_right,
        real_inner_self_eq_norm_sq]
      exact this
    rintro ⟨ha, hb⟩
    -- ⊢ SameRay ℝ x (a • x + b • ↑(rightAngleRotation o) x)
    have hx' : 0 < ‖x‖ := by simpa using hx
    -- ⊢ SameRay ℝ x (a • x + b • ↑(rightAngleRotation o) x)
    have ha' : 0 ≤ a := nonneg_of_mul_nonneg_left ha (by positivity)
    -- ⊢ SameRay ℝ x (a • x + b • ↑(rightAngleRotation o) x)
    have hb' : b = 0 := eq_zero_of_ne_zero_of_mul_right_eq_zero (pow_ne_zero 2 hx'.ne') hb
    -- ⊢ SameRay ℝ x (a • x + b • ↑(rightAngleRotation o) x)
    simpa [hb'] using SameRay.sameRay_nonneg_smul_right x ha'
    -- 🎉 no goals
  · intro h
    -- ⊢ 0 ≤ inner x y ∧ ↑(↑(areaForm o) x) y = 0
    obtain ⟨r, hr, rfl⟩ := h.exists_nonneg_left hx
    -- ⊢ 0 ≤ inner x (r • x) ∧ ↑(↑(areaForm o) x) (r • x) = 0
    simp only [inner_smul_right, real_inner_self_eq_norm_sq, LinearMap.map_smulₛₗ,
      areaForm_apply_self, Algebra.id.smul_eq_mul, mul_zero, eq_self_iff_true,
      and_true_iff]
    positivity
    -- 🎉 no goals
#align orientation.nonneg_inner_and_area_form_eq_zero_iff_same_ray Orientation.nonneg_inner_and_areaForm_eq_zero_iff_sameRay

/-- A complex-valued real-bilinear map on an oriented real inner product space of dimension 2. Its
real part is the inner product and its imaginary part is `Orientation.areaForm`.

On `ℂ` with the standard orientation, `kahler w z = conj w * z`; see `Complex.kahler`. -/
def kahler : E →ₗ[ℝ] E →ₗ[ℝ] ℂ :=
  LinearMap.llcomp ℝ E ℝ ℂ Complex.ofRealClm ∘ₗ innerₛₗ ℝ +
    LinearMap.llcomp ℝ E ℝ ℂ ((LinearMap.lsmul ℝ ℂ).flip Complex.I) ∘ₗ ω
#align orientation.kahler Orientation.kahler

theorem kahler_apply_apply (x y : E) : o.kahler x y = ⟪x, y⟫ + ω x y • Complex.I :=
  rfl
#align orientation.kahler_apply_apply Orientation.kahler_apply_apply

theorem kahler_swap (x y : E) : o.kahler x y = conj (o.kahler y x) := by
  have : ∀ r : ℝ, Complex.ofReal' r = @IsROrC.ofReal ℂ _ r := fun r => rfl
  -- ⊢ ↑(↑(kahler o) x) y = ↑(starRingEnd ((fun x => ℂ) x)) (↑(↑(kahler o) y) x)
  simp only [kahler_apply_apply]
  -- ⊢ ↑(inner x y) + ↑(↑(areaForm o) x) y • Complex.I = ↑(starRingEnd ℂ) (↑(inner  …
  rw [real_inner_comm, areaForm_swap]
  -- ⊢ ↑(inner y x) + -↑(↑(areaForm o) y) x • Complex.I = ↑(starRingEnd ℂ) (↑(inner …
  simp [this]
  -- 🎉 no goals
#align orientation.kahler_swap Orientation.kahler_swap

@[simp]
theorem kahler_apply_self (x : E) : o.kahler x x = ‖x‖ ^ 2 := by
  simp [kahler_apply_apply, real_inner_self_eq_norm_sq]
  -- 🎉 no goals
#align orientation.kahler_apply_self Orientation.kahler_apply_self

@[simp]
theorem kahler_rightAngleRotation_left (x y : E) :
    o.kahler (J x) y = -Complex.I * o.kahler x y := by
  simp only [o.areaForm_rightAngleRotation_left, o.inner_rightAngleRotation_left,
    o.kahler_apply_apply, Complex.ofReal_neg, Complex.real_smul]
  linear_combination ω x y * Complex.I_sq
  -- 🎉 no goals
#align orientation.kahler_right_angle_rotation_left Orientation.kahler_rightAngleRotation_left

@[simp]
theorem kahler_rightAngleRotation_right (x y : E) :
    o.kahler x (J y) = Complex.I * o.kahler x y := by
  simp only [o.areaForm_rightAngleRotation_right, o.inner_rightAngleRotation_right,
    o.kahler_apply_apply, Complex.ofReal_neg, Complex.real_smul]
  linear_combination -ω x y * Complex.I_sq
  -- 🎉 no goals
#align orientation.kahler_right_angle_rotation_right Orientation.kahler_rightAngleRotation_right

-- @[simp] -- Porting note: simp normal form is `kahler_comp_rightAngleRotation'`
theorem kahler_comp_rightAngleRotation (x y : E) : o.kahler (J x) (J y) = o.kahler x y := by
  simp only [kahler_rightAngleRotation_left, kahler_rightAngleRotation_right]
  -- ⊢ Complex.I * (-Complex.I * ↑(↑(kahler o) x) y) = ↑(↑(kahler o) x) y
  linear_combination -o.kahler x y * Complex.I_sq
  -- 🎉 no goals
#align orientation.kahler_comp_right_angle_rotation Orientation.kahler_comp_rightAngleRotation

theorem kahler_comp_rightAngleRotation' (x y : E) :
    -(Complex.I * (Complex.I * o.kahler x y)) = o.kahler x y := by
  linear_combination -o.kahler x y * Complex.I_sq
  -- 🎉 no goals

@[simp]
theorem kahler_neg_orientation (x y : E) : (-o).kahler x y = conj (o.kahler x y) := by
  have : ∀ r : ℝ, Complex.ofReal' r = @IsROrC.ofReal ℂ _ r := fun r => rfl
  -- ⊢ ↑(↑(kahler (-o)) x) y = ↑(starRingEnd ((fun x => ℂ) y)) (↑(↑(kahler o) x) y)
  simp [kahler_apply_apply, this]
  -- 🎉 no goals
#align orientation.kahler_neg_orientation Orientation.kahler_neg_orientation

theorem kahler_mul (a x y : E) : o.kahler x a * o.kahler a y = ‖a‖ ^ 2 * o.kahler x y := by
  trans (↑(‖a‖ ^ 2) : ℂ) * o.kahler x y
  -- ⊢ ↑(↑(kahler o) x) a * ↑(↑(kahler o) a) y = ↑(‖a‖ ^ 2) * ↑(↑(kahler o) x) y
  · ext
    -- ⊢ (↑(↑(kahler o) x) a * ↑(↑(kahler o) a) y).re = (↑(‖a‖ ^ 2) * ↑(↑(kahler o) x …
    · simp only [o.kahler_apply_apply, Complex.add_im, Complex.add_re, Complex.I_im, Complex.I_re,
        Complex.mul_im, Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re, Complex.real_smul]
      rw [real_inner_comm a x, o.areaForm_swap x a]
      -- ⊢ (inner a x + (-↑(↑(areaForm o) a) x * 0 - 0 * 1)) * (inner a y + (↑(↑(areaFo …
      linear_combination o.inner_mul_inner_add_areaForm_mul_areaForm a x y
      -- 🎉 no goals
    · simp only [o.kahler_apply_apply, Complex.add_im, Complex.add_re, Complex.I_im, Complex.I_re,
        Complex.mul_im, Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re, Complex.real_smul]
      rw [real_inner_comm a x, o.areaForm_swap x a]
      -- ⊢ (inner a x + (-↑(↑(areaForm o) a) x * 0 - 0 * 1)) * (0 + (↑(↑(areaForm o) a) …
      linear_combination o.inner_mul_areaForm_sub a x y
      -- 🎉 no goals
  · norm_cast
    -- 🎉 no goals
#align orientation.kahler_mul Orientation.kahler_mul

theorem normSq_kahler (x y : E) : Complex.normSq (o.kahler x y) = ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  simpa [kahler_apply_apply, Complex.normSq, sq] using o.inner_sq_add_areaForm_sq x y
  -- 🎉 no goals
#align orientation.norm_sq_kahler Orientation.normSq_kahler

theorem abs_kahler (x y : E) : Complex.abs (o.kahler x y) = ‖x‖ * ‖y‖ := by
  rw [← sq_eq_sq, Complex.sq_abs]
  · linear_combination o.normSq_kahler x y
    -- 🎉 no goals
  · positivity
    -- 🎉 no goals
  · positivity
    -- 🎉 no goals
#align orientation.abs_kahler Orientation.abs_kahler

theorem norm_kahler (x y : E) : ‖o.kahler x y‖ = ‖x‖ * ‖y‖ := by simpa using o.abs_kahler x y
                                                                 -- 🎉 no goals
#align orientation.norm_kahler Orientation.norm_kahler

theorem eq_zero_or_eq_zero_of_kahler_eq_zero {x y : E} (hx : o.kahler x y = 0) : x = 0 ∨ y = 0 := by
  have : ‖x‖ * ‖y‖ = 0 := by simpa [hx] using (o.norm_kahler x y).symm
  -- ⊢ x = 0 ∨ y = 0
  cases' eq_zero_or_eq_zero_of_mul_eq_zero this with h h
  -- ⊢ x = 0 ∨ y = 0
  · left
    -- ⊢ x = 0
    simpa using h
    -- 🎉 no goals
  · right
    -- ⊢ y = 0
    simpa using h
    -- 🎉 no goals
#align orientation.eq_zero_or_eq_zero_of_kahler_eq_zero Orientation.eq_zero_or_eq_zero_of_kahler_eq_zero

theorem kahler_eq_zero_iff (x y : E) : o.kahler x y = 0 ↔ x = 0 ∨ y = 0 := by
  refine' ⟨o.eq_zero_or_eq_zero_of_kahler_eq_zero, _⟩
  -- ⊢ x = 0 ∨ y = 0 → ↑(↑(kahler o) x) y = 0
  rintro (rfl | rfl) <;> simp
  -- ⊢ ↑(↑(kahler o) 0) y = 0
                         -- 🎉 no goals
                         -- 🎉 no goals
#align orientation.kahler_eq_zero_iff Orientation.kahler_eq_zero_iff

theorem kahler_ne_zero {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) : o.kahler x y ≠ 0 := by
  apply mt o.eq_zero_or_eq_zero_of_kahler_eq_zero
  -- ⊢ ¬(x = 0 ∨ y = 0)
  tauto
  -- 🎉 no goals
#align orientation.kahler_ne_zero Orientation.kahler_ne_zero

theorem kahler_ne_zero_iff (x y : E) : o.kahler x y ≠ 0 ↔ x ≠ 0 ∧ y ≠ 0 := by
  refine' ⟨_, fun h => o.kahler_ne_zero h.1 h.2⟩
  -- ⊢ ↑(↑(kahler o) x) y ≠ 0 → x ≠ 0 ∧ y ≠ 0
  contrapose
  -- ⊢ ¬(x ≠ 0 ∧ y ≠ 0) → ¬↑(↑(kahler o) x) y ≠ 0
  simp only [not_and_or, Classical.not_not, kahler_apply_apply, Complex.real_smul]
  -- ⊢ x = 0 ∨ y = 0 → ↑(inner x y) + ↑(↑(↑(areaForm o) x) y) * Complex.I = 0
  rintro (rfl | rfl) <;> simp
  -- ⊢ ↑(inner 0 y) + ↑(↑(↑(areaForm o) 0) y) * Complex.I = 0
                         -- 🎉 no goals
                         -- 🎉 no goals
#align orientation.kahler_ne_zero_iff Orientation.kahler_ne_zero_iff

theorem kahler_map {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [hF : Fact (finrank ℝ F = 2)] (φ : E ≃ₗᵢ[ℝ] F) (x y : F) :
    (Orientation.map (Fin 2) φ.toLinearEquiv o).kahler x y = o.kahler (φ.symm x) (φ.symm y) := by
  simp [kahler_apply_apply, areaForm_map]
  -- 🎉 no goals
#align orientation.kahler_map Orientation.kahler_map

/-- The bilinear map `kahler` is invariant under pullback by a positively-oriented isometric
automorphism. -/
theorem kahler_comp_linearIsometryEquiv (φ : E ≃ₗᵢ[ℝ] E)
    (hφ : 0 < LinearMap.det (φ.toLinearEquiv : E →ₗ[ℝ] E)) (x y : E) :
    o.kahler (φ x) (φ y) = o.kahler x y := by
  simp [kahler_apply_apply, o.areaForm_comp_linearIsometryEquiv φ hφ]
  -- 🎉 no goals
#align orientation.kahler_comp_linear_isometry_equiv Orientation.kahler_comp_linearIsometryEquiv

end Orientation

namespace Complex

attribute [local instance] Complex.finrank_real_complex_fact

@[simp]
protected theorem areaForm (w z : ℂ) : Complex.orientation.areaForm w z = (conj w * z).im := by
  let o := Complex.orientation
  -- ⊢ ↑(↑(Orientation.areaForm Complex.orientation) w) z = (↑(starRingEnd ℂ) w * z …
  simp only [o.areaForm_to_volumeForm, o.volumeForm_robust Complex.orthonormalBasisOneI rfl,
    (Basis.det_apply), Matrix.det_fin_two, (Basis.toMatrix_apply), toBasis_orthonormalBasisOneI,
    Matrix.cons_val_zero, coe_basisOneI_repr, Matrix.cons_val_one, Matrix.head_cons, mul_im,
    conj_re, conj_im]
  ring
  -- 🎉 no goals
#align complex.area_form Complex.areaForm

@[simp]
protected theorem rightAngleRotation (z : ℂ) :
    Complex.orientation.rightAngleRotation z = I * z := by
  apply ext_inner_right ℝ
  -- ⊢ ∀ (v : ℂ), inner (↑(Orientation.rightAngleRotation Complex.orientation) z) v …
  intro w
  -- ⊢ inner (↑(Orientation.rightAngleRotation Complex.orientation) z) w = inner (I …
  rw [Orientation.inner_rightAngleRotation_left]
  -- ⊢ ↑(↑(Orientation.areaForm Complex.orientation) z) w = inner (I * z) w
  simp only [Complex.areaForm, Complex.inner, mul_re, mul_im, conj_re, conj_im, map_mul, conj_I,
    neg_re, neg_im, I_re, I_im]
  ring
  -- 🎉 no goals
#align complex.right_angle_rotation Complex.rightAngleRotation

@[simp]
protected theorem kahler (w z : ℂ) : Complex.orientation.kahler w z = conj w * z := by
  rw [Orientation.kahler_apply_apply]
  -- ⊢ ↑(inner w z) + ↑(↑(Orientation.areaForm Complex.orientation) w) z • I = ↑(st …
  ext1 <;> simp
  -- ⊢ (↑(inner w z) + ↑(↑(Orientation.areaForm Complex.orientation) w) z • I).re = …
           -- 🎉 no goals
           -- 🎉 no goals
#align complex.kahler Complex.kahler

end Complex

namespace Orientation

local notation "ω" => o.areaForm

local notation "J" => o.rightAngleRotation

open Complex

-- Porting note: The instance `finrank_real_complex_fact` cannot be found by synthesis for
-- `areaForm_map`, `rightAngleRotation_map` and `kahler_map` in the three theorems below,
-- so it has to be provided by unification (i.e. by naming the instance-implicit argument where
-- it belongs and using `(hF := _)`).

/-- The area form on an oriented real inner product space of dimension 2 can be evaluated in terms
of a complex-number representation of the space. -/
theorem areaForm_map_complex (f : E ≃ₗᵢ[ℝ] ℂ)
    (hf : Orientation.map (Fin 2) f.toLinearEquiv o = Complex.orientation) (x y : E) :
    ω x y = (conj (f x) * f y).im := by
  rw [← Complex.areaForm, ← hf, areaForm_map (hF := _)]
  -- ⊢ ↑(↑(areaForm o) x) y = ↑(↑(areaForm o) (↑(LinearIsometryEquiv.symm f) (↑f x) …
  iterate 2 rw [LinearIsometryEquiv.symm_apply_apply]
  -- 🎉 no goals
#align orientation.area_form_map_complex Orientation.areaForm_map_complex

/-- The rotation by 90 degrees on an oriented real inner product space of dimension 2 can be
evaluated in terms of a complex-number representation of the space. -/
theorem rightAngleRotation_map_complex (f : E ≃ₗᵢ[ℝ] ℂ)
    (hf : Orientation.map (Fin 2) f.toLinearEquiv o = Complex.orientation) (x : E) :
    f (J x) = I * f x := by
  rw [← Complex.rightAngleRotation, ← hf, rightAngleRotation_map (hF := _),
    LinearIsometryEquiv.symm_apply_apply]
#align orientation.right_angle_rotation_map_complex Orientation.rightAngleRotation_map_complex

/-- The Kahler form on an oriented real inner product space of dimension 2 can be evaluated in terms
of a complex-number representation of the space. -/
theorem kahler_map_complex (f : E ≃ₗᵢ[ℝ] ℂ)
    (hf : Orientation.map (Fin 2) f.toLinearEquiv o = Complex.orientation) (x y : E) :
    o.kahler x y = conj (f x) * f y := by
  rw [← Complex.kahler, ← hf, kahler_map (hF := _)]
  -- ⊢ ↑(↑(kahler o) x) y = ↑(↑(kahler o) (↑(LinearIsometryEquiv.symm f) (↑f x))) ( …
  iterate 2 rw [LinearIsometryEquiv.symm_apply_apply]
  -- 🎉 no goals
#align orientation.kahler_map_complex Orientation.kahler_map_complex

end Orientation
