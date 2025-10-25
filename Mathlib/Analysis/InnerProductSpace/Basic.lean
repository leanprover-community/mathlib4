/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Sébastien Gouëzel, Frédéric Dupuis
-/
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Defs

/-!
# Properties of inner product spaces

This file proves many basic properties of inner product spaces (real or complex).

## Main results

- `inner_mul_inner_self_le`: the Cauchy-Schwarz inequality (one of many variants).
- `norm_inner_eq_norm_iff`: the equality criterion in the Cauchy-Schwarz inequality (also in many
  variants).
- `inner_eq_sum_norm_sq_div_four`: the polarization identity.

## Tags

inner product space, Hilbert space, norm

-/


noncomputable section

open RCLike Real Filter Topology ComplexConjugate Finsupp

open LinearMap (BilinForm)

variable {𝕜 E F : Type*} [RCLike 𝕜]

section BasicProperties_Seminormed

open scoped InnerProductSpace

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

local postfix:90 "†" => starRingEnd _

export InnerProductSpace (norm_sq_eq_re_inner)

@[simp]
theorem inner_conj_symm (x y : E) : ⟪y, x⟫† = ⟪x, y⟫ :=
  InnerProductSpace.conj_inner_symm _ _

theorem real_inner_comm (x y : F) : ⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ :=
  @inner_conj_symm ℝ _ _ _ _ x y

theorem inner_eq_zero_symm {x y : E} : ⟪x, y⟫ = 0 ↔ ⟪y, x⟫ = 0 := by
  rw [← inner_conj_symm]
  exact star_eq_zero

instance {ι : Sort*} (v : ι → E) : IsSymm ι fun i j => ⟪v i, v j⟫ = 0 where
  symm _ _ := inner_eq_zero_symm.1

@[simp]
theorem inner_self_im (x : E) : im ⟪x, x⟫ = 0 := by rw [← @ofReal_inj 𝕜, im_eq_conj_sub]; simp

theorem inner_add_left (x y z : E) : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫ :=
  InnerProductSpace.add_left _ _ _

theorem inner_add_right (x y z : E) : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x, z⟫ := by
  rw [← inner_conj_symm, inner_add_left, RingHom.map_add]
  simp only [inner_conj_symm]

theorem inner_re_symm (x y : E) : re ⟪x, y⟫ = re ⟪y, x⟫ := by rw [← inner_conj_symm, conj_re]

theorem inner_im_symm (x y : E) : im ⟪x, y⟫ = -im ⟪y, x⟫ := by rw [← inner_conj_symm, conj_im]

section Algebra
variable {𝕝 : Type*} [CommSemiring 𝕝] [StarRing 𝕝] [Algebra 𝕝 𝕜] [Module 𝕝 E]
  [IsScalarTower 𝕝 𝕜 E] [StarModule 𝕝 𝕜]

/-- See `inner_smul_left` for the common special when `𝕜 = 𝕝`. -/
lemma inner_smul_left_eq_star_smul (x y : E) (r : 𝕝) : ⟪r • x, y⟫ = r† • ⟪x, y⟫ := by
  rw [← algebraMap_smul 𝕜 r, InnerProductSpace.smul_left, starRingEnd_apply, starRingEnd_apply,
    ← algebraMap_star_comm, ← smul_eq_mul, algebraMap_smul]

/-- Special case of `inner_smul_left_eq_star_smul` when the acting ring has a trivial star
(e.g. `ℕ`, `ℤ`, `ℚ≥0`, `ℚ`, `ℝ`). -/
lemma inner_smul_left_eq_smul [TrivialStar 𝕝] (x y : E) (r : 𝕝) : ⟪r • x, y⟫ = r • ⟪x, y⟫ := by
  rw [inner_smul_left_eq_star_smul, starRingEnd_apply, star_trivial]

/-- See `inner_smul_right` for the common special when `𝕜 = 𝕝`. -/
lemma inner_smul_right_eq_smul (x y : E) (r : 𝕝) : ⟪x, r • y⟫ = r • ⟪x, y⟫ := by
  rw [← inner_conj_symm, inner_smul_left_eq_star_smul, starRingEnd_apply, starRingEnd_apply,
    star_smul, star_star, ← starRingEnd_apply, inner_conj_symm]

end Algebra

/-- See `inner_smul_left_eq_star_smul` for the case of a general algebra action. -/
theorem inner_smul_left (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪x, y⟫ :=
  inner_smul_left_eq_star_smul ..

theorem real_inner_smul_left (x y : F) (r : ℝ) : ⟪r • x, y⟫_ℝ = r * ⟪x, y⟫_ℝ :=
  inner_smul_left _ _ _

theorem inner_smul_real_left (x y : E) (r : ℝ) : ⟪(r : 𝕜) • x, y⟫ = r • ⟪x, y⟫ := by
  rw [inner_smul_left, conj_ofReal, Algebra.smul_def]

/-- See `inner_smul_right_eq_smul` for the case of a general algebra action. -/
theorem inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * ⟪x, y⟫ :=
  inner_smul_right_eq_smul ..

theorem real_inner_smul_right (x y : F) (r : ℝ) : ⟪x, r • y⟫_ℝ = r * ⟪x, y⟫_ℝ :=
  inner_smul_right _ _ _

theorem inner_smul_real_right (x y : E) (r : ℝ) : ⟪x, (r : 𝕜) • y⟫ = r • ⟪x, y⟫ := by
  rw [inner_smul_right, Algebra.smul_def]

/-- The inner product as a sesquilinear form.

Note that in the case `𝕜 = ℝ` this is a bilinear form. -/
@[simps!]
def sesqFormOfInner : E →ₗ[𝕜] E →ₗ⋆[𝕜] 𝕜 :=
  LinearMap.mk₂'ₛₗ (RingHom.id 𝕜) (starRingEnd _) (fun x y => ⟪y, x⟫)
    (fun _x _y _z => inner_add_right _ _ _) (fun _r _x _y => inner_smul_right _ _ _)
    (fun _x _y _z => inner_add_left _ _ _) fun _r _x _y => inner_smul_left _ _ _

/-- The real inner product as a bilinear form.

Note that unlike `sesqFormOfInner`, this does not reverse the order of the arguments. -/
@[simps!]
def bilinFormOfRealInner : BilinForm ℝ F := sesqFormOfInner.flip

/-- An inner product with a sum on the left. -/
theorem sum_inner {ι : Type*} (s : Finset ι) (f : ι → E) (x : E) :
    ⟪∑ i ∈ s, f i, x⟫ = ∑ i ∈ s, ⟪f i, x⟫ :=
  map_sum (sesqFormOfInner (𝕜 := 𝕜) (E := E) x) _ _

/-- An inner product with a sum on the right. -/
theorem inner_sum {ι : Type*} (s : Finset ι) (f : ι → E) (x : E) :
    ⟪x, ∑ i ∈ s, f i⟫ = ∑ i ∈ s, ⟪x, f i⟫ :=
  map_sum (LinearMap.flip sesqFormOfInner x) _ _

/-- An inner product with a sum on the left, `Finsupp` version. -/
protected theorem Finsupp.sum_inner {ι : Type*} (l : ι →₀ 𝕜) (v : ι → E) (x : E) :
    ⟪l.sum fun (i : ι) (a : 𝕜) => a • v i, x⟫ = l.sum fun (i : ι) (a : 𝕜) => conj a • ⟪v i, x⟫ := by
  convert sum_inner (𝕜 := 𝕜) l.support (fun a => l a • v a) x
  simp only [inner_smul_left, Finsupp.sum, smul_eq_mul]

/-- An inner product with a sum on the right, `Finsupp` version. -/
protected theorem Finsupp.inner_sum {ι : Type*} (l : ι →₀ 𝕜) (v : ι → E) (x : E) :
    ⟪x, l.sum fun (i : ι) (a : 𝕜) => a • v i⟫ = l.sum fun (i : ι) (a : 𝕜) => a • ⟪x, v i⟫ := by
  convert inner_sum (𝕜 := 𝕜) l.support (fun a => l a • v a) x
  simp only [inner_smul_right, Finsupp.sum, smul_eq_mul]

protected theorem DFinsupp.sum_inner {ι : Type*} [DecidableEq ι] {α : ι → Type*}
    [∀ i, AddZeroClass (α i)] [∀ (i) (x : α i), Decidable (x ≠ 0)] (f : ∀ i, α i → E)
    (l : Π₀ i, α i) (x : E) : ⟪l.sum f, x⟫ = l.sum fun i a => ⟪f i a, x⟫ := by
  simp +contextual only [DFinsupp.sum, sum_inner]

protected theorem DFinsupp.inner_sum {ι : Type*} [DecidableEq ι] {α : ι → Type*}
    [∀ i, AddZeroClass (α i)] [∀ (i) (x : α i), Decidable (x ≠ 0)] (f : ∀ i, α i → E)
    (l : Π₀ i, α i) (x : E) : ⟪x, l.sum f⟫ = l.sum fun i a => ⟪x, f i a⟫ := by
  simp +contextual only [DFinsupp.sum, inner_sum]

@[simp]
theorem inner_zero_left (x : E) : ⟪0, x⟫ = 0 := by
  rw [← zero_smul 𝕜 (0 : E), inner_smul_left, RingHom.map_zero, zero_mul]

theorem inner_re_zero_left (x : E) : re ⟪0, x⟫ = 0 := by
  simp only [inner_zero_left, AddMonoidHom.map_zero]

@[simp]
theorem inner_zero_right (x : E) : ⟪x, 0⟫ = 0 := by
  rw [← inner_conj_symm, inner_zero_left, RingHom.map_zero]

theorem inner_re_zero_right (x : E) : re ⟪x, 0⟫ = 0 := by
  simp only [inner_zero_right, AddMonoidHom.map_zero]

theorem inner_self_nonneg {x : E} : 0 ≤ re ⟪x, x⟫ :=
  PreInnerProductSpace.toCore.re_inner_nonneg x

theorem real_inner_self_nonneg {x : F} : 0 ≤ ⟪x, x⟫_ℝ :=
  @inner_self_nonneg ℝ F _ _ _ x

@[simp]
theorem inner_self_ofReal_re (x : E) : (re ⟪x, x⟫ : 𝕜) = ⟪x, x⟫ :=
  ((RCLike.is_real_TFAE (⟪x, x⟫ : 𝕜)).out 2 3).2 (inner_self_im (𝕜 := 𝕜) x)

theorem inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ = (‖x‖ : 𝕜) ^ 2 := by
  rw [← inner_self_ofReal_re, ← norm_sq_eq_re_inner, ofReal_pow]

theorem inner_self_re_eq_norm (x : E) : re ⟪x, x⟫ = ‖⟪x, x⟫‖ := by
  conv_rhs => rw [← inner_self_ofReal_re]
  symm
  exact norm_of_nonneg inner_self_nonneg

theorem inner_self_ofReal_norm (x : E) : (‖⟪x, x⟫‖ : 𝕜) = ⟪x, x⟫ := by
  rw [← inner_self_re_eq_norm]
  exact inner_self_ofReal_re _

theorem real_inner_self_abs (x : F) : |⟪x, x⟫_ℝ| = ⟪x, x⟫_ℝ :=
  @inner_self_ofReal_norm ℝ F _ _ _ x

theorem norm_inner_symm (x y : E) : ‖⟪x, y⟫‖ = ‖⟪y, x⟫‖ := by rw [← inner_conj_symm, norm_conj]

@[simp]
theorem inner_neg_left (x y : E) : ⟪-x, y⟫ = -⟪x, y⟫ := by
  rw [← neg_one_smul 𝕜 x, inner_smul_left]
  simp

@[simp]
theorem inner_neg_right (x y : E) : ⟪x, -y⟫ = -⟪x, y⟫ := by
  rw [← inner_conj_symm, inner_neg_left]; simp only [RingHom.map_neg, inner_conj_symm]

theorem inner_neg_neg (x y : E) : ⟪-x, -y⟫ = ⟪x, y⟫ := by simp

theorem inner_self_conj (x : E) : ⟪x, x⟫† = ⟪x, x⟫ := inner_conj_symm _ _

theorem inner_sub_left (x y z : E) : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫ := by
  simp [sub_eq_add_neg, inner_add_left]

theorem inner_sub_right (x y z : E) : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫ := by
  simp [sub_eq_add_neg, inner_add_right]

theorem inner_mul_symm_re_eq_norm (x y : E) : re (⟪x, y⟫ * ⟪y, x⟫) = ‖⟪x, y⟫ * ⟪y, x⟫‖ := by
  rw [← inner_conj_symm, mul_comm]
  exact re_eq_norm_of_mul_conj ⟪y, x⟫

/-- Expand `⟪x + y, x + y⟫` -/
theorem inner_add_add_self (x y : E) : ⟪x + y, x + y⟫ = ⟪x, x⟫ + ⟪x, y⟫ + ⟪y, x⟫ + ⟪y, y⟫ := by
  simp only [inner_add_left, inner_add_right]; ring

/-- Expand `⟪x + y, x + y⟫_ℝ` -/
theorem real_inner_add_add_self (x y : F) :
    ⟪x + y, x + y⟫_ℝ = ⟪x, x⟫_ℝ + 2 * ⟪x, y⟫_ℝ + ⟪y, y⟫_ℝ := by
  have : ⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ := by rw [← inner_conj_symm]; rfl
  simp only [inner_add_add_self, this, add_left_inj]
  ring

-- Expand `⟪x - y, x - y⟫`
theorem inner_sub_sub_self (x y : E) : ⟪x - y, x - y⟫ = ⟪x, x⟫ - ⟪x, y⟫ - ⟪y, x⟫ + ⟪y, y⟫ := by
  simp only [inner_sub_left, inner_sub_right]; ring

/-- Expand `⟪x - y, x - y⟫_ℝ` -/
theorem real_inner_sub_sub_self (x y : F) :
    ⟪x - y, x - y⟫_ℝ = ⟪x, x⟫_ℝ - 2 * ⟪x, y⟫_ℝ + ⟪y, y⟫_ℝ := by
  have : ⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ := by rw [← inner_conj_symm]; rfl
  simp only [inner_sub_sub_self, this, add_left_inj]
  ring

/-- Parallelogram law -/
theorem parallelogram_law {x y : E} : ⟪x + y, x + y⟫ + ⟪x - y, x - y⟫ = 2 * (⟪x, x⟫ + ⟪y, y⟫) := by
  simp only [inner_add_add_self, inner_sub_sub_self]
  ring

/-- **Cauchy–Schwarz inequality**. -/
theorem inner_mul_inner_self_le (x y : E) : ‖⟪x, y⟫‖ * ‖⟪y, x⟫‖ ≤ re ⟪x, x⟫ * re ⟪y, y⟫ :=
  letI : PreInnerProductSpace.Core 𝕜 E := PreInnerProductSpace.toCore
  InnerProductSpace.Core.inner_mul_inner_self_le x y

/-- Cauchy–Schwarz inequality for real inner products. -/
theorem real_inner_mul_inner_self_le (x y : F) : ⟪x, y⟫_ℝ * ⟪x, y⟫_ℝ ≤ ⟪x, x⟫_ℝ * ⟪y, y⟫_ℝ :=
  calc
    ⟪x, y⟫_ℝ * ⟪x, y⟫_ℝ ≤ ‖⟪x, y⟫_ℝ‖ * ‖⟪y, x⟫_ℝ‖ := by
      rw [real_inner_comm y, ← norm_mul]
      exact le_abs_self _
    _ ≤ ⟪x, x⟫_ℝ * ⟪y, y⟫_ℝ := @inner_mul_inner_self_le ℝ _ _ _ _ x y

theorem inner_eq_ofReal_norm_sq_left_iff {v w : E} : ⟪v, w⟫_𝕜 = ‖v‖ ^ 2 ↔ ⟪v, v - w⟫_𝕜 = 0 := by
  rw [inner_sub_right, sub_eq_zero, inner_self_eq_norm_sq_to_K, eq_comm]

theorem inner_eq_norm_sq_left_iff {v w : F} : ⟪v, w⟫_ℝ = ‖v‖ ^ 2 ↔ ⟪v, v - w⟫_ℝ = 0 :=
  inner_eq_ofReal_norm_sq_left_iff

theorem inner_eq_ofReal_norm_sq_right_iff {v w : E} : ⟪v, w⟫_𝕜 = ‖w‖ ^ 2 ↔ ⟪v - w, w⟫_𝕜 = 0 := by
  rw [inner_sub_left, sub_eq_zero, inner_self_eq_norm_sq_to_K, eq_comm]

theorem inner_eq_norm_sq_right_iff {v w : F} : ⟪v, w⟫_ℝ = ‖w‖ ^ 2 ↔ ⟪v - w, w⟫_ℝ = 0 :=
  inner_eq_ofReal_norm_sq_right_iff

end BasicProperties_Seminormed

section BasicProperties

variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

export InnerProductSpace (norm_sq_eq_re_inner)

@[simp]
theorem inner_self_eq_zero {x : E} : ⟪x, x⟫ = 0 ↔ x = 0 := by
  rw [inner_self_eq_norm_sq_to_K, sq_eq_zero_iff, ofReal_eq_zero, norm_eq_zero]

theorem inner_self_ne_zero {x : E} : ⟪x, x⟫ ≠ 0 ↔ x ≠ 0 :=
  inner_self_eq_zero.not

variable (𝕜)

theorem ext_inner_left {x y : E} (h : ∀ v, ⟪v, x⟫ = ⟪v, y⟫) : x = y := by
  rw [← sub_eq_zero, ← @inner_self_eq_zero 𝕜, inner_sub_right, sub_eq_zero, h (x - y)]

theorem ext_iff_inner_left {x y : E} : x = y ↔ ∀ v, ⟪v, x⟫ = ⟪v, y⟫ :=
  ⟨fun h _ ↦ h ▸ rfl, ext_inner_left 𝕜⟩

theorem ext_inner_right {x y : E} (h : ∀ v, ⟪x, v⟫ = ⟪y, v⟫) : x = y := by
  rw [← sub_eq_zero, ← @inner_self_eq_zero 𝕜, inner_sub_left, sub_eq_zero, h (x - y)]

theorem ext_iff_inner_right {x y : E} : x = y ↔ ∀ v, ⟪x, v⟫ = ⟪y, v⟫ :=
  ⟨fun h _ ↦ h ▸ rfl, ext_inner_right 𝕜⟩

variable {𝕜}

@[simp]
theorem re_inner_self_nonpos {x : E} : re ⟪x, x⟫ ≤ 0 ↔ x = 0 := by
  rw [← norm_sq_eq_re_inner, (sq_nonneg _).ge_iff_eq', sq_eq_zero_iff, norm_eq_zero]

@[simp]
lemma re_inner_self_pos {x : E} : 0 < re ⟪x, x⟫ ↔ x ≠ 0 := by
  simpa [-re_inner_self_nonpos] using re_inner_self_nonpos (𝕜 := 𝕜) (x := x).not

@[deprecated (since := "2025-04-22")] alias inner_self_nonpos := re_inner_self_nonpos
@[deprecated (since := "2025-04-22")] alias inner_self_pos := re_inner_self_pos

open scoped InnerProductSpace in
theorem real_inner_self_nonpos {x : F} : ⟪x, x⟫_ℝ ≤ 0 ↔ x = 0 := re_inner_self_nonpos (𝕜 := ℝ)

open scoped InnerProductSpace in
theorem real_inner_self_pos {x : F} : 0 < ⟪x, x⟫_ℝ ↔ x ≠ 0 := re_inner_self_pos (𝕜 := ℝ)

/-- A family of vectors is linearly independent if they are nonzero
and orthogonal. -/
theorem linearIndependent_of_ne_zero_of_inner_eq_zero {ι : Type*} {v : ι → E} (hz : ∀ i, v i ≠ 0)
    (ho : Pairwise fun i j => ⟪v i, v j⟫ = 0) : LinearIndependent 𝕜 v := by
  rw [linearIndependent_iff']
  intro s g hg i hi
  have h' : g i * ⟪v i, v i⟫ = ⟪v i, ∑ j ∈ s, g j • v j⟫ := by
    rw [inner_sum]
    symm
    convert Finset.sum_eq_single (M := 𝕜) i ?_ ?_
    · rw [inner_smul_right]
    · intro j _hj hji
      rw [inner_smul_right, ho hji.symm, mul_zero]
    · exact fun h => False.elim (h hi)
  simpa [hg, hz] using h'

end BasicProperties

section Norm_Seminormed

open scoped InnerProductSpace

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

local notation "IK" => @RCLike.I 𝕜 _

theorem norm_eq_sqrt_re_inner (x : E) : ‖x‖ = √(re ⟪x, x⟫) :=
  calc
    ‖x‖ = √(‖x‖ ^ 2) := (sqrt_sq (norm_nonneg _)).symm
    _ = √(re ⟪x, x⟫) := congr_arg _ (norm_sq_eq_re_inner _)

@[deprecated (since := "2025-04-22")] alias norm_eq_sqrt_inner := norm_eq_sqrt_re_inner

theorem norm_eq_sqrt_real_inner (x : F) : ‖x‖ = √⟪x, x⟫_ℝ :=
  @norm_eq_sqrt_re_inner ℝ _ _ _ _ x

theorem inner_self_eq_norm_mul_norm (x : E) : re ⟪x, x⟫ = ‖x‖ * ‖x‖ := by
  rw [@norm_eq_sqrt_re_inner 𝕜, ← sqrt_mul inner_self_nonneg (re ⟪x, x⟫),
    sqrt_mul_self inner_self_nonneg]

theorem inner_self_eq_norm_sq (x : E) : re ⟪x, x⟫ = ‖x‖ ^ 2 := by
  rw [pow_two, inner_self_eq_norm_mul_norm]

theorem real_inner_self_eq_norm_mul_norm (x : F) : ⟪x, x⟫_ℝ = ‖x‖ * ‖x‖ := by
  have h := @inner_self_eq_norm_mul_norm ℝ F _ _ _ x
  simpa using h

theorem real_inner_self_eq_norm_sq (x : F) : ⟪x, x⟫_ℝ = ‖x‖ ^ 2 := by
  rw [pow_two, real_inner_self_eq_norm_mul_norm]

/-- Expand the square -/
theorem norm_add_sq (x y : E) : ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * re ⟪x, y⟫ + ‖y‖ ^ 2 := by
  repeat' rw [sq (M := ℝ), ← @inner_self_eq_norm_mul_norm 𝕜]
  rw [inner_add_add_self, two_mul]
  simp only [add_assoc, add_left_inj, add_right_inj, AddMonoidHom.map_add]
  rw [← inner_conj_symm, conj_re]

alias norm_add_pow_two := norm_add_sq

/-- Expand the square -/
theorem norm_add_sq_real (x y : F) : ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * ⟪x, y⟫_ℝ + ‖y‖ ^ 2 := by
  have h := @norm_add_sq ℝ _ _ _ _ x y
  simpa using h

alias norm_add_pow_two_real := norm_add_sq_real

/-- Expand the square -/
theorem norm_add_mul_self (x y : E) :
    ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + 2 * re ⟪x, y⟫ + ‖y‖ * ‖y‖ := by
  repeat' rw [← sq (M := ℝ)]
  exact norm_add_sq _ _

/-- Expand the square -/
theorem norm_add_mul_self_real (x y : F) :
    ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + 2 * ⟪x, y⟫_ℝ + ‖y‖ * ‖y‖ := by
  have h := @norm_add_mul_self ℝ _ _ _ _ x y
  simpa using h

/-- Expand the square -/
theorem norm_sub_sq (x y : E) : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * re ⟪x, y⟫ + ‖y‖ ^ 2 := by
  rw [sub_eq_add_neg, @norm_add_sq 𝕜 _ _ _ _ x (-y), norm_neg, inner_neg_right, map_neg, mul_neg,
    sub_eq_add_neg]

alias norm_sub_pow_two := norm_sub_sq

/-- Expand the square -/
theorem norm_sub_sq_real (x y : F) : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * ⟪x, y⟫_ℝ + ‖y‖ ^ 2 :=
  @norm_sub_sq ℝ _ _ _ _ _ _

alias norm_sub_pow_two_real := norm_sub_sq_real

/-- Expand the square -/
theorem norm_sub_mul_self (x y : E) :
    ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ - 2 * re ⟪x, y⟫ + ‖y‖ * ‖y‖ := by
  repeat' rw [← sq (M := ℝ)]
  exact norm_sub_sq _ _

/-- Expand the square -/
theorem norm_sub_mul_self_real (x y : F) :
    ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ - 2 * ⟪x, y⟫_ℝ + ‖y‖ * ‖y‖ := by
  have h := @norm_sub_mul_self ℝ _ _ _ _ x y
  simpa using h

/-- Cauchy–Schwarz inequality with norm -/
theorem norm_inner_le_norm (x y : E) : ‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := 𝕜) x, norm_eq_sqrt_re_inner (𝕜 := 𝕜) y]
  letI : PreInnerProductSpace.Core 𝕜 E := PreInnerProductSpace.toCore
  exact InnerProductSpace.Core.norm_inner_le_norm x y

theorem nnnorm_inner_le_nnnorm (x y : E) : ‖⟪x, y⟫‖₊ ≤ ‖x‖₊ * ‖y‖₊ :=
  norm_inner_le_norm x y

theorem re_inner_le_norm (x y : E) : re ⟪x, y⟫ ≤ ‖x‖ * ‖y‖ :=
  le_trans (re_le_norm ⟪x, y⟫) (norm_inner_le_norm x y)

/-- Cauchy–Schwarz inequality with norm -/
theorem abs_real_inner_le_norm (x y : F) : |⟪x, y⟫_ℝ| ≤ ‖x‖ * ‖y‖ :=
  (Real.norm_eq_abs _).ge.trans (norm_inner_le_norm x y)

/-- Cauchy–Schwarz inequality with norm -/
theorem real_inner_le_norm (x y : F) : ⟪x, y⟫_ℝ ≤ ‖x‖ * ‖y‖ :=
  le_trans (le_abs_self _) (abs_real_inner_le_norm _ _)

lemma inner_eq_zero_of_left {x : E} (y : E) (h : ‖x‖ = 0) : ⟪x, y⟫_𝕜 = 0 := by
  rw [← norm_eq_zero]
  refine le_antisymm ?_ (by positivity)
  exact norm_inner_le_norm _ _ |>.trans <| by simp [h]

lemma inner_eq_zero_of_right (x : E) {y : E} (h : ‖y‖ = 0) : ⟪x, y⟫_𝕜 = 0 := by
  rw [inner_eq_zero_symm, inner_eq_zero_of_left _ h]

variable (𝕜)

include 𝕜 in
theorem parallelogram_law_with_norm (x y : E) :
    ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖) := by
  simp only [← @inner_self_eq_norm_mul_norm 𝕜]
  rw [← re.map_add, parallelogram_law, two_mul, two_mul]
  simp only [re.map_add]

include 𝕜 in
theorem parallelogram_law_with_nnnorm (x y : E) :
    ‖x + y‖₊ * ‖x + y‖₊ + ‖x - y‖₊ * ‖x - y‖₊ = 2 * (‖x‖₊ * ‖x‖₊ + ‖y‖₊ * ‖y‖₊) :=
  Subtype.ext <| parallelogram_law_with_norm 𝕜 x y

variable {𝕜}

/-- Polarization identity: The real part of the inner product, in terms of the norm. -/
theorem re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (x y : E) :
    re ⟪x, y⟫ = (‖x + y‖ * ‖x + y‖ - ‖x‖ * ‖x‖ - ‖y‖ * ‖y‖) / 2 := by
  rw [@norm_add_mul_self 𝕜]
  ring

/-- Polarization identity: The real part of the inner product, in terms of the norm. -/
theorem re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two (x y : E) :
    re ⟪x, y⟫ = (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ - ‖x - y‖ * ‖x - y‖) / 2 := by
  rw [@norm_sub_mul_self 𝕜]
  ring

/-- Polarization identity: The real part of the inner product, in terms of the norm. -/
theorem re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four (x y : E) :
    re ⟪x, y⟫ = (‖x + y‖ * ‖x + y‖ - ‖x - y‖ * ‖x - y‖) / 4 := by
  rw [@norm_add_mul_self 𝕜, @norm_sub_mul_self 𝕜]
  ring

/-- Polarization identity: The imaginary part of the inner product, in terms of the norm. -/
theorem im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_four (x y : E) :
    im ⟪x, y⟫ = (‖x - IK • y‖ * ‖x - IK • y‖ - ‖x + IK • y‖ * ‖x + IK • y‖) / 4 := by
  simp only [@norm_add_mul_self 𝕜, @norm_sub_mul_self 𝕜, inner_smul_right, I_mul_re]
  ring

/-- Polarization identity: The inner product, in terms of the norm. -/
theorem inner_eq_sum_norm_sq_div_four (x y : E) :
    ⟪x, y⟫ = ((‖x + y‖ : 𝕜) ^ 2 - (‖x - y‖ : 𝕜) ^ 2 +
              ((‖x - IK • y‖ : 𝕜) ^ 2 - (‖x + IK • y‖ : 𝕜) ^ 2) * IK) / 4 := by
  rw [← re_add_im ⟪x, y⟫, re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four,
    im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_four]
  push_cast
  simp only [sq, ← mul_div_right_comm, ← add_div]

/-- Polarization identity: The real inner product, in terms of the norm. -/
theorem real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (x y : F) :
    ⟪x, y⟫_ℝ = (‖x + y‖ * ‖x + y‖ - ‖x‖ * ‖x‖ - ‖y‖ * ‖y‖) / 2 :=
  re_to_real.symm.trans <|
    re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two x y

/-- Polarization identity: The real inner product, in terms of the norm. -/
theorem real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two (x y : F) :
    ⟪x, y⟫_ℝ = (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ - ‖x - y‖ * ‖x - y‖) / 2 :=
  re_to_real.symm.trans <|
    re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two x y

/-- Pythagorean theorem, if-and-only-if vector inner product form. -/
theorem norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero (x y : F) :
    ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ ↔ ⟪x, y⟫_ℝ = 0 := by
  rw [@norm_add_mul_self ℝ, add_right_cancel_iff, add_eq_left, mul_eq_zero]
  simp

/-- Pythagorean theorem, if-and-if vector inner product form using square roots. -/
theorem norm_add_eq_sqrt_iff_real_inner_eq_zero {x y : F} :
    ‖x + y‖ = √(‖x‖ * ‖x‖ + ‖y‖ * ‖y‖) ↔ ⟪x, y⟫_ℝ = 0 := by
  rw [← norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero, eq_comm, sqrt_eq_iff_mul_self_eq,
    eq_comm] <;> positivity

/-- Pythagorean theorem, vector inner product form. -/
theorem norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (x y : E) (h : ⟪x, y⟫ = 0) :
    ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ := by
  rw [@norm_add_mul_self 𝕜, add_right_cancel_iff, add_eq_left, mul_eq_zero]
  apply Or.inr
  simp only [h, zero_re]

/-- Pythagorean theorem, vector inner product form. -/
theorem norm_add_sq_eq_norm_sq_add_norm_sq_real {x y : F} (h : ⟪x, y⟫_ℝ = 0) :
    ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ :=
  (norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero x y).2 h

/-- Pythagorean theorem, subtracting vectors, if-and-only-if vector
inner product form. -/
theorem norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero (x y : F) :
    ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ ↔ ⟪x, y⟫_ℝ = 0 := by
  rw [@norm_sub_mul_self ℝ, add_right_cancel_iff, sub_eq_add_neg, add_eq_left, neg_eq_zero,
    mul_eq_zero]
  simp

/-- Pythagorean theorem, subtracting vectors, if-and-if vector inner product form using square
roots. -/
theorem norm_sub_eq_sqrt_iff_real_inner_eq_zero {x y : F} :
    ‖x - y‖ = √(‖x‖ * ‖x‖ + ‖y‖ * ‖y‖) ↔ ⟪x, y⟫_ℝ = 0 := by
  rw [← norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero, eq_comm, sqrt_eq_iff_mul_self_eq,
    eq_comm] <;> positivity

/-- Pythagorean theorem, subtracting vectors, vector inner product
form. -/
theorem norm_sub_sq_eq_norm_sq_add_norm_sq_real {x y : F} (h : ⟪x, y⟫_ℝ = 0) :
    ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ :=
  (norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero x y).2 h

/-- The sum and difference of two vectors are orthogonal if and only
if they have the same norm. -/
theorem real_inner_add_sub_eq_zero_iff (x y : F) : ⟪x + y, x - y⟫_ℝ = 0 ↔ ‖x‖ = ‖y‖ := by
  conv_rhs => rw [← mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)]
  simp only [← @inner_self_eq_norm_mul_norm ℝ, inner_add_left, inner_sub_right, real_inner_comm y x,
    sub_eq_zero, re_to_real]
  grind

/-- Given two orthogonal vectors, their sum and difference have equal norms. -/
theorem norm_sub_eq_norm_add {v w : E} (h : ⟪v, w⟫ = 0) : ‖w - v‖ = ‖w + v‖ := by
  rw [← mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)]
  simp only [h, ← @inner_self_eq_norm_mul_norm 𝕜, sub_neg_eq_add, sub_zero, map_sub, zero_re,
    zero_sub, add_zero, map_add, inner_add_right, inner_sub_left, inner_sub_right, inner_re_symm,
    zero_add]

/-- The real inner product of two vectors, divided by the product of their
norms, has absolute value at most 1. -/
theorem abs_real_inner_div_norm_mul_norm_le_one (x y : F) : |⟪x, y⟫_ℝ / (‖x‖ * ‖y‖)| ≤ 1 := by
  rw [abs_div, abs_mul, abs_norm, abs_norm]
  exact div_le_one_of_le₀ (abs_real_inner_le_norm x y) (by positivity)

/-- The inner product of a vector with a multiple of itself. -/
theorem real_inner_smul_self_left (x : F) (r : ℝ) : ⟪r • x, x⟫_ℝ = r * (‖x‖ * ‖x‖) := by
  rw [real_inner_smul_left, ← real_inner_self_eq_norm_mul_norm]

/-- The inner product of a vector with a multiple of itself. -/
theorem real_inner_smul_self_right (x : F) (r : ℝ) : ⟪x, r • x⟫_ℝ = r * (‖x‖ * ‖x‖) := by
  rw [inner_smul_right, ← real_inner_self_eq_norm_mul_norm]

/-- The inner product of two weighted sums, where the weights in each
sum add to 0, in terms of the norms of pairwise differences. -/
theorem inner_sum_smul_sum_smul_of_sum_eq_zero {ι₁ : Type*} {s₁ : Finset ι₁} {w₁ : ι₁ → ℝ}
    (v₁ : ι₁ → F) (h₁ : ∑ i ∈ s₁, w₁ i = 0) {ι₂ : Type*} {s₂ : Finset ι₂} {w₂ : ι₂ → ℝ}
    (v₂ : ι₂ → F) (h₂ : ∑ i ∈ s₂, w₂ i = 0) :
    ⟪∑ i₁ ∈ s₁, w₁ i₁ • v₁ i₁, ∑ i₂ ∈ s₂, w₂ i₂ • v₂ i₂⟫_ℝ =
      (-∑ i₁ ∈ s₁, ∑ i₂ ∈ s₂, w₁ i₁ * w₂ i₂ * (‖v₁ i₁ - v₂ i₂‖ * ‖v₁ i₁ - v₂ i₂‖)) / 2 := by
  simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
    real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two, ← div_sub_div_same,
    add_div, mul_sub_left_distrib, left_distrib, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, h₁, h₂, zero_mul,
    mul_zero, Finset.sum_const_zero, zero_add, zero_sub, Finset.mul_sum, neg_div,
    Finset.sum_div, mul_div_assoc, mul_assoc]

end Norm_Seminormed

section Norm

open scoped InnerProductSpace

variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {ι : Type*}

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- Formula for the distance between the images of two nonzero points under an inversion with center
zero. See also `EuclideanGeometry.dist_inversion_inversion` for inversions around a general
point. -/
theorem dist_div_norm_sq_smul {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) (R : ℝ) :
    dist ((R / ‖x‖) ^ 2 • x) ((R / ‖y‖) ^ 2 • y) = R ^ 2 / (‖x‖ * ‖y‖) * dist x y :=
  calc
    dist ((R / ‖x‖) ^ 2 • x) ((R / ‖y‖) ^ 2 • y) =
        √(‖(R / ‖x‖) ^ 2 • x - (R / ‖y‖) ^ 2 • y‖ ^ 2) := by
      rw [dist_eq_norm, sqrt_sq (norm_nonneg _)]
    _ = √((R ^ 2 / (‖x‖ * ‖y‖)) ^ 2 * ‖x - y‖ ^ 2) :=
      congr_arg (√·) <| by
        simp [field, sq, norm_sub_mul_self_real, norm_smul, real_inner_smul_left, inner_smul_right,
          Real.norm_of_nonneg (mul_self_nonneg _), -mul_eq_mul_left_iff]
        ring
    _ = R ^ 2 / (‖x‖ * ‖y‖) * dist x y := by
      rw [sqrt_mul, sqrt_sq, sqrt_sq, dist_eq_norm] <;> positivity

/-- The inner product of a nonzero vector with a nonzero multiple of
itself, divided by the product of their norms, has absolute value
1. -/
theorem norm_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul {x : E} {r : 𝕜} (hx : x ≠ 0)
    (hr : r ≠ 0) : ‖⟪x, r • x⟫‖ / (‖x‖ * ‖r • x‖) = 1 := by
  have hx' : ‖x‖ ≠ 0 := by simp [hx]
  have hr' : ‖r‖ ≠ 0 := by simp [hr]
  rw [inner_smul_right, norm_mul, ← inner_self_re_eq_norm, inner_self_eq_norm_mul_norm, norm_smul]
  rw [← mul_assoc, ← div_div, mul_div_cancel_right₀ _ hx', ← div_div, mul_comm,
    mul_div_cancel_right₀ _ hr', div_self hx']

/-- The inner product of a nonzero vector with a nonzero multiple of
itself, divided by the product of their norms, has absolute value
1. -/
theorem abs_real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul {x : F} {r : ℝ}
    (hx : x ≠ 0) (hr : r ≠ 0) : |⟪x, r • x⟫_ℝ| / (‖x‖ * ‖r • x‖) = 1 :=
  norm_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul hx hr

/-- The inner product of a nonzero vector with a positive multiple of
itself, divided by the product of their norms, has value 1. -/
theorem real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul {x : F} {r : ℝ} (hx : x ≠ 0)
    (hr : 0 < r) : ⟪x, r • x⟫_ℝ / (‖x‖ * ‖r • x‖) = 1 := by
  rw [real_inner_smul_self_right, norm_smul, Real.norm_eq_abs, ← mul_assoc ‖x‖, mul_comm _ |r|,
    mul_assoc, abs_of_nonneg hr.le, div_self]
  exact mul_ne_zero hr.ne' (mul_self_ne_zero.2 (norm_ne_zero_iff.2 hx))

/-- The inner product of a nonzero vector with a negative multiple of
itself, divided by the product of their norms, has value -1. -/
theorem real_inner_div_norm_mul_norm_eq_neg_one_of_ne_zero_of_neg_mul {x : F} {r : ℝ} (hx : x ≠ 0)
    (hr : r < 0) : ⟪x, r • x⟫_ℝ / (‖x‖ * ‖r • x‖) = -1 := by
  rw [real_inner_smul_self_right, norm_smul, Real.norm_eq_abs, ← mul_assoc ‖x‖, mul_comm _ |r|,
    mul_assoc, abs_of_neg hr, neg_mul, div_neg_eq_neg_div, div_self]
  exact mul_ne_zero hr.ne (mul_self_ne_zero.2 (norm_ne_zero_iff.2 hx))

variable (𝕜) in
theorem norm_inner_eq_norm_tfae (x y : E) :
    List.TFAE [‖⟪x, y⟫‖ = ‖x‖ * ‖y‖,
      x = 0 ∨ y = (⟪x, y⟫ / ⟪x, x⟫) • x,
      x = 0 ∨ ∃ r : 𝕜, y = r • x,
      x = 0 ∨ y ∈ 𝕜 ∙ x] := by
  tfae_have 1 → 2 := by
    refine fun h => or_iff_not_imp_left.2 fun hx₀ => ?_
    have : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 hx₀)
    rw [← sq_eq_sq₀, mul_pow, ← mul_right_inj' this, eq_comm, ← sub_eq_zero, ← mul_sub] at h <;>
      try positivity
    simp only [@norm_sq_eq_re_inner 𝕜] at h
    letI : InnerProductSpace.Core 𝕜 E := InnerProductSpace.toCore
    erw [← InnerProductSpace.Core.cauchy_schwarz_aux (𝕜 := 𝕜) (F := E)] at h
    rw [InnerProductSpace.Core.normSq_eq_zero, sub_eq_zero] at h
    rw [div_eq_inv_mul, mul_smul, h, inv_smul_smul₀]
    rwa [inner_self_ne_zero]
  tfae_have 2 → 3 := fun h => h.imp_right fun h' => ⟨_, h'⟩
  tfae_have 3 → 1 := by
    rintro (rfl | ⟨r, rfl⟩) <;>
    simp [inner_smul_right, norm_smul, inner_self_eq_norm_sq_to_K,
      sq, mul_left_comm]
  tfae_have 3 ↔ 4 := by simp only [Submodule.mem_span_singleton, eq_comm]
  tfae_finish

/-- If the inner product of two vectors is equal to the product of their norms, then the two vectors
are multiples of each other. One form of the equality case for Cauchy-Schwarz.
Compare `inner_eq_norm_mul_iff`, which takes the stronger hypothesis `⟪x, y⟫ = ‖x‖ * ‖y‖`. -/
theorem norm_inner_eq_norm_iff {x y : E} (hx₀ : x ≠ 0) (hy₀ : y ≠ 0) :
    ‖⟪x, y⟫‖ = ‖x‖ * ‖y‖ ↔ ∃ r : 𝕜, r ≠ 0 ∧ y = r • x :=
  calc
    ‖⟪x, y⟫‖ = ‖x‖ * ‖y‖ ↔ x = 0 ∨ ∃ r : 𝕜, y = r • x :=
      (norm_inner_eq_norm_tfae 𝕜 x y).out 0 2
    _ ↔ ∃ r : 𝕜, y = r • x := or_iff_right hx₀
    _ ↔ ∃ r : 𝕜, r ≠ 0 ∧ y = r • x :=
      ⟨fun ⟨r, h⟩ => ⟨r, fun hr₀ => hy₀ <| h.symm ▸ smul_eq_zero.2 <| Or.inl hr₀, h⟩,
        fun ⟨r, _hr₀, h⟩ => ⟨r, h⟩⟩

/-- The inner product of two vectors, divided by the product of their
norms, has absolute value 1 if and only if they are nonzero and one is
a multiple of the other. One form of equality case for Cauchy-Schwarz. -/
theorem norm_inner_div_norm_mul_norm_eq_one_iff (x y : E) :
    ‖⟪x, y⟫ / (‖x‖ * ‖y‖)‖ = 1 ↔ x ≠ 0 ∧ ∃ r : 𝕜, r ≠ 0 ∧ y = r • x := by
  constructor
  · intro h
    have hx₀ : x ≠ 0 := fun h₀ => by simp [h₀] at h
    have hy₀ : y ≠ 0 := fun h₀ => by simp [h₀] at h
    refine ⟨hx₀, (norm_inner_eq_norm_iff hx₀ hy₀).1 <| eq_of_div_eq_one ?_⟩
    simpa using h
  · rintro ⟨hx, ⟨r, ⟨hr, rfl⟩⟩⟩
    simp only [norm_div, norm_mul, norm_ofReal, abs_norm]
    exact norm_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul hx hr

/-- The inner product of two vectors, divided by the product of their
norms, has absolute value 1 if and only if they are nonzero and one is
a multiple of the other. One form of equality case for Cauchy-Schwarz. -/
theorem abs_real_inner_div_norm_mul_norm_eq_one_iff (x y : F) :
    |⟪x, y⟫_ℝ / (‖x‖ * ‖y‖)| = 1 ↔ x ≠ 0 ∧ ∃ r : ℝ, r ≠ 0 ∧ y = r • x :=
  @norm_inner_div_norm_mul_norm_eq_one_iff ℝ F _ _ _ x y

theorem inner_eq_norm_mul_iff_div {x y : E} (h₀ : x ≠ 0) :
    ⟪x, y⟫ = (‖x‖ : 𝕜) * ‖y‖ ↔ (‖y‖ / ‖x‖ : 𝕜) • x = y := by
  have h₀' := h₀
  rw [← norm_ne_zero_iff, Ne, ← @ofReal_eq_zero 𝕜] at h₀'
  constructor <;> intro h
  · have : x = 0 ∨ y = (⟪x, y⟫ / ⟪x, x⟫ : 𝕜) • x :=
      ((norm_inner_eq_norm_tfae 𝕜 x y).out 0 1).1 (by simp [h])
    rw [this.resolve_left h₀, h]
    simp [norm_smul, inner_self_ofReal_norm, mul_div_cancel_right₀ _ h₀']
  · conv_lhs => rw [← h, inner_smul_right, inner_self_eq_norm_sq_to_K]
    field_simp

/-- If the inner product of two vectors is equal to the product of their norms (i.e.,
`⟪x, y⟫ = ‖x‖ * ‖y‖`), then the two vectors are nonnegative real multiples of each other. One form
of the equality case for Cauchy-Schwarz.
Compare `norm_inner_eq_norm_iff`, which takes the weaker hypothesis `abs ⟪x, y⟫ = ‖x‖ * ‖y‖`. -/
theorem inner_eq_norm_mul_iff {x y : E} :
    ⟪x, y⟫ = (‖x‖ : 𝕜) * ‖y‖ ↔ (‖y‖ : 𝕜) • x = (‖x‖ : 𝕜) • y := by
  rcases eq_or_ne x 0 with (rfl | h₀)
  · simp
  · rw [inner_eq_norm_mul_iff_div h₀, div_eq_inv_mul, mul_smul, inv_smul_eq_iff₀]
    rwa [Ne, ofReal_eq_zero, norm_eq_zero]

/-- If the inner product of two vectors is equal to the product of their norms (i.e.,
`⟪x, y⟫ = ‖x‖ * ‖y‖`), then the two vectors are nonnegative real multiples of each other. One form
of the equality case for Cauchy-Schwarz.
Compare `norm_inner_eq_norm_iff`, which takes the weaker hypothesis `abs ⟪x, y⟫ = ‖x‖ * ‖y‖`. -/
theorem inner_eq_norm_mul_iff_real {x y : F} : ⟪x, y⟫_ℝ = ‖x‖ * ‖y‖ ↔ ‖y‖ • x = ‖x‖ • y :=
  inner_eq_norm_mul_iff

/-- The inner product of two vectors, divided by the product of their
norms, has value 1 if and only if they are nonzero and one is
a positive multiple of the other. -/
theorem real_inner_div_norm_mul_norm_eq_one_iff (x y : F) :
    ⟪x, y⟫_ℝ / (‖x‖ * ‖y‖) = 1 ↔ x ≠ 0 ∧ ∃ r : ℝ, 0 < r ∧ y = r • x := by
  constructor
  · intro h
    have hx₀ : x ≠ 0 := fun h₀ => by simp [h₀] at h
    have hy₀ : y ≠ 0 := fun h₀ => by simp [h₀] at h
    refine ⟨hx₀, ‖y‖ / ‖x‖, div_pos (norm_pos_iff.2 hy₀) (norm_pos_iff.2 hx₀), ?_⟩
    exact ((inner_eq_norm_mul_iff_div hx₀).1 (eq_of_div_eq_one h)).symm
  · rintro ⟨hx, ⟨r, ⟨hr, rfl⟩⟩⟩
    exact real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul hx hr

/-- The inner product of two vectors, divided by the product of their
norms, has value -1 if and only if they are nonzero and one is
a negative multiple of the other. -/
theorem real_inner_div_norm_mul_norm_eq_neg_one_iff (x y : F) :
    ⟪x, y⟫_ℝ / (‖x‖ * ‖y‖) = -1 ↔ x ≠ 0 ∧ ∃ r : ℝ, r < 0 ∧ y = r • x := by
  rw [← neg_eq_iff_eq_neg, ← neg_div, ← inner_neg_right, ← norm_neg y,
    real_inner_div_norm_mul_norm_eq_one_iff, (@neg_surjective ℝ _).exists]
  refine Iff.rfl.and (exists_congr fun r => ?_)
  rw [neg_pos, neg_smul, neg_inj]

/-- If the inner product of two unit vectors is `1`, then the two vectors are equal. One form of
the equality case for Cauchy-Schwarz. -/
theorem inner_eq_one_iff_of_norm_one {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ⟪x, y⟫ = 1 ↔ x = y := by
  convert inner_eq_norm_mul_iff (𝕜 := 𝕜) (E := E) using 2 <;> simp [hx, hy]

/-- If the inner product of two unit vectors is `-1`, then the two vectors are negations of each
other. -/
theorem inner_eq_neg_one_iff_of_norm_one {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ⟪x, y⟫ = -1 ↔ x = -y := by
  rw [← neg_eq_iff_eq_neg, ← inner_neg_right, inner_eq_one_iff_of_norm_one hx (norm_neg y ▸ hy)]

/-- The inner product of two unit vectors is less than or equal to `1`. -/
theorem real_inner_le_one_of_norm_one {x y : F} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : ⟪x, y⟫_ℝ ≤ 1 := by
  simpa [hx, hy] using real_inner_le_norm x y

/-- The inner product of two unit vectors is greater than or equal to `-1`. -/
theorem neg_one_le_real_inner_of_norm_one {x y : F} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    -1 ≤ ⟪x, y⟫_ℝ := by
  simpa [hx, hy] using neg_le_of_abs_le (abs_real_inner_le_norm x y)

@[simp]
theorem inner_self_eq_one_of_norm_one {x : E} (hx : ‖x‖ = 1) : ⟪x, x⟫_𝕜 = 1 :=
  (inner_eq_one_iff_of_norm_one hx hx).mpr rfl

theorem inner_lt_norm_mul_iff_real {x y : F} : ⟪x, y⟫_ℝ < ‖x‖ * ‖y‖ ↔ ‖y‖ • x ≠ ‖x‖ • y :=
  calc
    ⟪x, y⟫_ℝ < ‖x‖ * ‖y‖ ↔ ⟪x, y⟫_ℝ ≠ ‖x‖ * ‖y‖ :=
      ⟨ne_of_lt, lt_of_le_of_ne (real_inner_le_norm _ _)⟩
    _ ↔ ‖y‖ • x ≠ ‖x‖ • y := not_congr inner_eq_norm_mul_iff_real

/-- If the inner product of two unit vectors is strictly less than `1`, then the two vectors are
distinct. One form of the equality case for Cauchy-Schwarz. -/
theorem inner_lt_one_iff_real_of_norm_one {x y : F} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ⟪x, y⟫_ℝ < 1 ↔ x ≠ y := by convert inner_lt_norm_mul_iff_real (F := F) <;> simp [hx, hy]

/-- The sphere of radius `r = ‖y‖` is tangent to the plane `⟪x, y⟫ = ‖y‖ ^ 2` at `x = y`. -/
theorem eq_of_norm_le_re_inner_eq_norm_sq {x y : E} (hle : ‖x‖ ≤ ‖y‖) (h : re ⟪x, y⟫ = ‖y‖ ^ 2) :
    x = y := by
  suffices H : re ⟪x - y, x - y⟫ ≤ 0 by rwa [re_inner_self_nonpos, sub_eq_zero] at H
  have H₁ : ‖x‖ ^ 2 ≤ ‖y‖ ^ 2 := by gcongr
  have H₂ : re ⟪y, x⟫ = ‖y‖ ^ 2 := by rwa [← inner_conj_symm, conj_re]
  simpa [inner_sub_left, inner_sub_right, ← norm_sq_eq_re_inner, h, H₂] using H₁

/-- Equality is achieved in the triangle inequality iff the two vectors are collinear. -/
theorem norm_add_eq_iff_real {x y : F} : ‖x + y‖ = ‖x‖ + ‖y‖ ↔ ‖y‖ • x = ‖x‖ • y := by
  rw [← pow_left_inj₀ (norm_nonneg _) (Left.add_nonneg (norm_nonneg _) (norm_nonneg _)) two_ne_zero,
    norm_add_sq (𝕜 := ℝ), add_pow_two, add_left_inj, add_right_inj, re_to_real, mul_assoc,
    mul_right_inj' two_ne_zero, ← inner_eq_norm_mul_iff_real]

end Norm

section RCLike

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- A field `𝕜` satisfying `RCLike` is itself a `𝕜`-inner product space. -/
instance RCLike.innerProductSpace : InnerProductSpace 𝕜 𝕜 where
  inner x y := y * conj x
  norm_sq_eq_re_inner x := by simp only [mul_conj, ← ofReal_pow, ofReal_re]
  conj_inner_symm x y := by simp only [mul_comm, map_mul, starRingEnd_self_apply]
  add_left x y z := by simp only [mul_add, map_add]
  smul_left x y z := by simp only [mul_comm (conj z), mul_assoc, smul_eq_mul, map_mul]

@[simp]
theorem RCLike.inner_apply (x y : 𝕜) : ⟪x, y⟫ = y * conj x :=
  rfl

/-- A version of `RCLike.inner_apply` that swaps the order of multiplication. -/
theorem RCLike.inner_apply' (x y : 𝕜) : ⟪x, y⟫ = conj x * y := mul_comm _ _

end RCLike

section RCLikeToReal

open scoped InnerProductSpace

variable {G : Type*}
variable (𝕜 E)
variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- A general inner product implies a real inner product. This is not registered as an instance
since `𝕜` does not appear in the return type `Inner ℝ E`. -/
def Inner.rclikeToReal : Inner ℝ E where inner x y := re ⟪x, y⟫

/-- A general inner product space structure implies a real inner product structure.

This is not registered as an instance since
* `𝕜` does not appear in the return type `InnerProductSpace ℝ E`,
* It is likely to create instance diamonds, as it builds upon the diamond-prone
  `NormedSpace.restrictScalars`.

However, it can be used in a proof to obtain a real inner product space structure from a given
`𝕜`-inner product space structure. -/
-- See note [reducible non-instances]
abbrev InnerProductSpace.rclikeToReal : InnerProductSpace ℝ E :=
  { Inner.rclikeToReal 𝕜 E,
    NormedSpace.restrictScalars ℝ 𝕜 E with
    norm_sq_eq_re_inner := norm_sq_eq_re_inner
    conj_inner_symm := fun _ _ => inner_re_symm _ _
    add_left := fun x y z => by
      simp only [Inner.rclikeToReal, inner_add_left, map_add]
    smul_left := fun x y r => by
      letI := NormedSpace.restrictScalars ℝ 𝕜 E
      have : r • x = (r : 𝕜) • x := rfl
      simp only [Inner.rclikeToReal, this, conj_trivial, inner_smul_left, conj_ofReal,
        re_ofReal_mul] }

variable {E}

theorem real_inner_eq_re_inner (x y : E) :
    (Inner.rclikeToReal 𝕜 E).inner x y = re ⟪x, y⟫ :=
  rfl

theorem real_inner_I_smul_self (x : E) :
    (Inner.rclikeToReal 𝕜 E).inner x ((I : 𝕜) • x) = 0 := by
  simp [real_inner_eq_re_inner 𝕜, inner_smul_right]

/-- A complex inner product implies a real inner product. This cannot be an instance since it
creates a diamond with `PiLp.innerProductSpace` because `re (sum i, ⟪x i, y i⟫)` and
`sum i, re ⟪x i, y i⟫` are not defeq. -/
def InnerProductSpace.complexToReal [SeminormedAddCommGroup G] [InnerProductSpace ℂ G] :
    InnerProductSpace ℝ G :=
  InnerProductSpace.rclikeToReal ℂ G

instance : InnerProductSpace ℝ ℂ := InnerProductSpace.complexToReal

@[simp]
protected theorem Complex.inner (w z : ℂ) : ⟪w, z⟫_ℝ = (z * conj w).re :=
  rfl

end RCLikeToReal

/-- An `RCLike` field is a real inner product space. -/
noncomputable instance RCLike.toInnerProductSpaceReal : InnerProductSpace ℝ 𝕜 where
  __ := Inner.rclikeToReal 𝕜 𝕜
  norm_sq_eq_re_inner := norm_sq_eq_re_inner
  conj_inner_symm x y := inner_re_symm ..
  add_left x y z :=
    show re (_ * _) = re (_ * _) + re (_ * _) by simp only [map_add, mul_re, conj_re, conj_im]; ring
  smul_left x y r :=
    show re (_ * _) = _ * re (_ * _) by
      simp only [mul_re, conj_re, conj_im, conj_trivial, smul_re, smul_im]; ring

-- The instance above does not create diamonds for concrete `𝕜`:
example : (innerProductSpace : InnerProductSpace ℝ ℝ) = RCLike.toInnerProductSpaceReal := rfl
example :
    (instInnerProductSpaceRealComplex : InnerProductSpace ℝ ℂ) = RCLike.toInnerProductSpaceReal :=
  rfl
