/-
Copyright (c) 2024 Mitchell Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Lee
-/
import Mathlib.LinearAlgebra.Reflection
import Mathlib.GroupTheory.Coxeter.Matrix
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Polyrith

/-!
# The standard geometric representation

Throughout this file, `B` is a type and `M : CoxeterMatrix B` is a Coxeter matrix.
`cs : CoxeterSystem M W` is a Coxeter system; that is, `W` is a group, and `cs` holds the data
of a group isomorphism `W ≃* M.group`, where `M.group` refers to the quotient of the free group on
`B` by the Coxeter relations given by the matrix `M`. See `Mathlib/GroupTheory/Coxeter/Basic.lean`
for more details.

Let $V$ be the free $\mathbb{R}$ vector space over `B` and let $\{\alpha_i\}$ be the standard basis
of $V$. We define a the *standard bilinear form* on $V$ (`CoxeterMatrix.standardBilinForm`) by
$$\langle \alpha_i, \alpha_{i'}\rangle = -\cos (\pi / M_{i, i'}),$$
where $M$ is the Coxeter matrix of $W$. This is positive definite if and only if $W$ is a finite
group, although we do not prove that in this file.

## Main definitions

* `CoxeterMatrix.standardBilinForm`

## References

* [A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*](bjorner2005)

-/

noncomputable section

open List Real LinearMap

namespace CoxeterMatrix

variable {B : Type*}
variable (M : CoxeterMatrix B)

local notation "V" => B →₀ ℝ

/-- The simple root at index `i`. That is, the standard basis vector of `B →₀ ℝ` at index `i`. -/
def simpleRoot (i : B) : V := Finsupp.single i 1

local prefix:100 "α" => simpleRoot

/-- The standard bilinear form on `B →₀ ℝ`. Given by `⟪αᵢ, αⱼ⟫ = -cos (π / Mᵢⱼ)`
for `i j : B`, where {αᵢ} is the standard basis of `B →₀ ℝ` and `M` is the Coxeter matrix.
This is positive definite if and only if the associated Coxeter group is finite. -/
def standardBilinForm : LinearMap.BilinForm ℝ V :=
  (Finsupp.lift (V →ₗ[ℝ] ℝ) ℝ B)
    (fun i ↦ ((Finsupp.lift ℝ ℝ B) (fun i' ↦ -cos (π / M i i'))))

local notation:max "⟪"  a  ","  b  "⟫" => M.standardBilinForm a b

theorem standardBilinForm_simpleRoot_self (i : B) :
    ⟪α i, α i⟫ = 1 := by simp [standardBilinForm, simpleRoot, M.diagonal i]

theorem standardBilinForm_simpleRoot_simpleRoot (i i' : B) :
    ⟪α i, α i'⟫ = - cos (π / M i i') := by simp [standardBilinForm, simpleRoot]

theorem isSymm_standardBilinForm : LinearMap.IsSymm (standardBilinForm M) := by
  rw [LinearMap.isSymm_iff_eq_flip]
  ext i i'
  simp [standardBilinForm, M.symmetric i i']

theorem standardBilinForm_comm (v v' : V) : ⟪v, v'⟫ = ⟪v', v⟫ := M.isSymm_standardBilinForm.eq v v'

/-- The orthogonal reflection in the vector `v` under the standard bilinear form.
-/
def orthoReflection {v : V} (hv : ⟪v, v⟫ = 1) : V →ₗ[ℝ] V :=
  Module.reflection (show ((2 : ℝ) • (standardBilinForm M v)) v = 2 by
      rw [LinearMap.smul_apply, hv, smul_eq_mul, mul_one])

local prefix:100 "r" => M.orthoReflection

attribute [local simp] Module.reflection
attribute [local simp] Module.preReflection

theorem orthoReflection_apply {v : V} (hv : ⟪v, v⟫ = 1) (w : V) :
    (r hv) w = w - (2 * ⟪v, w⟫) • v :=
  Module.reflection_apply _ _

@[simp]
theorem orthoReflection_apply_self {v : V} (hv : ⟪v, v⟫ = 1) : (r hv) v = -v :=
  Module.reflection_apply_self _

theorem orthoReflection_sq {v : V} (hv : ⟪v, v⟫ = 1) :
    (r hv) * (r hv) = LinearMap.id := by
  apply LinearMap.ext
  exact Module.involutive_reflection (show ((2 : ℝ) • (standardBilinForm M v)) v = 2 by
    rw [LinearMap.smul_apply, hv]; norm_num)

theorem orthoReflection_eq_orthoReflection_iff {v v' : V} (hv : ⟪v, v⟫ = 1) (hv' : ⟪v', v'⟫ = 1) :
    r hv = r hv' ↔ ∃ μ : ℝ, v' = μ • v := by
  constructor
  · intro h
    use ⟪v, v'⟫
    apply_fun (· v') at h
    rw [M.orthoReflection_apply_self hv', M.orthoReflection_apply] at h
    apply_fun (v' + ·) at h
    rw [add_right_neg, add_sub, ← two_smul ℝ v', sub_eq_zero] at h
    apply_fun (((1 : ℝ) / 2) • ·) at h
    rw [smul_smul, smul_smul, ← mul_assoc] at h
    norm_num at h
    exact h
  · rintro ⟨μ, rfl⟩
    have hμ : μ * μ = 1 := by
      simpa only [map_smul, LinearMap.smul_apply, smul_eq_mul, hv, mul_one] using hv'
    apply LinearMap.ext
    intro w
    simp only [orthoReflection_apply, map_smul, smul_apply, smul_eq_mul, mul_comm μ, smul_smul,
      mul_assoc, hμ, mul_one]

@[simp]
theorem standardBilinForm_orthoReflection_apply {v : V} {hv : ⟪v, v⟫ = 1} (w w' : V) :
    ⟪(r hv) w, (r hv) w'⟫ = ⟪w, w'⟫ := by
  simp only [orthoReflection_apply, map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul,
    ← M.isSymm_standardBilinForm.eq v w, RingHom.id_apply, hv]
  ring

/-- Any orthogonal reflection is orthogonal with respect to the standard bilinear form. -/
theorem standardBilinForm_compl₁₂_orthoReflection {v : V} (hv : ⟪v, v⟫ = 1) :
    LinearMap.compl₁₂ M.standardBilinForm (r hv) (r hv) = M.standardBilinForm :=
  LinearMap.ext fun w ↦ LinearMap.ext fun w' ↦ M.standardBilinForm_orthoReflection_apply w w'

/-- The orthogonal reflection in the standard basis vector `αᵢ` under the standard bilinear form. -/
def simpleOrthoReflection (i : B) := r (M.standardBilinForm_simpleRoot_self i)

local prefix:100 "σ" => M.simpleOrthoReflection

theorem simpleOrthoReflection_simpleRoot (i i' : B) :
    (σ i) (α i') = α i' + (2 * cos (π / M i i')) • α i := by
  dsimp [simpleOrthoReflection, orthoReflection]
  rw [standardBilinForm_simpleRoot_simpleRoot, sub_eq_add_neg, ← neg_smul]
  ring_nf

@[simp] theorem simpleOrthoReflection_simpleRoot_self (i : B) : (σ i) (α i) = -α i := by
  simp [simpleOrthoReflection_simpleRoot, M.diagonal i, two_smul]

private lemma sin_pi_div_m_ne_zero {m : ℕ} (hm : 1 < m) : sin (π / m) ≠ 0 := by
  have h₀ : 0 < π / m := div_pos pi_pos (zero_lt_one.trans (by exact_mod_cast hm))
  have h₁ : π / m < π := div_lt_self pi_pos (by exact_mod_cast hm)
  exact ne_of_gt (sin_pos_of_pos_of_lt_pi h₀ h₁)

theorem orthoReflection_mul_orthoReflection_pow_apply {v v' : V} {m : ℕ} (k : ℕ) (hm : 1 < m)
    (hv : ⟪v, v⟫ = 1) (hv' : ⟪v', v'⟫ = 1) (hvv' : ⟪v, v'⟫ = - cos (π / m)) :
    ((r hv * r hv') ^ k) v =
      (sin ((2 * k + 1) * (π / m)) / sin (π / m)) • v +
        (sin (2 * k * (π / m)) / sin (π / m)) • v' := by
  induction' k with k ih
  · simp [div_self (sin_pi_div_m_ne_zero hm)]
  · -- Apply inductive hypothesis.
    letI _inst : AddCommMonoid V := Finsupp.instAddCommMonoid
    rw [pow_succ', LinearMap.mul_apply, ih, LinearMap.mul_apply]
    -- Expand everything out.
    simp only [map_add, map_smul, orthoReflection_apply, smul_sub, smul_smul, hv', map_sub, hv]
    -- Rewrite using - cos (π / m) = ⟪v, v'⟫.
    rw [M.standardBilinForm_comm v' v, hvv']
    clear hv hv' hvv' ih
    -- Sort the terms and write the entire expression as a • v + b • v'.
    simp only [sub_eq_add_neg, neg_add, ← neg_smul, smul_eq_mul]
    have h₁ : ∀ a b : ℝ, a • v + b • v = (a + b) • v :=
      fun _ _ ↦ (add_smul _ _ _).symm
    have h₂ : ∀ a b : ℝ, a • v' + b • v' = (a + b) • v' :=
      fun _ _ ↦ (add_smul _ _ _).symm
    have h₃ : ∀ a b : ℝ, a • v' + b • v = b • v + a • v' :=
      fun _ _ ↦ add_comm _ _
    have h₄ : ∀ a b c : ℝ, a • v + b • v' + c • v = (a + c) • v + b • v' :=
      fun a b c ↦ (add_right_comm _ _ _).trans (congrArg (· + _) (h₁ a c))
    have h₅ : ∀ a b c : ℝ, a • v + b • v' + c • v' = a • v + (b + c) • v' :=
      fun a b c ↦ (add_assoc _ _ _).trans (congrArg (_ + ·) (h₂ b c))
    simp only [← add_assoc, h₁, h₂, h₃, h₄, h₅]
    clear h₁ h₂ h₃ h₄ h₅
    -- Simplify using the sine and cosine angle addition formula.
    have h₆ : ((2 * (Nat.succ k) + 1) * (π / m)) = 2 * k * (π / m) + π / m + π / m + π / m := by
      rw [Nat.succ_eq_add_one]
      push_cast
      ring
    have h₇ : ((2 * (Nat.succ k)) * (π / m)) = 2 * k * (π / m) + π / m + π / m := by
      rw [Nat.succ_eq_add_one]
      push_cast
      ring
    have h₈ : ((2 * k + 1) * (π / m)) = 2 * k * (π / m) + π / m := by ring
    simp only [h₆, h₇, h₈, sin_add, cos_add]
    clear h₆ h₇ h₈
    -- Now equate the coefficients of `v` and `v'`.
    congr
    · field_simp [sin_pi_div_m_ne_zero hm]
      linear_combination
        (3 * sin (2 * k * π / m) * cos (π / m) + cos (2 * k * π / m) * sin (π / m)) *
          sin_sq_add_cos_sq (π / m)
    · field_simp [sin_pi_div_m_ne_zero hm]
      linear_combination sin (2 * k * π / m) * sin_sq_add_cos_sq (π / m)

private lemma orthoReflection_mul_orthoReflection_pow_order_apply_v {v v' : V} {m : ℕ} (hm : 1 < m)
    (hv : ⟪v, v⟫ = 1) (hv' : ⟪v', v'⟫ = 1) (hvv' : ⟪v, v'⟫ = -cos (π / m)) :
    (((r hv) * (r hv')) ^ m) v = v := by
  rw [M.orthoReflection_mul_orthoReflection_pow_apply m hm hv hv' hvv']
  rw [add_mul, mul_assoc 2, mul_div_cancel₀ _ (by positivity)]
  simp [add_comm, sin_add_two_pi, sin_two_pi, div_self (sin_pi_div_m_ne_zero hm)]

private lemma orthoReflection_mul_orthoReflection_pow_order_apply_v' {v v' : V} {m : ℕ} (hm : 1 < m)
    (hv : ⟪v, v⟫ = 1) (hv' : ⟪v', v'⟫ = 1) (hvv' : ⟪v, v'⟫ = -cos (π / m)) :
    (((r hv) * (r hv')) ^ m) v' = v' := let a := r hv; let b := r hv'; calc
  ((a * b) ^ m) v'
  _ = (b * b * (a * b) ^ m) v'         := by simp [M.orthoReflection_sq hv']
  _ = (b * (b * (a * b) ^ m)) v'       := by rw [mul_assoc]
  _ = (b * ((b * a) ^ m * b)) v'       := by
    congr 2
    exact (SemiconjBy.eq (SemiconjBy.pow_right (by unfold SemiconjBy; group) m))
  _ = (b * (b * a) ^ m * b) v'         := by rw [mul_assoc]
  _ = (b * (b * a) ^ m) (b v')         := LinearMap.mul_apply _ _ _
  _ = (b * (b * a) ^ m) (-v')          := congrArg _ (M.orthoReflection_apply_self hv')
  _ = -((b * (b * a) ^ m) v')          := map_neg _ _
  _ = -(b (((b * a) ^ m) v'))          := congrArg _ (LinearMap.mul_apply _ _ _)
  _ = -(b v')                          := by
    congr
    apply M.orthoReflection_mul_orthoReflection_pow_order_apply_v hm hv' hv
    rwa [← M.standardBilinForm_comm v v']
  _ = -(-v')                           := congrArg _ (M.orthoReflection_apply_self hv')
  _ = v'                               := neg_neg v'

private lemma can_decomp_into_parallel_and_orthogonal {v v' : V} (w : V) {m : ℕ}
    (hv : ⟪v, v⟫ = 1) (hv' : ⟪v', v'⟫ = 1) (hvv' : ⟪v, v'⟫ = -cos (π / m)) (hm : m > 1) :
    ∃ (μ₁ μ₂ : ℝ) (w' : V), w = w' + μ₁ • v + μ₂ • v' ∧ ⟪v, w'⟫ = 0 ∧ ⟪v', w'⟫ = 0 := by
  let μ₁ := (1 / (sin (π / m)) ^ 2) * (⟪v, w⟫ + cos (π / m) * ⟪v', w⟫)
  let μ₂ := (1 / (sin (π / m)) ^ 2) * (⟪v', w⟫ + cos (π / m) * ⟪v, w⟫)
  use μ₁, μ₂, w - μ₁ • v - μ₂ • v', by abel
  -- Expand everything out.
  simp only [mul_add, LinearMap.map_sub, LinearMap.map_add, LinearMap.map_smul, smul_eq_mul,
    μ₁, μ₂]
  -- Use known values of bilinear form.
  rw [(by rw [← M.isSymm_standardBilinForm.eq v' v]; simp : ⟪v', v⟫ = ⟪v, v'⟫)]
  simp only [hv, hv', hvv']
  field_simp [sin_pi_div_m_ne_zero hm]
  ring_nf
  constructor
  all_goals
    rw [Real.sin_sq]
    ring

lemma orthoReflection_apply_eq_self_of_orthogonal
    {v : V} (hv : ⟪v, v⟫ = 1) (w : V) (hvw : ⟪v, w⟫ = 0) :
    (r hv) w = w := by
  simp [orthoReflection_apply, hvw]

private lemma fixed_of_orthogonal {v v' : V} (w : V) {m : ℕ}
    (hv : ⟪v, v⟫ = 1) (hv' : ⟪v', v'⟫ = 1) (hvw : ⟪v, w⟫ = 0) (hv'w : ⟪v', w⟫ = 0) :
    (((r hv) * (r hv')) ^ m) w = w := by
  induction' m with m ih
  · simp
  · rw [pow_succ', LinearMap.mul_apply, ih, LinearMap.mul_apply]
    simp [M.orthoReflection_apply_eq_self_of_orthogonal hv w hvw,
      M.orthoReflection_apply_eq_self_of_orthogonal hv' w hv'w]

private lemma orthoReflection_mul_orthoReflection_pow_order {v v' : V} {m : ℕ}
    (hv : ⟪v, v⟫ = 1) (hv' : ⟪v', v'⟫ = 1) (hvv' : ⟪v, v'⟫ = -cos (π / m)) (hm : m ≠ 1) :
    ((r hv) * (r hv')) ^ m = 1 := by
  rcases Nat.lt_or_gt_of_ne hm with mlt | mgt
  · simp [Nat.lt_one_iff.mp mlt]
  · apply LinearMap.ext
    intro w
    obtain ⟨μ₁, μ₂, w', rfl, h₁, h₂⟩ := M.can_decomp_into_parallel_and_orthogonal w hv hv' hvv' mgt
    simp only [LinearMap.map_add, LinearMap.map_smul, LinearMap.one_apply]
    congr
    · exact M.fixed_of_orthogonal w' hv hv' h₁ h₂
    · exact M.orthoReflection_mul_orthoReflection_pow_order_apply_v mgt hv hv' hvv'
    · exact M.orthoReflection_mul_orthoReflection_pow_order_apply_v' mgt hv hv' hvv'

end CoxeterMatrix
