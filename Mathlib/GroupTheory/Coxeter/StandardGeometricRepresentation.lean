/-
Copyright (c) 2024 Mitchell Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Lee, Johan Commelin
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
def orthoReflection (v : V) : V ≃ₗ[ℝ] V :=
  if hv : ⟪v, v⟫ = 1
  then Module.reflection (f := ((2 : ℝ) • (standardBilinForm M v))) (x := v) <| by
        rw [LinearMap.smul_apply, hv, smul_eq_mul, mul_one]
  else LinearEquiv.neg _

local prefix:100 "r" => M.orthoReflection

attribute [local simp] Module.reflection
attribute [local simp] Module.preReflection

theorem orthoReflection_apply {v : V} (hv : ⟪v, v⟫ = 1) (w : V) :
    (r v) w = w - (2 * ⟪v, w⟫) • v := by
  rw [orthoReflection, dif_pos hv, Module.reflection_apply, LinearMap.smul_apply, smul_eq_mul]

@[simp]
theorem orthoReflection_apply_self (v : V) : (r v) v = -v := by
  by_cases hv : ⟪v, v⟫ = 1
  · rw [orthoReflection, dif_pos hv, Module.reflection_apply_self]
  · rw [orthoReflection, dif_neg hv, LinearEquiv.neg_apply]

theorem involutive_orthoReflection (v : V) :
    Function.Involutive (r v) := by
  by_cases hv : ⟪v, v⟫ = 1
  · rw [orthoReflection, dif_pos hv]
    exact Module.involutive_reflection (show ((2 : ℝ) • (standardBilinForm M v)) v = 2 by
      rw [LinearMap.smul_apply, hv]; norm_num)
  · rw [orthoReflection, dif_neg hv]
    intro x
    simp

@[simp]
theorem orthoReflection_sq (v : V) :
    (r v) * (r v) = LinearEquiv.refl _ _ := by
  apply LinearEquiv.ext
  apply involutive_orthoReflection

theorem orthoReflection_eq_orthoReflection_iff {v v' : V} (hv : ⟪v, v⟫ = 1) (hv' : ⟪v', v'⟫ = 1) :
    r v = r v' ↔ ∃ μ : ℝ, v' = μ • v := by
  constructor
  · intro h
    use ⟪v, v'⟫
    apply_fun (· v') at h
    rw [M.orthoReflection_apply_self v', M.orthoReflection_apply hv] at h
    apply_fun (v' + ·) at h
    rw [add_right_neg, add_sub, ← two_smul ℝ v', sub_eq_zero] at h
    apply_fun (((1 : ℝ) / 2) • ·) at h
    rw [smul_smul, smul_smul, ← mul_assoc] at h
    norm_num at h
    exact h
  · rintro ⟨μ, rfl⟩
    have hμ : μ * μ = 1 := by
      simpa only [map_smul, LinearMap.smul_apply, smul_eq_mul, hv, mul_one] using hv'
    apply LinearEquiv.ext
    intro w
    simp only [hv, orthoReflection_apply, map_smul, smul_apply, smul_eq_mul, mul_comm μ, mul_assoc,
      hμ, mul_one, smul_smul]

@[simp]
theorem standardBilinForm_orthoReflection_apply (v : V) (w w' : V) :
    ⟪(r v) w, (r v) w'⟫ = ⟪w, w'⟫ := by
  by_cases hv : ⟪v, v⟫ = 1
  · simp only [orthoReflection_apply, map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul,
      ← M.isSymm_standardBilinForm.eq v w, RingHom.id_apply, hv]
    ring
  · simp only [orthoReflection, dif_neg hv, LinearEquiv.neg_apply, map_neg, neg_apply, neg_neg]

/-- Any orthogonal reflection is orthogonal with respect to the standard bilinear form. -/
theorem standardBilinForm_compl₁₂_orthoReflection (v : V) :
    LinearMap.compl₁₂ M.standardBilinForm (r v) (r v) = M.standardBilinForm :=
  LinearMap.ext fun w ↦ LinearMap.ext fun w' ↦ M.standardBilinForm_orthoReflection_apply v w w'

/-- The orthogonal reflection in the standard basis vector `αᵢ` under the standard bilinear form. -/
def simpleOrthoReflection (i : B) := r (α i)

local prefix:100 "σ" => M.simpleOrthoReflection

theorem simpleOrthoReflection_simpleRoot (i i' : B) :
    (σ i) (α i') = α i' + (2 * cos (π / M i i')) • α i := by
  simp [simpleOrthoReflection, orthoReflection_apply, standardBilinForm_simpleRoot_self]
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
    ((r v * r v') ^ k) v =
      (sin ((2 * k + 1) * (π / m)) / sin (π / m)) • v +
        (sin (2 * k * (π / m)) / sin (π / m)) • v' := by
  induction' k with k ih
  · simp [div_self (sin_pi_div_m_ne_zero hm)]
  · -- Apply inductive hypothesis.
    letI _inst : AddCommMonoid V := Finsupp.instAddCommMonoid
    rw [pow_succ', LinearEquiv.mul_apply, ih, LinearEquiv.mul_apply]
    -- Expand everything out.
    simp only [map_add, map_smul, orthoReflection_apply, smul_sub, smul_smul, hv', map_sub, hv]
    -- Rewrite using - cos (π / m) = ⟪v, v'⟫.
    rw [M.standardBilinForm_comm v' v, hvv']
    clear hv hv' hvv' ih
    -- Sort the terms and write the entire expression as a • v + b • v'.
    simp only [sub_eq_add_neg, neg_add, ← neg_smul, smul_eq_mul, ← add_assoc]
    simp only [← add_smul, add_comm (_ • v') (_ • v), add_right_comm _ (_ • v') (_ • v),
      add_assoc (_ • v) (_ • v') (_ • v')]
    -- Simplify using the sine and cosine angle addition formula.
    push_cast
    simp only [add_mul, mul_add, one_mul, ← add_assoc, two_mul, sin_add, cos_add]
    generalize hπm : π / m = πm
    have nz : πm.sin ≠ 0 := by simpa only [← hπm] using sin_pi_div_m_ne_zero hm
    -- Now equate the coefficients of `v` and `v'`.
    congr
    · field_simp [nz]
      linear_combination
        (6 * (↑k * πm).sin * (↑k * πm).cos * πm.cos * πm.sin ^ 7 -
              (↑k * πm).sin ^ 2 * πm.sin ^ 8 + (↑k * πm).cos ^ 2 * πm.sin ^ 8) *
          (sin_sq_add_cos_sq πm)
    · field_simp [nz]
      linear_combination 2 * (↑k * πm).sin * (↑k * πm).cos * πm.sin ^ 4 * (sin_sq_add_cos_sq πm)

private lemma orthoReflection_mul_orthoReflection_pow_order_apply_v {v v' : V} {m : ℕ} (hm : 1 < m)
    (hv : ⟪v, v⟫ = 1) (hv' : ⟪v', v'⟫ = 1) (hvv' : ⟪v, v'⟫ = -cos (π / m)) :
    (((r v) * (r v')) ^ m) v = v := by
  rw [M.orthoReflection_mul_orthoReflection_pow_apply m hm hv hv' hvv',
    add_mul, mul_assoc 2, mul_div_cancel₀ _ (by positivity)]
  simp [add_comm, sin_add_two_pi, sin_two_pi, div_self (sin_pi_div_m_ne_zero hm)]

private lemma orthoReflection_mul_orthoReflection_pow_order_apply_v' {v v' : V} {m : ℕ} (hm : 1 < m)
    (hv : ⟪v, v⟫ = 1) (hv' : ⟪v', v'⟫ = 1) (hvv' : ⟪v, v'⟫ = -cos (π / m)) :
    (((r v) * (r v')) ^ m) v' = v' := by
  let a := r v; let b := r v';
  have h₁ : SemiconjBy b (a * b) (b * a) := by simp [SemiconjBy, mul_assoc]
  have h₂ : ((b * a) ^ m) v' = v' := by
    rw [M.orthoReflection_mul_orthoReflection_pow_order_apply_v hm hv' hv]
    rwa [← M.standardBilinForm_comm v v']
  calc
  ((a * b) ^ m) v'
  _ = (b * b * (a * b) ^ m) v' := by simp [M.orthoReflection_sq v']
  _ = (b * (b * a) ^ m * b) v' := by simp [(h₁.pow_right m).eq, mul_assoc]
  _ = v'                       := by simp [h₂, M.orthoReflection_apply_self v']

private lemma can_decomp_into_parallel_and_orthogonal {v v' : V} (w : V) {m : ℕ}
    (hv : ⟪v, v⟫ = 1) (hv' : ⟪v', v'⟫ = 1) (hvv' : ⟪v, v'⟫ = -cos (π / m)) (hm : m > 1) :
    ∃ (μ₁ μ₂ : ℝ) (w' : V), w = w' + μ₁ • v + μ₂ • v' ∧ ⟪v, w'⟫ = 0 ∧ ⟪v', w'⟫ = 0 := by
  let μ₁ := (1 / (sin (π / m)) ^ 2) * (⟪v, w⟫ + cos (π / m) * ⟪v', w⟫)
  let μ₂ := (1 / (sin (π / m)) ^ 2) * (⟪v', w⟫ + cos (π / m) * ⟪v, w⟫)
  use μ₁, μ₂, w - μ₁ • v - μ₂ • v', by abel
  -- Expand everything out.
  simp only [mul_add, map_sub, map_add, map_smul, smul_eq_mul, μ₁, μ₂]
  -- Use known values of bilinear form.
  field_simp [M.standardBilinForm_comm v' v, hv, hv', hvv', sin_pi_div_m_ne_zero hm]
  ring_nf
  rw [Real.sin_sq]
  ring_nf
  simp

lemma orthoReflection_apply_eq_self_of_orthogonal
    {v : V} (hv : ⟪v, v⟫ = 1) (w : V) (hvw : ⟪v, w⟫ = 0) :
    (r v) w = w := by
  simp [M.orthoReflection_apply hv, hvw]

private lemma fixed_of_orthogonal {v v' : V} (w : V) (m : ℕ)
    (hv : ⟪v, v⟫ = 1) (hv' : ⟪v', v'⟫ = 1) (hvw : ⟪v, w⟫ = 0) (hv'w : ⟪v', w⟫ = 0) :
    (((r v) * (r v')) ^ m) w = w := by
  induction' m with m ih
  · simp
  · rw [pow_succ', LinearEquiv.mul_apply, ih, LinearEquiv.mul_apply]
    simp [M.orthoReflection_apply_eq_self_of_orthogonal hv w hvw,
      M.orthoReflection_apply_eq_self_of_orthogonal hv' w hv'w]

private lemma orthoReflection_mul_orthoReflection_pow_order {v v' : V} {m : ℕ}
    (hv : ⟪v, v⟫ = 1) (hv' : ⟪v', v'⟫ = 1) (hvv' : ⟪v, v'⟫ = -cos (π / m)) (hm : m ≠ 1) :
    ((r v) * (r v')) ^ m = 1 := by
  rcases hm.lt_or_lt with mlt | mgt
  · simp [Nat.lt_one_iff.mp mlt]
  · apply LinearEquiv.ext
    intro w
    obtain ⟨μ₁, μ₂, w', rfl, h₁, h₂⟩ := M.can_decomp_into_parallel_and_orthogonal w hv hv' hvv' mgt
    simp_all [M.fixed_of_orthogonal, M.orthoReflection_mul_orthoReflection_pow_order_apply_v,
      M.orthoReflection_mul_orthoReflection_pow_order_apply_v']

end CoxeterMatrix
